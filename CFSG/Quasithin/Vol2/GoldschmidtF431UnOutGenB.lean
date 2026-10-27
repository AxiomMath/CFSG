module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutGenA
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutDatum

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431

universe u v

section Reps

variable {Mb : Type u} [Group Mb] {T Sb N N' V : Subgroup Mb} {f z t : Mb}

theorem F431UnOut.rep_mem (O : F431UnOut T Sb f N N' z t V) {i : Mb} (hi : i = z ∨ i = t) :
    i ∈ Sb := by
  rcases hi with h | h
  · rw [h]
    exact O.z_mem
  · rw [h]
    exact O.t_mem

theorem F431UnOut.exists_rep {G : Type v} [Group G] {b : ↥N →* G} {b' : ↥N' →* G}
    (O : F431UnOut T Sb f N N' z t V) (C : F431Comp N N' b b') {x : Mb} (hx : x ∈ Sb)
    (hxo : orderOf x = 2) :
    ∃ i, (i = z ∨ i = t) ∧ IsConj x i ∧ IsConj (amalgamMap b b' x) (amalgamMap b b' i) := by
  obtain ⟨i, hi, hch⟩ := O.fusion x hx hxo
  exact ⟨i, hi, isConj_of_fusion hch, isConj_amalgam_of_fusion C O.T_le O.T_le' hch⟩

end Reps

section Main

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] [Finite G] {T Sb N N' V : Subgroup Mb}
  {f z t : Mb} {b : ↥N →* G} {b' : ↥N' →* G} {M M' : Subgroup G}

theorem UnGSetup.sylow_img (S : UnGSetup N N' b b' M M') (O : F431UnOut T Sb f N N' z t V) :
    IsSylowTwoOf (subImg b T) ⊤ := by
  have hzN : z ∈ N := O.T_le (O.S_le O.z_mem)
  have hbz : Subgroup.centralizer ({b ⟨z, hzN⟩} : Set G) ≤ b.range := by
    rw [S.range]
    exact S.cent _ (map_mem_centerOf_perfectCore S.comp.inj₁ S.range hzN O.z_ZN)
      ((orderOf_img S.comp.inj₁ hzN).trans O.z_two)
  exact lemma_F433_aux b S.comp.inj₁ O.sylow O.T_le (O.S_le O.z_mem) O.z_two O.center_T hbz

theorem UnGSetup.not_isConj_amalgam (S : UnGSetup N N' b b' M M')
    (O : F431UnOut T Sb f N N' z t V) :
    ¬ IsConj (amalgamMap b b' z) (amalgamMap b b' t) := by
  have hzT : z ∈ T := O.S_le O.z_mem
  have htT : t ∈ T := O.S_le O.t_mem
  rw [amalgamMap_of_mem₁ b b' (O.T_le hzT), amalgamMap_of_mem₁ b b' (O.T_le htT)]
  exact S.not_isConj_zt (O.T_le hzT) (O.T_le htT) O.sylow O.T_le O.T_le' hzT O.z_two O.z_ZN
    O.center_T (O.V_le.trans O.S_le) O.V_ab O.V_sq O.V_eq O.V_unique O.V_zt.1 O.V_zt.2
    O.zt_not_conj

theorem UnGSetup.isConj_of_isConj_img (S : UnGSetup N N' b b' M M')
    (O : F431UnOut T Sb f N N' z t V) {x y : Mb} (hx : x ∈ Sb) (hy : y ∈ Sb)
    (hxo : orderOf x = 2) (hyo : orderOf y = 2)
    (h : IsConj (amalgamMap b b' x) (amalgamMap b b' y)) : IsConj x y := by
  obtain ⟨i, hi, hxi, hxiφ⟩ := O.exists_rep S.comp hx hxo
  obtain ⟨j, hj, hyj, hyjφ⟩ := O.exists_rep S.comp hy hyo
  have hij : IsConj (amalgamMap b b' i) (amalgamMap b b' j) := (hxiφ.symm.trans h).trans hyjφ
  have hnc := S.not_isConj_amalgam O
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · rw [show i = j from hi.trans hj.symm] at hxi
    exact hxi.trans hyj.symm
  · rw [hi, hj] at hij
    exact absurd hij hnc
  · rw [hi, hj] at hij
    exact absurd hij.symm hnc
  · rw [show i = j from hi.trans hj.symm] at hxi
    exact hxi.trans hyj.symm

theorem UnGSetup.sylow_Tf [Finite Mb] (S : UnGSetup N N' b b' M M')
    (O : F431UnOut T Sb f N N' z t V) :
    IsSylowTwoOf (subImg b (spTf T f))
      (Subgroup.centralizer ({b ⟨f, O.T_le O.f_mem⟩} : Set G)) := by
  have hwc : ∀ (x y : Mb) (hx : x ∈ N) (hy : y ∈ N), x ∈ spWf T f → y ∈ spWf T f →
      orderOf x = 2 → orderOf y = 2 → IsConj (b ⟨x, hx⟩) (b ⟨y, hy⟩) → IsConj x y := by
    intro x y hx hy hxW hyW hxo hyo h
    refine S.isConj_of_isConj_img O (O.W_le hxW) (O.W_le hyW) hxo hyo ?_
    rw [amalgamMap_of_mem₁ b b' hx, amalgamMap_of_mem₁ b b' hy]
    exact h
  have hcomm : ∀ x ∈ spWf T f, ∀ y ∈ spWf T f, y * x = x * y := by
    intro x hx y hy
    unfold spWf at hx hy
    exact (mem_centerOf_iff.mp hx.1).2 y (mem_centerOf_iff.mp hy.1).1
  refine sylow_Tf_of_weakly_closed (Sb := spWf T f) S.comp.inj₁ S.range S.cent O.T_le O.f_mem
    O.Sylow_Tf O.Z_sq ?_ ?_ O.W_ne hwc
  · intro x hxZ y hyC hxy
    have hyW : y ∈ spWf T f := (mem_centerOf_iff.mp hyC).1
    by_cases hx1 : x = 1
    · rw [hx1] at hxy
      rw [isConj_one_right.mp hxy]
      exact (centerOf (perfectCore N)).one_mem
    · obtain ⟨m, -, hm⟩ := O.ZN_trans x hxZ hx1
      exact O.W_cls y hyW ((isConj_iff.mpr ⟨m, hm⟩).trans hxy)
  · intro x hx
    exact mem_centerOf_iff.mpr ⟨hx, fun y hy => hcomm x hx y hy⟩

end Main

end CFSG.Quasithin.H13.F431.Un
