module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFlag

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

@[expose] def Vtail : Submodule K (Fin 4 → K) where
  carrier := {v | v 0 = 0}
  add_mem' := fun ha hb => by simp [Set.mem_setOf_eq.mp ha, Set.mem_setOf_eq.mp hb]
  zero_mem' := rfl
  smul_mem' := fun a _ hv => by simp [Set.mem_setOf_eq.mp hv]

@[expose] def tailProj : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun v j := if j = 0 then 0 else v j
  map_add' v w := by funext j; by_cases h : j = 0 <;> simp [h]
  map_smul' c v := by funext j; by_cases h : j = 0 <;> simp [h]

theorem ker_tailProj : LinearMap.ker (tailProj (K := K)) = Vsub 4 1 := by
  ext v
  rw [LinearMap.mem_ker]
  constructor
  · intro h j hj
    have hv := congrFun h j
    have hj0 : j ≠ 0 := fun h0 => by
      rw [h0] at hj
      exact Nat.not_le_of_gt (Nat.succ_pos 0) hj
    simpa [tailProj, hj0] using hv
  · intro h
    funext j
    by_cases hj0 : j = 0
    · subst hj0
      simp [tailProj]
    · have hj : 1 ≤ j.val := Nat.succ_le_of_lt ((Fin.pos_iff_ne_zero).mpr hj0)
      simp [tailProj, hj0, h j hj]

theorem tailProj_mem (v : Fin 4 → K) : tailProj v ∈ (Vtail : Submodule K (Fin 4 → K)) := by
  show (tailProj v) 0 = 0
  simp [tailProj]

theorem tailProj_of_mem {v : Fin 4 → K} (hv : v ∈ (Vtail : Submodule K (Fin 4 → K))) :
    tailProj v = v := by
  have hv0 : v 0 = 0 := by simpa [Vtail] using hv
  funext j
  by_cases h : j = 0
  · subst h
    simp [tailProj, hv0]
  · simp [tailProj, h]

theorem map_tailProj_of_le {S : Submodule K (Fin 4 → K)} (hS : S ≤ Vtail) :
    S.map tailProj = S := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [tailProj_of_mem (hS hv)]
  · intro hw
    exact ⟨w, hw, tailProj_of_mem (hS hw)⟩

theorem map_tailProj_Vsub : (Vsub 4 1 : Submodule K (Fin 4 → K)).map tailProj = ⊥ := by
  rw [← LinearMap.le_ker_iff_map, ker_tailProj]

private theorem plh_map_tailProj_le {S T T' : Submodule K (Fin 4 → K)}
    (hS : S ⊓ Vsub 4 1 = ⊥) (hT : T ≤ S) (hT' : T' ≤ S)
    (h : T.map tailProj = T'.map tailProj) : T ≤ T' := by
  intro v hv
  have hmap : tailProj v ∈ T'.map tailProj := by
    rw [← h]
    exact ⟨v, hv, rfl⟩
  obtain ⟨v', hv', hv'eq⟩ := hmap
  have hsub : v - v' ∈ S := S.sub_mem (hT hv) (hT' hv')
  have hker : v - v' ∈ Vsub 4 1 := by
    rw [← ker_tailProj, LinearMap.mem_ker, map_sub, hv'eq, sub_self]
  have hmem : v - v' ∈ S ⊓ Vsub 4 1 := ⟨hsub, hker⟩
  rw [hS] at hmem
  have h0 : v - v' = 0 := by simpa using hmem
  have hvv' : v = v' := sub_eq_zero.mp h0
  rw [hvv']
  exact hv'

theorem map_tailProj_inj {S T T' : Submodule K (Fin 4 → K)} (hS : S ⊓ Vsub 4 1 = ⊥) (hT : T ≤ S)
    (hT' : T' ≤ S) (h : T.map tailProj = T'.map tailProj) : T = T' :=
  le_antisymm (plh_map_tailProj_le hS hT hT' h) (plh_map_tailProj_le hS hT' hT h.symm)

theorem Vtail_inf_Vsub : (Vtail : Submodule K (Fin 4 → K)) ⊓ Vsub 4 1 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  obtain ⟨hv0, hv1⟩ := Submodule.mem_inf.mp hv
  have hv00 : v 0 = 0 := by simpa [Vtail] using hv0
  funext j
  by_cases hj : j = 0
  · subst hj
    exact hv00
  · exact hv1 j (Nat.succ_le_of_lt ((Fin.pos_iff_ne_zero).mpr hj))

structure TData (K : Type) [Field K] where
  okL : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) → Prop

@[expose] def AdmT (D : TData K) (p L H : Submodule K (Fin 4 → K)) : Prop :=
  H ⊓ Vsub 4 1 = ⊥ ∧ D.okL (p.map tailProj) (L.map tailProj)

@[expose] def BPt (u : Submodule K (Fin 4 → K)) : Prop :=
  u ≤ Vtail ∧ finrank K u = 1

@[expose] def BFl (p L : Submodule K (Fin 4 → K)) : Prop :=
  p ≤ L ∧ L ≤ Vtail ∧ finrank K p = 1 ∧ finrank K L = 2

@[expose] def BAdj (D : TData K) (u t : Submodule K (Fin 4 → K)) : Prop :=
  u ≠ t ∧ D.okL u (u ⊔ t) ∧ D.okL t (u ⊔ t)

structure TBase (D : TData K) : Prop where
  link : ∀ p L, BFl p L → D.okL p L →
    ∃ L₂ L₃, L₂ ≠ L₃ ∧ BFl p L₂ ∧ BFl p L₃ ∧ D.okL p L₂ ∧ D.okL p L₃
  nbr2 : ∀ u v, (∃ L, BFl u L ∧ D.okL u L) → (∃ L, BFl v L ∧ D.okL v L) →
    ∃ t, BPt t ∧ BAdj D u t ∧ BAdj D v t
  nbr4 : ∀ a b c d, BPt a → BPt b → BPt c → BPt d → BAdj D a b → BAdj D b c → BAdj D c d →
    BAdj D d a → ∃ t, BPt t ∧ BAdj D a t ∧ BAdj D b t ∧ BAdj D c t ∧ BAdj D d t
  nbr3 : ∀ u c d, (∃ L, BFl u L ∧ D.okL u L) → BPt c → BPt d → BAdj D c d →
    ∃ t, BPt t ∧ BAdj D u t ∧ BAdj D c t ∧ BAdj D d t
  cone : ∀ x y z, BPt x → BPt y → BPt z → BAdj D x y → BAdj D y z → BAdj D z x →
    ∃ t, BPt t ∧ BAdj D x t ∧ BAdj D y t ∧ BAdj D z t ∧ finrank K ↥(x ⊔ y ⊔ t) = 3 ∧
      finrank K ↥(y ⊔ z ⊔ t) = 3 ∧ finrank K ↥(z ⊔ x ⊔ t) = 3

theorem finrank_map_tailProj {S : Submodule K (Fin 4 → K)} (h : S ⊓ Vsub 4 1 = ⊥) :
    finrank K (S.map tailProj) = finrank K S := by
  have hd : Disjoint S (LinearMap.ker (tailProj (K := K))) := by
    rw [ker_tailProj]
    exact disjoint_iff.mpr h
  have hinj : Function.Injective (tailProj.domRestrict S) :=
    (LinearMap.injective_domRestrict_iff).mpr hd
  rw [← LinearMap.range_domRestrict S tailProj, LinearMap.finrank_range_of_inj hinj]

theorem map_tailProj_sup (S T : Submodule K (Fin 4 → K)) :
    (S ⊔ T).map tailProj = S.map tailProj ⊔ T.map tailProj := by
  rw [Submodule.map_sup]

theorem sup_Vsub_eq_comap {S : Submodule K (Fin 4 → K)} :
    S ⊔ Vsub 4 1 = (S.map tailProj).comap tailProj := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_comap]
    obtain ⟨s, hs, v, hv, hsv⟩ := Submodule.mem_sup.mp hx
    have hv0 : tailProj v = 0 := by
      rw [← LinearMap.mem_ker, ker_tailProj]
      exact hv
    rw [← hsv, map_add, hv0, add_zero]
    exact Submodule.mem_map_of_mem hs
  · intro hx
    rw [Submodule.mem_comap] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    have hxker : x - s ∈ Vsub 4 1 := by
      rw [← ker_tailProj, LinearMap.mem_ker, map_sub, hsx, sub_self]
    have hsx' : s + (x - s) = x := by abel
    rw [← hsx']
    exact Submodule.add_mem_sup hs hxker

theorem exists_plane_avoiding {L : Submodule K (Fin 4 → K)} (hL : finrank K L = 2)
    (h : L ⊓ Vsub 4 1 = ⊥) :
    ∃ H : Submodule K (Fin 4 → K), L ≤ H ∧ finrank K H = 3 ∧ H ⊓ Vsub 4 1 = ⊥ := by
  have hfin1 : finrank K (Vsub 4 1 : Submodule K (Fin 4 → K)) = 1 := by
    simpa using finrank_Vsub (K := K) (n := 4) (c := 1) (by norm_num)
  have hsup3 : finrank K ↥(L ⊔ Vsub 4 1) = 3 := by
    have hle := Submodule.finrank_sup_add_finrank_inf_eq L (Vsub 4 1 : Submodule K (Fin 4 → K))
    rw [h, finrank_bot, hL, hfin1] at hle
    omega
  have hne : L ⊔ Vsub 4 1 ≠ ⊤ := by
    intro htop
    have h4 : finrank K ↥(L ⊔ Vsub 4 1) = 4 := by
      rw [htop, finrank_top]
      exact Module.finrank_fin_fun K
    omega
  obtain ⟨w, hw⟩ : ∃ w, w ∉ L ⊔ Vsub 4 1 := by
    by_contra hc
    rw [not_exists] at hc
    exact hne (eq_top_iff.mpr fun w _ => by
      by_contra hw
      exact hc w hw)
  have hwL : w ∉ L := fun hwL => hw (Submodule.mem_sup_left hwL)
  have hw0 : w ≠ 0 := fun h0 => hw (h0.symm ▸ Submodule.zero_mem _)
  refine ⟨L ⊔ K ∙ w, le_sup_left, ?_, ?_⟩
  · have hdisj : Disjoint L (K ∙ w) := Submodule.disjoint_span_singleton_of_notMem hwL
    have hle := Submodule.finrank_sup_add_finrank_inf_eq L (K ∙ w : Submodule K (Fin 4 → K))
    rw [hdisj.eq_bot, finrank_bot, hL, finrank_span_singleton hw0] at hle
    omega
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨hxH, hxV⟩ := Submodule.mem_inf.mp hx
    obtain ⟨l, hl, y, hy, hxy⟩ := Submodule.mem_sup.mp hxH
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hc0 : c = 0
    · subst hc0
      have hy0 : y = 0 := by rw [← hc, zero_smul]
      have hxL : x ∈ L := by rw [← hxy, hy0, add_zero]; exact hl
      have hmem : x ∈ L ⊓ Vsub 4 1 := ⟨hxL, hxV⟩
      rw [h] at hmem
      simpa using hmem
    · exfalso
      have hwmem : w ∈ L ⊔ Vsub 4 1 := by
        have hxc : x - l = c • w := by rw [← hxy, add_sub_cancel_left, hc]
        have hw_eq : w = c⁻¹ • (x - l) := by
          rw [hxc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hw_eq]
        have hl' : l ∈ L ⊔ Vsub 4 1 := Submodule.mem_sup_left (S := L) (T := Vsub 4 1) hl
        have hx' : x ∈ L ⊔ Vsub 4 1 := Submodule.mem_sup_right (S := L) (T := Vsub 4 1) hxV
        exact (L ⊔ Vsub 4 1).smul_mem _ ((L ⊔ Vsub 4 1).sub_mem hx' hl')
      exact hw hwmem

end CFSG.ClassicalInvolution.Phan.PhanE

end
