module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveCore
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def Fix121 (G A : Subgroup (LGL 2 V)) (a : LGL 2 V) : Prop :=
  fixMod (cE G) a ⊓ commSub G = commSub A ⊔ cE G

theorem fix121_of_gen {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g)
    {a : LGL 2 V} (ha : a ∈ A) (hgen : G = Subgroup.zpowers a ⊔ cj g A) : Fix121 G A a := by
  unfold Fix121
  have hAG : A ≤ G := by rw [h.gen]; exact le_sup_left
  have hBg : cj g A ≤ G := by rw [h.gen]; exact le_sup_right
  have hquadB := commSpace_cj_eq_bot h.quadratic g
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxfix : a x - x ∈ cE G := hx.1
    have hxG : x ∈ commSub G := hx.2
    have hxsup : x ∈ commSub A ⊔ commSub (cj g A) := by
      rw [← twelveOneK_sum h]; exact hxG
    obtain ⟨u, huA, v, hvB, huv⟩ := Submodule.mem_sup.mp hxsup
    have hav : a v - v ∈ cE G := by
      have h1 : a x - x = (a u - u) + (a v - v) := by rw [← huv, map_add]; abel
      rw [h1] at hxfix
      have hu0 : a u - u = 0 := by
        rw [commSub_le_fixSub_of_quadratic h.quadratic huA a ha, sub_self]
      rw [hu0, zero_add] at hxfix
      exact hxfix
    have hvG : v ∈ commSub G := by
      rw [twelveOneK_sum h]; exact Submodule.mem_sup_right hvB
    have hvW : v ∈ cE G := by
      have hgenS : G = Subgroup.closure ({a} ∪ (cj g A : Set (LGL 2 V))) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, ← zpowers_eq_closure]
        exact hgen
      have hS : ∀ t ∈ ({a} ∪ (cj g A : Set (LGL 2 V))), t v - v ∈ cE G := by
        intro t ht
        rcases ht with ht | ht
        · rw [Set.mem_singleton_iff] at ht; subst ht; exact hav
        · have : t v = v := commSub_le_fixSub_of_quadratic hquadB hvB t ht
          rw [this, sub_self]; exact (cE G).zero_mem
      exact mem_cE_of_fixed_mod_cj h hvB (fixMod_of_closure hgenS hS)
    rw [← huv]
    exact Submodule.add_mem_sup huA hvW
  · intro x hx
    obtain ⟨u, huA, w, hwW, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨?_, ?_⟩
    · show a (u + w) - (u + w) ∈ cE G
      have hu : a u = u := commSub_le_fixSub_of_quadratic h.quadratic huA a ha
      have hw : a w = w := (cE_le_fixSub G hwW) a (hAG ha)
      have h1 : a (u + w) - (u + w) = (a u - u) + (a w - w) := by rw [map_add]; abel
      rw [h1, hu, hw, sub_self, sub_self, add_zero]
      exact (cE G).zero_mem
    · exact (commSub G).add_mem
        (by rw [twelveOneK_sum h]; exact Submodule.mem_sup_left huA)
        (cE_le_commSub G hwW)

theorem twelveOneK_aa {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g)
    {a : LGL 2 V} (ha : a ∈ A) (hfa : Fix121 G A a)
    (hfb : Fix121 G (cj g A) ((MulAut.conj g) a)) :
    fixMod (cE G) (a * (MulAut.conj g) a) ⊓ commSub G ≤ cE G := by
  have hAG : A ≤ G := by rw [h.gen]; exact le_sup_left
  have hBg : cj g A ≤ G := by rw [h.gen]; exact le_sup_right
  have hquadB := commSpace_cj_eq_bot h.quadratic g
  have hfixA : fixMod (cE G) a ⊓ commSub G = commSub A ⊔ cE G := hfa
  set ag : LGL 2 V := (MulAut.conj g) a with hagdef
  have hfixB : fixMod (cE G) ag ⊓ commSub G = commSub (cj g A) ⊔ cE G := hfb
  have hb : ag ∈ cj g A := by
    rw [hagdef]; exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hss : a * a = 1 := h.elemAb.mul_self_eq_one ha
  intro x hx
  have haa : (a * ag) x - x ∈ cE G := hx.1
  have hxG : x ∈ commSub G := hx.2
  have hxsup : x ∈ commSub A ⊔ commSub (cj g A) := by
    rw [← twelveOneK_sum h]; exact hxG
  obtain ⟨u, huA, v, hvB, huv⟩ := Submodule.mem_sup.mp hxsup
  have huG : u ∈ commSub G := by
    rw [twelveOneK_sum h]; exact Submodule.mem_sup_left huA
  have hvG : v ∈ commSub G := by
    rw [twelveOneK_sum h]; exact Submodule.mem_sup_right hvB
  have hau : a u = u := commSub_le_fixSub_of_quadratic h.quadratic huA a ha
  have hagv : ag v = v := commSub_le_fixSub_of_quadratic hquadB hvB ag hb
  have haav : a (a v) = v := by rw [← LinearEquiv.mul_apply, hss]; rfl
  have hz : (ag u - u) - (a v - v) ∈ cE G := by
    have h1 : a ((a * ag) x - x) ∈ cE G := map_mem_cE G (hAG ha) haa
    have h2 : a ((a * ag) x - x) = (ag u - u) - (a v - v) := by
      have hss' : ∀ y : V, a (a y) = y := fun y => by rw [← LinearEquiv.mul_apply, hss]; rfl
      rw [show x = u + v from huv.symm]
      simp only [LinearEquiv.mul_apply, map_add, map_sub, hss', hagv, haav, hau]
      abel
    rwa [h2] at h1
  have hzA : ag u - u ∈ commSub (cj g A) := sub_mem_commSub (cj g A) hb u
  have hzB : a v - v ∈ commSub A := sub_mem_commSub A ha v
  have hmk : (cE G).mkQ (ag u - u) = (cE G).mkQ (a v - v) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero (cE G)).mpr hz
  have hag_u : ag u - u ∈ cE G := by
    have hmem : (cE G).mkQ (ag u - u) ∈
        (commSub (cj g A)).map (cE G).mkQ ⊓ (commSub A).map (cE G).mkQ := by
      refine ⟨Submodule.mem_map.mpr ⟨ag u - u, hzA, rfl⟩, ?_⟩
      rw [hmk]
      exact Submodule.mem_map.mpr ⟨a v - v, hzB, rfl⟩
    rw [inf_comm, twelveOneK_map_inf h] at hmem
    exact (Submodule.Quotient.mk_eq_zero (cE G)).mp (by simpa using hmem)
  have hav : a v - v ∈ cE G :=
    (Submodule.Quotient.mk_eq_zero (cE G)).mp (by
      change (cE G).mkQ (a v - v) = 0
      rw [← hmk]
      exact (Submodule.Quotient.mk_eq_zero (cE G)).mpr hag_u)
  have huW : u ∈ cE G := by
    have hu_sup : u ∈ commSub (cj g A) ⊔ cE G := by
      rw [← hfixB]
      exact ⟨(mem_fixMod).mpr hag_u, huG⟩
    exact inf_sup_cE_leK h ⟨huA, hu_sup⟩
  have hvW : v ∈ cE G := by
    have hv_sup : v ∈ commSub A ⊔ cE G := by
      rw [← hfixA]
      exact ⟨(mem_fixMod).mpr hav, hvG⟩
    exact inf_sup_cE_le_agK h ⟨hvB, hv_sup⟩
  rw [← huv]
  exact (cE G).add_mem huW hvW

@[expose] def Conclusion121 (G A : Subgroup (LGL 2 V)) (g : LGL 2 V) (P : LGL 2 V → Prop) :
    Prop :=
  commSub G = commSub A ⊔ commSub (cj g A) ∧
  (commSub A).map (cE G).mkQ ⊓ (commSub (cj g A)).map (cE G).mkQ = ⊥ ∧
  (∀ a ∈ A, P a → fixMod (cE G) a ⊓ commSub G = commSub A ⊔ cE G) ∧
  (∀ a ∈ A, P a → fixMod (cE G) (a * (MulAut.conj g) a) ⊓ commSub G ≤ cE G)

theorem conclusion121_of_gen {G A : Subgroup (LGL 2 V)} {g : LGL 2 V} (h : Hyp121K G A g)
    {P : LGL 2 V → Prop} (hP : ∀ a ∈ A, P a → G = Subgroup.zpowers a ⊔ cj g A)
    (hP' : ∀ a ∈ A, P a → G = Subgroup.zpowers ((MulAut.conj g) a) ⊔ A) :
    Conclusion121 G A g P := by
  unfold Conclusion121
  refine ⟨twelveOneK_sum h, twelveOneK_map_inf h, ?_, ?_⟩
  · intro a ha hPa
    exact fix121_of_gen h ha (hP a ha hPa)
  · intro a ha hPa
    have hb : (MulAut.conj g) a ∈ cj g A := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hgen' : G = Subgroup.zpowers ((MulAut.conj g) a) ⊔ cj g⁻¹ (cj g A) := by
      rw [cj_self_inv]
      exact hP' a ha hPa
    have hfb := fix121_of_gen h.conj hb hgen'
    exact twelveOneK_aa h ha (fix121_of_gen h ha (hP a ha hPa)) hfb

end CFSG.LocalAnalysis.WeakClosure81
