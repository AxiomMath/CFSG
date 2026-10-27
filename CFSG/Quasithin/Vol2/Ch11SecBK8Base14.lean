module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base13

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def sqSub (S : Submodule K (Fin 3 → K)) : Subgroup (W6 K) where
  carrier := {v | Multiplicative.toAdd v ∘ Sum.inl ∈ S ∧ Multiplicative.toAdd v ∘ Sum.inr ∈ S}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · change Multiplicative.toAdd a ∘ Sum.inl + Multiplicative.toAdd b ∘ Sum.inl ∈ S
      exact S.add_mem ha.1 hb.1
    · change Multiplicative.toAdd a ∘ Sum.inr + Multiplicative.toAdd b ∘ Sum.inr ∈ S
      exact S.add_mem ha.2 hb.2
  one_mem' := ⟨S.zero_mem, S.zero_mem⟩
  inv_mem' {a} ha := by
    refine ⟨?_, ?_⟩
    · change -(Multiplicative.toAdd a ∘ Sum.inl) ∈ S
      exact S.neg_mem ha.1
    · change -(Multiplicative.toAdd a ∘ Sum.inr) ∈ S
      exact S.neg_mem ha.2

theorem mem_sqSub {S : Submodule K (Fin 3 → K)} {v : W6 K} :
    v ∈ sqSub S ↔ Multiplicative.toAdd v ∘ Sum.inl ∈ S ∧ Multiplicative.toAdd v ∘ Sum.inr ∈ S :=
  Iff.rfl

@[expose] def lineL (S : Submodule K (Fin 3 → K)) : Subgroup (W6 K) where
  carrier := {v | Multiplicative.toAdd v ∘ Sum.inl ∈ S ∧ Multiplicative.toAdd v ∘ Sum.inr = 0}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · change Multiplicative.toAdd a ∘ Sum.inl + Multiplicative.toAdd b ∘ Sum.inl ∈ S
      exact S.add_mem ha.1 hb.1
    · change Multiplicative.toAdd a ∘ Sum.inr + Multiplicative.toAdd b ∘ Sum.inr = 0
      rw [ha.2, hb.2, add_zero]
  one_mem' := ⟨S.zero_mem, rfl⟩
  inv_mem' {a} ha := by
    refine ⟨?_, ?_⟩
    · change -(Multiplicative.toAdd a ∘ Sum.inl) ∈ S
      exact S.neg_mem ha.1
    · change -(Multiplicative.toAdd a ∘ Sum.inr) = 0
      rw [ha.2, neg_zero]

theorem mem_lineL {S : Submodule K (Fin 3 → K)} {v : W6 K} :
    v ∈ lineL S ↔ Multiplicative.toAdd v ∘ Sum.inl ∈ S ∧ Multiplicative.toAdd v ∘ Sum.inr = 0 :=
  Iff.rfl

theorem card_sqSub [Finite K] (S : Submodule K (Fin 3 → K)) :
    Nat.card ↥(sqSub S) = Nat.card ↥S ^ 2 := by
  rw [sq, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun v => (⟨_, v.2.1⟩, ⟨_, v.2.2⟩)
      invFun := fun p => ⟨Multiplicative.ofAdd (Sum.elim p.1.1 p.2.1), p.1.2, p.2.2⟩
      left_inv := fun v => Subtype.ext (by
        apply Multiplicative.toAdd.injective
        funext i
        rcases i with i | i <;> rfl)
      right_inv := fun p => rfl }

theorem lineL_ne_bot {S : Submodule K (Fin 3 → K)} {w : Fin 3 → K} (hw : w ∈ S) (hw0 : w ≠ 0) :
    lineL S ≠ ⊥ := by
  intro h
  have hmem : Multiplicative.ofAdd (Sum.elim w (0 : Fin 3 → K)) ∈ lineL S :=
    mem_lineL.mpr ⟨hw, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  apply hw0
  funext j
  exact congrFun (congrArg Multiplicative.toAdd hmem) (Sum.inl j)

theorem toAdd_comm_trvW {f : (Fin 3 → K) →ₗ[K] K} {w : Fin 3 → K} {y : MulAut (W6 K)}
    (hy : ∀ v, toAddMap y v = trvW f w v) (v : W6 K) :
    Multiplicative.toAdd (y v * v⁻¹) =
      Sum.elim (f (Multiplicative.toAdd v ∘ Sum.inl) • w)
        (f (Multiplicative.toAdd v ∘ Sum.inr) • w) := by
  rw [toAdd_mul, toAdd_inv]
  have := hy (Multiplicative.toAdd v)
  change Multiplicative.toAdd (y (Multiplicative.ofAdd (Multiplicative.toAdd v))) = _ at this
  rw [ofAdd_toAdd] at this
  rw [this]
  simp only [trvW]
  abel

theorem commSub_top_axis {A : Subgroup (MulAut (W6 K))} {f : (Fin 3 → K) →ₗ[K] K}
    (hf0 : f ≠ 0) (hform : ∀ y ∈ A, ∃ w, f w = 0 ∧ ∀ v, toAddMap y v = trvW f w v)
    (hsurj : ∀ w, f w = 0 → ∃ y ∈ A, ∀ v, toAddMap y v = trvW f w v) :
    commSub ⊤ A = sqSub (LinearMap.ker f) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, f v₀ = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    exact ⟨(f u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, v, -, rfl⟩
    obtain ⟨w, hw, hyw⟩ := hform y hy
    have h1 := toAdd_comm_trvW hyw v
    refine ⟨?_, ?_⟩
    · change Multiplicative.toAdd (y v * v⁻¹) ∘ Sum.inl ∈ LinearMap.ker f
      rw [h1, Sum.elim_comp_inl, LinearMap.mem_ker, map_smul, hw, smul_zero]
    · change Multiplicative.toAdd (y v * v⁻¹) ∘ Sum.inr ∈ LinearMap.ker f
      rw [h1, Sum.elim_comp_inr, LinearMap.mem_ker, map_smul, hw, smul_zero]
  · intro v hv
    have hgen : ∀ (s : Fin 3 → K), f s = 0 → ∀ b : Bool,
        Multiplicative.ofAdd (if b then Sum.elim s (0 : Fin 3 → K) else Sum.elim 0 s) ∈
          commSub ⊤ A := by
      intro s hs b
      obtain ⟨y, hy, hys⟩ := hsurj s hs
      set u : W6 K := Multiplicative.ofAdd
        (if b then Sum.elim v₀ (0 : Fin 3 → K) else Sum.elim 0 v₀) with hu
      refine Subgroup.subset_closure ⟨y, hy, u, Subgroup.mem_top u, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [toAdd_comm_trvW hys, hu, toAdd_ofAdd]
      cases b <;> simp [hv₀]
    have hdec : v = Multiplicative.ofAdd
        (Sum.elim (Multiplicative.toAdd v ∘ Sum.inl) (0 : Fin 3 → K)) *
        Multiplicative.ofAdd (Sum.elim (0 : Fin 3 → K) (Multiplicative.toAdd v ∘ Sum.inr)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
      funext i
      rcases i with i | i <;> simp
    rw [hdec]
    exact Subgroup.mul_mem _ (by simpa using hgen _ hv.1 true) (by simpa using hgen _ hv.2 false)

theorem commSub_zpowers_axis [CharP K 2] {A : Subgroup (MulAut (W6 K))}
    {f : (Fin 3 → K) →ₗ[K] K} (hform : ∀ y ∈ A, ∃ w, f w = 0 ∧ ∀ v, toAddMap y v = trvW f w v)
    (hsurj : ∀ w, f w = 0 → ∃ y ∈ A, ∀ v, toAddMap y v = trvW f w v) {u : Fin 3 → K}
    (hu : f u ≠ 0) :
    commSub (Subgroup.zpowers (Multiplicative.ofAdd (Sum.elim u (0 : Fin 3 → K)))) A =
      lineL (LinearMap.ker f) := by
  set a : W6 K := Multiplicative.ofAdd (Sum.elim u (0 : Fin 3 → K)) with ha
  have hsq : a * a = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [CharTwo.add_self_eq_zero]
  have hz : ∀ z ∈ Subgroup.zpowers a, z = 1 ∨ z = a := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, hsq, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hsq, one_zpow, one_mul, zpow_one]
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, z, hz', rfl⟩
    obtain ⟨w, hw, hyw⟩ := hform y hy
    rcases hz z hz' with rfl | rfl
    · rw [map_one, one_mul, inv_one]
      exact (lineL _).one_mem
    · have h1 := toAdd_comm_trvW hyw a
      refine ⟨?_, ?_⟩
      · change Multiplicative.toAdd (y a * a⁻¹) ∘ Sum.inl ∈ LinearMap.ker f
        rw [h1, Sum.elim_comp_inl, LinearMap.mem_ker, map_smul, hw, smul_zero]
      · change Multiplicative.toAdd (y a * a⁻¹) ∘ Sum.inr = 0
        rw [h1, Sum.elim_comp_inr, ha, toAdd_ofAdd, Sum.elim_comp_inr, map_zero, zero_smul]
  · intro v hv
    obtain ⟨y, hy, hys⟩ := hsurj ((f u)⁻¹ • (Multiplicative.toAdd v ∘ Sum.inl))
      (by rw [map_smul, hv.1, smul_zero])
    refine Subgroup.subset_closure ⟨y, hy, a, Subgroup.mem_zpowers a, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_comm_trvW hys, ha, toAdd_ofAdd, Sum.elim_comp_inl, Sum.elim_comp_inr, map_zero,
      zero_smul, smul_smul, mul_inv_cancel₀ hu, one_smul]
    funext i
    rcases i with i | i
    · rfl
    · exact (congrFun hv.2 i).symm

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
