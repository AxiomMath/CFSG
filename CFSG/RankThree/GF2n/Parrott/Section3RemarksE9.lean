module

public import CFSG.GroupTheory.HyperplaneDecomposition
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

section Lines

variable {Γ : Type*} [Group Γ] {a b : Γ}

private theorem pow_three_eq_one_of_orderOf {x : Γ} (hx : orderOf x = 3) : x ^ 3 = 1 := by
  rw [← hx]
  exact pow_orderOf_eq_one x

private theorem eq_one_or_eq_or_eq_sq_of_mem_zpowers {x y : Γ} (hx : orderOf x = 3)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_emod' k (pow_three_eq_one_of_orderOf hx)]
  have h : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases h with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (Or.inl (zpow_one x))
  · exact Or.inr (Or.inr (zpow_ofNat x 2))

theorem isElemAbelian_zpowers_sup_of_commute [Finite Γ] (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Γ) = 9 := by
  have h := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
    (X := Subgroup.zpowers a) (by rw [Nat.card_zpowers, ha]) hb hnot fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (hab.zpow_left k).eq
  exact ⟨h.1, h.2.trans (by norm_num)⟩

private def lineGen (a b : Γ) : Fin 4 → Γ :=
  ![a, b, a * b, a * b⁻¹]

private theorem orderOf_mul_of_order_three (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) : orderOf (a * b) = 3 := by
  refine orderOf_eq_prime ?_ fun h => hnot ?_
  · rw [hab.mul_pow, pow_three_eq_one_of_orderOf ha, pow_three_eq_one_of_orderOf hb, one_mul]
  · rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)

private theorem orderOf_mul_inv_of_order_three (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) : orderOf (a * b⁻¹) = 3 := by
  refine orderOf_eq_prime ?_ fun h => hnot ?_
  · rw [hab.inv_right.mul_pow, inv_pow, pow_three_eq_one_of_orderOf ha,
      pow_three_eq_one_of_orderOf hb, inv_one, one_mul]
  · rw [← mul_inv_eq_one.mp h]
    exact Subgroup.mem_zpowers a

private theorem orderOf_lineGen (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : Commute a b)
    (hnot : b ∉ Subgroup.zpowers a) (i : Fin 4) : orderOf (lineGen a b i) = 3 := by
  fin_cases i
  exacts [ha, hb, orderOf_mul_of_order_three ha hb hab hnot,
    orderOf_mul_inv_of_order_three ha hb hab hnot]

private theorem lineGen_mem_sup (i : Fin 4) :
    lineGen a b i ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  fin_cases i
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  · exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b)
  · exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a)
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))

private theorem exists_mem_zpowers_lineGen (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) {x : Γ} (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    ∃ i : Fin 4, x ∈ Subgroup.zpowers (lineGen a b i) := by
  have hle : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set Γ) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hab.zpow_right k).eq.symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx
  have hb2 : b ^ 2 = b⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, pow_three_eq_one_of_orderOf hb])
  have hsq : (a * b⁻¹) ^ 2 = a ^ 2 * b := by
    rw [hab.inv_right.mul_pow, inv_pow, hb2, inv_inv]
  rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers ha hy with h1 | h1 | h1 <;>
    rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers hb hz with h2 | h2 | h2 <;> rw [h1, h2]
  · exact ⟨0, by rw [one_mul]; exact Subgroup.one_mem _⟩
  · exact ⟨1, by rw [one_mul]; exact Subgroup.mem_zpowers _⟩
  · exact ⟨1, by rw [one_mul]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2⟩
  · exact ⟨0, by rw [mul_one]; exact Subgroup.mem_zpowers _⟩
  · exact ⟨2, Subgroup.mem_zpowers _⟩
  · exact ⟨3, by rw [hb2]; exact Subgroup.mem_zpowers _⟩
  · exact ⟨0, by rw [mul_one]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2⟩
  · exact ⟨3, by rw [← hsq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2⟩
  · exact ⟨2, by rw [← hab.mul_pow]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2⟩

private theorem zpowers_eq_of_mem_of_order_three [Finite Γ] {x y : Γ} (hx : orderOf x = 3)
    (hy : orderOf y = 3) (h : x ∈ Subgroup.zpowers y) :
    Subgroup.zpowers x = Subgroup.zpowers y :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy])

end Lines

section Hyperplanes

variable {Γ : Type} [Group Γ] {a b : Γ}

private theorem mem_hyperplanes_of_card {D E : Subgroup Γ} (hDE : D ≤ E) (hD : Nat.card D = 3)
    (hE : Nat.card E = 9) : D ∈ hyperplanes 3 E := by
  refine ⟨hDE, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := D) (K := E)
  rw [inf_eq_left.mpr hDE, hD, hE] at h
  omega

private theorem zpowers_lineGen_mem_hyperplanes [Finite Γ] (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) (i : Fin 4) :
    Subgroup.zpowers (lineGen a b i) ∈ hyperplanes 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
  mem_hyperplanes_of_card (Subgroup.zpowers_le.mpr (lineGen_mem_sup i))
    (by rw [Nat.card_zpowers, orderOf_lineGen ha hb hab hnot i])
    (isElemAbelian_zpowers_sup_of_commute ha hb hab hnot).2

private theorem exists_eq_zpowers_lineGen [Finite Γ] (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) {D : Subgroup Γ}
    (hD : D ∈ hyperplanes 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) :
    ∃ i : Fin 4, D = Subgroup.zpowers (lineGen a b i) := by
  obtain ⟨hEea, hEcard⟩ := isElemAbelian_zpowers_sup_of_commute ha hb hab hnot
  obtain ⟨hDE, hDi⟩ := hD
  have hDcard : Nat.card D = 3 := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    rw [inf_eq_left.mpr hDE, hDi, hEcard] at h
    omega
  obtain ⟨x, hxD, hx1⟩ : ∃ x ∈ D, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one D with h | h
    · rw [h, Subgroup.card_bot] at hDcard
      omega
    · exact h
  have hxord : orderOf x = 3 := orderOf_eq_prime (hEea.2 x (hDE hxD)) hx1
  obtain ⟨i, hi⟩ := exists_mem_zpowers_lineGen ha hb hab (hDE hxD)
  refine ⟨i, ?_⟩
  rw [← zpowers_eq_of_mem_of_order_three hxord (orderOf_lineGen ha hb hab hnot i) hi]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxD)
    (by rw [hDcard, Nat.card_zpowers, hxord])).symm

private theorem injective_zpowers_lineGen [Finite Γ] (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    Function.Injective fun i : Fin 4 => Subgroup.zpowers (lineGen a b i) := by
  have hab3 := orderOf_mul_of_order_three ha hb hab hnot
  have hna : a ∉ Subgroup.zpowers b := fun h => hnot (by
    rw [zpowers_eq_of_mem_of_order_three ha hb h]
    exact Subgroup.mem_zpowers b)
  have h02 : a * b ∉ Subgroup.zpowers a := fun h => hnot (by
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) h)
  have h03 : a * b⁻¹ ∉ Subgroup.zpowers a := fun h => hnot (by
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) h)
  have h12 : a * b ∉ Subgroup.zpowers b := fun h => hna (by
    simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)))
  have h13 : a * b⁻¹ ∉ Subgroup.zpowers b := fun h => hna (by
    simpa using Subgroup.mul_mem _ h (Subgroup.mem_zpowers b))
  have h23 : a * b⁻¹ ∉ Subgroup.zpowers (a * b) := fun h => h12 (by
    have e : (a * b)⁻¹ * (a * b⁻¹) = b := by
      calc (a * b)⁻¹ * (a * b⁻¹) = b⁻¹ * b⁻¹ * b ^ 3 := by
            rw [pow_three_eq_one_of_orderOf hb]; group
        _ = b := by group
    have hbm := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers (a * b))) h
    rw [e] at hbm
    rw [zpowers_eq_of_mem_of_order_three hb hab3 hbm]
    exact Subgroup.mem_zpowers _)
  intro i j hij
  have h1 : lineGen a b j ∈ Subgroup.zpowers (lineGen a b i) := by
    rw [show Subgroup.zpowers (lineGen a b i) = Subgroup.zpowers (lineGen a b j) from hij]
    exact Subgroup.mem_zpowers _
  have h2 : lineGen a b i ∈ Subgroup.zpowers (lineGen a b j) := by
    rw [show Subgroup.zpowers (lineGen a b j) = Subgroup.zpowers (lineGen a b i) from hij.symm]
    exact Subgroup.mem_zpowers _
  clear hij
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact absurd h1 hnot | exact absurd h2 hnot
    | exact absurd h1 h02 | exact absurd h2 h02
    | exact absurd h1 h03 | exact absurd h2 h03
    | exact absurd h1 h12 | exact absurd h2 h12
    | exact absurd h1 h13 | exact absurd h2 h13
    | exact absurd h1 h23 | exact absurd h2 h23

private theorem bijective_zpowers_lineGen [Finite Γ] (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    Function.Bijective fun i : Fin 4 =>
      (⟨Subgroup.zpowers (lineGen a b i), zpowers_lineGen_mem_hyperplanes ha hb hab hnot i⟩ :
        hyperplanes 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) := by
  refine ⟨fun i j h => injective_zpowers_lineGen ha hb hab hnot (congrArg Subtype.val h),
    fun D => ?_⟩
  obtain ⟨i, hi⟩ := exists_eq_zpowers_lineGen ha hb hab hnot D.2
  exact ⟨i, Subtype.ext hi.symm⟩

end Hyperplanes

private theorem finrank_eq_sum_four_of_bijective {ι M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] [Module.Finite (ZMod 2) M] {p : ι → Submodule (ZMod 2) M}
    {e : Fin 4 → ι} (he : Function.Bijective e) (hind : iSupIndep p)
    {T : Submodule (ZMod 2) M} (hsup : ⨆ i, p i = T) :
    Module.finrank (ZMod 2) T = Module.finrank (ZMod 2) (p (e 0)) +
      Module.finrank (ZMod 2) (p (e 1)) + Module.finrank (ZMod 2) (p (e 2)) +
      Module.finrank (ZMod 2) (p (e 3)) := by
  have h := TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep (hind.comp he.1)
  rw [Fin.sum_univ_four] at h
  rw [← hsup, ← he.2.iSup_comp p]
  exact h

section Coprime

variable {Γ : Type} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable (ρ : Representation (ZMod 2) Γ W)

theorem mem_fixedSpace_zpowers_iff {g : Γ} {v : W} :
    v ∈ fixedSpace ρ (Subgroup.zpowers g) ↔ ρ g v = v := by
  rw [mem_fixedSpace_iff]
  refine ⟨fun h => h g (Subgroup.mem_zpowers g), fun h d hd => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  clear hd
  have hinv : ρ g⁻¹ v = v := by
    conv_lhs => rw [← h]
    rw [← rho_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply]
  induction k with
  | zero => rw [zpow_zero, map_one, Module.End.one_apply]
  | succ n ih => rw [zpow_add_one, rho_mul_apply, h, ih]
  | pred n ih => rw [zpow_sub_one, rho_mul_apply, hinv, ih]

private theorem natCast_card_zpowers_eq_one {a : Γ} (ha : orderOf a = 3)
    [Fintype (Subgroup.zpowers a)] :
    ((Fintype.card (Subgroup.zpowers a) : ℕ) : ZMod 2) = 1 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, ha]
  rfl

private theorem sub_normOp_mem_commSpace (B : Subgroup Γ) [Fintype B]
    (hB : ((Fintype.card B : ℕ) : ZMod 2) = 1) (v : W) :
    v - normOp ρ B v ∈ commSpace ρ B := by
  have h : v - normOp ρ B v = -∑ x : B, (ρ x v - v) := by
    rw [Finset.sum_sub_distrib, normOp_apply, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2), hB, one_smul, neg_sub]
  rw [h]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun x _ => Submodule.subset_span ⟨x, x.2, v, rfl⟩)

theorem isCompl_fixedSpace_commSpace [Finite Γ] {a : Γ} (ha : orderOf a = 3) :
    IsCompl (fixedSpace ρ (Subgroup.zpowers a)) (commSpace ρ (Subgroup.zpowers a)) := by
  have : Fintype (Subgroup.zpowers a) := Fintype.ofFinite _
  have hB := natCast_card_zpowers_eq_one ha
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hvF hvU
    have h := normOp_of_mem_fixedSpace ρ _ hvF
    rwa [normOp_commSpace ρ _ hvU, hB, one_smul, eq_comm] at h
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have h := Submodule.add_mem_sup (mem_fixedSpace_normOp ρ (Subgroup.zpowers a) v)
      (sub_normOp_mem_commSpace ρ _ hB v)
    rwa [add_sub_cancel] at h

theorem commSpace_inf_fixedSpace_eq_bot [Finite Γ] {a : Γ} (ha : orderOf a = 3) :
    commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers a) = ⊥ :=
  (isCompl_fixedSpace_commSpace ρ ha).symm.inf_eq_bot

theorem finrank_fixedSpace_add_finrank_commSpace [Finite Γ] [Module.Finite (ZMod 2) W] {a : Γ}
    (ha : orderOf a = 3) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) +
      Module.finrank (ZMod 2) (commSpace ρ (Subgroup.zpowers a)) = Module.finrank (ZMod 2) W :=
  Submodule.finrank_add_eq_of_isCompl (isCompl_fixedSpace_commSpace ρ ha)

theorem finrank_fixedSpace_eq_add [Finite Γ] [Module.Finite (ZMod 2) W] {a : Γ}
    (ha : orderOf a = 3) (g : Γ) (hg : Commute a g) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers g)) =
      Module.finrank (ZMod 2)
          ↥(fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g)) +
        Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g)) := by
  have : Fintype (Subgroup.zpowers a) := Fintype.ofFinite _
  have hB := natCast_card_zpowers_eq_one ha
  have hcomm : ∀ x ∈ Subgroup.zpowers a, g * x = x * g := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (hg.zpow_left k).eq.symm
  have hsup : fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g) ⊔
      commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g) =
        fixedSpace ρ (Subgroup.zpowers g) := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) fun v hv => ?_
    have hN : normOp ρ (Subgroup.zpowers a) v ∈ fixedSpace ρ (Subgroup.zpowers g) := by
      rw [mem_fixedSpace_zpowers_iff] at hv ⊢
      rw [normOp_comm ρ _ hcomm, hv]
    have h := Submodule.add_mem_sup
      (Submodule.mem_inf.mpr ⟨mem_fixedSpace_normOp ρ (Subgroup.zpowers a) v, hN⟩)
      (Submodule.mem_inf.mpr ⟨sub_normOp_mem_commSpace ρ _ hB v, Submodule.sub_mem _ hv hN⟩)
    rwa [add_sub_cancel] at h
  have hinf : fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g) ⊓
      (commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g)) = ⊥ := by
    rw [eq_bot_iff, ← (isCompl_fixedSpace_commSpace ρ ha).inf_eq_bot]
    exact inf_le_inf inf_le_left inf_le_left
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g))
    (commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers g))
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h

end Coprime

section Decomposition

variable {Γ : Type} [Group Γ] [Finite Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable (ρ : Representation (ZMod 2) Γ W) {a b : Γ}

private theorem iSupIndep_fixedSpace_hyperplanes_E9 (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a)
    (hE : fixedSpace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥) :
    iSupIndep fun D : hyperplanes 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) =>
      fixedSpace ρ D.1 :=
  CFSG.SolvableHall.iSupIndep_invariants_hyperplanes ρ Nat.prime_two Nat.prime_three
    (by norm_num) (isElemAbelian_zpowers_sup_of_commute ha hb hab hnot).1 hE

private theorem iSup_fixedSpace_hyperplanes_E9 [Module.Finite (ZMod 2) W] (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    ⨆ D : hyperplanes 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b), fixedSpace ρ D.1 = ⊤ := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have hne : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≠ ⊥ := by
    intro h
    have ha1 : a ∈ (⊥ : Subgroup Γ) := h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    rw [Subgroup.mem_bot] at ha1
    rw [ha1, orderOf_one] at ha
    exact absurd ha (by norm_num)
  exact CFSG.SolvableHall.iSup_invariants_hyperplanes_eq_top ρ Nat.prime_two Nat.prime_three
    (by norm_num) (isElemAbelian_zpowers_sup_of_commute ha hb hab hnot).1 hne

theorem sup_fixedSpace_eq_top [Module.Finite (ZMod 2) W] (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    fixedSpace ρ (Subgroup.zpowers a) ⊔ fixedSpace ρ (Subgroup.zpowers b) ⊔
        fixedSpace ρ (Subgroup.zpowers (a * b)) ⊔ fixedSpace ρ (Subgroup.zpowers (a * b⁻¹)) =
      ⊤ := by
  rw [eq_top_iff, ← iSup_fixedSpace_hyperplanes_E9 ρ ha hb hab hnot]
  refine iSup_le fun D => ?_
  obtain ⟨i, hi⟩ := exists_eq_zpowers_lineGen ha hb hab hnot D.2
  rw [hi]
  fin_cases i
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem iSupIndep_fixedSpace_of_fixedSpace_eq_bot (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a)
    (hE : fixedSpace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥) :
    iSupIndep ![fixedSpace ρ (Subgroup.zpowers a), fixedSpace ρ (Subgroup.zpowers b),
      fixedSpace ρ (Subgroup.zpowers (a * b)), fixedSpace ρ (Subgroup.zpowers (a * b⁻¹))] := by
  have h := (iSupIndep_fixedSpace_hyperplanes_E9 ρ ha hb hab hnot hE).comp
    (bijective_zpowers_lineGen ha hb hab hnot).1
  convert h using 1
  funext i
  fin_cases i <;> rfl

theorem finrank_eq_sum_fixedSpace_of_fixedSpace_eq_bot [Module.Finite (ZMod 2) W]
    (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : Commute a b)
    (hnot : b ∉ Subgroup.zpowers a)
    (hE : fixedSpace ρ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥) :
    Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) +
        Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers b)) +
        Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers (a * b))) +
        Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers (a * b⁻¹))) := by
  rw [← finrank_top (ZMod 2) W]
  exact finrank_eq_sum_four_of_bijective (bijective_zpowers_lineGen ha hb hab hnot)
    (iSupIndep_fixedSpace_hyperplanes_E9 ρ ha hb hab hnot hE)
    (iSup_fixedSpace_hyperplanes_E9 ρ ha hb hab hnot)

theorem finrank_commSpace_eq_sum [Module.Finite (ZMod 2) W] (ha : orderOf a = 3)
    (hb : orderOf b = 3) (hab : Commute a b) (hnot : b ∉ Subgroup.zpowers a) :
    Module.finrank (ZMod 2) (commSpace ρ (Subgroup.zpowers a)) =
      Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers b)) +
        Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers (a * b))) +
        Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers (a * b⁻¹))) := by
  obtain ⟨hEea, -⟩ := isElemAbelian_zpowers_sup_of_commute ha hb hab hnot
  obtain ⟨hind, hsup⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.HyperplaneDecompositionOnCommSpace.decomposition (p := 3)
      (by decide) ρ _ (Subgroup.zpowers a) hEea le_sup_left
      (fun k hk z hz => hEea.comm hk (Subgroup.mem_sup_left hz))
      (by rw [Nat.card_zpowers, ha]; decide)
  have h : Module.finrank (ZMod 2) (commSpace ρ (Subgroup.zpowers a)) =
      Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers a)) +
        Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers b)) +
        Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers (a * b))) +
        Module.finrank (ZMod 2)
          ↥(commSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers (a * b⁻¹))) :=
    finrank_eq_sum_four_of_bijective (bijective_zpowers_lineGen ha hb hab hnot) hind hsup
  rw [h, commSpace_inf_fixedSpace_eq_bot ρ ha, finrank_bot, zero_add]

end Decomposition

end CFSG.RankThree.GF2n.Parrott.Remarks
