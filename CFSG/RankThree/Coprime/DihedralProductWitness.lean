module

public import CFSG.RankThree.Coprime.InvariantAbelianDetection
public import CFSG.RankThree.LocalRank.ElementaryTwoWeights
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG.RankThree.LocalRank
open scoped IsMulCommutative

@[expose] def negationAction (p : ℕ) :
    Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod p)) where
  toFun e := if Multiplicative.toAdd e = 0 then 1 else MulEquiv.inv (Multiplicative (ZMod p))
  map_one' := by simp
  map_mul' := by
    intro x y
    have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have hinv : MulEquiv.inv (Multiplicative (ZMod p)) * MulEquiv.inv (Multiplicative (ZMod p)) =
        1 := by
      ext c
      simp
    rcases h2 (Multiplicative.toAdd x) with hx | hx <;>
      rcases h2 (Multiplicative.toAdd y) with hy | hy <;>
      simp [hx, hy, hinv, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem toAdd_negationAction (p : ℕ) (e : Multiplicative (ZMod 2))
    (c : Multiplicative (ZMod p)) :
    Multiplicative.toAdd (negationAction p e c) =
      (-1 : ZMod p) ^ (Multiplicative.toAdd e).val * Multiplicative.toAdd c := by
  have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h2 (Multiplicative.toAdd e) with he | he
  · have he' : e = 1 := toAdd_eq_zero.mp he
    simp [negationAction, he']
  · have he' : e ≠ 1 := by
      intro h
      rw [h, toAdd_one] at he
      exact absurd he (by decide)
    have h1 : (1 : ZMod 2).val = 1 := rfl
    simp [negationAction, he', he, h1]

section Representation

variable {P : Type*} [Group P] {A : Type*} [Group A] [MulDistribMulAction A P]

@[expose] noncomputable def invariantSubgroupRep (p : ℕ) [Fact p.Prime] (D : Subgroup P)
    [IsElementaryAbelian p D] (hD : ∀ a : A, ∀ x ∈ D, a • x ∈ D) :
    Representation (ZMod p) A (Additive D) where
  toFun a := AddMonoidHom.toZModLinearMap p
    { toFun := fun v => Additive.ofMul
        (⟨a • ((Additive.toMul v : D) : P), hD a _ (Additive.toMul v).2⟩ : D)
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp
      map_add' := by
        intro v w
        apply Additive.toMul.injective
        apply Subtype.ext
        simp [smul_mul'] }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  map_mul' := by
    intro a b
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [mul_smul]

theorem coe_toMul_invariantSubgroupRep (p : ℕ) [Fact p.Prime] (D : Subgroup P)
    [IsElementaryAbelian p D] (hD : ∀ a : A, ∀ x ∈ D, a • x ∈ D) (a : A) (v : Additive D) :
    ((Additive.toMul (invariantSubgroupRep p D hD a v) : D) : P) =
      a • ((Additive.toMul v : D) : P) :=
  rfl

end Representation

section Weights

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_basis_weight_vectors {A : Type*} [CommGroup A] [Finite A]
    [Module (ZMod 2) (Additive A)] {K : Type*} [Field K] (hK : (2 : K) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K A V)
    (hρ : Function.Injective ρ) {n : ℕ} (hn : Module.finrank (ZMod 2) (Additive A) = n) :
    ∃ (a : Module.Basis (Fin n) (ZMod 2) (Additive A)) (u : Fin n → V), LinearIndependent K u ∧
      ∀ (b : A) (j : Fin n), ρ b (u j) = (-1 : K) ^ (a.repr (Additive.ofMul b) j).val • u j := by
  classical
  let := Fintype.ofFinite A
  have : Finite (Module.Dual (ZMod 2) (Additive A)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive A) => (f : Additive A → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive A))
  have : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hspan := (injective_iff_span_signWeightSpace ρ hK).mp hρ
  obtain ⟨s, hsS, hsspan, hsli⟩ := exists_linearIndependent (ZMod 2)
    {χ : Module.Dual (ZMod 2) (Additive A) | signWeightSpace ρ χ ≠ ⊥}
  let χ0 : Module.Basis s (ZMod 2) (Module.Dual (ZMod 2) (Additive A)) :=
    Module.Basis.mk hsli (by rw [Subtype.range_coe, hsspan, hspan])
  have hcard : Fintype.card s = n := by
    rw [← Module.finrank_eq_card_basis χ0, Subspace.dual_finrank_eq, hn]
  let χB := χ0.reindex (Fintype.equivFinOfCardEq hcard)
  let aB := χB.dualBasis.map (Module.evalEquiv (ZMod 2) (Additive A)).symm
  have hχa : ∀ j, χB j = aB.coord j := by
    intro j
    apply aB.ext
    intro i
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    have h1 : χB j (aB i) = (Module.evalEquiv (ZMod 2) (Additive A) (aB i)) (χB j) := rfl
    rw [h1]
    simp only [aB, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      Module.Basis.dualBasis_apply_self]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, h.symm]
  have hmem : ∀ j, signWeightSpace ρ (χB j) ≠ ⊥ := by
    intro j
    have : χB j ∈ s := by
      simp only [χB, Module.Basis.reindex_apply, χ0, Module.Basis.mk_apply]
      exact Subtype.mem _
    exact hsS this
  choose u hu hu0 using fun j => Submodule.exists_mem_ne_zero_of_ne_bot (hmem j)
  refine ⟨aB, u, ?_, ?_⟩
  · exact iSupIndep.linearIndependent _ ((iSupIndep_signWeightSpace ρ hK).comp χB.injective) hu
      hu0
  · intro b j
    rw [(mem_signWeightSpace ρ (χB j) (u j)).mp (hu j) b, hχa j, Module.Basis.coord_apply]

end Weights

section Semidirect

variable {P : Type*} [Group P] {A : Type*} [CommGroup A] [MulDistribMulAction A P]

theorem nonempty_semidirect_mulEquiv_pi {p n : ℕ} [Module (ZMod 2) (Additive A)]
    (Λ : Multiplicative (Fin n → ZMod p) →* P) (hΛ : Function.Injective Λ)
    (aB : Module.Basis (Fin n) (ZMod 2) (Additive A))
    (hsmul : ∀ (b : A) (c : Fin n → ZMod p), b • Λ (Multiplicative.ofAdd c) =
      Λ (Multiplicative.ofAdd fun j => (-1 : ZMod p) ^ (aB.repr (Additive.ofMul b) j).val * c j)) :
    Nonempty ((Λ.range.map (SemidirectProduct.inl : P →* P ⋊[MulDistribMulAction.toMulAut A P] A) ⊔
        (SemidirectProduct.inr : A →* P ⋊[MulDistribMulAction.toMulAut A P] A).range :
          Subgroup (P ⋊[MulDistribMulAction.toMulAut A P] A)) ≃*
      (Fin n → Multiplicative (ZMod p) ⋊[negationAction p] Multiplicative (ZMod 2))) := by
  classical
  let Avec : (Fin n → ZMod 2) → A := fun e => Additive.toMul (aB.equivFun.symm e)
  have hAvec_add : ∀ e e', Avec (e + e') = Avec e * Avec e' := by
    intro e e'
    simp only [Avec, map_add, toMul_add]
  have hAvec_zero : Avec 0 = 1 := by simp [Avec]
  have hrepr : ∀ e j, aB.repr (Additive.ofMul (Avec e)) j = e j := by
    intro e j
    simp only [Avec, ofMul_toMul]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hAvec_inj : ∀ e, Avec e = 1 → e = 0 := by
    intro e he
    have h : aB.equivFun.symm e = 0 := by
      have := congrArg Additive.ofMul he
      rwa [ofMul_one] at this
    exact (LinearEquiv.map_eq_zero_iff _).mp h
  let Ψ : (Fin n → Multiplicative (ZMod p) ⋊[negationAction p] Multiplicative (ZMod 2)) →*
      P ⋊[MulDistribMulAction.toMulAut A P] A :=
    { toFun := fun x => ⟨Λ (Multiplicative.ofAdd fun i => Multiplicative.toAdd (x i).left),
        Avec fun i => Multiplicative.toAdd (x i).right⟩
      map_one' := by
        apply SemidirectProduct.ext
        · simp only [Pi.one_apply, SemidirectProduct.one_left, toAdd_one]
          rw [show (fun _ : Fin n => (0 : ZMod p)) = 0 from rfl, ofAdd_zero, map_one]
        · simp only [Pi.one_apply, SemidirectProduct.one_right, toAdd_one]
          exact hAvec_zero
      map_mul' := by
        intro x y
        apply SemidirectProduct.ext
        · simp only [Pi.mul_apply, SemidirectProduct.mul_left, toAdd_mul, toAdd_negationAction,
            MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
          rw [hsmul, ← map_mul, ← ofAdd_add]
          congr 2
          funext j
          simp only [Pi.add_apply, hrepr]
        · simp only [Pi.mul_apply, SemidirectProduct.mul_right, toAdd_mul]
          exact hAvec_add _ _ }
  have hΨ : ∀ x, Ψ x = ⟨Λ (Multiplicative.ofAdd fun i => Multiplicative.toAdd (x i).left),
        Avec fun i => Multiplicative.toAdd (x i).right⟩ := fun x => rfl
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hΨ] at hx
    have hl := congrArg SemidirectProduct.left hx
    have hr := congrArg SemidirectProduct.right hx
    simp only [SemidirectProduct.one_left, SemidirectProduct.one_right] at hl hr
    have hc : (fun i => Multiplicative.toAdd (x i).left) = 0 := by
      have := hΛ (hl.trans (map_one Λ).symm)
      simpa using this
    have he := hAvec_inj _ hr
    funext i
    apply SemidirectProduct.ext
    · have := congrFun hc i
      simpa using this
    · have := congrFun he i
      simpa using this
  have hrange : Ψ.range = (Λ.range.map (SemidirectProduct.inl :
        P →* P ⋊[MulDistribMulAction.toMulAut A P] A) ⊔
      (SemidirectProduct.inr : A →* P ⋊[MulDistribMulAction.toMulAut A P] A).range) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [← SemidirectProduct.inl_left_mul_inr_right (Ψ x)]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, ⟨_, rfl⟩, rfl⟩)
        (Subgroup.mem_sup_right ⟨_, rfl⟩)
    · refine sup_le ?_ ?_
      · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
        refine ⟨fun i => ⟨Multiplicative.ofAdd (Multiplicative.toAdd c i), 1⟩, ?_⟩
        rw [hΨ]
        apply SemidirectProduct.ext
        · simp
        · simp only [SemidirectProduct.right_inl, toAdd_one]
          exact hAvec_zero
      · rintro _ ⟨b, rfl⟩
        refine ⟨fun i => ⟨1, Multiplicative.ofAdd (aB.repr (Additive.ofMul b) i)⟩, ?_⟩
        rw [hΨ]
        apply SemidirectProduct.ext
        · simp only [toAdd_one, SemidirectProduct.left_inr]
          rw [show (fun _ : Fin n => (0 : ZMod p)) = 0 from rfl, ofAdd_zero, map_one]
        · simp only [SemidirectProduct.right_inr, toAdd_ofAdd, Avec]
          rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply, toMul_ofMul]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end Semidirect

section Construction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {P : Type*} [Group P] {A : Type*} [CommGroup A] [MulDistribMulAction A P]

theorem dihedral_product_of_weight_vectors {p : ℕ} [Fact p.Prime] {n : ℕ}
    [Module (ZMod 2) (Additive A)] (D : Subgroup P) [IsElementaryAbelian p D]
    (hDinv : ∀ a : A, ∀ x ∈ D, a • x ∈ D) (aB : Module.Basis (Fin n) (ZMod 2) (Additive A))
    (u : Fin n → Additive D) (hli : LinearIndependent (ZMod p) u)
    (hw : ∀ (b : A) (j : Fin n), invariantSubgroupRep p D hDinv b (u j) =
      (-1 : ZMod p) ^ (aB.repr (Additive.ofMul b) j).val • u j) :
    ∃ (U : Subgroup P) (_ : IsElementaryAbelian p U),
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) ∧ Nat.card U = p ^ n ∧
      ∃ uB : Module.Basis (Fin n) (ZMod p) (Additive U),
        (∀ i j, Additive.toMul (aB i) • ((Additive.toMul (uB j) : U) : P) =
          if i = j then ((Additive.toMul (uB j) : U) : P)⁻¹
          else ((Additive.toMul (uB j) : U) : P)) ∧
        Nonempty ((U.map (SemidirectProduct.inl :
            P →* P ⋊[MulDistribMulAction.toMulAut A P] A) ⊔
          (SemidirectProduct.inr : A →* P ⋊[MulDistribMulAction.toMulAut A P] A).range :
            Subgroup (P ⋊[MulDistribMulAction.toMulAut A P] A)) ≃*
          (Fin n → Multiplicative (ZMod p) ⋊[negationAction p] Multiplicative (ZMod 2))) := by
  classical
  let Λ0 : Multiplicative (Fin n → ZMod p) →* D :=
    AddMonoidHom.toMultiplicativeLeft (Fintype.linearCombination (ZMod p) u).toAddMonoidHom
  let Λ : Multiplicative (Fin n → ZMod p) →* P := D.subtype.comp Λ0
  have hΛ : ∀ c, Λ (Multiplicative.ofAdd c) = ((Additive.toMul (∑ i, c i • u i) : D) : P) := by
    intro c
    rfl
  have hΛinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [← ofAdd_toAdd x, hΛ] at hx
    have h0 : ∑ i, (Multiplicative.toAdd x) i • u i = 0 := by
      have h1 : Additive.toMul (∑ i, (Multiplicative.toAdd x) i • u i) = 1 := Subtype.ext hx
      exact h1
    have h2 := Fintype.linearIndependent_iff.mp hli _ h0
    rw [← ofAdd_toAdd x]
    have h3 : Multiplicative.toAdd x = 0 := funext h2
    rw [h3, ofAdd_zero]
  have hsmul : ∀ (b : A) (c : Fin n → ZMod p), b • Λ (Multiplicative.ofAdd c) =
      Λ (Multiplicative.ofAdd fun j =>
        (-1 : ZMod p) ^ (aB.repr (Additive.ofMul b) j).val * c j) := by
    intro b c
    rw [hΛ, hΛ, ← coe_toMul_invariantSubgroupRep p D hDinv]
    congr 3
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hw, smul_smul, mul_comm]
  let U : Subgroup P := Λ.range
  have hUexp : Monoid.exponent U ∣ p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, c, rfl⟩
    apply Subtype.ext
    have hc : c ^ p = 1 := by
      have h := ZModModule.char_nsmul_eq_zero p (Multiplicative.toAdd c)
      rw [← ofAdd_toAdd c, ← ofAdd_nsmul, h, ofAdd_zero]
    change Λ c ^ p = 1
    rw [← map_pow, hc, map_one]
  let hUel : IsElementaryAbelian p U := ⟨hUexp⟩
  have hUinv : ∀ a : A, ∀ x ∈ U, a • x ∈ U := by
    rintro a _ ⟨c, rfl⟩
    rw [← ofAdd_toAdd c, hsmul]
    exact ⟨_, rfl⟩
  let e0 : Multiplicative (Fin n → ZMod p) ≃* U := MonoidHom.ofInjective hΛinj
  have hcard : Nat.card U = p ^ n := by
    rw [← Nat.card_congr e0.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
  let eAdd : Additive U ≃+ (Fin n → ZMod p) := MulEquiv.toAdditiveLeft e0.symm
  let eLin : Additive U ≃ₗ[ZMod p] (Fin n → ZMod p) :=
    LinearEquiv.ofBijective (eAdd.toAddMonoidHom.toZModLinearMap p) eAdd.bijective
  let uB := Module.Basis.ofEquivFun eLin
  have huB : ∀ j, ((Additive.toMul (uB j) : U) : P) = ((Additive.toMul (u j) : D) : P) := by
    intro j
    have h1 : uB j = Additive.ofMul (e0 (Multiplicative.ofAdd (Pi.single j 1))) := by
      rw [Module.Basis.coe_ofEquivFun, LinearEquiv.symm_apply_eq]
      simp [eLin, eAdd]
    rw [h1, toMul_ofMul, MonoidHom.ofInjective_apply, hΛ, ← Fintype.linearCombination_apply,
      Fintype.linearCombination_apply_single, one_smul]
  refine ⟨U, hUel, hUinv, hcard, uB, fun i j => ?_,
    nonempty_semidirect_mulEquiv_pi Λ hΛinj aB hsmul⟩
  rw [huB, ← coe_toMul_invariantSubgroupRep p D hDinv, hw, ofMul_toMul, Module.Basis.repr_self,
    Finsupp.single_apply]
  split_ifs with h
  · have h1 : (1 : ZMod 2).val = 1 := rfl
    rw [h1, pow_one, show ((-1 : ZMod p) • u j) = -u j from neg_one_smul _ _, toMul_neg,
      Subgroup.coe_inv]
  · rw [ZMod.val_zero, pow_zero, show ((1 : ZMod p) • u j) = u j from one_smul _ _]

end Construction

theorem class_two_dihedral_product_witness {p : ℕ} [hpF : Fact p.Prime] (hodd : Odd p)
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (hexp : Monoid.exponent P ∣ p)
    (hclass : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥)
    {A : Type*} [CommGroup A] [Finite A] [Module (ZMod 2) (Additive A)] (n : ℕ)
    (hA : Nat.card A = 2 ^ n) [MulDistribMulAction A P] [FaithfulSMul A P] :
    ∃ (U : Subgroup P) (_ : IsElementaryAbelian p U),
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) ∧ Nat.card U = p ^ n ∧
      ∃ (a : Module.Basis (Fin n) (ZMod 2) (Additive A))
        (u : Module.Basis (Fin n) (ZMod p) (Additive U)),
        (∀ i j, Additive.toMul (a i) • ((Additive.toMul (u j) : U) : P) =
          if i = j then ((Additive.toMul (u j) : U) : P)⁻¹
          else ((Additive.toMul (u j) : U) : P)) ∧
        Nonempty ((U.map (SemidirectProduct.inl :
            P →* P ⋊[MulDistribMulAction.toMulAut A P] A) ⊔
          (SemidirectProduct.inr : A →* P ⋊[MulDistribMulAction.toMulAut A P] A).range :
            Subgroup (P ⋊[MulDistribMulAction.toMulAut A P] A)) ≃*
          (Fin n → Multiplicative (ZMod p) ⋊[negationAction p] Multiplicative (ZMod 2))) := by
  classical
  have hexp' : ∀ x : P, x ^ p = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp
  have hcomm : commutator P ≤ center P := by
    have h : ⁅commutator P, (⊤ : Subgroup P)⁆ = ⊥ := by
      rw [← Subgroup.top_lowerCentralSeries_one, ← Subgroup.lowerCentralSeries_succ]
      exact hclass
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] at h
    exact h
  obtain ⟨⟨D, hD⟩, hmax⟩ :=
    elementary_two_invariant_abelian_detection (A := A) hpF.out hodd hP hexp' hcomm
  obtain ⟨hDel, -, -, hfaith⟩ := hmax D hD
  have hDinv := hD.prop.1
  have hρ : Function.Injective (invariantSubgroupRep p D hDinv) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine hfaith inferInstance a fun x hx => ?_
    have h1 := LinearMap.congr_fun ha (Additive.ofMul (⟨x, hx⟩ : D))
    have h2 := congrArg (fun v : Additive D => ((Additive.toMul v : D) : P)) h1
    simpa [coe_toMul_invariantSubgroupRep] using h2
  have hK : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have hp2 : p = 2 := le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hpF.out.two_le
    rw [hp2] at hodd
    exact absurd hodd (by decide)
  have : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hn : Module.finrank (ZMod 2) (Additive A) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_congr Additive.toMul, hA, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have : FiniteDimensional (ZMod p) (Additive D) := Module.Finite.of_finite
  obtain ⟨aB, u, hli, hw⟩ := exists_basis_weight_vectors hK _ hρ hn
  obtain ⟨U, hU, hUinv, hUcard, uB, hrel, hiso⟩ :=
    dihedral_product_of_weight_vectors D hDinv aB u hli hw
  exact ⟨U, hU, hUinv, hUcard, aB, uB, hrel, hiso⟩

end CFSG.RankThree.Coprime
