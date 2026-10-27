module

public import CFSG.Quasithin.Vol2.Ch10SecCWF
public import CFSG.Quasithin.Background.G13Two
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix

namespace G16

variable {U : Type} [CommGroup U] {F : Type} [Field F] {Gm : Subgroup (MulAut U)}

@[expose] def zeroOn {s : ℕ} (J : Set (Fin s)) :
    Subgroup (Multiplicative (Fin s → Fin 2 → F)) where
  carrier := {x | ∀ j ∈ J, Multiplicative.toAdd x j = 0}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb j hj => by
    show Multiplicative.toAdd a j + Multiplicative.toAdd b j = 0
    rw [ha j hj, hb j hj, add_zero]
  inv_mem' := fun {a} ha j hj => by
    show -(Multiplicative.toAdd a j) = 0
    rw [ha j hj, neg_zero]

@[expose] noncomputable def crd {s : ℕ} (Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm)) :
    U →* Multiplicative (Fin s → Fin 2 → F) :=
  (AddMonoidHom.toMultiplicativeRight Θ.symm.toAddMonoidHom).comp (QuotientGroup.mk' (fixV Gm))

theorem toAdd_crd {s : ℕ} (Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm)) (u : U) :
    Multiplicative.toAdd (crd Θ u) = Θ.symm (Additive.ofMul (u : U ⧸ fixV Gm)) := rfl

theorem crd_eq_one_iff {s : ℕ} (Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm)) (u : U) :
    crd Θ u = 1 ↔ u ∈ fixV Gm := by
  rw [← QuotientGroup.eq_one_iff, ← toAdd_eq_zero, toAdd_crd, AddEquiv.map_eq_zero_iff]
  rfl

theorem crd_surjective {s : ℕ} (Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm))
    (x : Fin s → Fin 2 → F) : ∃ u : U, Multiplicative.toAdd (crd Θ u) = x := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul (Θ x))
  refine ⟨u, ?_⟩
  rw [toAdd_crd, show Additive.ofMul (u : U ⧸ fixV Gm) = Θ x by rw [hu]; rfl,
    AddEquiv.symm_apply_apply]

theorem toAdd_crd_apply {s : ℕ} {e' : ↥Gm ≃* SL(2, F)}
    {Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm)}
    (hΘ : ∀ (k : SL(2, F)) (x : Fin s → Fin 2 → F),
      Θ (fun j => k • x j) = Additive.ofMul (rho e' k (Additive.toMul (Θ x))))
    (h : ↥Gm) (u : U) :
    Multiplicative.toAdd (crd Θ ((h : MulAut U) u)) =
      fun j => e' h • Multiplicative.toAdd (crd Θ u) j := by
  apply Θ.injective
  rw [hΘ, toAdd_crd, toAdd_crd, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  show Additive.ofMul (((h : MulAut U) u : U) : U ⧸ fixV Gm) =
    Additive.ofMul (rho e' (e' h) (u : U ⧸ fixV Gm))
  rw [rho_mk, MulEquiv.symm_apply_apply]

theorem realizes_natural {e' : ↥Gm ≃* SL(2, F)} {s : ℕ}
    {Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm)}
    (hΘ : ∀ (k : SL(2, F)) (x : Fin s → Fin 2 → F),
      Θ (fun j => k • x j) = Additive.ofMul (rho e' k (Additive.toMul (Θ x))))
    (i : Fin s) :
    (FFModel.nat (StatedSL 2 F)).Realizes Gm ((zeroOn {j | j ≠ i}).comap (crd Θ))
      (fixV Gm) := by
  set eSL := specialLinearGroupEquivStatedSL 2 F with heSL
  set Wi := (zeroOn {j | j ≠ i}).comap (crd Θ) with hWi
  let ψ : ↥(StatedSL 2 F) →* ↥Gm := e'.symm.toMonoidHom.comp eSL.symm.toMonoidHom
  have hψ : ∀ γ, e' (ψ γ) = eSL.symm γ := fun γ => MulEquiv.apply_symm_apply _ _
  let ci : ↥Wi →* Multiplicative (Fin 2 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (Multiplicative.toAdd (crd Θ (u : U)) i)
      map_one' := by
        rw [Subgroup.coe_one, map_one]
        rfl
      map_mul' := fun a b => by
        rw [Subgroup.coe_mul, map_mul]
        rfl }
  have hci : ∀ u : ↥Wi, ci u = Multiplicative.ofAdd (Multiplicative.toAdd (crd Θ (u : U)) i) :=
    fun _ => rfl
  let β : ↥Wi →* ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 2 → F))).subgroupOf ⊤ :=
    (QuotientGroup.mk' _).comp (ci.codRestrict ⊤ fun _ => Subgroup.mem_top _)
  have hβ1 : ∀ (u : ↥Wi) (m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → F)))),
      β u = QuotientGroup.mk m ↔ ci u = m := fun u m => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.mem_bot, Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.codRestrict_apply,
      inv_mul_eq_one]
  have hZW : fixV Gm ≤ Wi := fun z hz j _ => by
    rw [(crd_eq_one_iff Θ z).2 hz]
    rfl
  dsimp only [FFModel.Realizes, FFModel.RealizesVia, FFModel.nat]
  refine ⟨ψ, fun h => ⟨eSL (e' h), ?_⟩, hZW, bot_le, fun h u hu j hj => ?_,
    fun h z hz => by rw [hz _ h.2]; exact hz, fun _ _ _ => Subgroup.mem_top _,
    fun γ m hm => ?_, β, ?_, ?_, ?_⟩
  · show e'.symm (eSL.symm (eSL (e' h))) = h
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  · rw [toAdd_crd_apply hΘ]
    show e' h • Multiplicative.toAdd (crd Θ u) j = 0
    rw [hu j hj, smul_eq_mulVec', Matrix.mulVec_zero]
  · rw [Subgroup.mem_bot] at hm ⊢
    rw [hm]
    show Multiplicative.ofAdd (_ *ᵥ (0 : Fin 2 → F)) = 1
    rw [Matrix.mulVec_zero]
    rfl
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu⟩ := crd_surjective Θ (Pi.single i (Multiplicative.toAdd (m : Multiplicative _)))
    have huW : u ∈ Wi := fun j hj => by rw [hu, Pi.single_eq_of_ne hj]
    refine ⟨⟨u, huW⟩, (hβ1 _ _).2 ?_⟩
    rw [hci]
    simp only [hu, Pi.single_eq_same, ofAdd_toAdd]
  · intro u
    constructor
    · intro h1
      have h2 : ci u = 1 := (hβ1 u 1).1 (h1.trans (QuotientGroup.mk_one _).symm)
      rw [hci, ofAdd_eq_one] at h2
      rw [← crd_eq_one_iff Θ, ← toAdd_eq_zero]
      funext j
      by_cases hj : j = i
      · subst hj
        exact h2
      · exact u.2 j hj
    · intro h1
      have h2 : ci u = 1 := by
        rw [hci, (crd_eq_one_iff Θ (u : U)).2 h1]
        rfl
      exact ((hβ1 u 1).2 h2).trans (QuotientGroup.mk_one _)
  · intro γ u m hu hm h1
    have hm' : ci u = m := (hβ1 u m).1 h1
    refine (hβ1 _ _).2 ?_
    rw [hci]
    show Multiplicative.ofAdd (Multiplicative.toAdd (crd Θ (((ψ γ : ↥Gm) : MulAut U) u)) i) =
      Multiplicative.ofAdd (((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (m : Multiplicative (Fin 2 → F)))
    rw [toAdd_crd_apply hΘ, hψ]
    beta_reduce
    rw [smul_eq_mulVec', ← hm', hci, toAdd_ofAdd]
    congr 2
    have h3 := specialLinearGroupEquivStatedSL_coe 2 F (eSL.symm γ)
    rw [MulEquiv.apply_symm_apply] at h3
    exact h3.symm

theorem exists_natural_sum [Finite F] {e' : ↥Gm ≃* SL(2, F)} {e : ℕ} (hcard : Nat.card F = 2 ^ e)
    {s : ℕ} {Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm)}
    (hΘ : ∀ (k : SL(2, F)) (x : Fin s → Fin 2 → F),
      Θ (fun j => k • x j) = Additive.ofMul (rho e' k (Additive.toMul (Θ x)))) :
    ∃ (s : ℕ) (W : Fin s → Subgroup U), (∀ i, fixV Gm ≤ W i) ∧
      (∀ i, W i ⊓ (fixV Gm ⊔ ⨆ (j : Fin s) (_ : j ≠ i), W j) = fixV Gm) ∧
      (fixV Gm ⊔ ⨆ i, W i) = ⊤ ∧ ∀ i, BinaryNaturalSL Gm (W i) (fixV Gm) 2 e := by
  set W : Fin s → Subgroup U := fun i => (zeroOn {j | j ≠ i}).comap (crd Θ) with hW
  have hZW : ∀ i, fixV Gm ≤ W i := fun i z hz j _ => by
    rw [(crd_eq_one_iff Θ z).2 hz]
    rfl
  have hzero : ∀ u : U, (∀ j, Multiplicative.toAdd (crd Θ u) j = 0) → u ∈ fixV Gm :=
    fun u h => by
      rw [← crd_eq_one_iff Θ u, ← toAdd_eq_zero]
      funext j
      exact h j
  refine ⟨s, W, hZW, fun i => ?_, ?_, fun i => ⟨F, inferInstance, inferInstance, hcard,
    realizes_natural hΘ i⟩⟩
  · refine le_antisymm ?_ (le_inf (hZW i) le_sup_left)
    rintro u ⟨hui, hu⟩
    have hN : fixV Gm ⊔ ⨆ (j : Fin s) (_ : j ≠ i), W j ≤ (zeroOn {i}).comap (crd Θ) := by
      refine sup_le (fun z hz j _ => ?_) (iSup₂_le fun j hj v hv j' hj' => ?_)
      · rw [(crd_eq_one_iff Θ z).2 hz]
        rfl
      · rw [Set.mem_singleton_iff] at hj'
        subst hj'
        exact hv _ (Ne.symm hj)
    have h1 : Multiplicative.toAdd (crd Θ u) i = 0 := hN hu i rfl
    refine hzero u fun j => ?_
    by_cases hj : j = i
    · subst hj
      exact h1
    · exact hui j hj
  · rw [eq_top_iff]
    intro u _
    set x := Multiplicative.toAdd (crd Θ u) with hx
    choose v hv using fun i => crd_surjective Θ (Pi.single i (x i))
    have hvW : ∀ i, v i ∈ W i := fun i j hj => by
      show Multiplicative.toAdd (crd Θ (v i)) j = 0
      rw [hv i, Pi.single_eq_of_ne hj]
    have hprod : crd Θ (∏ i, v i) = crd Θ u := by
      apply Multiplicative.toAdd.injective
      rw [map_prod, toAdd_prod]
      simp only [hv]
      exact Finset.univ_sum_single x
    have hz : u * (∏ i, v i)⁻¹ ∈ fixV Gm := by
      rw [← crd_eq_one_iff Θ, map_mul, map_inv, hprod, mul_inv_cancel]
    have e1 : u = u * (∏ i, v i)⁻¹ * ∏ i, v i := by group
    rw [e1]
    exact Subgroup.mul_mem_sup hz
      (Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (hvW i))

theorem asG16_of_G13
    (hG13 : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], G1.Theorem_G_1_3 F 2 (le_refl 2)) :
    ASInputs.AS_G_1_6 := by
  intro U _ _ hU Gm R e _ hF hR hgen hC
  obtain ⟨F, _, _, hcard, ⟨e0⟩⟩ := hF
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := e) (by rw [← Nat.card_eq_fintype_card, hcard])
  obtain ⟨e', he'⟩ := exists_mulEquiv_Rg hR e0
  obtain ⟨s, Θ, hΘ⟩ := exists_equiv_rho (hG13 F) hU hR.1 he' hC hgen
  exact exists_natural_sum hcard hΘ

end G16

theorem asG16_holds : ASInputs.AS_G_1_6 :=
  G16.asG16_of_G13 fun _ _ _ _ => G1.theorem_G_1_3_two

end CFSG.Quasithin.Vol2.Ch10
