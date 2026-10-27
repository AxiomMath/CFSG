module

public import CFSG.Quasithin.Background.F918P0
public import CFSG.Quasithin.Background.F918Z0Def

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix

section Realize

@[expose] noncomputable def topBotQuotEquiv (M : Type) [CommGroup M] :
    (↥(⊤ : Subgroup M) ⧸ ((⊥ : Subgroup M).subgroupOf ⊤)) ≃* M :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (⊤ : Subgroup M))).trans
    ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)

theorem topBotQuotEquiv_mk (M : Type) [CommGroup M] (m : ↥(⊤ : Subgroup M)) :
    topBotQuotEquiv M (QuotientGroup.mk m) = (m : M) := rfl

theorem realizes_tensorNat_of_tensorData {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {d : ℕ} {K : Type} [Field K]
    (π : (↥(StatedSL d K) × ↥(StatedSL d K)) →* ↥H) (hπ : Function.Surjective π)
    (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) K))
    (hβ : ∀ (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (v : V),
      β ((π γ : MulAut V) v) = tensorAct d K γ (β v)) :
    (FFModel.tensorNat d K).Realizes H ⊤ ⊥ := by
  let E : Type := Multiplicative (Matrix (Fin d) (Fin d) K)
  let e : ↥(⊤ : Subgroup V) ≃* (↥(⊤ : Subgroup E) ⧸ (⊥ : Subgroup E).subgroupOf ⊤) :=
    (Subgroup.topEquiv.trans β).trans (topBotQuotEquiv E).symm
  have hker : ∀ (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (m : E), m ∈ (⊥ : Subgroup E) →
      tensorAct d K γ m ∈ (⊥ : Subgroup E) := by
    intro γ m hm
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm]
    apply Multiplicative.toAdd.injective
    simp [tensorAct]
  have hequi : ∀ (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (u : ↥(⊤ : Subgroup V))
      (m : ↥(⊤ : Subgroup E)) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ (⊤ : Subgroup V))
      (hm : tensorAct d K γ (m : E) ∈ (⊤ : Subgroup E)),
      e.toMonoidHom u = QuotientGroup.mk m →
        e.toMonoidHom ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
          QuotientGroup.mk ⟨tensorAct d K γ (m : E), hm⟩ := by
    intro γ u m hu hm hum
    apply (topBotQuotEquiv E).injective
    have h1 : β (u : V) = (m : E) := by
      have := congrArg (topBotQuotEquiv E) hum
      simpa [e, topBotQuotEquiv_mk] using this
    show β ((π γ : MulAut V) (u : V)) = tensorAct d K γ (m : E)
    rw [hβ γ (u : V), h1]
  refine ⟨π, hπ, bot_le, bot_le, fun h u _ => trivial, ?_, fun γ m _ => trivial, hker,
    e.toMonoidHom, e.surjective, ?_, hequi⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz]
    exact map_one (h : MulAut V)
  · intro u
    rw [Subgroup.mem_bot]
    change e u = 1 ↔ (u : V) = 1
    rw [map_eq_one_iff e e.injective]
    exact Subtype.ext_iff

theorem omega4PlusModule_of_tensorData {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (π : (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) →* ↥H) (hπ : Function.Surjective π)
    (β : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) K))
    (hβ : ∀ (γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) (v : V),
      β ((π γ : MulAut V) v) = tensorAct 2 K γ (β v)) :
    Omega4PlusModule H n :=
  ⟨K, inferInstance, inferInstance, hK, realizes_tensorNat_of_tensorData π hπ β hβ⟩

theorem tensorNatL32_of_tensorData {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (π : (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))) →* ↥H) (hπ : Function.Surjective π)
    (β : V ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hβ : ∀ (γ : ↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))) (v : V),
      β ((π γ : MulAut V) v) = tensorAct 3 (ZMod 2) γ (β v)) :
    TensorNatL32 H :=
  realizes_tensorNat_of_tensorData π hπ β hβ

end Realize

section Transport

variable {F K : Type} [Field F] [Field K]

@[expose] def glMapEquiv (d : ℕ) (φ : F ≃+* K) :
    Matrix.GeneralLinearGroup (Fin d) F ≃* Matrix.GeneralLinearGroup (Fin d) K :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin d) φ).toMulEquiv

theorem coe_glMapEquiv (d : ℕ) (φ : F ≃+* K) (A : Matrix.GeneralLinearGroup (Fin d) F) :
    ((glMapEquiv d φ A : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) F).map φ := rfl

theorem det_glMapEquiv (d : ℕ) (φ : F ≃+* K) (A : Matrix.GeneralLinearGroup (Fin d) F) :
    ((glMapEquiv d φ A : Matrix.GeneralLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K).det = φ (A : Matrix (Fin d) (Fin d) F).det := by
  rw [coe_glMapEquiv]
  exact (RingHom.map_det φ.toRingHom (A : Matrix (Fin d) (Fin d) F)).symm

theorem map_statedSL_glMapEquiv (d : ℕ) (φ : F ≃+* K) :
    (StatedSL d F).map (glMapEquiv d φ).toMonoidHom = StatedSL d K := by
  unfold StatedSL
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨A, hA, rfl⟩
    show ((glMapEquiv d φ A : Matrix.GeneralLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K).det = 1
    rw [det_glMapEquiv, hA, map_one]
  · intro hB
    refine ⟨(glMapEquiv d φ).symm B, ?_, (glMapEquiv d φ).apply_symm_apply B⟩
    have h := det_glMapEquiv d φ ((glMapEquiv d φ).symm B)
    rw [(glMapEquiv d φ).apply_symm_apply B, hB] at h
    exact φ.injective (by rw [← h, map_one])

@[expose] noncomputable def statedSLMapEquiv (d : ℕ) (φ : F ≃+* K) :
    ↥(StatedSL d F) ≃* ↥(StatedSL d K) :=
  ((glMapEquiv d φ).subgroupMap (StatedSL d F)).trans
    (MulEquiv.subgroupCongr (map_statedSL_glMapEquiv d φ))

theorem coe_statedSLMapEquiv (d : ℕ) (φ : F ≃+* K) (A : ↥(StatedSL d F)) :
    (((statedSLMapEquiv d φ A : ↥(StatedSL d K)) : Matrix.GeneralLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) =
      ((A : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F).map φ := rfl

@[expose] def matMapEquiv (d : ℕ) (φ : F ≃+* K) :
    Multiplicative (Matrix (Fin d) (Fin d) F) ≃* Multiplicative (Matrix (Fin d) (Fin d) K) :=
  AddEquiv.toMultiplicative (AddEquiv.mapMatrix φ.toAddEquiv)

theorem matMapEquiv_tensorAct (d : ℕ) (φ : F ≃+* K)
    (γ : ↥(StatedSL d F) × ↥(StatedSL d F))
    (X : Multiplicative (Matrix (Fin d) (Fin d) F)) :
    matMapEquiv d φ (tensorAct d F γ X) =
      tensorAct d K (statedSLMapEquiv d φ γ.1, statedSLMapEquiv d φ γ.2) (matMapEquiv d φ X) := by
  apply Multiplicative.toAdd.injective
  simp [matMapEquiv, tensorAct, Matrix.map_mul, Matrix.transpose_map, coe_statedSLMapEquiv]

theorem tensorData_transport {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {d : ℕ}
    (φ : F ≃+* K)
    (π : (↥(StatedSL d F) × ↥(StatedSL d F)) →* ↥H) (hπ : Function.Surjective π)
    (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F))
    (hβ : ∀ (γ : ↥(StatedSL d F) × ↥(StatedSL d F)) (v : V),
      β ((π γ : MulAut V) v) = tensorAct d F γ (β v)) :
    ∃ (π' : (↥(StatedSL d K) × ↥(StatedSL d K)) →* ↥H) (_ : Function.Surjective π')
      (β' : V ≃* Multiplicative (Matrix (Fin d) (Fin d) K)),
      ∀ (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (v : V),
        β' ((π' γ : MulAut V) v) = tensorAct d K γ (β' v) := by
  let e : (↥(StatedSL d F) × ↥(StatedSL d F)) ≃* (↥(StatedSL d K) × ↥(StatedSL d K)) :=
    (statedSLMapEquiv d φ).prodCongr (statedSLMapEquiv d φ)
  refine ⟨π.comp e.symm.toMonoidHom, hπ.comp e.symm.surjective, β.trans (matMapEquiv d φ),
    fun γ v => ?_⟩
  have h1 : e (e.symm γ) = γ := e.apply_symm_apply γ
  have h2 := matMapEquiv_tensorAct d φ (e.symm γ) (β v)
  change matMapEquiv d φ (β ((π (e.symm γ) : MulAut V) v)) =
    tensorAct d K γ (matMapEquiv d φ (β v))
  rw [hβ, h2]
  have h3 : (statedSLMapEquiv d φ (e.symm γ).1, statedSLMapEquiv d φ (e.symm γ).2) = γ := h1
  rw [h3]

end Transport

section CardEq

theorem tensorData_of_card_eq {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {d : ℕ}
    {F K : Type} [Field F] [Field K] [Finite F] [Finite K] (hFK : Nat.card F = Nat.card K)
    (π : (↥(StatedSL d F) × ↥(StatedSL d F)) →* ↥H) (hπ : Function.Surjective π)
    (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F))
    (hβ : ∀ (γ : ↥(StatedSL d F) × ↥(StatedSL d F)) (v : V),
      β ((π γ : MulAut V) v) = tensorAct d F γ (β v)) :
    ∃ (π' : (↥(StatedSL d K) × ↥(StatedSL d K)) →* ↥H) (_ : Function.Surjective π')
      (β' : V ≃* Multiplicative (Matrix (Fin d) (Fin d) K)),
      ∀ (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (v : V),
        β' ((π' γ : MulAut V) v) = tensorAct d K γ (β' v) := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card F = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hFK
  exact tensorData_transport (FiniteField.ringEquivOfCardEq hc) π hπ β hβ

theorem tensorNatL32_of_tensorData_of_card_two {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (π : (↥(StatedSL 3 F) × ↥(StatedSL 3 F)) →* ↥H) (hπ : Function.Surjective π)
    (β : V ≃* Multiplicative (Matrix (Fin 3) (Fin 3) F))
    (hβ : ∀ (γ : ↥(StatedSL 3 F) × ↥(StatedSL 3 F)) (v : V),
      β ((π γ : MulAut V) v) = tensorAct 3 F γ (β v)) :
    TensorNatL32 H := by
  obtain ⟨π', hπ', β', hβ'⟩ :=
    tensorData_of_card_eq (K := ZMod 2) (by rw [hF, Nat.card_zmod]) π hπ β hβ
  exact tensorNatL32_of_tensorData π' hπ' β' hβ'

end CardEq

section FromModel

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] {d r : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}

theorem IsMatModel.rho_injective (hM : IsMatModel D X β ρ σ) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : ∀ v : V, (g : MulAut V) v = v := by
    intro v
    apply β.injective
    rw [hM.hρ g v, hg]
    simp
  exact Subtype.ext (MulEquiv.ext h1)

theorem IsMatModel.sigma_injective (hM : IsMatModel D X β ρ σ) : Function.Injective σ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ∀ v : V, (x : MulAut V) v = v := by
    intro v
    apply β.injective
    rw [hM.hσ x v, hx]
    simp
  exact Subtype.ext (MulEquiv.ext h1)

end FromModel

section FromSqModel

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] {d : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem exists_tensorData_of_matModel (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (hM : IsMatModel D X β ρ σ) (hρ : ρ.range = StatedSL d F) (hσ : σ.range = StatedSL d F) :
    ∃ π : (↥(StatedSL d F) × ↥(StatedSL d F)) →* ↥(D ⊔ X), Function.Surjective π ∧
      ∀ (γ : ↥(StatedSL d F) × ↥(StatedSL d F)) (v : V),
        β ((π γ : MulAut V) v) = tensorAct d F γ (β v) := by
  let eρ : ↥D ≃* ↥(StatedSL d F) :=
    (MonoidHom.ofInjective hM.rho_injective).trans (MulEquiv.subgroupCongr hρ)
  let eσ : ↥X ≃* ↥(StatedSL d F) :=
    (MonoidHom.ofInjective hM.sigma_injective).trans (MulEquiv.subgroupCongr hσ)
  let π₀ : (↥(StatedSL d F) × ↥(StatedSL d F)) →* MulAut V :=
    (D.subtype.comp eρ.symm.toMonoidHom).noncommCoprod (X.subtype.comp eσ.symm.toMonoidHom)
      (fun g h => hcomm _ (eρ.symm g).2 _ (eσ.symm h).2)
  have hπ₀ : ∀ γ : ↥(StatedSL d F) × ↥(StatedSL d F),
      π₀ γ = ((eρ.symm γ.1 : ↥D) : MulAut V) * ((eσ.symm γ.2 : ↥X) : MulAut V) := fun γ => rfl
  have hmem : ∀ γ : ↥(StatedSL d F) × ↥(StatedSL d F), π₀ γ ∈ D ⊔ X :=
    fun γ => Subgroup.mul_mem_sup (eρ.symm γ.1).2 (eσ.symm γ.2).2
  have hle : D ⊔ X ≤ π₀.range := by
    refine sup_le ?_ ?_
    · intro a ha
      refine ⟨(eρ ⟨a, ha⟩, 1), ?_⟩
      rw [hπ₀, MulEquiv.symm_apply_apply, map_one]
      simp
    · intro a ha
      refine ⟨(1, eσ ⟨a, ha⟩), ?_⟩
      rw [hπ₀, MulEquiv.symm_apply_apply, map_one]
      simp
  have key : ∀ (γ : ↥(StatedSL d F) × ↥(StatedSL d F)) (v : V),
      β ((π₀ γ : MulAut V) v) = Multiplicative.ofAdd
        (((γ.1 : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          Multiplicative.toAdd (β v) *
          ((γ.2 : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ) := by
    intro γ v
    have hg : ρ (eρ.symm γ.1) = (γ.1 : Matrix.GeneralLinearGroup (Fin d) F) :=
      congrArg Subtype.val (eρ.apply_symm_apply γ.1)
    have hh : σ (eσ.symm γ.2) = (γ.2 : Matrix.GeneralLinearGroup (Fin d) F) :=
      congrArg Subtype.val (eσ.apply_symm_apply γ.2)
    rw [hπ₀, MulAut.mul_apply, hM.hρ, hM.hσ, hg, hh, toAdd_ofAdd, mul_assoc]
  refine ⟨π₀.codRestrict (D ⊔ X) hmem, ?_, fun γ v => key γ v⟩
  rintro ⟨y, hy⟩
  obtain ⟨γ, hγ⟩ := hle hy
  exact ⟨γ, Subtype.ext hγ⟩

theorem omega4PlusModule_of_matModel [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    {β : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin 2) F}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F}
    (hM : IsMatModel D X β ρ σ) (hρ : ρ.range = StatedSL 2 F) (hσ : σ.range = StatedSL 2 F) :
    Omega4PlusModule (D ⊔ X) n := by
  obtain ⟨π, hπ, hβ⟩ := exists_tensorData_of_matModel hcomm hM hρ hσ
  exact omega4PlusModule_of_tensorData hF π hπ β hβ

theorem tensorNatL32_of_matModel_of_card_two [Finite F] (hF : Nat.card F = 2)
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    {β : V ≃* Multiplicative (Matrix (Fin 3) (Fin 3) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin 3) F}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin 3) F}
    (hM : IsMatModel D X β ρ σ) (hρ : ρ.range = StatedSL 3 F) (hσ : σ.range = StatedSL 3 F) :
    TensorNatL32 (D ⊔ X) := by
  obtain ⟨π, hπ, hβ⟩ := exists_tensorData_of_matModel hcomm hM hρ hσ
  exact tensorNatL32_of_tensorData_of_card_two hF π hπ β hβ

end FromSqModel

end CFSG.Quasithin
