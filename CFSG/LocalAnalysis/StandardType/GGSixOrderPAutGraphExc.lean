module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraph
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcE6
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcE7
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcF4
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace OrdPGraph

section Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem adjDiagFieldForm_of_adjFieldForm
    {p : ℕ} (h : RootDetectExc.AdjFieldForm τ K p) :
    RootDetectExc.AdjDiagFieldForm τ K p := by
  intro β hβ
  obtain ⟨g, σ, hσ, hg⟩ := h β hβ
  refine ⟨g, 1, σ, hσ, fun x => ?_⟩
  rw [hg x, rootDiagUnit_one, mul_one, inv_one, mul_one]

theorem diagField_xPar
    (F : RootOperatorFamily τ)
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    rootDiagUnit τ a * Units.map (entrywiseHom σ.toRingHom)
        ((xPar F γ c : adjointGroup τ K) : ModGL τ K) * (rootDiagUnit τ a)⁻¹ =
      ((xPar F γ ((rootChar a γ : K) * σ c) : adjointGroup τ K) : ModGL τ K) := by
  rw [xPar_of_isRoot hγ, xPar_of_isRoot hγ, RootOperatorFamily.coe_eltElement,
    RootOperatorFamily.coe_eltElement, RootDetectExc.units_map_entrywiseHom_eltUnit,
    RootDetectExc.rootDiagUnit_conj_eltUnit]

theorem modelDiagField_of_adjDiagFieldForm
    (F : RootOperatorFamily τ) {S : Type*} [Group S] (Δ : UniversalRootDatum S)
    (π : S →* adjointGroup τ K)
    (hroot : ∀ γ ∈ Δ.roots, ∃ δ, IsRoot τ δ ∧ (∀ z ∈ Δ.rootGroup γ, ∃ c, π z = xPar F δ c) ∧
      ∀ c, ∃ z ∈ Δ.rootGroup γ, π z = xPar F δ c)
    {p : ℕ} (hform : RootDetectExc.AdjDiagFieldForm τ K p) (β : MulAut (adjointGroup τ K))
    (hβ : β ^ p = 1) : ModelDiagField Δ π β := by
  obtain ⟨g, a, σ, -, hg⟩ := hform β hβ
  refine ⟨g, fun γ hγ z hz => ?_⟩
  obtain ⟨δ, hδ, h1, h2⟩ := hroot γ hγ
  obtain ⟨c, hc⟩ := h1 z hz
  obtain ⟨z', hz', hz'e⟩ := h2 ((rootChar a δ : K) * σ c)
  refine ⟨z', hz', Subtype.ext ?_⟩
  rw [hz'e, ← diagField_xPar F a σ hδ c, ← hc]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
  group

theorem adjDatum_hroot
    (F : RootOperatorFamily τ) :
    ∀ γ ∈ (adjDatum F K).roots, ∃ δ, IsRoot τ δ ∧
      (∀ z ∈ (adjDatum F K).rootGroup γ, ∃ c, MonoidHom.id (adjointGroup τ K) z = xPar F δ c) ∧
      ∀ c, ∃ z ∈ (adjDatum F K).rootGroup γ, MonoidHom.id (adjointGroup τ K) z = xPar F δ c := by
  intro γ hγ
  have hγ' : IsRoot τ γ := mem_adjDatum_roots.mp hγ
  refine ⟨γ, hγ', fun z hz => ?_, fun c => ⟨xPar F γ c, xPar_mem hγ' c, rfl⟩⟩
  obtain ⟨c, hc⟩ := (mem_rootGroup_iff hγ' z).mp hz
  exact ⟨c, hc.symm⟩

end Adjoint

end OrdPGraph

section E8

theorem ggOrdPGraphModelAt_E8 : GGOrdPGraphModelAt .E8 := by
  intro n f hadm _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨(ggU .E8 n f).K, inferInstance, MonoidHom.id _, Function.surjective_id, ?_,
    fun p _ _ _ β hβ => ?_⟩
  · rw [MonoidHom.ker_id]
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm
  · exact OrdPGraph.modelDiagField_of_adjDiagFieldForm (rootOperatorFamily .E8)
      (e8Datum (GaloisField 2 f)) (MonoidHom.id _) (OrdPGraph.adjDatum_hroot _)
      (OrdPGraph.adjDiagFieldForm_of_adjFieldForm
        (RootDetectExc.adjFieldForm_E7_E8 hf _ hK .E8 (Or.inr rfl) p)) β hβ

theorem ggOrdPGraphAt_E8 : GGOrdPGraphAt .E8 :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_E8

end E8

section F4

theorem ggOrdPGraphModelAt_F4 : GGOrdPGraphModelAt .F4 := by
  intro n f hadm _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨(ggU .F4 n f).K, inferInstance, MonoidHom.id _, Function.surjective_id, ?_,
    fun p hp hp2 _ β hβ => ?_⟩
  · rw [MonoidHom.ker_id]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm
  · exact OrdPGraph.modelDiagField_of_adjDiagFieldForm (rootOperatorFamily .F4)
      (f4Datum (GaloisField 2 f)) (MonoidHom.id _) (OrdPGraph.adjDatum_hroot _)
      (OrdPGraph.adjDiagFieldForm_of_adjFieldForm
        (RootDetectExc.adjFieldForm_F4 hf _ hK (hp.odd_of_ne_two hp2))) β hβ

theorem ggOrdPGraphAt_F4 : GGOrdPGraphAt .F4 :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_F4

end F4

section E7

theorem ggOrdPGraphModelAt_E7 : GGOrdPGraphModelAt .E7 := by
  intro n f hadm _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨adjointGroup .E7 (GaloisField 2 f), inferInstance, e7Isogeny (GaloisField 2 f),
    e7Isogeny_surjective _, CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center,
    fun p _ _ _ β hβ => ?_⟩
  refine OrdPGraph.modelDiagField_of_adjDiagFieldForm (rootOperatorFamily .E7)
    (e7Datum (GaloisField 2 f)) (e7Isogeny (GaloisField 2 f)) ?_
    (OrdPGraph.adjDiagFieldForm_of_adjFieldForm
      (RootDetectExc.adjFieldForm_E7_E8 hf _ hK .E7 (Or.inl rfl) p)) β hβ
  intro γ hγ
  have hγ' : IsRoot .E7 γ := e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  have hε : ((e7Eps γ : ℤ) : GaloisField 2 f) * (e7Eps γ : GaloisField 2 f) = 1 := by
    rcases e7Eps_eq_one_or γ with h | h <;> rw [h] <;> norm_num
  refine ⟨γ, hγ', fun z hz => ?_, fun c =>
    ⟨e7Data_valid.xm (GaloisField 2 f) γ ((e7Eps γ : GaloisField 2 f) * c),
      e7Data_valid.xm_mem_rootGroup _ γ _, ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup (GaloisField 2 f)).mp hz
    exact ⟨_, e7Isogeny_xm (GaloisField 2 f) γ c⟩
  · rw [e7Isogeny_xm, ← mul_assoc, hε, one_mul]

theorem ggOrdPGraphAt_E7 : GGOrdPGraphAt .E7 :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_E7

end E7

section E6

theorem ggOrdPGraphModelAt_E6 : GGOrdPGraphModelAt .E6 := by
  intro n f hadm _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨adjointGroup .E6 (GaloisField 2 f), inferInstance, e6Isogeny (GaloisField 2 f),
    e6Isogeny_surjective _, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center,
    fun p hp hp2 _ β hβ => ?_⟩
  refine OrdPGraph.modelDiagField_of_adjDiagFieldForm (rootOperatorFamily .E6)
    (e6Datum (GaloisField 2 f)) (e6Isogeny (GaloisField 2 f)) ?_
    (RootDetectExc.adjDiagFieldForm_E6 _ (hp.odd_of_ne_two hp2)) β hβ
  intro γ hγ
  have hγ' : IsRoot .E6 γ := e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  refine ⟨γ, hγ', fun z hz => ?_, fun c =>
    ⟨e6Data_valid.xm (GaloisField 2 f) γ
      ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : GaloisField 2 f) * c),
      e6Data_valid.xm_mem_rootGroup _ γ _, ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 f)).mp hz
    refine ⟨(relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ : GaloisField 2 f) * c, ?_⟩
    rw [e6Isogeny_xm (GaloisField 2 f) hγ', CFSG.LieType.Steinberg.Isogeny.yPar]
  · rw [e6Isogeny_xm (GaloisField 2 f) hγ', CFSG.LieType.Steinberg.Isogeny.yPar, ← mul_assoc,
      relSignOr_mul_self, one_mul]

theorem ggOrdPGraphAt_E6 : GGOrdPGraphAt .E6 :=
  ggOrdPGraphAt_of_model ggOrdPGraphModelAt_E6

end E6

end CFSG.StandardType
