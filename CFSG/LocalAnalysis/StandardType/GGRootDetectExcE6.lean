module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcDiag
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RootDetectExc

theorem adjDiagFieldForm_E6
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : Odd p) : AdjDiagFieldForm .E6 K p := by
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨Θ, -, hΘ, -, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  intro β hβ
  obtain ⟨g, a, σ, ε, hgε⟩ := hnf β
  have h2 : Θ β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  rw [hΘ β g a σ ε hgε] at h2
  have h3 : σ ^ p = 1 := congrArg Prod.fst h2
  have h4 : (Multiplicative.ofAdd (((ε : ℕ) : ZMod (exactE .E6)))) ^ p = 1 :=
    congrArg Prod.snd h2
  rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff] at h4
  have hε : (ε : ℕ) = 0 := by
    have h2p : ¬ 2 ∣ p := by
      rintro ⟨m, rfl⟩
      exact (Nat.not_even_iff_odd.mpr hp) ⟨m, by ring⟩
    have h5 : 2 ∣ (ε : ℕ) :=
      ((Nat.Prime.dvd_mul Nat.prime_two).mp (h4 : 2 ∣ p * (ε : ℕ))).resolve_left h2p
    have h6 : (ε : ℕ) < 2 := ε.isLt
    omega
  refine ⟨g, a, σ, h3, fun h => ?_⟩
  rw [hgε h, hε, exactQ_zero, mul_one, inv_one, mul_one]

theorem e6Root_toWeight : ∀ k : Fin 72, ∃ j : Fin Tag.E6.rank,
    MinData.toWeight (C2E6Std.e6Root k) j = 1 ∨ MinData.toWeight (C2E6Std.e6Root k) j = -1 := by
  decide +kernel

theorem exists_toWeight_eq_one_E6 {δ : Fin Tag.E6.rank → ℤ}
    (hδ : IsRoot .E6 δ) :
    ∃ j : Fin Tag.E6.rank, MinData.toWeight δ j = 1 ∨ MinData.toWeight δ j = -1 := by
  obtain ⟨k, rfl⟩ := C2E6Std.exists_e6Root_eq hδ
  exact e6Root_toWeight k

theorem hm_mem_ggTorus
    {τ : Tag} {D : MinData τ}
    (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan) (k : Type*) [Field k]
    (j : Fin τ.rank) (t : kˣ) : hV.hm k j t ∈ ggTorus (hV.minDatum hA k) := by
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  have hγ' : IsRoot τ γ := (hV.mem_minDatum_roots hA k).mp hγ
  have hinv : hV.hm k j t⁻¹ = (hV.hm k j t)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hV.hm_mul, inv_mul_cancel, hV.hm_one]
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).mp hn
    rw [hV.hm_conj_xm k hγ' j t c]
    exact hV.xm_mem_rootGroup k γ _
  · intro hn
    obtain ⟨c, hc⟩ := (hV.mem_rootGroup k).mp hn
    have hn' : n = hV.hm k j t⁻¹ * hV.xm k γ c * (hV.hm k j t⁻¹)⁻¹ := by
      rw [hc, hinv, inv_inv]
      group
    rw [hn', hV.hm_conj_xm k hγ' j t⁻¹ c]
    exact hV.xm_mem_rootGroup k γ _

theorem hdiag_E6
    (k : Type) [Field k] [Finite k] :
    ∀ δ ∈ (e6Datum k).roots, ∀ a : Fin Tag.E6.rank → kˣ, ∃ h ∈ ggTorus (e6Datum k),
      ∀ z ∈ (e6Datum k).rootGroup δ,
        ((e6Isogeny k (h * z * h⁻¹) : adjointGroup .E6 k) : ModGL .E6 k) =
          rootDiagUnit .E6 a * ((e6Isogeny k z : adjointGroup .E6 k) : ModGL .E6 k) *
            (rootDiagUnit .E6 a)⁻¹ := by
  intro δ hδ a
  have hδ' : IsRoot .E6 δ := (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 k).mp hδ
  obtain ⟨j, hj⟩ := exists_toWeight_eq_one_E6 hδ'
  obtain ⟨t, ht⟩ : ∃ t : kˣ, t ^ MinData.toWeight δ j = rootChar a δ := by
    rcases hj with h1 | h1
    · exact ⟨rootChar a δ, by rw [h1, zpow_one]⟩
    · exact ⟨(rootChar a δ)⁻¹, by rw [h1, zpow_neg_one, inv_inv]⟩
  refine ⟨e6Data_valid.hm k j t, hm_mem_ggTorus e6Data_valid isFiniteType_cartan_E6 k j t,
    fun z hz => ?_⟩
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).mp hz
  rw [e6Data_valid.hm_conj_xm k hδ' j t c, ht, e6Isogeny_xm k hδ', e6Isogeny_xm k hδ',
    CFSG.LieType.Steinberg.Isogeny.yPar, CFSG.LieType.Steinberg.Isogeny.yPar,
    xPar_of_isRoot hδ', xPar_of_isRoot hδ', RootOperatorFamily.coe_eltElement,
    RootOperatorFamily.coe_eltElement, rootDiagUnit_conj_eltUnit]
  congr 1
  ring

end RootDetectExc

section Family

theorem ggRootDetect_E6 : GGRootDetect .E6 := by
  intro G _ _ n f ψ hadm _ hker p hp hp2 _ c hc hcp γ hγ u hT
  obtain ⟨-, hf, -⟩ := hadm
  have : Finite ↥(e6Data_valid.minGroup (GaloisField 2 f)) := by
    have : Finite (Module.End (GaloisField 2 f) (Fin e6Data.d →₀ GaloisField 2 f)) :=
      Module.finite_of_finite (GaloisField 2 f)
    infer_instance
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀ : Fin Tag.E6.rank → ℤ, γ₀ = γ := ⟨γ, rfl⟩
  change γ₀ ∈ (e6Datum (GaloisField 2 f)).roots at hγ
  have hγ' : IsRoot .E6 γ₀ := e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 _ |>.mp hγ
  have hodd : Odd (Nat.card (e6Isogeny (GaloisField 2 f)).ker) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker
      (GaloisField 2 f) (p := 2)
    exact Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  have hinv : ∀ δ ∈ (e6Datum (GaloisField 2 f)).roots,
      ∀ z ∈ (e6Datum (GaloisField 2 f)).rootGroup δ, z * z = 1 := by
    intro δ _ z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 f)).mp hz
    rw [← e6Data_valid.xm_add, CharTwo.add_self_eq_zero, e6Data_valid.xm_zero]
  exact RootDetectExc.ggPsiInnerDiag_of_isogeny_diag (rootOperatorFamily .E6)
    (e6Datum (GaloisField 2 f)) (isPerfect_e6 (GaloisField 2 f)).commutator_eq_top
    center_adjointGroup_eq_bot (e6Isogeny_surjective (GaloisField 2 f))
    (ker_le_center_of_isQuasisimple (isQuasisimple_e6 (GaloisField 2 f))
      (e6Isogeny_ne_one (GaloisField 2 f))) hodd hinv
    (RootDetectExc.hdiag_E6 (GaloisField 2 f))
    (hp.odd_of_ne_two hp2) (RootDetectExc.adjDiagFieldForm_E6 _ (hp.odd_of_ne_two hp2)) hker
    hc hcp (α := ⟨γ₀, hγ'⟩)
    (fun t => ⟨e6Data_valid.xm (GaloisField 2 f) γ₀
      ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ₀ : GaloisField 2 f) * t),
      e6Data_valid.xm_mem_rootGroup _ γ₀ _, by
        have h := e6Isogeny_xm (GaloisField 2 f) hγ'
          ((relSignOr (rootOperatorFamily .E6) e6AdjData_valid γ₀ : GaloisField 2 f) * t)
        rw [CFSG.LieType.Steinberg.Isogeny.yPar, ← mul_assoc, relSignOr_mul_self, one_mul,
          xPar_of_isRoot hγ'] at h
        exact h⟩) hT

end Family

end CFSG.StandardType
