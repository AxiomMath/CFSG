module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcMarkedModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RecipeExcLang

theorem exists_marked_chev_E6
    {f : ℕ} (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ f' : MulAut (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false)),
      GGTableBFieldSylowMark p
        (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
          (LargeEvenChevH TwistTag.E6.tag.cartan K false)) f' ∧
      GGTableBMarkedFactorization p
        (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
          (LargeEvenChevH TwistTag.E6.tag.cartan K false)) f' := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨Θ, -, hΘ, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  have : IsCyclic (RingAut K) := isCyclic_ringEquiv_of_card hK
  have : Finite (RingAut K) :=
    Finite.of_injective (fun e : RingAut K => (e : K → K))
      fun a b h => RingEquiv.ext fun x => congrFun h x
  obtain ⟨σ₀', hσ₀'ord, hσ₀'gen⟩ := exists_pPart_generator_of_isCyclic (G := RingAut K) hp
  have hσΘ : ∀ σ : K ≃+* K, Θ (entrywiseAdjointAut TwistTag.E6.tag σ) = (σ, 1) := by
    intro σ
    have h1 := hΘ (entrywiseAdjointAut TwistTag.E6.tag σ) 1 1 σ ⟨0, exactE_pos _⟩ fun h => by
      rw [coe_entrywiseAdjointAut, rootDiagUnit_one]
      change _ = _ * _ * exactQ TwistTag.E6.tag K 0 * _ * (exactQ TwistTag.E6.tag K 0)⁻¹ * _ * _
      rw [exactQ_zero]
      simp
    rw [h1]
    simp
  refine exists_marked_chev_of_quotient (τ := TwistTag.E6.tag) (K := K) (p := p)
    (G := RingAut K × Multiplicative (ZMod (exactE TwistTag.E6.tag))) Θ (σ₀', 1) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨c, hc⟩ := hσ₀'ord
    exact ⟨c, by rw [Prod.orderOf_mk, hc, orderOf_one, Nat.lcm_one_right]⟩
  · intro σ hσ
    obtain ⟨k, hk⟩ := hσ
    have hsnd : σ.2 = 1 := by
      have h2 : σ.2 ^ p ^ k = 1 := by
        have h := congrArg Prod.snd hk
        simpa [Prod.pow_snd] using h
      have h2sq : σ.2 ^ 2 = 1 := by
        have hall : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
        exact hall σ.2
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        ((Nat.coprime_two_right.mpr hodd).pow_left k)
        (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h2sq))
    obtain ⟨j, hj⟩ := hσ₀'gen σ.1 (by
      refine ⟨k, ?_⟩
      have h := congrArg Prod.fst hk
      simpa [Prod.pow_fst] using h)
    refine ⟨j, ?_⟩
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · rw [hj]
      simp
    · rw [hsnd]
      simp
  · exact ⟨σ₀', hσΘ σ₀'⟩
  · intro σ h
    have hσ := hσΘ σ
    rw [hσ] at h
    simpa using congrArg Prod.fst h
  · intro α hα
    have hk : α ∈ Θ.ker := MonoidHom.mem_ker.mpr hα
    obtain ⟨g, a, hga⟩ := (hker α).mp hk
    have hw : (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a ∈
        inndiagGroup TwistTag.E6.tag K :=
      mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
    refine ⟨⟨_, hw⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    have e := hga h
    rw [e, coe_inndiagConj]
    group

end CFSG.StandardType
