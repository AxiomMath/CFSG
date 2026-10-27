module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLangAlign
public import CFSG.LocalAnalysis.StandardType.GGTBTorTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLangCent
import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistAlign
import CFSG.LocalAnalysis.StandardType.GGTBE6Witness
import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescent
import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
import CFSG.LieType.Steinberg.CentralExt.PerfectLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrth
import CFSG.LieType.Chevalley.GraphFixedParameterFields

public noncomputable section

namespace CFSG.StandardType.TwE6ThreeLang

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.StandardType.TwE6Lang CFSG.StandardType.TBE6IndTwist
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem torData_odd {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) (hodd : Odd (Nat.card ψ₀.ker))
    (hcard : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≤
      Nat.card (WeylGroup .E6)) :
    GGTorusTorData (2 ^ n + 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ L' A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  have hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ n) := fun c => hσ c
  have hσ2 : ∀ c, σ.toRingHom (σ.toRingHom c) = c := by
    intro c
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨θ₀, hθ₀q, hθ₀o, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hn K hK
  change orderOf θ₀ = 2 at hθ₀o
  have hσθ : σ = θ₀ := RingEquiv.ext fun c => (hσ c).trans (hθ₀q c).symm
  have hσ1 : σ ≠ 1 := by
    rw [hσθ]
    intro h
    rw [h, orderOf_one] at hθ₀o
    omega
  have hσσ : σ * σ = 1 := RingEquiv.ext fun c => hσ2 c
  obtain ⟨l, hl⟩ := CFSG.SeitzReduction.LinearPilot.exists_trace_one_of_involution hσ1 hσσ
  obtain ⟨ζ, hζo⟩ := exists_normOne_prime K σ hn hK hσq Nat.prime_three h3
  have hζ : ζ ^ 3 = 1 := by
    apply Subtype.ext
    change (ζ : Kˣ) ^ 3 = 1
    rw [← hζo, pow_orderOf_eq_one]
  have hζK : (ζ : Kˣ) ^ 3 = 1 := congrArg Subtype.val hζ
  let e : CFSG.LieType.Steinberg.normOne σ ≃* Multiplicative (ZMod (2 ^ n + 1)) := by
    have he : CFSG.LieType.Steinberg.normOne σ ≃*
        Multiplicative (ZMod (Nat.card (CFSG.LieType.Steinberg.normOne σ))) :=
      (zmodCyclicMulEquiv inferInstance).symm
    rwa [card_normOne K σ hK hσq] at he
  obtain ⟨r, κ, hκinj, hκr, hact⟩ :=
    exists_aligned_three hn hK σ hσ h3 hl hζK hζo hψ₀ hker hperf hA hAH h5 hsc
  let ψa : L' →* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (RecipeExcLang.twConj K σ r⁻¹).toMonoidHom.comp ψ₀
  have hψa : Function.Surjective ψa := (RecipeExcLang.twConj K σ r⁻¹).surjective.comp hψ₀
  have hkera : ψa.ker = ψ₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (RecipeExcLang.twConj K σ r⁻¹).map_eq_one_iff
  have hkera' : ψa.ker ≤ Subgroup.center L' := hkera ▸ hker
  obtain ⟨φ, hφs, hφ, hφc⟩ :=
    exists_cover_fixed_of_odd hn hK σ hσq ψa hψa hkera' hperf (hkera ▸ hodd)
  obtain ⟨δ, hδ⟩ := exists_diagonal_descent hK σ hσq hσ2 l hl φ hφs hφc
  have hδi := scalar_descent_injective σ hσ2 l hl φ δ hK hσq hn ψa hφ hδ
  have hκ : ∀ a : A, (a : MulAut L') = δ (frameB σ ζ hζ (κ a)) := by
    intro a
    haveI : Group.IsPerfect L' := ⟨hperf⟩
    have hcomp : ψa.comp (a : MulAut L').toMonoidHom =
        ψa.comp (δ (frameB σ ζ hζ (κ a))).toMonoidHom := by
      apply MonoidHom.ext
      intro y
      obtain ⟨x, rfl⟩ := hφs y
      apply Subtype.ext
      change ((RecipeExcLang.twConj K σ r⁻¹ (ψ₀ ((a : MulAut L') (φ x))) :
          ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        ((ψa (δ (frameB σ ζ hζ (κ a)) (φ x)) : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
          ModGL TwistTag.E6.tag K)
      rw [hact a (φ x), hδ, hφ]
      have hx : ((RecipeExcLang.twConj K σ r⁻¹ (ψ₀ (φ x)) : ↥(twistedE6RootGroup K σ)) :
          ModGL TwistTag.E6.tag K) =
          ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hn hK σ.toRingHom hσq x :
            graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) :=
        congrArg Subtype.val (hφ x)
      rw [hx]
      exact (isogeny_fixedDiagonalHom σ hσ2 l hl hn hK hσq (frameB σ ζ hζ (κ a)) x).symm
    exact MulEquiv.ext fun y =>
      DFunLike.congr_fun (CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hkera' hcomp) y
  have hact' : GGE6ThreeActData A κ
      (fun i => φ (langWeylHom K σ.toRingHom hσ2 hl (simple .E6 i))) :=
    ⟨hκinj, hκr, fun i a => frame_act σ hσ2 l hl φ δ hK hφs hδ ζ hζ κ hκ hκr i a⟩
  have hnorm : ∀ i : Fin Tag.E6.rank,
      MulAut.conj (φ (langWeylHom K σ.toRingHom hσ2 hl (simple .E6 i))) ∈
        Subgroup.normalizer (A : Set (MulAut L')) :=
    hact'.conj_w_mem_normalizer
  have hAD : A ≤ δ.range := frame_le_range σ δ ζ hζ κ hκ
  have hroot := root_nontrivial_three σ δ ζ hζ hζo e hδi κ hκ hκr
  have hcent : ∀ x : L', (∀ a ∈ A, MulAut.conj x * a = a * MulAut.conj x) →
      x ∈ (φ.comp (langTorusHom K σ hσ2 l hl)).range := fun x hx =>
    cover_centralizer_three σ hσ2 l hl φ δ hn hK hσq hφs ψa hψa hφ hδ ζ hζ hζo A
      (fun v hv => hyp_le σ δ ζ hζ κ hκ hκr hv) x hx
  have hact'' : GGE6ThreeActData A κ (scalarWitness σ hσ2 l hl φ δ e A hnorm).n := by
    rw [scalarWitness_n σ hσ2 l hl φ δ e A hnorm]
    exact hact'
  exact ⟨scalarWitness σ hσ2 l hl φ δ e A hnorm, ggTDHolds_of_parts
    (scalar_holdsOne σ hσ2 l hl φ δ hn hK hσq ψa hφ hφs hδi hδ e A hAD hnorm)
    (scalar_holdsTwo σ hσ2 l hl φ δ hK hδi hδ e A hroot hnorm)
    (scalar_holdsThree_of_cent σ hσ2 l hl φ δ hK hδ e A hAD hnorm hcent)
    (TBE6.ggTDHoldsFour_of_actData (scalarWitness σ hσ2 l hl φ δ e A hnorm) hact'' hcard)⟩

theorem torData_recipe_odd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* TwE6Delta.RecipeR K n} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hodd : Odd (Nat.card ψ.ker)) :
    GGTorusTorData (2 ^ n + 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ L' A := by
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := hTB
  have hcard : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≤
      Nat.card (WeylGroup .E6) := by
    obtain ⟨Φ, T, w, h⟩ := (E6ThreeModel.e6ThreeModel_holds.2 K n hn hK h3 L' ψ hψ hker hperf A
      hA hAI h5 hsc).exists_data
    exact (Nat.card_congr h.automizerEquivWeyl.toEquiv).ge
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := n) hn hK
  let ψ₀ : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ
  have hψ₀ : Function.Surjective ψ₀ := ε.symm.surjective.comp hψ
  have hk : ψ₀.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ε.symm.map_eq_one_iff
  have hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l) := by
    intro a ha
    obtain ⟨φR, hφR, hφRl⟩ := hAI a ha
    obtain ⟨w, hw⟩ := (hε φR).2 hφR
    refine ⟨RecipeExcLang.twConj K σ w, ⟨w, rfl⟩, fun l => ?_⟩
    change RecipeExcLang.twConj K σ w (ε.symm (ψ l)) = ε.symm (ψ (a l))
    rw [← hφRl, ← hw, TwE6Transport.recipeConj_apply, MulEquiv.symm_apply_apply]
  exact torData_odd hn hK σ hσ h3 hψ₀ (hk ▸ hker) hperf hA hAH h5 hsc (hk ▸ hodd) hcard

theorem ggTorusTorW_recipe_twE6_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusTorW 3 5 (2 ^ n + 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆
      (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro L' _ _ ψ A hTB
  by_cases hodd : Odd (Nat.card ψ.ker)
  · exact torData_recipe_odd hn hK h3 hTB hodd
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3A, hsc⟩ := hTB
  have hn1 : n = 1 := by
    by_contra hne
    apply hodd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
      (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
    obtain ⟨σ, hσ, ε, -⟩ := TwE6Transport.exists_recipeConj (K := K) (n := n) hn hK
    let ψ₀ : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ
    have hk : ψ₀.ker = ψ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ε.symm.map_eq_one_iff
    rw [← hk]
    exact odd_card_ker_of_two_le (by omega) hK σ (fun c => hσ c) ψ₀
      (ε.symm.surjective.comp hψ) (hk ▸ hker) hperf
  subst hn1
  have hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker) := fun a ha =>
    U63TB.mem_presZ_of_ker hker fun z hz => U63TB.preserves_ker (hAI a ha) hz
  have hTB₁ : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1)
      (L' ⧸ U63TB.twoSub ψ.ker hker) (U63TB.psi1 hker) (U63TB.redSub hker hAle).range := by
    refine ⟨U63TB.psi1_surjective hker hψ, U63TB.psi1_ker_central hker,
      U63TB.commutator_quot hker hperf, U63TB.isElemAbelian_range_redSub hker hAle hAe,
      U63TB.redSub_hAI hker hAle hAI, ?_, ?_, U63TB.selfCent_quot hker hAe hAle hsc⟩
    · rw [U63TB.card_range_redSub hker hAle hperf]
      exact hr
    · rw [U63TB.card_range_redSub hker hAle hperf]
      exact h3A
  exact ggTorusTorData_descent_two hker hperf hAe hAle
    (torData_recipe_odd le_rfl hK h3 hTB₁ (U63TB.odd_card_ker_psi1 hker))

theorem ggTBTorTwE6Three_holds : GGTBTorTwE6Three := by
  intro lab hlab htag h3
  have hm : ggTorM lab = 2 ^ lab.n + 1 := by simp [ggTorM, htag]
  rw [hm] at h3 ⊢
  exact TwE6Delta.labelAll htag
    (Q := fun R _ I => GGTorusTorW 3 5 (2 ^ lab.n + 1) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ R I)
    fun K _ _ hK => ggTorusTorW_recipe_twE6_three hlab.1 hK h3

end CFSG.StandardType.TwE6ThreeLang

end
