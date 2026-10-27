module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerFive
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDiv
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenTable
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Arith

theorem ggAKFT_card_of_dFourTwo {X : Type} [Group X] (h : LieModel X .POmegaPlus 4 2 1) :
    Nat.card X = 174182400 := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl]
    decide
  all_goals exact absurd h0 (by norm_num)

theorem ggAKFT_ordSL_ne_dFourTwo {d a : ℕ} (hd : 2 ≤ d) (ha : 2 ≤ a) :
    (2 ^ a) ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1)) /
      Nat.gcd d (2 ^ a - 1) ≠ 174182400 := by
  intro h
  have hgP : Nat.gcd d (2 ^ a - 1) ∣ ∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h2 : (2 ^ a) ^ 2 - 1 ∣ ∏ j ∈ Finset.Icc 2 d, ((2 ^ a) ^ j - 1) :=
      Finset.dvd_prod_of_mem (fun j => (2 ^ a) ^ j - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hd⟩)
    refine dvd_trans ?_ h2
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ a) 1 2
  have h' := h
  rw [Nat.mul_div_assoc _ hgP] at h'
  have hdvd : 2 ^ (a * (d * (d - 1) / 2)) ∣ 2 ^ 12 * 42525 := by
    rw [pow_mul]
    exact Dvd.intro _ (h'.trans (by norm_num))
  have hcop : Nat.Coprime (2 ^ (a * (d * (d - 1) / 2))) 42525 :=
    Nat.Coprime.pow_left _ (by norm_num)
  have hbound : a * (d * (d - 1) / 2) ≤ 12 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  have hd4 : d ≤ 4 := by
    by_contra h5
    push Not at h5
    have h20 : 20 ≤ d * (d - 1) := Nat.mul_le_mul (by omega : 5 ≤ d) (by omega : 4 ≤ d - 1)
    have h10 : 10 ≤ d * (d - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
    have := Nat.mul_le_mul ha h10
    omega
  interval_cases d
  · have ha12 : a ≤ 12 := by norm_num at hbound; omega
    interval_cases a <;> revert h <;> decide
  · have ha4 : a ≤ 4 := by norm_num at hbound; omega
    interval_cases a <;> revert h <;> decide
  · have ha2 : a ≤ 2 := by norm_num at hbound; omega
    interval_cases a
    revert h
    decide

end Arith

section Tags

@[expose] def GGLayerNotDFourTwoTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ → 2 ≤ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ y : G, y ^ p = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        ¬ LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1

theorem ggLayerNotDFourTwoInput_of_tags (h : ∀ t, GGLayerNotDFourTwoTag t) :
    GGLayerNotDFourTwoInput := by
  intro G _ _ t n f ψ G₀ hpres hf p hp hp2 y hy hN hdiag C hC
  exact h t G n f ψ G₀ hpres hf p hp hp2 y hy hN hdiag C hC

theorem ggLayerNotDFourTwoTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGLayerNotDFourTwoTag t := by
  intro G _ _ n f ψ G₀ hpres
  have hrk := hpres.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggLayerNotDFourTwoTag_POmegaOdd : GGLayerNotDFourTwoTag .POmegaOdd :=
  fun _ _ _ _ _ _ _ hpres => absurd rfl hpres.1.1.2.2.2

end Tags

section PSL

open CFSG.RankThree.PartOne.KCLinComm Matrix LayerFacts LayerPDiv

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem ggAKFT_exists_psl_of_isComponentOf_sl [Finite G] [Finite F] [CharP F 2]
    {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsPGroup p E) (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    ∃ (d : ℕ) (D : Type) (_ : Field D) (_ : Finite D), 2 ≤ d ∧ CharP D 2 ∧
      Nat.card F ≤ Nat.card D ∧
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃*
        SpecialLinearGroup (Fin d) D ⧸ Subgroup.center (SpecialLinearGroup (Fin d) D)) := by
  classical
  obtain ⟨r, D, d, _, _, _, θ, hθinj, hθrange⟩ :=
    exists_piGL_centralizer (LinTorus.inducedMatrices ψ E)
      (natCast_card_inducedMatrices_ne_zero hker hp hp2 hE)
  have hchar : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  set ι : SpecialLinearGroup (Fin (m + 1)) F →* GL (Fin (m + 1)) F :=
    SpecialLinearGroup.toGL with hιdef
  have hιinj : Function.Injective ι := SpecialLinearGroup.toGL_injective
  have hC₀θ : ggCentSL ψ E = θ.range.comap ι := by rw [hθrange]; rfl
  set S : {b : Fin r // GoodBlock D d b} → Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    fun b => ((blockSL D d b.1).map θ).comap ι with hSdef
  have hSrange : ∀ b : {b : Fin r // GoodBlock D d b}, (blockSL D d b.1).map θ ≤ ι.range := by
    intro b
    have hperf : ⁅blockSL D d b.1, blockSL D d b.1⁆ = blockSL D d b.1 :=
      CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect
        (isPerfect_blockSL b.1 b.2.1 b.2.2)
    rw [← hperf, Subgroup.map_commutator]
    refine (Subgroup.commutator_mono le_top le_top).trans ?_
    rw [← _root_.commutator_def, hιdef, SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Abelianization.commutator_subset_ker _
  have hSmap : ∀ b, (S b).map ι = (blockSL D d b.1).map θ := fun b =>
    Subgroup.map_comap_eq_self (hSrange b)
  have hÑmap : (⨆ b, S b).map ι = (goodSL D d).map θ := by
    rw [Subgroup.map_iSup, goodSL, Subgroup.map_iSup]
    exact iSup_congr hSmap
  have hSC : ∀ b, S b ≤ ggCentSL ψ E := fun b => by
    rw [hC₀θ]
    exact Subgroup.comap_mono (Subgroup.map_le_range θ _)
  have hSn : ∀ b, ∀ c ∈ ggCentSL ψ E, ∀ s ∈ S b, c * s * c⁻¹ ∈ S b := by
    intro b c hc s hs
    rw [hC₀θ] at hc
    obtain ⟨w, hw⟩ := hc
    obtain ⟨g, hg, hgs⟩ := hs
    refine ⟨w * g * w⁻¹, conj_mem_blockSL b.1 w hg, ?_⟩
    rw [map_mul, map_mul, map_inv, hw, hgs, map_mul, map_mul, map_inv]
  let eB : ∀ b : {b : Fin r // GoodBlock D d b}, ↥(blockSL D d b.1) ≃* ↥(S b) := fun b =>
    ((Subgroup.equivMapOfInjective _ θ hθinj).trans
      (MulEquiv.subgroupCongr (hSmap b)).symm).trans
        (Subgroup.equivMapOfInjective _ ι hιinj).symm
  have hSq : ∀ b, CFSG.IsQuasisimple (S b) := fun b =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (eB b) (isQuasisimple_blockSL b.1 b.2.1 b.2.2)
  have hder : ∃ k, ggDer (ggCentSL ψ E) k ≤ ⨆ b, S b := by
    obtain ⟨k, hk⟩ := exists_derivedSeries_le_goodSL (E := D) (m := d)
    refine ⟨k, ?_⟩
    rw [← Subgroup.map_le_map_iff_of_injective hιinj, map_ggDer, hÑmap]
    calc ggDer ((ggCentSL ψ E).map ι) k ≤ ggDer θ.range k :=
          ggDer_mono (by rw [hC₀θ]; exact Subgroup.map_comap_le _ _) k
      _ = (ggDer ⊤ k).map θ := by rw [map_ggDer, ← MonoidHom.range_eq_map]
      _ = (derivedSeries _ k).map θ := by rw [ggDer_top]
      _ ≤ (goodSL D d).map θ := Subgroup.map_mono hk
  obtain ⟨b, rfl⟩ := exists_eq_map_of_isComponentOf ψ hker (map_ggCentSL_le hEA)
    (normal_map_ggCentSL hker) (commutator_le_map_ggCentSL hker) S hSC hSn hSq hder hK
  let eS : SpecialLinearGroup (Fin (d b.1)) (D b.1) ≃* ↥(S b) :=
    (MonoidHom.ofInjective (blockEmbed_injective (E := D) (m := d) b.1)).trans (eB b)
  have hSLperf : Group.IsPerfect (SpecialLinearGroup (Fin (d b.1)) (D b.1)) :=
    (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL b.2.1 b.2.2).1
  obtain ⟨e₁⟩ := ggCenterQuotEquiv_of_surjective hSLperf eS.toMonoidHom eS.surjective
    (fun x hx => by
      have h1 : eS x = eS 1 := by rw [map_one]; exact hx
      rw [eS.injective h1]
      exact Subgroup.one_mem _)
  obtain ⟨e₂⟩ := ggCenterQuotEquiv_of_surjective (hSq b).1 (ψ.subgroupMap (S b))
    (ψ.subgroupMap_surjective (S b)) (fun x hx => by
      have h1 : ψ (x : SpecialLinearGroup (Fin (m + 1)) F) = 1 := congrArg Subtype.val hx
      have hxZ := hker h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ g))
  exact ⟨d b.1, D b.1, inferInstance, inferInstance, b.2.1, hchar b.1,
    Nat.card_le_card_of_injective _ (algebraMap F (D b.1)).injective, ⟨e₂.symm.trans e₁.symm⟩⟩

end PSL

section TagPSL

theorem ggLayerNotDFourTwoTag_PSL : GGLayerNotDFourTwoTag .PSL := by
  intro G _ _ n f ψ G₀ hpres hf2 p hp hp2 y hy _ hdiag C hC hD4
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange, ← ggCentralizer_zpowers_eq] at hC
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin (m + 1)) (GaloisField 2 f),
      (y⁻¹, A) ∈ LinFusion.ggInducedPairs ψ :=
    LinFusion.exists_mem_ggInducedPairs (y := y⁻¹) hrk ψ hker (by rwa [inv_inv])
  have hA' : (y, A⁻¹) ∈ LinFusion.ggInducedPairs ψ := by
    have h := (LinFusion.ggInducedPairs ψ).inv_mem hA
    rwa [Prod.inv_mk, inv_inv] at h
  have hEA : ∀ e ∈ Subgroup.zpowers y, ∃ B, (e, B) ∈ LinFusion.ggInducedPairs ψ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h := (LinFusion.ggInducedPairs ψ).zpow_mem hA' k
    have e : ((y, A⁻¹) : G × GL (Fin (m + 1)) (GaloisField 2 f)) ^ k = (y ^ k, A⁻¹ ^ k) :=
      rfl
    exact ⟨A⁻¹ ^ k, e ▸ h⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨d, D, _, _, hd, hD2, hFD, ⟨e⟩⟩ := ggAKFT_exists_psl_of_isComponentOf_sl
    (F := GaloisField 2 f) hker hp hp2 (ggIsPGroup_zpowers_of_pow_eq_one hy) hEA hC
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card D = 2 ^ a := by
    have : Fintype D := Fintype.ofFinite D
    obtain ⟨k, -, hk⟩ := FiniteField.card D 2
    exact ⟨k, by rw [Nat.card_eq_fintype_card, hk]⟩
  have ha2 : 2 ≤ a := by
    have h1 : 2 ^ 2 ≤ 2 ^ a :=
      calc 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        _ = Nat.card (GaloisField 2 f) := hF.symm
        _ ≤ Nat.card D := hFD
        _ = 2 ^ a := ha
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hcard := ggAKFT_card_of_dFourTwo hD4
  rw [Nat.card_congr e.toEquiv] at hcard
  have hPSL : Nat.card (Matrix.SpecialLinearGroup (Fin d) D ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin d) D)) =
      Nat.card D ^ (d * (d - 1) / 2) * (∏ j ∈ Finset.Icc 2 d, (Nat.card D ^ j - 1)) /
        Nat.gcd d (Nat.card D - 1) :=
    (Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj d D).toEquiv).trans
      (CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega))
  rw [hPSL, ha] at hcard
  exact ggAKFT_ordSL_ne_dFourTwo hd ha2 hcard

theorem ggLayerNotDFourTwoInput_of_remaining (hPSU : GGLayerNotDFourTwoTag .PSU)
    (hPSp : GGLayerNotDFourTwoTag .PSp) (hPlus : GGLayerNotDFourTwoTag .POmegaPlus)
    (hMinus : GGLayerNotDFourTwoTag .POmegaMinus) (hF4 : GGLayerNotDFourTwoTag .F4)
    (hE6 : GGLayerNotDFourTwoTag .E6) (hE7 : GGLayerNotDFourTwoTag .E7)
    (hE8 : GGLayerNotDFourTwoTag .E8) (hTwE6 : GGLayerNotDFourTwoTag .twistedE6) :
    GGLayerNotDFourTwoInput := by
  refine ggLayerNotDFourTwoInput_of_tags fun t => ?_
  cases t with
  | PSL => exact ggLayerNotDFourTwoTag_PSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggLayerNotDFourTwoTag_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | G2 => exact ggLayerNotDFourTwoTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggLayerNotDFourTwoTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggLayerNotDFourTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggLayerNotDFourTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggLayerNotDFourTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggLayerNotDFourTwoTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end TagPSL

end CFSG.StandardType
