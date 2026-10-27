module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDichotomy
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpTwoDelta
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperBD
import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
import CFSG.LocalAnalysis.StandardType.MarkingSmall
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Defs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.SymCtxQuot
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S15K.FamilyHerm
public import Certificates.Certificate8026Base
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

@[expose] def GGLabSp6 (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ lab.n = 1

theorem card_le_pow_twoLocalPrimeRank_of_sstar {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] [Finite R] (hZ : Subgroup.center R = ⊥)
    (θ : L ⧸ Subgroup.center L ≃* R) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {I : Set (MulAut R)}
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hOD : GGOutdiagOdd p R I)
    (hinn : ∀ b (hb : b ∈ B), ggLAut L θ ⟨b, hBN hb⟩ ∈ (MulAut.conj : R →* MulAut R).range)
    (h4 : ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hδ : ¬ ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) ∧
      T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
      B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥) :
    Nat.card B ≤ p ^ (twoLocalPrimeRank p R + 1) := by
  classical
  haveI := Fact.mk hp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hDn, hID, hodd⟩ := hOD
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := h4
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
    mem_normalizer_of_sstar hS hnc (hTx ht)
  set conj : R →* MulAut R := MulAut.conj with hconj
  have hconj_inj : Function.Injective conj := by
    intro a b hab
    have hc : b⁻¹ * a ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut R => φ g) hab
      simp only [hconj, MulAut.conj_apply] at h1
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
        _ = b⁻¹ * a * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [hc, mul_one]
  set lamT := ((ggLAut L θ).comp (Subgroup.inclusion hTN)).range with hlamT
  have hlamT2 : IsPGroup 2 lamT :=
    hT2.of_surjective ((ggLAut L θ).comp (Subgroup.inclusion hTN)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  by_cases hΘ1 : lamT ⊓ conj.range = ⊥
  ·
    exfalso
    refine hδ ⟨T ⊓ Subgroup.centralizer (L : Set G), inf_le_right, inf_le_left.trans hTx,
      hT2.to_le inf_le_left, ?_,
      commutator_inf_centralizer_ne_bot hp hp2 hL θ (fun b hb => hS.1.1.2 b hb) hBN h3 hDn hID
        hodd hT2 hTN hBT hTB hΘ1⟩
    rw [Subgroup.le_normalizer_iff]
    intro b hb t ht
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : b⁻¹ * l * b ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hBN (Subgroup.inv_mem _ hb)) l).mp hl
      rwa [inv_inv] at h1
    have hc := Subgroup.mem_centralizer_iff.mp ht.2 _ hl'
    calc l * (b * t * b⁻¹) = b * ((b⁻¹ * l * b) * t) * b⁻¹ := by group
      _ = b * (t * (b⁻¹ * l * b)) * b⁻¹ := by rw [hc]
      _ = b * t * b⁻¹ * l := by group
  ·
    set lamB := ((ggLAut L θ).comp (Subgroup.inclusion hBN)).range with hlamB
    have hlamBinn : lamB ≤ conj.range := by
      rintro _ ⟨b, rfl⟩
      exact hinn b b.2
    set U := (lamT ⊓ conj.range).comap conj with hU
    set E := lamB.comap conj with hE
    have hU1 : U ≠ ⊥ := by
      intro hbot
      apply hΘ1
      rw [eq_bot_iff]
      rintro φ ⟨hφT, r, rfl⟩
      have hr : r ∈ U := ⟨hφT, r, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hr
      rw [hr, map_one]
      exact Subgroup.one_mem _
    have hU2 : IsPGroup 2 U := (hlamT2.to_le inf_le_left).comap_of_injective conj hconj_inj
    have hEU : E ≤ Subgroup.normalizer (U : Set R) := by
      rw [Subgroup.le_normalizer_iff]
      intro e he u hu
      obtain ⟨b, hbe⟩ := he
      obtain ⟨⟨t, htu⟩, -⟩ := hu
      refine ⟨?_, e * u * e⁻¹, rfl⟩
      have hbtb : b * (t : G) * (b : G)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hBT b.2) t).mp t.2
      refine ⟨⟨b * t * (b : G)⁻¹, hbtb⟩, ?_⟩
      have h1 : Subgroup.inclusion hTN ⟨b * t * (b : G)⁻¹, hbtb⟩ =
          Subgroup.inclusion hBN b * Subgroup.inclusion hTN t *
            (Subgroup.inclusion hBN b)⁻¹ :=
        Subtype.ext rfl
      simp only [MonoidHom.comp_apply] at hbe htu ⊢
      rw [h1, map_mul, map_mul, map_inv, hbe, htu, map_mul, map_mul, map_inv]
    have hEmap : E.map conj = lamB := by
      rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr hlamBinn]
    have hEcard : Nat.card E = Nat.card lamB := by
      rw [← hEmap, Subgroup.card_map_of_injective hconj_inj]
    have hBab : ∀ b c : B, b * c = c * b := fun b c =>
      hS.1.1.1.is_comm.comm b c
    have hEel : IsElemAbelian p E := by
      refine ⟨⟨⟨fun e f => Subtype.ext (hconj_inj ?_)⟩⟩, fun e he => hconj_inj ?_⟩
      · obtain ⟨b, hb⟩ := e.2
        obtain ⟨c, hc⟩ := f.2
        simp only [Subgroup.coe_mul, map_mul]
        rw [← hb, ← hc, ← map_mul, ← map_mul, hBab]
      · obtain ⟨b, hb⟩ := he
        rw [map_pow, ← hb, ← map_pow, map_one]
        have hbp : b ^ p = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, OneMemClass.coe_one]
          exact hS.1.1.2 b b.2)
        rw [hbp, map_one]
    have hker : ((ggLAut L θ).comp (Subgroup.inclusion hBN)).ker = (ggGamma L hBN).ker := by
      ext b
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ggGamma_eq_one_iff]
      constructor
      · intro h
        exact mem_centralizer_of_ggLAut_eq_one L θ hL h
      · intro h
        exact ggLAut_eq_one_of_mem_centralizer L θ h
    have hlamBcard : Nat.card lamB = Nat.card (ggGamma L hBN).range := by
      rw [hlamB, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
        ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (ggGamma L hBN)).toEquiv,
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv]
    have hBcard : Nat.card lamB * p = Nat.card B := by
      rw [hlamBcard]
      exact card_range_ggGamma_mul L hBN hp hS
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEel.isPGroup
    have hkle : k ≤ twoLocalPrimeRank p R :=
      CFSG.LocalAnalysis.GLTheoremA.le_twoLocalPrimeRank_of_normalizer hp hU1 hU2 hEel hk hEU
    rw [← hBcard, ← hEcard, hk, ← pow_succ]
    exact Nat.pow_le_pow_right hp.pos (Nat.succ_le_succ hkle)

theorem not_ggInnerDiagOnLabel_sp6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) : ¬ GGInnerDiagOnLabel GGLabSp6 3 Bs L := by
  intro hM
  obtain ⟨⟨-, -, -, -, -, hβ, hS, hst⟩, ⟨hBBs, -, -, -⟩, -⟩ := hC
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨-, -, -, -, -, -, -, hlabSp, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hr, hn⟩ := hlabSp
  dsimp only at ht hr hn
  subst hr hn
  have key : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ 1 →
      ∀ I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K 3))),
      IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K 3)) →
      (∃ a b : LargeEvenProj (LargeEvenSpGroup K 3), a * b ≠ b * a) →
      ∀ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSpGroup K 3),
      Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      False := by
    intro K _ _ hK I hs hna θ hBsN h3s
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (le_refl 1) hK
    haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
    haveI : Finite (LargeEvenSpGroup K 3) := Finite.of_injective
      (fun y : LargeEvenSpGroup K 3 =>
        ((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))
      (fun y z hyz => Subtype.ext (Units.ext hyz))
    have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
    have h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ :=
      fun b hb => h3s b (hBBs hb)
    have hZ : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K 3)) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (LargeEvenProj (LargeEvenSpGroup K 3))) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hna
        have hb : b ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K 3)) := by
          rw [h]
          exact Subgroup.mem_top b
        exact hab (Subgroup.mem_center_iff.mp hb a)
    have hnc := UnitTB.exists_noncyclic_of_torusLift Nat.prime_three (le_refl 2) hL θ
      (TwoThree.ggTorusLift_sp_two (k := 2) hK2)
    have hinn : ∀ b (hb : b ∈ B), ggLAut L θ ⟨b, hBN hb⟩ ∈
        (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K 3) →* _).range := fun b hb =>
      TwoThree.mem_range_conj_sp hK2 le_rfl _
    set ψ : L →* LargeEvenProj (LargeEvenSpGroup K 3) :=
      θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hψdef
    have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : ψ.ker ≤ Subgroup.center L := by
      intro l hl
      rw [MonoidHom.mem_ker] at hl
      have h1 : (QuotientGroup.mk' (Subgroup.center L)) l = 1 :=
        θ.injective (by rw [map_one]; exact hl)
      exact (QuotientGroup.eq_one_iff l).mp h1
    have hδ : ¬ ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) ∧
        T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
        B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥ := by
      intro hδ
      obtain ⟨-, hδ2⟩ := ggDeltaAdm_of_delta Nat.prime_three hS hBN hδ
      rcases hδ2 with ⟨⟨a, ⟨b, rfl⟩, hna'⟩, -⟩ | ⟨hdvd, -, -⟩
      · obtain ⟨g, hg⟩ := isInner_of_induces hψ hker hL (ggGamma L hBN b)
          (TwoThree.mem_range_conj_sp hK2 le_rfl (ggLAut L θ ⟨b, hBN b.2⟩))
          (fun l => ggLAut_apply L θ _ l)
        exact hna' ⟨g, hg.symm⟩
      · exact ggCenterPrime_sp (K := K) (m := 3) Nat.prime_three (by norm_num) L ψ hψ hker hL
          hdvd
    have hcard := card_le_pow_twoLocalPrimeRank_of_sstar Nat.prime_three (by norm_num) hS hnc hL
      hZ θ hBN h3 (SpTwo.ggOutdiagOdd_spTwo hK2 le_rfl I) hinn hst.2.1 hδ
    obtain ⟨e⟩ := nonempty_largeEvenProj_equiv_of_card_two hK2 (LargeEvenSpGroup K 3)
    have hR2 : twoLocalPrimeRank 3 (LargeEvenProj (LargeEvenSpGroup K 3)) ≤ 2 :=
      ((CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three).trans_le
        (CFSG.LocalAnalysis.GLTheoremA.twoLocalPrimeRank_statedSp_le (K := K) (ℓ := 3)
          (by norm_num) Nat.prime_three (by norm_num) (by rw [hK2]; norm_num)))
    have hB : Nat.card B = 3 ^ twoLocalPrimeRank 3 G := hS.1.2.1
    have h4 : 4 ≤ twoLocalPrimeRank 3 G := hβ.2.2.2
    have h81 : 3 ^ 4 ≤ Nat.card B := hB ▸ Nat.pow_le_pow_right (by norm_num) h4
    have h27 : Nat.card B ≤ 3 ^ 3 :=
      hcard.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  rcases ht with rfl | rfl
  · obtain ⟨K, _, _, hK, hs, hna, θ, -, hBsN, h3s⟩ := hraw
    exact key K hK _ hs hna θ hBsN h3s
  · obtain ⟨K, _, _, hK, hs, hna, θ, -, hBsN, h3s⟩ := hraw
    exact key K hK _ hs hna θ hBsN h3s

end CFSG.StandardType

end
