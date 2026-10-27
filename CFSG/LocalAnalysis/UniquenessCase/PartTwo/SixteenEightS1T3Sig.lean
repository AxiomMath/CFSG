module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SigS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SigM
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.RankFour
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaPlanes
import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t3_simple_and_mult (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : (IsSLn X n 1 ∧ 4 ≤ n) ∨ (IsSpn X n 1 ∧ 6 ≤ n) ∨ (IsOmegaPlus X n 1 ∧ 6 ≤ n) ∨
      (IsOmegaMinus X n 1 ∧ 6 ≤ n) ∨ (UC22.IsAlt X n ∧ 8 ≤ n)) :
    IsSimpleGroup X ∧ ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 ^ k :=
  ⟨s16t3_isSimpleGroup_of_shape hX, s16t3_card_mult_eq_two_pow_of_shape hGA hSchur hX⟩

@[expose] def ThreeRankShape {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  ∃ n : ℕ, (IsSLn ↥L n 1 ∧ 8 ≤ n) ∨ (IsSpn ↥L n 1 ∧ 8 ≤ n) ∨ (IsOmegaPlus ↥L n 1 ∧ 8 ≤ n) ∨
    (IsOmegaMinus ↥L n 1 ∧ 10 ≤ n) ∨ (UC22.IsAlt ↥L n ∧ 12 ≤ n)

private theorem s16t3_four_le_pRank_statedSL {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {n : ℕ} (hn : 8 ≤ n) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL n K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hKunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  haveI : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.mp (by rw [hKunits])
  have hscal : StatedScalars (Fin n) K = ⊥ := by
    unfold StatedScalars
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨u, rfl⟩
    rw [Subsingleton.elim u 1, map_one]
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk'
      ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))).ker := by
    rw [QuotientGroup.ker_mk']
    simp [hscal]
  have h := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_three
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))) hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  exact (CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.psl_four_le_pRank_three
    (K := K) hn).trans h

private theorem s16t3_four_le_pRank_statedSp {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSp m K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hKunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  haveI : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.mp (by rw [hKunits])
  have hscal : StatedScalars (Fin m ⊕ Fin m) K = ⊥ := by
    unfold StatedScalars
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨u, rfl⟩
    rw [Subsingleton.elim u 1, map_one]
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk'
      ((StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (StatedSp m K))).ker := by
    rw [QuotientGroup.ker_mk']
    simp [hscal]
  have h := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_three
    (QuotientGroup.mk' ((StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (StatedSp m K))) hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  exact (CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.psp_four_le_pRank_three
    (K := K) hm).trans h

private theorem s16t3_pRank_eq_top_of_mulEquiv {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {X : Type} [Group X] [Finite X] (e : ↥L ≃* X) :
    CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L).trans
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e)

theorem ThreeRankShape.four_le_pRank {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hS : ThreeRankShape L) : 4 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨n, hn | hn | hn | hn | hn⟩ := hS
  · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hn.1
    letI : Field K := hKf
    letI : Finite K := hKfin
    rw [s16t3_pRank_eq_top_of_mulEquiv e]
    exact s16t3_four_le_pRank_statedSL (by simpa using hKcard) (by omega)
  · obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hn.1
    letI : Field K := hKf
    letI : Finite K := hKfin
    rw [s16t3_pRank_eq_top_of_mulEquiv e]
    exact s16t3_four_le_pRank_statedSp (by simpa using hKcard) (by omega)
  · obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hn.1
    letI : Field K := hKf
    letI : Finite K := hKfin
    rw [s16t3_pRank_eq_top_of_mulEquiv e]
    haveI : CharP K 2 := by
      haveI : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime (p := 2)
        (by rw [← Nat.card_eq_fintype_card]; simpa using hKcard)
    exact
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.four_le_pRank_three_omegaPlus
        (K := K) (n := n / 2) (by omega)
  · obtain ⟨-, K, hKf, hKfin, b, c, hKcard, -, ⟨e⟩⟩ := hn.1
    letI : Field K := hKf
    letI : Finite K := hKfin
    rw [s16t3_pRank_eq_top_of_mulEquiv e]
    haveI : CharP K 2 := by
      haveI : Fintype K := Fintype.ofFinite K
      exact charP_of_card_eq_prime (p := 2)
        (by rw [← Nat.card_eq_fintype_card]; simpa using hKcard)
    exact
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.four_le_pRank_three_omegaMinus
        (K := K) (n := n / 2) (by omega) b c
  · obtain ⟨e⟩ := hn.1
    rw [s16t3_pRank_eq_top_of_mulEquiv e]
    exact CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.four_le_pRank_alternatingGroup
      (N := n) (by omega)

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_pRank_le_M_of_exists_cover (h : S16gRowCtx D V₀ V L hV)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k) :
    CFSG.Open.pRank 3 (lBar V₀ V hV L) ≤ CFSG.Open.pRank 3 D.M := by
  obtain ⟨Y, hYle, hperf, hO2E, hCY, hYbar⟩ := s16g_exists_cover D h.std h.setting h.quasi
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  have hYs : Y ≤ stabTil V₀ V := hYle.trans hMs
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  let φ : ↥Y →* ↥(barSub V₀ V hV Y) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hYs))
      (barSub V₀ V hV Y) (fun g => actTil_mem_barSub V₀ V hV g.2 (hYs g.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV Y ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  let N : Subgroup ↥Y := φ.ker
  have hNker : N = (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y := by
    ext g
    rw [show N = φ.ker from rfl, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_cTilde_iff hV hMn]
    have hgY : (g : G) ∈ Y := g.2
    constructor
    · intro h1
      exact ⟨hgY, hYle hgY, hYs hgY, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  haveI : N.Normal := MonoidHom.normal_ker φ
  have hNsolv : Group.IsSolvable ↥N := by
    rw [hNker]
    have hle : (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y ≤ CFSG.solvableRadical ↥Y := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hCY (Subgroup.mem_subgroupOf.mp hx)
      have hzx' : z = x := Subtype.ext hzx
      exact hzx' ▸ hz
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥Y)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hperfY : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hlayerY : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
    have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
      QuotientGroup.mk'_surjective _
    have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have hcomap : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
      apply Subgroup.map_injective Y.subtype_injective
      change F11.O2E Y = (⊤ : Subgroup ↥Y).map Y.subtype
      rw [hO2E, hTop]
    have h := Subgroup.map_comap_eq_self_of_surjective hπ
      (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)))
    rw [hcomap, Subgroup.map_top_of_surjective _ hπ] at h
    exact h.symm
  have hKnc : ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
    intro hc
    exact CFSG.LocalAnalysis.GLTheoremA.SFM12.not_all_commute_of_quasisimple h.quasi
      (fun a b => hc.is_comm.comm a b)
  have hcenterK : Subgroup.center ↥(lBar V₀ V hV L) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc
  have hzK : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L))) := by
    rw [hcenterK, Subgroup.card_bot]
    exact odd_one
  let eQ : (↥Y ⧸ N) ≃* ↥(lBar V₀ V hV L) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans (MulEquiv.subgroupCongr hYbar)
  have hN2 : IsPGroup 2 N :=
    s16w_isPGroup_ker_of_two_multiplier hperfY hlayerY N hNsolv eQ h.quasi hzK hmult
  have hNdvd : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow (hk ▸ h3)) (by norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hquot := CFSG.SectionRank.pRank_quotient_eq (p := 3) N hNdvd
  have hpEqL : CFSG.Open.pRank 3 (lBar V₀ V hV L)
      = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (lBar V₀ V hV L)
  have htopL : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L))
      = CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ N)) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eQ).symm
  have hYtop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) = CFSG.Open.pRank 3 Y :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Y).symm
  have hmono : CFSG.Open.pRank 3 Y ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hYle
  calc CFSG.Open.pRank 3 (lBar V₀ V hV L)
      = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := hpEqL
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ N)) := htopL
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) := hquot
    _ = CFSG.Open.pRank 3 Y := hYtop
    _ ≤ CFSG.Open.pRank 3 D.M := hmono

theorem S16gRowCtx.three_mem_sig_of_rank (h : S16gRowCtx D V₀ V L hV)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (lBar V₀ V hV L)) : 3 ∈ D.sig :=
  h.std.hSg.four_mem 3 Nat.prime_three (by norm_num)
    (h4.trans (s16t3_pRank_le_M_of_exists_cover h hsimple hmult))

theorem S16gRowCtx.three_mem_sig_of_shape (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hS : ThreeRankShape (lBar V₀ V hV L)) : 3 ∈ D.sig := by
  have h4 := hS.four_le_pRank
  obtain ⟨n, hn | hn | hn | hn | hn⟩ := hS
  · obtain ⟨hs, hm⟩ := s16t3_simple_and_mult hGA hSchur (Or.inl ⟨hn.1, by omega⟩)
    exact h.three_mem_sig_of_rank hs hm h4
  · obtain ⟨hs, hm⟩ := s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inl ⟨hn.1, by omega⟩))
    exact h.three_mem_sig_of_rank hs hm h4
  · obtain ⟨hs, hm⟩ := s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inr (Or.inl ⟨hn.1, by omega⟩)))
    exact h.three_mem_sig_of_rank hs hm h4
  · obtain ⟨hs, hm⟩ :=
      s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inr (Or.inr (Or.inl ⟨hn.1, by omega⟩))))
    exact h.three_mem_sig_of_rank hs hm h4
  · obtain ⟨hs, hm⟩ :=
      s16t3_simple_and_mult hGA hSchur (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn.1, by omega⟩))))
    exact h.three_mem_sig_of_rank hs hm h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
