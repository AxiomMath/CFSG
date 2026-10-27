module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.LieType.Steinberg.CentralExt.SuzukiMultiplier
public import CFSG.LieType.Multipliers.Sz8
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Quasithin.E2

open CFSG.RankThree.PerfectCover CFSG.Assembly.LowTwoRank
open CFSG.BenderSuzuki.MatrixGroups (SuzukiMatrixGroup)

theorem isSimpleGroup_of_psl_or_sz {Y : Type} [Group Y] {n : ℕ}
    (h : IsPSL 2 2 n Y ∨ IsSz n Y) : IsSimpleGroup Y := by
  rcases h with h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity Y 2 n h).2

theorem commutator_eq_top_of_psl_or_sz {Y : Type} [Group Y] {n : ℕ} (hn : 1 < n)
    (h : IsPSL 2 2 n Y ∨ IsSz n Y) : commutator Y = ⊤ := by
  rcases h with h | h
  · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have h4 : ∃ s : Finset K, s.card = 4 := by
      obtain ⟨s, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by
          rw [Finset.card_univ, Fintype.card_eq_nat_card, hK]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
      exact ⟨s, hs.2⟩
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    let f : Matrix.SpecialLinearGroup (Fin 2) K →* Y :=
      ((projectiveSpecialLinearGroupEquivStatedProj 2 K).trans eK.symm).toMonoidHom.comp
        (QuotientGroup.mk' _)
    have hf : Function.Surjective f :=
      ((projectiveSpecialLinearGroupEquivStatedProj 2 K).trans eK.symm).surjective.comp
        (QuotientGroup.mk'_surjective _)
    have : Group.IsPerfect Y := Group.IsPerfect.ofSurjective hf
    exact Group.IsPerfect.commutator_eq_top
  · obtain ⟨a, ha, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel h
    have : Group.IsPerfect (SuzukiMatrixGroup a) :=
      CFSG.SectionRank.suzukiMatrixGroup_isPerfect a ha
    have : Group.IsPerfect Y :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top

theorem nonabelian_of_commutator_eq_top {Y : Type} [Group Y] [Nontrivial Y]
    (h : commutator Y = ⊤) : ∃ a b : Y, a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  have hbot : commutator Y = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hno a b, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨y, hy⟩ := exists_ne (1 : Y)
  have : y ∈ commutator Y := h ▸ Subgroup.mem_top y
  rw [hbot, Subgroup.mem_bot] at this
  exact hy this

theorem nonabelian_of_psl_or_sz {Y : Type} [Group Y] {n : ℕ} (hn : 1 < n)
    (h : IsPSL 2 2 n Y ∨ IsSz n Y) : ∃ a b : Y, a * b ≠ b * a := by
  have := (isSimpleGroup_of_psl_or_sz h).toNontrivial
  exact nonabelian_of_commutator_eq_top (commutator_eq_top_of_psl_or_sz hn h)

theorem exists_surjective_center {L S : Type} [Group L] [Group S] [Group.IsPerfect L]
    (e : L ⧸ Subgroup.center L ≃* S) :
    ∃ φ : CFSG.Open.griessHopfMultiplier S →* Subgroup.center L, Function.Surjective φ := by
  have hk : (centralQuotientMap e).ker ≤ Subgroup.center L := (centralQuotientMap_ker e).le
  let e2 : (centralQuotientMap e).ker ≃* Subgroup.center L :=
    MulEquiv.subgroupCongr (centralQuotientMap_ker e)
  exact ⟨e2.toMonoidHom.comp ((hopfMultiplierToKer (centralQuotientMap e)
      (centralQuotientMap_surjective e) hk).comp (hopfMultiplierEquivGriess S).toMonoidHom),
    e2.surjective.comp ((hopfMultiplierToKer_surjective _ _ hk).comp
      (hopfMultiplierEquivGriess S).surjective)⟩

theorem eq_bot_of_surjective_subsingleton {A : Type*} [Group A] [Subsingleton A] {L : Type*}
    [Group L] {Z : Subgroup L} (φ : A →* Z) (hφ : Function.Surjective φ) : Z = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨a, ha⟩ := hφ ⟨z, hz⟩
  rw [Subsingleton.elim a 1, map_one] at ha
  have := congrArg Subtype.val ha
  simpa [eq_comm] using this

theorem sq_eq_one_of_surjective {A : Type*} [Group A] (hA : ∀ a : A, a * a = 1) {L : Type*}
    [Group L] {Z : Subgroup L} (φ : A →* Z) (hφ : Function.Surjective φ) :
    ∀ z ∈ Z, z * z = 1 := by
  intro z hz
  obtain ⟨a, ha⟩ := hφ ⟨z, hz⟩
  have := congrArg Subtype.val (congrArg φ (hA a))
  rw [map_mul, ha, map_one] at this
  exact this

theorem center_eq_bot_of_isPSL
    {L Y : Type} [Group L] [Group Y] [Group.IsPerfect L] {n : ℕ}
    (hn : 3 ≤ n) (hY : IsPSL 2 2 n Y) (e : L ⧸ Subgroup.center L ≃* Y) :
    Subgroup.center L = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hY
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ n := by rw [Fintype.card_eq_nat_card, hK]
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
    (k := K) (by omega) (by
      intro h9
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega)
  have hodd : Odd (Fintype.card K - 1) := by
    rw [hcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)] at eM
  have : Subsingleton (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) := eM.toEquiv.subsingleton
  obtain ⟨φ, hφ⟩ := exists_surjective_center
    (e.trans (eK.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm))
  exact eq_bot_of_surjective_subsingleton φ hφ

theorem nonempty_alt_five_of_isPSL_two {Y : Type} [Group Y]
    (hY : IsPSL 2 2 2 Y) : Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hY
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inl (by rw [hK]; norm_num))
  exact ⟨eK.trans e4⟩

theorem sq_eq_one_of_mem_center_isPSL_two
    {L Y : Type} [Group L] [Group Y] [Group.IsPerfect L] (hY : IsPSL 2 2 2 Y)
    (e : L ⧸ Subgroup.center L ≃* Y) : ∀ z ∈ Subgroup.center L, z * z = 1 := by
  obtain ⟨e4⟩ := nonempty_alt_five_of_isPSL_two hY
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (by rw [Nat.card_zmod]))
  let e' : L ⧸ Subgroup.center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) :=
    e.trans (e4.trans (e5.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5)).symm))
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
    (k := ZMod 5) (by rw [ZMod.card]) (by rw [ZMod.card]; norm_num)
  rw [ZMod.card, show Nat.gcd 2 (5 - 1) = 2 by norm_num] at eM
  obtain ⟨φ, hφ⟩ := exists_surjective_center e'
  refine sq_eq_one_of_surjective (fun a => ?_) φ hφ
  apply eM.injective
  rw [map_mul, map_one]
  generalize eM a = b
  revert b
  decide

theorem center_eq_bot_of_isSz {L Y : Type} [Group L] [Group Y] [Group.IsPerfect L] {n : ℕ}
    (hn : n ≠ 3) (hY : IsSz n Y) (e : L ⧸ Subgroup.center L ≃* Y) : Subgroup.center L = ⊥ := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨eK⟩⟩ := hY
  have ha2 : 2 ≤ a := by omega
  let eS : Y ≃* SuzukiMatrixGroup a :=
    eK.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      ((CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hK).trans
        (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)))
  let eZ : SuzukiMatrixGroup a ⧸ Subgroup.center (SuzukiMatrixGroup a) ≃* SuzukiMatrixGroup a :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Steinberg.CentralExt.SuzukiClosed.suzuki_center_eq_bot ha2)).trans
      QuotientGroup.quotientBot
  obtain ⟨-, hsub⟩ := CFSG.LieType.Steinberg.CentralExt.SuzukiClosed.suzuki_hopfMultiplier ha2
  obtain ⟨φ, hφ⟩ := exists_surjective_center (e.trans (eS.trans eZ.symm))
  exact eq_bot_of_surjective_subsingleton φ hφ

theorem sq_eq_one_of_mem_center_isSz_three
    {L Y : Type} [Group L]
    [Group Y] [Group.IsPerfect L] (hY : IsSz 3 Y) (e : L ⧸ Subgroup.center L ≃* Y) :
    ∀ z ∈ Subgroup.center L, z * z = 1 := by
  have hm : CFSG.Blueprint.LieModel Y .twistedB2 0 2 3 := Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hY⟩))
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Sz8.multiplier_Sz_eight Y hm
  obtain ⟨φ, hφ⟩ := exists_surjective_center e
  refine sq_eq_one_of_surjective (fun a => ?_) φ hφ
  apply eM.injective
  rw [map_mul, map_one]
  generalize eM a = b
  revert b
  decide

end CFSG.Quasithin.E2
