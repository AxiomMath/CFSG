module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofCent
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofG2Two
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.Background.FFC2G2
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.Quasithin.Recognition.CertU33Perm

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LieType.Ree
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def ResidualFacts (C : Type) [Group C] : Prop :=
  (∀ y : C, y ^ 3 = 1 → y ∈ perfectResidual C) ∧ IsSimpleGroup (perfectResidual C) ∧
    ∃ x y : perfectResidual C, x * y ≠ y * x

section General

variable {C : Type} [Group C]

theorem ResidualFacts.of_mulEquiv {D : Type} [Group D] (e : C ≃* D) (h : ResidualFacts D) :
    ResidualFacts C := by
  obtain ⟨h3, hs, x, y, hxy⟩ := h
  set ρ := perfectResidualEquivOfMulEquiv e with hρ
  have : IsSimpleGroup (perfectResidual D) := hs
  refine ⟨fun z hz => ?_, ρ.isSimpleGroup, ρ.symm x, ρ.symm y, fun h => hxy ?_⟩
  · have hz' : e z ∈ perfectResidual D := h3 (e z) (by rw [← map_pow, hz, map_one])
    rw [← KFacts.perfectResidual_map_mulEquiv e] at hz'
    obtain ⟨w, hw, hwz⟩ := hz'
    rwa [e.injective hwz] at hw
  · have := congrArg ρ h
    simpa using this

theorem residualFacts_of_isSimpleGroup [IsSimpleGroup C] (hnc : ∃ x y : C, x * y ≠ y * x) :
    ResidualFacts C := by
  have hP : Group.IsPerfect C := Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
  have htop : perfectResidual C = ⊤ := KFacts.perfectResidual_eq_top_of_isPerfect hP
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨fun z _ => htop ▸ Subgroup.mem_top z, ?_, ⟨x, htop ▸ Subgroup.mem_top x⟩,
    ⟨y, htop ▸ Subgroup.mem_top y⟩, fun h => hxy (congrArg Subtype.val h)⟩
  exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup

theorem residualFacts_of_commutator (hs : IsSimpleGroup (commutator C))
    (hnc : ∃ x y : commutator C, x * y ≠ y * x)
    (h3 : ∀ y : C, y ^ 3 = 1 → y ∈ commutator C) : ResidualFacts C := by
  have hP : Group.IsPerfect (commutator C) :=
    Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
  have heq : perfectResidual C = commutator C := by
    refine le_antisymm ?_ (Item87Res2Proof.le_perfectResidual_of_isPerfect hP)
    rw [← derivedSeries_one]
    exact iInf_le _ 1
  obtain ⟨x, y, hxy⟩ := hnc
  refine ⟨fun z hz => heq ▸ h3 z hz, (MulEquiv.subgroupCongr heq).isSimpleGroup,
    ⟨x, by rw [heq]; exact x.2⟩, ⟨y, by rw [heq]; exact y.2⟩, fun h => hxy ?_⟩
  have h' := congrArg (fun z : perfectResidual C => (z : C)) h
  exact Subtype.ext (by simpa using h')

theorem mem_of_pow_three_of_not_dvd_index {N : Subgroup C} [N.Normal] (hN : ¬ 3 ∣ N.index)
    {y : C} (hy : y ^ 3 = 1) : y ∈ N := by
  have h1 : orderOf (y : C ⧸ N) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : C ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
  · rw [h] at h2
    exact absurd h2 hN

end General

theorem residualFacts_projSp {m : ℕ} (hm : 1 ≤ m) :
    ResidualFacts (projSp 2 (GaloisField 2 m)) := by
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  refine ResidualFacts.of_mulEquiv (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
    (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 m))).symm ?_
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [hF, pow_one]
    refine ResidualFacts.of_mulEquiv
      (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2) ?_
    have hs := CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
    have hnc : ∃ x y : commutator CFSG.ComponentClassification.PresentationLocal.sympFour,
        x * y ≠ y * x := by
      by_contra hc
      push Not at hc
      exact CFSG.ComponentClassification.PresentationLocal.not_isMulCommutative_commutator_sympFour
        ⟨⟨hc⟩⟩
    obtain ⟨-, h3⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (MulEquiv.refl _)
    exact residualFacts_of_commutator hs hnc fun y hy => h3 Nat.prime_three (by norm_num) y hy
  · have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2
    have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
      (GaloisField 2 m) 2 (by norm_num) (Or.inl (Or.inr h4))
    have h4' : ∃ s : Finset (GaloisField 2 m), s.card = 4 := by
      have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField 2 m))) (n := 4) (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact h4)
      exact ⟨s, hs⟩
    have hp := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2
      (GaloisField 2 m) (Or.inl h4')
    exact residualFacts_of_isSimpleGroup (exists_ne_comm_of_isPerfect hp)


theorem index_commutator_g2_two
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    (commutator (adjointGroup .G2 k)).index = 2 := by
  obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hk
  obtain ⟨F⟩ := Item812Res8.nonempty_commutator_g2_two_equiv hk (Subgroup.topEquiv.trans E)
  have h1 : Nat.card (adjointGroup .G2 k) = 12096 := by
    rw [(CFSG.LieType.Chevalley.exact_G2_finite_order k hk).2.1]
    norm_num
  have h2 : Nat.card (commutator (adjointGroup .G2 k)) = 6048 := by
    rw [commutator_def, Nat.card_congr F.toEquiv]
    exact CFSG.Quasithin.card_u33Pres
  have h := (commutator (adjointGroup .G2 k)).card_mul_index
  rw [h1, h2] at h
  omega

theorem residualFacts_of_isoGTwoEven
    {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : IsoGTwoEven X m) : ResidualFacts X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  refine ResidualFacts.of_mulEquiv e ?_
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have hs := Sec11.KS11Lie3Proof.isSimpleGroup_commutator_g2_two hK2
    refine residualFacts_of_commutator hs ?_ ?_
    · obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK2
      obtain ⟨-, hnc, -⟩ :=
        CFSG.Quasithin.FFC.commutator_data_g2 hK2 (Subgroup.topEquiv.trans E)
      rw [commutator_def]
      exact hnc
    · intro y hy
      exact mem_of_pow_three_of_not_dvd_index (by rw [index_commutator_g2_two hK2]; norm_num) hy
  · have hK3 : 3 ≤ Nat.card K := by
      rw [hK]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3
    have hs : IsSimpleGroup (adjointGroup .G2 K) :=
      CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
        ((QuotientGroup.quotientMulEquivOfEq
          (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
            QuotientGroup.quotientBot).symm
    exact residualFacts_of_isSimpleGroup (exists_ne_comm_of_isPerfect hq.1)

section Tits

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem isSimpleGroup_commutator_tits (hK2 : Nat.card K = 2) :
    IsSimpleGroup (commutator (reeFixed ReeTag.F4 K 0)) := by
  set T := CFSG.LieType.Simplicity.titsData K hK2
  have hnt : Nontrivial (commutator (reeFixed ReeTag.F4 K 0)) :=
    ⟨⟨⟨T.g₀, T.g₀_mem⟩, 1, fun h => T.g₀_ne_one (congrArg Subtype.val h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  rcases T.eq_bot_or_eq_of_le hK2 (N.map (commutator (reeFixed ReeTag.F4 K 0)).subtype)
      (Subgroup.map_subtype_le N)
      (by
        rintro d hd _ ⟨n, hn, rfl⟩
        exact ⟨⟨d, hd⟩ * n * ⟨d, hd⟩⁻¹, hN.conj_mem n hn ⟨d, hd⟩, rfl⟩) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (x : reeFixed ReeTag.F4 K 0) ∈
        N.map (commutator (reeFixed ReeTag.F4 K 0)).subtype := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  · right
    rw [eq_top_iff]
    intro x _
    have : (x : reeFixed ReeTag.F4 K 0) ∈
        N.map (commutator (reeFixed ReeTag.F4 K 0)).subtype := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := this
    rw [← Subtype.ext hyx]
    exact hy

theorem index_commutator_tits_le (hK2 : Nat.card K = 2) :
    (commutator (reeFixed ReeTag.F4 K 0)).index ≤ 2 := by
  set T := CFSG.LieType.Simplicity.titsData K hK2
  set D := commutator (reeFixed ReeTag.F4 K 0)
  have htop := T.commutator_sup_zpowers_eq_top hK2
  set π := QuotientGroup.mk' D
  have hsurj : ∀ y : reeFixed ReeTag.F4 K 0 ⧸ D, y ∈ Subgroup.zpowers (π T.g₁) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D y
    have hg : g ∈ D ⊔ Subgroup.zpowers T.g₁ := htop ▸ Subgroup.mem_top g
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨n, ?_⟩
    have hπd : π d = 1 := (QuotientGroup.eq_one_iff d).2 hd
    show π T.g₁ ^ n = π (d * T.g₁ ^ n)
    rw [map_mul, hπd, one_mul, map_zpow]
  have hsq : π T.g₁ ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 T.g₁_sq_mem
  have hord : orderOf (π T.g₁) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hsq
  have htop' : Subgroup.zpowers (π T.g₁) = ⊤ := eq_top_iff.2 fun y _ => hsurj y
  calc D.index = Nat.card (reeFixed ReeTag.F4 K 0 ⧸ D) := rfl
    _ = Nat.card (⊤ : Subgroup (reeFixed ReeTag.F4 K 0 ⧸ D)) := Subgroup.card_top.symm
    _ = Nat.card (Subgroup.zpowers (π T.g₁)) := by rw [htop']
    _ = orderOf (π T.g₁) := Nat.card_zpowers _
    _ ≤ 2 := hord

end Tits

theorem residualFacts_reeGamma {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    ResidualFacts (ReeTag.F4.reeGamma k b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    refine ResidualFacts.of_mulEquiv (ReeTag.reeFixedEquivReeGamma k 0).symm ?_
    have hs := isSimpleGroup_commutator_tits hk2
    have hidx := index_commutator_tits_le hk2
    obtain ⟨x, hx, y, hy, hxy⟩ := (CFSG.LieType.Simplicity.titsData k hk2).nonabelian
    refine residualFacts_of_commutator hs
      ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩ fun z hz => ?_
    refine mem_of_pow_three_of_not_dvd_index ?_ hz
    have h0 : (commutator (reeFixed ReeTag.F4 k 0)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  · have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    have hs : IsSimpleGroup (ReeTag.F4.reeGamma k b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
    exact residualFacts_of_isSimpleGroup (exists_ne_comm_of_isPerfect hperf)

theorem residualFacts_barCentralizer
    {G : Type} [Group G] [Finite G] {X : Subgroup G} {a : G}
    {m : ℕ} (hm : 1 ≤ m) (htype : IsGammaType (X ⧸ aschbacherSolvableCore 3 X) m)
    (hU : ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) (3 * m)) (ha3 : a ^ 3 = 1)
    (hk : KFacts.InducesStdKind X a .field ∨ KFacts.InducesStdKind X a .graphField)
    (hG2 : Sec8PairGTwo X a m) :
    ResidualFacts (barCentralizer (Subgroup.zpowers a) X) := by
  have hout : Sec4.InducesOuterTheta a X := by
    rcases hk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h (by decide)
  rcases htype with ⟨k, hk', hkm, ⟨e₀⟩⟩ | hD | ⟨q, hq2, hqe, hGq⟩ | hU' | hS | hSp
  ·
    have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk'
    obtain ⟨-, k', hk'1, -, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
    obtain ⟨b, k₀, _, _, _, hk₀, ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk'1 hK (e₀.trans e₁) ha3 hout
    exact ResidualFacts.of_mulEquiv φ (residualFacts_reeGamma hk₀)
  ·
    exact residualFacts_of_isoGTwoEven hm (hG2 (Or.inl hD))
  ·
    exact residualFacts_of_isoGTwoEven hm
      (hG2 (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq)))
  · exact (hU (Or.inl hU')).elim
  · exact (hU (Or.inr hS)).elim
  ·
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := m) (by omega) ha3 hout hSp
    exact ResidualFacts.of_mulEquiv ι (residualFacts_projSp hm)

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
