module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.CGT.PushingUpLit.T2K.SixC
public import CFSG.CGT.PushingUpLit.Glue.NinePair
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.BlockInteract
public import CFSG.CGT.PushingUpLit.NineContent
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def gammaEleven (M V : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ V ∧ U ≠ ⊥ ∧ ¬ Subgroup.centralizer (U : Set G) ≤ M ∧
    Opp 2 (M ⊓ Subgroup.centralizer (U : Set G)) ≤ Subgroup.centralizer (V : Set G)}

@[expose] def deltaEleven (M V : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ gammaEleven M V ∧ (E3.mQuot V U : ℕ∞) = rMV M V}

theorem mem_deltaEleven {M V U : Subgroup G} :
    U ∈ deltaEleven M V ↔ U ∈ gammaEleven M V ∧ (E3.mQuot V U : ℕ∞) = rMV M V :=
  Iff.rfl

theorem deltaEleven_subset_gammaEleven (M V : Subgroup G) :
    deltaEleven M V ⊆ gammaEleven M V := fun _ h => h.1

structure Setting11 (M V Q : Subgroup G) : Prop where
  charTwo : IsCharTwoType G
  maxLocal : rankThreeIsMaxTwoLocal M
  isElemAbelian : IsElemAbelian 2 V
  V_le_M : V ≤ M
  normal : M ≤ Subgroup.normalizer (V : Set G)
  V_ne_bot : V ≠ ⊥
  sylowQ : CFSG.RankThree.PartOne.IsSylowOf 2 Q (M ⊓ Subgroup.centralizer (V : Set G))
  uniqueMax : UniqueMax M (Subgroup.normalizer (Q : Set G) ⊓ M)

theorem exists_isMaxTwoLocalSubgroup_le {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ M' : Subgroup G, IsMaxTwoLocalSubgroup M' ∧ H ≤ M' := by
  classical
  set S : Set (Subgroup G) := {K | IsTwoLocal K ∧ H ≤ K} with hS
  have hfin : S.Finite := Set.toFinite S
  obtain ⟨M', hM', hmax⟩ := hfin.toFinset.exists_max_image (fun K => Nat.card K)
    (by rw [Set.Finite.toFinset_nonempty]; exact ⟨H, hH, le_rfl⟩)
  have hM'S : M' ∈ S := (hfin.mem_toFinset).1 hM'
  refine ⟨M', ⟨hM'S.1, fun K hK hM'K => ?_⟩, hM'S.2⟩
  by_contra hne
  have hlt : M' < K := lt_of_le_of_ne hM'K (fun h => hne h.symm)
  have hle := hmax K ((hfin.mem_toFinset).2 ⟨hK, hM'S.2.trans hM'K⟩)
  exact absurd hle (not_le.2 (Subgroup.card_lt_of_lt hlt))

theorem eleven_a {V Q : Subgroup G} (hQ : Q ≤ Subgroup.centralizer (V : Set G)) :
    V ≤ Subgroup.centralizer (Q : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact (Subgroup.mem_centralizer_iff.1 (hQ hq) v hv).symm

theorem normalizer_le_of_uniqueMax {M X D : Subgroup G} (huniq : UniqueMax M X)
    (hD : D ≠ ⊥) (hD2 : IsPGroup 2 D) (hXD : X ≤ Subgroup.normalizer (D : Set G)) :
    Subgroup.normalizer (D : Set G) ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (D : Set G)) := ⟨D, hD, hD2, rfl⟩
  obtain ⟨M', hM'max, hle⟩ := exists_isMaxTwoLocalSubgroup_le hloc
  have hmem : M' ∈ calMOf X := ⟨hM'max, hXD.trans hle⟩
  rw [huniq] at hmem
  rw [Set.mem_singleton_iff] at hmem
  rw [← hmem]
  exact hle

theorem eleven_b {M Q D : Subgroup G}
    (huniq : UniqueMax M (Subgroup.normalizer (Q : Set G) ⊓ M))
    (hD : D ≠ ⊥) (hD2 : IsPGroup 2 D)
    (h : Subgroup.normalizer (Q : Set G) ⊓ M ≤ Subgroup.normalizer (D : Set G)) :
    Subgroup.normalizer (D : Set G) ≤ M :=
  normalizer_le_of_uniqueMax huniq hD hD2 h

theorem eleven_b_char {M Q C : Subgroup G}
    (huniq : UniqueMax M (Subgroup.normalizer (Q : Set G) ⊓ M))
    (hCQ : C ≤ Q) (hCchar : (C.subgroupOf Q).Characteristic)
    (hC : C ≠ ⊥) (hC2 : IsPGroup 2 C) :
    Subgroup.normalizer (C : Set G) ≤ M := by
  haveI : (C.subgroupOf Q).Characteristic := hCchar
  have hNQ : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((C.subgroupOf Q).map Q.subtype : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (C.subgroupOf Q)
  have hmap : (C.subgroupOf Q).map Q.subtype = C := Subgroup.map_subgroupOf_eq_of_le hCQ
  rw [hmap] at hNQ
  exact eleven_b huniq hC hC2 (inf_le_left.trans hNQ)

theorem eleven_c_normalizer {M V : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hle : M ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup.normalizer (V : Set G) = M :=
  hM.2 _ ⟨V, hV, hV2, rfl⟩ hle

theorem Opp_conjSubgroup (p : ℕ) (X : Subgroup G) (g : G) :
    Opp p (conjSubgroup X g) = conjSubgroup (Opp p X) g := by
  have h1 : conjSubgroup X g = CFSG.RankThree.PartOne.conjBy g⁻¹ X := by
    ext x
    rw [mem_conjSubgroup_iff, CFSG.RankThree.PartOne.Equivariance.mem_conjBy]
    simp
  have h2 : conjSubgroup (Opp p X) g =
      CFSG.RankThree.PartOne.conjBy g⁻¹ (Opp p X) := by
    ext x
    rw [mem_conjSubgroup_iff, CFSG.RankThree.PartOne.Equivariance.mem_conjBy]
    simp
  unfold Opp
  rw [h1, CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy]
  exact h2.symm

theorem eleven_c_gamma {M V U : Subgroup G} (hMnorm : M ≤ Subgroup.normalizer (V : Set G))
    (hU : U ∈ gammaEleven M V) {m : G} (hm : m ∈ M) :
    conjSubgroup U m ∈ gammaEleven M V := by
  obtain ⟨hUV, hUne, hCU, hO⟩ := hU
  have hMm : conjSubgroup M m = M :=
    conjSubgroup_eq_iff_mem_normalizer.2 ((Subgroup.le_normalizer (H := M)) hm)
  have hVmV : conjSubgroup V m = V :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hMnorm hm)
  have hCmV : conjSubgroup (Subgroup.centralizer (V : Set G)) m =
      Subgroup.centralizer (V : Set G) := by
    rw [conjSubgroup_centralizer, hVmV]
  have hXm : conjSubgroup (M ⊓ Subgroup.centralizer (U : Set G)) m =
      M ⊓ Subgroup.centralizer (conjSubgroup U m : Set G) := by
    rw [conjSubgroup_inf, hMm, conjSubgroup_centralizer]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc conjSubgroup U m ≤ conjSubgroup V m := conjSubgroup_mono_left m hUV
      _ = V := hVmV
  · intro h
    exact hUne (conjSubgroup_eq_bot_iff.1 h)
  · intro hle
    rw [← conjSubgroup_centralizer U m, ← hMm] at hle
    exact hCU ((conjSubgroup_le_conjSubgroup_iff m).1 hle)
  · calc Opp 2 (M ⊓ Subgroup.centralizer (conjSubgroup U m : Set G))
        = Opp 2 (conjSubgroup (M ⊓ Subgroup.centralizer (U : Set G)) m) := by rw [hXm]
      _ = conjSubgroup (Opp 2 (M ⊓ Subgroup.centralizer (U : Set G))) m :=
            Opp_conjSubgroup 2 _ m
      _ ≤ conjSubgroup (Subgroup.centralizer (V : Set G)) m := conjSubgroup_mono_left m hO
      _ = Subgroup.centralizer (V : Set G) := hCmV

theorem eleven_e {D : Subgroup G} (hchar : IsCharTwoType G) (hD : D ≠ ⊥) (hD2 : IsPGroup 2 D) :
    IsCharacteristicP 2 ↥(Subgroup.centralizer (D : Set G)) :=
  CFSG.CGT.PushingUpLit.T2K.isCharacteristicP_centralizer hchar hD2 hD

theorem centMod_bot_eq_inf_centralizer {V : Subgroup G} {m : G} :
    centMod ⊥ V m = (V ⊓ Subgroup.centralizer ({m} : Set G) : Subgroup G) := by
  ext v
  simp only [centMod, Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨hv, hm⟩
    exact ⟨hv, (commutatorElement_eq_one_iff_mul_comm.1
      (by rw [commutatorElement_def]; exact hm)).symm⟩
  · rintro ⟨hv, hm⟩
    exact ⟨hv, by
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]; exact hm.symm⟩

theorem eleven_d {M V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V)
    (hlt : E3.mQuot V U < mBar M ⊥ V hV) :
    Opp 2 (M ⊓ Subgroup.centralizer (U : Set G)) ≤ Subgroup.centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hn : E3.mQuot V U < E3.mParam (Mbar M ⊥ V hV) := hlt
  unfold Opp
  rw [pElementSubgroup, Subgroup.closure_le]
  rintro x ⟨hxMU, k, hk⟩
  obtain ⟨hxM, hxU⟩ := Subgroup.mem_inf.1 hxMU
  by_cases hxc : x ∈ Subgroup.centralizer (V : Set G)
  · exact hxc
  · exfalso
    have hxstab : x ∈ stabTil ⊥ V :=
      Subgroup.mem_inf.2 ⟨hMV hxM, Subgroup.mem_normalizer_iff_map_conj_eq.2 (by simp)⟩
    let g : stabTil ⊥ V := ⟨x, hxstab⟩
    have hxb1 : actTil ⊥ V hV g ≠ 1 := by
      intro h1
      apply hxc
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h2 := (actTil_eq_one_iff ⊥ V hV g).1 h1 v hv
      rw [Subgroup.mem_bot] at h2
      exact (commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h2)).symm
    have hmem : actTil ⊥ V hV g ∈ Mbar M ⊥ V hV :=
      actTil_mem_barSub ⊥ V hV (X := M) (g := x) hxM hxstab
    have hord_dvd : orderOf (actTil ⊥ V hV g) ∣ 2 ^ k := by
      have h1 := orderOf_map_dvd (actTil ⊥ V hV) g
      have hg_ord : orderOf g = orderOf x := (Subgroup.orderOf_coe g).symm
      rwa [hg_ord, hk] at h1
    obtain ⟨j, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord_dvd
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        rw [pow_zero] at hj
        exact absurd (orderOf_eq_one_iff.1 hj.2) hxb1
      · exact hpos
    have hA1 : Subgroup.zpowers (actTil ⊥ V hV g) ≠ ⊥ := by
      intro h0
      exact hxb1 ((Subgroup.zpowers_eq_bot).1 h0)
    have hApg : IsPGroup 2 (Subgroup.zpowers (actTil ⊥ V hV g)) := by
      refine IsPGroup.of_card (n := j) ?_
      rw [Nat.card_zpowers, hj.2]
    have hA : E3.mParam (Mbar M ⊥ V hV) ≤
        rkIdx (fixV (Subgroup.zpowers (actTil ⊥ V hV g))) :=
      E3.mParam_le_rkIdx_fixV (Subgroup.zpowers_le.2 hmem) hApg hA1
    have hltfix : E3.mQuot V U <
        rkIdx (fixV (Subgroup.zpowers (actTil ⊥ V hV g))) :=
      lt_of_lt_of_le hn hA
    have hcard := (centMod_card_iff ⊥ V hV g (E3.mQuot V U)).2 hltfix
    have hUC : U ≤ V ⊓ Subgroup.centralizer ({x} : Set G) := by
      intro u hu
      exact Subgroup.mem_inf.2 ⟨hUV hu, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hxU u hu⟩
    have hcardU : Nat.card U ≤ Nat.card (centMod ⊥ V x) := by
      rw [centMod_bot_eq_inf_centralizer]
      refine Nat.card_le_card_of_injective
        (fun u : U => (⟨u.1, hUC u.2⟩ : ↥(V ⊓ Subgroup.centralizer ({x} : Set G)))) ?_
      intro a b h
      exact Subtype.ext (congrArg
        (fun z : ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) => (z : G)) h)
    have hVcard : Nat.card V = 2 ^ E3.mQuot V U * Nat.card U :=
      E3.card_eq_two_pow_mul hVpg hUV
    have hchain : 2 ^ (E3.mQuot V U + 1) * Nat.card U ≤
        2 ^ E3.mQuot V U * Nat.card U :=
      calc 2 ^ (E3.mQuot V U + 1) * Nat.card U
          ≤ 2 ^ (E3.mQuot V U + 1) * Nat.card (centMod ⊥ V x) :=
            Nat.mul_le_mul_left _ hcardU
        _ ≤ Nat.card V := hcard
        _ = 2 ^ E3.mQuot V U * Nat.card U := hVcard
    have hpos : 0 < Nat.card U := Nat.card_pos
    have h2 : 2 ^ (E3.mQuot V U + 1) ≤ 2 ^ E3.mQuot V U :=
      Nat.le_of_mul_le_mul_right hchain hpos
    rw [pow_succ] at h2
    have h3 : 2 ≤ 1 :=
      Nat.le_of_mul_le_mul_left (by simpa using h2)
        (pow_pos (a := 2) (by norm_num) (E3.mQuot V U))
    omega

theorem mBar_le_mQuot_bot {M V : Subgroup G} (hV : IsElemAbelian 2 V) :
    mBar M ⊥ V hV ≤ E3.mQuot V ⊥ := by
  have hc : Nat.card (Vtil ⊥ V hV) = Nat.card V := by
    have h := card_Vtil_eq (⊥ : Subgroup G) V hV bot_le
    simpa using h.symm
  calc mBar M ⊥ V hV = E3.mParam (Mbar M ⊥ V hV) := rfl
    _ ≤ rk (Vtil ⊥ V hV) := E3.mParam_le_rk _
    _ = E3.mQuot V ⊥ := by rw [rk, E3.mQuot, Subgroup.relIndex_bot_left, hc]

theorem eleven_f {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hlt : rMV M V < (mBar M ⊥ V hV : ℕ∞)) :
    (deltaEleven M V).Nonempty := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne_top : rMV M V ≠ ⊤ := by
    intro h
    rw [h] at hlt
    exact not_top_lt hlt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne_top
  have hn' : rMV M V = (n : ℕ∞) := hn.symm
  have hn_lt : n < mBar M ⊥ V hV := by
    have := hlt
    rw [hn'] at this
    exact ENat.natCast_lt_natCast.1 this
  have hnle : ∀ U : Subgroup G, U ≤ V → ¬ Subgroup.centralizer (U : Set G) ≤ M →
      n ≤ E3.mQuot V U := by
    intro U hUV' hCU
    have h := iInf₂_le (f := fun U (_ : U ∈ {U : Subgroup G |
        U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ M}) => (E3.mQuot V U : ℕ∞)) U
      ⟨hUV', hCU⟩
    have h' : rMV M V ≤ (E3.mQuot V U : ℕ∞) := h
    rw [hn'] at h'
    exact ENat.natCast_le_natCast.1 h'
  have hex : ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ M ∧
      E3.mQuot V U = n := by
    by_contra h
    push_neg at h
    have hge : ((n + 1 : ℕ) : ℕ∞) ≤ rMV M V := by
      refine le_iInf₂ fun U hU => ?_
      have h1 : n ≤ E3.mQuot V U := hnle U hU.1 hU.2
      have h2 : E3.mQuot V U ≠ n := h U hU.1 hU.2
      exact ENat.natCast_le_natCast.2 (by omega)
    rw [hn'] at hge
    exact absurd (ENat.natCast_le_natCast.1 hge) (by omega)
  obtain ⟨U, hUV, hCU, hUeq⟩ := hex
  have hneq : U ≠ ⊥ := by
    intro hbot
    have hm := mBar_le_mQuot_bot (M := M) hV
    rw [hbot] at hUeq
    omega
  refine ⟨U, ⟨hUV, hneq, hCU, ?_⟩, ?_⟩
  · exact eleven_d hV hMV hUV (by rw [hUeq]; exact hn_lt)
  · have : (E3.mQuot V U : ℕ∞) = (n : ℕ∞) := by exact_mod_cast hUeq
    exact this.trans hn

theorem kProper_subgroup (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (H : Subgroup G) :
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog ↥H :=
  CFSG.LocalAnalysis.ComponentInitial.kProper_subgroup
    (C := CFSG.Assembly.InCatalog) (hC := CFSG.Assembly.inCatalog_isoInvariant) hK H

theorem exists_normalizer_gt_of_isPGroup {S P : Subgroup G} (hS : IsPGroup 2 S) (hP : P ≤ S)
    (hne : P ≠ S) : ∃ b ∈ S, b ∈ Subgroup.normalizer (P : Set G) ∧ b ∉ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥S := hS.isNilpotent
  have hlt : P.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hP
    intro y hy
    have : (⟨y, hy⟩ : ↥S) ∈ P.subgroupOf S := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
  have hlt2 : P.subgroupOf S < Subgroup.normalizer ((P.subgroupOf S : Subgroup ↥S) : Set ↥S) :=
    hnc _ hlt
  obtain ⟨b, hbN, hbP⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 hlt2).2
  refine ⟨(b : G), b.2, ?_, fun hb => hbP (Subgroup.mem_subgroupOf.2 hb)⟩
  have hbsub : b ∈ (Subgroup.normalizer (P : Set G)).subgroupOf S := by
    rw [Subgroup.subgroupOf_normalizer_eq hP]
    exact hbN
  exact Subgroup.mem_subgroupOf.1 hbsub

theorem eq_of_isSylowOf_of_isPGroup_le {Q K P : Subgroup G} (hQ : IsSylowOf 2 Q K)
    (hQP : Q ≤ P) (hPK : P ≤ K) (hP2 : IsPGroup 2 P) : P = Q := by
  by_contra hne
  have hmq : E3.mQuot P Q ≠ 0 := fun h0 =>
    hne ((E3.mQuot_eq_zero_iff hP2 hQP).1 h0).symm
  have h2dvd : 2 ∣ Q.relIndex P := by
    rw [E3.relIndex_eq_two_pow hP2 Q]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmq
    rw [hk, pow_succ]
    exact dvd_mul_left (2 : ℕ) _
  have hdvd : 2 ∣ Q.relIndex K := by
    rw [← Subgroup.relIndex_mul_relIndex (H := Q) (K := P) (L := K) hQP hPK]
    exact dvd_mul_of_dvd_left h2dvd _
  exact hQ.2.2 hdvd

theorem eleven_two_sylow {M V Q U : Subgroup G} (hV : IsElemAbelian 2 V) (hVM : V ≤ M)
    (huniq : UniqueMax M (Subgroup.normalizer (Q : Set G) ⊓ M))
    (hQ : CFSG.RankThree.PartOne.IsSylowOf 2 Q (M ⊓ Subgroup.centralizer (V : Set G)))
    (hU : U ∈ gammaEleven M V) :
    CFSG.RankThree.PartOne.IsSylowOf 2 Q (Subgroup.centralizer (U : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUV, hUne, hCU, hO⟩ := hU
  have hQleM : Q ≤ M := hQ.1.trans inf_le_left
  have hQleCV : Q ≤ Subgroup.centralizer (V : Set G) := hQ.1.trans inf_le_right
  have hQ2 : IsPGroup 2 Q := hQ.2.1
  have hQH : Q ≤ Subgroup.centralizer (U : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huq : u ∈ Subgroup.centralizer (Q : Set G) := eleven_a hQleCV (hUV hu)
    exact (Subgroup.mem_centralizer_iff.1 huq q hq).symm
  have hVcV : V ≤ Subgroup.centralizer (V : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (B2F.isElemAbelian_comm hV hv hw).symm
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hVK' : V ≤ M ⊓ Subgroup.centralizer (V : Set G) := le_inf hVM hVcV
    have hVne : V ≠ ⊥ := fun h => hUne (le_bot_iff.1 (hUV.trans (le_of_eq h)))
    have h2V : 2 ∣ Nat.card V := by
      obtain ⟨n, hn⟩ := (B2F.isPGroup_of_isElemAbelian hV).exists_card_eq
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact absurd ((Subgroup.eq_bot_iff_card V).2 (by rw [hn, h0, pow_zero])) hVne
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        rw [hn, hk, pow_succ]
        exact dvd_mul_left (2 : ℕ) _
    have h2K' : 2 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G)) :=
      dvd_trans h2V (Subgroup.card_dvd_of_le hVK')
    have hnot := hQ.2.2
    rw [hbot, Subgroup.relIndex_bot_left] at hnot
    exact hnot h2K'
  have hQK_sylow : CFSG.RankThree.PartOne.IsSylowOf 2 Q
      (M ⊓ Subgroup.centralizer (U : Set G)) := by
    have hQK : Q ≤ M ⊓ Subgroup.centralizer (U : Set G) := le_inf hQleM hQH
    refine ⟨hQK, hQ2, ?_⟩
    intro hdvd
    have hQh2 : IsPGroup 2 (Q.subgroupOf (M ⊓ Subgroup.centralizer (U : Set G))) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
    obtain ⟨S, hQS⟩ := hQh2.exists_le_sylow
    have hSne : (Q.subgroupOf (M ⊓ Subgroup.centralizer (U : Set G)) :
          Subgroup ↥(M ⊓ Subgroup.centralizer (U : Set G))) ≠
        (S : Subgroup ↥(M ⊓ Subgroup.centralizer (U : Set G))) := by
      intro heq
      have hnot := S.not_dvd_index
      rw [← heq] at hnot
      exact hnot (by simpa [Subgroup.relIndex] using hdvd)
    obtain ⟨b, hbS, hbN, hbQ⟩ :=
      exists_normalizer_gt_of_isPGroup S.isPGroup' hQS hSne
    have hb'N : (b : G) ∈ Subgroup.normalizer (Q : Set G) := by
      have h := Subgroup.le_normalizer_map
        (H := (Q.subgroupOf (M ⊓ Subgroup.centralizer (U : Set G)) :
          Subgroup ↥(M ⊓ Subgroup.centralizer (U : Set G))))
        (M ⊓ Subgroup.centralizer (U : Set G)).subtype
      have hmap : (Q.subgroupOf (M ⊓ Subgroup.centralizer (U : Set G)) :
            Subgroup ↥(M ⊓ Subgroup.centralizer (U : Set G))).map
            (M ⊓ Subgroup.centralizer (U : Set G)).subtype = Q := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQK]
      rw [hmap] at h
      exact h ⟨b, hbN, rfl⟩
    have hb'K : (b : G) ∈ M ⊓ Subgroup.centralizer (U : Set G) := b.2
    have hb'2 : IsPGroup 2 (Subgroup.zpowers (b : G)) :=
      (S.isPGroup'.map (M ⊓ Subgroup.centralizer (U : Set G)).subtype).to_le
        (Subgroup.zpowers_le.2 ⟨b, hbS, rfl⟩)
    have hb'K' : (b : G) ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨hb'K.1, ?_⟩
      have hpow : ∃ n, orderOf (b : G) = 2 ^ n := by
        obtain ⟨n, hn⟩ := hb'2.exists_card_eq
        exact ⟨n, by rwa [Nat.card_zpowers] at hn⟩
      exact hO (Subgroup.subset_closure ⟨hb'K, hpow⟩)
    have hP2 : IsPGroup 2 ↥(Q ⊔ Subgroup.zpowers (b : G)) :=
      hQ2.to_sup_of_normal_left' hb'2 (Subgroup.zpowers_le.2 hb'N)
    have hPK' : Q ⊔ Subgroup.zpowers (b : G) ≤ M ⊓ Subgroup.centralizer (V : Set G) :=
      sup_le hQ.1 (Subgroup.zpowers_le.2 hb'K')
    have hneP : Q ⊔ Subgroup.zpowers (b : G) ≠ Q := by
      intro heq
      have hbQ' : (b : G) ∈ Q := by
        have : (b : G) ∈ Q ⊔ Subgroup.zpowers (b : G) :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers (b : G))
        rwa [heq] at this
      exact hbQ (Subgroup.mem_subgroupOf.2 hbQ')
    exact hneP (eq_of_isSylowOf_of_isPGroup_le hQ le_sup_left hPK' hP2)
  refine ⟨hQH, hQ2, ?_⟩
  intro hdvd
  have hQh2 : IsPGroup 2 (Q.subgroupOf (Subgroup.centralizer (U : Set G))) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  obtain ⟨S, hQS⟩ := hQh2.exists_le_sylow
  have hSne : (Q.subgroupOf (Subgroup.centralizer (U : Set G)) :
        Subgroup ↥(Subgroup.centralizer (U : Set G))) ≠
      (S : Subgroup ↥(Subgroup.centralizer (U : Set G))) := by
    intro heq
    have hnot := S.not_dvd_index
    rw [← heq] at hnot
    exact hnot (by simpa [Subgroup.relIndex] using hdvd)
  obtain ⟨b, hbS, hbN, hbQ⟩ :=
    exists_normalizer_gt_of_isPGroup S.isPGroup' hQS hSne
  have hb'N : (b : G) ∈ Subgroup.normalizer (Q : Set G) := by
    have h := Subgroup.le_normalizer_map
      (H := (Q.subgroupOf (Subgroup.centralizer (U : Set G)) :
        Subgroup ↥(Subgroup.centralizer (U : Set G))))
      (Subgroup.centralizer (U : Set G)).subtype
    have hmap : (Q.subgroupOf (Subgroup.centralizer (U : Set G)) :
          Subgroup ↥(Subgroup.centralizer (U : Set G))).map
          (Subgroup.centralizer (U : Set G)).subtype = Q := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQH]
    rw [hmap] at h
    exact h ⟨b, hbN, rfl⟩
  have hb'M : (b : G) ∈ M := eleven_b huniq hQne hQ2 inf_le_left hb'N
  have hb'K : (b : G) ∈ M ⊓ Subgroup.centralizer (U : Set G) := ⟨hb'M, b.2⟩
  have hb'2 : IsPGroup 2 (Subgroup.zpowers (b : G)) :=
    (S.isPGroup'.map (Subgroup.centralizer (U : Set G)).subtype).to_le
      (Subgroup.zpowers_le.2 ⟨b, hbS, rfl⟩)
  have hP2 : IsPGroup 2 ↥(Q ⊔ Subgroup.zpowers (b : G)) :=
    hQ2.to_sup_of_normal_left' hb'2 (Subgroup.zpowers_le.2 hb'N)
  have hPK : Q ⊔ Subgroup.zpowers (b : G) ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    sup_le (le_inf hQleM hQH) (Subgroup.zpowers_le.2 hb'K)
  have hneP : Q ⊔ Subgroup.zpowers (b : G) ≠ Q := by
    intro heq
    have hbQ' : (b : G) ∈ Q := by
      have : (b : G) ∈ Q ⊔ Subgroup.zpowers (b : G) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers (b : G))
      rwa [heq] at this
    exact hbQ (Subgroup.mem_subgroupOf.2 hbQ')
  exact hneP (eq_of_isSylowOf_of_isPGroup_le hQK_sylow le_sup_left hPK hP2)

theorem eleven_three {M V U H : Subgroup G}
    (hH : H = Subgroup.centralizer (U : Set G))
    (hKH : CFSG.Assembly.KProper CFSG.Assembly.InCatalog ↥H) (hcharH : IsCharacteristicP 2 ↥H)
    (T : Sylow 2 ↥H)
    (hcore : (characteristicCoreStar (T : Subgroup ↥H)).map H.subtype ≤ M) :
    (⊤ : Subgroup ↥H) = (⊤ ⊓ M.subgroupOf H) ⊔
      ⨆ (Y : Subgroup ↥H) (_ : Y ∈ blocksStar (T : Subgroup ↥H))
        (_ : ¬ (Y.map H.subtype) ≤ M), Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (⨆ (Y : Subgroup ↥H) (_ : Y ∈ blocksStar (T : Subgroup ↥H)), Y) ⊔
      characteristicCoreStar (T : Subgroup ↥H) = ⊤ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved (G := ↥H) hKH hcharH T
  have hcore' : characteristicCoreStar (T : Subgroup ↥H) ≤ M.subgroupOf H := by
    rw [Subgroup.subgroupOf, Subgroup.comap_subtype]
    exact (Subgroup.map_le_iff_le_comap).1 hcore
  refine le_antisymm ?_ le_top
  refine (le_of_eq hfac.symm).trans ?_
  refine sup_le ?_ ?_
  · refine iSup₂_le fun Y hY => ?_
    by_cases hYM : Y.map H.subtype ≤ M
    · exact le_sup_of_le_left (le_inf le_top ((Subgroup.map_le_iff_le_comap).1 hYM))
    · exact le_sup_of_le_right (le_iSup_of_le Y (le_iSup_of_le hY (le_iSup_of_le hYM le_rfl)))
  · exact le_sup_of_le_left (le_inf le_top hcore')

theorem eleven_three_uncond {M V Q U H : Subgroup G}
    (hH : H = Subgroup.centralizer (U : Set G))
    (hset : Setting11 M V Q)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hU : U ∈ gammaEleven M V)
    (T : Sylow 2 ↥H) (hT : (T : Subgroup ↥H).map H.subtype = Q) :
    (⊤ : Subgroup ↥H) = (⊤ ⊓ M.subgroupOf H) ⊔
      ⨆ (Y : Subgroup ↥H) (_ : Y ∈ blocksStar (T : Subgroup ↥H))
        (_ : ¬ (Y.map H.subtype) ≤ M), Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUne : U ≠ ⊥ := hU.2.1
  have hU2 : IsPGroup 2 U := (B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).to_le hU.1
  have hQ2 : IsPGroup 2 Q := hset.sylowQ.2.1
  have hQleM : Q ≤ M := hset.sylowQ.1.trans inf_le_left
  have hQleCV : Q ≤ Subgroup.centralizer (V : Set G) := hset.sylowQ.1.trans inf_le_right
  have hQH : Q ≤ H := by
    rw [hH]
    exact hQleCV.trans (Subgroup.centralizer_le hU.1)
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hVcV : V ≤ Subgroup.centralizer (V : Set G) := fun v hv => by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (B2F.isElemAbelian_comm hset.isElemAbelian hv hw).symm
    have hVK' : V ≤ M ⊓ Subgroup.centralizer (V : Set G) := le_inf hset.V_le_M hVcV
    have hVne : V ≠ ⊥ := fun h => hUne (le_bot_iff.1 (hU.1.trans (le_of_eq h)))
    have h2V : 2 ∣ Nat.card V := by
      obtain ⟨n, hn⟩ := (B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).exists_card_eq
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact absurd ((Subgroup.eq_bot_iff_card V).2 (by rw [hn, h0, pow_zero])) hVne
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        rw [hn, hk, pow_succ]
        exact dvd_mul_left (2 : ℕ) _
    have h2K' : 2 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G)) :=
      dvd_trans h2V (Subgroup.card_dvd_of_le hVK')
    have hnot := hset.sylowQ.2.2
    rw [hbot, Subgroup.relIndex_bot_left] at hnot
    exact hnot h2K'
  have hT' : (T : Subgroup ↥H) = Q.subgroupOf H := by
    rw [Subgroup.subgroupOf, ← hT]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective T).symm
  have hC : Subgroup.centralizer (omegaOneCenterIn Q : Set G) ⊓ H ≤ M := by
    refine (inf_le_left.trans
      (Subgroup.centralizer_le_normalizer (omegaOneCenterIn Q : Set G))).trans ?_
    haveI : ((omegaOneCenterIn Q).subgroupOf Q).Characteristic :=
      characteristic_omegaOneCenterIn Q
    have hω0 : omegaOneCenterIn Q ≠ ⊥ := omegaOneCenterIn_ne_bot hQ2 hQne
    have hω2 : IsPGroup 2 (omegaOneCenterIn Q) := hQ2.to_le (omegaOneCenterIn_le Q)
    have hN : Subgroup.normalizer (Q : Set G) ⊓ M ≤
        Subgroup.normalizer (omegaOneCenterIn Q : Set G) := by
      refine inf_le_left.trans ?_
      have hmap : ((omegaOneCenterIn Q).subgroupOf Q).map Q.subtype = omegaOneCenterIn Q :=
        Subgroup.map_subgroupOf_eq_of_le (omegaOneCenterIn_le Q)
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        ((omegaOneCenterIn Q).subgroupOf Q)
      rwa [hmap] at h
    exact eleven_b hset.uniqueMax hω0 hω2 hN
  have hN : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS Q →
      (B.subgroupOf (pushingUpS Q)).Characteristic → Subgroup.normalizer (B : Set G) ⊓ H ≤ M := by
    intro B hB0 hBS hBc
    refine inf_le_left.trans ?_
    have hBQ : B ≤ Q := hBS.trans (inf_le_left : pushingUpS Q ≤ Q)
    have h1 : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (pushingUpS Q : Set G) := by
      haveI : ((pushingUpS Q).subgroupOf Q).Characteristic := characteristic_pushingUpS Q
      have hmap : ((pushingUpS Q).subgroupOf Q).map Q.subtype = pushingUpS Q :=
        Subgroup.map_subgroupOf_eq_of_le (inf_le_left : pushingUpS Q ≤ Q)
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        ((pushingUpS Q).subgroupOf Q)
      rwa [hmap] at h
    have h2 : Subgroup.normalizer (pushingUpS Q : Set G) ≤
        Subgroup.normalizer (B : Set G) := by
      haveI : (B.subgroupOf (pushingUpS Q)).Characteristic := hBc
      have hmap : (B.subgroupOf (pushingUpS Q)).map (pushingUpS Q).subtype = B :=
        Subgroup.map_subgroupOf_eq_of_le hBS
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (B.subgroupOf (pushingUpS Q))
      rwa [hmap] at h
    exact eleven_b hset.uniqueMax hB0 (hQ2.to_le hBQ) ((inf_le_left.trans h1).trans h2)
  have hcore : (characteristicCoreStar (T : Subgroup ↥H)).map H.subtype ≤ M :=
    calc (characteristicCoreStar (T : Subgroup ↥H)).map H.subtype
        ≤ (M.subgroupOf H).map H.subtype :=
          Subgroup.map_mono (CFSG.CGT.PushingUpLit.Glue.characteristicCoreStar_subgroupOf_le
            (T' := T) hT' hQH hC hN)
      _ = M ⊓ H := Subgroup.subgroupOf_map_subtype M H
      _ ≤ M := inf_le_left
  exact eleven_three (V := V) hH (kProper_subgroup hK H)
    (by rw [hH]; exact eleven_e hset.charTwo hUne hU2) T hcore

theorem mQuot_inf_le_add {V A B : Subgroup G} (hV : IsPGroup 2 V) :
    E3.mQuot V (A ⊓ B) ≤ E3.mQuot V A + E3.mQuot V B := by
  have h := Subgroup.relIndex_inf_le (H := A) (K := B) (L := V)
  rw [E3.relIndex_eq_two_pow hV, E3.relIndex_eq_two_pow hV, E3.relIndex_eq_two_pow hV,
    ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem eleven_five {M V U : Subgroup G} (hMmax : rankThreeIsMaxTwoLocal M)
    (h114 : (∀ g ∈ M, U ⊓ conjSubgroup U g ∈ gammaEleven M V) →
      ∃ (E : Subgroup G) (L : Set (Subgroup G)), M ≤ Subgroup.normalizer (E : Set G) ∧
        (∀ A ∈ L, A ≤ E) ∧ (∀ A ∈ L, E ≤ Subgroup.normalizer (A : Set G)) ∧
        (∀ A ∈ L, ¬ A ≤ M → pCoreOf 2 A ≠ ⊥) ∧ ∃ A ∈ L, ¬ A ≤ M) :
    ∃ g ∈ M, U ⊓ conjSubgroup U g ∉ gammaEleven M V := by
  by_contra hall
  push_neg at hall
  obtain ⟨E, L, hEinv, hLsub, hLnormal, hLo2, A, hAL, hAM⟩ := h114 hall
  have hO2A : pCoreOf 2 A ≠ ⊥ := hLo2 A hAL hAM
  have hAE : A ≤ E := hLsub A hAL
  have hAnorm : E ≤ Subgroup.normalizer (A : Set G) := hLnormal A hAL
  have hle : pCoreOf 2 A ≤ pCoreOf 2 E := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      (le_trans (CFSG.openPCoreOf_le 2 A) hAE) ?_ ?_
    · exact hAnorm.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pCore 2 ↥A))
    · exact (CFSG.pCore_isPGroup (p := 2) (G := ↥A)).map A.subtype
  have hRne : pCoreOf 2 E ≠ ⊥ := fun hbot =>
    hO2A (le_bot_iff.1 (hle.trans (le_of_eq hbot)))
  have hR2 : IsPGroup 2 (pCoreOf 2 E) := (CFSG.pCore_isPGroup (p := 2) (G := ↥E)).map E.subtype
  have hNE_R : Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 E : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pCore 2 ↥E)
  have hE_R : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set G) :=
    (Subgroup.le_normalizer (H := E)).trans hNE_R
  have hM_R : M ≤ Subgroup.normalizer (pCoreOf 2 E : Set G) := hEinv.trans hNE_R
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 E : Set G)) :=
    ⟨pCoreOf 2 E, hRne, hR2, rfl⟩
  have hEq : Subgroup.normalizer (pCoreOf 2 E : Set G) = M := hMmax.2 _ hloc hM_R
  exact hAM (hAE.trans (hE_R.trans (le_of_eq hEq)))

theorem eleven_six {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (h115 : ∀ U ∈ deltaEleven M V, ∃ g ∈ M, U ⊓ conjSubgroup U g ∉ gammaEleven M V) :
    (mBar M ⊥ V hV : ℕ∞) ≤ 2 * rMV M V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  by_cases hlt : rMV M V < (mBar M ⊥ V hV : ℕ∞)
  · obtain ⟨U, hU⟩ := eleven_f hV hMV hlt
    obtain ⟨g, hgM, hgnot⟩ := h115 U hU
    have hWV : U ⊓ conjSubgroup U g ≤ V := inf_le_left.trans hU.1.1
    have hUgV : conjSubgroup U g ≤ V := by
      rw [← conjSubgroup_eq_iff_mem_normalizer.2 (hMV hgM)]
      exact conjSubgroup_mono_left g hU.1.1
    have hmW : mBar M ⊥ V hV ≤ E3.mQuot V (U ⊓ conjSubgroup U g) := by
      by_contra hcon
      push_neg at hcon
      have hO := eleven_d hV hMV hWV hcon
      have hWne : U ⊓ conjSubgroup U g ≠ ⊥ := by
        intro hbot
        have := mBar_le_mQuot_bot (M := M) hV
        rw [hbot] at hcon
        omega
      have hCW : ¬ Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G) ≤ M := by
        intro hle
        exact hU.1.2.2.1 ((Subgroup.centralizer_le inf_le_left).trans hle)
      exact hgnot ⟨hWV, hWne, hCW, hO⟩
    have h2 : (E3.mQuot V (U ⊓ conjSubgroup U g) : ℕ∞) ≤ 2 * rMV M V := by
      have hsub := mQuot_inf_le_add (V := V) (A := U) (B := conjSubgroup U g) hVpg
      have hVg : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.2 (hMV hgM)
      have hmc : E3.mQuot V (conjSubgroup U g) = E3.mQuot V U := by
        conv_lhs => rw [← hVg]
        rw [mQuot_conjSubgroup]
      calc (E3.mQuot V (U ⊓ conjSubgroup U g) : ℕ∞)
          ≤ ((E3.mQuot V U + E3.mQuot V (conjSubgroup U g) : ℕ) : ℕ∞) := by
            exact_mod_cast hsub
        _ = (E3.mQuot V U : ℕ∞) + (E3.mQuot V (conjSubgroup U g) : ℕ∞) := by
            rw [Nat.cast_add]
        _ = rMV M V + rMV M V := by
            rw [show (E3.mQuot V (conjSubgroup U g) : ℕ∞) = rMV M V from by rw [hmc, hU.2],
              hU.2]
        _ = 2 * rMV M V := by rw [two_mul]
    exact le_trans (by exact_mod_cast hmW) h2
  · push_neg at hlt
    calc (mBar M ⊥ V hV : ℕ∞) ≤ rMV M V := hlt
      _ ≤ 2 * rMV M V := by
        rw [two_mul]
        exact le_add_of_nonneg_right zero_le

end CFSG.LocalAnalysis.WeakClosure81
