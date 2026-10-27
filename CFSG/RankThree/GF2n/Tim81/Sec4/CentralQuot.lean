module

public import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTIBasic
public import CFSG.CGT.Timmesfeld75.Core214Proof
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.RankThree.GF2n.Tim81.CentralTI

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement Pointwise

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_sylow_le_normalizer {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y))) :
    ∃ S : Sylow 2 Y, (S : Subgroup Y) ≤ Subgroup.normalizer (T : Set Y) ∧ T ≤ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup Y := Subgroup.normalizer (T : Set Y)
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hTpN : IsPGroup 2 (T.subgroupOf N) := hT.comap_subtype
  obtain ⟨S₀, hS₀⟩ := hTpN.exists_le_sylow
  let U : Subgroup Y := (S₀ : Subgroup ↥N).map N.subtype
  have hUp : IsPGroup 2 U := S₀.isPGroup'.map N.subtype
  have hTU : T ≤ U := by
    intro t ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hTN ht⟩, hS₀ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hUN : U ≤ N := Subgroup.map_subtype_le _
  obtain ⟨S, hUS⟩ := hUp.exists_le_sylow
  refine ⟨S, ?_, hTU.trans hUS⟩
  by_contra hnot
  have hne : (U.subgroupOf (S : Subgroup Y)) ≠ ⊤ := by
    intro htop
    apply hnot
    intro s hs
    have hsin : (⟨s, hs⟩ : ↥S) ∈ (⊤ : Subgroup ↥S) := Subgroup.mem_top _
    rw [← htop] at hsin
    exact hUN (Subgroup.mem_subgroupOf.mp hsin)
  have hlt : (U.subgroupOf (S : Subgroup Y)) < ⊤ := lt_of_le_of_ne le_top hne
  haveI : Group.IsNilpotent ↥S := S.isPGroup'.isNilpotent
  have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent (G := ↥S)
  obtain ⟨y, hyNorm, hyU⟩ :=
    SetLike.exists_of_lt (hnc (U.subgroupOf (S : Subgroup Y)) hlt)
  have hyconj : conjSubgroup y (U.subgroupOf (S : Subgroup Y)) = U.subgroupOf (S : Subgroup Y) :=
    mem_normalizer_iff_conjSubgroup_eq.mp hyNorm
  have hyUY : conjSubgroup (y : Y) U = U := by
    have h := congrArg (Subgroup.map (S : Subgroup Y).subtype) hyconj
    rwa [map_conjSubgroup, Subgroup.map_subgroupOf_eq_of_le hUS] at h
  have hyT : conjSubgroup (y : Y) T = T :=
    hwc.2 (y : Y) (by
      calc conjSubgroup (y : Y) T ≤ conjSubgroup (y : Y) U := Subgroup.map_mono hTU
        _ = U := hyUY
        _ ≤ N := hUN)
  have hyN : (y : Y) ∈ N := mem_normalizer_iff_conjSubgroup_eq.mpr hyT
  let Q : Subgroup Y := U ⊔ Subgroup.zpowers (y : Y)
  have hQS : Q ≤ (S : Subgroup Y) :=
    sup_le hUS (Subgroup.zpowers_le.mpr y.2)
  have hQp : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  have hQN : Q ≤ N := sup_le hUN (Subgroup.zpowers_le.mpr hyN)
  have hQ0p : IsPGroup 2 (Q.subgroupOf N) := hQp.comap_subtype
  have hS₀Q : (S₀ : Subgroup ↥N) ≤ Q.subgroupOf N := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩))
  have hQeq : Q.subgroupOf N = (S₀ : Subgroup ↥N) := S₀.is_maximal' hQ0p hS₀Q
  have hyQ : (⟨(y : Y), hyN⟩ : ↥N) ∈ Q.subgroupOf N :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  rw [hQeq] at hyQ
  have hyU' : (y : Y) ∈ U := by
    have hmem : N.subtype ⟨(y : Y), hyN⟩ ∈ U :=
      Subgroup.mem_map_of_mem (f := N.subtype) hyQ
    simpa using hmem
  exact hyU (Subgroup.mem_subgroupOf.mpr hyU')

theorem normalizer_sylow_le_normalizer {T : Subgroup Y} (hwc : WeaklyClosedIn T
    (Subgroup.normalizer (T : Set Y))) {S : Sylow 2 Y} (hTS : T ≤ S)
    (hSN : (S : Subgroup Y) ≤ Subgroup.normalizer (T : Set Y)) :
    Subgroup.normalizer (S : Set Y) ≤ Subgroup.normalizer (T : Set Y) := by
  intro b hb
  have hb' : conjSubgroup b (S : Subgroup Y) = S :=
    mem_normalizer_iff_conjSubgroup_eq.1 hb
  exact mem_normalizer_iff_conjSubgroup_eq.mpr (hwc.2 b (by
    calc conjSubgroup b T ≤ conjSubgroup b (S : Subgroup Y) := Subgroup.map_mono hTS
      _ = S := hb'
      _ ≤ Subgroup.normalizer (T : Set Y) := hSN))

theorem inf_eq_bot_of_not_normal {T Z : Subgroup Y} [Z.Normal] (hTI : IsTI T)
    (hZ : Z ≤ Subgroup.center Y) (hnot : ¬ T.Normal) : T ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  by_contra hz1
  have hz1' : z ≠ 1 := fun h => hz1 (by simpa [h])
  have hzT : z ∈ T := (Subgroup.mem_inf.mp hz).1
  have hzZ : z ∈ Z := (Subgroup.mem_inf.mp hz).2
  have hzconj : ∀ y : Y, z ∈ conjSubgroup y T := by
    intro y
    rw [mem_conjSubgroup]
    have h : y⁻¹ * z * y = z := by
      rw [Subgroup.mem_center_iff.mp (hZ hzZ) y⁻¹]
      group
    rwa [h]
  have hle : ∀ y : Y, T ≤ conjSubgroup y T := by
    intro y
    have hz' : z ∈ T ⊓ conjSubgroup y T := ⟨hzT, hzconj y⟩
    rcases hTI y with h | h
    · rw [h] at hz'
      exact absurd (Subgroup.mem_bot.mp hz') hz1'
    · simpa [h] using (inf_le_right : T ⊓ conjSubgroup y T ≤ conjSubgroup y T)
  refine hnot ⟨fun x hx g => ?_⟩
  have hxg : x ∈ conjSubgroup g⁻¹ T := by
    rw [conjSubgroup_eq_of_ge (hle g⁻¹)]
    exact hx
  rw [mem_conjSubgroup] at hxg
  simpa using hxg

theorem map_sup_conj_eq_top {T Z : Subgroup Y} [Z.Normal] {g : Y}
    (h : T ⊔ conjSubgroup g T = ⊤) :
    T.map (QuotientGroup.mk' Z) ⊔
        conjSubgroup (QuotientGroup.mk' Z g) (T.map (QuotientGroup.mk' Z)) = ⊤ := by
  rw [← map_conjSubgroup, ← Subgroup.map_sup, h,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]

@[expose] def WeakTI {L : Type*} [Group L] (T : Subgroup L) : Prop :=
  ∀ t ∈ T, t ≠ 1 → ∀ y : L, y * t = t * y → Odd (orderOf y) →
    y ∈ Subgroup.normalizer (T : Set L)

theorem weakTI_map {T Z : Subgroup Y} [Z.Normal] (hT : Assembly.IsElemAbelian 2 T)
    (hTI : IsTI T) (hZ : Z ≤ Subgroup.center Y) :
    WeakTI (T.map (QuotientGroup.mk' Z)) := by
  classical
  intro tbar htbar htbar1 ybar hybar hodd
  obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp htbar
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z ybar
  have ht1 : t ≠ 1 := by
    intro h
    exact htbar1 (by rw [h, map_one])
  have ht2 : t ^ 2 = 1 := hT.2 t htT
  let c : Y := ⁅t, y⁆
  have hcZ : c ∈ Z := by
    apply (QuotientGroup.eq_one_iff c).mp
    change (QuotientGroup.mk' Z) ⁅t, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hybar.symm
  have hct : c * t = t * c := (Subgroup.mem_center_iff.mp (hZ hcZ) t).symm
  have hcy : c * y = y * c := (Subgroup.mem_center_iff.mp (hZ hcZ) y).symm
  have hc2 : c ^ 2 = 1 := by
    have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
    have h1 : (t * c) ^ 2 = 1 := by
      have htc : t * c = y * t * y⁻¹ := by
        change t * ⁅t, y⁆ = y * t * y⁻¹
        rw [commutatorElement_def,
          show t * (t * y * t⁻¹ * y⁻¹) = (t * t) * (y * t⁻¹ * y⁻¹) by group,
          ht2', one_mul, inv_eq_of_mul_eq_one_right ht2']
      rw [htc, conj_pow, ht2, mul_one, mul_inv_cancel]
    have h2 : (t * c) ^ 2 = c ^ 2 := by
      rw [Commute.mul_pow (Commute.symm hct), ht2, one_mul]
    rwa [h2] at h1
  have hyk : y ^ orderOf (QuotientGroup.mk' Z y) ∈ Z := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' Z) (y ^ orderOf (QuotientGroup.mk' Z y)) = 1
    rw [map_pow]
    exact pow_orderOf_eq_one _
  have hck : c ^ orderOf (QuotientGroup.mk' Z y) = 1 := by
    rw [Commute.commutatorElement_pow_right (h := (Subgroup.mem_center_iff.mp (hZ hcZ) y))]
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hZ hyk) t
  have hc1 : c = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have h := hck
    rw [show orderOf (QuotientGroup.mk' Z y) = 2 * m + 1 from hm, pow_succ, pow_mul,
      hc2, one_pow, one_mul] at h
    exact h
  have hty : t * y = y * t :=
    (commutatorElement_eq_one_iff_mul_comm).mp (by simpa [c] using hc1)
  have hyt : y * t = t * y := hty.symm
  have hyN : y ∈ Subgroup.normalizer (T : Set Y) := by
    refine CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTI htT ht1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hyt.symm
  refine mem_normalizer_iff_conjSubgroup_eq.mpr ?_
  rw [← map_conjSubgroup, mem_normalizer_iff_conjSubgroup_eq.mp hyN]

theorem isWC_of_isTI {T : Subgroup Y} (hT : Assembly.IsElemAbelian 2 T) (hTI : IsTI T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y))) : IsWC T := by
  refine ⟨hT, ?_⟩
  intro t ht ht1
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact congrArg Subtype.val (hT.1.is_comm.comm ⟨t, ht⟩ ⟨x, hx⟩)
  · intro g hg
    refine hwc.2 g ?_
    intro x hx
    refine CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTI ht ht1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Subgroup.mem_centralizer_iff.mp (hg hx) t (Set.mem_singleton t)

private theorem weaklyClosedIn_subgroupOf_centralizer {T : Subgroup Y} {t : Y}
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hTC : T ≤ Subgroup.centralizer ({t} : Set Y)) :
    WeaklyClosedIn (T.subgroupOf (Subgroup.centralizer ({t} : Set Y)))
      (Subgroup.normalizer
        (T.subgroupOf (Subgroup.centralizer ({t} : Set Y)) : Set _)) := by
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro c hc
  have hmap_le : (conjSubgroup c (T.subgroupOf (Subgroup.centralizer ({t} : Set Y)))).map
      (Subgroup.centralizer ({t} : Set Y)).subtype ≤
      Subgroup.normalizer (T : Set Y) := by
    calc (conjSubgroup c (T.subgroupOf (Subgroup.centralizer ({t} : Set Y)))).map
          (Subgroup.centralizer ({t} : Set Y)).subtype
        ≤ (Subgroup.normalizer
            (T.subgroupOf (Subgroup.centralizer ({t} : Set Y)) : Set _)).map
            (Subgroup.centralizer ({t} : Set Y)).subtype := Subgroup.map_mono hc
      _ ≤ Subgroup.normalizer
            ((T.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map
              (Subgroup.centralizer ({t} : Set Y)).subtype : Set Y) :=
          Subgroup.le_normalizer_map (Subgroup.centralizer ({t} : Set Y)).subtype
      _ = Subgroup.normalizer (T : Set Y) := by
          rw [Subgroup.map_subgroupOf_eq_of_le hTC]
  have hconjY : conjSubgroup (c : Y) T = T := by
    refine hwc.2 (c : Y) ?_
    rwa [map_conjSubgroup, Subgroup.map_subgroupOf_eq_of_le hTC] at hmap_le
  apply Subgroup.map_subtype_inj.mp
  rw [map_conjSubgroup, Subgroup.map_subgroupOf_eq_of_le hTC]
  exact hconjY

theorem isWC_of_weakTI {T : Subgroup Y} (hT : Assembly.IsElemAbelian 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y))) (hwti : WeakTI T) :
    IsWC T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 T := CFSG.Open.IsElemAbelian.isPGroup hT
  refine ⟨hT, ?_⟩
  intro t ht ht1
  let C : Subgroup Y := Subgroup.centralizer ({t} : Set Y)
  have hTC : T ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact congrArg Subtype.val (hT.1.is_comm.comm ⟨t, ht⟩ ⟨x, hx⟩)
  have hO_le_NT : CFSG.GroupTheory.oddOrderClosure C ≤
      Subgroup.normalizer (T : Set Y) := by
    rw [CFSG.GroupTheory.oddOrderClosure_le_iff]
    rintro g ⟨hgC, hgodd⟩
    exact hwti t ht ht1 g (by
      have h := Subgroup.mem_centralizer_iff.mp hgC t (Set.mem_singleton t)
      exact h.symm) hgodd
  have hTsub : IsPGroup 2 (T.subgroupOf C) := hTp.comap_subtype
  have hwcC : WeaklyClosedIn (T.subgroupOf C)
      (Subgroup.normalizer (T.subgroupOf C : Set ↥C)) :=
    weaklyClosedIn_subgroupOf_centralizer hwc hTC
  obtain ⟨S, hSN, _⟩ :=
    CFSG.RankThree.GF2n.Tim81.CentralTI.exists_sylow_le_normalizer hTsub hwcC
  let Q : Subgroup Y := (S : Subgroup ↥C).map C.subtype
  have hQ2 : IsPGroup 2 Q := S.isPGroup'.map C.subtype
  have hQC : Q ≤ C := Subgroup.map_subtype_le _
  have hQN : Q ≤ Subgroup.normalizer (T : Set Y) := by
    calc Q = (S : Subgroup ↥C).map C.subtype := rfl
      _ ≤ (Subgroup.normalizer (T.subgroupOf C : Set ↥C)).map C.subtype :=
          Subgroup.map_mono hSN
      _ ≤ Subgroup.normalizer ((T.subgroupOf C).map C.subtype : Set Y) :=
          Subgroup.le_normalizer_map C.subtype
      _ = Subgroup.normalizer (T : Set Y) := by
          rw [Subgroup.map_subgroupOf_eq_of_le hTC]
  have hQS : (Q.subgroupOf C : Subgroup ↥C) = S := by
    change ((S : Subgroup ↥C).map C.subtype).comap C.subtype = S
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hQidx : ¬ 2 ∣ (Q.subgroupOf C).index := by
    rw [hQS]
    exact S.not_dvd_index
  have hsup : CFSG.GroupTheory.oddOrderClosure C ⊔ Q = C :=
    CFSG.GroupTheory.sup_sylow_eq C hQC hQ2 hQidx
  have hC_le_NT : C ≤ Subgroup.normalizer (T : Set Y) := by
    rw [← hsup]
    exact sup_le hO_le_NT hQN
  refine ⟨hTC, ?_⟩
  intro g hg
  exact hwc.2 g (hg.trans hC_le_NT)

theorem isWC_map_mk' {T Z : Subgroup Y} [Z.Normal]
    (hT : Assembly.IsElemAbelian 2 T) (hTI : IsTI T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set Y)))
    (hZ : Z ≤ Subgroup.center Y) : IsWC (T.map (QuotientGroup.mk' Z)) :=
  isWC_of_weakTI (CFSG.Open.IsElemAbelian.map hT (QuotientGroup.mk' Z))
    ⟨Subgroup.le_normalizer, weaklyClosed_map_mk' hZ hwc⟩ (weakTI_map hT hTI hZ)

theorem le_centralizer_of_odd_card {T O : Subgroup Y} (hT : Assembly.IsElemAbelian 2 T)
    (h4 : 4 ≤ Nat.card T) (hTI : IsTI T) (hTO : T ≤ Subgroup.normalizer (O : Set Y))
    (hO : Odd (Nat.card O)) : O ≤ Subgroup.centralizer (T : Set Y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Subgroup.Normalizes T O := ⟨hTO⟩
  letI : CFSG.IsElementaryAbelian 2 ↥T :=
    { toIsMulCommutative := hT.1
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro x
        apply Subtype.ext
        simpa using hT.2 (x : Y) x.2 }
  have hO_le_NT : O ≤ Subgroup.normalizer (T : Set Y) := by
    have hgen := CFSG.SolvableHall.coprime_centralizer_generation
      (p := 2) (A := ↥T) (H := ↥O) (by simpa using h4)
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hO)
    have hle : (⨆ (a : ↥T) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) ↥O) ≤
        (Subgroup.normalizer (T : Set Y)).comap O.subtype := by
      refine iSup₂_le fun a ha => ?_
      intro x hx
      have hfix : a • x = x :=
        (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
      have hval := congrArg (Subtype.val) hfix
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at hval
      exact CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTI a.2
        (fun h => ha (Subtype.ext h)) (by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          have h := congrArg (fun z => z * (a : Y)) hval
          simpa [mul_assoc] using h)
    intro o ho
    have htop : (⟨o, ho⟩ : ↥O) ∈ (⊤ : Subgroup ↥O) := Subgroup.mem_top _
    rw [← hgen] at htop
    exact hle htop
  have hcommO : ⁅O, T⁆ ≤ O := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hTO
  have hcommT : ⁅O, T⁆ ≤ T :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hO_le_NT
  have hdisj : O ⊓ T = ⊥ := by
    have hS2 : IsPGroup 2 ↥(O ⊓ T) := by
      refine isPGroup_iff_pow_pow_eq_one.mpr fun x => ⟨1, ?_⟩
      have hxT : (x : Y) ∈ T := (Subgroup.mem_inf.mp x.2).2
      have hx2 : (x : Y) ^ 2 = 1 := hT.2 _ hxT
      apply Subtype.ext
      simpa using hx2
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(O ⊓ T))).mp hS2
    have hcop : Nat.Coprime (Nat.card ↥(O ⊓ T)) (Nat.card O) := by
      rw [hn]
      exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hO)
    have hcard1 : Nat.card ↥(O ⊓ T) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (Subgroup.card_dvd_of_le inf_le_left)
    exact Subgroup.card_eq_one.mp hcard1
  have hcomm_bot : ⁅O, T⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf hcommO hcommT).trans (le_of_eq hdisj)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot

private theorem zstar_O_odd_quot {N O : Subgroup Y} [N.Normal]
    (hmapO : O.map (QuotientGroup.mk' N) = CFSG.Open.fusionOddCore (Y ⧸ N)) :
    Odd (Nat.card (↥O ⧸ N.subgroupOf O)) := by
  classical
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  let ψ : ↥O →* ↥(CFSG.Open.fusionOddCore (Y ⧸ N)) :=
    MonoidHom.codRestrict (π.comp O.subtype) (CFSG.Open.fusionOddCore (Y ⧸ N))
      (fun x => by
        rw [← hmapO]
        exact Subgroup.mem_map_of_mem π x.2)
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp (show (z : Y ⧸ N) ∈ O.map π by
      rw [hmapO]; exact z.2)
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  have hker : MonoidHom.ker ψ = N.subgroupOf O := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (x : Y)).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : Y)).mpr h
  have e : (↥O ⧸ (N.subgroupOf O)) ≃* ↥(CFSG.Open.fusionOddCore (Y ⧸ N)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  rw [Nat.card_congr e.toEquiv]
  exact odd_card_fusionOddCore (Y ⧸ N)

private theorem zstar_Q_exact {N O : Subgroup Y} [N.Normal]
    (hN : N ≤ Subgroup.center Y) (hNp : IsPGroup 2 N)
    (Q : Subgroup ↥O) (hQcomp : (N.subgroupOf O).IsComplement' Q)
    (hQodd : Odd (Nat.card Q)) :
    ∀ x : ↥O, Odd (orderOf x) → x ∈ Q := by
  intro x hxodd
  obtain ⟨⟨⟨n, hn⟩, ⟨q, hq⟩⟩, hnq, -⟩ := hQcomp.existsUnique x
  have hnqO : n * q = x := by
    have h1 : ((⟨n, hn⟩ : N.subgroupOf O) : ↥O) * ((⟨q, hq⟩ : Q) : ↥O) = x := hnq
    simpa using h1
  have hncomm : Commute n q := by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hN (Subgroup.mem_subgroupOf.mp hn)) (q : Y)).symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNsub_p : IsPGroup 2 (N.subgroupOf O) := hNp.comap_subtype (K := O)
  obtain ⟨k, hk⟩ := hNsub_p.exists_orderOf_eq_pow ⟨n, hn⟩
  rw [Subgroup.orderOf_mk] at hk
  have hqodd : Odd (orderOf q) :=
    Odd.of_dvd_nat hQodd (Subgroup.orderOf_dvd_natCard Q hq)
  have hco : (orderOf n).Coprime (orderOf q) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hqodd)
  have hord := Commute.orderOf_mul_eq_mul_orderOf_of_coprime hncomm hco
  have hxodd' : Odd (orderOf (n * q)) := by rwa [hnqO]
  have hdn : orderOf n ∣ orderOf (n * q) := by
    rw [hord]
    exact dvd_mul_right _ _
  have hoddn : Odd (orderOf n) := Odd.of_dvd_nat hxodd' hdn
  have hn1 : orderOf n = 1 := by
    rw [hk] at hoddn ⊢
    rcases k with _ | k
    · simp
    · exfalso
      have heven : Even (2 ^ (k + 1)) := Even.pow_of_ne_zero (by decide : Even 2) (by omega)
      exact (Nat.not_even_iff_odd.mpr hoddn) heven
  have hn_eq : n = 1 := orderOf_eq_one_iff.mp hn1
  rw [hn_eq, one_mul] at hnqO
  rwa [← hnqO]

private theorem zstar_exists_QY {N O : Subgroup Y} [N.Normal] [O.Normal]
    (hN : N ≤ Subgroup.center Y) (hNp : IsPGroup 2 N) (hN_le_O : N ≤ O)
    (hindex_odd : Odd (N.subgroupOf O).index) :
    ∃ QY : Subgroup Y, QY.Normal ∧ Odd (Nat.card QY) ∧ O = N ⊔ QY := by
  classical
  have hO_normal : O.Normal := inferInstance
  have hNsub_p : IsPGroup 2 (N.subgroupOf O) := hNp.comap_subtype (K := O)
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf O)) (N.subgroupOf O).index := by
    obtain ⟨k, hk⟩ := hNsub_p.exists_card_dvd_pow
    obtain ⟨m, hm, hmk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk
    rw [hmk]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hindex_odd)
  obtain ⟨Q, hQcomp⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  let QY : Subgroup Y := Q.map O.subtype
  have hQodd : Odd (Nat.card Q) := by
    rw [← hQcomp.symm.index_eq_card]
    exact hindex_odd
  have hQYodd : Odd (Nat.card QY) := by
    dsimp [QY]
    rw [Subgroup.card_map_of_injective O.subtype_injective]
    exact hQodd
  have hONQ : O = N ⊔ QY := by
    have h := congrArg (Subgroup.map O.subtype) hQcomp.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hN_le_O, Subgroup.map_top,
      Subgroup.range_subtype] at h
    exact h.symm
  have hQ_exact : ∀ x : ↥O, Odd (orderOf x) → x ∈ Q :=
    zstar_Q_exact hN hNp Q hQcomp hQodd
  have hQY_normal : QY.Normal := by
    refine ⟨fun q hq g => ?_⟩
    obtain ⟨q0, hq0Q, rfl⟩ := Subgroup.mem_map.mp hq
    have hq0_odd : Odd (orderOf q0) :=
      Odd.of_dvd_nat hQodd (Subgroup.orderOf_dvd_natCard Q hq0Q)
    have hconjO : g * (q0 : Y) * g⁻¹ ∈ O := hO_normal.conj_mem q0 q0.2 g
    have hconj_odd : Odd (orderOf (⟨g * (q0 : Y) * g⁻¹, hconjO⟩ : ↥O)) := by
      rw [Subgroup.orderOf_mk]
      rw [show g * (q0 : Y) * g⁻¹ = (MulAut.conj g) (q0 : Y) from rfl,
        (MulAut.conj g).orderOf_eq (q0 : Y), Subgroup.orderOf_coe]
      exact hq0_odd
    have hqQ : (⟨g * (q0 : Y) * g⁻¹, hconjO⟩ : ↥O) ∈ Q := hQ_exact _ hconj_odd
    exact Subgroup.mem_map.mpr ⟨_, hqQ, rfl⟩
  exact ⟨QY, hQY_normal, hQYodd, hONQ⟩

private theorem zstar_sup_top_normal {T N : Subgroup Y} [N.Normal]
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤) (hZ : ZStarCase (Y ⧸ N)) :
    let O : Subgroup Y := (fusionOddCore (Y ⧸ N)).comap (QuotientGroup.mk' N)
    T ⊔ O = ⊤ ∧ (T ⊔ O).Normal := by
  classical
  let O : Subgroup Y := (fusionOddCore (Y ⧸ N)).comap (QuotientGroup.mk' N)
  haveI hO_normal : O.Normal := by
    dsimp [O]
    infer_instance
  have hcomm_le : commutator Y ≤ O := by
    rw [commutator_eq_normalClosure]
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨a, b, rfl⟩
    refine Subgroup.mem_comap.mpr ?_
    rw [commutatorElement_def]
    have h := (zStarCase_iff.mp hZ) (QuotientGroup.mk' N a⁻¹) (QuotientGroup.mk' N b⁻¹)
    simpa [O, map_mul, map_inv, mul_assoc] using h
  haveI hTO_normal : (T ⊔ O).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨t, ht, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hgo : g * o * g⁻¹ ∈ O := hO_normal.conj_mem o ho g
    have hgt : g * t * g⁻¹ ∈ T ⊔ O := by
      have hcomm : ⁅g, t⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top t)
      have hcommO : ⁅g, t⁆ ∈ O := hcomm_le hcomm
      have heq : g * t * g⁻¹ = ⁅g, t⁆ * t := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact (T ⊔ O).mul_mem (Subgroup.mem_sup_right hcommO) (Subgroup.mem_sup_left ht)
    have heq : g * (t * o) * g⁻¹ = (g * t * g⁻¹) * (g * o * g⁻¹) := by group
    rw [heq]
    exact (T ⊔ O).mul_mem hgt (Subgroup.mem_sup_right hgo)
  have hTO_top : T ⊔ O = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgen]
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    exact Subgroup.mem_sup_left hx
  exact ⟨hTO_top, hTO_normal⟩

theorem zstar_normal {T N : Subgroup Y} [N.Normal] (hT : Assembly.IsElemAbelian 2 T)
    (h4 : 4 ≤ Nat.card T) (hTI : IsTI T)
    (hgen : Subgroup.normalClosure (T : Set Y) = ⊤)
    (hN : N ≤ Subgroup.center Y) (hNp : IsPGroup 2 N)
    (hZ : ZStarCase (Y ⧸ N)) : T.Normal := by
  classical
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  let O : Subgroup Y := (fusionOddCore (Y ⧸ N)).comap π
  haveI hO_normal : O.Normal := by
    dsimp [O]
    infer_instance
  have hN_le_O : N ≤ O := by
    intro n hn
    exact Subgroup.mem_comap.mpr (by
      have h : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [h]
      exact (CFSG.Open.fusionOddCore (Y ⧸ N)).one_mem)
  have hmapO : O.map π = fusionOddCore (Y ⧸ N) := by
    dsimp [O]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  have hO_odd_quot : Odd (Nat.card (↥O ⧸ N.subgroupOf O)) :=
    zstar_O_odd_quot (N := N) (O := O) hmapO
  have hindex_odd : Odd (N.subgroupOf O).index := by
    rw [Subgroup.index_eq_card]
    exact hO_odd_quot
  obtain ⟨QY, hQY_normal, hQYodd, hONQ⟩ :=
    zstar_exists_QY (N := N) (O := O) hN hNp hN_le_O hindex_odd
  have hTO_top : T ⊔ O = ⊤ :=
    (zstar_sup_top_normal (T := T) (N := N) hgen hZ).1
  haveI : QY.Normal := hQY_normal
  have hT_le_NQY : T ≤ Subgroup.normalizer (QY : Set Y) :=
    Subgroup.le_normalizer_of_normal (H := QY)
  have hQle : QY ≤ Subgroup.normalizer (T : Set Y) :=
    (le_centralizer_of_odd_card hT h4 hTI hT_le_NQY hQYodd).trans
      (Subgroup.centralizer_le_normalizer (T : Set Y))
  have hYle : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (T : Set Y) := by
    calc (⊤ : Subgroup Y) = T ⊔ O := hTO_top.symm
      _ = T ⊔ (N ⊔ QY) := by rw [hONQ]
      _ ≤ Subgroup.normalizer (T : Set Y) :=
          sup_le Subgroup.le_normalizer
            (sup_le (hN.trans (Subgroup.center_le_normalizer (T : Set Y))) hQle)
  rw [← Subgroup.normalizer_eq_top_iff]
  exact le_antisymm le_top hYle

end CFSG.RankThree.GF2n.Tim81.CentralTI
