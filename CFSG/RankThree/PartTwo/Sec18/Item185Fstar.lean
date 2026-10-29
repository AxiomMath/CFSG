module

import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Simple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Late.Uniqueness
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

private theorem mk_commute_of_mem_pCore {X : Type} [Group X] {b l : X}
    (h : b * l * b⁻¹ * l⁻¹ ∈ CFSG.pCore 2 X) :
    QuotientGroup.mk' (CFSG.pCore 2 X) b * QuotientGroup.mk' (CFSG.pCore 2 X) l =
      QuotientGroup.mk' (CFSG.pCore 2 X) l * QuotientGroup.mk' (CFSG.pCore 2 X) b := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) (b * l * b⁻¹ * l⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h
  simp only [map_mul, map_inv] at h1
  have h2 := mul_inv_eq_one.mp h1
  calc QuotientGroup.mk' (CFSG.pCore 2 X) b * QuotientGroup.mk' (CFSG.pCore 2 X) l
      = (QuotientGroup.mk' (CFSG.pCore 2 X) b * QuotientGroup.mk' (CFSG.pCore 2 X) l *
          (QuotientGroup.mk' (CFSG.pCore 2 X) b)⁻¹) * QuotientGroup.mk' (CFSG.pCore 2 X) b := by
        group
    _ = QuotientGroup.mk' (CFSG.pCore 2 X) l * QuotientGroup.mk' (CFSG.pCore 2 X) b := by
        rw [h2]

private theorem mem_pCore_two_of_mem_pCoreOf {M : Subgroup G} {b l : M}
    (h : (b : G) * (l : G) * (b : G)⁻¹ * (l : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    b * l * b⁻¹ * l⁻¹ ∈ CFSG.pCore 2 M := by
  unfold CFSG.Open.pCoreOf at h
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp h
  have hnb : n = b * l * b⁻¹ * l⁻¹ := Subtype.ext (by simpa using hnx)
  rw [← hnb]
  exact hn

private theorem centralizes_pCore_three {Y : Type} [Group Y] [Finite Y] {Bs P' : Subgroup Y}
    (hP3 : IsPGroup 3 P') (hPidx : ¬ 3 ∣ P'.index)
    (hnorm : ∀ x ∈ P', ∀ b ∈ Bs, x * b * x⁻¹ ∈ Bs)
    (hBO : Bs ⊓ CFSG.pCore 3 Y = ⊥) :
    ∀ x ∈ CFSG.pCore 3 Y, ∀ b ∈ Bs, b * x = x * b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 3 Y).Normal := CFSG.pCore_normal
  intro x hx b hb
  have hle : CFSG.pCore 3 Y ≤ (hP3.toSylow hPidx : Subgroup Y) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup (hP3.toSylow hPidx)
  rw [IsPGroup.toSylow_coe] at hle
  have hxP : x ∈ P' := hle hx
  have hc1 : b * x * b⁻¹ * x⁻¹ ∈ CFSG.pCore 3 Y :=
    mul_mem (Subgroup.Normal.conj_mem inferInstance x hx b) (inv_mem hx)
  have hc2 : b * x * b⁻¹ * x⁻¹ ∈ Bs := by
    have e : b * x * b⁻¹ * x⁻¹ = b * (x * b⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem hb (hnorm x hxP b⁻¹ (inv_mem hb))
  have hc : b * x * b⁻¹ * x⁻¹ = 1 := by
    have hmem : b * x * b⁻¹ * x⁻¹ ∈ Bs ⊓ CFSG.pCore 3 Y := ⟨hc2, hc1⟩
    rw [hBO, Subgroup.mem_bot] at hmem
    exact hmem
  have h2 : b * x * b⁻¹ = x := mul_inv_eq_one.mp hc
  calc b * x = (b * x * b⁻¹) * b := by group
    _ = x * b := by rw [h2]

private theorem le_pCore_of_normal_abelian {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {Z : Subgroup Y} [Z.Normal] (hZab : ∀ z ∈ Z, ∀ w ∈ Z, z * w = w * z)
    {S : Subgroup Y} (hSZ : S ≤ Z) (hS : IsPGroup p S) : S ≤ CFSG.pCore p Y := by
  have hSp : IsPGroup p (S.comap Z.subtype) :=
    hS.comap_of_injective Z.subtype Z.subtype_injective
  have hSn : (S.comap Z.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hcn : ((g * n * g⁻¹ : Z) : Y) = (n : Y) := by
      have h1 : (g : Y) * (n : Y) = (n : Y) * (g : Y) := hZab _ g.2 _ n.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h1]
      group
    show ((g * n * g⁻¹ : Z) : Y) ∈ S
    rw [hcn]
    exact hn
  have hSle : S.comap Z.subtype ≤ CFSG.pCore p Z :=
    le_sSup (show S.comap Z.subtype ∈ {K : Subgroup Z | K.Normal ∧ IsPGroup p K} from
      ⟨hSn, hSp⟩)
  have hSle' : S ≤ CFSG.Open.pCoreOf p Z := by
    intro s hs
    have hmem : (⟨s, hSZ hs⟩ : Z) ∈ S.comap Z.subtype := hs
    exact Subgroup.mem_map.mpr ⟨⟨s, hSZ hs⟩, hSle hmem, rfl⟩
  exact hSle'.trans
    (CFSG.RankThree.PartTwo.Late.pCoreOf_le_pCore_of_isSubnormal p
      (Subgroup.Normal.isSubnormal inferInstance))

private theorem normal_centralizer_inf_generalizedFitting {Y : Type} [Group Y] :
    (Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) ⊓
      CFSG.generalizedFitting Y).Normal := by
  haveI : (CFSG.generalizedFitting Y).Normal :=
    CFSG.ComponentClassification.AS76b.generalizedFitting_normal
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨hzC, hzF⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.Normal.conj_mem inferInstance z hzF g⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hconj : g⁻¹ * f * g ∈ CFSG.generalizedFitting Y := by
    simpa using Subgroup.Normal.conj_mem inferInstance f hf g⁻¹
  have hcomm := Subgroup.mem_centralizer_iff.mp hzC (g⁻¹ * f * g) hconj
  calc f * (g * z * g⁻¹) = g * ((g⁻¹ * f * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * f * g)) * g⁻¹ := by rw [hcomm]
    _ = g * z * g⁻¹ * f := by group

private theorem comm_centralizer_inf_generalizedFitting {Y : Type} [Group Y] :
    ∀ z ∈ (Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) ⊓
      CFSG.generalizedFitting Y),
      ∀ w ∈ (Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) ⊓
        CFSG.generalizedFitting Y), z * w = w * z := by
  intro z hz w hw
  obtain ⟨hzC, -⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨-, hwF⟩ := Subgroup.mem_inf.mp hw
  exact (Subgroup.mem_centralizer_iff.mp hzC w hwF).symm

private theorem false_of_Y {Y : Type} [Group Y] [Finite Y] {Bs : Subgroup Y}
    (hBs3 : IsPGroup 3 Bs) (hBs1 : Bs ≠ ⊥) (hBO : Bs ⊓ CFSG.pCore 3 Y = ⊥)
    (hO2 : CFSG.pCore 2 Y = ⊥)
    (hO3 : ∀ x ∈ CFSG.pCore 3 Y, ∀ b ∈ Bs, b * x = x * b)
    (hOp : ∀ p : ℕ, p.Prime → 3 < p → ∀ x ∈ CFSG.pCore p Y, ∀ b ∈ Bs, b * x = x * b)
    (hcomp : ∀ J : Subgroup Y, CFSG.IsComponent J → ∀ b ∈ Bs, ∀ j ∈ J, b * j = j * b) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : ∀ q : ℕ, q.Prime → ∀ b ∈ Bs, ∀ x ∈ CFSG.pCore q Y, b * x = x * b := by
    intro q hq b hb x hx
    rcases Nat.lt_or_ge q 3 with h | h
    · have hq2 : q = 2 := by
        interval_cases q
        · exact absurd hq Nat.not_prime_zero
        · exact absurd hq Nat.not_prime_one
        · rfl
      subst hq2
      rw [hO2, Subgroup.mem_bot] at hx
      subst hx
      simp
    · rcases Nat.lt_or_ge 3 q with h' | h'
      · exact hOp q hq h' x hx b hb
      · have hq3 : q = 3 := by omega
        subst hq3
        exact hO3 x hx b hb
  have hFc : ∀ b ∈ Bs, CFSG.fittingSubgroup Y ≤ Subgroup.centralizer ({b} : Set Y) := by
    intro b hb
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hprime p.1.1 (Nat.mem_primeFactors.mp p.1.2).1 b hb x hx
  have hLc : ∀ b ∈ Bs, CFSG.layer Y ≤ Subgroup.centralizer ({b} : Set Y) := by
    intro b hb
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun K hK => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomp K hK b hb x hx
  have hFs : ∀ b ∈ Bs, CFSG.generalizedFitting Y ≤ Subgroup.centralizer ({b} : Set Y) := by
    intro b hb
    rw [CFSG.generalizedFitting.eq_sup]
    exact sup_le (hFc b hb) (hLc b hb)
  have hBC : ∀ b ∈ Bs, b ∈ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact ((Subgroup.mem_centralizer_iff.mp (hFs b hb hf)) b (Set.mem_singleton b)).symm
  have hBF : ∀ b ∈ Bs, b ∈ CFSG.generalizedFitting Y := fun b hb =>
    CFSG.centralizer_generalizedFitting_le Y (hBC b hb)
  have hBZ : ∀ b ∈ Bs, b ∈ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) ⊓
      CFSG.generalizedFitting Y :=
    fun b hb => Subgroup.mem_inf.mpr ⟨hBC b hb, hBF b hb⟩
  haveI hZN := normal_centralizer_inf_generalizedFitting (Y := Y)
  have hB3pc : Bs ≤ CFSG.pCore 3 Y :=
    le_pCore_of_normal_abelian (p := 3)
      (Z := Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) ⊓
        CFSG.generalizedFitting Y)
      comm_centralizer_inf_generalizedFitting (fun b hb => hBZ b hb) hBs3
  have h := le_inf (le_refl Bs) hB3pc
  rw [hBO] at h
  exact hBs1 (le_bot_iff.mp h)

private theorem exists_oTwoComponents_map_eq {X : Type} [Group X] [Finite X]
    {J : Subgroup (X ⧸ CFSG.pCore 2 X)} (hJ : CFSG.IsComponent J) :
    ∃ L : Subgroup X, L ∈ oTwoComponents X ∧
      L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) = J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J', hJ'⟩ : ∃ J' : Subgroup X, J' = J.comap (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
    ⟨_, rfl⟩
  have hJ'sn : J'.IsSubnormal := by
    rw [hJ']
    exact hJ.2.comap _
  have hPrN : (CFSG.perfectResidual ↥J').Normal := by
    obtain ⟨n, hn, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥J')
    rw [hn]
    infer_instance
  have hPrP : Group.IsPerfect (CFSG.perfectResidual ↥J') :=
    CFSG.Wreathed.PrimewisePerfectLift.perfectResidual_isPerfect
  obtain ⟨L, hL⟩ : ∃ L : Subgroup X, L = (CFSG.perfectResidual ↥J').map J'.subtype :=
    ⟨_, rfl⟩
  have hLJ' : L ≤ J' := by
    rw [hL]
    exact Subgroup.map_subtype_le _
  have hLsub : L.subgroupOf J' = CFSG.perfectResidual ↥J' := by
    rw [hL, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective J'.subtype_injective _
  have hLsn : L.IsSubnormal :=
    Subgroup.IsSubnormal.trans hLJ' (by rw [hLsub]; exact hPrN.isSubnormal) hJ'sn
  have hLperf : Group.IsPerfect L := by
    rw [hL]
    exact isPerfect_map_subtype hPrP
  have hmem' : ∀ x : X, x ∈ J' → QuotientGroup.mk' (CFSG.pCore 2 X) x ∈ J := by
    intro x hx
    rw [hJ'] at hx
    exact Subgroup.mem_comap.mp hx
  let φ : ↥J' →* ↥J :=
    ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp J'.subtype).codRestrict J
      (fun x => hmem' (x : X) x.2)
  have hφsurj : Function.Surjective φ := by
    intro j
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) (j : X ⧸ CFSG.pCore 2 X)
    have hxJ' : x ∈ J' := by
      rw [hJ']
      exact Subgroup.mem_comap.mpr (by rw [hx]; exact j.2)
    exact ⟨⟨x, hxJ'⟩, Subtype.ext hx⟩
  have hJperf : Group.IsPerfect ↥J := hJ.1.1
  have htop : Group.IsPerfect (⊤ : Subgroup ↥J) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv.symm : ↥J ≃* (⊤ : Subgroup ↥J)).toMonoidHom)
      (MulEquiv.surjective _)
  have hPJ : CFSG.perfectResidual ↥J = ⊤ :=
    top_unique (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual ⊤ htop)
  have hmapφ : (CFSG.perfectResidual ↥J').map φ = ⊤ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq φ hφsurj).trans hPJ
  have hLπ : L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) = J := by
    rw [hL, Subgroup.map_map]
    have hcomp : J.subtype.comp φ = (QuotientGroup.mk' (CFSG.pCore 2 X)).comp J'.subtype := rfl
    rw [← hcomp, ← Subgroup.map_map, hmapφ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hker : ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp L.subtype).ker = CFSG.pCore 2 L := by
    apply le_antisymm
    · have h2 : IsPGroup 2 ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp L.subtype).ker := by
        intro x
        have hx : ((x : L) : X) ∈ CFSG.pCore 2 X := by
          have h1 := MonoidHom.mem_ker.mp x.2
          exact (QuotientGroup.eq_one_iff ((x : L) : X)).mp h1
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨_, hx⟩
        exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
      exact le_sSup ⟨inferInstance, h2⟩
    · intro x hx
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff ((x : L) : X)).mpr
        (CFSG.RankThree.PartTwo.Late.pCoreOf_le_pCore_of_isSubnormal 2 hLsn
          (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have hrange : ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp L.subtype).range = J := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hLπ]
  let e : (L ⧸ CFSG.pCore 2 L) ≃* ↥J :=
    ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivRange _)).trans (MulEquiv.subgroupCongr hrange)
  have hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hJ.1
  refine ⟨L, ?_, hLπ⟩
  show Group.IsPerfect L ∧ L.IsSubnormal ∧ CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)
  exact ⟨hLperf, hLsn, hq⟩

theorem exists_component {A M : Subgroup G} (h : Sec18Std G A M) {B P : Subgroup G}
    (hP : IsSylowOf 3 P ⊤) (hBP : B ≤ P) (hPM : P ≤ M) (hB3 : IsPGroup 3 B) (hB1 : B ≠ ⊥)
    (hBn : P ≤ Subgroup.normalizer (B : Set G))
    (hBO : B ⊓ (Sec4.oTwoP 3 ↥M).map M.subtype = ⊥)
    (hBM : B ≤ M)
    (hcent : ∀ p : ℕ, p.Prime → 3 < p → ∀ b ∈ B, ∀ y ∈ (Sec4.oTwoP p ↥M).map M.subtype,
      b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    ∃ K ∈ oTwoComponentsIn M, ∃ b ∈ B, ∃ k ∈ K, b * k * b⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
  by_contra hne
  push Not at hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : Subgroup ↥M, Bp = B.subgroupOf M := ⟨_, rfl⟩
  obtain ⟨Pp, hPp⟩ : ∃ Pp : Subgroup ↥M, Pp = P.subgroupOf M := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      Bs = Bp.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      P' = Pp.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := ⟨_, rfl⟩
  have hBpB : ∀ b ∈ Bp, (b : G) ∈ B := fun b hb => by
    rw [hBp] at hb
    exact Subgroup.mem_subgroupOf.mp hb
  have hmemBp : ∀ b : G, ∀ hb : b ∈ B, (⟨b, hBM hb⟩ : ↥M) ∈ Bp := fun b hb => by
    rw [hBp]
    exact Subgroup.mem_subgroupOf.mpr hb
  have hmemBs : ∀ b : G, ∀ hb : b ∈ B,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨b, hBM hb⟩ : ↥M) ∈ Bs := fun b hb => by
    rw [hBs]
    exact Subgroup.mem_map_of_mem _ (hmemBp b hb)
  have hBpPG : IsPGroup 3 Bp := by
    rw [hBp]
    exact hB3.comap_of_injective M.subtype M.subtype_injective
  have hBs3 : IsPGroup 3 Bs := by
    rw [hBs]
    exact IsPGroup.map hBpPG _
  have hBs1 : Bs ≠ ⊥ := by
    intro hbot
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    have hbM : b ∈ M := hBM hb
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨b, hbM⟩ : ↥M) ∈ Bs := hmemBs b hb
    rw [hbot, Subgroup.mem_bot] at h2
    have h3 : (⟨b, hbM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff (⟨b, hbM⟩ : ↥M)).mp h2
    have h4 : (⟨b, hbM⟩ : ↥M) ∈ Sec4.oTwoP 3 ↥M := Sec4.pCore_two_le_oTwoP 3 ↥M h3
    have h5 : b ∈ B ⊓ (Sec4.oTwoP 3 ↥M).map M.subtype :=
      ⟨hb, Subgroup.mem_map_of_mem M.subtype h4⟩
    rw [hBO, Subgroup.mem_bot] at h5
    exact Subgroup.mem_bot.mpr h5
  have hBO' : Bs ⊓ CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hx3⟩
    rw [hBs] at hxB
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hxB
    have hbT : b' ∈ Sec4.oTwoP 3 ↥M := hx3
    have h5 : (b' : G) ∈ B ⊓ (Sec4.oTwoP 3 ↥M).map M.subtype :=
      ⟨hBpB b' hb', Subgroup.mem_map_of_mem M.subtype hbT⟩
    rw [hBO, Subgroup.mem_bot] at h5
    have h6 : b' = 1 := Subtype.ext (by simpa using h5)
    rw [Subgroup.mem_bot, h6, map_one]
  have hO2 : CFSG.pCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hP3G : IsPGroup 3 P := hP.isPGroup
  have hPpP : IsPGroup 3 Pp := by
    rw [hPp]
    exact hP3G.comap_of_injective M.subtype M.subtype_injective
  have hP3' : IsPGroup 3 P' := by
    rw [hP']
    exact IsPGroup.map hPpP _
  have hPK : ¬ 3 ∣ P.relIndex ⊤ := by
    have := (CFSG.ABGLocalTools.isSylowOf_iff (p := 3) (P := P) (K := ⊤)).mp hP
    exact this.2.2
  have hdiv : P.relIndex M ∣ P.relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_dvd_index_of_le hPM
  have hPM3 : ¬ 3 ∣ P.relIndex M := fun h => hPK (h.trans hdiv)
  have hPpidx : Pp.index = P.relIndex M := by
    rw [hPp]
    rfl
  have hPidx : ¬ 3 ∣ P'.index := by
    rw [hP']
    intro h
    apply hPM3
    rw [← hPpidx]
    exact h.trans (Subgroup.index_map_dvd Pp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M)))
  have hnorm : ∀ x ∈ P', ∀ b ∈ Bs, x * b * x⁻¹ ∈ Bs := by
    intro x hx b hb
    rw [hP'] at hx
    rw [hBs] at hb ⊢
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [hPp] at hp'
    have hpP : (p' : G) ∈ P := Subgroup.mem_subgroupOf.mp hp'
    have hbB : (b' : G) ∈ B := hBpB b' hb'
    have hconj : (p' : G) * (b' : G) * (p' : G)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hBn hpP) (b' : G)).mp hbB
    have hconj' : p' * b' * p'⁻¹ ∈ Bp := by
      rw [hBp, Subgroup.mem_subgroupOf]
      simpa using hconj
    have key : QuotientGroup.mk' (CFSG.pCore 2 ↥M) p' * QuotientGroup.mk' (CFSG.pCore 2 ↥M) b' *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) p')⁻¹ =
          QuotientGroup.mk' (CFSG.pCore 2 ↥M) (p' * b' * p'⁻¹) := by
      simp
    rw [key]
    exact Subgroup.mem_map_of_mem _ hconj'
  have hO3 := centralizes_pCore_three hP3' hPidx hnorm hBO'
  have hOp : ∀ p : ℕ, p.Prime → 3 < p → ∀ x ∈ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M),
      ∀ b ∈ Bs, b * x = x * b := by
    intro p hp h3 x hx b hb
    rw [hBs] at hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) x
    have ht : t ∈ Sec4.oTwoP p ↥M := hx
    have hc := hcent p hp h3 (b' : G) (hBpB b' hb') (t : G) (Subgroup.mem_map_of_mem M.subtype ht)
    exact mk_commute_of_mem_pCore (mem_pCore_two_of_mem_pCoreOf (b := b') (l := t) hc)
  have hcomp : ∀ J : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), CFSG.IsComponent J →
      ∀ b ∈ Bs, ∀ j ∈ J, b * j = j * b := by
    intro J hJ b hb j hj
    obtain ⟨L, hL, hLJ⟩ := exists_oTwoComponents_map_eq hJ
    rw [hBs] at hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← hLJ] at hj
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hj
    have hK : L.map M.subtype ∈ oTwoComponentsIn M := ⟨L, hL, rfl⟩
    have hkey := hne (L.map M.subtype) hK (b' : G) (hBpB b' hb') (l : G)
      (Subgroup.mem_map_of_mem M.subtype hl)
    exact mk_commute_of_mem_pCore (mem_pCore_two_of_mem_pCoreOf (b := b') (l := l) hkey)
  exact false_of_Y hBs3 hBs1 hBO' hO2 hO3 hOp hcomp

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
