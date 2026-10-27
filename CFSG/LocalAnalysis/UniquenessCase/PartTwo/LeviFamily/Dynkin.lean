module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenLevi
import CFSG.GroupTheory.PCore.PCoreOfNormalEq
import CFSG.GroupTheory.PElementCommutator
import CFSG.GroupTheory.Commutator.JoinNormalizer
import CFSG.GroupTheory.CentralExtensionPGroup
import CFSG.GroupTheory.OddOrderClosure
import CFSG.Quasithin.MS93.ASKer
import CFSG.ClassicalInvolution.Asc77.AscT3CIIX
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen2
import TauCeti.GroupTheory.Elementary
import CFSG.GroupTheory.PElementSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

namespace IsLeviFamily

variable {P : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}

omit [Finite Q] in
private theorem normal_subgroupOf_of_sup_eq_of_commutator_le {A B L' O : Subgroup Q}
    (hAB : A ⊔ B = L') (hO : O ≤ A) (hc : ⁅A, B⁆ ≤ O) :
    (A.subgroupOf L').Normal := by
  have hAle : A ≤ L' := by rw [← hAB]; exact le_sup_left
  have hBA : ⁅B, A⁆ ≤ A := by
    rw [Subgroup.commutator_comm]
    exact hc.trans hO
  have hBnorm : B ≤ Subgroup.normalizer (A : Set Q) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr hBA
  have hLnorm : L' ≤ Subgroup.normalizer (A : Set Q) := by
    rw [← hAB]
    exact sup_le Subgroup.le_normalizer hBnorm
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAle).mpr hLnorm

omit [Finite Q] in
private theorem mem_pCoreOf_of_pow_two_mem (hL : IsLeviFamily P d L) (i : Fin d) {t : Q}
    {k : ℕ} (ht : t ∈ L i) (htk : t ^ 2 ^ k = 1)
    (hc : ∀ g ∈ L i, ⁅t, g⁆ ∈ pCoreOf 2 P) : t ∈ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup Q := pCoreOf 2 P with hOdef
  set H : Subgroup Q := L i with hHdef
  set E : Subgroup ↥H := CFSG.pCore 2 ↥H with hEdef
  let π : ↥H →* Bar2 H := QuotientGroup.mk' E
  have hOsub : O.subgroupOf H = E := by
    rw [hOdef, hEdef]
    have hpH : pCoreOf 2 P = pCoreOf 2 H := by
      rw [hHdef]
      exact (CFSG.GroupTheory.pCoreOf_eq_of_le_of_normal 2 (hL.le i) (hL.normal i)
        (hL.pCoreOf_le i)).symm
    rw [hpH]
    exact CFSG.openPCoreOf_subgroupOf 2 H
  let tH : ↥H := ⟨t, hHdef.symm ▸ ht⟩
  have htkH : tH ^ 2 ^ k = 1 := Subtype.ext (by simpa [tH] using htk)
  have hmemE : ∀ g : ↥H, ⁅tH, g⁆ ∈ E := by
    intro g
    have hmemO : H.subtype ⁅tH, g⁆ ∈ O := by
      rw [map_commutatorElement]
      exact hc (g : Q) g.2
    exact hOsub ▸ Subgroup.mem_subgroupOf.mpr hmemO
  have hcent : π tH ∈ Subgroup.center (Bar2 H) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E y
    have hcomm : ⁅π tH, π g⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hmemE g)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  have hpow : (π tH) ^ 2 ^ k = 1 := by
    rw [← map_pow, htkH, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers (π tH)) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hzp : Subgroup.zpowers (π tH) ≤ CFSG.pCore 2 (Bar2 H) :=
    CFSG.LieType.BorelTits.le_pCore (r := 2)
      (Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcent)) hz2
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hzp
  have ht1 : π tH = 1 := by
    have := hzp (Subgroup.mem_zpowers (π tH))
    simpa using this
  have htE : tH ∈ E := (QuotientGroup.eq_one_iff _).mp ht1
  have htOsub : tH ∈ O.subgroupOf H := by rwa [hOsub]
  simpa [tH] using (Subgroup.mem_subgroupOf.mp htOsub)

omit [Finite Q] in
private theorem opp_le_pCoreOf_of_commutator_le (hL : IsLeviFamily P d L) (i : Fin d)
    {A : Subgroup Q} (hAle : A ≤ L i) (hc : ⁅A, L i⁆ ≤ pCoreOf 2 P) :
    Opp 2 A ≤ pCoreOf 2 P := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxA, k, hk⟩
  refine mem_pCoreOf_of_pow_two_mem (k := k) hL i (hAle hxA) ?_ ?_
  · rw [← hk]
    exact pow_orderOf_eq_one x
  · intro g hg
    exact Subgroup.commutator_le.mp hc x hxA g hg

private theorem subgroupOf_opp_eq_pElementSubgroup_top {G : Type} [Group G] [Finite G]
    {H : Subgroup G} :
    (Opp 2 H).subgroupOf H =
      CFSG.RankThree.PartOne.pElementSubgroup 2 (⊤ : Subgroup ↥H) := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (close16_opp_le 2 H),
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map Nat.prime_two H.subtype ⊤,
    Subgroup.map_top, Subgroup.range_subtype]
  rfl

omit [Finite Q] in
theorem pCoreOf_eq (hL : IsLeviFamily P d L) (i : Fin d) : pCoreOf 2 (L i) = pCoreOf 2 P :=
  CFSG.GroupTheory.pCoreOf_eq_of_le_of_normal 2 (hL.le i) (hL.normal i) (hL.pCoreOf_le i)

theorem opp_eq (hL : IsLeviFamily P d L) (i : Fin d) : Opp 2 (L i) = L i := by
  refine le_antisymm (close16_opp_le 2 (L i)) ?_
  have hO : pCoreOf 2 P ≤ Opp 2 (L i) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) (hL.pCoreOf_le i)
  calc L i = Opp 2 (L i) ⊔ pCoreOf 2 P := hL.eq_opp_sup i
    _ ≤ Opp 2 (L i) ⊔ Opp 2 (L i) := sup_le_sup le_rfl hO
    _ = Opp 2 (L i) := sup_idem _

theorem le_opp (hL : IsLeviFamily P d L) (i : Fin d) : L i ≤ Opp 2 P := by
  rw [← opp_eq hL i]
  exact s13_Thirteen2_pElementSubgroup_mono (hL.le i)

theorem not_oUpperTwo_le (hL : IsLeviFamily P d L) (i : Fin d) :
    ¬ S17.oUpperTwo (L i) ≤ pCoreOf 2 P := by
  intro hle
  have h2 : IsPGroup 2 (L i) := by
    refine CFSG.Quasithin.MS93.isPGroup_of_odd_eq_one ?_
    intro k hk hkodd
    have hkO : k ∈ pCoreOf 2 P := hle (by
      rw [S17.oUpperTwo_eq_closure]
      exact Subgroup.subset_closure ⟨hk, hkodd⟩)
    have hx : (⟨k, hkO⟩ : ↥(pCoreOf 2 P)) ^ orderOf k = 1 := by
      refine Subtype.ext ?_
      simp
    have h1 := CFSG.GroupTheory.SuzukiTwoGroup.eq_one_of_pow_eq_one_of_odd
      (S := ↥(pCoreOf 2 P)) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) hkodd hx
    simpa using congrArg Subtype.val h1
  have hLO : L i ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hL.le i)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le i)).mp (hL.normal i)) h2
  exact hL.ne i (le_antisymm hLO (hL.pCoreOf_le i))

private theorem isNilpotent_bar2_of_upperTwo_central {H O : Subgroup Q} (hO : O = pCoreOf 2 H)
    (hJL : ⁅S17.oUpperTwo H, H⁆ ≤ O) : Group.IsNilpotent (Bar2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J : Subgroup Q := S17.oUpperTwo H with hJdef
  set E : Subgroup ↥H := CFSG.pCore 2 ↥H with hEdef
  let π : ↥H →* Bar2 H := QuotientGroup.mk' E
  have hOsub : O.subgroupOf H = E := by
    rw [hO, hEdef]
    exact CFSG.openPCoreOf_subgroupOf 2 H
  have hJnormal : (J.subgroupOf H).Normal := by
    rw [hJdef, S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
    exact CFSG.GroupTheory.normal_oddOrderClosure_subgroupOf H
  let Jb : Subgroup (Bar2 H) := (J.subgroupOf H).map π
  have hJb_normal : Jb.Normal := hJnormal.map π (QuotientGroup.mk'_surjective E)
  have hJb_center : Jb ≤ Subgroup.center (Bar2 H) := by
    refine Subgroup.commutator_top_right_eq_bot_iff_le_center.mp ?_
    have hker : ⁅J.subgroupOf H, (⊤ : Subgroup ↥H)⁆ ≤ π.ker := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [MonoidHom.mem_ker]
      have hxJ : ((x : ↥H) : Q) ∈ J := Subgroup.mem_subgroupOf.mp hx
      have hmemO : H.subtype ⁅x, y⁆ ∈ O := by
        rw [map_commutatorElement]
        exact Subgroup.commutator_le.mp hJL ((x : ↥H) : Q) hxJ ((y : ↥H) : Q) y.2
      have hmemE : ⁅x, y⁆ ∈ E := hOsub ▸ Subgroup.mem_subgroupOf.mpr hmemO
      change (QuotientGroup.mk' E) ⁅x, y⁆ = 1
      exact (QuotientGroup.eq_one_iff _).mpr hmemE
    change ⁅(J.subgroupOf H).map π, (⊤ : Subgroup (Bar2 H))⁆ = ⊥
    rw [← Subgroup.map_top_of_surjective (f := π) (QuotientGroup.mk'_surjective E),
      ← Subgroup.map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr hker
  have hquot2 : IsPGroup 2 (Bar2 H ⧸ Jb) := by
    have : Jb.Normal := hJb_normal
    refine TauCeti.isPGroup_quotient_of_forall_exists_pow_mem ?_
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E x
    obtain ⟨k, hk⟩ := CFSG.GroupTheory.pow_two_pow_mem_oddOrderClosure H g.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    refine Subgroup.mem_map.mpr ⟨g ^ 2 ^ k, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hJdef, S17.oUpperTwo_eq_closure, ← CFSG.GroupTheory.oddOrderClosure_eq_closure]
    simpa using hk
  have : Jb.Normal := hJb_normal
  have : Group.IsNilpotent (Bar2 H ⧸ Jb) := hquot2.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' Jb) (by
    rw [QuotientGroup.ker_mk']
    exact hJb_center)

private theorem isPGroup_bar2_of_opp_sup {H O : Subgroup Q} (hO : O = pCoreOf 2 H)
    (hHopp : H = Opp 2 H ⊔ O) (hNil : Group.IsNilpotent (Bar2 H)) :
    IsPGroup 2 (Bar2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup ↥H := CFSG.pCore 2 ↥H with hEdef
  let π : ↥H →* Bar2 H := QuotientGroup.mk' E
  have hOsub : O.subgroupOf H = E := by
    rw [hO, hEdef]
    exact CFSG.openPCoreOf_subgroupOf 2 H
  have hOH : O ≤ H := by rw [hO]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hOppSub : (Opp 2 H).subgroupOf H =
      CFSG.RankThree.PartOne.pElementSubgroup 2 (⊤ : Subgroup ↥H) :=
    subgroupOf_opp_eq_pElementSubgroup_top (H := H)
  have hgen : Subgroup.closure {x : Bar2 H | ∃ k : ℕ, orderOf x = 2 ^ k} = ⊤ := by
    have hsup : (Opp 2 H).subgroupOf H ⊔ E = ⊤ := by
      calc
        (Opp 2 H).subgroupOf H ⊔ E
            = (Opp 2 H).subgroupOf H ⊔ O.subgroupOf H := by rw [hOsub]
        _ = (Opp 2 H ⊔ O).subgroupOf H :=
          (Subgroup.subgroupOf_sup (close16_opp_le 2 H) hOH).symm
        _ = H.subgroupOf H := by rw [← hHopp]
        _ = ⊤ := Subgroup.subgroupOf_self H
    have hTop : ((Opp 2 H).subgroupOf H).map π = ⊤ := by
      have hmap := congrArg (Subgroup.map π) hsup
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
        Subgroup.map_top_of_surjective (f := π) (QuotientGroup.mk'_surjective E)] at hmap
      simpa using hmap
    have hTop' : CFSG.RankThree.PartOne.pElementSubgroup 2 (⊤ : Subgroup (Bar2 H)) = ⊤ := by
      have h := hTop
      rw [hOppSub,
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pElementSubgroup_map Nat.prime_two π ⊤,
        Subgroup.map_top_of_surjective (f := π) (QuotientGroup.mk'_surjective E)] at h
      exact h
    simpa [CFSG.RankThree.PartOne.pElementSubgroup] using hTop'
  have : Group.IsNilpotent (Bar2 H) := hNil
  have hcl := CFSG.GroupTheory.isPGroup_closure_of_isNilpotent (Y := Bar2 H) (p := 2)
    (S := {x : Bar2 H | ∃ k : ℕ, orderOf x = 2 ^ k})
    fun s hs => ⟨hs.choose, hs.choose_spec ▸ pow_orderOf_eq_one s⟩
  rw [hgen] at hcl
  exact hcl.of_equiv Subgroup.topEquiv

omit [Finite Q] in
private theorem le_pCoreOf_of_isPGroup_bar2 {H : Subgroup Q} (hLb2 : IsPGroup 2 (Bar2 H)) :
    H ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup ↥H := CFSG.pCore 2 ↥H with hEdef
  let π : ↥H →* Bar2 H := QuotientGroup.mk' E
  have htop : CFSG.pCore 2 (Bar2 H) = ⊤ :=
    top_le_iff.mp (CFSG.LieType.BorelTits.le_pCore 2
      (inferInstance : (⊤ : Subgroup (Bar2 H)).Normal)
      (hLb2.of_equiv Subgroup.topEquiv.symm))
  have hbot : CFSG.pCore 2 (Bar2 H) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have : Subsingleton (Bar2 H) := by
    refine ⟨fun x y => ?_⟩
    have hx : x = 1 := by
      have hxmem : x ∈ CFSG.pCore 2 (Bar2 H) := by rw [htop]; exact Subgroup.mem_top x
      rwa [hbot] at hxmem
    have hy : y = 1 := by
      have hymem : y ∈ CFSG.pCore 2 (Bar2 H) := by rw [htop]; exact Subgroup.mem_top y
      rwa [hbot] at hymem
    rw [hx, hy]
  intro x hx
  have hx1 : π ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
  have hxE : (⟨x, hx⟩ : ↥H) ∈ E := by
    have h : (⟨x, hx⟩ : ↥H) ∈ π.ker := MonoidHom.mem_ker.mpr hx1
    rwa [show π.ker = E from QuotientGroup.ker_mk' E] at h
  exact Subgroup.mem_map_of_mem H.subtype hxE

private theorem le_pCoreOf_of_upperTwo_central {H O : Subgroup Q} (hO : O = pCoreOf 2 H)
    (hJL : ⁅S17.oUpperTwo H, H⁆ ≤ O) (hHopp : H = Opp 2 H ⊔ O) :
    H ≤ pCoreOf 2 H :=
  le_pCoreOf_of_isPGroup_bar2 (isPGroup_bar2_of_opp_sup hO hHopp
    (isNilpotent_bar2_of_upperTwo_central hO hJL))

private theorem le_pCoreOf_of_tits (hL : IsLeviFamily P d L) (i : Fin d) {A B : Subgroup Q}
    (hA : pCoreOf 2 P ≤ A) (hB : pCoreOf 2 P ≤ B)
    (hAB : A ⊔ B = L i) (hc : ⁅A, B⁆ ≤ pCoreOf 2 P)
    (hAc : ¬ ⁅A, L i⁆ ≤ pCoreOf 2 P) (hBc : ¬ ⁅B, L i⁆ ≤ pCoreOf 2 P) :
    L i ≤ pCoreOf 2 P := by
  set O : Subgroup Q := pCoreOf 2 P with hOdef
  set H : Subgroup Q := L i with hHdef
  have hAle : A ≤ H := by rw [← hAB]; exact le_sup_left
  have hBle : B ≤ H := by rw [← hAB]; exact le_sup_right
  have hAnormal : (A.subgroupOf H).Normal :=
    normal_subgroupOf_of_sup_eq_of_commutator_le hAB hA hc
  have hBnormal : (B.subgroupOf H).Normal := by
    refine normal_subgroupOf_of_sup_eq_of_commutator_le (A := B) (B := A) ?_ hB ?_
    · rw [sup_comm, hAB]
    · rw [Subgroup.commutator_comm]
      exact hc
  have hJA : S17.oUpperTwo H ≤ A := hL.tits i A hA hAle hAnormal hAc
  have hJB : S17.oUpperTwo H ≤ B := hL.tits i B hB hBle hBnormal hBc
  have hJL : ⁅S17.oUpperTwo H, H⁆ ≤ O := by
    have hnormA : A ≤ Subgroup.normalizer (O : Set Q) :=
      (hAle.trans (hHdef.symm ▸ hL.le i)).trans
        (by rw [hOdef]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    have hnormB : B ≤ Subgroup.normalizer (O : Set Q) :=
      (hBle.trans (hHdef.symm ▸ hL.le i)).trans
        (by rw [hOdef]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    have hJA' : ⁅S17.oUpperTwo H, A⁆ ≤ O := by
      have hBA : ⁅B, A⁆ ≤ O := by rw [Subgroup.commutator_comm]; exact hc
      exact (Subgroup.commutator_mono hJB le_rfl).trans hBA
    have hJB' : ⁅S17.oUpperTwo H, B⁆ ≤ O :=
      (Subgroup.commutator_mono hJA le_rfl).trans hc
    have h := CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      (Y := S17.oUpperTwo H) (A := A) (B := B) (N := O) hnormA hnormB hJA' hJB'
    simpa [hHdef, hAB] using h
  have hOeq : O = pCoreOf 2 H := by
    rw [hOdef, hHdef]
    exact (pCoreOf_eq hL i).symm
  have hHopp : H = Opp 2 H ⊔ O := by
    rw [hHdef, hOdef]
    exact hL.eq_opp_sup i
  have hHO : H ≤ O := by
    have h := le_pCoreOf_of_upperTwo_central hOeq hJL hHopp
    rwa [← hOeq] at h
  simpa [hHdef, hOdef] using hHO

theorem indecomposable (hL : IsLeviFamily P d L) (i : Fin d) (A B : Subgroup Q)
    (hA : pCoreOf 2 P ≤ A) (hB : pCoreOf 2 P ≤ B) (hA2 : A = Opp 2 A ⊔ pCoreOf 2 P)
    (hB2 : B = Opp 2 B ⊔ pCoreOf 2 P) (hAB : A ⊔ B = L i) (hc : ⁅A, B⁆ ≤ pCoreOf 2 P) :
    A = L i ∨ B = L i := by
  have hAle : A ≤ L i := by rw [← hAB]; exact le_sup_left
  have hBle : B ≤ L i := by rw [← hAB]; exact le_sup_right
  by_cases hAc : ⁅A, L i⁆ ≤ pCoreOf 2 P
  · have hOppA : Opp 2 A ≤ pCoreOf 2 P :=
      opp_le_pCoreOf_of_commutator_le hL i hAle hAc
    have hAO : A = pCoreOf 2 P := by
      refine le_antisymm ?_ hA
      calc A = Opp 2 A ⊔ pCoreOf 2 P := hA2
        _ ≤ pCoreOf 2 P ⊔ pCoreOf 2 P := sup_le_sup hOppA le_rfl
        _ = pCoreOf 2 P := sup_idem _
    right
    rw [← hAB, hAO]
    exact (sup_eq_right.mpr hB).symm
  · by_cases hBc : ⁅B, L i⁆ ≤ pCoreOf 2 P
    · have hOppB : Opp 2 B ≤ pCoreOf 2 P :=
        opp_le_pCoreOf_of_commutator_le hL i hBle hBc
      have hBO : B = pCoreOf 2 P := by
        refine le_antisymm ?_ hB
        calc B = Opp 2 B ⊔ pCoreOf 2 P := hB2
          _ ≤ pCoreOf 2 P ⊔ pCoreOf 2 P := sup_le_sup hOppB le_rfl
          _ = pCoreOf 2 P := sup_idem _
      left
      rw [← hAB, hBO]
      exact (sup_eq_left.mpr hA).symm
    · exact absurd (le_antisymm (le_pCoreOf_of_tits hL i hA hB hAB hc hAc hBc)
        (hL.pCoreOf_le i)) (hL.ne i)

private theorem exists_not_commutator_le_of_not_commutator_le (hL : IsLeviFamily P d L)
    {K0 X C O N : Subgroup Q} (hK0 : K0 = Opp 2 P) (hC : C = ⁅K0, X⁆)
    (hN : N = C ⊔ O) (hO : O = pCoreOf 2 P)
    (hX : X ≤ Subgroup.normalizer (K0 : Set Q))
    (hcore : pCoreOf 2 K0 = O) (hO_K0 : O ≤ K0)
    (h : ¬ ⁅K0, X⁆ ≤ pCoreOf 2 K0) :
    ∃ i, ¬ ⁅N, L i⁆ ≤ O := by
  by_contra hnone
  push Not at hnone
  have hK0_eq : (⨆ i, L i) = K0 := by
    rw [hL.iSup_eq, ← hK0, ← hO]
    exact sup_eq_left.mpr hO_K0
  have hNK0 : ⁅N, K0⁆ ≤ O := by
    rw [← hK0_eq]
    exact CFSG.GroupTheory.commutator_iSup_right_le_of_le_normalizer
      (fun j => (hL.le j).trans (by rw [hO]; exact
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)) hnone
  have hCN : C ≤ N := by rw [hN]; exact le_sup_left
  have hCC : ⁅C, K0⁆ ≤ O := (Subgroup.commutator_mono hCN le_rfl).trans hNK0
  have hcomm : ⁅K0, X⁆ ≤ pCoreOf 2 K0 := by
    refine CFSG.GroupTheory.commutator_le_pCoreOf_of_commutator_commutator_le
      (K := K0) (X := X) ?_ hX ?_
    · rw [hK0]; exact close16_opp_idem 2 P
    · rw [hcore]
      rw [hC] at hCC
      exact hCC
  exact h hcomm

private theorem not_commutator_commutator_le_of_not_commutator_le (hL : IsLeviFamily P d L)
    {N O : Subgroup Q} (i : Fin d) (hO : O = pCoreOf 2 P)
    (hN_norm_L : N ≤ Subgroup.normalizer (L i : Set Q))
    (hi : ¬ ⁅N, L i⁆ ≤ O) :
    ¬ ⁅⁅L i, N⁆, L i⁆ ≤ O := by
  intro hle
  apply hi
  have hLiN : ⁅L i, N⁆ ≤ pCoreOf 2 (L i) := by
    refine CFSG.GroupTheory.commutator_le_pCoreOf_of_commutator_commutator_le
      (K := L i) (X := N) (opp_eq hL i) hN_norm_L ?_
    rw [pCoreOf_eq hL i, ← hO]
    exact hle
  rw [pCoreOf_eq hL i, ← hO] at hLiN
  rwa [Subgroup.commutator_comm]

omit [Finite Q] in
private theorem oUpperTwo_le_sup_of_not_commutator_commutator_le (hL : IsLeviFamily P d L)
    {N O : Subgroup Q} (i : Fin d) (hO : O = pCoreOf 2 P)
    (hN_norm_L : N ≤ Subgroup.normalizer (L i : Set Q))
    (hi2 : ¬ ⁅⁅L i, N⁆, L i⁆ ≤ O) :
    S17.oUpperTwo (L i) ≤ ⁅L i, N⁆ ⊔ O := by
  set N' : Subgroup Q := ⁅L i, N⁆ ⊔ O with hN'def
  have hO_le : O ≤ L i := by rw [hO]; exact hL.pCoreOf_le i
  have hN'_le : N' ≤ L i := by
    rw [hN'def]
    refine sup_le ?_ hO_le
    have h : ⁅N, L i⁆ ≤ L i :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp hN_norm_L
    rw [Subgroup.commutator_comm]
    exact h
  have hN'_normal : (N'.subgroupOf (L i)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN'_le]
    intro x hx
    rw [hN'def]
    exact Subgroup.inf_normalizer_le_normalizer_sup (⁅L i, N⁆) O
      ⟨(Subgroup.normalizer_commutator_ge_left (L i) N) hx,
        (hL.le i).trans (by rw [hO]; exact
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P) hx⟩
  have hN'_not : ¬ ⁅N', L i⁆ ≤ O := by
    intro hle
    apply hi2
    have hLiN' : ⁅L i, N'⁆ ≤ O := by
      rw [Subgroup.commutator_comm]
      exact hle
    have h1 : ⁅L i, ⁅L i, N⁆⁆ ≤ O :=
      (Subgroup.commutator_mono (le_refl (L i)) (by rw [hN'def]; exact le_sup_left)).trans
        hLiN'
    rwa [Subgroup.commutator_comm]
  exact hL.tits i N' (by rw [← hO]; exact le_sup_right) hN'_le hN'_normal
    (hO ▸ hN'_not)

private theorem oUpperTwo_le_commutator_of_le_sup {d : ℕ} {L : Fin d → Subgroup Q}
    {C O : Subgroup Q} (i : Fin d) (hO2 : IsPGroup 2 O)
    (hO_norm_C : O ≤ Subgroup.normalizer (C : Set Q))
    {N' : Subgroup Q} (hJ : S17.oUpperTwo (L i) ≤ N') (hN' : N' ≤ C ⊔ O) :
    S17.oUpperTwo (L i) ≤ C := by
  rw [S17.oUpperTwo_eq_closure]
  refine (Subgroup.closure_le C).mpr ?_
  rintro u ⟨huL, huodd⟩
  have huJ : u ∈ S17.oUpperTwo (L i) := by
    rw [S17.oUpperTwo_eq_closure]
    exact Subgroup.subset_closure ⟨huL, huodd⟩
  exact CFSG.ClassicalInvolution.Asc77.T3CII.mem_of_odd_orderOf_of_mem_sup
    (N := C) (P := O) hO2 hO_norm_C (hN' (hJ huJ)) huodd

theorem exists_oUpperTwo_le_commutator (hL : IsLeviFamily P d L) {X : Subgroup Q}
    (hX : X ≤ normalizer (Opp 2 P : Set Q)) (h : ¬ ⁅Opp 2 P, X⁆ ≤ pCoreOf 2 (Opp 2 P)) :
    ∃ i, S17.oUpperTwo (L i) ≤ ⁅Opp 2 P, X⁆ := by
  set K0 : Subgroup Q := Opp 2 P with hK0def
  set O : Subgroup Q := pCoreOf 2 P with hOdef
  set C : Subgroup Q := ⁅K0, X⁆ with hCdef
  set N : Subgroup Q := C ⊔ O with hNdef
  have hO2 : IsPGroup 2 O := hOdef.symm ▸ (by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
  have hO_K0 : O ≤ K0 := by
    rw [hOdef, hK0def]
    exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hcore : pCoreOf 2 K0 = O := by
    rw [hOdef]
    refine CFSG.GroupTheory.pCoreOf_eq_of_le_of_normal 2 ?_ ?_ ?_
    · rw [hK0def]; exact close16_opp_le 2 P
    · rw [hK0def]; exact close16_opp_normal 2 P
    · exact hO_K0
  have hX' : X ≤ Subgroup.normalizer (K0 : Set Q) := by rwa [hK0def]
  have hN_le_K0 : N ≤ K0 := by
    rw [hNdef]
    refine sup_le ?_ hO_K0
    rw [hCdef, Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hX'
  have hN_le_P : N ≤ P :=
    hN_le_K0.trans (by rw [hK0def]; exact close16_opp_le 2 P)
  have hN_norm_L : ∀ i, N ≤ Subgroup.normalizer (L i : Set Q) := fun i =>
    hN_le_P.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le i)).mp (hL.normal i))
  have hK0_norm_C : K0 ≤ Subgroup.normalizer (C : Set Q) := by
    rw [hCdef]
    exact Subgroup.normalizer_commutator_ge_left K0 X
  have hK0_norm_O : K0 ≤ Subgroup.normalizer (O : Set Q) := by
    rw [hOdef]
    exact (hK0def.symm ▸ close16_opp_le 2 P).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have hK0_norm_N : K0 ≤ Subgroup.normalizer (N : Set Q) := by
    rw [hNdef]
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_sup C O
      ⟨hK0_norm_C hx, hK0_norm_O hx⟩
  obtain ⟨i, hi⟩ := exists_not_commutator_le_of_not_commutator_le hL hK0def hCdef hNdef
    hOdef hX' hcore hO_K0 (by simpa [hCdef] using h)
  have hi2 := not_commutator_commutator_le_of_not_commutator_le hL i hOdef (hN_norm_L i) hi
  have hJ := oUpperTwo_le_sup_of_not_commutator_commutator_le hL i hOdef (hN_norm_L i) hi2
  have hN'_le : ⁅L i, N⁆ ⊔ O ≤ C ⊔ O := by
    refine sup_le ?_ le_sup_right
    have h : ⁅K0, N⁆ ≤ N :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp hK0_norm_N
    have hLiN : ⁅L i, N⁆ ≤ N :=
      (Subgroup.commutator_mono (le_opp hL i) le_rfl).trans h
    rwa [hNdef] at hLiN
  refine ⟨i, ?_⟩
  simpa [hCdef, hK0def] using
    oUpperTwo_le_commutator_of_le_sup i hO2 (hO_K0.trans hK0_norm_C) hJ hN'_le

end IsLeviFamily

theorem isDynkinFamilyIn_of_isLeviFamily {M Dsub : Subgroup Q} {d : ℕ} {L : Fin d → Subgroup Q}
    (hL : IsLeviFamily (Dsub ⊓ M) d L) :
    S19.IsDynkinFamilyIn M Dsub d L (fun i => S17.oUpperTwo (L i)) := by
  unfold S19.IsDynkinFamilyIn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hL.pCoreOf_le i, hL.le i, hL.normal i, hL.eq_opp_sup i,
      IsLeviFamily.not_oUpperTwo_le hL i⟩
  · exact hL.commutator_le
  · exact hL.iSup_eq
  · exact fun i A B hA hB hA2 hB2 hAB hc =>
      IsLeviFamily.indecomposable hL i A B hA hB hA2 hB2 hAB hc
  · intro i
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
