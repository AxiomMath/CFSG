module

public import CFSG.OddTranspositions.PartThree.LocalBenderBasic
public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.GroupTheory.OddCoreQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.Timmesfeld.Bridge.OddTranspDefs
public import Certificates.Certificate113

import CFSG.Timmesfeld.Bridge.Asc72Central
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.CGT.Timmesfeld75.SimpleAssembly
import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.OddTranspositions.O4PairTenWidth
public import CFSG.OddTranspositions.Width
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem setup_localGroup_of_transitive (hS : Setup G D) {z d₀ : G} (hd₀ : d₀ ∈ centSet D z)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y) :
    Setup (localGroup D z) (localSet D z) := by
  have hd₀H : d₀ ∈ localGroup D z := mem_localGroup_of_mem hd₀
  refine ⟨⟨⟨d₀, hd₀H⟩, ?_⟩, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      obtain ⟨k, hk, hkg⟩ :=
        htrans d₀ hd₀ (g : G) (show (g : G) ∈ centSet D z from hg)
      exact isConj_iff.mpr ⟨⟨k, hk⟩, Subtype.ext hkg⟩
    · intro hg
      obtain ⟨k, hk⟩ := isConj_iff.mp hg
      have hkg : (k : G) * d₀ * (k : G)⁻¹ = (g : G) := congrArg Subtype.val hk
      refine ⟨?_, ?_⟩
      · rw [← hkg]
        exact hS.normal (k : G) d₀ hd₀.1
      · rw [← hkg]
        exact ((commute_of_mem_localGroup k.2).mul_left hd₀.2).mul_left
          (commute_of_mem_localGroup k.2).inv_left
  · exact (hS.oddT.preimage (localGroup D z)).mono (fun x hx => hx.1)
  · exact Subgroup.closure_closure_coe_preimage

theorem centralizer_eq_of_mul_mul {H : Type} [Group H] [Finite H] {E : Set H}
    (hSH : Setup H E) {O : Subgroup H} [O.Normal] (hOodd : Odd (Nat.card O))
    {u v z b : H} (hu : u ∈ E) (hv : v ∈ E) (hb : b ∈ E) (huv : u ≠ v) (hc : Commute u v)
    (hz : z ∈ Subgroup.center H) (hz2 : z * z = 1) (hbz : b = u * v * z) :
    O ⊓ Subgroup.centralizer ({b} : Set H) = O ⊓ Subgroup.centralizer ({u} : Set H) ∧
      O ⊓ Subgroup.centralizer ({b} : Set H) = O ⊓ Subgroup.centralizer ({v} : Set H) := by
  classical
  have hbuz : b * z = u * v := by rw [hbz, mul_assoc, hz2, mul_one]
  have hcomm : ∀ n ∈ O ⊓ Subgroup.centralizer ({b} : Set H), Commute n u ∧ Commute n v := by
    rintro n ⟨hnO, hnc⟩
    have hnb : Commute n b := Subgroup.mem_centralizer_singleton_iff.mp hnc
    have hnz : Commute n z := Subgroup.mem_center_iff.mp hz n
    have hnbuv : Commute n (u * v) := by
      have h1 : Commute n (b * z) := hnb.mul_right hnz
      rwa [hbuz] at h1
    have hnbvu : Commute n (v * u) := by rwa [hc.eq] at hnbuv
    exact ⟨commute_of_mem_odd_normal hSH.oddT hSH.normal hOodd hu hv huv hc hnO hnbuv,
      commute_of_mem_odd_normal hSH.oddT hSH.normal hOodd hv hu huv.symm hc.symm hnO hnbvu⟩
  have hle_u : O ⊓ Subgroup.centralizer ({b} : Set H) ≤
      O ⊓ Subgroup.centralizer ({u} : Set H) :=
    fun n hn => ⟨hn.1, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm n hn).1⟩
  have hle_v : O ⊓ Subgroup.centralizer ({b} : Set H) ≤
      O ⊓ Subgroup.centralizer ({v} : Set H) :=
    fun n hn => ⟨hn.1, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm n hn).2⟩
  have hcard_u := CFSG.GroupTheory.card_inf_centralizer_eq_of_isConj (O := O) (hSH.isConj hb hu)
  have hcard_v := CFSG.GroupTheory.card_inf_centralizer_eq_of_isConj (O := O) (hSH.isConj hb hv)
  exact ⟨Subgroup.eq_of_le_of_card_ge hle_u (le_of_eq hcard_u.symm),
    Subgroup.eq_of_le_of_card_ge hle_v (le_of_eq hcard_v.symm)⟩

theorem le_centralizer_of_mul_mul {H : Type} [Group H] [Finite H] {E : Set H}
    (hSH : Setup H E) {O : Subgroup H} [O.Normal] (hOodd : Odd (Nat.card O))
    {u v z b : H} (hu : u ∈ E) (hv : v ∈ E) (hb : b ∈ E) (huv : u ≠ v) (hc : Commute u v)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hz : z ∈ Subgroup.center H) (hz2 : z * z = 1) (hbz : b = u * v * z) :
    O ≤ O ⊓ Subgroup.centralizer ({u} : Set H) := by
  obtain ⟨hbu, hbv⟩ := centralizer_eq_of_mul_mul hSH hOodd hu hv hb huv hc hz hz2 hbz
  have hbuz : b * z = u * v := by rw [hbz, mul_assoc, hz2, mul_one]
  have hCuv : O ⊓ Subgroup.centralizer ({u * v} : Set H) =
      O ⊓ Subgroup.centralizer ({b} : Set H) := by
    have hcent : Subgroup.centralizer ({u * v} : Set H) =
        Subgroup.centralizer ({b} : Set H) := by
      ext n
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hn
        have hnz : Commute n z := Subgroup.mem_center_iff.mp hz n
        have hn' : Commute n (u * v) := hn
        have h1 : Commute n ((u * v) * z) := hn'.mul_right hnz
        rwa [← hbz] at h1
      · intro hn
        have hnz : Commute n z := Subgroup.mem_center_iff.mp hz n
        have hn' : Commute n b := hn
        have h1 : Commute n (b * z) := hn'.mul_right hnz
        rwa [hbuz] at h1
    rw [hcent]
  have hsup := odd_normal_le_sup_centralizer (G := H) (N := O) hOodd hu2 hv2 hu1 hv1 huv hc
  simpa only [← hbu, ← hbv, hCuv, sup_idem] using hsup

theorem oddCore_le_center_localGroup (hS : Setup G D) {z u v : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y) :
    CFSG.oddCore (localGroup D z) ≤ Subgroup.center (localGroup D z) := by
  classical
  set H := localGroup D z with hH
  have hSH : Setup H (localSet D z) := setup_localGroup_of_transitive hS hu htrans
  let u' : H := ⟨u, mem_localGroup_of_mem hu⟩
  let v' : H := ⟨v, mem_localGroup_of_mem hv⟩
  let b' : H := ⟨u * v * z, mem_localGroup_of_mem (mul_mul_mem_centSet hu hv huvz)⟩
  let z' : H := ⟨z, self_mem_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz⟩
  have hu' : u' ∈ localSet D z := hu
  have hv' : v' ∈ localSet D z := hv
  have hb' : b' ∈ localSet D z := mul_mul_mem_centSet hu hv huvz
  have hz'c : z' ∈ Subgroup.center H :=
    self_mem_center_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  have hz'2 : z' * z' = 1 :=
    Subtype.ext (mul_self_eq_one_of_mul_mul_mem hS.oddT hu hv hc huvz)
  have hu'2 : u' * u' = 1 := hSH.oddT.mul_self_eq_one hu'
  have hv'2 : v' * v' = 1 := hSH.oddT.mul_self_eq_one hv'
  have hu'1 : u' ≠ 1 := hSH.oddT.ne_one hu'
  have hv'1 : v' ≠ 1 := hSH.oddT.ne_one hv'
  have huv' : u' ≠ v' := fun h => huv (congrArg Subtype.val h)
  have hu'v' : Commute u' v' := Subtype.ext hc.eq
  have hb'z' : b' = u' * v' * z' := Subtype.ext rfl
  set O := CFSG.oddCore H with hO
  have hOodd : Odd (Nat.card O) := CFSG.ABGLocalTools.odd_card_oddCore
  have hOleCu : O ≤ O ⊓ Subgroup.centralizer ({u'} : Set H) :=
    le_centralizer_of_mul_mul hSH hOodd hu' hv' hb' huv' hu'v' hu'2 hv'2 hu'1 hv'1 hz'c hz'2 hb'z'
  have huO : ∀ n ∈ O, Commute n u' := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mp (hOleCu hn).2
  have hD_comm : ∀ d ∈ localSet D z, ∀ n ∈ O, Commute n d := by
    intro d hd n hn
    obtain ⟨c, hc_eq⟩ := isConj_iff.mp (hSH.isConj hu' hd)
    have hncO : c⁻¹ * n * c ∈ O := by
      simpa using (inferInstance : O.Normal).conj_mem n hn c⁻¹
    have hnc : Commute (c⁻¹ * n * c) u' := huO _ hncO
    have hconj := (Commute.conj_iff c).mpr hnc
    rw [show c * (c⁻¹ * n * c) * c⁻¹ = n by group, hc_eq] at hconj
    exact hconj
  exact CFSG.GroupTheory.le_center_of_centralizes_set hSH.gen hD_comm

theorem solvableRadical_le_center_localGroup (hS : Setup G D) {z u v : G}
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v) (hc : Commute u v)
    (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z)) :
    CFSG.solvableRadical (localGroup D z) ≤ Subgroup.center (localGroup D z) :=
  otg2_solvableRadical_le_center hQ
    (oddCore_le_center_localGroup hS hu hv huv hc huvz htrans)

theorem setup_oddCore_quotient (hS : Setup G D) {z u : G} (hu : u ∈ centSet D z)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y) :
    Setup (localGroup D z ⧸ CFSG.oddCore (localGroup D z))
      (QuotientGroup.mk' (CFSG.oddCore (localGroup D z)) '' localSet D z) := by
  classical
  set H := localGroup D z with hH
  set O := CFSG.oddCore H with hO
  have hSH : Setup H (localSet D z) := setup_localGroup_of_transitive hS hu htrans
  have hOodd : Odd (Nat.card O) := CFSG.ABGLocalTools.odd_card_oddCore
  have hπ1 : ∀ d ∈ localSet D z, QuotientGroup.mk' O d ≠ 1 := by
    intro d hd h1
    have hdO : (d : H) ∈ O := (QuotientGroup.eq_one_iff d).mp h1
    have hdne : d ≠ 1 := hSH.oddT.ne_one hd
    have hd2 : d * d = 1 := hSH.oddT.mul_self_eq_one hd
    have hord2 : orderOf d = 2 :=
      @orderOf_eq_prime H _ d 2 ⟨Nat.prime_two⟩ (by rwa [pow_two]) hdne
    exact CFSG.Timmesfeld.Connectivity.not_mem_of_odd_card hOodd hord2 hdO
  exact hSH.map (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O) hπ1

theorem oddCore_quotient_inf_commutator_eq_bot
    (hS : Setup G D) {z u v : G} (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ((CFSG.solvableRadical (localGroup D z)).map
        (QuotientGroup.mk' (CFSG.oddCore (localGroup D z)))) ⊓
      commutator (localGroup D z ⧸ CFSG.oddCore (localGroup D z)) = ⊥ := by
  classical
  set H := localGroup D z with hH
  set O := CFSG.oddCore H with hO
  have hSH : Setup H (localSet D z) := setup_localGroup_of_transitive hS hu htrans
  have hOZ : O ≤ Subgroup.center H := oddCore_le_center_localGroup hS hu hv huv hc huvz htrans
  have hSZ : CFSG.solvableRadical H ≤ Subgroup.center H :=
    solvableRadical_le_center_localGroup hS hu hv huv hc huvz htrans hQ
  have hOleOs : O ≤ CFSG.solvableRadical H := hOZ.trans otg2_center_le_solvableRadical
  let π : H →* H ⧸ O := QuotientGroup.mk' O
  let E : Subgroup (H ⧸ O) := (CFSG.solvableRadical H).map π
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hEc : E ≤ Subgroup.center (H ⧸ O) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨t, rfl⟩ := hπs g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp (hSZ hs) t
  have hEn : E.Normal := Subgroup.normal_of_le_center hEc
  have hE2 : IsPGroup 2 E := by
    simpa only [E, π, hO] using
      CFSG.GroupTheory.isPGroup_two_map_mk_oddCore_of_le_center hSZ
  have hB' : CFSG.BenderSuzuki.IsBenderGroup ((H ⧸ O) ⧸ E) :=
    CFSG.CGT.Timmesfeld75.isBenderGroup_of_mulEquiv
      (QuotientGroup.quotientQuotientEquivQuotient O (CFSG.solvableRadical H) hOleOs) hB
  have hS' : Setup (H ⧸ O) (π '' localSet D z) := setup_oddCore_quotient hS hu htrans
  exact @inf_commutator_eq_bot_of_isBenderGroup (H ⧸ O) _ (π '' localSet D z) _ hS'
    E hEc hE2 hEn hB'

theorem image_center_not_mem_commutator (hS : Setup G D)
    {z u v : G} (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ∀ x : localGroup D z, x ∈ Subgroup.center (localGroup D z) → x * x = 1 → x ≠ 1 →
      QuotientGroup.mk' (CFSG.oddCore (localGroup D z)) x ∉
        commutator (localGroup D z ⧸ CFSG.oddCore (localGroup D z)) := by
  classical
  set H := localGroup D z with hH
  set O := CFSG.oddCore H with hO
  have hinf := oddCore_quotient_inf_commutator_eq_bot hS hu hv huv hc huvz htrans hQ hB
  intro x hxc hx2 hx1
  have hxOs : x ∈ CFSG.solvableRadical H := otg2_center_le_solvableRadical hxc
  have hxE : QuotientGroup.mk' O x ∈ (CFSG.solvableRadical H).map (QuotientGroup.mk' O) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hxOs
  have hxO : x ∉ O := by
    intro hxO
    have hord2 : orderOf x = 2 :=
      @orderOf_eq_prime H _ x 2 ⟨Nat.prime_two⟩ (by rwa [pow_two]) hx1
    exact CFSG.Timmesfeld.Connectivity.not_mem_of_odd_card
      (CFSG.ABGLocalTools.odd_card_oddCore (H := H)) hord2 hxO
  have hπx1 : QuotientGroup.mk' O x ≠ 1 := fun h1 => hxO ((QuotientGroup.eq_one_iff x).mp h1)
  intro hxK'
  have hmem : QuotientGroup.mk' O x ∈
      (CFSG.solvableRadical H).map (QuotientGroup.mk' O) ⊓ commutator (H ⧸ O) :=
    ⟨hxE, hxK'⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  exact hπx1 hmem

theorem not_mem_commutator_localGroup (hS : Setup G D)
    {z u v : G} (hz1 : z ≠ 1) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ∀ x : localGroup D z, (x : G) ∈ centSet D z → x ∉ commutator (localGroup D z) := by
  classical
  set H := localGroup D z with hH
  set O := CFSG.oddCore H with hO
  intro x hx hxmem
  have hSH : Setup H (localSet D z) := setup_localGroup_of_transitive hS hu htrans
  have hzH : z ∈ H := self_mem_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  let z' : H := ⟨z, hzH⟩
  have hz'c : z' ∈ Subgroup.center H :=
    self_mem_center_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  have hz'2 : z' * z' = 1 :=
    Subtype.ext (mul_self_eq_one_of_mul_mul_mem hS.oddT hu hv hc huvz)
  have hz'ne : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hπz : QuotientGroup.mk' O z' ∉ commutator (H ⧸ O) :=
    image_center_not_mem_commutator hS hu hv huv hc huvz htrans hQ hB z' hz'c hz'2 hz'ne
  have hmap : (commutator H).map (QuotientGroup.mk' O) = commutator (H ⧸ O) := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)]
  have hsub : localSet D z ⊆ (commutator H : Subgroup H) := by
    intro y hy
    obtain ⟨c, hc_eq⟩ := isConj_iff.mp (hSH.isConj hy (show x ∈ localSet D z from hx))
    have hy_eq : y = c⁻¹ * x * c := by rw [← hc_eq]; group
    rw [hy_eq]
    simpa using (inferInstance : (commutator H).Normal).conj_mem x hxmem c⁻¹
  have htop : commutator H = ⊤ := by
    rw [eq_top_iff, ← hSH.gen]
    exact (Subgroup.closure_le (commutator H)).mpr hsub
  have hzmem : z' ∈ commutator H := by
    rw [htop]
    exact Subgroup.mem_top z'
  have hπz' : QuotientGroup.mk' O z' ∈ commutator (H ⧸ O) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hzmem
  exact hπz hπz'

theorem eq_one_or_eq_of_mem_center_localGroup (hS : Setup G D)
    {z u v : G} (hz1 : z ≠ 1) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (huv : u ≠ v)
    (hc : Commute u v) (huvz : u * v * z ∈ D)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z,
      ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ∀ c ∈ Subgroup.center (localGroup D z), c * c = 1 → (c : G) = 1 ∨ (c : G) = z := by
  classical
  set H := localGroup D z with hH
  set O := CFSG.oddCore H with hO
  intro c hcc hc2
  have hSH : Setup H (localSet D z) := setup_localGroup_of_transitive hS hu htrans
  have hinf := oddCore_quotient_inf_commutator_eq_bot hS hu hv huv hc huvz htrans hQ hB
  have hzH : z ∈ H := self_mem_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  let z' : H := ⟨z, hzH⟩
  have hz'c : z' ∈ Subgroup.center H :=
    self_mem_center_localGroup_of_mul_mul_mem hS.oddT hu hv hc huvz
  have hz'2 : z' * z' = 1 :=
    Subtype.ext (mul_self_eq_one_of_mul_mul_mem hS.oddT hu hv hc huvz)
  have hz'ne : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  by_cases hc1 : c = 1
  · exact Or.inl (by rw [hc1]; rfl)
  · right
    have hπz : QuotientGroup.mk' O z' ∉ commutator (H ⧸ O) :=
      image_center_not_mem_commutator hS hu hv huv hc huvz htrans hQ hB z' hz'c hz'2 hz'ne
    have hπc : QuotientGroup.mk' O c ∉ commutator (H ⧸ O) :=
      image_center_not_mem_commutator hS hu hv huv hc huvz htrans hQ hB c hcc hc2 hc1
    have hK'ne : commutator (H ⧸ O) ≠ ⊤ := fun htop => hπc (htop ▸ Subgroup.mem_top _)
    have hlt : 1 < (commutator (H ⧸ O)).index := Subgroup.one_lt_index_of_ne_top hK'ne
    have hS' : Setup (H ⧸ O) (QuotientGroup.mk' O '' localSet D z) :=
      setup_oddCore_quotient hS hu htrans
    have hidx2 : (commutator (H ⧸ O)).index = 2 := by
      have hle := hS'.index_commutator_le_two
      omega
    have hczO : c * z' ∈ O :=
      CFSG.GroupTheory.mul_mem_oddCore_of_mem_center hz'c hz'2 hcc hπc hπz hinf hidx2
    exact congrArg (fun x : H => (x : G))
      (CFSG.GroupTheory.eq_of_mul_mem_oddCore_of_mem_center
        (Subgroup.mem_center_iff.mp hcc z') hc2 hz'2 hczO)

end CFSG.OddTranspositions.PartThree
