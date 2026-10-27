module

public import CFSG.OddTranspositions.PartThree.EightEight.StarConj
public import CFSG.OddTranspositions.PartThree.OddTranspClosure
public import CFSG.GroupTheory.PCore.SolvableRadical

import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.LocalBenderCenter
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OpenA7M22Lemma
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.Timmesfeld.Bridge.OddLocalRootCore
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

theorem commute_conj_and_mul_mem_pCore_of_not_commute {X : Type} [Group X] {E : Set X}
    (hS : Setup X E) {q a : X} (hq : q ∈ CFSG.pCore 2 X) (ha : a ∈ E)
    (hqa : ¬ Commute q a) :
    Commute a (q * a * q⁻¹) ∧ q * a * q⁻¹ ∈ E ∧ q * a * q⁻¹ ≠ a ∧
      a * (q * a * q⁻¹) ∈ CFSG.pCore 2 X := by
  have hbE : q * a * q⁻¹ ∈ E := hS.conj_mem q ha
  have hbne : q * a * q⁻¹ ≠ a := by
    intro hba
    exact hqa (mul_inv_eq_iff_eq_mul.mp hba)
  have habO : a * (q * a * q⁻¹) ∈ CFSG.pCore 2 X := by
    have h1 : a * q * a⁻¹ ∈ CFSG.pCore 2 X := by
      have h := (CFSG.pCore_normal (p := 2) (G := X)).conj_mem' q hq a⁻¹
      simpa [inv_inv] using h
    have h2 : q⁻¹ ∈ CFSG.pCore 2 X := (CFSG.pCore 2 X).inv_mem hq
    have h3 := (CFSG.pCore 2 X).mul_mem h1 h2
    have hab_eq : (a * q * a⁻¹) * q⁻¹ = a * (q * a * q⁻¹) := by
      rw [hS.oddT.inv_eq ha]
      group
    rwa [hab_eq] at h3
  refine ⟨?_, hbE, hbne, habO⟩
  rcases hS.oddT.commute_or_odd ha hbE with h | hodd
  · exact h
  · exfalso
    have h1 : a * (q * a * q⁻¹) = 1 :=
      CFSG.RankThree.PartTwo.Sec15.eq_one_of_mem_of_odd_orderOf'
        (CFSG.pCore_isPGroup (p := 2) (G := X)) habO hodd
    exact hbne (hS.oddT.eq_of_mul_eq_one ha h1).symm

theorem exists_not_commute_and_subset_pCore {X : Type} [Group X] {E : Set X}
    (hS : Setup X E) {z : X} (hz : z ∈ Subgroup.center X) (hz2 : z * z = 1)
    (hmul : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → Commute a b → a * b * z ∈ E)
    {q : X} (hq : q ∈ CFSG.pCore 2 X) (hqcent : q ∉ Subgroup.center X) :
    ∃ a ∈ E, ¬ Commute q a ∧ E ⊆ CFSG.pCore 2 X := by
  classical
  have hqnc : ∃ a ∈ E, ¬ Commute q a := by
    by_contra h
    push Not at h
    exact hqcent (CFSG.Timmesfeld.Bridge.OddLocal.mem_center_of_commute_gen hS.gen h)
  obtain ⟨a, ha, hqa⟩ := hqnc
  obtain ⟨hcomm, hbE, hbne, habO⟩ :=
    commute_conj_and_mul_mem_pCore_of_not_commute hS hq ha hqa
  have habzE : a * (q * a * q⁻¹) * z ∈ E :=
    hmul a ha (q * a * q⁻¹) hbE (fun h => hbne h.symm) hcomm
  have hzO : z ∈ CFSG.pCore 2 X := by
    have : (Subgroup.zpowers z).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
    exact CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.mem_pCore hz2
  have habzO : a * (q * a * q⁻¹) * z ∈ CFSG.pCore 2 X :=
    (CFSG.pCore 2 X).mul_mem habO hzO
  refine ⟨a, ha, hqa, ?_⟩
  intro e he
  obtain ⟨c, hc⟩ := isConj_iff.mp (hS.isConj habzE he)
  rw [← hc]
  simpa using
    (CFSG.pCore_normal (p := 2) (G := X)).conj_mem' (a * (q * a * q⁻¹) * z) habzO c⁻¹

theorem pCore_two_le_center_of_mul_mul_mem {X : Type} [Group X] [Finite X] {E : Set X}
    (hS : Setup X E) {z : X} (hz : z ∈ Subgroup.center X) (hz2 : z * z = 1)
    (hmul : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → Commute a b → a * b * z ∈ E) :
    CFSG.pCore 2 X ≤ Subgroup.center X := by
  classical
  intro q hqO
  by_contra hqcent
  obtain ⟨a, ha, hqa, hEsub⟩ :=
    exists_not_commute_and_subset_pCore hS hz hz2 hmul hqO hqcent
  have haO : a ∈ CFSG.pCore 2 X := hEsub ha
  have hex : ∃ d ∈ E, ¬ Commute a d := by
    by_contra h
    push Not at h
    exact hqa ((Subgroup.mem_center_iff.mp
      (CFSG.Timmesfeld.Bridge.OddLocal.mem_center_of_commute_gen hS.gen h)) q)
  obtain ⟨d, hdE, had⟩ := hex
  have hadO : a * d ∈ CFSG.pCore 2 X :=
    (CFSG.pCore 2 X).mul_mem haO (hEsub hdE)
  have hodd : Odd (orderOf (a * d)) := hS.oddT.odd_of_not_commute ha hdE had
  have had1 : a * d = 1 :=
    CFSG.RankThree.PartTwo.Sec15.eq_one_of_mem_of_odd_orderOf'
      (CFSG.pCore_isPGroup (p := 2) (G := X)) hadO hodd
  have hda : a = d := hS.oddT.eq_of_mul_eq_one ha had1
  exact had (by rw [hda])

theorem oddCore_le_center_of_mul_mul_mem {X : Type} [Group X] [Finite X] {E : Set X}
    (hS : Setup X E) {z : X} (hz : z ∈ Subgroup.center X) (hz2 : z * z = 1)
    (hmul : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → Commute a b → a * b * z ∈ E)
    (hpair : ∃ u ∈ E, ∃ v ∈ E, u ≠ v ∧ Commute u v) :
    CFSG.oddCore X ≤ Subgroup.center X := by
  obtain ⟨u, hu, v, hv, huv, hc⟩ := hpair
  have huvzE : u * v * z ∈ E := hmul u hu v hv huv hc
  have hOodd : Odd (Nat.card (CFSG.oddCore X)) := CFSG.ABGLocalTools.odd_card_oddCore
  have hOle : CFSG.oddCore X ≤
      CFSG.oddCore X ⊓ Subgroup.centralizer ({u} : Set X) :=
    le_centralizer_of_mul_mul hS hOodd hu hv huvzE huv hc
      (hS.oddT.mul_self_eq_one hu) (hS.oddT.mul_self_eq_one hv)
      (hS.oddT.ne_one hu) (hS.oddT.ne_one hv) hz hz2 rfl
  refine CFSG.GroupTheory.le_center_of_centralizes_set hS.gen ?_
  intro d hd n hn
  obtain ⟨c, hc_eq⟩ := isConj_iff.mp (hS.isConj hu hd)
  have hncO : c⁻¹ * n * c ∈ CFSG.oddCore X := by
    simpa using (CFSG.oddCore_normal X).conj_mem' n hn c
  have hnc : Commute (c⁻¹ * n * c) u :=
    Subgroup.mem_centralizer_singleton_iff.mp (hOle hncO).2
  have hconj := (Commute.conj_iff c).mpr hnc
  rwa [show c * (c⁻¹ * n * c) * c⁻¹ = n by group, hc_eq] at hconj

theorem solvableRadical_eq_center_of_mul_mul_mem {X : Type} [Group X] [Finite X] {E : Set X}
    (hS : Setup X E) {z : X} (hz : z ∈ Subgroup.center X) (hz2 : z * z = 1)
    (hmul : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → Commute a b → a * b * z ∈ E)
    (hpair : ∃ u ∈ E, ∃ v ∈ E, u ≠ v ∧ Commute u v) :
    CFSG.solvableRadical X = Subgroup.center X := by
  refine le_antisymm (otg2_solvableRadical_le_center
    (pCore_two_le_center_of_mul_mul_mem hS hz hz2 hmul)
    (oddCore_le_center_of_mul_mul_mem hS hz hz2 hmul hpair)) otg2_center_le_solvableRadical

namespace EightEight

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_not_commute_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a : G}
    (ha : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    ∃ c ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x, ¬ Commute a c := by
  classical
  let z : G := (x * y * w) ^ n
  let K : Subgroup G := localGroup D z
  let Δ₁ : Set G := conjOrbit K x
  let K₁ : Subgroup G := Subgroup.closure Δ₁
  obtain ⟨a', ha', hne', -, -⟩ :=
    exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord
      (by simpa [z, K, Δ₁] using ha)
  have horb : conjOrbit K₁ x = Δ₁ := by
    simpa [K₁, Δ₁, K, z] using conjOrbit_closure_conjOrbit_eq hC.setup ht hn hord
  have haO : a ∈ conjOrbit K₁ x := by
    rw [horb]
    simpa [z, K, Δ₁] using ha
  have ha'K : a' ∈ conjOrbit K₁ a := by
    have h := conjOrbit_eq_of_mem (M := K₁) (u := x) (v := a) haO
    rw [h]
    rw [horb]
    simpa [z, K, Δ₁] using ha'
  obtain ⟨k, hk, hk'⟩ := ha'K
  by_contra h
  push Not at h
  have hacl : ∀ g ∈ K₁, Commute a g := by
    intro g hg
    exact commute_of_mem_closure (S := {a}) (T := Δ₁)
      (fun u hu v hv => by
        rw [Set.mem_singleton_iff.mp hu]
        exact h v (by simpa [z, K, Δ₁] using hv))
      (Subgroup.subset_closure (Set.mem_singleton a)) hg
  have hak : Commute a k := hacl k hk
  have ha'eq : a' = a := by
    rw [hk']
    rw [← hak.eq]
    group
  exact hne' ha'eq

theorem solvableRadical_closure_conjOrbit_eq_center (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    CFSG.solvableRadical (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)) =
      Subgroup.center (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)) := by
  classical
  let z : G := (x * y * w) ^ n
  let K : Subgroup G := localGroup D z
  let Δ₁ : Set G := conjOrbit K x
  let K₁ : Subgroup G := Subgroup.closure Δ₁
  have hthird := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hzz : z * z = 1 := by simpa [z] using hthird.1
  have hzx : Commute z x := by simpa [z] using hthird.2.2.1
  have hxc : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hΔD : Δ₁ ⊆ D := fun a ha => (conjOrbit_subset_centSet hC.setup.normal hxc ha).1
  have hpowdata := pow_mem_closure_conjOrbit hC.setup ht hn hord
  have hzK₁ : z ∈ K₁ := by simpa [K₁, Δ₁, K, z] using hpowdata.1
  have hcent : ∀ g ∈ K₁, Commute g z := by
    intro g hg
    exact hpowdata.2 g (by simpa [K₁, Δ₁, K, z] using hg)
  have hzcenter : (⟨z, hzK₁⟩ : K₁) ∈ Subgroup.center K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent (g : G) g.2).eq
  have hz2K : (⟨z, hzK₁⟩ : K₁) * ⟨z, hzK₁⟩ = 1 :=
    Subtype.ext (by simpa using hzz)
  have horb : conjOrbit K₁ x = Δ₁ := by
    simpa [K₁, Δ₁, K, z] using conjOrbit_closure_conjOrbit_eq hC.setup ht hn hord
  have hcls : ∃ t : K₁, inClosure Δ₁ = {g | IsConj t g} := by
    simpa [K₁] using
      isClass_inClosure_of_conjOrbit_closure_eq (Ω := Δ₁) (x := x)
        (by simpa [Δ₁, K] using self_mem_conjOrbit K x) (by simpa [K₁] using horb)
  have hsetup : Setup K₁ (inClosure Δ₁) :=
    setup_inClosure hC.setup.oddT hΔD hcls
  have hmul : ∀ a ∈ inClosure Δ₁, ∀ b ∈ inClosure Δ₁, a ≠ b → Commute a b →
      a * b * ⟨z, hzK₁⟩ ∈ inClosure Δ₁ := by
    intro a ha b hb hab hcomm
    have hcomm' : Commute (a : G) (b : G) := hcomm.map (Subgroup.subtype K₁)
    have hdata := mul_mul_pow_mem_conjOrbit_and_commute h86 h87 hC hrad hO4 hF hne ht hn hord
      (by simpa [inClosure, Δ₁, K, z] using ha)
      (by simpa [inClosure, Δ₁, K, z] using hb)
      (fun h => hab (Subtype.ext h).symm) hcomm'
    simpa [inClosure, Δ₁, K, z] using hdata.1
  have hpair : ∃ u ∈ inClosure Δ₁, ∃ v ∈ inClosure Δ₁, u ≠ v ∧ Commute u v := by
    have hxO : x ∈ conjOrbit K x := self_mem_conjOrbit K x
    obtain ⟨a', ha', hne', hcomm', -⟩ :=
      exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord
        (by simpa [z, K] using hxO)
    refine ⟨⟨x, Subgroup.subset_closure hxO⟩, by simpa [inClosure, Δ₁] using hxO,
      ⟨a', Subgroup.subset_closure (by simpa [Δ₁, K, z] using ha')⟩,
      by simpa [inClosure, Δ₁, K, z] using ha', ?_, ?_⟩
    · intro h
      exact hne' (congrArg Subtype.val h).symm
    · exact Subtype.ext hcomm'.eq
  have hres := solvableRadical_eq_center_of_mul_mul_mem (X := K₁) hsetup hzcenter hz2K hmul hpair
  simpa [K₁, Δ₁, K, z] using hres

theorem injOn_mk_center_closure_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    Set.InjOn (QuotientGroup.mk' (Subgroup.center
        (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x))))
      (inClosure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)) := by
  classical
  let z : G := (x * y * w) ^ n
  let K : Subgroup G := localGroup D z
  let Δ₁ : Set G := conjOrbit K x
  let K₁ : Subgroup G := Subgroup.closure Δ₁
  have hzx : Commute z x := by
    simpa [z] using
      (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1
  have hxc : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hΔD : Δ₁ ⊆ D := fun a ha => (conjOrbit_subset_centSet hC.setup.normal hxc ha).1
  have hE : IsOddTransp (inClosure Δ₁) := isOddTransp_inClosure hC.setup.oddT hΔD
  have hnc : ∀ a ∈ inClosure Δ₁, ∃ b ∈ inClosure Δ₁, ¬ Commute a b := by
    intro a ha
    obtain ⟨c, hc, hca⟩ :=
      exists_not_commute_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
        (by simpa [inClosure, Δ₁, K, z] using ha)
    refine ⟨⟨c, Subgroup.subset_closure (by simpa [Δ₁, K, z] using hc)⟩,
      by simpa [inClosure, Δ₁, K, z] using hc, ?_⟩
    intro h
    exact hca (h.map (Subgroup.subtype K₁))
  have hres := injOn_mk_of_le_center hE (N := Subgroup.center K₁) le_rfl hnc
  simpa [K₁, Δ₁, K, z] using hres

omit [Finite G] in
theorem commute_mk_center_closure_conjOrbit_iff (hC : HypothesisC D)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n)
    {a b : Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)}
    (ha : a ∈ inClosure (conjOrbit (localGroup D ((x * y * w) ^ n)) x))
    (hb : b ∈ inClosure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)) :
    Commute (QuotientGroup.mk' (Subgroup.center
        (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x))) a)
      (QuotientGroup.mk' (Subgroup.center
        (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x))) b) ↔
      Commute a b := by
  classical
  let z : G := (x * y * w) ^ n
  let K : Subgroup G := localGroup D z
  let Δ₁ : Set G := conjOrbit K x
  let K₁ : Subgroup G := Subgroup.closure Δ₁
  have hzx : Commute z x := by
    simpa [z] using
      (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1
  have hxc : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hΔD : Δ₁ ⊆ D := fun a ha => (conjOrbit_subset_centSet hC.setup.normal hxc ha).1
  have hE : IsOddTransp (inClosure Δ₁) := isOddTransp_inClosure hC.setup.oddT hΔD
  change Commute (QuotientGroup.mk' (Subgroup.center K₁) a)
    (QuotientGroup.mk' (Subgroup.center K₁) b) ↔ Commute a b
  constructor
  · intro h
    exact commute_of_commute_mk_of_le_center' hE le_rfl ha hb h
  · intro h
    exact h.map (QuotientGroup.mk' (Subgroup.center K₁))

end EightEight

end CFSG.OddTranspositions.PartThree

end
