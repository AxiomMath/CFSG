module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
import CFSG.Quasithin.Background.B5Sec
import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w1369_sq_mem_of_sup_zpowers {G : Type*} [Group G] {N : Subgroup G} {s : G}
    (hs : s ^ 2 = 1) (hN : s ∈ Subgroup.normalizer (N : Set G)) {g : G}
    (hg : g ∈ N ⊔ Subgroup.zpowers s) : g ^ 2 ∈ N := by
  have hconj : ∀ z ∈ Subgroup.zpowers s, ∀ n ∈ N, z * n * z⁻¹ ∈ N :=
    Subgroup.le_normalizer_iff.mp (Subgroup.zpowers_le.mpr hN)
  have hpow2 : ∀ z ∈ Subgroup.zpowers s, z ^ 2 = 1 := by
    intro z hz
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact dvd_trans (orderOf_dvd_of_mem_zpowers hz) (orderOf_dvd_iff_pow_eq_one.mpr hs)
  have key : ∀ x ∈ Subgroup.closure ((N : Set G) ∪ (Subgroup.zpowers s : Set G)),
      ∃ n ∈ N, ∃ m : ℤ, x = n * s ^ m := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_union] at hy
        rcases hy with hyN | hyz
        · exact ⟨y, hyN, 0, by simp⟩
        · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyz
          exact ⟨1, N.one_mem, m, by rw [← hm]; simp⟩
    | one => exact ⟨1, N.one_mem, 0, by simp⟩
    | mul y z _ _ ihy ihz =>
        obtain ⟨n1, hn1, m1, rfl⟩ := ihy
        obtain ⟨n2, hn2, m2, rfl⟩ := ihz
        refine ⟨n1 * (s ^ m1 * n2 * (s ^ m1)⁻¹),
          N.mul_mem hn1 (hconj (s ^ m1) (Subgroup.mem_zpowers_iff.mpr ⟨m1, rfl⟩) n2 hn2),
          m1 + m2, ?_⟩
        rw [zpow_add]
        group
    | inv y _ ih =>
        obtain ⟨n, hn, m, rfl⟩ := ih
        refine ⟨(s ^ m)⁻¹ * n⁻¹ * s ^ m, ?_, -m, ?_⟩
        · have h := hconj (s ^ (-m)) (Subgroup.mem_zpowers_iff.mpr ⟨-m, rfl⟩) n⁻¹
            (N.inv_mem hn)
          simpa [zpow_neg] using h
        · rw [zpow_neg]
          group
  obtain ⟨n, hn, m, hgm⟩ := key g (Subgroup.sup_eq_closure N (Subgroup.zpowers s) ▸ hg)
  rw [hgm]
  have hz2 : (s ^ m) ^ 2 = 1 := hpow2 (s ^ m) (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
  have hzN : (s ^ m) * n * (s ^ m)⁻¹ ∈ N :=
    hconj (s ^ m) (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩) n hn
  have hdecomp : (n * s ^ m) ^ 2 = n * ((s ^ m) * n * (s ^ m)⁻¹) * (s ^ m) ^ 2 := by
    simp only [pow_two]
    group
  rw [hdecomp, hz2, mul_one]
  exact N.mul_mem hn hzN

variable {W : Type} [CommGroup W] [Finite W]

theorem w1369_isQuasisimple_secSub_open {U Z : Subgroup W} {L : Subgroup (MulAut W)}
    (hL : StabPair L U Z) (hf : FaithOn L U Z) (hq : CFSG.Open.IsQuasisimple ↥L) :
    CFSG.Open.IsQuasisimple ↥(secSub U Z L) := by
  obtain ⟨e⟩ := mulEquiv_secSub hL hf
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq

private theorem w1369_inf_eq_bot_of_odd_of_isPGroup {G : Type*} [Group G] [Finite G]
    {Y R : Subgroup G} (hY : Odd (Nat.card Y)) (hR : IsPGroup 2 R) : Y ⊓ R = ⊥ := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card R) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hY)
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

private theorem w1369_isQuasisimple_native {Q : Type*} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hq.2
  refine ⟨Group.isPerfect_def.mpr hq.1, hq.2, ?_⟩
  by_contra hcon
  have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := by
    intro a b
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    have h1 : QuotientGroup.mk' (Subgroup.center Q) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have htop : Subgroup.center Q = ⊤ := top_le_iff.mp (hq.1 ▸ hle)
  exact (not_subsingleton_iff_nontrivial.mpr inferInstance)
    (QuotientGroup.subsingleton_iff.mpr htop)

theorem w1369_o2Trivial_of_odd_centralizer {M : Type} [CommGroup M] [Finite M]
    {Y L : Subgroup (MulAut M)} (hLY : L ≤ Y) (hN : (L.subgroupOf Y).Normal)
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Odd (Nat.card ↥((Subgroup.center ↥L).map L.subtype)))
    (hC : Odd (Nat.card ↥(Subgroup.centralizer (L : Set (MulAut M)) ⊓ Y))) :
    O2Trivial Y := by
  have hq' : CFSG.IsQuasisimple ↥L := w1369_isQuasisimple_native hq
  intro P hPY hPN hP2
  have hNPL : ((P ⊓ L).subgroupOf L).Normal := by
    have h1 : ((P.subgroupOf Y).comap (Subgroup.inclusion hLY)).Normal :=
      hPN.comap (Subgroup.inclusion hLY)
    have h2 : (P ⊓ L).subgroupOf L = (P.subgroupOf Y).comap (Subgroup.inclusion hLY) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
      constructor
      · rintro ⟨hxP, -⟩; exact hxP
      · intro hxP; exact ⟨hxP, x.2⟩
    rw [h2]; exact h1
  have hPL2 : IsPGroup 2 (P ⊓ L : Subgroup (MulAut M)) := hP2.to_le inf_le_left
  have hPLbot : P ⊓ L = ⊥ := by
    rcases CFSG.Quasithin.H13.Ch4.J4KX.normal_le_center_or_top hq'
      ((P ⊓ L).subgroupOf L) with hcenter | htop
    · have hle : P ⊓ L ≤ (Subgroup.center ↥L).map L.subtype := by
        intro x hx
        exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hcenter (Subgroup.mem_subgroupOf.mpr hx),
          rfl⟩
      have hinf := w1369_inf_eq_bot_of_odd_of_isPGroup
        (Y := (Subgroup.center ↥L).map L.subtype) (R := P ⊓ L) hZ hPL2
      rwa [inf_eq_right.mpr hle] at hinf
    · exfalso
      have hLP : L ≤ P := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥L) ∈ (P ⊓ L).subgroupOf L := by rw [htop]; trivial
        simpa using (Subgroup.mem_subgroupOf.mp hx').1
      haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
      haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
      haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
      exact (Group.IsPerfect.not_isNilpotent ↥L) (hP2.to_le hLP).isNilpotent
  have hPYnorm : Y ≤ Subgroup.normalizer (P : Set (MulAut M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mp hPN
  have hLYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut M)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hN
  have hcomm_le : ⁅P, L⁆ ≤ P ⊓ L := by
    rw [Subgroup.commutator_le]
    intro p hp l hl
    have hpY : p ∈ Y := hPY hp
    have hlY : l ∈ Y := hLY hl
    have hPmem : ⁅p, l⁆ ∈ P := by
      have hconj : l * p⁻¹ * l⁻¹ ∈ P :=
        (Subgroup.le_normalizer_iff.mp hPYnorm l hlY) p⁻¹ (P.inv_mem hp)
      rw [commutatorElement_def]
      simpa only [mul_assoc] using P.mul_mem hp hconj
    have hLmem : ⁅p, l⁆ ∈ L := by
      have hconj : p * l * p⁻¹ ∈ L :=
        (Subgroup.le_normalizer_iff.mp hLYnorm p hpY) l hl
      rw [commutatorElement_def]
      simpa only [mul_assoc] using L.mul_mem hconj (L.inv_mem hl)
    exact ⟨hPmem, hLmem⟩
  have hcomm_eq_bot : ⁅P, L⁆ = ⊥ := eq_bot_iff.mpr (hcomm_le.trans_eq hPLbot)
  have hPcent : P ≤ Subgroup.centralizer (L : Set (MulAut M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_eq_bot
  have hPle : P ≤ Subgroup.centralizer (L : Set (MulAut M)) ⊓ Y := le_inf hPcent hPY
  have hbot : (Subgroup.centralizer (L : Set (MulAut M)) ⊓ Y) ⊓ P = ⊥ :=
    w1369_inf_eq_bot_of_odd_of_isPGroup
      (Y := Subgroup.centralizer (L : Set (MulAut M)) ⊓ Y) (R := P) hC hP2
  rwa [inf_eq_right.mpr hPle] at hbot

theorem w1369_isKGroup_secSub {Y A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hY : CFSG.Open.IsKGroup ↥Y) (hA : A ≤ Y) (hstab : StabPair A U Z) :
    CFSG.IsKGroup ↥(secSub U Z A) := by
  have hAU : A ≤ stabSub U := fun a ha =>
    mem_stabSub_of_invariant (hstab a ha).1 (inv_mem_of_forall_mem a (hstab a ha).1)
  have hAZ : A ≤ stabSub Z := fun a ha =>
    mem_stabSub_of_invariant (hstab a ha).2 (inv_mem_of_forall_mem a (hstab a ha).2)
  let f : ↥A →* ↥(secSub U Z A) :=
    (B5.secHom A hAU hAZ).codRestrict (secSub U Z A) (fun a => by
      change (B5.secHom A hAU hAZ) a ∈ autSec A U Z
      rw [← B5.range_secHom A hAU hAZ]
      exact MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : MulAut (Sect U Z)) ∈ (B5.secHom A hAU hAZ).range := by
      rw [B5.range_secHom A hAU hAZ]
      exact y.2
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hy
    exact ⟨a, Subtype.ext ha⟩
  have hA_K : CFSG.Open.IsKGroup ↥A := CFSG.Open.IsKGroup.of_le hY hA
  have hsec : CFSG.Open.IsKGroup ↥(secSub U Z A) :=
    CFSG.Open.IsKGroup.of_surjective hA_K f hf
  have hsec' : CFSG.KCore.KGroupNonab CFSG.Assembly.InCatalog ↥(secSub U Z A) := hsec
  exact hsec'.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
