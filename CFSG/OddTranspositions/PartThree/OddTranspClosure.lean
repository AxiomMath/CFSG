module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.Asc72Minimal
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type*} [Group G] {D : Set G}

abbrev inClosure (Ω : Set G) : Set (Subgroup.closure Ω) :=
  {z | (z : G) ∈ Ω}

theorem closure_inClosure (Ω : Set G) : Subgroup.closure (inClosure Ω) = ⊤ :=
  Subgroup.closure_preimage_eq_top _

theorem isClass_inClosure_of_conjOrbit_closure_eq {H : Type} [Group H] {Ω : Set H} {x : H}
    (hx : x ∈ Ω) (horb : conjOrbit (Subgroup.closure Ω) x = Ω) :
    ∃ t : Subgroup.closure Ω, inClosure Ω = {g | IsConj t g} := by
  refine ⟨⟨x, Subgroup.subset_closure hx⟩, ?_⟩
  ext g
  constructor
  · intro hg
    have hg' : (g : H) ∈ conjOrbit (Subgroup.closure Ω) x := by rw [horb]; exact hg
    obtain ⟨m, hm, hgm⟩ := hg'
    exact isConj_iff.mpr ⟨⟨m, hm⟩, Subtype.ext hgm.symm⟩
  · intro hg
    obtain ⟨c, hc⟩ := isConj_iff.mp hg
    have hc' : (c : H) * x * (c : H)⁻¹ = (g : H) := by
      simpa using congrArg Subtype.val hc
    have hmem : (g : H) ∈ conjOrbit (Subgroup.closure Ω) x := ⟨(c : H), c.2, hc'.symm⟩
    rw [horb] at hmem
    exact hmem

theorem isOddTransp_inClosure (hD : IsOddTransp D) {Ω : Set G} (hΩD : Ω ⊆ D) :
    IsOddTransp (inClosure Ω) := by
  constructor
  · intro z hz
    rw [← Subgroup.orderOf_coe]
    exact hD.1 _ (hΩD hz)
  · intro z hz z' hz'
    have h : orderOf (z * z') = orderOf ((z : G) * z') := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [h]
    exact hD.2 _ (hΩD hz) _ (hΩD hz')

theorem setup_inClosure (hD : IsOddTransp D) {Ω : Set G} (hΩD : Ω ⊆ D)
    (hcls : ∃ t : Subgroup.closure Ω, inClosure Ω = {g | IsConj t g}) :
    Setup (Subgroup.closure Ω) (inClosure Ω) :=
  ⟨hcls, isOddTransp_inClosure hD hΩD, closure_inClosure Ω⟩

theorem commute_of_commute_mk_of_le_center' {X : Type*} [Group X] {E : Set X}
    (hE : IsOddTransp E) {N : Subgroup X} [N.Normal] (hN : N ≤ Subgroup.center X) {z w : X}
    (hz : z ∈ E) (hw : w ∈ E) (h : Commute (QuotientGroup.mk' N z) (QuotientGroup.mk' N w)) :
    Commute z w := by
  by_contra hnc
  have hzz : z * z = 1 := hE.mul_self_eq_one hz
  have hww : w * w = 1 := hE.mul_self_eq_one hw
  have hoddzw : Odd (orderOf (z * w)) := hE.odd_of_not_commute hz hw hnc
  have hcen : (z * w) ^ 2 ∈ Subgroup.center X := by
    refine hN ((QuotientGroup.eq_one_iff _).mp ?_)
    change QuotientGroup.mk' N ((z * w) ^ 2) = 1
    rw [map_pow, map_mul, h.mul_pow, pow_two (QuotientGroup.mk' N z),
      pow_two (QuotientGroup.mk' N w), ← map_mul, ← map_mul, hzz, hww, map_one, mul_one]
  have h1 : (z * w) ^ 2 = (w * z) ^ 2 := by
    have hc := Subgroup.mem_center_iff.1 hcen z
    calc (z * w) ^ 2 = z⁻¹ * (z * (z * w) ^ 2) := by group
      _ = z⁻¹ * ((z * w) ^ 2 * z) := by rw [hc]
      _ = (w * z) ^ 2 := by simp only [pow_two]; group
  have h2 : (z * w) ^ 4 = 1 := by
    have h3 : (w * z) = (z * w)⁻¹ := by rw [mul_inv_rev, hE.inv_eq hz, hE.inv_eq hw]
    have h4 : (z * w) ^ 2 * (z * w) ^ 2 = 1 := by
      calc (z * w) ^ 2 * (z * w) ^ 2 = (z * w) ^ 2 * (w * z) ^ 2 := by rw [← h1]
        _ = 1 := by rw [h3, inv_pow, mul_inv_cancel]
    calc (z * w) ^ 4 = (z * w) ^ 2 * (z * w) ^ 2 := by group
      _ = 1 := h4
  have hdvd : orderOf (z * w) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h2)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hne
    rw [hi] at hoddzw
    exact (Nat.not_even_iff_odd.2 hoddzw) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact hnc (hE.eq_of_mul_eq_one hz hi ▸ Commute.refl z)

theorem injOn_mk_of_le_center {X : Type*} [Group X] {E : Set X} (hE : IsOddTransp E)
    {N : Subgroup X} [N.Normal] (hN : N ≤ Subgroup.center X)
    (hnc : ∀ a ∈ E, ∃ b ∈ E, ¬ Commute a b) : Set.InjOn (QuotientGroup.mk' N) E := by
  intro x hx y hy hq
  set z : X := x⁻¹ * y with hzdef
  have hzc : z ∈ Subgroup.center X := hN (QuotientGroup.eq.mp hq)
  have hzcomm : ∀ g : X, Commute z g := fun g => ((Subgroup.mem_center_iff.mp hzc) g).symm
  by_contra hne
  have hz1 : z ≠ 1 := by
    intro h
    apply hne
    calc x = x * z := by rw [h, mul_one]
      _ = y := by rw [hzdef]; group
  have hx2 : x * x = 1 := hE.mul_self_eq_one hx
  have hy2 : y * y = 1 := hE.mul_self_eq_one hy
  have hy_eq : y = x * z := by rw [hzdef]; group
  have hz2 : z * z = 1 := by
    have h1 : y ^ 2 = x ^ 2 * z ^ 2 := by rw [hy_eq, (hzcomm x).symm.mul_pow 2]
    rw [pow_two, pow_two, pow_two, hx2, hy2, one_mul] at h1
    exact h1.symm
  have hzord : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using hz2) hz1
  obtain ⟨w, hw, hxw⟩ := hnc x hx
  have hodd : Odd (orderOf (x * w)) := hE.odd_of_not_commute hx hw hxw
  have hm1 : orderOf (x * w) ≠ 1 := fun h =>
    hxw (hE.eq_of_mul_eq_one hx (orderOf_eq_one_iff.mp h) ▸ Commute.refl x)
  have hyw : y * w = (x * w) * z := by
    rw [hy_eq, mul_assoc, (hzcomm w).eq, ← mul_assoc]
  have hcop : (orderOf (x * w)).Coprime (orderOf z) := by
    rw [hzord]
    exact hodd.coprime_two_right
  have hord : orderOf (y * w) = 2 * orderOf (x * w) := by
    rw [hyw, ((hzcomm (x * w)).symm).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hzord,
      Nat.mul_comm]
  rcases hE.2 y hy w hw with hdvd | hodd'
  · rw [hord] at hdvd
    have : orderOf (x * w) ∣ 1 :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp (by simpa using hdvd)
    exact hm1 (Nat.dvd_one.mp this)
  · rw [hord] at hodd'
    exact hodd'.not_two_dvd_nat (dvd_mul_right 2 _)

end CFSG.OddTranspositions.PartThree
