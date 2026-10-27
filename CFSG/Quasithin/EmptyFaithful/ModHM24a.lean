module

public import CFSG.Quasithin.EmptyFaithful.ModHOut4
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.Quasithin.Background.A318PL3Unit
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.FFC4Res
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.ModHEl
public import CFSG.Quasithin.EmptyFaithful.ModHOut3
public import CFSG.Quasithin.EmptyFaithful.ModHPerm
public import CFSG.Quasithin.EmptyFaithful.ModHRho
public import CFSG.Quasithin.EmptyFaithful.R3c11Core
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.SBd12Main
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements
public import Certificates.Kernel.J4Count.Prim
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.ModH.M24a

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24 (m24_overgroups m24Mems)

theorem exists_hall_two_p {K : Type} [Group K] [Finite K] (hK : Group.IsSolvable K) (U : Subgroup K)
    (hU : IsPGroup 2 ↥U) (p : ℕ) (hp : p.Prime) :
    ∃ H : Subgroup K, U ≤ H ∧ (∀ q : ℕ, q.Prime → q ∣ Nat.card ↥H → q = 2 ∨ q = p) ∧
      ¬ 2 ∣ H.index ∧ ¬ p ∣ H.index := by
  classical
  let π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp⟩}
  have hU' : CFSG.IsPiSubgroup π U := by
    intro q hq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU
    have h2 : q.val ∣ 2 ^ n := hn ▸ hq
    have : q.val = 2 :=
      (Nat.prime_dvd_prime_iff_eq q.prop Nat.prime_two).1 (q.prop.dvd_of_dvd_pow h2)
    left
    exact Subtype.ext this
  obtain ⟨H, hH, hUH⟩ := CFSG.SolvableHall.solvable_hall_containment hK π U hU'
  refine ⟨H, hUH, fun q hq hqd => ?_, ?_, ?_⟩
  · rcases hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqd with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h
  · intro h2
    exact hH.p_in_pi_of_p_dvd_index ⟨2, Nat.prime_two⟩ h2 (Or.inl rfl)
  · intro hpd
    exact hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpd (Or.inr rfl)

theorem hall_5120_of_322560 {h k : ℕ} (hr : h * k = 322560)
    (hh : ∀ q : ℕ, q.Prime → q ∣ h → q = 2 ∨ q = 5) (hk2 : ¬ 2 ∣ k) (hk5 : ¬ 5 ∣ k) :
    h = 5120 := by
  have hk : k ∣ 5120 * 63 := ⟨h, by rw [show 5120 * 63 = 322560 by norm_num, ← hr]; ring⟩
  have hc2 : Nat.Coprime (2 ^ 10) k :=
    Nat.Coprime.pow_left 10 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk2)
  have hc5 : Nat.Coprime 5 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk5
  have hc : Nat.Coprime 5120 k := by
    have := Nat.Coprime.mul_left hc2 hc5
    simpa using this
  have hk63 : k ∣ 63 := (Nat.Coprime.dvd_of_dvd_mul_left hc.symm hk)
  have hkle : k ≤ 63 := Nat.le_of_dvd (by norm_num) hk63
  interval_cases k <;>
    first
    | omega
    | (exfalso; have := hh 3 (by norm_num) (by omega); omega)
    | (exfalso; have := hh 7 (by norm_num) (by omega); omega)

theorem hall_5120_of_138240 {h k : ℕ} (hr : h * k = 138240)
    (hh : ∀ q : ℕ, q.Prime → q ∣ h → q = 2 ∨ q = 5) (hk2 : ¬ 2 ∣ k) (hk5 : ¬ 5 ∣ k) :
    h = 5120 := by
  have hk : k ∣ 5120 * 27 := ⟨h, by rw [show 5120 * 27 = 138240 by norm_num, ← hr]; ring⟩
  have hc2 : Nat.Coprime (2 ^ 10) k :=
    Nat.Coprime.pow_left 10 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk2)
  have hc5 : Nat.Coprime 5 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk5
  have hc : Nat.Coprime 5120 k := by
    have := Nat.Coprime.mul_left hc2 hc5
    simpa using this
  have hk27 : k ∣ 27 := (Nat.Coprime.dvd_of_dvd_mul_left hc.symm hk)
  have hkle : k ≤ 27 := Nat.le_of_dvd (by norm_num) hk27
  interval_cases k <;>
    first
    | omega
    | (exfalso; have := hh 3 (by norm_num) (by omega); omega)

theorem hall_7168_of_64512 {h k : ℕ} (hr : h * k = 64512)
    (hh : ∀ q : ℕ, q.Prime → q ∣ h → q = 2 ∨ q = 7) (hk2 : ¬ 2 ∣ k) (hk7 : ¬ 7 ∣ k) :
    h = 7168 := by
  have hk : k ∣ 7168 * 9 := ⟨h, by rw [show 7168 * 9 = 64512 by norm_num, ← hr]; ring⟩
  have hc2 : Nat.Coprime (2 ^ 10) k :=
    Nat.Coprime.pow_left 10 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk2)
  have hc7 : Nat.Coprime 7 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk7
  have hc : Nat.Coprime 7168 k := by
    have := Nat.Coprime.mul_left hc2 hc7
    simpa using this
  have hk9 : k ∣ 9 := (Nat.Coprime.dvd_of_dvd_mul_left hc.symm hk)
  have hkle : k ≤ 9 := Nat.le_of_dvd (by norm_num) hk9
  interval_cases k <;>
    first
    | omega
    | (exfalso; have := hh 3 (by norm_num) (by omega); omega)

abbrev G24 : Type := ↥NativeSporadic.M24

section Main


theorem overgroup_row (hns : ¬ Group.IsSolvable G24) {Sb Y : Subgroup G24} (hS : IsSylowTwoOf Sb ⊤)
    (hY : Sb ≤ Y) (hYs : Group.IsSolvable ↥Y) : ∃ m ∈ m24Mems, Nat.card ↥Y = m.order := by
  have : Finite G24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).1
  have hX : Nonempty (G24 ≃* NativeSporadic.Carrier .M24) := ⟨MulEquiv.refl _⟩
  rcases m24_overgroups hX hS hY with htop | ⟨m, hm, hord, -, -⟩
  · exfalso
    apply hns
    rw [htop] at hYs
    exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup G24).subtype)
      (by intro x; exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  · exact ⟨m, hm, hord⟩

theorem hall_overgroup_card (hns : ¬ Group.IsSolvable G24) {Sb Zb : Subgroup G24}
    (hS : IsSylowTwoOf Sb ⊤) (hSZ : Sb ≤ Zb) (hZs : Group.IsSolvable ↥Zb) (p : ℕ) (hp : p.Prime) :
    ∃ H k : ℕ, H * k = Nat.card ↥Zb ∧ ¬ 2 ∣ k ∧ ¬ p ∣ k ∧
      (∀ q : ℕ, q.Prime → q ∣ H → q = 2 ∨ q = p) ∧ ∃ m ∈ m24Mems, H = m.order := by
  have : Finite G24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).1
  have hU : IsPGroup 2 ↥(Sb.subgroupOf Zb) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSZ).symm
  obtain ⟨H, hUH, hHq, hk2, hkp⟩ := exists_hall_two_p hZs (Sb.subgroupOf Zb) hU p hp
  have hHZ : H.map Zb.subtype ≤ Zb := Subgroup.map_subtype_le H
  have hSH : Sb ≤ H.map Zb.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hSZ]
    exact Subgroup.map_mono hUH
  have hHs : Group.IsSolvable ↥(H.map Zb.subtype) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hHZ)
      (Subgroup.inclusion_injective hHZ)
  obtain ⟨m, hm, hord⟩ := overgroup_row hns hS hSH hHs
  have hcard : Nat.card ↥(H.map Zb.subtype) = Nat.card ↥H :=
    (Nat.card_congr (H.equivMapOfInjective Zb.subtype Subtype.val_injective).toEquiv).symm
  refine ⟨Nat.card ↥H, H.index, ?_, hk2, hkp, hHq, m, hm, ?_⟩
  · exact Subgroup.card_mul_index H
  · rw [← hcard, hord]

theorem card_nine_m24 (hns : ¬ Group.IsSolvable G24) {Sb Zb : Subgroup G24} (hS : IsSylowTwoOf Sb ⊤)
    (hSZ : Sb ≤ Zb) (hZs : Group.IsSolvable ↥Zb) (h9 : 9 ∣ Nat.card ↥Zb) :
    Nat.card ↥Zb = 9216 := by
  obtain ⟨m, hm, hord⟩ := overgroup_row hns hS hSZ hZs
  have hno : ∀ m' ∈ m24Mems, m'.order ≠ 5120 ∧ m'.order ≠ 7168 := by decide
  simp only [m24Mems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (hord ▸ h9) (by decide)
  · exfalso
    obtain ⟨H, k, hHk, hk2, hk5, hHq, m', hm', hHm⟩ :=
      hall_overgroup_card hns hS hSZ hZs 5 (by norm_num)
    have := hall_5120_of_322560 (by rw [hHk]; exact hord) hHq hk2 hk5
    exact (hno m' hm').1 (hHm ▸ this)
  · exfalso
    obtain ⟨H, k, hHk, hk2, hk7, hHq, m', hm', hHm⟩ :=
      hall_overgroup_card hns hS hSZ hZs 7 (by norm_num)
    have := hall_7168_of_64512 (by rw [hHk]; exact hord) hHq hk2 hk7
    exact (hno m' hm').2 (hHm ▸ this)
  · exfalso
    obtain ⟨H, k, hHk, hk2, hk5, hHq, m', hm', hHm⟩ :=
      hall_overgroup_card hns hS hSZ hZs 5 (by norm_num)
    have := hall_5120_of_138240 (by rw [hHk]; exact hord) hHq hk2 hk5
    exact (hno m' hm').1 (hHm ▸ this)
  · exact absurd (hord ▸ h9) (by decide)
  · exact hord
  · exact absurd (hord ▸ h9) (by decide)
  · exact absurd (hord ▸ h9) (by decide)
  · exact absurd (hord ▸ h9) (by decide)
  · exact absurd (hord ▸ h9) (by decide)
  · exact hord
  · exact absurd (hord ▸ h9) (by decide)
  · exact hord

end Main

end CFSG.Quasithin.ModH.M24a
