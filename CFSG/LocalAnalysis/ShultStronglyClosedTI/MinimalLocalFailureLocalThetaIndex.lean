module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaImage
public import CFSG.Assembly.OrderReductions.PrimePart

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.OrderReductions.PrimePart
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem elementary_odd_supplement_index
    (I U : Subgroup G) [I.Normal] [IsElementaryAbelian 2 I]
    (hUodd : Odd (Nat.card U)) (hgen : I ⊔ U = ⊤) :
    ∃ n : ℕ, U.index = 2 ^ n := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
  have hcoprime : Nat.Coprime (Nat.card I) (Nat.card U) := by
    rw [hn]
    exact (Nat.coprime_two_left.mpr hUodd).pow_left n
  have hdis : Disjoint I U := Subgroup.disjoint_of_coprime_natCard hcoprime
  have hmul : (I : Set G) * (U : Set G) = Set.univ := by
    ext g
    constructor
    · intro _
      exact Set.mem_univ g
    · intro _
      exact Set.mem_mul.mpr (Subgroup.mem_sup_of_normal_left.mp
        (hgen.symm ▸ Subgroup.mem_top g))
  have hcompl := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis hmul
  exact ⟨n, hcompl.index_eq_card.trans hn⟩

theorem odd_kernel_elementary_factor_index
    (I U R : Subgroup G) [I.Normal] [R.Normal]
    (hUodd : Odd (Nat.card U)) (hgen : I ⊔ U = ⊤)
    (hinter : I ⊓ R ≤ U)
    [IsElementaryAbelian 2 (I.map (QuotientGroup.mk' R))] :
    ∃ n : ℕ, U.index = 2 ^ n := by
  let C := I ⊓ R
  let q := QuotientGroup.mk' C
  let r := QuotientGroup.mk' R
  let e : I.map q →* I.map r :=
    ((QuotientGroup.map C R (MonoidHom.id G) inf_le_right).comp
      (I.map q).subtype).codRestrict _ (by
        rintro ⟨x, hx⟩
        obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hx
        exact Subgroup.mem_map.mpr ⟨i, hi, rfl⟩)
  have heinj : Function.Injective e := by
    apply (MonoidHom.ker_eq_bot_iff e).mp
    apply le_antisymm _ bot_le
    rintro x hx
    obtain ⟨i, hi, hix⟩ := Subgroup.mem_map.mp x.property
    have hir : r i = 1 := by
      have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      change QuotientGroup.map C R (MonoidHom.id G) inf_le_right x.val = 1 at hh
      rw [← hix] at hh
      exact hh
    have hiR : i ∈ R := (QuotientGroup.eq_one_iff i).mp hir
    have hiC : i ∈ C := ⟨hi, hiR⟩
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    rw [← hix]
    exact (QuotientGroup.eq_one_iff i).mpr hiC
  let : IsElementaryAbelian 2 (I.map q) := elementary_of_injective e heinj
  let : (I.map q).Normal := (inferInstance : I.Normal).map q
    (QuotientGroup.mk'_surjective C)
  have hUimageodd : Odd (Nat.card (U.map q)) :=
    hUodd.of_dvd_nat (Subgroup.card_map_dvd U q)
  have hgenimage : I.map q ⊔ U.map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top,
      q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective C)]
  obtain ⟨n, hn⟩ := elementary_odd_supplement_index
    (I.map q) (U.map q) hUimageodd hgenimage
  refine ⟨n, ?_⟩
  have hkernel : q.ker ≤ U := by
    change (QuotientGroup.mk' C).ker ≤ U
    rw [QuotientGroup.ker_mk']
    exact hinter
  rw [U.index_map_eq (QuotientGroup.mk'_surjective C) hkernel] at hn
  exact hn

theorem normal_factor_relative_index
    (R U : Subgroup G) [R.Normal] :
    U.relIndex (U ⊔ R) = U.relIndex R := by
  have hUcard : U.relIndex (U ⊔ R) * Nat.card U =
      Nat.card (U ⊔ R : Subgroup G) := by
    have hh := (U.subgroupOf (U ⊔ R)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at hh
    exact hh
  have hRcard : R.relIndex U * Nat.card R =
      Nat.card (U ⊔ R : Subgroup G) := by
    have hh := (R.subgroupOf (U ⊔ R)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv,
      ← Subgroup.relIndex, Subgroup.relIndex_sup_right] at hh
    exact hh
  have hUinf := R.relIndex_mul_card U
  have hRinf := U.relIndex_mul_card R
  rw [inf_comm R U] at hUinf
  have hinfpos : 0 < Nat.card (U ⊓ R : Subgroup G) := Nat.card_pos
  have hrelpos : 0 < R.relIndex U := by
    have hUpos : 0 < Nat.card U := Nat.card_pos
    nlinarith
  nlinarith

theorem odd_normal_le_of_two_power_index
    (R U : Subgroup G) [R.Normal] (hRodd : Odd (Nat.card R))
    (hindex : ∃ n : ℕ, U.index = 2 ^ n) : R ≤ U := by
  obtain ⟨n, hn⟩ := hindex
  have hdiv : U.relIndex R ∣ U.index := by
    rw [← normal_factor_relative_index R U]
    exact Subgroup.relIndex_dvd_index_of_le le_sup_left
  have hcarddiv : U.relIndex R ∣ Nat.card R := U.relIndex_dvd_card R
  have hcoprime : Nat.Coprime (Nat.card R) U.index := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr hRodd).pow_right n
  exact (Subgroup.relIndex_eq_one).mp
    (Nat.eq_one_of_dvd_coprimes hcoprime hcarddiv hdiv)

theorem prime_part_of_two_power_index {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (U : Subgroup G) (hindex : ∃ n : ℕ, U.index = 2 ^ n) :
    primePart p (Nat.card U) = primePart p (Nat.card G) := by
  obtain ⟨n, hn⟩ := hindex
  have hnot : ¬ p ∣ U.index := by
    rw [hn]
    exact hp.coprime_iff_not_dvd.mp ((Nat.coprime_two_right.mpr hpodd).pow_right n)
  have hindexne : U.index ≠ 0 := by rw [hn]; exact pow_ne_zero n (by decide)
  rw [← U.card_mul_index, primePart_mul p _ _ Nat.card_pos.ne' hindexne]
  simp only [primePart, Nat.factorization_eq_zero_of_not_dvd hnot, pow_zero, mul_one]

theorem supplied_sylow_of_two_power_index {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (U : Subgroup G) (hindex : ∃ n : ℕ, U.index = 2 ^ n) (Q : Sylow p U) :
    ∃ S : Sylow p G, (S : Subgroup G) = (Q : Subgroup U).map U.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card ((Q : Subgroup U).map U.subtype) =
      primePart p (Nat.card G) := by
    rw [sylow_map_card_eq_primePart, prime_part_of_two_power_index hp hpodd U hindex]
  exact ⟨Sylow.ofCard ((Q : Subgroup U).map U.subtype) hcard, rfl⟩

end CFSG.ShultStronglyClosedTI.LocalTheta
