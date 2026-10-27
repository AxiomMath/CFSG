module

public import CFSG.RankThree.SubgroupLists.ExtraspecialCore
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped commutatorElement
open CFSG.RankThree.SubgroupLists (commutatorElement_mul_left commutatorElement_mul_right
  commutatorElement_mem_center)

variable {H : Type*} [Group H]

theorem ext27_noncomm (hcard : Nat.card H = 27) (hext : CFSG.IsExtraspecialPGroup 3 H) :
    ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.center H = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun x => Subgroup.mem_center_iff.mpr fun g => hcon g x
  have h3 := hext.2.2.2
  rw [htop, Subgroup.card_top, hcard] at h3
  omega

theorem ext27_card_quot (hcard : Nat.card H = 27) (hext : CFSG.IsExtraspecialPGroup 3 H) :
    Nat.card (H ⧸ Subgroup.center H) = 9 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
  rw [hcard, hext.2.2.2] at h1
  omega

theorem ext27_cube [Finite H] (hcard : Nat.card H = 27) (hext : CFSG.IsExtraspecialPGroup 3 H) (a : H) :
    a ^ 3 ∈ Subgroup.center H := by
  have hQcard := ext27_card_quot hcard hext
  have hcubeQ : ∀ q : H ⧸ Subgroup.center H, q ^ 3 = 1 := by
    intro q
    by_contra hq
    have hdvd : orderOf q ∣ 3 ^ 2 := by
      have := orderOf_dvd_natCard q
      rw [hQcard] at this
      norm_num
      exact this
    obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hcyc : IsCyclic (H ⧸ Subgroup.center H) := by
      apply isCyclic_of_orderOf_eq_card q
      rw [hQcard]
      interval_cases i
      · exfalso
        have h1 : orderOf q = 1 := by simpa using hoi
        exact hq (by rw [orderOf_eq_one_iff.mp h1]; simp)
      · exfalso
        have h3 : orderOf q = 3 := by simpa using hoi
        exact hq (by rw [← h3]; exact pow_orderOf_eq_one q)
      · simpa using hoi
    obtain ⟨a, b, hab⟩ := ext27_noncomm hcard hext
    have hcommH := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center H)) (QuotientGroup.ker_mk' _).le
    exact hab (hcommH.is_comm.comm a b)
  have h1 := hcubeQ (QuotientGroup.mk a)
  rw [← QuotientGroup.mk_pow] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem ext27_center_cube (hext : CFSG.IsExtraspecialPGroup 3 H) (z : H)
    (hz : z ∈ Subgroup.center H) : z ^ 3 = 1 := by
  have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center H)
  rw [hext.2.2.2] at h1
  have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
  simpa using congrArg (fun w : Subgroup.center H => (w : H)) h2

theorem ext27_pm [Finite H] (hcard : Nat.card H = 27) (hext : CFSG.IsExtraspecialPGroup 3 H) (φ : H ≃* H)
    (hφz : ∀ z ∈ Subgroup.center H, φ z = z) (hφ2 : ∀ x, φ (φ x) = x) :
    (∀ a, φ a * a⁻¹ ∈ Subgroup.center H) ∨ (∀ a, φ a * a ∈ Subgroup.center H) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
  have hclass : commutator H ≤ Subgroup.center H := hext.2.1.le
  have hcomm : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H := commutatorElement_mem_center hclass
  have hcube := ext27_cube hcard hext
  have hcen3 := ext27_center_cube hext
  have hcenc : ∀ z ∈ Subgroup.center H, ∀ g : H, g * z = z * g :=
    fun z hz => Subgroup.mem_center_iff.mp hz
  have hQcard := ext27_card_quot hcard hext
  obtain ⟨xm, hxm⟩ : ∃ x : H, x = a⁻¹ * φ a := ⟨_, rfl⟩
  obtain ⟨xp, hxp⟩ : ∃ x : H, x = b * φ b := ⟨_, rfl⟩
  have hxmZ : xm ∉ Subgroup.center H := by
    intro hz
    apply ha
    have h1 : φ a * a⁻¹ = a * xm * a⁻¹ := by rw [hxm]; group
    rw [h1, hcenc xm hz a]
    simpa using hz
  have hxpZ : xp ∉ Subgroup.center H := by
    intro hz
    apply hb
    have h1 : φ b * b = b⁻¹ * xp * b := by rw [hxp]; group
    rw [h1, hcenc xp hz b⁻¹]
    simpa using hz
  have hφxm : φ xm = xm⁻¹ := by rw [hxm, map_mul, map_inv, hφ2]; group
  obtain ⟨ζ, hζ⟩ : ∃ ζ : H, ζ = ⁅(φ b)⁻¹, b⁻¹⁆ := ⟨_, rfl⟩
  have hζZ : ζ ∈ Subgroup.center H := by rw [hζ]; exact hcomm _ _
  have hφxp : φ xp = xp * ζ := by
    rw [hxp, hζ, map_mul, hφ2, commutatorElement_def]
    group
  have hc1 : ⁅xp, xm⁆ = 1 := by
    have hcz : ⁅xp, xm⁆ ∈ Subgroup.center H := hcomm _ _
    have hφc : φ ⁅xp, xm⁆ = ⁅xp, xm⁆ := hφz _ hcz
    rw [map_commutatorElement, hφxp, hφxm, commutatorElement_mul_left hclass] at hφc
    have hζc : ⁅ζ, xm⁻¹⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hcenc ζ hζZ xm⁻¹).symm
    have hinv : ⁅xp, xm⁻¹⁆ = ⁅xp, xm⁆⁻¹ := by
      have h1 := commutatorElement_mul_right hclass xp xm⁻¹ xm
      rw [inv_mul_cancel, commutatorElement_one_right] at h1
      exact (eq_inv_of_mul_eq_one_left h1.symm)
    rw [hζc, mul_one, hinv] at hφc
    have hcc : ⁅xp, xm⁆ * ⁅xp, xm⁆ = 1 := by
      have : ⁅xp, xm⁆ * ⁅xp, xm⁆⁻¹ = 1 := mul_inv_cancel _
      rwa [hφc] at this
    have hc3 := hcen3 _ hcz
    calc ⁅xp, xm⁆ = ⁅xp, xm⁆ ^ 3 * (⁅xp, xm⁆ * ⁅xp, xm⁆)⁻¹ := by rw [pow_three]; group
      _ = 1 := by rw [hcc, hc3]; simp
  let π : H →* H ⧸ Subgroup.center H := QuotientGroup.mk' (Subgroup.center H)
  have hqpne : π xp ≠ 1 := fun h1 => hxpZ ((QuotientGroup.eq_one_iff _).mp h1)
  have hqp3 : (π xp) ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hcube xp)
  have hordp : orderOf (π xp) = 3 := orderOf_eq_prime hqp3 hqpne
  have hqmnm : π xm ∉ Subgroup.zpowers (π xp) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : π (xp ^ k) = π xm := by rw [map_zpow]; exact hk
    have hz : (xp ^ k)⁻¹ * xm ∈ Subgroup.center H := QuotientGroup.eq.mp hk'
    obtain ⟨z, hzdef⟩ : ∃ z : H, z = (xp ^ k)⁻¹ * xm := ⟨_, rfl⟩
    rw [← hzdef] at hz
    have hxz : xm = xp ^ k * z := by rw [hzdef]; group
    have hcx : Commute xp ζ := hcenc ζ hζZ xp
    have h1 : φ xm = xp ^ k * ζ ^ k * z := by
      rw [hxz, map_mul, map_zpow, hφxp, hcx.mul_zpow, hφz z hz]
    have hζk : ζ ^ k ∈ Subgroup.center H := Subgroup.zpow_mem _ hζZ k
    have h2 : xm⁻¹ = xm * ζ ^ k := by
      rw [← hφxm, h1]
      calc xp ^ k * ζ ^ k * z = xp ^ k * (ζ ^ k * z) := by rw [mul_assoc]
        _ = xp ^ k * (z * ζ ^ k) := by rw [hcenc z hz (ζ ^ k)]
        _ = xm * ζ ^ k := by rw [hxz]; exact (mul_assoc _ _ _).symm
    have h3 : xm * xm = (ζ ^ k)⁻¹ := by
      calc xm * xm = xm * (xm * ζ ^ k) * (ζ ^ k)⁻¹ := by group
        _ = xm * xm⁻¹ * (ζ ^ k)⁻¹ := by rw [← h2]
        _ = (ζ ^ k)⁻¹ := by group
    apply hxmZ
    have h4 : xm ^ 3 * (xm * xm)⁻¹ = xm := by rw [pow_three]; group
    rw [← h4]
    exact Subgroup.mul_mem _ (hcube xm) (Subgroup.inv_mem _ (by rw [h3]; exact Subgroup.inv_mem _ hζk))
  have hS : Subgroup.closure {π xp, π xm} = ⊤ := by
    set S := Subgroup.closure {π xp, π xm} with hSdef
    have hzp : Subgroup.zpowers (π xp) ≤ S :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hqmS : π xm ∈ S := Subgroup.subset_closure (by simp)
    have hne : Subgroup.zpowers (π xp) ≠ S := fun h1 => hqmnm (by rw [h1]; exact hqmS)
    have hdvd9 : Nat.card S ∣ 3 ^ 2 := by
      have := Subgroup.card_subgroup_dvd_card S
      rw [hQcard] at this
      norm_num
      exact this
    have hdvd3 : 3 ∣ Nat.card S := by
      have := Subgroup.card_dvd_of_le hzp
      rwa [Nat.card_zpowers, hordp] at this
    have hne3 : Nat.card S ≠ 3 := fun h3 =>
      hne (Subgroup.eq_of_le_of_card_ge hzp (by rw [Nat.card_zpowers, hordp, h3]))
    have h9 : Nat.card S = 9 := by
      obtain ⟨i, hi, hsi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd9
      interval_cases i
      · rw [hsi] at hdvd3
        norm_num at hdvd3
      · exact absurd (by simpa using hsi) hne3
      · simpa using hsi
    exact Subgroup.eq_top_of_card_eq S (by rw [h9, hQcard])
  let f : H →* H :=
    { toFun := fun y => ⁅xp, y⁆
      map_one' := commutatorElement_one_right xp
      map_mul' := fun y y' => commutatorElement_mul_right hclass xp y y' }
  have hf : ∀ y, f y = ⁅xp, y⁆ := fun y => rfl
  have hkerZ : ∀ z ∈ Subgroup.center H, f z = 1 := fun z hz =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hcenc z hz xp)
  have hgen : {xp, xm} ⊆ (f.ker : Set H) := by
    intro t ht
    rcases ht with rfl | rfl
    · exact (MonoidHom.mem_ker).mpr (by rw [hf]; exact commutatorElement_self _)
    · exact (MonoidHom.mem_ker).mpr (by rw [hf]; exact hc1)
  have hall : ∀ y : H, ⁅xp, y⁆ = 1 := by
    intro y
    have hπy : π y ∈ Subgroup.closure {π xp, π xm} := by rw [hS]; exact Subgroup.mem_top _
    have hmap : Subgroup.closure {π xp, π xm} = (Subgroup.closure {xp, xm}).map π := by
      rw [MonoidHom.map_closure, Set.image_pair]
    rw [hmap] at hπy
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hπy
    have hwker : f w = 1 := (MonoidHom.mem_ker).mp ((Subgroup.closure_le f.ker).mpr hgen hw)
    have hwz : w⁻¹ * y ∈ Subgroup.center H := QuotientGroup.eq.mp hwy
    have hy : y = w * (w⁻¹ * y) := by group
    have : f y = 1 := by rw [hy, map_mul, hwker, hkerZ _ hwz, mul_one]
    exact this
  apply hxpZ
  exact Subgroup.mem_center_iff.mpr fun g => (commutatorElement_eq_one_iff_mul_comm.mp (hall g)).symm

end CFSG.RankThree.PartOne.N1322
