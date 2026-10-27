module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent
import TauCeti.GroupTheory.Commutator
import CFSG.Mathlib.GroupTheory.InvertedCommuteCore
import CFSG.RankThree.PartOne.K1214.CycAlg
import CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_lt_pow_mem_commutator_mem (hG : IsPGroup p G) {H K : Subgroup G} (hKH : K ≤ H)
    (hne : K ≠ H) :
    ∃ M : Subgroup G, K ≤ M ∧ M < H ∧ (∀ g ∈ H, g ^ p ∈ M) ∧
      ∀ a ∈ H, ∀ b ∈ H, ⁅a, b⁆ ∈ M := by
  let K' : Subgroup ↥H := K.subgroupOf H
  have hK'ne : K' ≠ ⊤ := by
    intro htop
    exact hne (le_antisymm hKH (Subgroup.subgroupOf_eq_top.mp htop))
  have hfin : Finite (Subgroup ↥H) :=
    Finite.of_injective (fun L : Subgroup ↥H => (L : Set ↥H)) SetLike.coe_injective
  obtain ⟨M', hM'coat, hK'M'⟩ := (eq_top_or_exists_le_coatom K').resolve_left hK'ne
  have hpH : IsPGroup p ↥H := hG.to_subgroup H
  have hnil : Group.IsNilpotent ↥H := hpH.isNilpotent
  have hM'index : M'.index = p := (IsPGroup.isCoatom_iff_index_eq_prime hpH).mp hM'coat
  have hM'normal : M'.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M' Group.normalizerCondition_of_isNilpotent
      hM'coat
  have hqcard : Nat.card (↥H ⧸ M') = p := by
    rw [← Subgroup.index_eq_card, hM'index]
  have hqcomm : IsMulCommutative (↥H ⧸ M') :=
    (isCyclic_of_prime_card hqcard).isMulCommutative
  have hcommLe : commutator ↥H ≤ M' :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hqcomm
  have hpowM' : ∀ a : ↥H, a ^ p ∈ M' := by
    intro a
    have h := Subgroup.pow_index_mem M' a
    rwa [hM'index] at h
  have hcommM' : ∀ a b : ↥H, ⁅a, b⁆ ∈ M' := by
    intro a b
    exact hcommLe (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
      (Subgroup.mem_top a) (Subgroup.mem_top b))
  let M : Subgroup G := M'.map H.subtype
  have hKM : K ≤ M := by
    intro k hk
    exact Subgroup.mem_map.mpr
      ⟨⟨k, hKH hk⟩, hK'M' (Subgroup.mem_subgroupOf.mpr hk), rfl⟩
  have hMH : M ≤ H := Subgroup.map_subtype_le M'
  have htopmap : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← Subgroup.subgroupOf_self (H := H)]
    exact Subgroup.map_subgroupOf_eq_of_le le_rfl
  have hneMH : M ≠ H := by
    intro h
    apply hM'coat.ne_top
    apply Subgroup.map_subtype_inj.mp
    exact h.trans htopmap.symm
  refine ⟨M, hKM, lt_of_le_of_ne hMH hneMH, ?_, ?_⟩
  · intro g hg
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩ ^ p, hpowM' ⟨g, hg⟩, by simp⟩
  · intro a ha b hb
    exact Subgroup.mem_map.mpr
      ⟨⁅(⟨a, ha⟩ : ↥H), ⟨b, hb⟩⁆, hcommM' ⟨a, ha⟩ ⟨b, hb⟩, by simp⟩

omit [Finite G] in
private theorem invCommAux_commute_of_pow_eq (hp2 : p ≠ 2)
    (hcen : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.center G)
    {a b : G} (hc : ⁅a, b⁆ ∈ Subgroup.center G) (hcp : ⁅a, b⁆ ^ p = 1) {k : ℕ}
    (hk : b ^ p = (a ^ p) ^ k) : Commute a b := by
  set c : G := ⁅a, b⁆ with hcdef
  have hc' : c ∈ Subgroup.center G := by simpa [hcdef] using hc
  have hcp' : c ^ p = 1 := by simpa [hcdef] using hcp
  have hca : Commute a ⁅a, b⁆ := by
    show a * ⁅a, b⁆ = ⁅a, b⁆ * a
    have h := Subgroup.mem_center_iff.mp hc' a
    rw [hcdef] at h
    exact h
  set u : G := a ^ k with hudef
  have huap : u ^ p = (a ^ p) ^ k := by
    rw [hudef, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hupb : u ^ p = b ^ p := huap.trans hk.symm
  have hcu : ⁅u, b⁆ = c ^ k := by
    rw [hudef, hcdef]
    exact (Commute.commutatorElement_pow_left hca k).symm
  have hck : c ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hc' k
  have hcuinv : ⁅u⁻¹, b⁆ = (c ^ k)⁻¹ := by
    have hd : ⁅u⁻¹, b⁆ = u⁻¹ * ⁅u, b⁆⁻¹ * u := by
      rw [commutatorElement_def]
      group
    rw [hd, hcu]
    have hdcent : (c ^ k)⁻¹ ∈ Subgroup.center G := Subgroup.inv_mem _ hck
    have hcomm1 : u⁻¹ * (c ^ k)⁻¹ = (c ^ k)⁻¹ * u⁻¹ :=
      Subgroup.mem_center_iff.mp hdcent u⁻¹
    rw [hcomm1, mul_assoc, inv_mul_cancel, mul_one]
  have hdcent : (c ^ k)⁻¹ ∈ Subgroup.center G := Subgroup.inv_mem _ hck
  have hcomm_b : Commute b ⁅u⁻¹, b⁆ := by
    rw [hcuinv]
    exact Subgroup.mem_center_iff.mp hdcent b
  have hcomm_u : Commute u⁻¹ ⁅u⁻¹, b⁆ := by
    rw [hcuinv]
    exact Subgroup.mem_center_iff.mp hdcent u⁻¹
  have hpow_d : (c ^ k) ^ (p.choose 2) = 1 := by
    have hp : p.Prime := Fact.out
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have hm1 : p - 1 = 2 * m := by omega
    have hdvd : p ∣ p.choose 2 := by
      rw [Nat.choose_two_right, hm1]
      have h2 : p * (2 * m) / 2 = p * m := by
        rw [show p * (2 * m) = 2 * (p * m) by ring,
          Nat.mul_div_right (p * m) (by norm_num : 0 < 2)]
      rw [h2]
      exact dvd_mul_right p m
    obtain ⟨t, ht⟩ := hdvd
    have hckp : (c ^ k) ^ p = (c ^ p) ^ k := by
      rw [← pow_mul, Nat.mul_comm k p, pow_mul]
    rw [ht, pow_mul, hckp, hcp']
    simp
  have hpow_dinv : ((c ^ k)⁻¹) ^ (p.choose 2) = 1 := by
    rw [inv_pow, hpow_d, inv_one]
  have hqpow : (b * u⁻¹) ^ p = 1 := by
    rw [Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
      (a := b) (b := u⁻¹) hcomm_b hcomm_u p, hcuinv, inv_pow, hpow_dinv, hupb,
      mul_inv_cancel, one_mul]
  have hqcen : b * u⁻¹ ∈ Subgroup.center G := hcen _ hqpow
  have hqa : Commute (b * u⁻¹) a := (Subgroup.mem_center_iff.mp hqcen a).symm
  have hb_eq : b = (b * u⁻¹) * u := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [hb_eq]
  exact (hqa.symm).mul_right ((Commute.refl a).pow_right k)

theorem commute_of_commute_commutator_of_inv (hp2 : p ≠ 2) (hG : IsPGroup p G) (t : MulAut G)
    (hcen : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.center G)
    (U : Subgroup G) (hU : Nat.card U ≤ p) (hUinv : ∀ g : G, g ^ p = 1 → t g = g⁻¹ → g ∈ U)
    {x y : G} (hx : t x = x⁻¹) (hy : t y = y⁻¹) (hxc : Commute x ⁅x, y⁆)
    (hxpy : Commute (x ^ p) y) : Commute x y := by
  have hcp : ⁅x, y⁆ ^ p = 1 := by
    rw [hxc.commutatorElement_pow_left p]
    exact commutatorElement_eq_one_iff_commute.mpr hxpy
  have hc_center : ⁅x, y⁆ ∈ Subgroup.center G := hcen _ hcp
  set Y : Subgroup G := Subgroup.closure ({x ^ p, y ^ p} : Set G) with hY
  have hxY : x ^ p ∈ Y := by
    rw [hY]
    exact Subgroup.subset_closure (by simp)
  have hyY : y ^ p ∈ Y := by
    rw [hY]
    exact Subgroup.subset_closure (by simp)
  have hpair : ({x ^ p, y ^ p} : Set G).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxpy.pow_right p
    · exact (hxpy.pow_right p).symm
    · exact Commute.refl _
  have hcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    have hYc : IsMulCommutative ↥Y := Subgroup.isMulCommutative_closure hpair
    intro a ha b hb
    exact congrArg Subtype.val (hYc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinv : ∀ g ∈ Y, t g = g⁻¹ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · rw [map_pow, hx, inv_pow]
      · rw [map_pow, hy, inv_pow]
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [map_mul, iha, ihb, mul_inv_rev]
      exact Commute.inv_inv (show Commute a b from hcomm a ha b hb)
    | inv a ha iha => rw [map_inv, iha]
  have hYcyc : IsCyclic ↥Y :=
    CFSG.RankThree.PartOne.K1214.isCyclic_of_torsion_le (Fact.out : p.Prime)
      (hG.to_subgroup Y) hcomm hU (fun g hg hgp => hUinv g hgp (hinv g hg))
  have hdich := CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC.mem_zpowers_or_mem_zpowers_of_isCyclic
    Y (hG.to_subgroup Y) (x ^ p) (y ^ p) hxY hyY
  rcases hdich with hmem | hmem
  · obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (y ^ p) (x ^ p)).mp
      (mem_powers_iff_mem_zpowers.mpr hmem)
    exact invCommAux_commute_of_pow_eq hp2 hcen hc_center hcp hk.symm
  · obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (x ^ p) (y ^ p)).mp
      (mem_powers_iff_mem_zpowers.mpr hmem)
    have hc' : ⁅y, x⁆ ∈ Subgroup.center G := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hc_center
    have hcp' : ⁅y, x⁆ ^ p = 1 := by
      rw [← commutatorElement_inv, inv_pow, hcp, inv_one]
    exact (invCommAux_commute_of_pow_eq hp2 hcen hc' hcp' hk.symm).symm

theorem commute_of_inv_of_inv_of_le (hp2 : p ≠ 2) (hG : IsPGroup p G) (t : MulAut G)
    (ht : ∀ g, t (t g) = g) (hcen : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.center G)
    (U : Subgroup G) (hU : Nat.card U ≤ p) (hUinv : ∀ g : G, g ^ p = 1 → t g = g⁻¹ → g ∈ U)
    {x y : G} (hx : t x = x⁻¹) (hy : t y = y⁻¹) (M : Subgroup G)
    (hpow : ∀ g ∈ Subgroup.closure {x, y}, g ^ p ∈ M)
    (hcomm : ∀ a ∈ Subgroup.closure {x, y}, ∀ b ∈ Subgroup.closure {x, y}, ⁅a, b⁆ ∈ M)
    (hM : ∀ g ∈ M, t g = g⁻¹ → Commute g x ∧ Commute g y) :
    Commute x y := by
  have hxp : x ^ p ∈ M := hpow x (Subgroup.subset_closure (by simp))
  have hxpi : t (x ^ p) = (x ^ p)⁻¹ := by rw [map_pow, hx, inv_pow]
  exact commute_of_commute_commutator_of_inv hp2 hG t hcen U hU hUinv hx hy
    (commute_commutator_of_inv_of_le hp2 hG t ht hcen hx hy M hpow hcomm hM) (hM _ hxp hxpi).2

theorem commute_of_inv_of_inv_step (hp2 : p ≠ 2) (hG : IsPGroup p G) (t : MulAut G)
    (ht : ∀ g, t (t g) = g) (hcen : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.center G)
    (U : Subgroup G) (hU : Nat.card U ≤ p) (hUinv : ∀ g : G, g ^ p = 1 → t g = g⁻¹ → g ∈ U)
    {x y : G} (hx : t x = x⁻¹) (hy : t y = y⁻¹)
    (ih : ∀ g h : G, t g = g⁻¹ → t h = h⁻¹ →
      Nat.card (Subgroup.closure {g, h}) < Nat.card (Subgroup.closure {x, y}) → Commute g h) :
    Commute x y := by
  set H := Subgroup.closure ({x, y} : Set G) with hH
  have hxH : Subgroup.closure {x} ≤ H := Subgroup.closure_mono (by simp)
  have hyH : Subgroup.closure {y} ≤ H := Subgroup.closure_mono (by simp)
  by_cases hx1 : Subgroup.closure {x} = H
  · have hy' : y ∈ Subgroup.zpowers x := by
      rw [Subgroup.zpowers_eq_closure, hx1]
      exact Subgroup.subset_closure (by simp)
    obtain ⟨k, rfl⟩ := hy'
    exact (Commute.refl x).zpow_right k
  by_cases hy1 : Subgroup.closure {y} = H
  · have hx' : x ∈ Subgroup.zpowers y := by
      rw [Subgroup.zpowers_eq_closure, hy1]
      exact Subgroup.subset_closure (by simp)
    obtain ⟨k, rfl⟩ := hx'
    exact ((Commute.refl y).zpow_left k)
  obtain ⟨Mx, hxMx, hMxH, hpx, hcx⟩ := exists_lt_pow_mem_commutator_mem hG hxH hx1
  obtain ⟨My, hyMy, hMyH, hpy, hcy⟩ := exists_lt_pow_mem_commutator_mem hG hyH hy1
  have hxM : x ∈ Mx := hxMx (Subgroup.mem_closure_singleton_self x)
  have hyM : y ∈ My := hyMy (Subgroup.mem_closure_singleton_self y)
  refine commute_of_inv_of_inv_of_le hp2 hG t ht hcen U hU hUinv hx hy (Mx ⊓ My)
    (fun g hg => ⟨hpx g hg, hpy g hg⟩) (fun a ha b hb => ⟨hcx a ha b hb, hcy a ha b hb⟩) ?_
  intro g hg hgi
  refine ⟨ih g x hgi hx ?_, ih g y hgi hy ?_⟩
  · refine lt_of_le_of_lt (Subgroup.card_le_of_le ?_) (Subgroup.card_lt_of_lt hMxH)
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hg.1, hxM]
  · refine lt_of_le_of_lt (Subgroup.card_le_of_le ?_) (Subgroup.card_lt_of_lt hMyH)
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hg.2, hyM]

theorem commute_of_inv_of_inv (hp2 : p ≠ 2) (hG : IsPGroup p G) (t : MulAut G)
    (ht : ∀ g, t (t g) = g) (hcen : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.center G)
    (U : Subgroup G) (hU : Nat.card U ≤ p) (hUinv : ∀ g : G, g ^ p = 1 → t g = g⁻¹ → g ∈ U)
    {x y : G} (hx : t x = x⁻¹) (hy : t y = y⁻¹) : Commute x y := by
  suffices H : ∀ n : ℕ, ∀ x y : G, t x = x⁻¹ → t y = y⁻¹ →
      Nat.card (Subgroup.closure {x, y}) = n → Commute x y from H _ x y hx hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hx hy hn
    exact commute_of_inv_of_inv_step hp2 hG t ht hcen U hU hUinv hx hy
      fun g h hg hh hlt => ih _ (hn ▸ hlt) g h hg hh rfl

theorem isCyclic_closure_inv (hp2 : p ≠ 2) (hG : IsPGroup p G) (t : MulAut G)
    (ht : ∀ g, t (t g) = g) (hcen : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.center G)
    (U : Subgroup G) (hU : Nat.card U ≤ p) (hUinv : ∀ g : G, g ^ p = 1 → t g = g⁻¹ → g ∈ U) :
    IsCyclic (Subgroup.closure {g : G | t g = g⁻¹}) := by
  set S : Set G := {g : G | t g = g⁻¹} with hS
  have hpair : S.Pairwise Commute := fun a ha b hb _ =>
    commute_of_inv_of_inv hp2 hG t ht hcen U hU hUinv ha hb
  have hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    have := Subgroup.isMulCommutative_closure hpair
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinv : ∀ g ∈ Subgroup.closure S, t g = g⁻¹ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact hg
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [map_mul, iha, ihb, mul_inv_rev]
      exact Commute.inv_inv (show Commute a b from hcomm a ha b hb)
    | inv a ha iha => rw [map_inv, iha]
  exact CFSG.RankThree.PartOne.K1214.isCyclic_of_torsion_le (Fact.out : p.Prime)
    (hG.to_subgroup _) hcomm hU fun g hg hgp => hUinv g hgp (hinv g hg)

end CFSG.GroupTheory

end
