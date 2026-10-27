module

public import CFSG.GroupTheory.PerfectCoverProduct
public import Mathlib.GroupTheory.Coxeter.Basic

public section

namespace CFSG

open scoped commutatorElement

theorem odd_orderOf_of_mem_of_odd_card {N : Type*} [Group N] {A : Subgroup N}
    (hodd : Odd (Nat.card A)) {x : N} (hx : x ∈ A) : Odd (orderOf x) :=
  Odd.of_dvd_nat hodd (by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _)

theorem exists_involution_lift_of_odd_card_ker {N X : Type*} [Group N] [Group X] (π : N →* X)
    (hZ : π.ker ≤ Subgroup.center N) (hodd : Odd (Nat.card π.ker)) {u : N} {y : X}
    (hu : π u = y) (hy : y ^ 2 = 1) : ∃ t : N, π t = y ∧ t ^ 2 = 1 := by
  have hu2 : u ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hu, hy]
  obtain ⟨w, hw⟩ := hodd.coprime_two_right.pow_left_bijective.surjective
    (⟨u ^ 2, hu2⟩ : π.ker)
  have hwv : (w : N) ^ 2 = u ^ 2 := congrArg Subtype.val hw
  refine ⟨u * (w : N)⁻¹, ?_, ?_⟩
  · rw [map_mul, hu, map_inv, MonoidHom.mem_ker.mp w.2, inv_one, mul_one]
  · have hc : Commute u (w : N) := Subgroup.mem_center_iff.mp (hZ w.2) u
    calc (u * (w : N)⁻¹) ^ 2 = u ^ 2 * ((w : N)⁻¹) ^ 2 := hc.inv_right.mul_pow 2
      _ = u ^ 2 * ((w : N) ^ 2)⁻¹ := by rw [inv_pow]
      _ = u ^ 2 * (u ^ 2)⁻¹ := by rw [hwv]
      _ = 1 := mul_inv_cancel _

theorem isLiftable_of_involution_lifts {B N X : Type*} [Group N] [Group X]
    {M : CoxeterMatrix B} {π : N →* X} {s : B → X} {t : B → N}
    (hZ : π.ker ≤ Subgroup.center N) (hodd : Odd (Nat.card π.ker))
    (hπt : ∀ i, π (t i) = s i) (ht : ∀ i, t i ^ 2 = 1) (hs : M.IsLiftable s) :
    M.IsLiftable t := by
  intro i j
  set m := M i j with hm
  have hmem : (t i * t j) ^ m ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hπt i, hπt j]
    simpa [hm] using hs i j
  have hcent : (t i * t j) ^ m ∈ Subgroup.center N := hZ hmem
  have hi : t i * t i = 1 := by rw [← pow_two]; exact ht i
  have hj : t j * t j = 1 := by rw [← pow_two]; exact ht j
  have hinv_i : (t i)⁻¹ = t i := inv_eq_of_mul_eq_one_right hi
  have hinv_j : (t j)⁻¹ = t j := inv_eq_of_mul_eq_one_right hj
  have hconj : t i * (t i * t j) * (t i)⁻¹ = (t i * t j)⁻¹ := by
    calc t i * (t i * t j) * (t i)⁻¹ = (t i * t i) * (t j * (t i)⁻¹) := by group
      _ = t j * (t i)⁻¹ := by rw [hi, one_mul]
      _ = t j * t i := by rw [hinv_i]
      _ = (t i * t j)⁻¹ := by rw [mul_inv_rev, hinv_j, hinv_i]
  have hz_inv : (t i * t j) ^ m = ((t i * t j) ^ m)⁻¹ := by
    have h2 : t i * (t i * t j) ^ m * (t i)⁻¹ = (t i * t j) ^ m := by
      rw [Subgroup.mem_center_iff.mp hcent (t i), mul_assoc, mul_inv_cancel, mul_one]
    calc (t i * t j) ^ m = t i * (t i * t j) ^ m * (t i)⁻¹ := h2.symm
      _ = (t i * (t i * t j) * (t i)⁻¹) ^ m := conj_pow.symm
      _ = ((t i * t j)⁻¹) ^ m := by rw [hconj]
      _ = ((t i * t j) ^ m)⁻¹ := inv_pow (t i * t j) m
  have hz2 : ((t i * t j) ^ m) ^ 2 = 1 := by
    rw [pow_two, eq_inv_iff_mul_eq_one.mp hz_inv]
  have hdvd : orderOf ((t i * t j) ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  obtain ⟨k, hk⟩ := odd_orderOf_of_mem_of_odd_card hodd hmem
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hk
    omega

theorem disjoint_ker_commutator_of_central_ker {N X : Type*} [Group N] [Group X] [Finite N]
    (π : N →* X) (hZ : π.ker ≤ Subgroup.center N)
    (L : Subgroup N) (hL : L.map π = ⊤) (hcard : Nat.card L = Nat.card X) :
    Disjoint π.ker (commutator N) := by
  classical
  have hsurjL : Function.Surjective fun l : L => π l := by
    intro x
    have hx : x ∈ L.map π := by rw [hL]; exact Subgroup.mem_top x
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨l, hl⟩, rfl⟩
  have hbij : Function.Bijective fun l : L => π l :=
    hsurjL.bijective_of_nat_card_le (by rw [hcard])
  have hdisjL : L ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx.1⟩ : L) = 1 := by
      apply hbij.1
      show π x = π ((1 : L) : N)
      simpa using (MonoidHom.mem_ker.mp hx.2)
    exact Subtype.ext_iff.mp h1
  have hsup : L ⊔ π.ker = ⊤ := by
    rw [eq_top_iff]
    intro n _
    obtain ⟨l, hl⟩ := hsurjL (π n)
    have hl' : π (l : N) = π n := hl
    have hmem : n * (l : N)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hl', mul_inv_cancel]
    have hn : n = (n * (l : N)⁻¹) * (l : N) := by group
    rw [hn]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmem) (Subgroup.mem_sup_left l.2)
  have hcommle : commutator N ≤ L := by
    change ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ ≤ L
    rw [Subgroup.commutator_le]
    intro a _ b _
    have ha' : a ∈ L ⊔ π.ker := by rw [hsup]; exact Subgroup.mem_top a
    have hb' : b ∈ L ⊔ π.ker := by rw [hsup]; exact Subgroup.mem_top b
    obtain ⟨l₁, hl₁, k₁, hk₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha'
    obtain ⟨l₂, hl₂, k₂, hk₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb'
    rw [CFSG.GroupTheory.PerfectCover.commutatorElement_mul_mul_of_mem_center (hZ hk₁) (hZ hk₂)]
    exact Subgroup.commutator_le_self L (Subgroup.commutator_mem_commutator hl₁ hl₂)
  rw [disjoint_iff]
  refine le_antisymm ?_ bot_le
  intro x hx
  have hxL : x ∈ L := hcommle hx.2
  have hxinf : x ∈ L ⊓ π.ker := ⟨hxL, hx.1⟩
  rw [hdisjL] at hxinf
  exact hxinf

theorem disjoint_ker_commutator_of_coxeter {B N X : Type*} [Group N] [Group X] [Finite N]
    (M : CoxeterMatrix B) (π : N →* X) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center N) (hodd : Odd (Nat.card π.ker)) (s : B → X)
    (hs : M.IsLiftable s) (hgen : Subgroup.closure (Set.range s) = ⊤)
    (hW : Nat.card M.Group = Nat.card X) : Disjoint π.ker (commutator N) := by
  classical
  have hXfin : Finite X := Finite.of_surjective π hπ
  choose u hu using fun i => hπ (s i)
  have hs2 : ∀ i, (s i) ^ 2 = 1 := fun i => by simpa [pow_two] using hs i i
  choose t ht htsq using fun i => exists_involution_lift_of_odd_card_ker π hZ hodd (hu i) (hs2 i)
  have hlift : M.IsLiftable t := isLiftable_of_involution_lifts hZ hodd ht htsq hs
  let φ : M.Group →* N := M.toCoxeterSystem.lift ⟨t, hlift⟩
  have hφ : ∀ i, φ (M.toCoxeterSystem.simple i) = t i := fun i =>
    CoxeterSystem.lift_apply_simple M.toCoxeterSystem hlift i
  have hle : Subgroup.closure (Set.range s) ≤ (π.comp φ).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨M.toCoxeterSystem.simple i, by rw [MonoidHom.comp_apply, hφ i, ht i]⟩
  have hmap : φ.range.map π = ⊤ := by
    rw [← MonoidHom.range_comp]
    rw [hgen] at hle
    exact top_le_iff.mp hle
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hMfin : Finite M.Group := Nat.finite_of_card_ne_zero (by rw [hW]; exact hXpos.ne')
  have hLle : Nat.card φ.range ≤ Nat.card M.Group :=
    Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hsurjL : Function.Surjective fun l : φ.range => π l := by
    intro x
    have hx : x ∈ φ.range.map π := by rw [hmap]; exact Subgroup.mem_top x
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨l, hl⟩, rfl⟩
  have hXle : Nat.card X ≤ Nat.card φ.range := Nat.card_le_card_of_surjective _ hsurjL
  have hcard : Nat.card φ.range = Nat.card X :=
    le_antisymm (by rw [← hW]; exact hLle) hXle
  exact disjoint_ker_commutator_of_central_ker π hZ φ.range hmap hcard

end CFSG

end
