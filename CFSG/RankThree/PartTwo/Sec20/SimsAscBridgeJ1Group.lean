module

import CFSG.LargeExtraspecial.S12TriG2
import CFSG.Sporadic.Schreier.J1Centralizer
public import CFSG.Sporadic.Schreier.J1Faithful
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.Blueprint CFSG.Sporadic.Schreier

private theorem alt5_pow_six :
    ∀ g : alternatingGroup (Fin 5), g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

private theorem pow_two_or_pow_three_of_card_sixty {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : Nat.card S = 60) {y : S} (hy : y ^ 6 = 1) :
    y ^ 2 = 1 ∨ y ^ 3 = 1 := by
  obtain ⟨f⟩ :=
    CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hS
  refine (alt5_pow_six (f y) (by rw [← map_pow, hy, map_one])).imp (fun h => ?_) (fun h => ?_) <;>
    exact f.injective (by rw [map_pow, h, map_one])

private theorem commute_of_sq_eq_one {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) : Commute a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha])
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb])
  have h : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← sq, hab])
  rw [mul_inv_rev, ha', hb'] at h
  exact h

private theorem sq_eq_one_of_pow_two_pow {G : Type*} [Group G]
    (h4 : ∀ w : G, w ^ 4 = 1 → w ^ 2 = 1) : ∀ (k : ℕ) (g : G), g ^ 2 ^ k = 1 → g ^ 2 = 1
  | 0, g, hg => by rw [pow_zero, pow_one] at hg; rw [hg, one_pow]
  | 1, g, hg => by rwa [pow_one] at hg
  | k + 2, g, hg => by
    have e4 : (g ^ 2 ^ k) ^ 4 = g ^ 2 ^ (k + 2) := by
      rw [← pow_mul]
      congr 1
      ring
    have e2 : (g ^ 2 ^ k) ^ 2 = g ^ 2 ^ (k + 1) := by rw [← pow_mul, ← pow_succ]
    exact sq_eq_one_of_pow_two_pow h4 (k + 1) g (by rw [← e2]; exact h4 _ (by rw [e4]; exact hg))

private theorem exists_simple_index_two
    {u : Equiv.Perm (Fin 3080)} (hu : u ∈ j1P)
    (ho : orderOf u = 2) :
    ∃ D : Subgroup (Equiv.Perm (Fin 3080)), IsSimpleGroup D ∧ Nat.card D = 60 ∧ u ∉ D ∧
      ∀ a ∈ centralizerIn j1P u, ∀ b ∈ centralizerIn j1P u, (a * b ∈ D ↔ (a ∈ D ↔ b ∈ D)) := by
  obtain ⟨hC, -, D, hDC, hD60, hDs, x, hx, y, hy, hxy⟩ := j1P_involution_centralizer u hu ho
  have hidx : (D.subgroupOf (centralizerIn j1P u)).index = 2 := by
    have h := Subgroup.card_mul_index (D.subgroupOf (centralizerIn j1P u))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hD60, hC] at h
    omega
  refine ⟨D, hDs, hD60, fun huD => ?_, fun a ha b hb => ?_⟩
  ·
    have hZ : (⟨u, huD⟩ : D) ∈ Subgroup.center D := Subgroup.mem_center_iff.2 fun z =>
      Subtype.ext (mem_centralizerIn.1 (hDC z.2)).2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D) with h | h
    · rw [h, Subgroup.mem_bot] at hZ
      have hu1 : u = 1 := congrArg Subtype.val hZ
      rw [hu1, orderOf_one] at ho
      omega
    · have hxZ : (⟨x, hx⟩ : D) ∈ Subgroup.center D := by
        rw [h]
        exact Subgroup.mem_top _
      exact hxy (congrArg Subtype.val (Subgroup.mem_center_iff.1 hxZ ⟨y, hy⟩)).symm
  · have h := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h
    exact h

private theorem sq_eq_one_of_pow_four
    {w : Equiv.Perm (Fin 3080)} (hw : w ∈ j1P) (h4 : w ^ 4 = 1) :
    w ^ 2 = 1 := by
  by_contra h
  have ho : orderOf (w ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact h4) h
  obtain ⟨D, -, -, huD, hmul⟩ := exists_simple_index_two (j1P.pow_mem hw 2) ho
  have hwC : w ∈ centralizerIn j1P (w ^ 2) := mem_centralizerIn.2 ⟨hw, (Commute.self_pow w 2).eq⟩
  exact huD (by rw [sq]; exact (hmul w hwC w hwC).2 Iff.rfl)

private theorem mul_pow_six_eq_one {G : Type*} [Group G] {x d : G} (hxd : Commute x d)
    (hx3 : x ^ 3 = 1) (hd2 : d ^ 2 = 1) : (x * d) ^ 6 = 1 := by
  rw [hxd.mul_pow, show (6 : ℕ) = 3 * 2 from rfl, pow_mul, pow_mul', hx3, hd2, one_pow, one_pow,
    one_mul]

private theorem false_of_commute_four
    {x u v : Equiv.Perm (Fin 3080)} (hxP : x ∈ j1P)
    (huP : u ∈ j1P) (hvP : v ∈ j1P) (hx : orderOf x = 3) (hu : orderOf u = 2) (hv2 : v ^ 2 = 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) (hcomm : Commute u v) (hxu : Commute x u) (hxv : Commute x v) :
    False := by
  obtain ⟨D, hDs, hD60, huD, hmul⟩ := exists_simple_index_two huP hu
  have huC : u ∈ centralizerIn j1P u := mem_centralizerIn.2 ⟨huP, rfl⟩
  have hxC : x ∈ centralizerIn j1P u := mem_centralizerIn.2 ⟨hxP, hxu.eq⟩
  have hvC : v ∈ centralizerIn j1P u := mem_centralizerIn.2 ⟨hvP, hcomm.eq.symm⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hxD : x ∈ D := by
    have hx2C := (centralizerIn j1P u).mul_mem hxC hxC
    have h := (hmul _ hx2C _ hx2C).2 Iff.rfl
    have hx4 : x * x * (x * x) = x := by rw [← mul_assoc, ← pow_three', hx3, one_mul]
    rwa [hx4] at h
  obtain ⟨d, hdD, hd2, hd1, hxd⟩ : ∃ d ∈ D, d ^ 2 = 1 ∧ d ≠ 1 ∧ Commute x d := by
    by_cases hvD : v ∈ D
    · exact ⟨v, hvD, hv2, hv1, hxv⟩
    · refine ⟨u * v, (hmul u huC v hvC).2 (iff_of_false huD hvD), ?_, fun h => ?_,
        hxu.mul_right hxv⟩
      · rw [hcomm.mul_pow, hu2, hv2, one_mul]
      · apply huv
        rw [eq_inv_of_mul_eq_one_left h]
        exact inv_eq_of_mul_eq_one_right (by rw [← sq, hv2])
  haveI := hDs
  have hyD : x * d ∈ D := D.mul_mem hxD hdD
  have h6 : (⟨x * d, hyD⟩ : D) ^ 6 = 1 := Subtype.ext (mul_pow_six_eq_one hxd hx3 hd2)
  rcases pow_two_or_pow_three_of_card_sixty hD60 h6 with h | h
  · have h' : (x * d) ^ 2 = 1 := congrArg Subtype.val h
    rw [hxd.mul_pow, hd2, mul_one] at h'
    have h32 := orderOf_dvd_of_pow_eq_one h'
    rw [hx] at h32
    exact absurd h32 (by norm_num)
  · have h' : (x * d) ^ 3 = 1 := congrArg Subtype.val h
    rw [hxd.mul_pow, hx3, one_mul, pow_succ, hd2, one_mul] at h'
    exact hd1 h'

theorem card_le_two_of_commute_J1
    {H : Type*} [Group H] (e : H ≃* CFSG.Blueprint.NativeSporadic.J1) {x : H} (hx : orderOf x = 3)
    {P : Subgroup H} (hP : IsPGroup 2 P) (hPx : ∀ p ∈ P, p * x = x * p) : Nat.card P ≤ 2 := by
  let φ : H →* Equiv.Perm (Fin 3080) := j1P.subtype.comp (e.trans j1PermEquiv).toMonoidHom
  have hφi : Function.Injective φ := j1P.subtype_injective.comp (e.trans j1PermEquiv).injective
  have hφP : ∀ h, φ h ∈ j1P := fun h => ((e.trans j1PermEquiv) h).2
  let ψ : P →* Equiv.Perm (Fin 3080) := φ.comp P.subtype
  have hψi : Function.Injective ψ := hφi.comp P.subtype_injective
  have hψP : ∀ q, ψ q ∈ j1P := fun q => hφP q
  have h4 : ∀ w : P, w ^ 4 = 1 → w ^ 2 = 1 := fun w hw => hψi (by
    rw [map_pow, map_one]
    exact sq_eq_one_of_pow_four (hψP w) (by rw [← map_pow, hw, map_one]))
  have hsq : ∀ q : P, q ^ 2 = 1 := fun q => by
    obtain ⟨k, hk⟩ := hP q
    exact sq_eq_one_of_pow_two_pow h4 k q hk
  by_contra hlt
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite P
  have h3 : 2 < Fintype.card P := by rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h3
  have hne : ∀ {q : P}, q ≠ a → ψ (a⁻¹ * q) ≠ 1 := fun hq h =>
    hq (inv_mul_eq_one.1 (hψi (h.trans (map_one ψ).symm))).symm
  have hxψ : ∀ q : P, Commute (φ x) (ψ q) := fun q => by
    show φ x * φ q = φ q * φ x
    rw [← map_mul, ← map_mul, hPx q q.2]
  exact false_of_commute_four (u := ψ (a⁻¹ * b)) (v := ψ (a⁻¹ * c)) (hφP x) (hψP _) (hψP _)
    (by rw [orderOf_injective φ hφi]; exact hx)
    (orderOf_eq_prime (by rw [← map_pow, hsq, map_one]) (hne (Ne.symm hab)))
    (by rw [← map_pow, hsq, map_one]) (hne (Ne.symm hac))
    (fun h => hbc (mul_left_cancel (hψi h)))
    ((commute_of_sq_eq_one (hsq _) (hsq _) (hsq _)).map ψ) (hxψ _) (hxψ _)

end CFSG.RankThree.PartTwo.Sec20
