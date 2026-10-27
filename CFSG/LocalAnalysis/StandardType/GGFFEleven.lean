module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.RankThree.PartTwo.Sec21.FF81P51
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.GGFFNine
import CFSG.LocalAnalysis.StandardType.GGFFElevenMat
import CFSG.LocalAnalysis.StandardType.GGFFElevenA
import CFSG.LocalAnalysis.StandardType.GGFFElevenB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF.Setting

open SettingCore

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)
open CFSG.RankThree.PartTwo.Sec21.FF81 (autOrder)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

theorem exists_t0_sq (h : Setting b K z)
    (hS : ∀ S : Subgroup G, S ≤ CenS (Bt b z) → IsPGroup 2 S → S = ⊥) :
    ∃ x ∈ Nor (Bt b z), x * b * x⁻¹ = b⁻¹ ∧ (∀ i, x * zs z i * x⁻¹ = zs z i) ∧ x * x = 1 := by
  obtain ⟨n, hnN, hnb, hnz⟩ := h.exists_t0
  obtain ⟨a, m, ⟨j, rfl⟩, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have h2 : ∀ k : ℕ, n ^ (2 * k) * b * (n ^ (2 * k))⁻¹ = b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_two,
        show n ^ (2 * k) * (n * n) * b * (n ^ (2 * k) * (n * n))⁻¹ =
          n ^ (2 * k) * (n * (n * b * n⁻¹) * n⁻¹) * (n ^ (2 * k))⁻¹ by group, hnb,
        show n * b⁻¹ * n⁻¹ = (n * b * n⁻¹)⁻¹ by group, hnb, inv_inv, ih]
  set x := n ^ (2 * j + 1) with hx
  have hxb : x * b * x⁻¹ = b⁻¹ := by
    rw [hx, pow_succ, show n ^ (2 * j) * n * b * (n ^ (2 * j) * n)⁻¹ =
      (n ^ (2 * j) * (n * b * n⁻¹)⁻¹ * (n ^ (2 * j))⁻¹)⁻¹ by group, hnb, inv_inv, h2]
  have hxc : ∀ i, Commute x (zs z i) := fun i => by
    refine Commute.pow_left ?_ _
    calc n * zs z i = n * zs z i * n⁻¹ * n := by group
      _ = zs z i * n := by rw [hnz i]
  have hxz : ∀ i, x * zs z i * x⁻¹ = zs z i := fun i => by
    rw [(hxc i).eq, mul_inv_cancel_right]
  have hxo : x ^ 2 ^ a = 1 := by
    rw [hx, ← pow_mul, mul_comm, ← ho, pow_orderOf_eq_one]
  have hx2C : x * x ∈ CenS (Bt b z) := by
    show x * x ∈ Subgroup.centralizer ((Bt b z : Subgroup G) : Set G)
    rw [Bt_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have e : x * x * b * (x * x)⁻¹ = b := by
      rw [show x * x * b * (x * x)⁻¹ = x * (x * b * x⁻¹) * x⁻¹ by group, hxb,
        show x * b⁻¹ * x⁻¹ = (x * b * x⁻¹)⁻¹ by group, hxb, inv_inv]
    rcases hy with rfl | rfl | rfl | rfl
    · calc y * (x * x) = x * x * y * (x * x)⁻¹ * (x * x) := by rw [e]
        _ = x * x * y := by group
    all_goals exact (((hxc _).mul_left (hxc _)).eq).symm
  have hxx : (x * x) ^ 2 ^ a = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hxo, one_pow]
  have hP : IsPGroup 2 (Subgroup.zpowers (x * x)) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hxx)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hbot := hS _ ((Subgroup.zpowers_le).mpr hx2C) hP
  refine ⟨x, (Nor _).pow_mem hnN _, hxb, hxz, ?_⟩
  have := Subgroup.mem_zpowers (x * x)
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem autOrder_ne_1440 (h : Setting b K z) (hN : ModelN K z)
    (hchar : CFSG.Open.IsCharTwoType G) : autOrder (Bt b z) ≠ 1440 := by
  intro h1440
  obtain ⟨π, x₀, r, r', hB⟩ := hN.caseB
  have hπz : ∀ i, (π : G) * zs z i * (π : G)⁻¹ = zs z (finRotate 3 i) := fun i => by
    have := congrArg Subtype.val (hB.pi_z i)
    simpa [zs] using this
  have hπN : (π : G) ∈ Nor (Bt b z) :=
    mem_nor_Bt (by rw [h.conj_b π.2]; exact b_mem_Bt b z) fun i => by
      rw [hπz]; exact zs_mem_Bt b z _
  obtain ⟨n, hnN, hn1, hn2, hn3, hnx, hnπ⟩ := h.exists_hbar h1440
  obtain ⟨hρb, hρζ, hρz, hρx⟩ := hnπ π hπN (h.conj_b π.2) hπz
  have hτN : n⁻¹ * (π : G) * n ∈ Nor (Bt b z) :=
    (Nor _).mul_mem ((Nor _).mul_mem ((Nor _).inv_mem hnN) hπN) hnN
  have hS := h.cenB_two_eq_bot hN hchar hτN hρb hρζ
  have hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K := fun c hc _ hcm =>
    h.mem_of_two hS hc hcm
  obtain ⟨x, hxN, hxb, hxz, hx2⟩ := h.exists_t0_sq hS
  obtain ⟨g, -, hgb, hgx⟩ := h.exists_e23 h1440
  by_cases hin : ∃ k ∈ K, ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹
  · obtain ⟨k, hk, hk'⟩ := hin
    exact h.not_caseA hN hmem hxb hxz hx2 hk hk' hgb (hgx x hxN hxb hxz)
  · exact h.not_caseB hN hmem hxb hxz hx2 (fun k hk hk' => hin ⟨k, hk, hk'⟩) hnN hn1 hn2 hn3
      (hnx x hxN hxb hxz) hB ⟨hρb, hρζ, hρz, hρx x hxN hxb hxz⟩

end CFSG.StandardType.GGFF.Setting

end
