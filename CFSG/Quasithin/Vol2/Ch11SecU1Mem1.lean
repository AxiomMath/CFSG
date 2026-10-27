module

public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.Quasithin.Background.E1Sec6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin

namespace Mem

variable {G : Type} [Group G]

theorem conj_eq_or_eq_inv {P : Subgroup G} {r : ℕ} (hr : r.Prime) (hP : Nat.card P = r) {y : G}
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hy2 : y ^ 2 = 1) :
    (∀ x ∈ P, y * x * y⁻¹ = x) ∨ (∀ x ∈ P, y * x * y⁻¹ = x⁻¹) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact hr.ne_zero)
  have : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  have hyg : y * (g : G) * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hy _).mp g.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, hyg⟩)
  have hk' : (g : G) ^ k = y * g * y⁻¹ := by simpa using congrArg Subtype.val hk
  have hord : orderOf (g : G) = r := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hP]
  have hconj : ∀ m : ℤ, y * (g : G) ^ m * y⁻¹ = (g : G) ^ (k * m) := fun m => by
    rw [zpow_mul, hk', conj_zpow]
  have hyy : (g : G) = (g : G) ^ (k * k) := by
    have hy1 : y * y = 1 := by rw [← sq, hy2]
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
    have h1 : y * (y * (g : G) * y⁻¹) * y⁻¹ = (g : G) := by
      rw [hyinv, show y * (y * (g : G) * y) * y = (y * y) * g * (y * y) by simp only [mul_assoc],
        hy1, one_mul, mul_one]
    rw [← hk', hconj k] at h1
    exact h1.symm
  have hdvd : (r : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one]
    rw [show (k - 1) * (k + 1) = k * k - 1 by ring, zpow_sub, zpow_one, ← hyy, mul_inv_cancel]
  rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using hr)).dvd_or_dvd hdvd with h | h
  · left
    have hgk : (g : G) ^ k = g := by
      obtain ⟨c, hc⟩ := h
      rw [show k = 1 + r * c by omega, zpow_add, zpow_one, zpow_mul, ← hord, zpow_natCast,
        pow_orderOf_eq_one, one_zpow, mul_one]
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hm' : (g : G) ^ m = x := by simpa using congrArg Subtype.val hm
    rw [← hm', hconj, zpow_mul, hgk]
  · right
    have hgk : (g : G) ^ k = (g : G)⁻¹ := by
      obtain ⟨c, hc⟩ := h
      rw [show k = -1 + r * c by omega, zpow_add, zpow_neg_one, zpow_mul, ← hord, zpow_natCast,
        pow_orderOf_eq_one, one_zpow, mul_one]
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hm' : (g : G) ^ m = x := by simpa using congrArg Subtype.val hm
    rw [← hm', hconj, zpow_mul, hgk, inv_zpow]

theorem not_le_centralizer_of_inv {P : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hP : Nat.card P = r) {y : G} (hy : ∀ x ∈ P, y * x * y⁻¹ = x⁻¹) :
    ¬ P ≤ Subgroup.centralizer {y} := by
  intro hle
  have : Fact r.Prime := ⟨hr⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact hr.ne_zero)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) r (by rw [hP])
  have hc : y * (x : G) = x * y := Subgroup.mem_centralizer_iff.mp (hle x.2) y rfl
  have h1 : (x : G) = (x : G)⁻¹ := by
    have := hy x x.2
    rwa [hc, mul_inv_cancel_right] at this
  have h2 : orderOf (x : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    rw [sq]
    nth_rewrite 2 [h1]
    exact mul_inv_cancel _)
  rw [Subgroup.orderOf_coe, hx] at h2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)

end Mem

open Mem in
theorem torusMember_holds : TorusMember := by
  intro G _ _ T A P hT hAT hA hPr hP2 hτP ⟨a₀, ha₀, ha₀P⟩
  set r := Nat.card P with hr
  have hAτ : A ≤ E1.tauOf ⊤ T A := le_sup_left.trans (E1.le_tauOf hT hAT hA)
  have hAN : A ≤ Subgroup.normalizer (P : Set G) := hAτ.trans hτP
  have hsq : ∀ y ∈ A, y ^ 2 = 1 := fun y hy => hA.2 y hy
  have hdich := fun y (hy : y ∈ A) => conj_eq_or_eq_inv hPr rfl (hAN hy) (hsq y hy)
  have hcen : ∀ y : G, (∀ x ∈ P, y * x * y⁻¹ = x) → P ≤ Subgroup.centralizer {y} :=
    fun y h x hx => Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]
      have := h x hx
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
  have hinv₀ : ∀ x ∈ P, a₀ * x * a₀⁻¹ = x⁻¹ :=
    (hdich a₀ ha₀).resolve_left fun h => ha₀P (hcen a₀ h)
  have hPp : IsPGroup r P := IsPGroup.of_card (n := 1) (by rw [pow_one])
  have hne : P ≠ ⊥ := fun h => hPr.one_lt.ne' (by rw [hr, h, Subgroup.card_bot])
  have hcomm : ⁅P, A⁆ = P := by
    have hle : ⁅P, A⁆ ≤ P := E1.commutator_le_of_le_normalizer hAN
    have hne' : ⁅P, A⁆ ≠ ⊥ := by
      intro h
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact ha₀P (fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact (Subgroup.mem_centralizer_iff.mp (h hx) a₀ ha₀))
    obtain ⟨n, hn⟩ := Subgroup.card_dvd_of_le hle
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rcases (Nat.dvd_prime hPr).mp ⟨n, hn⟩ with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hne'
    · rw [h1]
  set B := A ⊓ Subgroup.centralizer (P : Set G) with hB
  have hmemB : ∀ y ∈ A, (y ∈ B ↔ ∀ x ∈ P, y * x * y⁻¹ = x) := fun y hy => by
    refine ⟨fun h x hx => ?_, fun h => ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩⟩
    · rw [← Subgroup.mem_centralizer_iff.mp h.2 x hx, mul_inv_cancel_right]
    · have := h x hx
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  have hidx : B.relIndex A = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨a₀, ha₀⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [hmemB _ (A.mul_mem b.2 ha₀), hmemB _ b.2]
    rcases hdich b b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h => ?_⟩
      apply not_le_centralizer_of_inv hPr hP2 rfl hinv₀ (hcen a₀ fun x hx => ?_)
      have h1 := h x hx
      rw [show (b : G) * a₀ * x * ((b : G) * a₀)⁻¹ = b * (a₀ * x * a₀⁻¹) * (b : G)⁻¹ by group,
        hinv₀ x hx] at h1
      have h2 := hb x⁻¹ (P.inv_mem hx)
      rw [h2] at h1
      rw [hinv₀ x hx]
      exact h1
    · refine Or.inl ⟨fun x hx => ?_, fun h => ?_⟩
      · rw [show (b : G) * a₀ * x * ((b : G) * a₀)⁻¹ = b * (a₀ * x * a₀⁻¹) * (b : G)⁻¹ by group,
          hinv₀ x hx, hb x⁻¹ (P.inv_mem hx), inv_inv]
      · exact not_le_centralizer_of_inv hPr hP2 rfl hb (hcen b h)
  exact (E1.isE_one_sup hPr hP2 hT hAT hA hPp hne hτP hcomm inf_le_left inf_le_right
    hidx.le).1

end CFSG.Quasithin.Vol2.Ch11.SecU1
