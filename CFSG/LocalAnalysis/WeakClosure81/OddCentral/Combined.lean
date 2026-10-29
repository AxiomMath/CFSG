module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.Decomposition
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.InvertsChief
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M] [DistribMulAction G M]

theorem smul_pm_neg {g y : G} (hgy : g * y = y * g) {m : M} (hm : g • m = -m) :
    g • (m + y • m) = -(m + y • m) ∧ g • (m - y • m) = -(m - y • m) := by
  have h : g • y • m = -(y • m) := by rw [smul_smul, hgy, mul_smul, hm, smul_neg]
  constructor
  · rw [smul_add, hm, h, neg_add]
  · rw [smul_sub, hm, h, neg_sub, sub_neg_eq_add, neg_add_eq_sub]

theorem eq_zero_of_LA (hModd : Odd (Nat.card M)) {x y w : G} (hy : y * y = 1)
    (hxy : x * y = y * x) (hyw : y * w = w * y)
    (hLAy : ∀ m : M, (x * y) • m = m → x • m = m) (hLAw : ∀ m : M, (x * w) • m = m → x • m = m)
    {m : M} (hx : x • m = -m) (hm : (y * w) • m = -m) : m = 0 := by
  have hyy : ∀ v : M, y • y • v = v := fun v => by rw [smul_smul, hy, one_smul]
  have hywy : (y * w) * y = y * (y * w) := by rw [mul_assoc, ← hyw, ← mul_assoc]
  obtain ⟨hxv, hxu⟩ := smul_pm_neg (y := y) hxy hx
  obtain ⟨hywv, hywu⟩ := smul_pm_neg (y := y) hywy hm
  have hv : m + y • m = 0 := by
    set v := m + y • m with hvdef
    have hyv : y • v = v := by rw [hvdef, smul_add, hyy, add_comm]
    have hwv : w • v = -v := by
      have : w = y * (y * w) := by rw [← mul_assoc, hy, one_mul]
      rw [this, mul_smul, hywv, smul_neg, hyv]
    have hxwv : (x * w) • v = v := by rw [mul_smul, hwv, smul_neg, hxv, neg_neg]
    exact eq_zero_of_neg_eq hModd (by rw [← hxv, hLAw v hxwv])
  have hu : m - y • m = 0 := by
    set u := m - y • m with hudef
    have hyu : y • u = -u := by rw [hudef, smul_sub, hyy, neg_sub]
    have hxyu : (x * y) • u = u := by rw [mul_smul, hyu, smul_neg, hxu, neg_neg]
    exact eq_zero_of_neg_eq hModd (by rw [← hxu, hLAy u hxyu])
  have : m + m = 0 := by
    rw [show m + m = (m + y • m) + (m - y • m) by abel, hv, hu, add_zero]
  exact eq_zero_of_neg_eq hModd (neg_eq_of_add_eq_zero_right this)


theorem centralizes_of_s3_frame {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M)
    (hModd : Odd (Nat.card M))
    (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    {Q Q₀ R R₁ : Subgroup G} [hQn : Q.Normal] [hRn : R₁.Normal] (hQ₀Q : Q₀ ≤ Q)
    (hQodd : Odd (Nat.card Q)) (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Q₀)
    (hQ₀Z : Q₀ ≤ center G) (hQ₀p : IsPGroup r Q₀) (hQr : ∀ x ∈ Q, x ^ r ∈ Q₀)
    (hchief : ∀ N : Subgroup G, N.Normal → Q₀ ≤ N → N ≤ Q → N = Q₀ ∨ N = Q)
    (hRodd : Odd (Nat.card R)) (hR₁odd : Odd (Nat.card R₁))
    (hRQ : ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ Q₀)
    {d : Fin 3 → G} {t : G} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (hdn : ∀ i j, i ≠ j → d i ≠ d j) (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hcR : ∀ g : G, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ R)
    (hRc : ∀ y ∈ R, ∀ x ∈ Q, (y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹) * x *
      (y * (d 0 * d 1 * d 2) * y⁻¹ * (d 0 * d 1 * d 2)⁻¹)⁻¹ * x⁻¹ ∈ Q₀)
    (hLAW : ∀ i j, i ≠ j → ∀ x ∈ Q, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Q₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Q₀)
    (hLAM : ∀ i j, i ≠ j → ∀ m : M, (d i * d j) • m = m → d i • m = m)
    (hS1 : ∃ x ∈ Q, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ Q₀) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ = x := by
  haveI hQ₀n : Q₀.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hQ₀Z hn) g, mul_inv_cancel_right]; exact hn⟩
  obtain ⟨hcQ, hT₁, -⟩ := s3_prime (R := R) hQ₀Q hQodd hQ' hchief hRodd hd hdc hcR hRc hLAW hS1
  have hdc' : ∀ i j, Commute (d i) (d j) := hdc
  have hdinv : ∀ i, (d i)⁻¹ = d i := fun i => inv_eq_of_mul_eq_one_right (hd i)
  have hM : ∃ m : M, d 0 • m ≠ m := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hnot⟩ := hS1
    apply hnot
    rw [hfaith _ h]; simp
  have hMnt : ∃ m : M, m ≠ 0 := by
    obtain ⟨m, hm⟩ := hM
    exact ⟨m, fun h => hm (by rw [h, smul_zero])⟩
  have hLAset : ∀ a ∈ ({d 0, d 1, d 2} : Set G), ∀ b ∈ ({d 0, d 1, d 2} : Set G), a ≠ b →
      ∀ m : M, (a * b) • m = m → a • m = m := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | exact absurd rfl hab | exact hLAM _ _ (by decide)
  have hQab := comm_of_frame_action hfaith hirr hModd hQodd hQ₀Q hQ₀Z hQ' (hd 0) (hd 1) (hd 2)
    (hdc 0 1) (hdc 0 2) (hdc 1 2) (hdn 0 1 (by decide)) (hdn 0 2 (by decide))
    (hdn 1 2 (by decide)) (ht 0) (ht 1) (ht 2) hcQ hT₁ hLAset hM
  refine ⟨hQab, ?_⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = d 0 * d 1 * d 2 := ⟨_, rfl⟩
  rw [← hcdef] at hcQ
  let z : Fin 3 → G := fun a => d (a + 1) * d (a + 2)
  have hz0 : z 0 = d 1 * d 2 := rfl
  have hz1 : z 1 = d 2 * d 0 := rfl
  have hz2' : z 2 = d 0 * d 1 := rfl
  have hcd : ∀ i, Commute c (d i) := fun i => by
    rw [hcdef]; exact ((hdc' 0 i).mul_left (hdc' 1 i)).mul_left (hdc' 2 i)
  have hcomm2 : ∀ i j k l, Commute (d i * d j) (d k * d l) := fun i j k l =>
    ((hdc' i k).mul_right (hdc' i l)).mul_left ((hdc' j k).mul_right (hdc' j l))
  have hc : c * c = 1 := by
    rw [hcdef]
    exact mul_sq_eq_one (mul_sq_eq_one (hd 0) (hd 1) (hdc 0 1)) (hd 2)
      ((hdc' 0 2).mul_left (hdc' 1 2))
  have hz : ∀ a, z a * z a = 1 := fun a => mul_sq_eq_one (hd _) (hd _) (hdc _ _)
  have hz2 : z 2 = z 0 * z 1 := by
    rw [hz0, hz1, hz2', show d 1 * d 2 * (d 2 * d 0) = d 1 * (d 2 * d 2) * d 0 by group, hd 2,
      mul_one, hdc 1 0]
  have hcz : ∀ a, c * z a = z a * c := fun a => ((hcd _).mul_right (hcd _)).eq
  have h01 : z 0 * z 1 = z 1 * z 0 := (hcomm2 _ _ _ _).eq
  have hne : ∀ i j, i ≠ j → d i * d j ≠ 1 := fun i j hij h => hdn i j hij (by
    rw [← hdinv j]; exact eq_inv_of_mul_eq_one_left h)
  have hn0 : z 0 ≠ 1 := hne 1 2 (by decide)
  have hn1 : z 1 ≠ 1 := hne 2 0 (by decide)
  have hn01 : z 0 ≠ z 1 := by
    rw [hz0, hz1, hdc 2 0]
    intro h
    exact hdn 1 0 (by decide) (mul_right_cancel h)
  have htz : ∀ a, t * z a * t⁻¹ = z (a + 1) := by
    intro a
    show t * (d (a + 1) * d (a + 2)) * t⁻¹ = d (a + 1 + 1) * d (a + 1 + 2)
    rw [show t * (d (a + 1) * d (a + 2)) * t⁻¹ = (t * d (a + 1) * t⁻¹) * (t * d (a + 2) * t⁻¹)
      by group, ht, ht]
    rw [add_right_comm a 2 1]
  have htc : t * c = c * t := by
    have h : t * c * t⁻¹ = c := by
      rw [hcdef, show t * (d 0 * d 1 * d 2) * t⁻¹ =
        (t * d 0 * t⁻¹) * (t * d 1 * t⁻¹) * (t * d 2 * t⁻¹) by group, ht, ht, ht]
      show d 1 * d 2 * d 0 = d 0 * d 1 * d 2
      rw [mul_assoc, hdc 2 0, ← mul_assoc, hdc 1 0]
    calc t * c = t * c * t⁻¹ * t := by group
      _ = c * t := by rw [h]
  have hT₁' : ∀ x ∈ Q, z 0 * x * (z 0)⁻¹ * x⁻¹ ∈ Q₀ → z 1 * x * (z 1)⁻¹ * x⁻¹ ∈ Q₀ → x ∈ Q₀ :=
    hT₁
  have hLA0 : ∀ m : M, c • m = m → z 0 • m = -m → m = 0 := by
    intro m hcm hzm
    have hd0 : d 0 = c * (d 1 * d 2) := by
      rw [hcdef, show d 0 * d 1 * d 2 * (d 1 * d 2) = d 0 * d 1 * (d 2 * d 1) * d 2 by group,
        hdc 2 1, show d 0 * d 1 * (d 1 * d 2) * d 2 = d 0 * (d 1 * d 1) * (d 2 * d 2) by group,
        hd 1, hd 2, mul_one, mul_one]
    have hx : d 0 • m = -m := by rw [hd0, mul_smul, ← hz0, hzm, smul_neg, hcm]
    exact eq_zero_of_LA hModd (hd 1) (hdc 0 1) (hdc 1 2) (hLAM 0 1 (by decide))
      (hLAM 0 2 (by decide)) hx hzm
  have hLA : ∀ m : M, ∀ a, c • m = m → z a • m = -m → m = 0 := by
    have hrot : ∀ a, (∀ m : M, c • m = m → z a • m = -m → m = 0) →
        ∀ m : M, c • m = m → z (a + 1) • m = -m → m = 0 := by
      intro a ih m hcm hzm
      have h1 : c • t⁻¹ • m = t⁻¹ • m := by
        rw [smul_smul, show c * t⁻¹ = t⁻¹ * c by
          calc c * t⁻¹ = t⁻¹ * (t * c) * t⁻¹ := by group
            _ = t⁻¹ * (c * t) * t⁻¹ := by rw [htc]
            _ = t⁻¹ * c := by group, mul_smul, hcm]
      have h2 : z a • t⁻¹ • m = -(t⁻¹ • m) := by
        rw [smul_smul, show z a * t⁻¹ = t⁻¹ * z (a + 1) by rw [← htz]; group, mul_smul, hzm,
          smul_neg]
      have := ih _ h1 h2
      simpa using congrArg (t • ·) this
    intro m a
    have key : ∀ a : Fin 3, a = 0 ∨ a = 0 + 1 ∨ a = 0 + 1 + 1 := by decide
    rcases key a with rfl | rfl | rfl
    · exact hLA0 m
    · exact hrot 0 hLA0 m
    · exact hrot _ (hrot 0 hLA0) m
  exact centralizes_of_frame'' hr hrM hModd hMnt hfaith hirr hR₁odd hQodd hQab hQ₀Q hQ₀Z hQ₀p hRQ
    hQr hc hz hz2 hcz h01 hn0 hn1 hn01 hcQ hT₁' hLA htz htc

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

