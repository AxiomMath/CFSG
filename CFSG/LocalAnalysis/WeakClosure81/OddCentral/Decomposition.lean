module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.RCentralizes
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G M : Type*} [Group G] [Finite G] [AddCommGroup M] [Finite M] [DistribMulAction G M]

theorem fix_all_of_fix_two {z : Fin 3 → G} (hz2 : z 2 = z 0 * z 1) {x : G} {a b : Fin 3}
    (hab : a ≠ b) (ha : z a * x * (z a)⁻¹ = x) (hb : z b * x * (z b)⁻¹ = x) :
    z 0 * x * (z 0)⁻¹ = x ∧ z 1 * x * (z 1)⁻¹ = x := by
  have e2 : z 2 * x * (z 2)⁻¹ = z 0 * (z 1 * x * (z 1)⁻¹) * (z 0)⁻¹ := by rw [hz2]; group
  have k1 : z 0 * x * (z 0)⁻¹ = x → z 2 * x * (z 2)⁻¹ = x → z 1 * x * (z 1)⁻¹ = x := by
    intro h0 h2
    rw [h2] at e2
    calc z 1 * x * (z 1)⁻¹ = (z 0)⁻¹ * (z 0 * (z 1 * x * (z 1)⁻¹) * (z 0)⁻¹) * z 0 := by group
      _ = (z 0)⁻¹ * x * z 0 := by rw [← e2]
      _ = (z 0)⁻¹ * (z 0 * x * (z 0)⁻¹) * z 0 := by rw [h0]
      _ = x := by group
  have k0 : z 1 * x * (z 1)⁻¹ = x → z 2 * x * (z 2)⁻¹ = x → z 0 * x * (z 0)⁻¹ = x := by
    intro h1 h2
    rw [h1, h2] at e2
    exact e2.symm
  fin_cases a <;> fin_cases b <;> simp at hab ha hb ⊢
  · exact ⟨ha, hb⟩
  · exact ⟨ha, k1 ha hb⟩
  · exact ⟨hb, ha⟩
  · exact ⟨k0 ha hb, ha⟩
  · exact ⟨hb, k1 hb ha⟩
  · exact ⟨k0 hb ha, hb⟩

theorem centralizes_of_frame' {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M)
    (hModd : Odd (Nat.card M)) (hMnt : ∃ m : M, m ≠ 0)
    {R₁ Q Q₀ Z : Subgroup G} [hRn : R₁.Normal] [hQn : Q.Normal] (hR₁odd : Odd (Nat.card R₁))
    (hQodd : Odd (Nat.card Q)) (hQab : ∀ x ∈ Q, ∀ x' ∈ Q, x * x' = x' * x) (hQ₀Q : Q₀ ≤ Q)
    (hQ₀Z : Q₀ ≤ center G) (hRQ : ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ Q₀)
    (hQr : ∀ x ∈ Q, x ^ r ∈ Q₀)
    (hZQ₀ : Z ≤ Q₀) (hZr : Nat.card Z = r) (hZΩ : ∀ q ∈ Q₀, q ^ r = 1 → q ∈ Z)
    (hZM : ∀ ζ ∈ Z, ζ ≠ 1 → ∀ m : M, ζ • m = m → m = 0)
    {z : Fin 3 → G} {t c : G} (hc : c * c = 1) (hz : ∀ a, z a * z a = 1)
    (hz2 : z 2 = z 0 * z 1) (hcz : ∀ a, c * z a = z a * c) (h01 : z 0 * z 1 = z 1 * z 0)
    (hn0 : z 0 ≠ 1) (hn1 : z 1 ≠ 1) (hn01 : z 0 ≠ z 1)
    (hcQ : ∀ x ∈ Q, c * x * c⁻¹ * x ∈ Q₀)
    (hT₁ : ∀ x ∈ Q, z 0 * x * (z 0)⁻¹ * x⁻¹ ∈ Q₀ → z 1 * x * (z 1)⁻¹ * x⁻¹ ∈ Q₀ → x ∈ Q₀)
    (hLA : ∀ m : M, ∀ a, c • m = m → z a • m = -m → m = 0)
    (ht : ∀ a, t * z a * t⁻¹ = z (a + 1)) (htc : t * c = c * t) :
    ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ = x := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hcc : ∀ y, c * (c * y * c⁻¹) * c⁻¹ = y := fun y => by
    rw [hcinv]
    calc c * (c * y * c) * c = (c * c) * y * (c * c) := by group
      _ = y := by rw [hc, one_mul, mul_one]
  have hQ₀c : ∀ q ∈ Q₀, ∀ g : G, g * q * g⁻¹ = q := fun q hq g => by
    rw [Subgroup.mem_center_iff.mp (hQ₀Z hq) g, mul_inv_cancel_right]
  have hQodd' := hQodd
  obtain ⟨n, hn⟩ := hQodd'
  have hsqrt : ∀ x ∈ Q, (x ^ 2) ^ (n + 1) = x := by
    intro x hx
    have h1 : x ^ Nat.card Q = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Q hx)
    rw [← pow_mul, show 2 * (n + 1) = Nat.card Q + 1 by omega, pow_succ, h1, one_mul]
  have hfixQ₀ : ∀ x ∈ Q, c * x * c⁻¹ = x → x ∈ Q₀ := by
    intro x hx hcx
    have h := hcQ x hx
    rw [hcx] at h
    rw [← hsqrt x hx, sq]
    exact pow_mem h _
  let V : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ c * x * c⁻¹ = x⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
        rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group, ha.2, hb.2,
          mul_inv_rev]
        exact hQab _ (Q.inv_mem ha.1) _ (Q.inv_mem hb.1)⟩
      one_mem' := ⟨Q.one_mem, by simp⟩
      inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by
        rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group, ha.2]⟩ }
  have hVQ : V ≤ Q := fun x hx => hx.1
  have hVQ₀ : ∀ v ∈ V, v ∈ Q₀ → v = 1 := by
    intro v hv hv0
    have h : v = v⁻¹ := by have := hv.2; rwa [hQ₀c v hv0 c] at this
    have : v * v = 1 := by nth_rewrite 2 [h]; exact mul_inv_cancel v
    exact eq_one_of_mul_self hQodd hv.1 this
  have hQV : ∀ x ∈ Q, ∃ q ∈ Q₀, ∃ v ∈ V, x = q * v := by
    intro x hx
    have hxcQ : c * x * c⁻¹ ∈ Q := hQn.conj_mem x hx c
    have hcomm : x * (c * x * c⁻¹) = (c * x * c⁻¹) * x := hQab _ hx _ hxcQ
    have hqf : c * (x * (c * x * c⁻¹)) * c⁻¹ = x * (c * x * c⁻¹) := by
      rw [show c * (x * (c * x * c⁻¹)) * c⁻¹ = (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) by group,
        hcc, hcomm]
    have hvQ : x * (c * x * c⁻¹)⁻¹ ∈ Q := Q.mul_mem hx (Q.inv_mem hxcQ)
    have hvf : c * (x * (c * x * c⁻¹)⁻¹) * c⁻¹ = (x * (c * x * c⁻¹)⁻¹)⁻¹ := by
      rw [show c * (x * (c * x * c⁻¹)⁻¹) * c⁻¹ = (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)⁻¹ by
        group, hcc, mul_inv_rev, inv_inv]
    refine ⟨(x * (c * x * c⁻¹)) ^ (n + 1),
      pow_mem (hfixQ₀ _ (Q.mul_mem hx hxcQ) hqf) _, (x * (c * x * c⁻¹)⁻¹) ^ (n + 1),
      ⟨pow_mem hvQ _, by rw [← conj_pow, hvf, inv_pow]⟩, ?_⟩
    have hc' : Commute (x * (c * x * c⁻¹)) (x * (c * x * c⁻¹)⁻¹) :=
      hQab _ (Q.mul_mem hx hxcQ) _ hvQ
    rw [← hc'.mul_pow]
    have : x * (c * x * c⁻¹) * (x * (c * x * c⁻¹)⁻¹) = x ^ 2 := by
      rw [show x * (c * x * c⁻¹) * (x * (c * x * c⁻¹)⁻¹) =
        x * ((c * x * c⁻¹) * x) * (c * x * c⁻¹)⁻¹ by group, ← hcomm, sq]
      group
    rw [this, hsqrt x hx]
  have hVr : ∀ v ∈ V, v ^ r = 1 := fun v hv =>
    hVQ₀ _ ⟨pow_mem hv.1 r, by rw [← conj_pow, hv.2, inv_pow]⟩ (hQr v hv.1)
  have hCT : ∀ v ∈ V, z 0 * v * (z 0)⁻¹ = v → z 1 * v * (z 1)⁻¹ = v → v = 1 :=
    fun v hv h0 h1 => hVQ₀ v hv (hT₁ v hv.1 (by rw [h0, mul_inv_cancel]; exact Q₀.one_mem)
      (by rw [h1, mul_inv_cancel]; exact Q₀.one_mem))
  have hzV : ∀ a, ∀ v ∈ V, z a * v * (z a)⁻¹ ∈ V := fun a v hv => ⟨hQn.conj_mem v hv.1 _, by
    calc c * (z a * v * (z a)⁻¹) * c⁻¹ = (c * z a) * v * (c * z a)⁻¹ := by group
      _ = (z a * c) * v * (z a * c)⁻¹ := by rw [hcz a]
      _ = z a * (c * v * c⁻¹) * (z a)⁻¹ := by group
      _ = (z a * v * (z a)⁻¹)⁻¹ := by rw [hv.2]; group⟩
  let Vi : Fin 3 → Subgroup G := fun a =>
    { carrier := {v | v ∈ V ∧ z a * v * (z a)⁻¹ = v}
      mul_mem' := fun {u w} hu hw => ⟨V.mul_mem hu.1 hw.1, by
        rw [show z a * (u * w) * (z a)⁻¹ = (z a * u * (z a)⁻¹) * (z a * w * (z a)⁻¹) by group,
          hu.2, hw.2]⟩
      one_mem' := ⟨V.one_mem, by simp⟩
      inv_mem' := fun {u} hu => ⟨V.inv_mem hu.1, by
        rw [show z a * u⁻¹ * (z a)⁻¹ = (z a * u * (z a)⁻¹)⁻¹ by group, hu.2]⟩ }
  have hViV : ∀ a, Vi a ≤ V := fun a v hv => hv.1
  have c02 : z 0 * z 2 = z 2 * z 0 := by rw [hz2, mul_assoc (z 0) (z 1) (z 0), ← h01]
  have c12 : z 1 * z 2 = z 2 * z 1 := by rw [hz2, ← mul_assoc, ← h01]
  have hzc : ∀ a b, z a * z b = z b * z a := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact h01 | exact h01.symm | exact c02 | exact c02.symm | exact c12 | exact c12.symm
  have hzinv : ∀ a b, a ≠ b → ∀ v ∈ Vi b, z a * v * (z a)⁻¹ = v⁻¹ := by
    intro a b hab v hv
    have hvQ := hVQ hv.1
    have hwV : v * (z a * v * (z a)⁻¹) ∈ V := V.mul_mem hv.1 (hzV a v hv.1)
    have hwa : z a * (v * (z a * v * (z a)⁻¹)) * (z a)⁻¹ = v * (z a * v * (z a)⁻¹) := by
      rw [show z a * (v * (z a * v * (z a)⁻¹)) * (z a)⁻¹ =
        (z a * v * (z a)⁻¹) * ((z a * z a) * v * (z a * z a)⁻¹) by group, hz a, one_mul, inv_one,
        mul_one]
      exact hQab _ (hQn.conj_mem v hvQ _) _ hvQ
    have hwb : z b * (v * (z a * v * (z a)⁻¹)) * (z b)⁻¹ = v * (z a * v * (z a)⁻¹) := by
      calc z b * (v * (z a * v * (z a)⁻¹)) * (z b)⁻¹
          = (z b * v * (z b)⁻¹) * ((z b * z a) * v * (z b * z a)⁻¹) := by group
        _ = (z b * v * (z b)⁻¹) * ((z a * z b) * v * (z a * z b)⁻¹) := by rw [hzc b a]
        _ = (z b * v * (z b)⁻¹) * (z a * (z b * v * (z b)⁻¹) * (z a)⁻¹) := by group
        _ = v * (z a * v * (z a)⁻¹) := by rw [hv.2]
    have h2 := fix_all_of_fix_two hz2 hab hwa hwb
    exact eq_inv_of_mul_eq_one_right (hCT _ hwV h2.1 h2.2)
  have hVodd : Odd (Nat.card V) := Odd.of_dvd_nat hQodd (Subgroup.card_dvd_of_le hVQ)
  have hcV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => hQab x hx.1 y hy.1
  have hVgen : ∀ v ∈ V, ∃ v₀ ∈ Vi 0, ∃ v₁ ∈ Vi 1, ∃ v₂ ∈ Vi 2, v = v₀ * v₁ * v₂ := by
    refine frame_induction hVodd (hzV 0) (hzV 1) (hz 0) (hz 1) h01 hn0 hn1 hn01
      (P := fun v => ∃ v₀ ∈ Vi 0, ∃ v₁ ∈ Vi 1, ∃ v₂ ∈ Vi 2, v = v₀ * v₁ * v₂)
      ⟨1, (Vi 0).one_mem, 1, (Vi 1).one_mem, 1, (Vi 2).one_mem, by simp⟩ ?_ ?_ ?_
    · rintro _ _ ⟨a₀, h₀, a₁, h₁, a₂, h₂, rfl⟩ ⟨b₀, k₀, b₁, k₁, b₂, k₂, rfl⟩
      refine ⟨a₀ * b₀, (Vi 0).mul_mem h₀ k₀, a₁ * b₁, (Vi 1).mul_mem h₁ k₁, a₂ * b₂,
        (Vi 2).mul_mem h₂ k₂, ?_⟩
      calc a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) = a₀ * a₁ * (a₂ * b₀) * b₁ * b₂ := by group
        _ = a₀ * a₁ * (b₀ * a₂) * b₁ * b₂ := by rw [hcV _ h₂.1 _ k₀.1]
        _ = a₀ * (a₁ * b₀) * a₂ * b₁ * b₂ := by group
        _ = a₀ * (b₀ * a₁) * a₂ * b₁ * b₂ := by rw [hcV _ h₁.1 _ k₀.1]
        _ = a₀ * b₀ * a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₀ * b₀ * a₁ * (b₁ * a₂) * b₂ := by rw [hcV _ h₂.1 _ k₁.1]
        _ = a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) := by group
    · rintro _ ⟨a₀, h₀, a₁, h₁, a₂, h₂, rfl⟩
      refine ⟨a₀⁻¹, (Vi 0).inv_mem h₀, a₁⁻¹, (Vi 1).inv_mem h₁, a₂⁻¹, (Vi 2).inv_mem h₂, ?_⟩
      have i0 := (Vi 0).inv_mem h₀
      have i1 := (Vi 1).inv_mem h₁
      have i2 := (Vi 2).inv_mem h₂
      calc (a₀ * a₁ * a₂)⁻¹ = a₂⁻¹ * a₁⁻¹ * a₀⁻¹ := by group
        _ = a₂⁻¹ * (a₀⁻¹ * a₁⁻¹) := by rw [mul_assoc, hcV _ i1.1 _ i0.1]
        _ = (a₀⁻¹ * a₁⁻¹) * a₂⁻¹ := hcV _ i2.1 _ (V.mul_mem i0.1 i1.1)
    · intro h hh hfix
      rcases hfix with h0 | h1 | h2
      · exact ⟨h, ⟨hh, h0⟩, 1, (Vi 1).one_mem, 1, (Vi 2).one_mem, by simp⟩
      · exact ⟨1, (Vi 0).one_mem, h, ⟨hh, h1⟩, 1, (Vi 2).one_mem, by simp⟩
      · exact ⟨1, (Vi 0).one_mem, 1, (Vi 1).one_mem, h, ⟨hh, by rw [hz2]; exact h2⟩, by simp⟩
  have htV : ∀ a v, v ∈ Vi a ↔ t * v * t⁻¹ ∈ Vi (a + 1) := by
    intro a v
    have hza : z a = t⁻¹ * z (a + 1) * t := by rw [← ht a]; group
    have htc' : t⁻¹ * c = c * t⁻¹ := by
      calc t⁻¹ * c = t⁻¹ * (c * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * c) * t⁻¹ := by rw [htc]
        _ = c * t⁻¹ := by group
    constructor
    · rintro ⟨⟨hvQ, hcv⟩, hzv⟩
      refine ⟨⟨hQn.conj_mem v hvQ t, ?_⟩, ?_⟩
      · calc c * (t * v * t⁻¹) * c⁻¹ = (c * t) * v * (c * t)⁻¹ := by group
          _ = (t * c) * v * (t * c)⁻¹ := by rw [htc]
          _ = t * (c * v * c⁻¹) * t⁻¹ := by group
          _ = (t * v * t⁻¹)⁻¹ := by rw [hcv]; group
      · rw [← ht a]
        calc t * z a * t⁻¹ * (t * v * t⁻¹) * (t * z a * t⁻¹)⁻¹
            = t * (z a * v * (z a)⁻¹) * t⁻¹ := by group
          _ = t * v * t⁻¹ := by rw [hzv]
    · rintro ⟨⟨hwQ, hcw⟩, hzw⟩
      have hv : v = t⁻¹ * (t * v * t⁻¹) * t := by group
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hv]; simpa using hQn.conj_mem _ hwQ t⁻¹
      · calc c * v * c⁻¹ = c * (t⁻¹ * (t * v * t⁻¹) * t) * c⁻¹ := by rw [← hv]
          _ = (c * t⁻¹) * (t * v * t⁻¹) * (c * t⁻¹)⁻¹ := by group
          _ = (t⁻¹ * c) * (t * v * t⁻¹) * (t⁻¹ * c)⁻¹ := by rw [htc']
          _ = t⁻¹ * (c * (t * v * t⁻¹) * c⁻¹) * t := by group
          _ = v⁻¹ := by rw [hcw]; group
      · calc z a * v * (z a)⁻¹
            = t⁻¹ * (z (a + 1) * (t * v * t⁻¹) * (z (a + 1))⁻¹) * t := by rw [hza]; group
          _ = v := by rw [hzw]; group
  exact centralizes_of_frame hr hrM hModd hMnt (R₁ := R₁) (Q := Q) (Q₀ := Q₀) (V := V) (Z := Z)
    hR₁odd hQodd hQab hQ₀Q hQ₀Z hRQ hQV hVQ hVr hZQ₀ hZr hZΩ hZM hViV hVgen hc hz hz2 hcz h01
    hn0 hn1 hn01 (fun v hv => hv.2) hzV hzinv hLA ht htV

theorem eq_zero_of_central (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    {ζ : G} (hζ : ζ ∈ center G) (hζ1 : ζ ≠ 1) {m : M} (hm : ζ • m = m) : m = 0 := by
  let N : AddSubgroup M :=
    { carrier := {m | ζ • m = m}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [smul_add, ha, hb]
      zero_mem' := smul_zero ζ
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢; rw [smul_neg, ha] }
  have hinv : ∀ g : G, ∀ m ∈ N, g • m ∈ N := by
    intro g m hm'
    show ζ • g • m = g • m
    rw [smul_smul, ← Subgroup.mem_center_iff.mp hζ g, mul_smul]
    exact congrArg (g • ·) hm'
  rcases hirr N hinv with h | h
  · have : m ∈ N := hm
    rw [h] at this
    exact (AddSubgroup.mem_bot).mp this
  · exact absurd (hfaith ζ fun m' => by
      have : m' ∈ N := by rw [h]; exact AddSubgroup.mem_top m'
      exact this) hζ1

theorem exists_omega {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M) (hMnt : ∃ m : M, m ≠ 0)
    (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    {Q₀ : Subgroup G} (hQ₀Z : Q₀ ≤ center G) (hQ₀p : IsPGroup r Q₀) (hQ₀1 : Q₀ ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≤ Q₀ ∧ Nat.card Z = r ∧ (∀ q ∈ Q₀, q ^ r = 1 → q ∈ Z) ∧
      ∀ ζ ∈ Z, ζ ≠ 1 → ∀ m : M, ζ • m = m → m = 0 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hcomm : ∀ a ∈ Q₀, ∀ b : G, Commute b a := fun a ha b =>
    Subgroup.mem_center_iff.mp (hQ₀Z ha) b
  let Z : Subgroup G :=
    { carrier := {q | q ∈ Q₀ ∧ q ^ r = 1}
      mul_mem' := fun {a b} ha hb => ⟨Q₀.mul_mem ha.1 hb.1, by
        rw [((hcomm b hb.1 a)).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨Q₀.one_mem, one_pow r⟩
      inv_mem' := fun {a} ha => ⟨Q₀.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hZM : ∀ ζ ∈ Z, ζ ≠ 1 → ∀ m : M, ζ • m = m → m = 0 := fun ζ hζ hζ1 m hm =>
    eq_zero_of_central hfaith hirr (hQ₀Z hζ.1) hζ1 hm
  refine ⟨Z, fun q hq => hq.1, ?_, fun q hq hqr => ⟨hq, hqr⟩, hZM⟩
  letI iC : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun a b => Subtype.ext (hcomm b b.2.1 a).eq }
  haveI : CFSG.IsElementaryAbelian r Z :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hcomm b b.2.1 a).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using g.2.2) }
  haveI : Nontrivial Q₀ := (Subgroup.nontrivial_iff_ne_bot Q₀).mpr hQ₀1
  have hdvd : r ∣ Nat.card Q₀ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ₀p
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
    rw [hk]; exact dvd_pow_self r hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q₀) r hdvd
  have hxZ : (x : G) ∈ Z := ⟨x.2, by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this⟩
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact hr.one_lt.ne hx
  haveI : Nontrivial Z := ⟨⟨⟨x, hxZ⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  let α : Z →* MulAut (Multiplicative M) :=
    { toFun := fun a =>
        { toFun := fun x => Multiplicative.ofAdd ((a : G) • x.toAdd)
          invFun := fun x => Multiplicative.ofAdd ((a : G)⁻¹ • x.toAdd)
          left_inv := fun x => by simp
          right_inv := fun x => by simp
          map_mul' := fun x x' => by simp [smul_add] }
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp [mul_smul] }
  have hgen := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top r hr α
    (by rwa [show Nat.card (Multiplicative M) = Nat.card M from
      Nat.card_congr Multiplicative.toAdd])
  obtain ⟨m₀, hm₀⟩ := hMnt
  have hex : ∃ B : Subgroup Z, B.index = r ∧
      ∃ x ∈ CFSG.SolvableSignalizer.fixedBySubgroup α B, x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hle : (⨆ (B : Subgroup Z) (_ : B.index = r),
        CFSG.SolvableSignalizer.fixedBySubgroup α B) ≤ ⊥ :=
      iSup₂_le fun B hB x hx => (Subgroup.mem_bot).mpr (hcon B hB x hx)
    rw [hgen] at hle
    have := hle (Subgroup.mem_top (Multiplicative.ofAdd m₀))
    rw [Subgroup.mem_bot] at this
    exact hm₀ (by simpa using congrArg Multiplicative.toAdd this)
  obtain ⟨B, hB, y, hy, hy1⟩ := hex
  have hyfix : ∀ b ∈ B, (b : G) • y.toAdd = y.toAdd := fun b hb =>
    congrArg Multiplicative.toAdd
      ((CFSG.SolvableSignalizer.mem_fixedBySubgroup α B y).mp hy b hb)
  have hyne : y.toAdd ≠ 0 := fun h => hy1 (by simpa using congrArg Multiplicative.ofAdd h)
  have hBbot : B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    by_contra hb1
    exact hyne (hZM b b.2 (fun h => hb1 (Subtype.ext h)) _ (hyfix b hb))
  rw [hBbot, Subgroup.index_bot] at hB
  exact hB

theorem centralizes_of_frame'' {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ Nat.card M)
    (hModd : Odd (Nat.card M)) (hMnt : ∃ m : M, m ≠ 0)
    (hfaith : ∀ g : G, (∀ m : M, g • m = m) → g = 1)
    (hirr : ∀ N : AddSubgroup M, (∀ g : G, ∀ m ∈ N, g • m ∈ N) → N = ⊥ ∨ N = ⊤)
    {R₁ Q Q₀ : Subgroup G} [hRn : R₁.Normal] [hQn : Q.Normal] (hR₁odd : Odd (Nat.card R₁))
    (hQodd : Odd (Nat.card Q)) (hQab : ∀ x ∈ Q, ∀ x' ∈ Q, x * x' = x' * x) (hQ₀Q : Q₀ ≤ Q)
    (hQ₀Z : Q₀ ≤ center G) (hQ₀p : IsPGroup r Q₀)
    (hRQ : ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ * x⁻¹ ∈ Q₀) (hQr : ∀ x ∈ Q, x ^ r ∈ Q₀)
    {z : Fin 3 → G} {t c : G} (hc : c * c = 1) (hz : ∀ a, z a * z a = 1)
    (hz2 : z 2 = z 0 * z 1) (hcz : ∀ a, c * z a = z a * c) (h01 : z 0 * z 1 = z 1 * z 0)
    (hn0 : z 0 ≠ 1) (hn1 : z 1 ≠ 1) (hn01 : z 0 ≠ z 1)
    (hcQ : ∀ x ∈ Q, c * x * c⁻¹ * x ∈ Q₀)
    (hT₁ : ∀ x ∈ Q, z 0 * x * (z 0)⁻¹ * x⁻¹ ∈ Q₀ → z 1 * x * (z 1)⁻¹ * x⁻¹ ∈ Q₀ → x ∈ Q₀)
    (hLA : ∀ m : M, ∀ a, c • m = m → z a • m = -m → m = 0)
    (ht : ∀ a, t * z a * t⁻¹ = z (a + 1)) (htc : t * c = c * t) :
    ∀ y ∈ R₁, ∀ x ∈ Q, y * x * y⁻¹ = x := by
  by_cases hQ₀1 : Q₀ = ⊥
  · intro y hy x hx
    have h := hRQ y hy x hx
    rw [hQ₀1, Subgroup.mem_bot] at h
    exact mul_inv_eq_one.mp h
  obtain ⟨Z, hZQ₀, hZr, hZΩ, hZM⟩ := exists_omega hr hrM hMnt hfaith hirr hQ₀Z hQ₀p hQ₀1
  exact centralizes_of_frame' hr hrM hModd hMnt hR₁odd hQodd hQab hQ₀Q hQ₀Z hRQ hQr hZQ₀ hZr hZΩ
    hZM hc hz hz2 hcz h01 hn0 hn1 hn01 hcQ hT₁ hLA ht htc

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

