module

public import Mathlib.GroupTheory.SchurZassenhaus
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def PSylowIn (p : ℕ) (Y : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ Y → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ p = 1) → P ≠ ⊥ →
    P ⊓ Subgroup.centralizer (Y : Set G) = ⊥ →
    ∃ S : Subgroup G, S ≤ Y ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ P ≤ Subgroup.normalizer (S : Set G) ∧
      S = ⁅S, P⁆

theorem exists_complement_of_inner [Finite G] {p : ℕ} (hp : p.Prime) {E Y : Subgroup G}
    (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEpow : ∀ x ∈ E, x ^ p = 1)
    (hinn : ∀ e ∈ E, ∃ x ∈ Y, ∃ y ∈ Subgroup.centralizer (Y : Set G), e = x * y)
    (hZ : ¬ p ∣ Nat.card ↥(Y ⊓ Subgroup.centralizer (Y : Set G))) :
    ∃ P : Subgroup G, P ≤ Y ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ (∀ x ∈ P, x ^ p = 1) ∧
      P ⊓ Subgroup.centralizer (Y : Set G) = ⊥ ∧
      (∀ e ∈ E, ∃ x ∈ P, ∃ y ∈ Subgroup.centralizer (Y : Set G), e = x * y) ∧
      (∀ x ∈ P, ∃ y ∈ Subgroup.centralizer (Y : Set G), x * y ∈ E) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := Subgroup.centralizer (Y : Set G) with hC
  have hCmem : ∀ y ∈ C, ∀ w ∈ Y, w * y = y * w := fun y hy w hw =>
    Subgroup.mem_centralizer_iff.1 hy w hw
  let M : Subgroup G :=
    { carrier := {x | x ∈ Y ∧ ∃ y ∈ C, x * y ∈ E}
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haY, ya, hya, hae⟩ ⟨hbY, yb, hyb, hbe⟩
        refine ⟨mul_mem haY hbY, ya * yb, mul_mem hya hyb, ?_⟩
        have : a * b * (ya * yb) = (a * ya) * (b * yb) := by
          calc a * b * (ya * yb) = a * (b * ya) * yb := by group
            _ = a * (ya * b) * yb := by rw [hCmem ya hya b hbY]
            _ = (a * ya) * (b * yb) := by group
        rw [this]
        exact mul_mem hae hbe
      inv_mem' := by
        rintro a ⟨haY, ya, hya, hae⟩
        refine ⟨inv_mem haY, ya⁻¹, inv_mem hya, ?_⟩
        have : a⁻¹ * ya⁻¹ = (a * ya)⁻¹ := by
          calc a⁻¹ * ya⁻¹ = (ya * a)⁻¹ := by group
            _ = (a * ya)⁻¹ := by rw [hCmem ya hya a haY]
        rw [this]
        exact inv_mem hae }
  have hMmem : ∀ x ∈ M, x ∈ Y ∧ ∃ y ∈ C, x * y ∈ E := fun x hx => hx
  have hMY : M ≤ Y := fun x hx => hx.1
  set Z : Subgroup G := Y ⊓ C with hZdef
  have hZM : Z ≤ M := by
    intro z hz
    exact ⟨hz.1, z⁻¹, inv_mem hz.2, by simp⟩
  have hZcomm : ∀ z ∈ Z, ∀ w ∈ Y, z * w = w * z := fun z hz w hw => (hCmem z hz.2 w hw).symm
  have hpowM : ∀ x ∈ M, x ^ p ∈ Z := by
    intro x hx
    obtain ⟨hxY, y, hy, he⟩ := hMmem x hx
    have hcomm : Commute x y := hCmem y hy x hxY
    have h1 : (x * y) ^ p = x ^ p * y ^ p := hcomm.mul_pow p
    have h2 : x ^ p = (y ^ p)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← h1, hEpow _ he])
    exact Subgroup.mem_inf.2 ⟨pow_mem hxY p, by rw [h2]; exact inv_mem (pow_mem hy p)⟩
  have hcommM : ∀ x₁ ∈ M, ∀ x₂ ∈ M, x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ Z := by
    have key : ∀ x₁ ∈ M, ∀ x₂ ∈ M, x₁⁻¹ * x₂⁻¹ * x₁ * x₂ ∈ Z := by
      intro x₁ h₁ x₂ h₂
      obtain ⟨hx₁Y, y₁, hy₁, he₁⟩ := hMmem x₁ h₁
      obtain ⟨hx₂Y, y₂, hy₂, he₂⟩ := hMmem x₂ h₂
      have heq : x₁ * x₂ * (y₁ * y₂) = x₂ * x₁ * (y₂ * y₁) := by
        calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
          _ = x₁ * (y₁ * x₂) * y₂ := by rw [hCmem y₁ hy₁ x₂ hx₂Y]
          _ = (x₁ * y₁) * (x₂ * y₂) := by group
          _ = (x₂ * y₂) * (x₁ * y₁) := hEcomm _ he₁ _ he₂
          _ = x₂ * (y₂ * x₁) * y₁ := by group
          _ = x₂ * (x₁ * y₂) * y₁ := by rw [← hCmem y₂ hy₂ x₁ hx₁Y]
          _ = x₂ * x₁ * (y₂ * y₁) := by group
      have hcC : x₁⁻¹ * x₂⁻¹ * x₁ * x₂ ∈ C := by
        have h3 : x₁ * x₂ = x₂ * x₁ * (y₂ * y₁) * (y₁ * y₂)⁻¹ := by
          calc x₁ * x₂ = x₁ * x₂ * (y₁ * y₂) * (y₁ * y₂)⁻¹ := by group
            _ = x₂ * x₁ * (y₂ * y₁) * (y₁ * y₂)⁻¹ := by rw [heq]
        have : x₁⁻¹ * x₂⁻¹ * x₁ * x₂ = y₂ * y₁ * (y₁ * y₂)⁻¹ := by
          calc x₁⁻¹ * x₂⁻¹ * x₁ * x₂ = (x₂ * x₁)⁻¹ * (x₁ * x₂) := by group
            _ = (x₂ * x₁)⁻¹ * (x₂ * x₁ * (y₂ * y₁) * (y₁ * y₂)⁻¹) :=
                congrArg (fun t => (x₂ * x₁)⁻¹ * t) h3
            _ = y₂ * y₁ * (y₁ * y₂)⁻¹ := by group
        rw [this]
        exact mul_mem (mul_mem hy₂ hy₁) (inv_mem (mul_mem hy₁ hy₂))
      exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (mul_mem (inv_mem hx₁Y) (inv_mem hx₂Y)) hx₁Y) hx₂Y,
        hcC⟩
    intro x₁ h₁ x₂ h₂
    have := key x₁⁻¹ (inv_mem h₁) x₂⁻¹ (inv_mem h₂)
    simpa using this
  let N : Subgroup M := Z.subgroupOf M
  have hNnormal : N.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZM]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hcomm : ∀ z ∈ Z, m * z * m⁻¹ = z := fun z hz => by
      have := hZcomm z hz m (hMY hm)
      calc m * z * m⁻¹ = (m * z) * m⁻¹ := rfl
        _ = (z * m) * m⁻¹ := by rw [← this]
        _ = z := by group
    constructor
    · intro hh
      rw [hcomm h hh]
      exact hh
    · intro hh
      have hc : (m * h * m⁻¹) * m = m * (m * h * m⁻¹) := hZcomm _ hh m (hMY hm)
      have : m * h * m⁻¹ = h := by
        calc m * h * m⁻¹ = m⁻¹ * (m * (m * h * m⁻¹)) := by group
          _ = m⁻¹ * ((m * h * m⁻¹) * m) := by rw [hc]
          _ = h := by group
      rw [← this]
      exact hh
  have hpgroup : IsPGroup p (M ⧸ N) := by
    intro g
    refine ⟨1, ?_⟩
    induction g using QuotientGroup.induction_on with
    | H x =>
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 (hpowM x x.2)
  obtain ⟨n, hn⟩ := hpgroup.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    have h1 : Nat.card N = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv
    have h2 : N.index = p ^ n := hn
    rw [h1, h2]
    exact Nat.Coprime.pow_right n (((Nat.Prime.coprime_iff_not_dvd hp).2 hZ).symm)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hdisj : Disjoint N H := hH.disjoint
  have hcodisj : N ⊔ H = ⊤ := hH.sup_eq_top
  have hPM : ∀ x ∈ H.map M.subtype, x ∈ M := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hPZ : ∀ x ∈ H.map M.subtype, x ∈ Z → x = 1 := by
    rintro _ ⟨h, hh, rfl⟩ hZx
    have hN : h ∈ N := Subgroup.mem_subgroupOf.2 hZx
    have := (Subgroup.disjoint_def.1 hdisj) hN hh
    rw [this]
    rfl
  refine ⟨H.map M.subtype, fun x hx => hMY (hPM x hx), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have hc := hcommM x (hPM x hx) y (hPM y hy)
    have hcP : x * y * x⁻¹ * y⁻¹ ∈ H.map M.subtype :=
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    have h1 := hPZ _ hcP hc
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  · intro x hx
    exact hPZ _ (pow_mem hx p) (hpowM x (hPM x hx))
  · rw [eq_bot_iff]
    intro x hx
    have hxP : x ∈ H.map M.subtype := hx.1
    have hxZ : x ∈ Z := Subgroup.mem_inf.2 ⟨hMY (hPM x hxP), hx.2⟩
    rw [Subgroup.mem_bot]
    exact hPZ x hxP hxZ
  · intro e he
    obtain ⟨x, hxY, y, hy, rfl⟩ := hinn e he
    have hxM : x ∈ M := ⟨hxY, y, hy, he⟩
    have hmem : (⟨x, hxM⟩ : M) ∈ N ⊔ H := by rw [hcodisj]; trivial
    obtain ⟨n, hn, h, hh, hnh⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun k hk l _ => by
        apply Subtype.ext
        exact hZcomm (k : G) (Subgroup.mem_subgroupOf.1 hk) (l : G) (hMY l.2)) hmem
    have hx : x = (n : G) * (h : G) := congrArg Subtype.val hnh
    have hnZ : (n : G) ∈ Z := Subgroup.mem_subgroupOf.1 hn
    refine ⟨(h : G), ⟨h, hh, rfl⟩, (n : G) * y, mul_mem hnZ.2 hy, ?_⟩
    rw [hx]
    calc (n : G) * (h : G) * y = (h : G) * (n : G) * y := by rw [hZcomm n hnZ h (hMY h.2)]
      _ = (h : G) * ((n : G) * y) := by group
  · rintro x hx
    exact (hMmem x (hPM x hx)).2

end CFSG.RankThree.PartOne.S15K
