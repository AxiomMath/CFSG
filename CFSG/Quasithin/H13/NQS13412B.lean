module

public import CFSG.Quasithin.H13.NQS13412A
public import CFSG.Quasithin.H13.NQS13410P

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem chief_of_action {X K W : Subgroup G} [IsMulCommutative ↥W] {Γ : Type} [Group Γ]
    (ρ : ↥(normalizer (W : Set G)) →* Γ) {P E : Subgroup Γ} (hXK : X ≤ K)
    (hKW : K ≤ normalizer (W : Set G)) (hWX : W ≤ normalizer (X : Set G))
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hKC : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)))
    (hρker : ∀ g : ↥(normalizer (W : Set G)), ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G))
    (hρP : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ X → ρ g ∈ P)
    (hE : ∀ γ ∈ P, ∀ e ∈ E, γ * e * γ⁻¹ ∈ E) (hE2 : ∀ e ∈ E, e * e = 1)
    {k₁ k₂ : G} (hk₁ : k₁ ∈ X) (hk₂ : k₂ ∈ X) {m₁ : ℕ} (hm₁ : Odd m₁) (hk₁m : k₁ ^ m₁ = 1)
    (hEc : ρ ⟨k₁, hKW (hXK hk₁)⟩ * ρ ⟨k₂, hKW (hXK hk₂)⟩ * (ρ ⟨k₁, hKW (hXK hk₁)⟩)⁻¹ *
      (ρ ⟨k₂, hKW (hXK hk₂)⟩)⁻¹ ∈ E)
    (hnc : ρ ⟨k₁, hKW (hXK hk₁)⟩ * (ρ ⟨k₁, hKW (hXK hk₁)⟩ * ρ ⟨k₂, hKW (hXK hk₂)⟩ *
      (ρ ⟨k₁, hKW (hXK hk₁)⟩)⁻¹ * (ρ ⟨k₂, hKW (hXK hk₂)⟩)⁻¹) * (ρ ⟨k₁, hKW (hXK hk₁)⟩)⁻¹ *
      (ρ ⟨k₁, hKW (hXK hk₁)⟩ * ρ ⟨k₂, hKW (hXK hk₂)⟩ * (ρ ⟨k₁, hKW (hXK hk₁)⟩)⁻¹ *
        (ρ ⟨k₂, hKW (hXK hk₂)⟩)⁻¹)⁻¹ ≠ 1) :
    HasTwoNoncentralChiefFactors X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXW : X ≤ normalizer (W : Set G) := hXK.trans hKW
  set n₁ : ↥(normalizer (W : Set G)) := ⟨k₁, hXW hk₁⟩ with hn₁
  set n₂ : ↥(normalizer (W : Set G)) := ⟨k₂, hXW hk₂⟩ with hn₂
  have hk₁W : k₁ ∉ centralizer (W : Set G) := fun h => by
    have h1 : ρ n₁ = 1 := (hρker n₁).2 h
    apply hnc
    rw [h1]
    group
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥W) ⟨b, hb⟩)
  have hlow : ∃ A₁ B₁ : Subgroup G, ⊥ ≤ B₁ ∧ A₁ ≤ W ⊓ X ∧ IsChiefFactorOf X A₁ B₁ ∧
      ¬ ⁅A₁, X⁆ ≤ B₁ := by
    obtain ⟨w, hw, hwk⟩ : ∃ w ∈ W, w * k₁ ≠ k₁ * w := by
      by_contra hno
      push Not at hno
      exact hk₁W (mem_centralizer_iff.2 fun w hw => hno w hw)
    set u := w⁻¹ * (k₁ * w * k₁⁻¹) with hu
    have hkw : k₁ * w * k₁⁻¹ ∈ W := (mem_normalizer_iff.mp (hXW hk₁) w).mp hw
    have huW : u ∈ W := mul_mem (inv_mem hw) hkw
    have huX : u ∈ X := by
      have h1 : w⁻¹ * k₁ * w ∈ X := by
        have := (mem_normalizer_iff.mp (hWX (inv_mem hw)) k₁).mp hk₁
        simpa using this
      have e : u = (w⁻¹ * k₁ * w) * k₁⁻¹ := by rw [hu]; group
      rw [e]
      exact mul_mem h1 (inv_mem hk₁)
    have hku : k₁ * u * k₁⁻¹ * u⁻¹ ∉ (⊥ : Subgroup G) := by
      intro h
      rw [mem_bot] at h
      have hku' : k₁ * u * k₁⁻¹ = u := by
        calc k₁ * u * k₁⁻¹ = k₁ * u * k₁⁻¹ * u⁻¹ * u := by group
          _ = u := by rw [h, one_mul]
      have hk2 : k₁ ^ 2 * w * (k₁ ^ 2)⁻¹ = w := by
        have e1 : k₁ * w * k₁⁻¹ = w * u := by rw [hu]; group
        calc k₁ ^ 2 * w * (k₁ ^ 2)⁻¹ = k₁ * (k₁ * w * k₁⁻¹) * k₁⁻¹ := by rw [pow_two]; group
          _ = k₁ * (w * u) * k₁⁻¹ := by rw [e1]
          _ = (k₁ * w * k₁⁻¹) * (k₁ * u * k₁⁻¹) := by group
          _ = w * u * u := by rw [e1, hku']
          _ = w := by
            rw [mul_assoc, ← pow_two, hW2 u huW, mul_one]
      obtain ⟨j, rfl⟩ := hm₁
      have hk : k₁ = (k₁ ^ 2) ^ (j + 1) := by
        rw [← pow_mul, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, hk₁m, one_mul]
      have hk2' : ∀ i : ℕ, (k₁ ^ 2) ^ i * w * ((k₁ ^ 2) ^ i)⁻¹ = w := by
        intro i
        induction i with
        | zero => simp
        | succ i ih =>
          calc (k₁ ^ 2) ^ (i + 1) * w * ((k₁ ^ 2) ^ (i + 1))⁻¹ =
              (k₁ ^ 2) ^ i * (k₁ ^ 2 * w * (k₁ ^ 2)⁻¹) * ((k₁ ^ 2) ^ i)⁻¹ := by group
            _ = w := by rw [hk2, ih]
      apply hwk
      have h1 := hk2' (j + 1)
      rw [← hk] at h1
      calc w * k₁ = k₁ * w * k₁⁻¹ * k₁ := by rw [h1]
        _ = k₁ * w := by group
    have hWX2 : IsPGroup 2 ↥(W ⊓ X) := fun x => ⟨1, Subtype.ext (by
      have := hW2 x (mem_inf.1 x.2).1
      simpa using this)⟩
    have hXWX : X ≤ normalizer ((W ⊓ X : Subgroup G) : Set G) := fun g hg =>
      inf_normalizer_le_normalizer_inf ⟨hXW hg, le_normalizer hg⟩
    have hXbot : X ≤ normalizer ((⊥ : Subgroup G) : Set G) := fun g _ => by
      rw [mem_normalizer_iff]
      intro h
      simp only [mem_bot]
      constructor
      · rintro rfl; group
      · intro h1
        have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [this, h1]; group
    obtain ⟨A₁, B₁, hB₁, hA₁, h1, h2⟩ := exists_noncentral_chief hk₁ hm₁ hk₁m _ (W ⊓ X) ⊥ le_rfl
      hWX2 inf_le_right bot_le hXWX hXbot ⟨u, mem_inf.2 ⟨huW, huX⟩, hku⟩
    exact ⟨A₁, B₁, hB₁, hA₁, h1, h2⟩
  obtain ⟨A₁, B₁, -, hA₁, hch1, hnc1⟩ := hlow
  set A := (E.comap ρ).map (normalizer (W : Set G)).subtype ⊓ X with hA
  set B := A ⊓ centralizer (W : Set G) with hB
  have hmemA : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ X → ρ g ∈ E → (g : G) ∈ A :=
    fun g hg hgE => mem_inf.2 ⟨⟨g, hgE, rfl⟩, hg⟩
  have hρA : ∀ {a : G} (ha : a ∈ A), ρ ⟨a, hXW (mem_inf.1 ha).2⟩ ∈ E := by
    intro a ha
    obtain ⟨⟨a', ha'E, rfl⟩, -⟩ := ha
    exact ha'E
  have hA2 : IsPGroup 2 ↥A := by
    intro a
    have haX : (a : G) ∈ X := (mem_inf.1 a.2).2
    have h1 : ρ ⟨(a : G) * a, hXW (mul_mem haX haX)⟩ = 1 := by
      rw [show (⟨(a : G) * a, hXW (mul_mem haX haX)⟩ : ↥(normalizer (W : Set G))) =
        ⟨a, hXW haX⟩ * ⟨a, hXW haX⟩ from rfl, map_mul]
      exact hE2 _ (hρA a.2)
    have h2 : (a : G) * a ∈ K ⊓ centralizer (W : Set G) :=
      mem_inf.2 ⟨hXK (mul_mem haX haX), (hρker _).1 h1⟩
    obtain ⟨s, hs⟩ := hKC ⟨_, h2⟩
    refine ⟨s + 1, Subtype.ext ?_⟩
    have h3 : ((a : G) * a) ^ 2 ^ s = 1 := by simpa using congrArg Subtype.val hs
    have h4 : (a : G) ^ 2 ^ (s + 1) = 1 := by
      rw [pow_succ', pow_mul, pow_two]
      exact h3
    rw [Subgroup.coe_pow, h4, Subgroup.coe_one]
  have hXA : X ≤ normalizer (A : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun k hk a ha => ?_
    have haX : a ∈ X := (mem_inf.1 ha).2
    refine hmemA ⟨k * a * k⁻¹, hXW (mul_mem (mul_mem hk haX) (inv_mem hk))⟩
      (mul_mem (mul_mem hk haX) (inv_mem hk)) ?_
    rw [show (⟨k * a * k⁻¹, hXW (mul_mem (mul_mem hk haX) (inv_mem hk))⟩ :
      ↥(normalizer (W : Set G))) = ⟨k, hXW hk⟩ * ⟨a, hXW haX⟩ * ⟨k, hXW hk⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv]
    exact hE _ (hρP _ hk) _ (hρA ha)
  have hXB : X ≤ normalizer (B : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hXA hg, le_normalizer_centralizer_of hXW hg⟩
  have ha : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ A := by
    have hX' : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ X :=
      mul_mem (mul_mem (mul_mem hk₁ hk₂) (inv_mem hk₁)) (inv_mem hk₂)
    refine hmemA ⟨_, hXW hX'⟩ hX' ?_
    rw [show (⟨k₁ * k₂ * k₁⁻¹ * k₂⁻¹, hXW hX'⟩ : ↥(normalizer (W : Set G))) =
      n₁ * n₂ * n₁⁻¹ * n₂⁻¹ from rfl, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hEc
  have hka : k₁ * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) * k₁⁻¹ * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹)⁻¹ ∉ B := by
    intro h
    have hc := (mem_inf.1 h).2
    have hX' : k₁ * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) * k₁⁻¹ * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹)⁻¹ ∈ X :=
      (mem_inf.1 h).1 |> fun h' => (mem_inf.1 h').2
    have h1 := (hρker ⟨_, hXW hX'⟩).2 hc
    apply hnc
    rw [show (⟨_, hXW hX'⟩ : ↥(normalizer (W : Set G))) =
      n₁ * (n₁ * n₂ * n₁⁻¹ * n₂⁻¹) * n₁⁻¹ * (n₁ * n₂ * n₁⁻¹ * n₂⁻¹)⁻¹ from rfl] at h1
    simpa only [map_mul, map_inv] using h1
  obtain ⟨A₂, B₂, hBB₂, hA₂A, hch2, hnc2⟩ := exists_noncentral_chief hk₁ hm₁ hk₁m _ A B le_rfl
    hA2 inf_le_right inf_le_left hXA hXB ⟨_, ha, hka⟩
  have hAO : A ≤ pCoreOf 2 X :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hXA hA2
  have hWXB : W ⊓ X ≤ B := by
    intro w hw
    obtain ⟨hwW, hwX⟩ := mem_inf.1 hw
    have hwC : w ∈ centralizer (W : Set G) :=
      mem_centralizer_iff.2 fun v hv => hcommW v hv w hwW
    refine mem_inf.2 ⟨hmemA ⟨w, hXW hwX⟩ hwX ?_, hwC⟩
    rw [(hρker _).2 hwC]
    exact one_mem _
  exact ⟨A₁, B₁, A₂, B₂, hA₂A.trans hAO, hch1, hch2, (hA₁.trans hWXB).trans hBB₂, hnc1, hnc2⟩

end CFSG.Quasithin.H13.NQS134
