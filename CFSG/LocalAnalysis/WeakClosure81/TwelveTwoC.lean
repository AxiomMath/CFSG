module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveCartan
public import CFSG.LocalAnalysis.WeakClosure81.TwelvePermMod
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section TwoC

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {n m : ℕ}

theorem Setting12One.exists_nontrivial_of_cartan [Finite G]
    {ρ : G →* LGL 2 V} {B A : Subgroup G} {Z : Submodule (ZMod 2) V}
    (h : Setting12One ρ B Z A n m) {S : Sylow 2 G} (hSB : B = normalizer (S : Set G))
    {T : Subgroup G} (hT1 : T ≠ ⊥) (hTB : T ≤ B)
    (hBST : ∀ b ∈ B, ∃ s ∈ (S : Subgroup G), ∃ x ∈ T, b = s * x)
    (hTS : ∀ x ∈ T, x ≠ 1 → ∀ s ∈ (S : Subgroup G), s * x = x * s → s = 1) :
    ∃ x ∈ T, ∃ z ∈ Z, ρ x z ≠ z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₀, hx₀T⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hSB' : (S : Subgroup G) ≤ B := hSB ▸ Subgroup.le_normalizer
  have hx₀N : x₀ ∈ normalizer ((S : Subgroup G) : Set G) := hSB ▸ hTB hx₀T
  have hSfix : ∀ s ∈ (S : Subgroup G), ∀ z ∈ Z, ρ s z = z := by
    intro s hs z hz
    obtain ⟨s', hs', rfl⟩ := exists_eq_commutator_of_fpf hx₀N (hTS x₀ hx₀T hx₀1') hs
    have h1 : ρ x₀⁻¹ z = z := hcon x₀⁻¹ (T.inv_mem hx₀T) z hz
    have h2 : ρ s' z ∈ Z := (h.stab s').mp (hSB' hs') z hz
    have h3 : ρ x₀ (ρ s' z) = ρ s' z := hcon x₀ hx₀T _ h2
    rw [map_mul, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, h1, h3, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hBfix : ∀ b ∈ B, ∀ z ∈ Z, ρ b z = z := by
    intro b hb z hz
    obtain ⟨s, hs, x, hx, rfl⟩ := hBST b hb
    rw [map_mul, LinearEquiv.mul_apply, hcon x hx z hz, hSfix s hs z hz]
  have hA4 : 4 ≤ Nat.card A := by
    rw [h.A_card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.one_lt_m
  have hfree : ∀ g : G, g ∉ B → ∀ a ∈ A, g⁻¹ * a * g ∈ B → a = 1 := fun g hg a ha hga =>
    rankOne_free_off_borel h.type h.borel h.A_le_B h.A_elem hg ha hga
  have hall : ∀ z ∈ Z, ∀ g : G, ρ g z = z := fun z hz =>
    permMod_fixed ρ h.A_le_B h.A_elem hA4 h.quad hfree (fun b hb => hBfix b hb z hz)
  have hBtop : B = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact (h.stab g).mpr fun z hz => by rw [hall z hz g]; exact hz
  exact rankOne_borel_ne_top h.type S (hSB.symm.trans hBtop)

theorem sylow_trivial_of_regular (ρ : G →* LGL 2 V) {S : Sylow 2 G} {T : Subgroup G}
    {Z : Submodule (ZMod 2) V} (hT : T ≤ normalizer (S : Set G))
    (hSZ : ∀ s ∈ (S : Subgroup G), ∀ z ∈ Z, ρ s z ∈ Z) (hZ0 : Z ≠ ⊥)
    (hreg : RegularOnNonzero ρ T Z) : ∀ s ∈ (S : Subgroup G), ∀ z ∈ Z, ρ s z = z := by
  obtain ⟨w, hwZ, hw0, hwfix⟩ := exists_fixed_vector_of_isPGroup ρ S.isPGroup' hSZ hZ0
  intro s hs z hz
  by_cases hz0 : z = 0
  · rw [hz0, map_zero]
  obtain ⟨x, hxT, hxw⟩ := hreg.2 w hwZ hw0 z hz hz0
  have hxN : x⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem (hT hxT)
  have hconj : x⁻¹ * s * x ∈ (S : Subgroup G) :=
    (Subgroup.mem_set_normalizer_iff''.mp (hT hxT) s).mp hs
  have key : ρ x (ρ (x⁻¹ * s * x) w) = ρ s (ρ x w) := by
    rw [← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul]
    congr 2
    group
  rw [← hxw, ← key, hwfix _ hconj]

theorem odd_orderOf_of_odd_card {T : Subgroup G} (hT : Odd (Nat.card T)) {x : G} (hx : x ∈ T) :
    Odd (orderOf x) := by
  have h1 : orderOf (⟨x, hx⟩ : T) ∣ Nat.card T := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact hT.of_dvd_nat h1

theorem eq_zero_of_fixed_of_odd_mem_borel (ρ : G →* LGL 2 V) {S : Sylow 2 G}
    {B T : Subgroup G} {Z : Submodule (ZMod 2) V} (hTB : T ≤ B)
    (hBZ : ∀ b ∈ B, ∀ z ∈ Z, ρ b z ∈ Z)
    (hBST : ∀ b ∈ B, ∃ s ∈ (S : Subgroup G), ∃ x ∈ T, b = s * x)
    (hS : ∀ s ∈ (S : Subgroup G), ∀ z ∈ Z, ρ s z = z)
    (hT : ∀ x ∈ T, x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0)
    {x : G} (hxB : x ∈ B) (hodd : Odd (orderOf x)) (hx1 : x ≠ 1) {z : V} (hz : z ∈ Z)
    (hfix : ρ x z = z) : z = 0 := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hBST x hxB
  have hyz : ρ y z ∈ Z := hBZ y (hTB hy) z hz
  have hyfix : ρ y z = z := by
    have : ρ s (ρ y z) = ρ y z := hS s hs _ hyz
    rw [map_mul, LinearEquiv.mul_apply, this] at hfix
    exact hfix
  by_cases hy1 : y = 1
  · exfalso
    apply hx1
    rw [hy1, mul_one] at hodd ⊢
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥(S : Subgroup G))).mp
      S.isPGroup' ⟨s, hs⟩
    have hk' : orderOf s = 2 ^ k := by simpa using hk
    rw [hk'] at hodd
    have hk0 : k = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨by decide, hne⟩)
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.mp hk'
  · exact hT y hy hy1 z hz hyfix

end TwoC

end CFSG.LocalAnalysis.WeakClosure81
