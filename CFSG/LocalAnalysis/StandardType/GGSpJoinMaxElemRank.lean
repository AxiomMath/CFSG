module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinMaxElemSp
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

section Maximal

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem mem_inf_of_commutes_of_inner {B Bs : Subgroup G} (hBs : GGBstar p B Bs) {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) {s : G} (hsX : s ∈ X)
    (hsp : s ^ p = 1) (hcomm : ∀ e ∈ Bs ⊓ X, s * e = e * s) : s ∈ Bs ⊓ X := by
  refine ⟨hBs.2.2.2 s ?_ hsp, hsX⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨u, hu, c, hc, hbc⟩ := ggBstar_split_of_inner hBs hX hnorm hinner b hb
  have h1 : s * u = u * s := hcomm u hu
  have h2 : s * c = c * s := Subgroup.mem_centralizer_iff.mp hc.2 s hsX
  rw [hbc]
  calc u * c * s = u * (c * s) := mul_assoc _ _ _
    _ = u * (s * c) := by rw [h2]
    _ = (u * s) * c := (mul_assoc _ _ _).symm
    _ = (s * u) * c := by rw [h1]
    _ = s * (u * c) := mul_assoc _ _ _

theorem comap_inf_maximal {F : Type} [Field F] {n : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (φ : StatedSp n F →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = X) (hX : Subgroup.center X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    (∀ a ∈ (Bs ⊓ X).comap φ, a ^ p = 1) ∧
      (∀ a ∈ (Bs ⊓ X).comap φ, ∀ b ∈ (Bs ⊓ X).comap φ, a * b = b * a) ∧
      (∀ g : StatedSp n F, g ^ p = 1 → (∀ a ∈ (Bs ⊓ X).comap φ, g * a = a * g) →
        g ∈ (Bs ⊓ X).comap φ) ∧
      Nat.card ↥((Bs ⊓ X).comap φ) = Nat.card ↥(Bs ⊓ X) := by
  have hle : Bs ⊓ X ≤ φ.range := by
    rw [hrange]
    exact inf_le_right
  have hEX : ∀ e ∈ Bs ⊓ X, ∃ a ∈ (Bs ⊓ X).comap φ, φ a = e := by
    intro e he
    obtain ⟨a, rfl⟩ := hle he
    exact ⟨a, he, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    apply hinj
    rw [map_pow, map_one]
    exact hBs.2.1.2 _ ha.1
  · intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact IsElemAbelian.comm hBs.2.1 ha.1 hb.1
  · intro g hgp hg
    have hgX : φ g ∈ X := by
      rw [← hrange]
      exact ⟨g, rfl⟩
    have hmem : φ g ∈ Bs ⊓ X := by
      refine mem_inf_of_commutes_of_inner hBs hX hnorm hinner hgX ?_ ?_
      · rw [← map_pow, hgp, map_one]
      · intro e he
        obtain ⟨a, ha, rfl⟩ := hEX e he
        rw [← map_mul, ← map_mul, hg a ha]
    exact hmem
  · have h := Subgroup.map_comap_eq_self hle
    rw [← Subgroup.card_map_of_injective (K := (Bs ⊓ X).comap φ) hinj, h]

theorem card_inf_eq_of_lifts {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B Bs X Y : Subgroup G} (hBs : GGBstar p B Bs)
    (φX : StatedSp n F →* G) (hXinj : Function.Injective φX) (hXrange : φX.range = X)
    (hXc : Subgroup.center X = ⊥) (hnormX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinnerX : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (φY : StatedSp n F →* G) (hYinj : Function.Injective φY) (hYrange : φY.range = Y)
    (hYc : Subgroup.center Y = ⊥) (hnormY : Bs ≤ Subgroup.normalizer (Y : Set G))
    (hinnerY : ∀ b ∈ Bs, ∃ x ∈ Y, ∀ y ∈ Y, b * y * b⁻¹ = x * y * x⁻¹) (hne : Bs ⊓ X ≠ ⊥) :
    Nat.card ↥(Bs ⊓ X) = Nat.card ↥(Bs ⊓ Y) := by
  obtain ⟨hpX, hcX, hmX, hcardX⟩ := comap_inf_maximal hBs φX hXinj hXrange hXc hnormX hinnerX
  obtain ⟨hpY, hcY, hmY, hcardY⟩ := comap_inf_maximal hBs φY hYinj hYrange hYc hnormY hinnerY
  have hne' : (Bs ⊓ X).comap φX ≠ ⊥ := by
    intro h
    apply hne
    have hle : Bs ⊓ X ≤ φX.range := by
      rw [hXrange]
      exact inf_le_right
    have h' := Subgroup.map_comap_eq_self hle
    rw [h, Subgroup.map_bot] at h'
    exact h'.symm
  rw [← hcardX, ← hcardY]
  exact OrdPNsSp.card_eq_of_maximal hp hp2 hpX hcX hmX hpY hcY hmY hne'

theorem card_bstar_centralizer_eq_of_lifts {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B Bs X Y : Subgroup G} (hBs : GGBstar p B Bs)
    (φX : StatedSp n F →* G) (hXinj : Function.Injective φX) (hXrange : φX.range = X)
    (hXc : Subgroup.center X = ⊥) (hnormX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinnerX : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (φY : StatedSp n F →* G) (hYinj : Function.Injective φY) (hYrange : φY.range = Y)
    (hYc : Subgroup.center Y = ⊥) (hnormY : Bs ≤ Subgroup.normalizer (Y : Set G))
    (hinnerY : ∀ b ∈ Bs, ∃ x ∈ Y, ∀ y ∈ Y, b * y * b⁻¹ = x * y * x⁻¹) (hne : Bs ⊓ X ≠ ⊥) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  have hX := card_ggBstar_split hBs hXc hnormX hinnerX
  have hY := card_ggBstar_split hBs hYc hnormY hinnerY
  have heq := card_inf_eq_of_lifts hp hp2 hBs φX hXinj hXrange hXc hnormX hinnerX φY hYinj hYrange
    hYc hnormY hinnerY hne
  have hpos : 0 < Nat.card ↥(Bs ⊓ X) := Nat.card_pos
  refine (Nat.eq_of_mul_eq_mul_left hpos ?_).symm
  calc Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = Nat.card Bs :=
        hX.symm
    _ = Nat.card ↥(Bs ⊓ Y) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) := hY
    _ = Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) := by rw [heq]

theorem card_bstar_centralizer_le_of_lifts {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) {B Bs X Y : Subgroup G} (hBs : GGBstar p B Bs)
    (φX : StatedSp n F →* G) (hXinj : Function.Injective φX) (hXrange : φX.range = X)
    (hXc : Subgroup.center X = ⊥) (hnormX : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinnerX : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (φY : StatedSp n F →* G) (hYinj : Function.Injective φY) (hYrange : φY.range = Y)
    (hYc : Subgroup.center Y = ⊥) (hnormY : Bs ≤ Subgroup.normalizer (Y : Set G))
    (hinnerY : ∀ b ∈ Bs, ∃ x ∈ Y, ∀ y ∈ Y, b * y * b⁻¹ = x * y * x⁻¹)
    (hcentX : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hrank : p ^ (n + 1) ≤ Nat.card Bs) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (Y : Set G)) ≤ p := by
  have hX := card_ggBstar_split hBs hXc hnormX hinnerX
  have hne : Bs ⊓ X ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(Bs ⊓ X) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [h1, one_mul] at hX
    have h2 : p ^ 2 ≤ p :=
      calc p ^ 2 ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp.pos (by omega)
        _ ≤ Nat.card Bs := hrank
        _ = Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := hX
        _ ≤ p := hcentX
    have h3 : p * p ≤ p * 1 := by rw [mul_one, ← sq]; exact h2
    have h4 : p ≤ 1 := Nat.le_of_mul_le_mul_left h3 hp.pos
    have h5 := hp.two_le
    omega
  exact (card_bstar_centralizer_eq_of_lifts hp hp2 hBs φX hXinj hXrange hXc hnormX hinnerX φY hYinj
    hYrange hYc hnormY hinnerY hne).le.trans hcentX

end Maximal

end CFSG.StandardType
