module

public import CFSG.RankThree.GF2n.Smith81.S81BPos

public section

namespace CFSG.RankThree.GF2n.Smith81.EGeom

section Model

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure MinuscLine (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ : V) (U₀ : Subgroup (V ≃ₗ[K] V)) : Prop where
  line_iff : ∀ g₁ ∈ Γ, ∀ g₂ ∈ Γ, ∀ g₃ ∈ Γ, ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    a • g₁ p₀ + b • g₂ p₀ = c • g₃ p₀ →
      g₂ p₀ ∈ Wsp (Submodule.span K {g₁ p₀}) (conjSub g₁ U₀)

end Model

end CFSG.RankThree.GF2n.Smith81.EGeom

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)}

theorem Ctx.psi_pi_ne_zero (ψ : M₀.E ≃ₗ[K] V) {C : Subgroup G} (hC : Ctx M Q Z C) {w : G}
    (hw : w ∈ C) (hw1 : w ≠ 1) : ψ (M₀.π w) ≠ 0 := by
  intro h0
  have h1 : M₀.π w = 0 := (map_eq_zero_iff ψ ψ.injective).mp h0
  have hZ : w ∈ Z := (M₀.π_ker w (hC.le hw)).mp h1
  have hbot : w ∈ Z ⊓ C := Subgroup.mem_inf.mpr ⟨hZ, hw⟩
  rw [hC.inf_eq_bot, Subgroup.mem_bot] at hbot
  exact hw1 hbot

theorem EGeom.EUniData.le_QB_of_sum_mem (hg : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {n : ℕ} (hG : MinuscGeom Γ p₀ U₀ n)
    (hL : MinuscLine Γ p₀ U₀) {X Y D : Subgroup G} (hX : Ctx M Q Z X) (hY : Ctx M Q Z Y)
    (hD : Ctx M Q Z D) (hcard : Nat.card ↥(Q ⊓ QB X) = Nat.card Z ^ (n + 1)) {x y : G}
    (hx : x ∈ X) (hy : y ∈ Y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x * y ∈ D) (hxy1 : x * y ≠ 1)
    (hne : Y ⊔ Z ≠ X ⊔ Z) : Y ≤ QB X := by
  obtain ⟨gX, hgX⟩ := d.exists_isPt hX
  obtain ⟨gY, hgY⟩ := d.exists_isPt hY
  obtain ⟨gD, hgD⟩ := d.exists_isPt hD
  have hmem : ∀ {C : Subgroup G} {g : V ≃ₗ[K] V}, d.IsPt C g → ∀ {w : G}, w ∈ C →
      ψ (M₀.π w) ∈ Submodule.span K {g p₀} := by
    intro C g hg' w hw
    have h : ψ (M₀.π w) ∈ (fun a : G => ψ (M₀.π a)) '' (C : Set G) := ⟨w, hw, rfl⟩
    rw [hg'.2.1] at h
    exact h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hmem hgX hx)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmem hgY hy)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hmem hgD hxy)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact Ctx.psi_pi_ne_zero ψ hX hx hx1 (by rw [← ha, zero_smul])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact Ctx.psi_pi_ne_zero ψ hY hy hy1 (by rw [← hb, zero_smul])
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact Ctx.psi_pi_ne_zero ψ hD hxy hxy1 (by rw [← hc, zero_smul])
  have hadd : ψ (M₀.π (x * y)) = ψ (M₀.π x) + ψ (M₀.π y) := by
    rw [M₀.π_mul x (hX.le hx) y (hY.le hy), map_add]
  have hrel : a • gX p₀ + b • gY p₀ = c • gD p₀ := by
    rw [ha, hb, hc, hadd]
  have hline := hL.line_iff gX hgX.1 gY hgY.1 gD hgD.1 a b c ha0 hb0 hc0 hrel
  have hspan : Submodule.span K {gY p₀} ≠ Submodule.span K {gX p₀} := fun h =>
    hne ((d.epos_eq_iff hX hY hgX hgY).mpr h)
  exact ((d.epos_Q_iff hX hY hgX hgY hcard hG.W_le hg.card).mpr ⟨hspan, hline⟩).2

end CFSG.RankThree.GF2n.Smith81
