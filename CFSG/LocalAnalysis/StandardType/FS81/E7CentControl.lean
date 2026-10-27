module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

private lemma fs81CentControl_mem_Y {X : Type} [Group X] {Y H Q M : Subgroup X} {σ b₀ : X}
    (hctrl : ∀ g : X, g * b₀ * g⁻¹ ∈ Y → g ∈ Y) (hMY : M ≤ Y)
    (hCM : ∀ c ∈ H, ⁅c, σ⁆ ∈ Q → ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hex : ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ M) {c : X} (hcH : c ∈ H)
    (hcQ : ⁅c, σ⁆ ∈ Q) : c ∈ Y := by
  obtain ⟨y, hyY, hyM⟩ := hex
  have hcy : c * y ∈ Y := by
    refine hctrl (c * y) ?_
    have e : (c * y) * b₀ * (c * y)⁻¹ = c * (y * b₀ * y⁻¹) * c⁻¹ := by group
    rw [e]
    exact hMY (hCM c hcH hcQ (y * b₀ * y⁻¹) hyM)
  have e : c = (c * y) * y⁻¹ := by group
  rw [e]
  exact Y.mul_mem hcy (Y.inv_mem hyY)

private lemma fs81CentControl_l_sq_mem {X : Type} [Group X] {H Q L : Subgroup X} {σ : X}
    (hHNQ : H ≤ Subgroup.normalizer (Q : Set X)) (hLH : L ≤ H) (hσ2 : orderOf σ = 2)
    {h l q : X} (hhH : h ∈ H) (hlL : l ∈ L) (hqQ : q ∈ Q)
    (hlq : h * σ * h⁻¹ = l * q) : l ^ 2 ∈ Q := by
  have hLNQ : L ≤ Subgroup.normalizer (Q : Set X) := hLH.trans hHNQ
  have hσsq : σ * σ = 1 := by rw [← pow_two, ← hσ2, pow_orderOf_eq_one]
  have hτsq : (h * σ * h⁻¹) * (h * σ * h⁻¹) = 1 := by
    have e : (h * σ * h⁻¹) * (h * σ * h⁻¹) = h * (σ * σ) * h⁻¹ := by group
    rw [e, hσsq]
    group
  set A : X := (h * σ * h⁻¹) * l⁻¹ with hA
  have hAQ : A ∈ Q := by
    rw [hA]
    have e : (h * σ * h⁻¹) * l⁻¹ = l * q * l⁻¹ := by rw [← hlq]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLNQ hlL) q).mp hqQ
  have hlAQ : l * A * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hLNQ hlL) A).mp hAQ
  have hmulQ : A * (l * A * l⁻¹) ∈ Q := Q.mul_mem hAQ hlAQ
  have hkey : A * (l * A * l⁻¹) * l ^ 2 = (h * σ * h⁻¹) * (h * σ * h⁻¹) := by
    rw [hA, hlq]
    group
  have hkey1 : A * (l * A * l⁻¹) * l ^ 2 = 1 := by rw [hkey, hτsq]
  have heq : l ^ 2 = (A * (l * A * l⁻¹))⁻¹ := by
    calc l ^ 2 = (A * (l * A * l⁻¹))⁻¹ * (A * (l * A * l⁻¹) * l ^ 2) := by group
      _ = (A * (l * A * l⁻¹))⁻¹ * 1 := by rw [hkey1]
      _ = (A * (l * A * l⁻¹))⁻¹ := by group
  rw [heq]
  exact Q.inv_mem hmulQ

private lemma fs81CentControl_l_involution {X : Type} [Group X] {H Q L : Subgroup X} {σ : X}
    (hHNQ : H ≤ Subgroup.normalizer (Q : Set X)) (hLH : L ≤ H) (hLQ : L ⊓ Q = ⊥)
    (hσL : σ ∈ L) (hσ2 : orderOf σ = 2) {h l q : X} (hhH : h ∈ H) (hlL : l ∈ L)
    (hqQ : q ∈ Q) (hlq : h * σ * h⁻¹ = l * q) : l ^ 2 = 1 ∧ l ≠ 1 := by
  have hl2 : l ^ 2 = 1 := by
    have hmem : l ^ 2 ∈ L ⊓ Q :=
      Subgroup.mem_inf.mpr
        ⟨L.pow_mem hlL 2, fs81CentControl_l_sq_mem hHNQ hLH hσ2 hhH hlL hqQ hlq⟩
    rw [hLQ] at hmem
    simpa using hmem
  refine ⟨hl2, ?_⟩
  intro hl1
  have hτQ : h * σ * h⁻¹ ∈ Q := by
    rw [hlq, hl1, one_mul]
    exact hqQ
  have hσQ : σ ∈ Q := by
    have e : σ = h⁻¹ * (h * σ * h⁻¹) * h := by group
    rw [e]
    simpa using
      (Subgroup.mem_normalizer_iff.mp (hHNQ (Subgroup.inv_mem H hhH)) (h * σ * h⁻¹)).mp hτQ
  have hσbot : σ ∈ L ⊓ Q := Subgroup.mem_inf.mpr ⟨hσL, hσQ⟩
  rw [hLQ] at hσbot
  have hσ1 : σ = 1 := by simpa using hσbot
  rw [hσ1, orderOf_one] at hσ2
  omega

private lemma fs81CentControl_commTau {X : Type} [Group X] {Q L : Subgroup X}
    (hLNQ : L ≤ Subgroup.normalizer (Q : Set X)) {b' l q : X} (hlL : l ∈ L)
    (hb'L : b' ∈ L) (hcomm : l * b' = b' * l) (hqQ : q ∈ Q) : ⁅b', l * q⁆ ∈ Q := by
  have hcommQ : ⁅b', q⁆ ∈ Q :=
    Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLNQ hb'L) q).mp hqQ) (Q.inv_mem hqQ)
  have hcommTau : ⁅b', l * q⁆ = l * ⁅b', q⁆ * l⁻¹ := by
    simp only [commutatorElement_def]
    calc b' * (l * q) * b'⁻¹ * (l * q)⁻¹
        = b' * l * q * b'⁻¹ * q⁻¹ * l⁻¹ := by group
      _ = l * b' * q * b'⁻¹ * q⁻¹ * l⁻¹ := by rw [hcomm]
      _ = l * (b' * q * b'⁻¹ * q⁻¹) * l⁻¹ := by group
  rw [hcommTau]
  exact (Subgroup.mem_normalizer_iff.mp (hLNQ hlL) ⁅b', q⁆).mp hcommQ

private lemma fs81CentControl_c_exists {X : Type} [Group X] {Y H Q L : Subgroup X} {σ b₀ : X}
    (hHNQ : H ≤ Subgroup.normalizer (Q : Set X)) (hLH : L ≤ H) (hLQ : L ⊓ Q = ⊥)
    (hσL : σ ∈ L) (hσ2 : orderOf σ = 2)
    (hinv : ∀ τ ∈ L, orderOf τ = 2 →
      ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ L ∧ τ * (y * b₀ * y⁻¹) = y * b₀ * y⁻¹ * τ)
    {h : X} (hhH : h ∈ H) (hh : h * σ * h⁻¹ ∈ L ⊔ Q) :
    ∃ y₁ ∈ Y, ∃ c : X, c ∈ H ∧ ⁅c, σ⁆ ∈ Q ∧
      c = (h⁻¹ * y₁) * b₀ * (h⁻¹ * y₁)⁻¹ := by
  have hLNQ : L ≤ Subgroup.normalizer (Q : Set X) := hLH.trans hHNQ
  have hdec : h * σ * h⁻¹ ∈ (↑(L ⊔ Q) : Set X) := hh
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L Q hLNQ, Set.mem_mul] at hdec
  obtain ⟨l, hlL, q, hqQ, hlq⟩ := hdec
  obtain ⟨hl2, hl1⟩ := fs81CentControl_l_involution hHNQ hLH hLQ hσL hσ2 hhH hlL hqQ hlq.symm
  obtain ⟨y₁, hy₁Y, hb'L, hcomm⟩ := hinv l hlL (orderOf_eq_prime hl2 hl1)
  set b' : X := y₁ * b₀ * y₁⁻¹ with hb'
  have hcommTauQ : ⁅b', h * σ * h⁻¹⁆ ∈ Q := by
    rw [← hlq]
    exact fs81CentControl_commTau hLNQ hlL hb'L hcomm hqQ
  set c : X := h⁻¹ * b' * h with hc
  have hcH : c ∈ H := by
    rw [hc]
    exact H.mul_mem (H.mul_mem (H.inv_mem hhH) (hLH hb'L)) hhH
  have hcQ : ⁅c, σ⁆ ∈ Q := by
    have e : ⁅c, σ⁆ = h⁻¹ * ⁅b', h * σ * h⁻¹⁆ * h := by
      rw [hc, commutatorElement_def]
      have hσe : σ = h⁻¹ * (h * σ * h⁻¹) * h := by group
      rw [hσe]
      group
    rw [e]
    simpa using
      (Subgroup.mem_normalizer_iff.mp (hHNQ (Subgroup.inv_mem H hhH)) _).mp hcommTauQ
  exact ⟨y₁, hy₁Y, c, hcH, hcQ, by rw [hc, hb']; group⟩

private lemma fs81CentControl_h_mem {X : Type} [Group X] {Y H Q L M : Subgroup X} {σ b₀ : X}
    (hHNQ : H ≤ Subgroup.normalizer (Q : Set X)) (hLH : L ≤ H) (hLQ : L ⊓ Q = ⊥)
    (hHY : H ⊓ Y ≤ L ⊔ Q) (hσL : σ ∈ L) (hσ2 : orderOf σ = 2)
    (hctrl : ∀ g : X, g * b₀ * g⁻¹ ∈ Y → g ∈ Y) (hMY : M ≤ Y)
    (hCM : ∀ c ∈ H, ⁅c, σ⁆ ∈ Q → ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hex : ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ M)
    (hinv : ∀ τ ∈ L, orderOf τ = 2 →
      ∃ y ∈ Y, y * b₀ * y⁻¹ ∈ L ∧ τ * (y * b₀ * y⁻¹) = y * b₀ * y⁻¹ * τ)
    {h : X} (hhH : h ∈ H) (hh : h * σ * h⁻¹ ∈ L ⊔ Q) : h ∈ L ⊔ Q := by
  obtain ⟨y₁, hy₁Y, c, hcH, hcQ, hceq⟩ :=
    fs81CentControl_c_exists hHNQ hLH hLQ hσL hσ2 hinv hhH hh
  have hcY : c ∈ Y := fs81CentControl_mem_Y hctrl hMY hCM hex hcH hcQ
  have hb0Y : (h⁻¹ * y₁) * b₀ * (h⁻¹ * y₁)⁻¹ ∈ Y := by
    rw [← hceq]
    exact hcY
  have hhy₁ : h⁻¹ * y₁ ∈ Y := hctrl _ hb0Y
  have hhY : h ∈ Y := by
    have e : h = y₁ * (h⁻¹ * y₁)⁻¹ := by group
    rw [e]
    exact Y.mul_mem hy₁Y (Y.inv_mem hhy₁)
  exact hHY (Subgroup.mem_inf.mpr ⟨hhH, hhY⟩)

theorem fs81CentControl_holds : FS81CentControl := by
  intro X _ _ Y H Q L M σ b₀ hQH hHNQ hLH hLQ hHY hσL hσ2 hctrl hMY hCM hex hinv h hhH hh
  exact fs81CentControl_h_mem hHNQ hLH hLQ hHY hσL hσ2 hctrl hMY hCM hex hinv hhH hh

end CFSG.StandardType.FrameRoute.FS81
