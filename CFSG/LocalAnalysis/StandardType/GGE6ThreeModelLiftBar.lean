module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelClassify

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

variable {R : Type} [Group R] [Finite R] {L' : Type} [Group L'] [Finite L'] (D : FrameData R)

theorem exists_weyl_lift_odd (hD : D.WeylOK) {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hodd : Odd (Nat.card ψ.ker)) (i : Fin 6) :
    ∃ w : L', ψ w = D.nb i ∧ w * w = 1 := by
  obtain ⟨w₀, hw₀⟩ := hψ (D.nb i)
  have hz : w₀ * w₀ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hw₀]
    exact hD.1 i
  have hzm : (w₀ * w₀) ^ Nat.card ψ.ker = 1 := by
    have h : (⟨w₀ * w₀, hz⟩ : ψ.ker) ^ Nat.card ψ.ker = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  refine ⟨w₀ ^ Nat.card ψ.ker, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hodd
    rw [map_pow, hw₀, hk, pow_succ, pow_mul, sq, hD.1 i, one_pow, one_mul]
  · rw [← pow_add, ← two_mul, pow_mul, sq, hzm]

theorem coboundary_clause (hAL : GGAbelianLift) (hD : D.Good)
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    {A : Subgroup (MulAut L')} (hA : IsPGroup 3 A) (hal : ∀ a ∈ A, ρ a ∈ D.diag.range)
    {w : Fin 6 → L'} (hw : ∀ i, ψ (w i) = D.nb i) :
    ∀ i, ∀ a ∈ A, w i * (a (w i))⁻¹ ∈ D.Tor.comap ψ ∧ (w i * (a (w i))⁻¹) ^ 3 = 1 := by
  intro i a ha
  obtain ⟨-, -, hcube⟩ := abelianLift_apply D hAL hD hψ hker hcard hρ hA hal hw
  obtain ⟨x, hx⟩ := hal a ha
  have hmem : ψ (w i * (a (w i))⁻¹) ∈ D.V0 := by
    rw [map_mul, map_inv, hw, ← hρ a (w i), ← hx, hw]
    exact hD.weyl.2.2.2 i (Multiplicative.toAdd x)
  exact ⟨D.V0_le_Tor hmem, hcube _ hmem⟩

theorem weyl_action_clause (hD : D.WeylOK) {ψ : L' →* R} (hψ : Function.Surjective ψ)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (hρinj : Function.Injective ρ)
    {A : Subgroup (MulAut L')} {Φ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hΦ : ∀ a : A, D.diag (Φ a) = ρ a)
    (hrange : Φ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ Φ.range ↔ x ∈ NoOffRest.hypE6)
    {w : Fin 6 → L'} (hw : ∀ i, ψ (w i) = D.nb i) :
    ∀ i (a : A), ∃ b : A, MulAut.conj (w i) * (a : MulAut L') * (MulAut.conj (w i))⁻¹ = b ∧
      Multiplicative.toAdd (Φ b) = adRefl .E6 3 i (Multiplicative.toAdd (Φ a)) := by
  intro i a
  have hρconj : ρ (MulAut.conj (w i)) = MulAut.conj (D.nb i) := by
    rw [rho_conj hψ hρ, hw]
  set x := Multiplicative.toAdd (Φ a) with hx
  have hmem : Multiplicative.ofAdd (adRefl .E6 3 i x) ∈ Φ.range := by
    rcases hrange with h | h
    · rw [h]
      exact Subgroup.mem_top _
    · exact (h _).2 (adRefl_mem_hypE6 ((h x).1 ⟨a, rfl⟩) i)
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, ?_, by rw [hb]; rfl⟩
  apply hρinj
  rw [map_mul, map_mul, map_inv, hρconj, ← hΦ a, ← hΦ b, hb]
  exact hD.2.2.1 i x

end CFSG.StandardType.E6ThreeModel
