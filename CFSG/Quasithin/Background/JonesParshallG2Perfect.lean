module

public import CFSG.Quasithin.Background.JonesParshallG2Gen
public import CFSG.Quasithin.Background.JonesParshallSL3Perfect

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

theorem g2X_smul_mul (a : Fin 3 → F) (s t : F) : g2X (s • a) * g2X (t • a) = g2X ((s + t) • a) := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change xaFun (s • a) (xaFun (t • a) x) = xaFun ((s + t) • a) x
  rw [zorn_eta x, xaFun_zmk, xaFun_zmk, xaFun_zmk]
  simp only [Pi.smul_apply, smul_eq_mul]
  apply zmk_congr <;> ring_nf

theorem g2Y_smul_mul (b : Fin 3 → F) (s t : F) : g2Y (s • b) * g2Y (t • b) = g2Y ((s + t) • b) := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change ybFun (s • b) (ybFun (t • b) x) = ybFun ((s + t) • b) x
  rw [zorn_eta x, ybFun_zmk, ybFun_zmk, ybFun_zmk]
  simp only [Pi.smul_apply, smul_eq_mul]
  apply zmk_congr <;> ring_nf

theorem g2X_zero : g2X (0 : Fin 3 → F) = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change xaFun 0 x = x
  rw [zorn_eta x, xaFun_zmk]
  apply zmk_congr <;> simp

theorem g2Y_zero : g2Y (0 : Fin 3 → F) = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change ybFun 0 x = x
  rw [zorn_eta x, ybFun_zmk]
  apply zmk_congr <;> simp

theorem g2X_inv (a : Fin 3 → F) : (g2X a)⁻¹ = g2X a :=
  inv_eq_of_mul_eq_one_right (g2X_mul_self a)

theorem g2Y_inv (b : Fin 3 → F) : (g2Y b)⁻¹ = g2Y b :=
  inv_eq_of_mul_eq_one_right (g2Y_mul_self b)

theorem conj_mem_commutator_self {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H)
    {k : G} (hk : k ∈ ⁅H, H⁆) : g * k * g⁻¹ ∈ ⁅H, H⁆ := by
  rw [Subgroup.commutator_def] at hk ⊢
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨g * a * g⁻¹, H.mul_mem (H.mul_mem hg ha) (H.inv_mem hg),
      g * b * g⁻¹, H.mul_mem (H.mul_mem hg hb) (H.inv_mem hg), ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

abbrev cayleyIncl (F : Type) [Field F] :
    ↥(cayleyGroup F) →* (quasithinZorn F ≃ₗ[F] quasithinZorn F) := (cayleyGroup F).subtype

theorem g2A_mem_commutator {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (A : SL3 F) :
    ((g2A A : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      ⁅cayleyGroup F, cayleyGroup F⁆ := by
  have hc2 : c ^ 2 ≠ 1 := by
    intro h
    apply hc1
    have : (c + 1) ^ 2 = 0 := by rw [add_sq_F, one_pow, h, CharTwo.add_self_eq_zero]
    exact (CharTwo.add_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))
  have hA : A ∈ commutator (SL3 F) := by
    rw [sl3_commutator_eq_top hc0 hc2]
    exact Subgroup.mem_top A
  set φ := (cayleyIncl F).comp (g2A (F := F))
  have hle : (commutator (SL3 F)).map φ ≤ ⁅cayleyGroup F, cayleyGroup F⁆ := by
    rw [commutator_def, Subgroup.map_commutator]
    apply Subgroup.commutator_mono <;> rintro _ ⟨B, -, rfl⟩ <;> exact (g2A B).2
  exact hle ⟨A, hA, rfl⟩

@[expose] def g2D (c : F) (hc : c ≠ 0) : ↥(cayleyGroup F) :=
  g2A (diag3 c c⁻¹ 1 (by field_simp))

theorem g2X_e0_mem_commutator {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ((g2X ![1, 0, 0] : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      ⁅cayleyGroup F, cayleyGroup F⁆ := by
  have hc' : c + 1 ≠ 0 := fun h => hc1 (by
    have : c = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq])
  set t := (c + 1)⁻¹
  have hconj : g2D c hc0 * g2X (t • (![1, 0, 0] : Fin 3 → F)) * (g2D c hc0)⁻¹ =
      g2X ((c * t) • (![1, 0, 0] : Fin 3 → F)) := by
    rw [g2D, g2A_mul_g2X, mul_inv_cancel_right]
    congr 1
    funext i
    fin_cases i <;> simp [diag3, mulVec, dotProduct, Fin.sum_univ_three]
  have e : ⁅g2D c hc0, g2X (t • (![1, 0, 0] : Fin 3 → F))⁆ = g2X (![1, 0, 0] : Fin 3 → F) := by
    rw [commutatorElement_def, hconj, g2X_inv, g2X_smul_mul]
    congr 1
    rw [show c * t + t = (c + 1) * t by ring, mul_inv_cancel₀ hc', one_smul]
  rw [← e]
  exact Subgroup.commutator_mem_commutator (g2D c hc0).2 (g2X _).2

theorem g2Y_e0_mem_commutator {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ((g2Y ![1, 0, 0] : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      ⁅cayleyGroup F, cayleyGroup F⁆ := by
  have hc' : c⁻¹ + 1 ≠ 0 := fun h => hc1 (by
    have : c⁻¹ = -1 := eq_neg_of_add_eq_zero_left h
    rw [CharTwo.neg_eq, inv_eq_one] at this
    exact this)
  set t := (c⁻¹ + 1)⁻¹
  have hconj : g2D c hc0 * g2Y (t • (![1, 0, 0] : Fin 3 → F)) * (g2D c hc0)⁻¹ =
      g2Y ((c⁻¹ * t) • (![1, 0, 0] : Fin 3 → F)) := by
    rw [g2D, g2A_mul_g2Y, mul_inv_cancel_right]
    congr 1
    have hadj : adjugate ((diag3 c c⁻¹ 1 (by field_simp) : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal ![c⁻¹, c, 1] := by
      change (((diag3 c c⁻¹ 1 (by field_simp))⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
      rw [diag3_inv]
      change diagonal ![c⁻¹, c⁻¹⁻¹, 1⁻¹] = _
      rw [inv_inv, inv_one]
    rw [hadj, diagonal_transpose]
    funext i
    fin_cases i <;> simp [mulVec_diagonal]
  have e : ⁅g2D c hc0, g2Y (t • (![1, 0, 0] : Fin 3 → F))⁆ = g2Y (![1, 0, 0] : Fin 3 → F) := by
    rw [commutatorElement_def, hconj, g2Y_inv, g2Y_smul_mul]
    congr 1
    rw [show c⁻¹ * t + t = (c⁻¹ + 1) * t by ring, mul_inv_cancel₀ hc', one_smul]
  rw [← e]
  exact Subgroup.commutator_mem_commutator (g2D c hc0).2 (g2Y _).2

theorem cayley_commutator_eq {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ⁅cayleyGroup F, cayleyGroup F⁆ = cayleyGroup F := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun g hg h hh => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
  conv_lhs => rw [cayleyGroup_eq_closure]
  rw [Subgroup.closure_le]
  rintro g (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨A, rfl⟩)
  · by_cases ha : a = 0
    · subst ha
      rw [g2X_zero]
      exact Subgroup.one_mem _
    obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit a ha)
    have e : g2X a = g2A B * g2X ![1, 0, 0] * (g2A B)⁻¹ := by
      rw [g2A_mul_g2X, mul_inv_cancel_right]
      congr 1
      exact hB.symm
    rw [e]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_commutator_self (g2A B).2 (g2X_e0_mem_commutator hc0 hc1)
  · by_cases hb : b = 0
    · subst hb
      rw [g2Y_zero]
      exact Subgroup.one_mem _
    obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit b hb)
    set B' : SL3 F := invTransposeFun B
    have hB' : (adjugate (B' : Matrix (Fin 3) (Fin 3) F))ᵀ = (B : Matrix (Fin 3) (Fin 3) F) := by
      change (adjugate ((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F)ᵀ)ᵀ = _
      rw [← adjugate_transpose, transpose_transpose]
      change adjugate (adjugate (B : Matrix (Fin 3) (Fin 3) F)) = _
      rw [adjugate_adjugate _ (by simp), B.2]
      simp
    have e : g2Y b = g2A B' * g2Y ![1, 0, 0] * (g2A B')⁻¹ := by
      rw [g2A_mul_g2Y, mul_inv_cancel_right, hB']
      congr 1
      exact hB.symm
    rw [e]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_commutator_self (g2A B').2 (g2Y_e0_mem_commutator hc0 hc1)
  · exact g2A_mem_commutator hc0 hc1 A

end CFSG.Quasithin.JonesParshall
