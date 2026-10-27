module

public import CFSG.Quasithin.Background.C124YLH6Off
public import CFSG.Quasithin.Background.C124YLH6Grp

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.H6

open Matrix CFSG.Quasithin CFSG.Open CFSG.Quasithin.C124.YL.A6

structure HatCtx {W : Type*} [CommGroup W] (K : Type) [Field K] [Finite K]
    (Γ₀ : Subgroup (GL (Fin 3) K)) (Ls : Subgroup (MulAut W)) (U Z : Subgroup W) where
  hK : Nat.card K = 4
  hdet : ∀ g ∈ Γ₀, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
  hat : IsHat ↥Γ₀ ↥(alternatingGroup (Fin 6))
  hcen : ∀ g ∈ Subgroup.center ↥Γ₀, ∃ a : K,
    ((g : ↥Γ₀) : GL (Fin 3) K).val = a • (1 : Matrix (Fin 3) (Fin 3) K)
  π : ↥Γ₀ →* ↥Ls
  real : (FFModel.nat Γ₀).RealizesVia Ls U Z π

namespace HatCtx

variable {W : Type*} [CommGroup W] [Finite W] {K : Type} [Field K] [Finite K]
  {Γ₀ : Subgroup (GL (Fin 3) K)} {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : HatCtx K Γ₀ Ls U Z)

include C in
theorem two_eq_zero : (2 : K) = 0 := by
  have hF4 : Nat.card K = 2 ^ 2 := by rw [C.hK]; norm_num
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hF4
  exact_mod_cast CharP.cast_eq_zero K 2

@[expose] def phi : ↥Γ₀ →* MulAut W := Ls.subtype.comp C.π

theorem phi_range : C.phi.range = Ls := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (C.π g).2
  · intro hx
    obtain ⟨g, hg⟩ := C.real.1 ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩

theorem phi_mem (g : ↥Γ₀) : C.phi g ∈ Ls := (C.π g).2

theorem coord : ∃ c : ↥U →* Multiplicative (Fin 3 → K), IsCoord U Z c ∧
    ∀ (γ : ↥Γ₀) (u : ↥U) (hu : C.phi γ (u : W) ∈ U),
      c ⟨C.phi γ (u : W), hu⟩ = natAct Γ₀ γ (c u) := by
  have hsec : ∀ q : (FFModel.nat Γ₀).Amb, q ∈ (FFModel.nat Γ₀).sec := fun _ => Subgroup.mem_top _
  have hker : ∀ q ∈ (FFModel.nat Γ₀).ker, q = 1 := fun q hq => Subgroup.mem_bot.1 hq
  exact coord_of_realizes hsec hker C.real

include C in
theorem card_Q : Nat.card (Multiplicative (Fin 3 → K)) = 64 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi, C.hK]
  simp [Finset.prod_const]

theorem π_injective : Function.Injective C.π := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro γ hγ
  have h1 : C.π γ = 1 := hγ
  have h2 : ∀ q : Multiplicative (Fin 3 → K), natAct Γ₀ γ q = q := by
    intro q
    obtain ⟨u, rfl⟩ := hc.surj q
    have hu : C.phi γ (u : W) ∈ U := C.real.2.2.2.1 (C.π γ) u u.2
    have := hequiv γ u hu
    have e : C.phi γ (u : W) = (u : W) := by
      show ((C.π γ : ↥Ls) : MulAut W) (u : W) = u
      rw [h1]
      rfl
    rw [← this]
    congr 1
    exact Subtype.ext e
  refine Subgroup.mem_bot.2 (eq_one_of_mulVec fun y => ?_)
  have := h2 (Multiplicative.ofAdd y)
  exact congrArg Multiplicative.toAdd this

theorem phi_injective : Function.Injective C.phi := Subtype.val_injective.comp C.π_injective

include C in
theorem exists_q : ∃ q : ↥Γ₀ →* P6, q.range = alternatingGroup (Fin 6) ∧ Nat.card q.ker = 3 ∧
    q.ker ≤ Subgroup.center ↥Γ₀ := by
  obtain ⟨q, hq, hker⟩ := exists_hat_hom C.hat
  exact ⟨q, hq, card_ker_hat C.hat hker, hker.le⟩

include C in
theorem h4 : ∀ B : Subgroup ↥Γ₀, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ a ∈ B, a * a = 1) →
    Nat.card B ≤ 4 := by
  obtain ⟨q, hq, hker3, -⟩ := C.exists_q
  exact fun B hc hs => card_le_four_of_elem hq hker3 hc hs

end HatCtx

end CFSG.Quasithin.C124.YL.H6
