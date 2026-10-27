module

public import CFSG.Quasithin.H13.NQRigidShortModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Family (IsComp IsBestOffender)
open CFSG.QuasithinUnique.Setup.SL2Modules (repOfSubgroup)
open scoped MatrixGroups LinearAlgebra.Projectivization

theorem center_eq_bot_of_isSimpleGroup {A : Type*} [Group A] [IsSimpleGroup A]
    (h : ∃ a b : A, a * b ≠ b * a) : center A = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ center A := h1 ▸ mem_top a
    exact hab (mem_center_iff.mp ha b).symm

variable {V : Type} [CommGroup V] [Finite V]

theorem offender_le_of_sl2_component
    (hV : ∀ v : V, v * v = 1) {G₀ L₀ X : Subgroup (MulAut V)} (hL : IsComp L₀ G₀)
    (hX : IsBestOffender G₀ X) (hLX : ⁅L₀, X⁆ ≠ ⊥)
    (hE : ∀ g ∈ G₀, g ∈ centralizer (L₀ : Set (MulAut V)) → g = 1)
    {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    [IsSimpleGroup SL(2, F)] (hnc : ∃ a b : SL(2, F), a * b ≠ b * a) (α₀ : ↥L₀ ≃* SL(2, F)) :
    X ≤ L₀ ∧ Nat.card X = 2 ^ n := by
  classical
  obtain ⟨hXN, -, ⟨Sd⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.irreducibleSectionProp V hV G₀ L₀ X hL hX hLX
  have hW2 : ∀ w : Sd.W, w * w = 1 := by
    intro w
    obtain ⟨v, rfl⟩ := Sd.π_surjective w
    rw [← map_mul]
    have h1 : v * v = 1 := Subtype.ext (by
      rw [coe_mul, OneMemClass.coe_one]
      exact hV v)
    rw [h1, map_one]
  have := Sd.nontrivial
  let fL : ↥L₀ →* MulAut Sd.W := Sd.τW.comp (inclusion le_sup_left)
  let fX : ↥X →* MulAut Sd.W := Sd.τW.comp (inclusion le_sup_right)
  have hirr1 : ∀ U : Subgroup Sd.W, (∀ g ∈ fL.range, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => Sd.irreducible U fun x hx u hu => by
      have hx' : x = inclusion le_sup_left ⟨(x : MulAut V), hx⟩ := Subtype.ext rfl
      rw [hx']
      exact hU _ ⟨⟨(x : MulAut V), hx⟩, rfl⟩ u hu
  obtain ⟨W, _, _, _, _, Ψ, hirr, hBe, hquad, hoff⟩ :=
    exists_moduleEquiv (L₁ := fL.range) (B₁ := fX.range) hW2 hirr1 Sd.abar_elem
      Sd.abar_quadratic Sd.abar_offender
  have : Finite (Module.End (ZMod 2) W)ˣ :=
    Finite.of_injective (fun u : (Module.End (ZMod 2) W)ˣ => (u.val : W → W))
      fun a b h => Units.ext (LinearMap.ext (congrFun h))
  have : IsSimpleGroup ↥L₀ := α₀.isSimpleGroup
  have hfL : Function.Injective fL := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fL.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff fL).mp h
    · exfalso
      apply Sd.lbar_ne_bot
      rw [eq_bot_iff]
      rintro _ ⟨l, rfl⟩
      exact (mem_bot).mpr (MonoidHom.mem_ker.mp (h ▸ mem_top l))
  set L₁ : Subgroup (Module.End (ZMod 2) W)ˣ := fL.range.map Ψ.toMonoidHom with hL₁
  set B₁ : Subgroup (Module.End (ZMod 2) W)ˣ := fX.range.map Ψ.toMonoidHom with hB₁
  let e₁ : ↥L₀ ≃* ↥L₁ :=
    (MonoidHom.ofInjective hfL).trans (fL.range.equivMapOfInjective _ Ψ.injective)
  let θ₁ : ↥L₁ ≃* SL(2, F) := e₁.symm.trans α₀
  have : IsSimpleGroup ↥L₁ := θ₁.isSimpleGroup
  have hcen : center ↥L₁ = ⊥ := center_eq_bot_of_isSimpleGroup (by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨θ₁.symm a, θ₁.symm b, fun h => hab (by simpa using congrArg θ₁ h)⟩)
  let α₁ : (↥L₁ ⧸ center ↥L₁) ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientBot.trans θ₁)
  have hperf : Group.IsPerfect ↥L₁ :=
    CFSG.QuasithinUnique.Setup.Lift.isPerfect_of_equiv
      (fL.range.equivMapOfInjective _ Ψ.injective) Sd.lbar_quasisimple.1
  have hB1 : B₁ ≠ ⊥ := by
    intro h0
    apply Sd.abar_ne_bot
    rw [eq_bot_iff]
    intro b hb
    have h1 : Ψ b ∈ B₁ := ⟨b, hb, rfl⟩
    rw [h0, mem_bot] at h1
    rw [mem_bot]
    exact Ψ.injective (h1.trans (map_one Ψ).symm)
  have hBN0 : fX.range ≤ normalizer (fL.range : Set (MulAut Sd.W)) := by
    rintro _ ⟨b, rfl⟩
    rw [mem_normalizer_iff]
    have hconj : ∀ (c : ↥X) (l : ↥L₀), fX c * fL l * (fX c)⁻¹ =
        fL ⟨(c : MulAut V) * l * (c : MulAut V)⁻¹,
          (mem_normalizer_iff.mp (hXN c.2) l).mp l.2⟩ := by
      intro c l
      show Sd.τW _ * Sd.τW _ * (Sd.τW _)⁻¹ = Sd.τW _
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    intro y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨_, (hconj b l).symm⟩
    · rintro ⟨l, hl⟩
      refine ⟨⟨(b : MulAut V)⁻¹ * l * (b : MulAut V)⁻¹⁻¹,
        (mem_normalizer_iff.mp (hXN (inv_mem b.2)) l).mp l.2⟩, ?_⟩
      have h1 := hconj b⁻¹ l
      have h2 : fX b⁻¹ = (fX b)⁻¹ := map_inv fX b
      rw [h2, inv_inv, hl] at h1
      rw [show (⟨(b : MulAut V)⁻¹ * l * (b : MulAut V)⁻¹⁻¹, _⟩ : ↥L₀) =
        ⟨((b⁻¹ : ↥X) : MulAut V) * l * ((b⁻¹ : ↥X) : MulAut V)⁻¹,
          (mem_normalizer_iff.mp (hXN (b⁻¹).2) l).mp l.2⟩ from rfl, ← h1]
      group
  have hBN : B₁ ≤ normalizer (L₁ : Set (Module.End (ZMod 2) W)ˣ) :=
    (map_mono hBN0).trans (le_normalizer_map _)
  have := hBe
  let : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  obtain ⟨-, θ, -, halt, -⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.central_quotient_SL2_quadratic_offender_alternatives
      (by omega : 2 ≤ n) hF L₁ hirr hperf α₁ B₁ hB1 hBN hquad hoff
  obtain ⟨hBL, -, β, -, ℓ, -, -, -, hBcard, -⟩ | ⟨-, hn2, -⟩ := halt
  swap
  · omega
  have hYG : L₀ ⊔ X ≤ G₀ := sup_le hL.1 hX.1
  have hYN : L₀ ⊔ X ≤ normalizer (L₀ : Set (MulAut V)) := sup_le le_normalizer hXN
  have hτinj : Function.Injective Sd.τW := by
    rw [injective_iff_map_eq_one]
    intro y hy
    apply Subtype.ext
    rw [OneMemClass.coe_one]
    refine hE _ (hYG y.2) ?_
    rw [mem_centralizer_iff]
    intro l hl
    have hc : (y : MulAut V) * l * (y : MulAut V)⁻¹ ∈ L₀ :=
      (mem_normalizer_iff.mp (hYN y.2) l).mp hl
    have hcL : (y : MulAut V) * l * (y : MulAut V)⁻¹ * l⁻¹ ∈ L₀ := mul_mem hc (inv_mem hl)
    have h1 : fL ⟨_, hcL⟩ = 1 := by
      have he : (inclusion le_sup_left ⟨_, hcL⟩ : ↥(L₀ ⊔ X)) =
          y * inclusion le_sup_left ⟨l, hl⟩ * y⁻¹ * (inclusion le_sup_left ⟨l, hl⟩)⁻¹ :=
        Subtype.ext rfl
      show Sd.τW (inclusion le_sup_left ⟨_, hcL⟩) = 1
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, hy]
      group
    have h2 := hfL (h1.trans (map_one fL).symm)
    have h3 : (y : MulAut V) * l * (y : MulAut V)⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h2
    calc l * (y : MulAut V) =
        ((y : MulAut V) * l * (y : MulAut V)⁻¹ * l⁻¹)⁻¹ * ((y : MulAut V) * l) := by group
      _ = (y : MulAut V) * l := by rw [h3, inv_one, one_mul]
  have hXL : X ≤ L₀ := by
    intro x hx
    have h1 : Ψ (fX ⟨x, hx⟩) ∈ L₁ := hBL ⟨fX ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    obtain ⟨_, ⟨l, rfl⟩, hl⟩ := h1
    have h2 : fL l = fX ⟨x, hx⟩ := Ψ.injective hl
    have h4 : (l : MulAut V) = x := congrArg Subtype.val (hτinj h2)
    rw [← h4]
    exact l.2
  have hfX : Function.Injective fX := hτinj.comp (inclusion_injective le_sup_right)
  have hXcard : Nat.card X = Nat.card B₁ := by
    rw [hB₁, card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective]
    exact Nat.card_congr (MonoidHom.ofInjective hfX).toEquiv
  exact ⟨hXL, hXcard.trans hBcard⟩

end CFSG.Quasithin.H13.NQRigid
