module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepCent
public import CFSG.Quasithin.Background.GoldschmidtB69DeepCount
public import CFSG.Quasithin.Background.GoldschmidtB69DeepSec

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace B69

theorem arith_q1 {s₁ s₂ k a₁ c₁ c₂ : ℕ} (hk : 0 < k) (hs₁ : 0 < s₁) (hle : a₁ * c₁ ≤ s₁)
    (hcount : s₁ * s₂ * k ≤ a₁ * k * c₁ * c₂) : s₂ ≤ c₂ := by
  have h1 : s₁ * s₂ * k ≤ s₁ * c₂ * k := by
    calc s₁ * s₂ * k ≤ a₁ * k * c₁ * c₂ := hcount
      _ = (a₁ * c₁) * c₂ * k := by ring
      _ ≤ s₁ * c₂ * k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
  have h2 : s₁ * s₂ ≤ s₁ * c₂ := Nat.le_of_mul_le_mul_right h1 hk
  exact Nat.le_of_mul_le_mul_left h2 hs₁

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_one_le_rAV (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {W₁ W₂ : Subgroup V} (h₁ : W₁ ∈ IrrPlus L (⊤ : Subgroup V))
    (h₂ : W₂ ∈ IrrPlus L (⊤ : Subgroup V)) (hne : W₁ ≠ W₂)
    (hq : 1 ≤ rAV (autSec A W₁ (fixV L))) : False := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hA₁ := a_stab_irr hV hA hL hLA h₁
  have hA₂ := a_stab_irr hV hA hL hLA h₂
  have hAW₁ : A ≤ stabSub W₁ := B1.le_stabSub_of_invariant hA₁
  have hAW₂ : A ≤ stabSub W₂ := B1.le_stabSub_of_invariant hA₂
  have hAU : A ≤ stabSub (fixV L) :=
    B1.le_stabSub_of_invariant (B1Red.fixV_inv_of_normalizes hAn)
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hB₁ := not_le_centSec_of_irr hL hAn hLA h₁ hA₁
  have hB₂ := not_le_centSec_of_irr hL hAn hLA h₂ hA₂
  have hcount := two_sections_count hV hA hL hLA h₁ h₂ hne
  have hK : A ⊓ centSec W₁ (fixV L) ⊓ centSec W₂ (fixV L) = A ⊓ centSec W₁ (fixV L) :=
    inf_eq_left.2 (inf_centSec_le hV hAel hL hAn h₁ h₂ hA₂)
  rw [hK] at hcount
  have hS2 : ∀ s : Sec W₁ (fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W₁ (fixV L)
  have hA2 : IsA2 (autSec A W₁ (fixV L)) (autSec A W₁ (fixV L)) :=
    ⟨le_rfl, autSec_ne_bot hAW₁ hAU hB₁, isElemAbelian2_autSec hAel hAW₁ hAU⟩
  have hle : Nat.card (autSec A W₁ (fixV L)) * Nat.card (fixV (autSec A W₁ (fixV L))) ≤
      Nat.card (Sec W₁ (fixV L)) := by
    by_contra hlt
    push Not at hlt
    exact absurd ((rAV_lt_one_iff hS2 hA2).2 hlt) (not_lt.2 hq)
  have hmul₁ := card_autSec_mul hAW₁ hAU
  rw [← hmul₁] at hcount
  have hs₂ := arith_q1 Nat.card_pos Nat.card_pos hle hcount
  have hc₂ : Nat.card (fixV (autSec A W₂ (fixV L))) ≤ Nat.card (Sec W₂ (fixV L)) :=
    Subgroup.card_le_card_group _
  have hfix : fixV (autSec A W₂ (fixV L)) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm hc₂ hs₂)
  apply hB₂
  intro a ha
  have hφ : B5.secHom A hAW₂ hAU ⟨a, ha⟩ ∈ autSec A W₂ (fixV L) := by
    rw [← B5.range_secHom A hAW₂ hAU]
    exact ⟨⟨a, ha⟩, rfl⟩
  have h1 : B5.secHom A hAW₂ hAU ⟨a, ha⟩ = 1 := by
    refine MulEquiv.ext fun s => ?_
    have : s ∈ fixV (autSec A W₂ (fixV L)) := by rw [hfix]; trivial
    exact this _ hφ
  exact (B5.mem_ker_secHom A hAW₂ hAU ⟨a, ha⟩).1 (MonoidHom.mem_ker.2 h1)

theorem one_le_rAV_of_qOf (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L)
    {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hQ : ((1 : ℚ) : WithTop ℚ) ≤ qOf (autSec (L ⊔ A) W (W ⊓ fixV L))) :
    1 ≤ rAV (autSec A W (fixV L)) := by
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hA₁ := a_stab_irr hV hA hL hLA hW
  have hAW : A ≤ stabSub W := B1.le_stabSub_of_invariant hA₁
  have hAZ : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hA₁ (B1Red.fixV_inv_of_normalizes hAn))
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hB : ¬ A ≤ centSec W (W ⊓ fixV L) := by
    rw [centSec_inf]
    exact not_le_centSec_of_irr hL hAn hLA hW hA₁
  have hA2 : IsA2 (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec A W (W ⊓ fixV L)) :=
    ⟨autSec_mono le_sup_right W _, autSec_ne_bot hAW hAZ hB, isElemAbelian2_autSec hAel hAW hAZ⟩
  have hquad : commSeries (autSec A W (W ⊓ fixV L)) 2 = ⊥ :=
    (isQuadratic_iff_commSeries_two _).1 (isQuadratic_autSec hAW hAZ (B1_4_3 hV hA))
  have := le_kq_iff.1 hQ _ hA2 hquad
  rw [rAV_autSec_inf A W (fixV L)]
  exact this

end B69

end CFSG.Quasithin
