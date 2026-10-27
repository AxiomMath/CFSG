module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin
open CFSG.Open (pCoreOf IsElemAbelian)
open scoped IsMulCommutative commutatorElement

namespace BK6

variable {G : Type} [Group G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem sup_commutator_eq_of {A Q : Subgroup G}
    (hCQ : V ⊓ Subgroup.centralizer (L : Set G) ≤ Q) (h1 : ∀ v ∈ V, ∀ a ∈ A, ⁅v, a⁆ ∈ Q)
    (h2 : ∀ q ∈ Q, ∃ c ∈ ⁅V, A⁆, q * c⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G)) :
    ⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = Q := by
  refine le_antisymm (sup_le (Subgroup.commutator_le.mpr h1) hCQ) fun q hq => ?_
  obtain ⟨c, hc, hqc⟩ := h2 q hq
  rw [show q = q * c⁻¹ * c by group, sup_comm]
  exact Subgroup.mul_mem_sup hqc hc

theorem sup_commutator_conj {A : Subgroup G} {l : G} (hl : l ∈ L)
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) :
    ⁅V, conjSubgroup A l⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) =
      conjSubgroup (⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) l := by
  have hV : conjSubgroup V l = V := by
    ext x
    rw [mem_conjSubgroup_iff]
    exact ((Subgroup.mem_normalizer_iff.mp hlV) x).symm
  have key : ∀ y ∈ Subgroup.centralizer (L : Set G), l * y * l⁻¹ = y := fun y hy => by
    rw [Subgroup.mem_centralizer_iff.mp hy l hl, mul_inv_cancel_right]
  have hC : conjSubgroup (V ⊓ Subgroup.centralizer (L : Set G)) l =
      V ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    rw [mem_conjSubgroup_iff]
    constructor
    · intro h
      have hy := key _ (Subgroup.mem_inf.mp h).2
      have hx : x = l * x * l⁻¹ := by
        calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
          _ = l⁻¹ * (l * (l * x * l⁻¹) * l⁻¹) * l := by rw [hy]
          _ = l * x * l⁻¹ := by group
      rw [hx]
      exact h
    · intro h
      rw [key x (Subgroup.mem_inf.mp h).2]
      exact h
  have hV' : V.map (MulAut.conj l⁻¹).toMonoidHom = V := hV
  have hC' : (V ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj l⁻¹).toMonoidHom =
      V ⊓ Subgroup.centralizer (L : Set G) := hC
  show ⁅V, A.map (MulAut.conj l⁻¹).toMonoidHom⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) =
    (⁅V, A⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G))).map (MulAut.conj l⁻¹).toMonoidHom
  rw [Subgroup.map_sup, Subgroup.map_commutator, hV', hC']

theorem conjSubgroup_eq_of {Q : Subgroup G} {l : G} (hV₁V : V₁ ≤ V) (hQV : Q ≤ V)
    (hlV : l ∈ Subgroup.normalizer (V : Set G)) (h : ∀ v ∈ V, v ∈ V₁ ↔ l * v * l⁻¹ ∈ Q) :
    conjSubgroup Q l = V₁ := by
  ext x
  rw [mem_conjSubgroup_iff]
  by_cases hx : x ∈ V
  · exact (h x hx).symm
  · exact ⟨fun h' => absurd ((Subgroup.mem_normalizer_iff.mp hlV x).mpr (hQV h')) hx,
      fun h' => absurd (hV₁V h') hx⟩

theorem le_mQuot_of_aSet [IsMulCommutative ↥V] (hV : IsElemAbelian 2 V) {A : Subgroup G}
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hA : autI hV A ∈ E3.aSet n (autI hV X)) :
    n ≤ E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) := by
  by_contra hlt
  push Not at hlt
  have hA' : autOn A V ∈ E3.aSet n (autOn X V) := hA
  have hm : E3.mQuot (autOn A V) ⊥ < n := by
    unfold E3.mQuot at hlt ⊢
    rwa [Subgroup.relIndex_bot_left, card_autOn_eq_relIndex hAV]
  have hfix := hA'.2.2.2 ⊥ bot_le hm
  apply hA'.2.1
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  ext v
  have hv : v ∈ fixV (⊥ : Subgroup (MulAut ↥V)) := fun x hx => by
    rw [Subgroup.mem_bot.mp hx]
    rfl
  rw [hfix] at hv
  exact congrArg Subtype.val (hv φ hφ)

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
