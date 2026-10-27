module

public import CFSG.Timmesfeld.Transvection.OddPairs
import CFSG.Timmesfeld.Transvection.OddPairsCone
import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.Transvection.Pres

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
  (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H) (θ : SU (unitaryInvolution F 2 n) 3 →* H)

theorem closure_range_oddFrameMap_eq_top (htop : Ψ₀.range ⊔ θ.range = ⊤)
    (hlast : (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Universal.Unitary.rootGroup
      (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) (2 * r))
        (cLastIdx r hr)).map Ψ₀ ≤ θ.range) :
    Subgroup.closure (⋃ k, Set.range (oddFrameMap hFn hr Ψ₀ θ (Pi.single k 1)) ∪
      Set.range (oddFrameMap hFn hr Ψ₀ θ (-Pi.single k 1))) = ⊤ := by
  set S := Subgroup.closure (⋃ k, Set.range (oddFrameMap hFn hr Ψ₀ θ (Pi.single k 1)) ∪
    Set.range (oddFrameMap hFn hr Ψ₀ θ (-Pi.single k 1))) with hS
  have hpos : ∀ k, Set.range (oddFrameMap hFn hr Ψ₀ θ (Pi.single k 1)) ⊆ S :=
    fun k _ hy => Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl hy⟩)
  have hneg : ∀ k, Set.range (oddFrameMap hFn hr Ψ₀ θ (-Pi.single k 1)) ⊆ S :=
    fun k _ hy => Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr hy⟩)
  have hθ : θ.range ≤ S := by
    rw [MonoidHom.range_eq_map, ← CFSG.LieType.Steinberg.rankOne_three_eq_top hFn,
      CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · intro x hx
      have hx' : x ∈ ((Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) 3 (Pi.single (0 : Fin (3 / 2)) 1)).map θ :
            Set H) := hx
      rw [← range_oddFrameMap_single_last hFn hr Ψ₀ θ] at hx'
      exact hpos _ hx'
    · intro x hx
      have hx' : x ∈ ((Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) 3 (-Pi.single (0 : Fin (3 / 2)) 1)).map θ :
            Set H) := hx
      rw [← range_oddFrameMap_neg_single_last hFn hr Ψ₀ θ] at hx'
      exact hneg _ hx'
  have hΨ : Ψ₀.range ≤ S := by
    obtain ⟨w, T, hct⟩ := Unitary.exists_isCTGroupDatum hFn (2 * r) (by omega)
    have hall := CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_eq_top_of_ct
      (D := Unitary.rootDatum hFn (2 * r)) hct (if_pos (even_two_mul r))
    rw [MonoidHom.range_eq_map, ← hall, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    by_cases hk : k = cLastIdx r hr
    · subst hk
      exact hlast.trans hθ
    · let k2 : Fin (2 * r / 2) := k
      have hk' : finCastOdd r k2 ≠ bcLastIdx r (Nat.one_le_of_lt hr) := fun h =>
        hk ((finCastOdd r).injective (h.trans (finCastOdd_cLastIdx hr).symm))
      have h1 := range_oddFrameMap_single_of_ne hFn hr Ψ₀ θ (k := finCastOdd r k2) hk'
      have h2 := range_oddFrameMap_neg_single_of_ne hFn hr Ψ₀ θ (k := finCastOdd r k2) hk'
      rw [Equiv.symm_apply_apply] at h1 h2
      rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · intro x hx
        change x ∈ ((Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) (2 * r) (Pi.single k2 1)).map Ψ₀ : Set H) at hx
        exact hpos _ (h1.symm ▸ hx)
      · intro x hx
        change x ∈ ((Unitary.rootGroup (unitaryInvolution F 2 n)
          (unitaryInvolution_involutive hFn) (2 * r) (-Pi.single k2 1)).map Ψ₀ : Set H) at hx
        exact hneg _ (h2.symm ▸ hx)
  rw [eq_top_iff, ← htop]
  exact sup_le hΨ hθ

end CFSG.Timmesfeld.Transvection
