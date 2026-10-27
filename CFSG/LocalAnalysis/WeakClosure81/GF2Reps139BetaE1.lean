module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaE1Aux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

theorem centralizer_eq_bot_of_cost_one {M : Type} [CommGroup M] [Finite M]
    (hM2 : ∀ m : M, m ^ 2 = 1) {K : Subgroup (MulAut M)} (hperf : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥)
    (hirr : IsIrrOn K ⊤ ⊥) {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K)
    (hcost : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 1) :
    Subgroup.centralizer (K : Set (MulAut M)) = ⊥ := by
  classical
  letI : Module (ZMod 2) (Additive M) := addModTwo hM2
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  have hcomm : ∀ k ∈ K, c * k = k * c := by
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp hc k hk).symm
  haveI : Nontrivial M := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact absurd (Subsingleton.elim (⊥ : Subgroup M) ⊤) (ne_of_lt hirr.1)
  have h0 : (0 : w1369E hM2 K) ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ : ∃ m : M, m ≠ 1 := exists_ne 1
    have h' : (0 : Module.End (ZMod 2) (Additive M)) = 1 := Subtype.ext_iff.mp h
    have h2 := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f (Additive.ofMul m)) h'
    rw [LinearMap.zero_apply, Module.End.one_apply] at h2
    exact hm (Additive.ofMul.injective h2.symm)
  let e : w1369E hM2 K := ⟨w1369LinHom hM2 c, w1369_linHom_mem_E hM2 hcomm⟩
  haveI : Finite (Module.End (ZMod 2) (Additive M)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (Additive M) =>
      (f : Additive M → Additive M)) DFunLike.coe_injective
  haveI : Finite (w1369E hM2 K) :=
    Finite.of_injective (fun x : w1369E hM2 K => (x : Module.End (ZMod 2) (Additive M)))
      Subtype.val_injective
  have he_ne0 : e ≠ 0 := by
    intro h
    have h' : w1369LinHom hM2 c = 0 := Subtype.ext_iff.mp h
    obtain ⟨m, hm⟩ : ∃ m : M, m ≠ 1 := exists_ne 1
    have h2 := congrArg (fun f : Module.End (ZMod 2) (Additive M) => f (Additive.ofMul m)) h'
    rw [w1369LinHom_ofMul, LinearMap.zero_apply] at h2
    have h3 : c m = 1 := Additive.ofMul.injective (by rw [h2]; rfl)
    exact hm (c.injective (h3.trans (map_one c).symm))
  by_cases hα : ∀ e : w1369E hM2 K, w1369Alpha hM2 hd2 hdN e = e
  · have hcardE := w1369_card_E_le_two hM2 hirr hd2 hdN hcost hα
    rcases w1369_eq_or_eq_of_card_le_two (a := 0) (b := 1) h0 hcardE e with h | h
    · exact absurd h he_ne0
    · have h1 : w1369LinHom hM2 c = 1 := by
        have h2 : (e : Module.End (ZMod 2) (Additive M)) = 1 := by
          rw [h]
          rfl
        exact h2
      exact w1369_linHom_eq_one hM2 h1
  · rw [not_forall] at hα
    obtain ⟨e₁, he₁⟩ := hα
    exact False.elim (w1369_false_of_card_four hM2 hperf hK1
      (w1369_card_eq_four hM2 hirr hd2 hdN hcost ⟨e₁, he₁⟩))

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
