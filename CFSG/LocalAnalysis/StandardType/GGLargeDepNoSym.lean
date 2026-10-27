module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymAug
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymDims

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLargeDep_noSym {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) (hconn : GGLargeConnected r s)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) (hρ : GGLargeRestr r s hA) :
    ¬ ((¬ p ∣ Module.finrank (ZMod p) ↥(ggFixLineT r s) + 1 ∧
        ∃ e : ↥(ggLargeRho r s hA).range ≃*
            Equiv.Perm (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 1)),
          ∀ q : ↥(ggLargeRho r s hA).range,
            GGLinRefl (q : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) →
              ∃ i j, i ≠ j ∧ e q = Equiv.swap i j) ∨
      (p ∣ Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2 ∧
        ∃ e : ↥(ggLargeRho r s hA).range ≃*
            Equiv.Perm (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2)),
          ∀ q : ↥(ggLargeRho r s hA).range,
            GGLinRefl (q : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) →
              ∃ i j, i ≠ j ∧ e q = Equiv.swap i j)) := by
  classical
  have hN : 11 ≤ N := C.lin.N_ge
  have hN2 : 2 ≤ N := by omega
  have : Finite T := C.lin.finT
  have : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) (s := s) C.lin.s_refl C.lin.fix_s
  have : Finite V := l04fD5_finite_of_moduleFinite (p := p)
  have : Finite (V ≃ₗ[ZMod p] V) := Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (congrFun h))
  have : Finite ↥(ggFixLineT r s) := Subtype.finite
  have : Finite (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) := Finite.of_injective (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) =>
      (e : ↥(ggFixLineT r s) → ↥(ggFixLineT r s)))
      (fun e1 e2 h => LinearEquiv.ext (congrFun h))
  obtain ⟨⟨hTlow, hTup⟩, hVdim, hFdim, _hsup⟩ := l04fD5_dims C
  let P : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r)
  let A : Subgroup (V ≃ₗ[ZMod p] V) := ggLargeGrp r s
  let Q : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) := (ggLargeRho r s hA).range
  have : Finite ↥Q := Subtype.finite
  have hPA : P ≤ A := Subgroup.closure_mono (Set.subset_union_left)
  have hρinj : Function.Injective (ggLargeRho r s hA) := hρ.1
  have hcardP : Nat.card ↥P = N.factorial := by
    have hN1 : 1 ≤ N := by omega
    have h := l04fD5_P_card (p := p) (m := N - 1) C.lin.p_ne_two
      (by omega : 5 ≤ (N - 1) + 1) (V := V) (h := h) (α := α) (r := r)
      C.lin.pair C.lin.refl_form
    simpa [Nat.sub_add_cancel hN1] using h
  intro hdisj
  rcases hdisj with ⟨hndvd, e, he⟩ | ⟨hdvd, e, he⟩
  · rcases (by omega : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 2 ∨ Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 1 ∨ Module.finrank (ZMod p) ↥(ggFixLineT r s) = N) with hn | hn | hn
    · let ρP := (ggLargeRho r s hA).comp (Subgroup.inclusion hPA)
      have hρPinj : Function.Injective ρP := by
        intro a b hab
        exact Subtype.ext (congrArg (fun g : ↥A => (g : V ≃ₗ[ZMod p] V)) (hρinj hab))
      have hcardρP : Nat.card ↥ρP.range = N.factorial := by
        change Nat.card ↥(Set.range (⇑ρP)) = N.factorial
        calc Nat.card ↥(Set.range (⇑ρP)) = Nat.card ↥P := (Nat.card_congr (Equiv.ofInjective (⇑ρP) hρPinj)).symm
          _ = N.factorial := hcardP
      have hle : ρP.range ≤ Q := by
        rintro _ ⟨a, rfl⟩
        exact ⟨Subgroup.inclusion hPA a, rfl⟩
      have hcardQle : Nat.card ↥ρP.range ≤ Nat.card ↥Q := Nat.card_le_card_of_injective (fun y : ↥ρP.range => (⟨y.1, hle y.2⟩ : ↥Q))
          (fun x y hxy => Subtype.ext (congrArg (fun z : ↥Q =>
            (z : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))) hxy))
      have hcardQ : Nat.card ↥Q = (N - 1).factorial := by
        calc Nat.card ↥Q = Nat.card (Equiv.Perm
                (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 1))) := Nat.card_congr e.toEquiv
          _ = (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 1).factorial := by rw [Nat.card_perm, Nat.card_fin]
          _ = (N - 1).factorial := by
                have h1 : Module.finrank (ZMod p) ↥(ggFixLineT r s) + 1 = N - 1 := by omega
                rw [h1]
      have hcontra : N.factorial ≤ (N - 1).factorial := by
        calc N.factorial = Nat.card ↥ρP.range := hcardρP.symm
          _ ≤ Nat.card ↥Q := hcardQle
          _ = (N - 1).factorial := hcardQ
      have hlt : (N - 1).factorial < N.factorial := Nat.factorial_lt_of_lt (by omega) (by omega)
      omega
    · apply hndvd
      rw [hn]
      have heq : N - 1 + 1 = N := by omega
      rw [heq]
      exact C.lin.p_dvd
    · exact ggLargeDep_noSym_aug C hconn hA hρ hn e he
  · rcases (by omega : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 2 ∨ Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 1 ∨ Module.finrank (ZMod p) ↥(ggFixLineT r s) = N) with hn | hn | hn
    · have hcardA : Nat.card ↥A = Nat.card ↥Q := by
        change Nat.card ↥A = Nat.card ↥(Set.range (⇑(ggLargeRho r s hA)))
        exact Nat.card_congr (Equiv.ofInjective (⇑(ggLargeRho r s hA)) hρinj)
      have hcardQ : Nat.card ↥Q = N.factorial := by
        calc Nat.card ↥Q = Nat.card (Equiv.Perm
                (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2))) := Nat.card_congr e.toEquiv
          _ = (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2).factorial := by rw [Nat.card_perm, Nat.card_fin]
          _ = N.factorial := by
                have h1 : Module.finrank (ZMod p) ↥(ggFixLineT r s) + 2 = N := by omega
                rw [h1]
      have hcardA' : Nat.card ↥A = N.factorial := hcardA.trans hcardQ
      have hPAeq : P = A := Subgroup.eq_of_le_of_card_ge hPA (by rw [hcardA', hcardP])
      have hFle : ggLinFix (Set.range r) ≤ Submodule.span (ZMod p) ({x} : Set V) := by
        intro v hv
        rw [← C.lin.fix_s]
        intro a ha
        obtain ⟨k, rfl⟩ := ha
        have hskA : s k ∈ A := Subgroup.subset_closure (Or.inr ⟨k, rfl⟩)
        have hskP : s k ∈ P := by rw [hPAeq]; exact hskA
        have hfixP : ∀ g ∈ P, g v = v := by
          intro g hg
          change g ∈ Subgroup.closure (Set.range r) at hg
          refine Subgroup.closure_induction (p := fun g _ => g v = v) ?_ ?_ ?_ ?_ hg
          · rintro g ⟨i, rfl⟩
            exact hv (r i) ⟨i, rfl⟩
          · simp
          · intro a b ha hb iha ihb
            rw [LinearEquiv.mul_apply, ihb, iha]
          · intro a ha iha
            apply a.injective
            exact (LinearEquiv.apply_symm_apply a v).trans iha.symm
        exact hfixP (s k) hskP
      have hFle1 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 1 := by
        have h1 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({x} : Set V)) := Submodule.finrank_mono hFle
        have h2 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({x} : Set V)) = 1 := by simpa using finrank_span_singleton (K := ZMod p) C.lin.x_ne
        omega
      omega
    · have hN1 : p ∣ N + 1 := by
        have h := hdvd
        rw [hn] at h
        have heq : (N - 1) + 2 = N + 1 := by omega
        rwa [heq] at h
      have hp1 : p ∣ 1 := by
        have h := Nat.dvd_sub hN1 C.lin.p_dvd
        have heq : (N + 1) - N = 1 := by omega
        rwa [heq] at h
      exact (Fact.out : p.Prime).not_dvd_one hp1
    · have hN2dvd : p ∣ N + 2 := by
        have h := hdvd
        rw [hn] at h
        exact h
      have hp2dvd : p ∣ 2 := by
        have h := Nat.dvd_sub hN2dvd C.lin.p_dvd
        have heq : (N + 2) - N = 2 := by omega
        rwa [heq] at h
      have hp2eq : p = 2 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp2dvd
      exact C.lin.p_ne_two hp2eq

end CFSG.StandardType

end
