module

public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerForm
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerTorus
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerLift
public import CFSG.LieType.Steinberg.Classical.Symplectic
import CFSG.LocalAnalysis.StandardType.GGStdPosAutWeyl
import CFSG.LocalAnalysis.StandardType.GGStdPosLeviSub
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS
  CFSG.Assembly.LowTwoRank

namespace RootKerC3

private def v3 (P : ℤ × ℤ × ℤ) : Fin 3 → ℤ := ![P.1, P.2.1, P.2.2]

private def R18 : List (ℤ × ℤ × ℤ) :=
  [(1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (0, 1, 1), (1, 1, 1), (1, 2, 1), (0, 2, 1),
    (2, 2, 1), (-1, 0, 0), (0, -1, 0), (-1, -1, 0), (0, 0, -1), (0, -1, -1), (-1, -1, -1),
    (-1, -2, -1), (0, -2, -1), (-2, -2, -1)]

private def prT (P E : ℤ × ℤ × ℤ) : ℤ :=
  E.1 * (2 * P.1 - P.2.1) + E.2.1 * (-P.1 + 2 * P.2.1 - 2 * P.2.2) +
    E.2.2 * (-P.2.1 + 2 * P.2.2)

private def qT (P P' : ℤ × ℤ × ℤ) : ℤ :=
  2 * P.1 * P'.1 - P.1 * P'.2.1 - P.2.1 * P'.1 + 2 * P.2.1 * P'.2.1 - 2 * P.2.1 * P'.2.2 -
    2 * P.2.2 * P'.2.1 + 4 * P.2.2 * P'.2.2

private def reflT (k : Fin 3) (P : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if k = 0 then (P.2.1 - P.1, P.2.1, P.2.2)
  else if k = 1 then (P.1, P.1 - P.2.1 + 2 * P.2.2, P.2.2)
  else (P.1, P.2.1, P.2.1 - P.2.2)

private def T27 : List (ℤ × ℤ × ℤ) :=
  ([-1, 0, 1] : List ℤ).flatMap fun a => ([-1, 0, 1] : List ℤ).flatMap fun b =>
    ([-1, 0, 1] : List ℤ).map fun c => (a, a + b, a + b + c)

private def TV (Q : ℤ × ℤ × ℤ) : List (ℤ × ℤ × ℤ) := T27.filter fun E => prT Q E = 0

private theorem R18_closed : ∀ P ∈ R18, reflT 0 P ∈ R18 ∧ reflT 1 P ∈ R18 ∧ reflT 2 P ∈ R18 := by
  decide

private theorem prT_bound : ∀ P ∈ R18, ∀ E ∈ T27, -2 ≤ prT P E ∧ prT P E ≤ 2 := by
  decide

private theorem comb1_check : ∀ Q ∈ R18, ∀ P ∈ R18, (∀ E ∈ TV Q, prT P E = 0) → P = Q ∨ P = -Q := by
  decide

private theorem comb2_check : ∀ Q ∈ R18, ∀ P ∈ R18, ∀ P' ∈ R18, qT P P = qT P' P' →
    (∀ E ∈ TV Q, (prT P' E - prT P E) % 3 = 0) →
      P' = P ∨ qT Q Q • P' = qT Q Q • P - (2 * qT P Q) • Q := by
  decide

private theorem v3_neg (P : ℤ × ℤ × ℤ) : v3 (-P) = -v3 P := by
  funext j
  fin_cases j <;> rfl

private theorem v3_sub (P Q : ℤ × ℤ × ℤ) : v3 (P - Q) = v3 P - v3 Q := by
  funext j
  fin_cases j <;> rfl

private theorem v3_smul (c : ℤ) (P : ℤ × ℤ × ℤ) : v3 (c • P) = c • v3 P := by
  funext j
  fin_cases j <;> rfl

private theorem coroot_cartanC_three (v : Fin 3 → ℤ) :
    coroot (Symplectic.cartanC 3) 0 v = 2 * v 0 - v 1 ∧
      coroot (Symplectic.cartanC 3) 1 v = -v 0 + 2 * v 1 - 2 * v 2 ∧
        coroot (Symplectic.cartanC 3) 2 v = -v 1 + 2 * v 2 := by
  simp only [coroot_apply, Fin.sum_univ_three, Symplectic.cartanC, Matrix.of_apply]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

private theorem cartanPair_v3 (P E : ℤ × ℤ × ℤ) :
    cartanPair (Symplectic.cartanC 3) (v3 P) (v3 E) = prT P E := by
  obtain ⟨h0, h1, h2⟩ := coroot_cartanC_three (v3 P)
  simp only [cartanPair, Fin.sum_univ_three, h0, h1, h2, prT]
  rfl

private theorem reflection_v3 (k : Fin 3) (P : ℤ × ℤ × ℤ) :
    reflection (Symplectic.cartanC 3) k (v3 P) = v3 (reflT k P) := by
  funext j
  rw [reflection_apply_coroot]
  fin_cases k <;> fin_cases j <;>
    simp [coroot_apply, Fin.sum_univ_three, Symplectic.cartanC, v3, reflT] <;> ring

private theorem mem_R18 (hA : TauCeti.IsFiniteType (Symplectic.cartanC 3)) {β : Fin 3 → ℤ}
    (hβ : β ∈ roots hA ∅) : ∃ P ∈ R18, β = v3 P := by
  rcases hβ with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  swap
  · exact absurd hi (Set.notMem_empty i)
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left with
  | one =>
    rw [map_one, Module.End.one_apply]
    fin_cases i
    · exact ⟨(1, 0, 0), by decide, by funext j; fin_cases j <;> rfl⟩
    · exact ⟨(0, 1, 0), by decide, by funext j; fin_cases j <;> rfl⟩
    · exact ⟨(0, 0, 1), by decide, by funext j; fin_cases j <;> rfl⟩
  | mul_simple_left w k ih =>
    obtain ⟨P, hP, e⟩ := ih
    rw [weylAction_mul_apply, weylAction_simple, e, reflection_v3]
    obtain ⟨h0, h1, h2⟩ := R18_closed P hP
    refine ⟨reflT k P, ?_, rfl⟩
    fin_cases k
    · exact h0
    · exact h1
    · exact h2

private theorem prT_sub (P P' E : ℤ × ℤ × ℤ) : prT (P' - P) E = prT P' E - prT P E := by
  simp only [prT, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem eq_zero_of_dvd_of_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℤ} (h1 : -2 ≤ m)
    (h2 : m ≤ 2) (h : (p : ℤ) ∣ m) : m = 0 := by
  have hp3 : (3 : ℤ) ≤ p := by
    have := hp.two_le
    exact_mod_cast (by omega : 3 ≤ p)
  obtain ⟨t, rfl⟩ := h
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have : t ≤ -1 := by omega
    nlinarith
  · exact mul_zero _
  · have : 1 ≤ t := by omega
    nlinarith

private theorem emod_three_of_dvd_of_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℤ} (h1 : -4 ≤ m)
    (h2 : m ≤ 4) (h : (p : ℤ) ∣ m) : m % 3 = 0 := by
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  obtain ⟨t, rfl⟩ := h
  rcases (by have := hp.two_le; omega : p = 3 ∨ 5 ≤ p) with rfl | hp5
  · exact Int.mul_emod_right 3 t
  · have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have : t ≤ -1 := by omega
      nlinarith
    · rfl
    · have : 1 ≤ t := by omega
      nlinarith

private theorem comb1 (hA : TauCeti.IsFiniteType (Symplectic.cartanC 3)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β γ : Fin 3 → ℤ} (hβ : β ∈ roots hA ∅) (hγ : γ ∈ roots hA ∅)
    (h : ∀ e, (p : ℤ) ∣ cartanPair (Symplectic.cartanC 3) γ e →
      (p : ℤ) ∣ cartanPair (Symplectic.cartanC 3) β e) :
    β = γ ∨ β = -γ := by
  obtain ⟨P, hP, rfl⟩ := mem_R18 hA hβ
  obtain ⟨Q, hQ, rfl⟩ := mem_R18 hA hγ
  have key : ∀ E ∈ TV Q, prT P E = 0 := by
    intro E hE
    obtain ⟨hE1, hE2⟩ := List.mem_filter.mp hE
    have hQE : prT Q E = 0 := of_decide_eq_true hE2
    have hd := h (v3 E) (by rw [cartanPair_v3, hQE]; exact dvd_zero _)
    rw [cartanPair_v3] at hd
    obtain ⟨b1, b2⟩ := prT_bound P hP E hE1
    exact eq_zero_of_dvd_of_two hp hp2 b1 b2 hd
  rcases comb1_check Q hQ P hP key with e | e
  · exact Or.inl (by rw [e])
  · exact Or.inr (by rw [e, v3_neg])

private def Qf (u v : Fin 3 → ℤ) : ℤ := qT (u 0, u 1, u 2) (v 0, v 1, v 2)

private theorem comb2 (hA : TauCeti.IsFiniteType (Symplectic.cartanC 3)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β β' γ : Fin 3 → ℤ} (hβ : β ∈ roots hA ∅) (hβ' : β' ∈ roots hA ∅)
    (hγ : γ ∈ roots hA ∅) (hlen : Qf β β = Qf β' β')
    (h : ∀ e, (p : ℤ) ∣ cartanPair (Symplectic.cartanC 3) γ e →
      (p : ℤ) ∣ cartanPair (Symplectic.cartanC 3) (β' - β) e) :
    β' = β ∨ Qf γ γ • β' = Qf γ γ • β - (2 * Qf β γ) • γ := by
  obtain ⟨P, hP, rfl⟩ := mem_R18 hA hβ
  obtain ⟨P', hP', rfl⟩ := mem_R18 hA hβ'
  obtain ⟨Q, hQ, rfl⟩ := mem_R18 hA hγ
  have key : ∀ E ∈ TV Q, (prT P' E - prT P E) % 3 = 0 := by
    intro E hE
    obtain ⟨hE1, hE2⟩ := List.mem_filter.mp hE
    have hQE : prT Q E = 0 := of_decide_eq_true hE2
    have hd := h (v3 E) (by rw [cartanPair_v3, hQE]; exact dvd_zero _)
    rw [← v3_sub, cartanPair_v3, prT_sub] at hd
    obtain ⟨b1, b2⟩ := prT_bound P hP E hE1
    obtain ⟨b1', b2'⟩ := prT_bound P' hP' E hE1
    exact emod_three_of_dvd_of_four hp hp2 (by linarith) (by linarith) hd
  rcases comb2_check Q hQ P hP P' hP' hlen key with e | e
  · exact Or.inl (by rw [e])
  · right
    have e' := congrArg v3 e
    rw [v3_sub, v3_smul, v3_smul, v3_smul] at e'
    exact e'

private theorem Qf_reflection (k : Fin 3) (u v : Fin 3 → ℤ) :
    Qf (reflection (Symplectic.cartanC 3) k u) (reflection (Symplectic.cartanC 3) k v) =
      Qf u v := by
  simp only [Qf, qT, reflection_apply_coroot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> simp [coroot_apply, Fin.sum_univ_three, Symplectic.cartanC] <;> ring

private theorem Qf_weylAction (hA : TauCeti.IsFiniteType (Symplectic.cartanC 3))
    (w : (coxeterMatrix hA).Group) (u v : Fin 3 → ℤ) :
    Qf (weylAction hA w u) (weylAction hA w v) = Qf u v := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left with
  | one => rw [map_one, Module.End.one_apply, Module.End.one_apply]
  | mul_simple_left w k ih =>
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple, Qf_reflection, ih]

private theorem Qf_smul_sub (a b : ℤ) (x y z : Fin 3 → ℤ) :
    Qf (a • x - b • y) z = a * Qf x z - b * Qf y z := by
  simp only [Qf, qT, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem Qf_smul (a : ℤ) (x z : Fin 3 → ℤ) : Qf (a • x) z = a * Qf x z := by
  simp only [Qf, qT, Pi.smul_apply, smul_eq_mul]
  ring

private theorem Qf_neg_right (x y : Fin 3 → ℤ) : Qf x (-y) = -Qf x y := by
  simp only [Qf, qT, Pi.neg_apply]
  ring

private theorem Qf_single_mul_coroot (i : Fin 3) (x : Fin 3 → ℤ) :
    Qf (Pi.single i 1) (Pi.single i 1) * coroot (Symplectic.cartanC 3) i x =
      2 * Qf x (Pi.single i 1) := by
  fin_cases i <;>
    simp [Qf, qT, coroot_apply, Fin.sum_univ_three, Symplectic.cartanC] <;> ring

private theorem Qf_single_pos (i : Fin 3) : 0 < Qf (Pi.single i 1) (Pi.single i 1) := by
  fin_cases i <;> simp [Qf, qT]

private theorem weylAction_conj_smul (hA : TauCeti.IsFiniteType (Symplectic.cartanC 3))
    (u : (coxeterMatrix hA).Group) (i : Fin 3) (v : Fin 3 → ℤ) :
    Qf (weylAction hA u (Pi.single i 1)) (weylAction hA u (Pi.single i 1)) •
        weylAction hA (u * (coxeterMatrix hA).simple i * u⁻¹) v =
      Qf (weylAction hA u (Pi.single i 1)) (weylAction hA u (Pi.single i 1)) • v -
        (2 * Qf v (weylAction hA u (Pi.single i 1))) • weylAction hA u (Pi.single i 1) := by
  have e : weylAction hA (u * (coxeterMatrix hA).simple i * u⁻¹) v =
      v - coroot (Symplectic.cartanC 3) i (weylAction hA u⁻¹ v) •
        weylAction hA u (Pi.single i 1) := by
    rw [weylAction_mul_apply, weylAction_mul_apply, ← CoxeterMatrix.toCoxeterSystem_simple,
      weylAction_simple, reflection_apply_coroot, map_sub, map_zsmul, weylAction_apply_inv_apply]
  have h1 := Qf_single_mul_coroot i (weylAction hA u⁻¹ v)
  rw [← Qf_weylAction hA u (Pi.single i 1), ← Qf_weylAction hA u (weylAction hA u⁻¹ v),
    weylAction_apply_inv_apply] at h1
  rw [e, smul_sub, smul_smul, h1]

private theorem eq_one_or_conj (hA : TauCeti.IsFiniteType (Symplectic.cartanC 3))
    (u : (coxeterMatrix hA).Group) (i : Fin 3) (w : (coxeterMatrix hA).Group)
    (h : ∀ β ∈ roots hA ∅, weylAction hA w β = β ∨
      Qf (weylAction hA u (Pi.single i 1)) (weylAction hA u (Pi.single i 1)) • weylAction hA w β =
        Qf (weylAction hA u (Pi.single i 1)) (weylAction hA u (Pi.single i 1)) • β -
          (2 * Qf β (weylAction hA u (Pi.single i 1))) • weylAction hA u (Pi.single i 1)) :
    w = 1 ∨ w = u * (coxeterMatrix hA).simple i * u⁻¹ := by
  have hs := weylAction_conj_smul hA u i
  set γ := weylAction hA u (Pi.single i 1) with hγdef
  set c := Qf γ γ with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, hγdef, Qf_weylAction]
    exact (Qf_single_pos i).ne'
  have hcan : ∀ a b : Fin 3 → ℤ, c • a = c • b → a = b := fun a b hab =>
    smul_right_injective _ hc hab
  have hγ : γ ∈ roots hA ∅ := Or.inl ⟨u, i, rfl⟩
  have hsingle : ∀ j : Fin 3, (Pi.single j 1 : Fin 3 → ℤ) ∈ roots hA ∅ := fun j =>
    Or.inl ⟨1, j, by rw [map_one, Module.End.one_apply]⟩
  have hext : ∀ w' : (coxeterMatrix hA).Group,
      (∀ j, weylAction hA w (Pi.single j 1) = weylAction hA w' (Pi.single j 1)) → w = w' :=
    fun w' hw => weylAction_injective hA ((Pi.basisFun ℤ (Fin 3)).ext fun j => by
      rw [Pi.basisFun_apply]
      exact hw j)
  have hrefl : ∀ a, Qf (c • a - (2 * Qf a γ) • γ) γ = -(c * Qf a γ) := fun a => by
    rw [Qf_smul_sub, ← hcdef]
    ring
  rcases h γ hγ with hv | hv
  · left
    refine hext 1 fun j => ?_
    rw [map_one, Module.End.one_apply]
    rcases h _ (hsingle j) with h1 | h1
    · exact h1
    · have hQ : Qf (weylAction hA w (Pi.single j 1)) γ = Qf (Pi.single j 1) γ :=
        calc _ = Qf (weylAction hA w (Pi.single j 1)) (weylAction hA w γ) := by rw [hv]
          _ = _ := Qf_weylAction hA w _ _
      have e1 := congrArg (fun v => Qf v γ) h1
      simp only [Qf_smul, hrefl, hQ] at e1
      have h0 : Qf (Pi.single j 1) γ = 0 := by
        have : c * Qf (Pi.single j 1) γ = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hc
      rw [h0, mul_zero, zero_smul, sub_zero] at h1
      exact hcan _ _ h1
  · right
    have hv' : weylAction hA w γ = -γ := hcan _ _ (by rw [hv]; module)
    refine hext _ fun j => hcan _ _ ?_
    rw [hs]
    rcases h _ (hsingle j) with h1 | h1
    · have hQ : Qf (Pi.single j 1) γ = -Qf (Pi.single j 1) γ :=
        calc Qf (Pi.single j 1) γ =
            Qf (weylAction hA w (Pi.single j 1)) (weylAction hA w γ) :=
              (Qf_weylAction hA w _ _).symm
          _ = _ := by rw [h1, hv', Qf_neg_right]
      have h0 : Qf (Pi.single j 1) γ = 0 := by linarith
      rw [h1, h0, mul_zero, zero_smul, sub_zero]
    · exact h1

end RootKerC3

private theorem ggRootKer_of_comb {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) {p : ℕ} {ζ : kˣ} (hζ : orderOf ζ = p)
    {ν : GGWeyl D →* K} (hν : GGWeylLift D ν) (u : GGWeyl D) (i : Fin D.rank)
    (hc1 : ∀ β ∈ D.roots, (∀ e : Fin D.rank → ℤ,
        (p : ℤ) ∣ cartanPair D.cartan (weylAction D.isFiniteType u (Pi.single i 1)) e →
          (p : ℤ) ∣ cartanPair D.cartan β e) →
      β = weylAction D.isFiniteType u (Pi.single i 1) ∨
        β = -weylAction D.isFiniteType u (Pi.single i 1))
    (hc2 : ∀ w : GGWeyl D, (∀ β ∈ D.roots, ∀ e : Fin D.rank → ℤ,
        (p : ℤ) ∣ cartanPair D.cartan (weylAction D.isFiniteType u (Pi.single i 1)) e →
          (p : ℤ) ∣ cartanPair D.cartan (weylAction D.isFiniteType w β - β) e) →
      w = 1 ∨ w = u * (coxeterMatrix D.isFiniteType).simple i * u⁻¹) :
    (∀ β ∈ D.roots, D.rootGroup β ≤ Subgroup.centralizer
          (ggTorusRootKer D p (weylAction D.isFiniteType u (Pi.single i 1))) →
      β = weylAction D.isFiniteType u (Pi.single i 1) ∨
        β = -weylAction D.isFiniteType u (Pi.single i 1)) ∧
    ∀ w : GGWeyl D, (∀ h ∈ ggTorusRootKer D p (weylAction D.isFiniteType u (Pi.single i 1)),
        ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center K) →
      w = 1 ∨ w = u * (coxeterMatrix D.isFiniteType).simple i * u⁻¹ := by
  set γ := weylAction D.isFiniteType u (Pi.single i 1)
  have hγ : γ ∈ D.roots := weylAction_mem_roots D.isFiniteType u (single_mem_roots i)
  have hord : ∀ m : ℤ, ζ ^ m = 1 ↔ (p : ℤ) ∣ m := fun m => by
    rw [← hζ, orderOf_dvd_iff_zpow_eq_one]
  have hgen : ∀ e : Fin D.rank → ℤ, (p : ℤ) ∣ cartanPair D.cartan γ e →
      ∃ g ∈ ggTorusRootKer D p γ, ∀ β ∈ D.roots, ∀ c : k,
        g * x β c * g⁻¹ = x β (((ζ ^ cartanPair D.cartan β e : kˣ) : k) * c) := by
    intro e he
    obtain ⟨g, hgT, hgp, hg⟩ := ggRootKer_exists_gen hE e (hζ ▸ pow_orderOf_eq_one ζ)
    refine ⟨g, ⟨hgT, hgp, fun z hz => ?_⟩, hg⟩
    obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 z).mp hz
    have h1 : g * x γ c * g⁻¹ = x γ (((ζ ^ cartanPair D.cartan γ e : kˣ) : k) * c) :=
      hg γ hγ c
    rw [(hord _).mpr he, Units.val_one, one_mul] at h1
    have hcg := mul_inv_eq_iff_eq_mul.mp h1
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hcg
  refine ⟨fun β hβ hle => hc1 β hβ fun e he => ?_, fun w hw => hc2 w fun β hβ e he => ?_⟩
  ·
    obtain ⟨g, hgE, hg⟩ := hgen e he
    have hcomm := Subgroup.mem_centralizer_iff.mp
      (hle (((hE.param β hβ).1 _).mpr ⟨1, rfl⟩)) g hgE
    have h1 : x β (((ζ ^ cartanPair D.cartan β e : kˣ) : k) * 1) = x β 1 := by
      rw [← hg β hβ 1, hcomm, mul_inv_cancel_right]
    have h2 := (hE.param β hβ).2.2 h1
    rw [mul_one] at h2
    exact (hord _).mp (Units.ext h2)
  ·
    obtain ⟨a, ha⟩ := ggRootKer_weylLift_conj hE hν w hβ
    have hwβ : weylAction D.isFiniteType w β ∈ D.roots :=
      weylAction_mem_roots D.isFiniteType w hβ
    obtain ⟨g, hgE, hg⟩ := hgen e he
    have hz := Subgroup.mem_center_iff.mp (hw g hgE)
    have e1 : (ν w * g) * x β 1 * (ν w * g)⁻¹ = x (weylAction D.isFiniteType w β)
        ((a : k) * ((ζ ^ cartanPair D.cartan β e : kˣ) : k)) := by
      calc (ν w * g) * x β 1 * (ν w * g)⁻¹ = ν w * (g * x β 1 * g⁻¹) * (ν w)⁻¹ := by group
        _ = _ := by rw [hg β hβ 1, ha, mul_one]
    have e2 : (ν w * g) * x β 1 * (ν w * g)⁻¹ = x (weylAction D.isFiniteType w β)
        (((ζ ^ cartanPair D.cartan (weylAction D.isFiniteType w β) e : kˣ) : k) *
          (a : k)) := by
      set z := ν w * g * (ν w)⁻¹ * g⁻¹
      have hνg : ν w * g = z * g * ν w := by simp only [z]; group
      rw [hνg]
      calc z * g * ν w * x β 1 * (z * g * ν w)⁻¹ =
          z * (g * (ν w * x β 1 * (ν w)⁻¹) * g⁻¹) * z⁻¹ := by group
        _ = z * x (weylAction D.isFiniteType w β)
            (((ζ ^ cartanPair D.cartan (weylAction D.isFiniteType w β) e : kˣ) : k) *
              (a : k)) * z⁻¹ := by rw [ha, mul_one, hg _ hwβ]
        _ = _ := by rw [← hz, mul_inv_cancel_right]
    have h3 := (hE.param _ hwβ).2.2 (e1.symm.trans e2)
    have h4 : ζ ^ cartanPair D.cartan β e =
        ζ ^ cartanPair D.cartan (weylAction D.isFiniteType w β) e :=
      Units.ext (mul_left_cancel₀ a.ne_zero (h3.trans (mul_comm _ _)))
    rw [ggRootKer_cartanPair_sub_left]
    exact (hord _).mp (by rw [zpow_sub, ← h4, mul_inv_cancel])

private theorem ggRootKer_sp3 {F : Type} [Field F]
    {x : (Fin (Symplectic.rootDatum 3 F).rank → ℤ) → F → StatedSp 3 F}
    {C : (Fin (Symplectic.rootDatum 3 F).rank → ℤ) → (Fin (Symplectic.rootDatum 3 F).rank → ℤ) →
      ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan
      (Symplectic.rootDatum 3 F).isFiniteType (Symplectic.rootDatum 3 F).divisible)}
    (hE : ChevalleyExtras (Symplectic.rootDatum 3 F) F x C O) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : Fˣ} (hζ : orderOf ζ = p)
    {ν : GGWeyl (Symplectic.rootDatum 3 F) →* StatedSp 3 F}
    (hν : GGWeylLift (Symplectic.rootDatum 3 F) ν) (u : GGWeyl (Symplectic.rootDatum 3 F))
    (i : Fin (Symplectic.rootDatum 3 F).rank) :
    (∀ β ∈ (Symplectic.rootDatum 3 F).roots, (Symplectic.rootDatum 3 F).rootGroup β ≤
        Subgroup.centralizer (ggTorusRootKer (Symplectic.rootDatum 3 F) p
          (weylAction (Symplectic.rootDatum 3 F).isFiniteType u (Pi.single i 1))) →
      β = weylAction (Symplectic.rootDatum 3 F).isFiniteType u (Pi.single i 1) ∨
        β = -weylAction (Symplectic.rootDatum 3 F).isFiniteType u (Pi.single i 1)) ∧
    ∀ w : GGWeyl (Symplectic.rootDatum 3 F), (∀ h ∈ ggTorusRootKer (Symplectic.rootDatum 3 F) p
        (weylAction (Symplectic.rootDatum 3 F).isFiniteType u (Pi.single i 1)),
        ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center (StatedSp 3 F)) →
      w = 1 ∨ w = u * (coxeterMatrix (Symplectic.rootDatum 3 F).isFiniteType).simple i * u⁻¹ := by
  have hA := (Symplectic.rootDatum 3 F).isFiniteType
  have hγ : weylAction hA u (Pi.single i 1) ∈ roots hA ∅ := Or.inl ⟨u, i, rfl⟩
  refine ggRootKer_of_comb hE hζ hν u i
    (fun β hβ h => RootKerC3.comb1 hA hp hp2 hβ hγ h) fun w hw => ?_
  refine RootKerC3.eq_one_or_conj hA u i w fun β hβ => ?_
  have hwβ : weylAction hA w β ∈ roots hA ∅ := weylAction_mem_roots hA w hβ
  exact RootKerC3.comb2 hA hp hp2 hβ hwβ hγ (RootKerC3.Qf_weylAction hA w β β).symm (hw β hβ)

theorem ggRootKerStmt_PSp3
    {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpf : p ∣ 2 ^ f - 1) (ν : GGWeyl (ggU .PSp 3 f).D →* (ggU .PSp 3 f).K)
    (hν : GGWeylLift (ggU .PSp 3 f).D ν) (u : GGWeyl (ggU .PSp 3 f).D)
    (i : Fin (ggU .PSp 3 f).D.rank) :
    (∀ β ∈ (ggU .PSp 3 f).D.roots, (ggU .PSp 3 f).D.rootGroup β ≤
        Subgroup.centralizer (ggTorusRootKer (ggU .PSp 3 f).D p
          (weylAction (ggU .PSp 3 f).D.isFiniteType u (Pi.single i 1))) →
      β = weylAction (ggU .PSp 3 f).D.isFiniteType u (Pi.single i 1) ∨
        β = -weylAction (ggU .PSp 3 f).D.isFiniteType u (Pi.single i 1)) ∧
    ∀ w : GGWeyl (ggU .PSp 3 f).D, (∀ h ∈ ggTorusRootKer (ggU .PSp 3 f).D p
        (weylAction (ggU .PSp 3 f).D.isFiniteType u (Pi.single i 1)),
        ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center (ggU .PSp 3 f).K) →
      w = 1 ∨ w = u * (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType).simple i * u⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, GaloisField.card 2 f (by omega)]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p (hcard ▸ hpf)
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan
    (Symplectic.rootDatum 3 (GaloisField 2 f)).isFiniteType
    (Dv := (Symplectic.rootDatum 3 (GaloisField 2 f)).divisible) rfl
  exact ggRootKer_sp3 (Sp.chevalleyExtras (by norm_num) O _
    (Sp.commutatorFormula O)) hp hp2 hζ hν u i

end CFSG.StandardType

end
