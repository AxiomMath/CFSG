module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFAct
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.StandardType
open CFSG.RankThree.OrthogonalInvolutions

theorem omqnf_vanish_of_involution {n : ℕ} {K : Type*} [Field K] [CharP K 2] {b c : K}
    {π : Equiv.Perm (Fin (n - 1))} (hπ : π * π = 1) {T : Vm n K ≃ₗ[K] Vm n K}
    (h : omqnfActs n b c π (1 : Fin (n - 1) → ℤ) T) :
    ∀ x ∈ commSpace T, quadMinus n K b c x = 0 := by
  have hππ : ∀ a, π (π a) = a := fun a => by
    have := congrArg (fun p : Equiv.Perm _ => p a) hπ
    simpa [Equiv.Perm.mul_apply] using this
  let τ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
    | .inl a => .inl (π a)
    | .inr (.inl a) => .inr (.inl (π a))
    | .inr (.inr t) => .inr (.inr t)
  have hτ : ∀ j, τ (τ j) = j := by
    intro j; rcases j with a | a | t <;> simp [τ, hππ]
  have hTsingle : ∀ j, T (Pi.single j 1) = Pi.single (τ j) 1 := by
    intro j
    rcases j with a | a | t
    · have := h.1 (Sum.inl a)
      rw [spMonoPerm_inl] at this
      simpa [omqnfFrame, eVec, τ] using this
    · have := h.1 (Sum.inr a)
      rw [spMonoPerm_inr] at this
      simpa [omqnfFrame, fVec, τ] using this
    · have hpl : (Pi.single (Sum.inr (Sum.inr t)) (1 : K) : Vm n K) =
          planeVec n (Pi.single t 1) := by
        funext a
        rcases a with i | i | s <;> simp [planeVec, Pi.single_apply, Sum.inr.injEq]
      have := h.2 (Pi.single t 1)
      simp only [Pi.one_apply, Finset.prod_const_one, if_true] at this
      rw [hpl, this]
  have hTv : ∀ (v : Vm n K) j, T v j = v (τ j) := by
    intro v j
    have hlin : (LinearMap.proj j).comp (T : Vm n K →ₗ[K] Vm n K) = LinearMap.proj (τ j) := by
      refine LinearMap.pi_ext fun i x => ?_
      have hx : (Pi.single i x : Vm n K) = x • Pi.single i 1 := by
        rw [← Pi.single_smul']
        simp
      rw [hx]
      simp only [LinearMap.comp_apply, LinearMap.coe_proj, Function.eval, LinearEquiv.coe_coe,
        map_smul, hTsingle, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases hji : j = τ i
      · have : τ j = i := by rw [hji, hτ]
        subst hji
        simp [hτ]
      · have : ¬ τ j = i := fun h' => hji (by rw [← h', hτ])
        simp [hji, this]
    exact congrArg (fun f : Vm n K →ₗ[K] K => f v) hlin
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  have hx' : ∀ j, (T v - v) j = v (τ j) - v j := fun j => by
    rw [Pi.sub_apply]
    change T v j - v j = _
    rw [hTv]
  rw [quadMinus_apply]
  have hpl : ∀ t : Fin 2, (T v - v) (.inr (.inr t)) = 0 := fun t => by
    change (T v - v) (.inr (.inr t)) = 0
    rw [hx']
    simp [τ]
  have hpl0 := hpl 0
  have hpl1 := hpl 1
  change (T v - v) (.inr (.inr 0)) = 0 at hpl0
  change (T v - v) (.inr (.inr 1)) = 0 at hpl1
  rw [hpl0, hpl1]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  refine Finset.sum_involution (fun a _ => π a) ?_ ?_ (fun a _ => Finset.mem_univ _)
    (fun a _ => hππ a)
  · intro a _
    have h1 := hx' (.inl a)
    have h2 := hx' (.inr (.inl a))
    have h3 := hx' (.inl (π a))
    have h4 := hx' (.inr (.inl (π a)))
    simp only [τ, hππ] at h1 h2 h3 h4
    change (T v - v) (.inl a) * (T v - v) (.inr (.inl a)) +
      (T v - v) (.inl (π a)) * (T v - v) (.inr (.inl (π a))) = 0
    rw [h1, h2, h3, h4]
    have : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
    calc _ = (v (.inl (π a)) - v (.inl a)) * (v (.inr (.inl (π a))) - v (.inr (.inl a))) +
        (v (.inl (π a)) - v (.inl a)) * (v (.inr (.inl (π a))) - v (.inr (.inl a))) := by ring
      _ = 0 := this _
  · intro a _ hne heq
    apply hne
    have h1 := hx' (.inl a)
    have h2 := hx' (.inr (.inl a))
    simp only [τ, heq, sub_self] at h1 h2
    change (T v - v) (.inl a) * (T v - v) (.inr (.inl a)) = 0
    rw [h1, zero_mul]

theorem omqnf_nonvanish_of_flip {n : ℕ} {K : Type*} [Field K] {b c : K}
    {s : Fin (n - 1) → ℤ} {a : Fin (n - 1)} (ha : s a = -1) {T : Vm n K ≃ₗ[K] Vm n K}
    (h : omqnfActs n b c (1 : Equiv.Perm (Fin (n - 1))) s T) :
    ∃ x ∈ commSpace T, quadMinus n K b c x ≠ 0 := by
  refine ⟨T (eVec n a) - eVec n a, sub_mem_commSpace T _, ?_⟩
  have h1 : T (eVec n a) = fVec n a := by
    have := h.1 (Sum.inl a)
    rw [spMonoPerm_inl, if_neg (by rw [ha]; norm_num)] at this
    exact this
  rw [h1, sub_eq_add_neg, ← neg_one_smul K (eVec n a : Vm n K),
    QuadraticMap.map_add (quadMinus n K b c), QuadraticMap.map_smul (quadMinus n K b c),
    quadMinus_fVec, quadMinus_eVec, QuadraticMap.polar_smul_right, polar_fVec_eVec]
  simp

end CFSG.LocalAnalysis.WeakClosure81
