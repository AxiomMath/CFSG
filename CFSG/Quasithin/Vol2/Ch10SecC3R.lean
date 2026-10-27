module

public import CFSG.Quasithin.Vol2.Ch10SecC3M

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def IsKClosed (S : Subgroup (WM K)) : Prop :=
  ∀ (c : K) (X : WM K), X ∈ S → Multiplicative.ofAdd (c • Multiplicative.toAdd X) ∈ S

theorem isKClosed_fixV {A : Subgroup (MulAut (WM K))} (hA : A ≤ linSub K) :
    IsKClosed (fixV A) := by
  intro c X hX a ha
  rw [(hA ha) c X, hX a ha]
  rfl

theorem card_WM [Finite K] : Nat.card (WM K) = Nat.card K ^ 4 := by
  have h : Nat.card (WM K) = Nat.card (Fin 2 → Fin 2 → K) := rfl
  rw [h, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
    ← pow_mul]

theorem card_mul_le_of_ne_top [Finite K] {S : Subgroup (WM K)} (hS : IsKClosed S)
    (hne : S ≠ ⊤) : Nat.card S * Nat.card K ≤ Nat.card K ^ 4 := by
  obtain ⟨v, hv⟩ : ∃ v : WM K, v ∉ S := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.mpr fun x _ => h x)
  let φ : ↥S × K → WM K := fun p => (p.1 : WM K) *
    Multiplicative.ofAdd (p.2 • Multiplicative.toAdd v)
  have hφ : Function.Injective φ := by
    rintro ⟨s, c⟩ ⟨s', c'⟩ h
    have h1 : Multiplicative.toAdd (s : WM K) + c • Multiplicative.toAdd v =
        Multiplicative.toAdd (s' : WM K) + c' • Multiplicative.toAdd v :=
      congrArg Multiplicative.toAdd h
    have hc : c = c' := by
      by_contra hcc
      have hd : c - c' ≠ 0 := sub_ne_zero.mpr hcc
      have hcv : c • Multiplicative.toAdd v = Multiplicative.toAdd (s' : WM K) +
          c' • Multiplicative.toAdd v - Multiplicative.toAdd (s : WM K) := by
        rw [← h1]
        abel
      have h2 : (c - c') • Multiplicative.toAdd v =
          Multiplicative.toAdd (s' : WM K) - Multiplicative.toAdd (s : WM K) := by
        rw [sub_smul, hcv]
        abel
      have h3 : Multiplicative.ofAdd ((c - c')⁻¹ • (Multiplicative.toAdd (s' : WM K) -
          Multiplicative.toAdd (s : WM K))) ∈ S :=
        hS _ _ (S.div_mem s'.2 s.2)
      rw [← h2, smul_smul, inv_mul_cancel₀ hd, one_smul] at h3
      exact hv h3
    subst hc
    have h4 : Multiplicative.toAdd (s : WM K) = Multiplicative.toAdd (s' : WM K) :=
      add_right_cancel h1
    exact Prod.ext (Subtype.ext (Multiplicative.toAdd.injective h4)) rfl
  have h1 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, card_WM] at h1

theorem card_sq_le [Finite K] {W : Subgroup (WM K)} (hW : IsKClosed W) {a : MulAut (WM K)}
    {σ : K ≃+* K} (ha : IsSemilin a σ) (hσ : σ ≠ 1) :
    Nat.card ↥(W ⊓ fixV (Subgroup.zpowers a)) ^ 2 ≤ Nat.card W := by
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  set C := W ⊓ fixV (Subgroup.zpowers a) with hC
  have hfix : ∀ X ∈ C, a X = X := fun X hX => hX.2 a (Subgroup.mem_zpowers a)
  let φ : ↥C × ↥C → ↥W := fun p => ⟨(p.1 : WM K) *
    Multiplicative.ofAdd (c • Multiplicative.toAdd (p.2 : WM K)), W.mul_mem p.1.2.1
      (hW c _ p.2.2.1)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    have h1 : Multiplicative.toAdd (u : WM K) + c • Multiplicative.toAdd (v : WM K) =
        Multiplicative.toAdd (u' : WM K) + c • Multiplicative.toAdd (v' : WM K) :=
      congrArg (fun z : ↥W => Multiplicative.toAdd (z : WM K)) h
    set w : WM K := (v : WM K) / v' with hw
    have hwC : w ∈ C := C.div_mem v.2 v'.2
    have hcw : Multiplicative.ofAdd (c • Multiplicative.toAdd w) = (u' : WM K) / u := by
      apply Multiplicative.toAdd.injective
      have hcv : c • Multiplicative.toAdd (v : WM K) = Multiplicative.toAdd (u' : WM K) +
          c • Multiplicative.toAdd (v' : WM K) - Multiplicative.toAdd (u : WM K) := by
        rw [← h1]
        abel
      rw [toAdd_ofAdd, hw, toAdd_div, toAdd_div, smul_sub, hcv]
      abel
    have hcwC : Multiplicative.ofAdd (c • Multiplicative.toAdd w) ∈ C := by
      rw [hcw]
      exact C.div_mem u'.2 u.2
    have h2 := hfix _ hcwC
    rw [ha, hfix w hwC] at h2
    have h3 : (σ c - c) • Multiplicative.toAdd w = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact congrArg Multiplicative.toAdd h2
    have hw0 : Multiplicative.toAdd w = 0 :=
      (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc)
    have hvv : (v : WM K) = v' := by
      have : w = 1 := Multiplicative.toAdd.injective hw0
      exact div_eq_one.mp this
    have huu : Multiplicative.toAdd (u : WM K) = Multiplicative.toAdd (u' : WM K) := by
      rw [hvv] at h1
      exact add_right_cancel h1
    exact Prod.ext (Subtype.ext (Multiplicative.toAdd.injective huu)) (Subtype.ext hvv)
  have h1 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, ← sq] at h1

end CFSG.Quasithin.Vol2.Ch10.C3.Om
