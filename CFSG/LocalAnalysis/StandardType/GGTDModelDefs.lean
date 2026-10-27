module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggTDTg {K : Type} [Field K] (μ : Subgroup Kˣ) (N : ℕ) :
    Subgroup (Fin (N + 1) → Kˣ) where
  carrier := {t | (∀ i, t i ∈ μ) ∧ ∏ i, t i = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨fun i => μ.mul_mem (ha i) (hb i), ?_⟩
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, ha1, hb1, mul_one]
  one_mem' := ⟨fun i => μ.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨fun i => μ.inv_mem (ha i), ?_⟩
    simp only [Pi.inv_apply, Finset.prod_inv_distrib, ha1, inv_one]

@[expose] def ggTDpvFun {K : Type} [Field K] (N : ℕ) (k : Fin N) (ζ : Kˣ) : Fin (N + 1) → Kˣ :=
  Pi.mulSingle k.castSucc ζ * Pi.mulSingle k.succ ζ⁻¹

@[expose] def ggTDpv {K : Type} [Field K] (μ : Subgroup Kˣ) (N : ℕ) (k : Fin N) :
    μ →* ggTDTg μ N where
  toFun ζ := ⟨ggTDpvFun N k (ζ : Kˣ), by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [ggTDpvFun, Pi.mul_apply, Pi.mulSingle_apply]
      split_ifs
      · exact μ.mul_mem ζ.2 (μ.inv_mem ζ.2)
      · simpa using ζ.2
      · simpa using μ.inv_mem ζ.2
      · simpa using μ.one_mem
    · simp [ggTDpvFun, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle']⟩
  map_one' := Subtype.ext (by ext i; simp [ggTDpvFun])
  map_mul' ζ ξ := Subtype.ext (by
    show ggTDpvFun N k ((ζ : Kˣ) * (ξ : Kˣ)) = ggTDpvFun N k (ζ : Kˣ) * ggTDpvFun N k (ξ : Kˣ)
    simp only [ggTDpvFun, Pi.mulSingle_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

structure GGTDModel (K : Type) [Field K] (N m : ℕ) (L' : Type) [Group L'] where
  μ : Subgroup Kˣ
  ι : μ ≃* Multiplicative (ZMod m)
  H : Type
  [grp : Group H]
  φ : H →* L'
  surj : Function.Surjective φ
  Act : MulAut L' → (Fin (N + 1) → Kˣ) → Prop
  act_one : Act 1 1
  act_mul : ∀ {a b : MulAut L'} {t u : Fin (N + 1) → Kˣ}, Act a t → Act b u → Act (a * b) (t * u)
  act_inv : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t → Act a⁻¹ t⁻¹
  act_unique : ∀ {a b : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t → Act b t → a = b
  act_ratio : ∀ {a : MulAut L'} {t u : Fin (N + 1) → Kˣ}, Act a t → Act a u →
    ∃ c : Kˣ, ∀ i, u i = c * t i
  act_const : ∀ {a : MulAut L'} (c : Kˣ), Act a (fun _ => c) → a = 1
  act_ratio_mem : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t → ∀ i j, t i / t j ∈ μ
  dgm : ggTDTg μ N →* H
  act_dgm : ∀ s : ggTDTg μ N, Act (MulAut.conj (φ (dgm s))) (s : Fin (N + 1) → Kˣ)
  act_fix : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ}, Act a t → ∀ s : ggTDTg μ N,
    a (φ (dgm s)) = φ (dgm s)
  ker_dgm : ∀ s : ggTDTg μ N, φ (dgm s) = 1 → ∃ c : Kˣ, ∀ i, (s : Fin (N + 1) → Kˣ) i = c
  Pm : Equiv.Perm (Fin (N + 1)) → H
  act_perm : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ} (σ : Equiv.Perm (Fin (N + 1))), Act a t →
    Act (MulAut.conj (φ (Pm σ)) * a * (MulAut.conj (φ (Pm σ)))⁻¹) (fun i => t (σ i))
  act_apply_perm : ∀ {a : MulAut L'} {t : Fin (N + 1) → Kˣ} (σ : Equiv.Perm (Fin (N + 1)))
    (s : ggTDTg μ N), Act a t → (∀ i, (s : Fin (N + 1) → Kˣ) i = t i / t (σ i)) →
    a (φ (Pm σ)) = φ (dgm s * Pm σ)
  inner_diag : ∀ (g : H) {t : Fin (N + 1) → Kˣ}, Act (MulAut.conj (φ g)) t →
    ∃ s : ggTDTg μ N, ∃ z ∈ Subgroup.center L', φ g = φ (dgm s) * z
  central_diag : ∀ z ∈ Subgroup.center L', Odd (orderOf z) → ∃ s : ggTDTg μ N, z = φ (dgm s)
  cent_diag : ∀ {ζ : Kˣ}, ζ ∈ μ → ζ ≠ ζ⁻¹ → ∀ g : H,
    (∀ k l : Fin (N + 1), k ≠ l → ∀ s : ggTDTg μ N,
      (s : Fin (N + 1) → Kˣ) = Pi.mulSingle k ζ * Pi.mulSingle l ζ⁻¹ →
      MulAut.conj (φ g) * MulAut.conj (φ (dgm s)) =
        MulAut.conj (φ (dgm s)) * MulAut.conj (φ g)) →
    ∃ s : ggTDTg μ N, ∃ z ∈ Subgroup.center L', φ g = φ (dgm s) * z
  heart_mem : ∀ {p : ℕ} {A : Subgroup (MulAut L')}, GGTorusSelfCent p A →
    (∀ a ∈ A, ∃ t, Act a t) → ∀ s : ggTDTg μ N, (∀ i, (s : Fin (N + 1) → Kˣ) i ^ p = 1) →
    MulAut.conj (φ (dgm s)) ∈ A

attribute [instance] GGTDModel.grp

section Wit

variable {K : Type} [Field K] {N m : ℕ} {L' : Type} [Group L']

@[expose] def ggTDT (M : GGTDModel K N m L') : Subgroup (MulAut L') where
  carrier := {a | ∃ t, M.Act a t}
  mul_mem' := by
    rintro a b ⟨t, ht⟩ ⟨u, hu⟩
    exact ⟨t * u, M.act_mul ht hu⟩
  one_mem' := ⟨1, M.act_one⟩
  inv_mem' := by
    rintro a ⟨t, ht⟩
    exact ⟨t⁻¹, M.act_inv ht⟩

open Classical in
@[expose] noncomputable def ggTDroot (M : GGTDModel K N m L') (k : Fin N) (a : MulAut L') :
    Multiplicative (ZMod m) :=
  if h : ∃ t, M.Act a t then
    M.ι ⟨(Classical.choose h) k.castSucc / (Classical.choose h) k.succ,
      M.act_ratio_mem (Classical.choose_spec h) _ _⟩
  else 1

@[expose] def ggTDcor (M : GGTDModel K N m L') (k : Fin N) : Multiplicative (ZMod m) →* L' :=
  (M.φ.comp (M.dgm.comp (ggTDpv M.μ N k))).comp M.ι.symm.toMonoidHom

@[expose] def ggTDn (M : GGTDModel K N m L') (k : Fin N) : L' :=
  M.φ (M.Pm (Equiv.swap k.castSucc k.succ))

@[expose] noncomputable def ggTDwit (M : GGTDModel K N m L') (A : Subgroup (MulAut L'))
    (hN : ∀ σ, MulAut.conj (M.φ (M.Pm σ)) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    GGTorusTorWit m N L' A where
  T := ggTDT M
  α := ggTDroot M
  cor := ggTDcor M
  n := ggTDn M
  hn := fun _ => hN _
  Tsc := (M.φ.comp M.dgm).range

end Wit

section Parts

variable {m N : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}

@[expose] def GGTDHoldsOne (w : GGTorusTorWit m N L' A) (C : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  (∀ x ∈ w.T, ∀ y ∈ w.T, x * y = y * x) ∧
  A ≤ w.T ∧
  (∀ k ζ, MulAut.conj (w.cor k ζ) ∈ w.T) ∧
  (∀ j, ∀ x ∈ w.T, ∀ y ∈ w.T, w.α j (x * y) = w.α j x * w.α j y) ∧
  (∀ k, Function.Injective (w.cor k)) ∧
  (∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) ∧
  (∀ τ ∈ w.T, ∀ k ζ, τ (w.cor k ζ) = w.cor k ζ) ∧
  (∀ i j ζ, w.α i (MulAut.conj (w.cor j ζ)) = ζ ^ C i j)

@[expose] def GGTDHoldsTwo (w : GGTorusTorWit m N L' A) : Prop :=
  (∀ k, ∀ τ ∈ w.T, MulAut.conj (w.n k) * τ * (MulAut.conj (w.n k))⁻¹ =
    τ * (MulAut.conj (w.cor k (w.α k τ)))⁻¹) ∧
  (∀ k, ∀ τ ∈ w.T, w.n k * (τ (w.n k))⁻¹ = (w.cor k (w.α k τ))⁻¹) ∧
  (∀ τ ∈ w.T, (∀ k, w.α k τ = 1) → τ = 1) ∧
  (∀ k, ∃ a ∈ A, w.α k a ≠ 1)

@[expose] def GGTDHoldsThree (w : GGTorusTorWit m N L' A) : Prop :=
  (∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range →
    ∃ t ∈ ⨆ k, (w.cor k).range, a = MulAut.conj t) ∧
  (∀ z ∈ Subgroup.center L', Odd (orderOf z) → z ∈ w.Tsc) ∧
  ((∀ g : L', (∀ a ∈ A, MulAut.conj g * a = a * MulAut.conj g) →
    g ∈ w.Tsc ⊔ Subgroup.center L') ∧
    (∀ τ ∈ w.T, ∀ t ∈ w.Tsc, τ t = t) ∧
    (∀ t ∈ w.Tsc, t ^ m = 1 → t ∈ ⨆ k, (w.cor k).range))

@[expose] def GGTDHoldsFour (w : GGTorusTorWit m N L' A) (M : CoxeterMatrix (Fin N)) : Prop :=
  ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
    Subgroup.closure (Set.range fun k => ggConjAut A (w.hn k)) ∧
  ∃ e : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
    ∀ k, (e (M.simple k) : MulAut ↥A) = ggConjAut A (w.hn k)

theorem ggTDHolds_of_parts {w : GGTorusTorWit m N L' A} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (h1 : GGTDHoldsOne w C) (h2 : GGTDHoldsTwo w)
    (h3 : GGTDHoldsThree w) (h4 : GGTDHoldsFour w M) : w.Holds C M := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h1
  obtain ⟨c9, c10, c11, c12⟩ := h2
  obtain ⟨c13, c14, c15⟩ := h3
  obtain ⟨c16, c17⟩ := h4
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩

end Parts

end CFSG.StandardType
