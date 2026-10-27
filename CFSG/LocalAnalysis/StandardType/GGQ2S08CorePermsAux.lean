module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


@[expose] noncomputable def ggQ2s08k4_permM
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (σ : Equiv.Perm (Fin N)) : V ≃ₗ[ZMod 3] V := f.equiv f σ

theorem ggQ2s08k4_permM_apply
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    ggQ2s08k4_permM f σ (f i) = f (σ i) :=
  Module.Basis.equiv_apply f i f σ

theorem ggQ2s08k4_permM_symm
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (σ : Equiv.Perm (Fin N)) :
    (ggQ2s08k4_permM f σ).symm = ggQ2s08k4_permM f σ.symm := by
  rw [ggQ2s08k4_permM, Module.Basis.equiv_symm, ggQ2s08k4_permM]

@[expose] noncomputable def ggQ2s08k4_diagU
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (u : Fin N → (ZMod 3)ˣ) : V ≃ₗ[ZMod 3] V :=
  f.equiv (f.unitsSMul u) (Equiv.refl (Fin N))

theorem ggQ2s08k4_diagU_apply
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (u : Fin N → (ZMod 3)ˣ) (i : Fin N) :
    ggQ2s08k4_diagU f u (f i) = (u i : ZMod 3) • f i := by
  rw [ggQ2s08k4_diagU, Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply]
  rfl

@[expose] noncomputable def ggQ2s08k4_diag
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (c : Fin N → ZMod 3) (hc : ∀ i, c i ≠ 0) : V ≃ₗ[ZMod 3] V :=
  ggQ2s08k4_diagU f (fun i => Units.mk0 (c i) (hc i))

theorem ggQ2s08k4_diag_apply
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (c : Fin N → ZMod 3) (hc : ∀ i, c i ≠ 0) (i : Fin N) :
    ggQ2s08k4_diag f c hc (f i) = c i • f i := by
  rw [ggQ2s08k4_diag, ggQ2s08k4_diagU_apply, Units.val_mk0]

theorem ggQ2s08k4_diag_congr
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {c c' : Fin N → ZMod 3} (h : c = c')
    (hc : ∀ i, c i ≠ 0) (hc' : ∀ i, c' i ≠ 0) :
    ggQ2s08k4_diag f c hc = ggQ2s08k4_diag f c' hc' := by
  subst h
  rfl

@[expose] noncomputable def ggQ2s08k4_sgn
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (i0 : Fin N) : V ≃ₗ[ZMod 3] V :=
  ggQ2s08k4_diag f (fun k => if k = i0 then (-1 : ZMod 3) else 1)
    (fun k => by split_ifs <;> decide)

theorem ggQ2s08k4_sgn_apply
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (i0 k : Fin N) :
    ggQ2s08k4_sgn f i0 (f k) = (if k = i0 then (-1 : ZMod 3) else 1) • f k := by
  rw [ggQ2s08k4_sgn, ggQ2s08k4_diag_apply]

@[expose] def ggQ2s08k4_signScalar
    {N : ℕ} (S : Finset (Fin N)) : Fin N → ZMod 3 :=
  fun k => if k ∈ S then -1 else 1

theorem ggQ2s08k4_signScalar_ne
    {N : ℕ} (S : Finset (Fin N)) :
    ∀ k, ggQ2s08k4_signScalar S k ≠ 0 := by
  intro k
  simp only [ggQ2s08k4_signScalar]
  by_cases h : k ∈ S <;> simp [h] <;> decide

theorem ggQ2s08k4_signScalar_insert
    {N : ℕ} (a : Fin N) (S : Finset (Fin N))
    (ha : a ∉ S) :
    ggQ2s08k4_signScalar (insert a S) =
      fun k => (if k = a then -1 else 1) * ggQ2s08k4_signScalar S k := by
  funext k
  simp only [ggQ2s08k4_signScalar, Finset.mem_insert]
  by_cases hka : k = a
  · subst hka; simp [ha]
  · simp [hka]

@[expose] def ggQ2s08k4_pairScalar
    {N : ℕ} (i0 j : Fin N) : Fin N → ZMod 3 :=
  fun k => if k = i0 then -1 else if k = j then -1 else 1

theorem ggQ2s08k4_pairScalar_ne
    {N : ℕ} (i0 j : Fin N) :
    ∀ k, ggQ2s08k4_pairScalar i0 j k ≠ 0 := by
  intro k
  simp only [ggQ2s08k4_pairScalar]
  by_cases h1 : k = i0 <;> by_cases h2 : k = j <;> simp [h1, h2] <;> decide

@[expose] noncomputable def ggQ2s08k4_pairDiag
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (i0 j : Fin N) : V ≃ₗ[ZMod 3] V :=
  ggQ2s08k4_diag f (ggQ2s08k4_pairScalar i0 j) (ggQ2s08k4_pairScalar_ne i0 j)

theorem ggQ2s08k4_pairDiag_apply
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (i0 j k : Fin N) :
    ggQ2s08k4_pairDiag f i0 j (f k) =
      ((if k = i0 then (-1 : ZMod 3) else if k = j then (-1 : ZMod 3) else 1) • f k) := by
  rw [ggQ2s08k4_pairDiag, ggQ2s08k4_diag_apply, ggQ2s08k4_pairScalar]

@[expose] def ggQ2s08k4_starScalar
    {N : ℕ} (i0 : Fin N) (T : Finset (Fin N)) :
    Fin N → ZMod 3 :=
  ∏ j ∈ T, ggQ2s08k4_pairScalar i0 j

theorem ggQ2s08k4_starScalar_ne
    {N : ℕ} (i0 : Fin N) (T : Finset (Fin N)) :
    ∀ k, ggQ2s08k4_starScalar i0 T k ≠ 0 := by
  intro k
  simp only [ggQ2s08k4_starScalar]
  rw [Finset.prod_apply]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => ggQ2s08k4_pairScalar_ne i0 j k)

theorem ggQ2s08k4_starScalar_insert
    {N : ℕ} (i0 a : Fin N) (T : Finset (Fin N))
    (ha : a ∉ T) :
    ggQ2s08k4_starScalar i0 (insert a T) =
      ggQ2s08k4_pairScalar i0 a * ggQ2s08k4_starScalar i0 T := by
  rw [ggQ2s08k4_starScalar, Finset.prod_insert ha, ggQ2s08k4_starScalar]

theorem ggQ2s08k4_zmod3_eq_one_or_neg_one
    (a : ZMod 3) (ha : a ≠ 0) :
    a = 1 ∨ a = (-1 : ZMod 3) := by
  revert a
  decide

theorem ggQ2s08k4_starScalar_apply
    {N : ℕ} (i0 : Fin N) (T : Finset (Fin N))
    (hi0 : i0 ∉ T) (k : Fin N) :
    ggQ2s08k4_starScalar i0 T k =
      (if k = i0 then (-1 : ZMod 3) ^ T.card else 1) * (if k ∈ T then -1 else 1) := by
  rw [ggQ2s08k4_starScalar, Finset.prod_apply]
  by_cases hki0 : k = i0
  · subst hki0
    rw [if_pos rfl, if_neg hi0, mul_one]
    trans ∏ _j ∈ T, (-1 : ZMod 3)
    · apply Finset.prod_congr rfl
      intro j _
      simp [ggQ2s08k4_pairScalar]
    · rw [Finset.prod_const]
  · rw [if_neg hki0, one_mul]
    trans ∏ j ∈ T, (if k = j then (-1 : ZMod 3) else 1)
    · apply Finset.prod_congr rfl
      intro j _
      simp [ggQ2s08k4_pairScalar, hki0]
    · rw [Finset.prod_ite_eq]

theorem ggQ2s08k4_eq_of_basis
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {e1 e2 : V ≃ₗ[ZMod 3] V} (h : ∀ i, e1 (f i) = e2 (f i)) : e1 = e2 := by
  apply LinearEquiv.toLinearMap_injective
  apply Module.Basis.ext f
  intro i
  exact h i

theorem ggQ2s08k4_diag_one
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V) :
    ggQ2s08k4_diag f (fun _ => 1) (fun _ => one_ne_zero) = 1 := by
  apply ggQ2s08k4_eq_of_basis
  intro i
  change ggQ2s08k4_diag f (fun _ => 1) (fun _ => one_ne_zero) (f i) = f i
  rw [ggQ2s08k4_diag_apply]
  simp

theorem ggQ2s08k4_sgn_mul_diag_signScalar
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (a : Fin N) (S : Finset (Fin N)) (ha : a ∉ S) :
    ggQ2s08k4_sgn f a * ggQ2s08k4_diag f (ggQ2s08k4_signScalar S)
        (ggQ2s08k4_signScalar_ne S) =
      ggQ2s08k4_diag f (ggQ2s08k4_signScalar (insert a S))
        (ggQ2s08k4_signScalar_ne (insert a S)) := by
  apply ggQ2s08k4_eq_of_basis
  intro k
  change (ggQ2s08k4_sgn f a * ggQ2s08k4_diag f (ggQ2s08k4_signScalar S)
      (ggQ2s08k4_signScalar_ne S)) (f k) = _
  rw [LinearEquiv.mul_apply, ggQ2s08k4_diag_apply, map_smul, ggQ2s08k4_sgn_apply,
    ggQ2s08k4_diag_apply, ggQ2s08k4_signScalar_insert a S ha]
  simp only [Pi.mul_apply]
  rw [smul_smul, mul_comm]

theorem ggQ2s08k4_pairDiag_mul_diag_starScalar
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (i0 a : Fin N) (T : Finset (Fin N)) (ha : a ∉ T) :
    ggQ2s08k4_pairDiag f i0 a * ggQ2s08k4_diag f (ggQ2s08k4_starScalar i0 T)
        (ggQ2s08k4_starScalar_ne i0 T) =
      ggQ2s08k4_diag f (ggQ2s08k4_starScalar i0 (insert a T))
        (ggQ2s08k4_starScalar_ne i0 (insert a T)) := by
  apply ggQ2s08k4_eq_of_basis
  intro k
  change (ggQ2s08k4_pairDiag f i0 a * ggQ2s08k4_diag f (ggQ2s08k4_starScalar i0 T)
      (ggQ2s08k4_starScalar_ne i0 T)) (f k) = _
  rw [LinearEquiv.mul_apply, ggQ2s08k4_diag_apply, map_smul, ggQ2s08k4_pairDiag_apply,
    ggQ2s08k4_diag_apply, ggQ2s08k4_starScalar_insert i0 a T ha]
  simp only [Pi.mul_apply, ggQ2s08k4_pairScalar]
  rw [smul_smul, mul_comm]

theorem ggQ2s08k4_starScalar_eq
    {N : ℕ} (i0 : Fin N) (T : Finset (Fin N))
    (hi0 : i0 ∉ T) (k : Fin N) :
    ggQ2s08k4_starScalar i0 T k =
      if k = i0 then (-1 : ZMod 3) ^ T.card else if k ∈ T then -1 else 1 := by
  rw [ggQ2s08k4_starScalar_apply i0 T hi0 k]
  by_cases hk : k = i0
  · rw [if_pos hk]; simp [hk, hi0]
  · rw [if_neg hk]; simp [hk]

theorem ggQ2s08k4_diag_signScalar_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (H : Subgroup (V ≃ₗ[ZMod 3] V)) (hs : ∀ a, ggQ2s08k4_sgn f a ∈ H) :
    ∀ S : Finset (Fin N),
      ggQ2s08k4_diag f (ggQ2s08k4_signScalar S) (ggQ2s08k4_signScalar_ne S) ∈ H := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    rw [ggQ2s08k4_diag_congr f (by funext k; simp [ggQ2s08k4_signScalar])
      (ggQ2s08k4_signScalar_ne ∅) (fun _ => one_ne_zero), ggQ2s08k4_diag_one]
    exact H.one_mem
  | insert a S ha ih =>
    rw [← ggQ2s08k4_sgn_mul_diag_signScalar f a S ha]
    exact H.mul_mem (hs a) ih

theorem ggQ2s08k4_diag_starScalar_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (H : Subgroup (V ≃ₗ[ZMod 3] V)) (i0 : Fin N)
    (hpair : ∀ j, j ≠ i0 → ggQ2s08k4_pairDiag f i0 j ∈ H) :
    ∀ T : Finset (Fin N), i0 ∉ T →
      ggQ2s08k4_diag f (ggQ2s08k4_starScalar i0 T) (ggQ2s08k4_starScalar_ne i0 T) ∈ H := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    rw [ggQ2s08k4_diag_congr f (by funext k; simp [ggQ2s08k4_starScalar])
      (ggQ2s08k4_starScalar_ne i0 ∅) (fun _ => one_ne_zero), ggQ2s08k4_diag_one]
    exact H.one_mem
  | insert a T ha ih =>
    intro hi0
    have hai0 : a ≠ i0 := fun h => hi0 (h ▸ Finset.mem_insert_self a T)
    have hi0T : i0 ∉ T := fun h => hi0 (Finset.mem_insert_of_mem h)
    rw [← ggQ2s08k4_pairDiag_mul_diag_starScalar f i0 a T ha]
    exact H.mul_mem (hpair a hai0) (ih hi0T)

theorem ggQ2s08k4_mono_of_monoEven
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {g : V ≃ₗ[ZMod 3] V} (h : GGQ2S08MonoEven f g) : GGQ2S08Mono f g := by
  obtain ⟨σ, ε, hε, _, hg⟩ := h
  exact ⟨σ, ε, hε, hg⟩

theorem ggQ2s08k4_mono_split
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {g : V ≃ₗ[ZMod 3] V} {σ : Equiv.Perm (Fin N)} {ε : Fin N → ZMod 3}
    (hε : ∀ i, ε i ≠ 0) (hgε : ∀ i, g (f i) = ε i • f (σ i)) :
    g = ggQ2s08k4_permM f σ * ggQ2s08k4_diag f ε hε := by
  apply ggQ2s08k4_eq_of_basis
  intro i
  change g (f i) = (ggQ2s08k4_permM f σ * ggQ2s08k4_diag f ε hε) (f i)
  rw [hgε i, LinearEquiv.mul_apply, ggQ2s08k4_diag_apply, map_smul, ggQ2s08k4_permM_apply]

theorem ggQ2s08k4_mono_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (H : Subgroup (V ≃ₗ[ZMod 3] V)) (hperm : ∀ σ, ggQ2s08k4_permM f σ ∈ H)
    (hs : ∀ a, ggQ2s08k4_sgn f a ∈ H) :
    ∀ g, GGQ2S08Mono f g → g ∈ H := by
  intro g hg
  obtain ⟨σ, ε, hε, hgε⟩ := hg
  rw [ggQ2s08k4_mono_split f hε hgε]
  refine H.mul_mem (hperm σ) ?_
  classical
  let S := Finset.univ.filter (fun i => ε i = -1)
  have hSmem : ∀ k, k ∈ S ↔ ε k = -1 := fun k => by simp [S]
  have hεS : ε = ggQ2s08k4_signScalar S := by
    funext k
    by_cases hk : ε k = -1
    · rw [ggQ2s08k4_signScalar, if_pos ((hSmem k).mpr hk)]; exact hk
    · rw [ggQ2s08k4_signScalar, if_neg (fun h => hk ((hSmem k).mp h))]
      rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (ε k) (hε k) with h | h
      · exact h
      · exact absurd h hk
  rw [ggQ2s08k4_diag_congr f hεS hε (ggQ2s08k4_signScalar_ne S)]
  exact ggQ2s08k4_diag_signScalar_mem f H hs S
theorem ggQ2s08k4_monoEven_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    (H : Subgroup (V ≃ₗ[ZMod 3] V)) (hperm : ∀ σ, ggQ2s08k4_permM f σ ∈ H) (i0 : Fin N)
    (hpair : ∀ j, j ≠ i0 → ggQ2s08k4_pairDiag f i0 j ∈ H) :
    ∀ g, GGQ2S08MonoEven f g → g ∈ H := by
  intro g hg
  obtain ⟨σ, ε, hε, hprod, hgε⟩ := hg
  rw [ggQ2s08k4_mono_split f hε hgε]
  refine H.mul_mem (hperm σ) ?_
  classical
  let S := Finset.univ.filter (fun i => ε i = -1)
  have hSmem : ∀ k, k ∈ S ↔ ε k = -1 := fun k => by simp [S]
  have hεfac : ∀ i, ε i = if i ∈ S then (-1 : ZMod 3) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact (hSmem i).mp hi
    · rw [if_neg hi]
      have hne : ε i ≠ -1 := fun h => hi ((hSmem i).mpr h)
      rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (ε i) (hε i) with h | h
      · exact h
      · exact absurd h hne
  have hSeven : Even S.card := by
    have hcongr : ∏ i, ε i = ∏ i, (if i ∈ S then (-1 : ZMod 3) else 1) :=
      Finset.prod_congr rfl (fun i _ => hεfac i)
    have hcalc : ∏ i, (if i ∈ S then (-1 : ZMod 3) else 1) = (-1 : ZMod 3) ^ S.card := by
      rw [Finset.prod_ite_mem]
      simp [Finset.prod_const]
    have hmain : (-1 : ZMod 3) ^ S.card = 1 :=
      ((hcongr.trans hcalc).symm).trans hprod
    by_contra hodd
    have hOdd : Odd S.card := Nat.not_even_iff_odd.mp hodd
    rw [show (-1 : ZMod 3) ^ S.card = -1 from Odd.neg_one_pow hOdd] at hmain
    exact absurd hmain (by decide)
  by_cases hi0 : i0 ∈ S
  · have hodd : Odd (S.erase i0).card := by
      apply Nat.not_even_iff_odd.mp
      intro he
      have h1 : Even ((S.erase i0).card + 1) := by
        rw [Finset.card_erase_add_one hi0]; exact hSeven
      exact (Nat.even_add_one.mp h1) he
    have hεstar : ε = ggQ2s08k4_starScalar i0 (S.erase i0) := by
      funext k
      rw [ggQ2s08k4_starScalar_eq i0 (S.erase i0) (by simp) k]
      by_cases hk : k = i0
      · rw [hk]
        rw [if_pos rfl, show (-1 : ZMod 3) ^ (S.erase i0).card = -1 from Odd.neg_one_pow hodd]
        exact (hSmem i0).mp hi0
      · rw [if_neg hk]
        by_cases hkT : k ∈ S.erase i0
        · rw [if_pos hkT]
          exact (hSmem k).mp (Finset.mem_of_mem_erase hkT)
        · rw [if_neg hkT]
          have hkS : k ∉ S := fun h => hkT (Finset.mem_erase.mpr ⟨hk, h⟩)
          have hne : ε k ≠ -1 := fun h => hkS ((hSmem k).mpr h)
          rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (ε k) (hε k) with h | h
          · exact h
          · exact absurd h hne
    rw [ggQ2s08k4_diag_congr f hεstar hε (ggQ2s08k4_starScalar_ne i0 _)]
    exact ggQ2s08k4_diag_starScalar_mem f H i0 hpair (S.erase i0) (by simp)
  · have hεstar : ε = ggQ2s08k4_starScalar i0 S := by
      funext k
      rw [ggQ2s08k4_starScalar_eq i0 S hi0 k]
      by_cases hk : k = i0
      · rw [hk]
        rw [if_pos rfl, show (-1 : ZMod 3) ^ S.card = 1 from Even.neg_one_pow hSeven]
        have hne : ε i0 ≠ -1 := fun h => hi0 ((hSmem i0).mpr h)
        rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (ε i0) (hε i0) with h | h
        · exact h
        · exact absurd h hne
      · rw [if_neg hk]
        by_cases hkT : k ∈ S
        · rw [if_pos hkT]
          exact (hSmem k).mp hkT
        · rw [if_neg hkT]
          have hne : ε k ≠ -1 := fun h => hkT ((hSmem k).mpr h)
          rcases ggQ2s08k4_zmod3_eq_one_or_neg_one (ε k) (hε k) with h | h
          · exact h
          · exact absurd h hne
    rw [ggQ2s08k4_diag_congr f hεstar hε (ggQ2s08k4_starScalar_ne i0 S)]
    exact ggQ2s08k4_diag_starScalar_mem f H i0 hpair S hi0
theorem ggQ2s08k4_mono_data_eq
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (f : Module.Basis (Fin N) (ZMod 3) V)
    {g : V ≃ₗ[ZMod 3] V} {σ τ : Equiv.Perm (Fin N)} {ε δ : Fin N → ZMod 3}
    (hε : ∀ i, ε i ≠ 0) (hδ : ∀ i, δ i ≠ 0)
    (hg : ∀ i, g (f i) = ε i • f (σ i)) (hh : ∀ i, g (f i) = δ i • f (τ i)) :
    σ = τ ∧ ε = δ := by
  have hrepr : ∀ (a b : Fin N) (c : ZMod 3),
      f.repr (c • f a) b = c * (if a = b then 1 else 0) := by
    intro a b c
    simp [map_smul, Module.Basis.repr_self_apply, smul_eq_mul, Finsupp.single_apply]
  have hστ : ∀ i, σ i = τ i := by
    intro i
    by_contra h
    have h1 : f.repr (g (f i)) (σ i) = ε i := by
      rw [hg i, hrepr, if_pos rfl, mul_one]
    have h2 : f.repr (g (f i)) (σ i) = 0 := by
      rw [hh i, hrepr, if_neg (Ne.symm h), mul_zero]
    rw [h1] at h2
    exact hε i h2
  have hεδ : ε = δ := by
    funext i
    have h1 : f.repr (g (f i)) (σ i) = ε i := by
      rw [hg i, hrepr, if_pos rfl, mul_one]
    have h2 : f.repr (g (f i)) (σ i) = δ i := by
      rw [hh i, hrepr, ← hστ i, if_pos rfl, mul_one]
    rw [h1] at h2
    exact h2
  exact ⟨Equiv.ext hστ, hεδ⟩
theorem ggQ2s08k4_prod_sign_single
    {N : ℕ}
    (c : Fin N → ZMod 3) (i0 : Fin N)
    (hi0 : c i0 = -1) (hrest : ∀ j, j ≠ i0 → c j = 1) :
    ∏ i, c i = (-1 : ZMod 3) := by
  rw [Finset.prod_eq_single i0]
  · exact hi0
  · intro j _ hj; exact hrest j hj
  · intro h; exact absurd (Finset.mem_univ i0) h
theorem ggQ2s08k4_prod_sign_pair
    {N : ℕ}
    (c : Fin N → ZMod 3) (i0 j0 : Fin N)
    (hij : i0 ≠ j0) (hi0 : c i0 = -1) (hj0 : c j0 = -1)
    (hrest : ∀ k, k ≠ i0 → k ≠ j0 → c k = 1) :
    ∏ i, c i = 1 := by
  classical
  rw [← Finset.mul_prod_erase (Finset.univ) c (Finset.mem_univ i0)]
  have hinner : ∏ i ∈ (Finset.univ.erase i0), c i = c j0 := by
    refine Finset.prod_eq_single j0 (fun k hk hkj => ?_) (fun hj => ?_)
    · exact hrest k (Finset.mem_erase.mp hk).1 hkj
    · exact absurd (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j0⟩) hj
  rw [hinner, hi0, hj0]
  decide

end CFSG.StandardType

end
