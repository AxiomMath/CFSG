module

public import CFSG.Quasithin.Vol2.Ch12Sec6L1a
public import CFSG.Quasithin.Background.B5FinS8Schur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a Equiv
open scoped IsMulCommutative

namespace S126P

theorem dAct_mul (σ τ : Perm (Fin 8)) (y : D8) : dAct (σ * τ) y = dAct σ (dAct τ y) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [dAct_mk, dAct_mk, dAct_mk]
  congr 1

theorem dAct_one (y : D8) : dAct 1 y = y := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [dAct_mk]
  congr 1

theorem dAct_inv_dAct (σ : Perm (Fin 8)) (y : D8) : dAct σ⁻¹ (dAct σ y) = y := by
  rw [← dAct_mul, inv_mul_cancel, dAct_one]

theorem dAct_dAct_inv (σ : Perm (Fin 8)) (y : D8) : dAct σ (dAct σ⁻¹ y) = y := by
  rw [← dAct_mul, mul_inv_cancel, dAct_one]

theorem dAct_pow (σ : Perm (Fin 8)) (n : ℕ) (y : D8) :
    dAct (σ ^ n) y = (dAct σ)^[n] y := by
  induction n generalizing y with
  | zero => rw [pow_zero, dAct_one]; rfl
  | succ n ih => rw [pow_succ, dAct_mul, ih, Function.iterate_succ_apply]

@[expose] def pe (a b : Fin 8) : ↥(coreMod 8) := B5FinS8.pelt a b

theorem wt_pv : ∀ a b : Fin 8, a ≠ b →
    (Finset.univ.filter fun i => B5FinS8.pv a b i ≠ 0).card = 2 := by
  decide +kernel

theorem pv_apply_self_left (a b : Fin 8) (h : a ≠ b) : B5FinS8.pv a b a ≠ 0 := by
  revert a b
  decide

theorem pv_apply_ne (a b i : Fin 8) (ha : i ≠ a) (hb : i ≠ b) : B5FinS8.pv a b i = 0 := by
  revert a b i
  decide

theorem permAct_pv (σ : Perm (Fin 8)) (a b : Fin 8) :
    permAct 8 σ (Multiplicative.ofAdd (B5FinS8.pv a b)) =
      Multiplicative.ofAdd (B5FinS8.pv (σ a) (σ b)) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply, toAdd_ofAdd, toAdd_ofAdd]
  simp only [B5FinS8.pv, B5FinS8.ev, Pi.add_apply]
  rw [Pi.single_apply, Pi.single_apply, Pi.single_apply, Pi.single_apply]
  simp only [Equiv.Perm.inv_eq_iff_eq]

theorem eq_one_of_dAct {σ : Perm (Fin 8)} (h : ∀ y : D8, dAct σ y = y) : σ = 1 := by
  by_contra hσ
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hσ (Equiv.ext hc)
  obtain ⟨k, hki, hks⟩ : ∃ k : Fin 8, k ≠ i ∧ k ≠ σ i := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    have h3 : ∀ k : Fin 8, k = i ∨ k = σ i := fun k => by
      by_cases hk : k = i
      · exact Or.inl hk
      · exact Or.inr (hc k hk)
    have hcard : (Finset.univ : Finset (Fin 8)) ⊆ {i, σ i} := fun k _ => by
      rcases h3 k with rfl | rfl <;> simp
    have := Finset.card_le_card hcard
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_le_two (a := i) (b := σ i)
    omega
  have hy := h (QuotientGroup.mk (pe i k))
  rw [dAct_mk] at hy
  rcases (mk_eq_iff _ _).1 hy with h1 | h1
  · have h2 := congrArg (fun z : PermMod 8 => (Multiplicative.toAdd z : Fin 8 → ZMod 2) (σ i)) h1
    simp only [coreAct_coe, pe, B5FinS8.pelt, permAct_pv, toAdd_ofAdd] at h2
    rw [pv_apply_ne i k (σ i) hi (Ne.symm hks)] at h2
    exact pv_apply_self_left (σ i) (σ k) (fun h => hki (σ.injective h).symm) h2
  · have h2 := congrArg wt h1
    have hw1 : wt (((coreAct 8 σ) (pe i k) : ↥(coreMod 8)) : PermMod 8) = 2 := by
      rw [coreAct_coe, wt_permAct]
      exact wt_pv i k (Ne.symm hki)
    have hw2 : wt ((pe i k : PermMod 8) * allOnes 8) = 6 := by
      have := wt_add_ones (B5FinS8.pv i k)
      rw [wt_pv i k (Ne.symm hki)] at this
      exact this
    rw [hw1, hw2] at h2
    exact absurd h2 (by norm_num)

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] def ActsAs (F : Frame126 T L V) (x : G) (σ : Perm (Fin 8)) : Prop :=
  ∀ v w : ↥V, (w : G) = x * v * x⁻¹ → F.β w = dAct σ (F.β v)

omit [IsMulCommutative ↥V] in
theorem conj_mem {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    x * (v : G) * x⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.1 hx v).1 v.2

theorem ActsAs.mul {F : Frame126 T L V} {x y : G} {σ τ : Perm (Fin 8)} (hx : ActsAs F x σ)
    (hy : ActsAs F y τ) (hyN : y ∈ Subgroup.normalizer (V : Set G)) :
    ActsAs F (x * y) (σ * τ) := by
  intro v w hw
  set u : ↥V := ⟨y * v * y⁻¹, conj_mem hyN v⟩
  have hu := hy v u rfl
  have hw' : (w : G) = x * u * x⁻¹ := by
    rw [hw]
    change x * y * v * (x * y)⁻¹ = x * (y * v * y⁻¹) * x⁻¹
    group
  rw [hx u w hw', hu, dAct_mul]

theorem ActsAs.inv {F : Frame126 T L V} {x : G} {σ : Perm (Fin 8)} (hx : ActsAs F x σ) :
    ActsAs F x⁻¹ σ⁻¹ := by
  intro v w hw
  have h1 : (v : G) = x * w * x⁻¹ := by rw [hw]; group
  rw [hx w v h1, dAct_inv_dAct]

theorem ActsAs.one (F : Frame126 T L V) : ActsAs F 1 1 := by
  intro v w hw
  have : w = v := Subtype.ext (by rw [hw]; group)
  rw [this, dAct_one]

theorem ActsAs.pow {F : Frame126 T L V} {x : G} {σ : Perm (Fin 8)} (hx : ActsAs F x σ)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (n : ℕ) : ActsAs F (x ^ n) (σ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact ActsAs.one F
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx hxN

theorem ActsAs.commutator {F : Frame126 T L V} {x y : G} {σ τ : Perm (Fin 8)}
    (hx : ActsAs F x σ) (hy : ActsAs F y τ) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) :
    ActsAs F (x * y * x⁻¹ * y⁻¹) (σ * τ * σ⁻¹ * τ⁻¹) :=
  (((hx.mul hy hyN).mul hx.inv (Subgroup.inv_mem _ hxN)).mul hy.inv (Subgroup.inv_mem _ hyN))

theorem ActsAs.unique {F : Frame126 T L V} {x : G} {σ τ : Perm (Fin 8)} (hσ : ActsAs F x σ)
    (hτ : ActsAs F x τ) (hxN : x ∈ Subgroup.normalizer (V : Set G)) : σ = τ := by
  have h1 : ∀ y : D8, dAct (σ⁻¹ * τ) y = y := by
    intro y
    obtain ⟨v, rfl⟩ := F.β_surj y
    rw [dAct_mul, ← hτ v ⟨x * v * x⁻¹, conj_mem hxN v⟩ rfl,
      hσ v ⟨x * v * x⁻¹, conj_mem hxN v⟩ rfl, dAct_inv_dAct]
  have h2 := eq_one_of_dAct h1
  rw [inv_mul_eq_one] at h2
  exact h2

theorem actsAs_of_mem_T (F : Frame126 T L V) {t : G} (ht : t ∈ T) :
    ∃ σ : Perm (Fin 8), PresPart σ ∧ ActsAs F t σ :=
  F.tAct t ht

theorem actsAs_of_pi (F : Frame126 T L V) {l : G} (hl : l ∈ Subgroup.normalizer (V : Set G))
    (σ : ↥(alternatingGroup (Fin 8)))
    (h : conjAct V ⟨l, hl⟩ = ((F.π σ : ↥(autOn L V)) : MulAut ↥V)) :
    ActsAs F l σ := by
  intro v w hw
  have hw' : w = conjAct V ⟨l, hl⟩ v := Subtype.ext hw
  rw [hw', h, F.equi]

theorem pow_eq_one_of_actsAs {F : Frame126 T L V} {x : G} {σ : Perm (Fin 8)} (hx : ActsAs F x σ)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) {n : ℕ} (hn : x ^ n = 1) : σ ^ n = 1 := by
  have h1 := hx.pow hxN n
  rw [hn] at h1
  exact (ActsAs.one F).unique h1 (Subgroup.one_mem _) |>.symm

end S126P

end CFSG.Quasithin.H13
