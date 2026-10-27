module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisOrbit
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusTwist

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CoxeterSystem
open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem
open CFSG.RankThree.GF2n.Smith81.D6Spin (graphSpin)

section Generic

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} {D : CurtisDatum G cs p}
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  [Finite G]

private theorem w135c2_omfPBound_form_c_eq_zero [Fact p.Prime] [CharP k p]
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {f : Module.Dual k V}
    (hf : ∀ z ∈ CFSG.Quasithin.SmithCurtis.augSub ρ D.L, f z = 0) (hfy : f y = 1)
    {m : ℕ} (b c : Fin m → W)
    (hmove : ∀ i j, ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * c j →
      ∃ s ∈ ω, μ s = D.dScalar χ s) (i j : Fin m) :
    f (ρ ((D.nW (b i))⁻¹ * D.nW (c j)) y) = 0 := by
  obtain ⟨h, hh, e⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.nW_inv_mul D (b i) (c j)
  obtain ⟨ω, hω, hωe⟩ := cs.exists_isReduced ((b i)⁻¹ * c j)
  rw [e, hωe,
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.form_nW_mul D ρ ht hf hfy hω hh]
  have hco : D.coinvScalar χ μ ω = 0 := by
    obtain ⟨s, hs, hμs⟩ := hmove i j ω hω hωe.symm
    exact List.prod_eq_zero (List.mem_map.mpr ⟨s, hs, sub_eq_zero.mpr hμs⟩)
  rw [hco, mul_zero]

private theorem w135c2_omfPBound_form_b_eq_ite [Fact p.Prime] [CharP k p]
    {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    {f : Module.Dual k V}
    (hf : ∀ z ∈ CFSG.Quasithin.SmithCurtis.augSub ρ D.L, f z = 0) (hfy : f y = 1)
    {m : ℕ} (b : Fin m → W)
    (hsep : ∀ i j, i ≠ j → ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * b j →
      ∃ s ∈ ω, μ s = D.dScalar χ s) (i j : Fin m) :
    f (ρ ((D.nW (b i))⁻¹ * D.nW (b j)) y) = if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst hji
    rw [inv_mul_cancel, map_one, Module.End.one_apply, hfy]
    simp
  · rw [if_neg hji]
    obtain ⟨h, hh, e⟩ :=
      CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.nW_inv_mul D (b i) (b j)
    obtain ⟨ω, hω, hωe⟩ := cs.exists_isReduced ((b i)⁻¹ * b j)
    rw [e, hωe,
      CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.form_nW_mul D ρ ht hf hfy hω hh]
    have hco : D.coinvScalar χ μ ω = 0 := by
      obtain ⟨s, hs, hμs⟩ := hsep i j (Ne.symm hji) ω hω hωe.symm
      exact List.prod_eq_zero (List.mem_map.mpr ⟨s, hs, sub_eq_zero.mpr hμs⟩)
    rw [hco, mul_zero]

private theorem w135c2_omfPBound_linearIndependent_sub_one_of_map [Fact p.Prime] [CharP k p]
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    (T : V →ₗ[k] V) {m : ℕ} (b c : Fin m → W) (a : Fin m → k)
    (hT : ∀ j, T (ρ (D.nW (b j)) y) = a j • ρ (D.nW (c j)) y)
    (hsep : ∀ i j, i ≠ j → ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * b j →
      ∃ s ∈ ω, μ s = D.dScalar χ s)
    (hmove : ∀ i j, ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * c j →
      ∃ s ∈ ω, μ s = D.dScalar χ s) :
    LinearIndependent k fun j => (T - 1) (ρ (D.nW (b j)) y) := by
  obtain ⟨f, hf, hfy⟩ := D.exists_form hρ ht.1 ht.2.1
  rw [Fintype.linearIndependent_iff]
  intro cc hc i
  have key : ∀ j, f (ρ ((D.nW (b i))⁻¹) ((T - 1) (ρ (D.nW (b j)) y)))
      = -(if j = i then 1 else 0) := by
    intro j
    have hz : ρ ((D.nW (b i))⁻¹) ((T - 1) (ρ (D.nW (b j)) y))
        = a j • ρ ((D.nW (b i))⁻¹ * D.nW (c j)) y
          - ρ ((D.nW (b i))⁻¹ * D.nW (b j)) y := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_smul, hT j, act_mul]
    rw [hz, map_sub, map_smul,
      w135c2_omfPBound_form_c_eq_zero (D := D) ht hf hfy b c hmove i j,
      w135c2_omfPBound_form_b_eq_ite (D := D) ht hf hfy b hsep i j,
      smul_zero, zero_sub]
  have h2 := congrArg (fun z => f (ρ ((D.nW (b i))⁻¹) z)) hc
  simp only [map_sum, map_smul, map_zero] at h2
  simp only [key, smul_eq_mul, mul_neg, mul_ite, mul_one, mul_zero, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h2
  exact neg_eq_zero.mp h2

theorem le_finrank_range_sub_one_of_map [Fact p.Prime] [CharP k p] [Module.Finite k V]
    (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k} (ht : D.IsCurtisType ρ y χ μ)
    (T : V →ₗ[k] V) {m : ℕ} (b c : Fin m → W) (a : Fin m → k)
    (hT : ∀ j, T (ρ (D.nW (b j)) y) = a j • ρ (D.nW (c j)) y)
    (hsep : ∀ i j, i ≠ j → ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * b j →
      ∃ s ∈ ω, μ s = D.dScalar χ s)
    (hmove : ∀ i j, ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = (b i)⁻¹ * c j →
      ∃ s ∈ ω, μ s = D.dScalar χ s) :
    m ≤ Module.finrank k (LinearMap.range (T - 1)) := by
  have hli := w135c2_omfPBound_linearIndependent_sub_one_of_map (D := D) hρ ht T b c a hT hsep
    hmove
  let Tm : V →ₗ[k] V := T - 1
  let w : Fin m → LinearMap.range Tm :=
    fun j => ⟨Tm (ρ (D.nW (b j)) y), ρ (D.nW (b j)) y, rfl⟩
  have hw : LinearIndependent k w := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro cc hc
    refine hli cc ?_
    have h := congrArg (fun z => (LinearMap.range Tm).subtype z) hc
    simpa [Tm, w, map_sum, map_smul] using h
  simpa [Tm] using hw.fintype_card_le_finrank

private theorem w135c2_omfPBound_smul_eq_of_inv_mul_smul_eq_self {X : Type*} [MulAction W X]
    {a b : W} {v : X} (h : (a⁻¹ * b) • v = v) : b • v = a • v := by
  calc b • v = (a * (a⁻¹ * b)) • v := by rw [mul_inv_cancel_left]
    _ = a • (a⁻¹ * b) • v := by rw [mul_smul]
    _ = a • v := by rw [h]

theorem le_finrank_range_sub_one_of_map_orbit [Fact p.Prime] [CharP k p] [Module.Finite k V]
    {X : Type*} [MulAction W X] (hρ : IsSimpleRep ρ) {y : V} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType ρ y χ μ) {v : X}
    (hv : ∀ s, μ s ≠ D.dScalar χ s → cs.simple s • v = v) (T : V →ₗ[k] V) {m : ℕ}
    (b c : Fin m → W) (a : Fin m → k) (hT : ∀ j, T (ρ (D.nW (b j)) y) = a j • ρ (D.nW (c j)) y)
    (hinj : ∀ i j, i ≠ j → b i • v ≠ b j • v) (hmove : ∀ i j, b i • v ≠ c j • v) :
    m ≤ Module.finrank k (LinearMap.range (T - 1)) := by
  refine le_finrank_range_sub_one_of_map (D := D) hρ ht T b c a hT ?_ ?_
  · intro i j hij ω _ hωe
    apply exists_mem_mu_eq_dScalar_of_smul_ne (D := D) hv
    intro hfix0
    have hfix : ((b i)⁻¹ * b j) • v = v := by rw [← hωe]; exact hfix0
    exact hinj i j hij (w135c2_omfPBound_smul_eq_of_inv_mul_smul_eq_self hfix).symm
  · intro i j ω _ hωe
    apply exists_mem_mu_eq_dScalar_of_smul_ne (D := D) hv
    intro hfix0
    have hfix : ((b i)⁻¹ * c j) • v = v := by rw [← hωe]; exact hfix0
    exact hmove i j (w135c2_omfPBound_smul_eq_of_inv_mul_smul_eq_self hfix).symm

end Generic

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem omPlusCurtisDatum_two_nW_mul (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n)
    (a b : (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    (omPlusCurtisDatum n F hn).nW (a * b) =
      (omPlusCurtisDatum n F hn).nW a * (omPlusCurtisDatum n F hn).nW b := by
  obtain ⟨h, hh, e⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.nW_mul
      (D := omPlusCurtisDatum n F hn) a b
  rw [omPlusCurtisDatum_two_H hF hn, Subgroup.mem_bot] at hh
  rw [hh, mul_one] at e
  exact e.symm

private theorem w135c2_omfPBound_toStdD_comp_omGraphSwap_q {n : ℕ} (hn : 3 ≤ n)
    (γ : Fin n → ℤ) :
    toStdD n (γ ∘ Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
        ⟨n - 1, by omega⟩ =
      Function.update (toStdD n γ) ⟨n - 1, by omega⟩ (-toStdD n γ ⟨n - 1, by omega⟩)
        ⟨n - 1, by omega⟩ := by
  have h1 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := Equiv.swap_apply_right _ _
  have h2 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := Equiv.swap_apply_left _ _
  have hidx : (⟨n - 1 - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  unfold toStdD
  simp only [Function.comp_apply, h1, h2, hidx, Function.update_self]
  split_ifs <;> omega

private theorem w135c2_omfPBound_toStdD_comp_omGraphSwap_p {n : ℕ} (hn : 3 ≤ n)
    (γ : Fin n → ℤ) :
    toStdD n (γ ∘ Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
        ⟨n - 2, by omega⟩ =
      Function.update (toStdD n γ) ⟨n - 1, by omega⟩ (-toStdD n γ ⟨n - 1, by omega⟩)
        ⟨n - 2, by omega⟩ := by
  have hne : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have hv : n - 2 = n - 1 := congrArg Fin.val h
    omega
  have h1 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := Equiv.swap_apply_left _ _
  have h2 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := Equiv.swap_apply_right _ _
  have hidx : (⟨n - 2 - 1, by omega⟩ : Fin n) = ⟨n - 3, by omega⟩ := by
    apply Fin.ext
    show n - 2 - 1 = n - 3
    omega
  have hfix : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩ := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
  have hsucc : (⟨n - 2 + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show n - 2 + 1 = n - 1
    omega
  unfold toStdD
  simp only [Function.comp_apply, h1]
  rw [Function.update_of_ne hne]
  simp only [hidx, hfix, hsucc, h2]
  split_ifs <;> omega

private theorem w135c2_omfPBound_toStdD_comp_omGraphSwap_ne {n : ℕ} (hn : 3 ≤ n)
    (γ : Fin n → ℤ) {a : Fin n}
    (hp : a ≠ ⟨n - 2, by omega⟩) (hq : a ≠ ⟨n - 1, by omega⟩) :
    toStdD n (γ ∘ Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) a =
      Function.update (toStdD n γ) ⟨n - 1, by omega⟩
        (-toStdD n γ ⟨n - 1, by omega⟩) a := by
  have hsubp : (⟨a.val - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
    intro h
    have hv : a.val - 1 = n - 2 := congrArg Fin.val h
    have havp : a.val ≠ n - 2 := fun h' => hp (Fin.ext h')
    have havq : a.val ≠ n - 1 := fun h' => hq (Fin.ext h')
    omega
  have hsubq : (⟨a.val - 1, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have hv : a.val - 1 = n - 1 := congrArg Fin.val h
    omega
  have hswap : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) a = a :=
    Equiv.swap_apply_of_ne_of_ne hp hq
  have hswap2 := Equiv.swap_apply_of_ne_of_ne hsubp hsubq
  have hcond : ¬ a.val + 2 = n := by
    intro h
    exact hp (Fin.ext (by show a.val = n - 2; omega))
  unfold toStdD
  simp only [Function.comp_apply, hswap, dif_neg hcond]
  rw [Function.update_of_ne hq]
  simp only [hswap2]
  split_ifs <;> omega

theorem toStdD_comp_omGraphSwap {n : ℕ} (hn : 2 ≤ n) (γ : Fin n → ℤ) :
    toStdD n (γ ∘ omGraphSwap hn) =
      Function.update (toStdD n γ) ⟨n - 1, by omega⟩ (-toStdD n γ ⟨n - 1, by omega⟩) := by
  rcases eq_or_lt_of_le hn with rfl | hn3
  · funext a
    fin_cases a <;> simp [toStdD, omGraphSwap, Function.update]
    all_goals ring
  · funext a
    simp only [omGraphSwap]
    by_cases hq : a = ⟨n - 1, by omega⟩
    · subst hq
      exact w135c2_omfPBound_toStdD_comp_omGraphSwap_q (by omega) γ
    · by_cases hp : a = ⟨n - 2, by omega⟩
      · subst hp
        exact w135c2_omfPBound_toStdD_comp_omGraphSwap_p (by omega) γ
      · exact w135c2_omfPBound_toStdD_comp_omGraphSwap_ne (by omega) γ hp hq

private theorem w135c2_omfPBound_stdReflD_conj_two_q {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ) :
    stdReflD n (⟨n - 1, by omega⟩ : Fin n) e ⟨n - 1, by omega⟩ =
      Function.update (stdReflD n (⟨n - 2, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 2, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) ⟨n - 1, by omega⟩ := by
  have hq : ¬ (⟨n - 1, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  have hp : (⟨n - 2, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [stdReflD_of_not_lt n hq, stdReflD_of_lt n hp]
  have hidxq : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) =
      ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  have hidxp : (⟨(⟨n - 2, by omega⟩ : Fin n).val + 1, hp⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show n - 2 + 1 = n - 1
    omega
  simp only [hidxq, hidxp]
  have h1 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := Equiv.swap_apply_right _ _
  have h2 : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  have hif : ((⟨n - 1, by omega⟩ : Fin n).val + 2 = n) ∨
      ((⟨n - 1, by omega⟩ : Fin n).val + 1 = n) :=
    Or.inr (by show n - 1 + 1 = n; omega)
  rw [Function.update_self]
  simp only [Function.comp_apply, h1]
  rw [Function.update_of_ne h2.symm, if_pos hif]
  ring

private theorem w135c2_omfPBound_stdReflD_conj_two_p {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ) :
    stdReflD n (⟨n - 1, by omega⟩ : Fin n) e ⟨n - 2, by omega⟩ =
      Function.update (stdReflD n (⟨n - 2, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 2, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) ⟨n - 2, by omega⟩ := by
  have hq : ¬ (⟨n - 1, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  have hp : (⟨n - 2, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [stdReflD_of_not_lt n hq, stdReflD_of_lt n hp]
  have hidxq : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) =
      ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  have hidxp : (⟨(⟨n - 2, by omega⟩ : Fin n).val + 1, hp⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show n - 2 + 1 = n - 1
    omega
  simp only [hidxq, hidxp]
  have h1 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := Equiv.swap_apply_left _ _
  have h2 : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  have hif : ((⟨n - 2, by omega⟩ : Fin n).val + 2 = n) ∨
      ((⟨n - 2, by omega⟩ : Fin n).val + 1 = n) :=
    Or.inl (by show n - 2 + 2 = n; omega)
  rw [Function.update_of_ne h2]
  simp only [Function.comp_apply, h1]
  rw [Function.update_self, if_pos hif]
  ring

private theorem w135c2_omfPBound_stdReflD_conj_two_ne {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ)
    {a : Fin n} (haq : a ≠ ⟨n - 1, by omega⟩) (hap : a ≠ ⟨n - 2, by omega⟩) :
    stdReflD n (⟨n - 1, by omega⟩ : Fin n) e a =
      Function.update (stdReflD n (⟨n - 2, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 2, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) a := by
  have hq : ¬ (⟨n - 1, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  have hp : (⟨n - 2, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [stdReflD_of_not_lt n hq, stdReflD_of_lt n hp]
  have hidxq : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) =
      ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  have hidxp : (⟨(⟨n - 2, by omega⟩ : Fin n).val + 1, hp⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show n - 2 + 1 = n - 1
    omega
  simp only [hidxq, hidxp]
  have hsub1 : ¬ a.val + 2 = n := by
    intro h
    exact hap (Fin.ext (by show a.val = n - 2; omega))
  have hsub2 : ¬ a.val + 1 = n := by
    intro h
    exact haq (Fin.ext (by show a.val = n - 1; omega))
  have hswap : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) a = a :=
    Equiv.swap_apply_of_ne_of_ne hap haq
  have hif : ¬ (a.val + 2 = n ∨ a.val + 1 = n) := by
    rintro (h | h)
    · exact hsub1 h
    · exact hsub2 h
  rw [Function.update_of_ne haq]
  simp only [Function.comp_apply]
  rw [hswap, Function.update_of_ne haq, if_neg hif]
  ring

private theorem w135c2_omfPBound_stdReflD_conj_two {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ) :
    stdReflD n (⟨n - 1, by omega⟩ : Fin n) e =
      Function.update (stdReflD n (⟨n - 2, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 2, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) := by
  funext a
  by_cases haq : a = ⟨n - 1, by omega⟩
  · subst haq
    exact w135c2_omfPBound_stdReflD_conj_two_q hn e
  · by_cases hap : a = ⟨n - 2, by omega⟩
    · subst hap
      exact w135c2_omfPBound_stdReflD_conj_two_p hn e
    · exact w135c2_omfPBound_stdReflD_conj_two_ne hn e haq hap


private theorem w135c2_omfPBound_stdReflD_conj_last_q {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ) :
    stdReflD n (⟨n - 2, by omega⟩ : Fin n) e ⟨n - 1, by omega⟩ =
      Function.update (stdReflD n (⟨n - 1, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 1, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) ⟨n - 1, by omega⟩ := by
  have hq : ¬ (⟨n - 1, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  have hp : (⟨n - 2, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [stdReflD_of_lt n hp, stdReflD_of_not_lt n hq]
  have hidxq : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) =
      ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  have hidxp : (⟨(⟨n - 2, by omega⟩ : Fin n).val + 1, hp⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show n - 2 + 1 = n - 1
    omega
  simp only [hidxq, hidxp]
  have h1 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := Equiv.swap_apply_right _ _
  have h2 : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  have hif : ((⟨n - 1, by omega⟩ : Fin n).val + 2 = n) ∨
      ((⟨n - 1, by omega⟩ : Fin n).val + 1 = n) :=
    Or.inr (by show n - 1 + 1 = n; omega)
  rw [Function.update_self]
  simp only [Function.comp_apply, h1]
  rw [if_pos hif, Function.update_of_ne h2.symm]
  ring

private theorem w135c2_omfPBound_stdReflD_conj_last_p {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ) :
    stdReflD n (⟨n - 2, by omega⟩ : Fin n) e ⟨n - 2, by omega⟩ =
      Function.update (stdReflD n (⟨n - 1, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 1, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) ⟨n - 2, by omega⟩ := by
  have hq : ¬ (⟨n - 1, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  have hp : (⟨n - 2, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [stdReflD_of_lt n hp, stdReflD_of_not_lt n hq]
  have hidxq : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) =
      ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  have hidxp : (⟨(⟨n - 2, by omega⟩ : Fin n).val + 1, hp⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show n - 2 + 1 = n - 1
    omega
  simp only [hidxq, hidxp]
  have h1 : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩)
      ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := Equiv.swap_apply_left _ _
  have h2 : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  have hif : ((⟨n - 2, by omega⟩ : Fin n).val + 2 = n) ∨
      ((⟨n - 2, by omega⟩ : Fin n).val + 1 = n) :=
    Or.inl (by show n - 2 + 2 = n; omega)
  rw [Function.update_of_ne h2]
  simp only [Function.comp_apply, h1]
  rw [Function.update_self, if_pos hif]
  ring

private theorem w135c2_omfPBound_stdReflD_conj_last_ne {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ)
    {a : Fin n} (haq : a ≠ ⟨n - 1, by omega⟩) (hap : a ≠ ⟨n - 2, by omega⟩) :
    stdReflD n (⟨n - 2, by omega⟩ : Fin n) e a =
      Function.update (stdReflD n (⟨n - 1, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 1, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) a := by
  have hq : ¬ (⟨n - 1, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  have hp : (⟨n - 2, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  rw [stdReflD_of_lt n hp, stdReflD_of_not_lt n hq]
  have hidxq : (⟨(⟨n - 1, by omega⟩ : Fin n).val - 1, by omega⟩ : Fin n) =
      ⟨n - 2, by omega⟩ := by
    apply Fin.ext
    show n - 1 - 1 = n - 2
    omega
  have hidxp : (⟨(⟨n - 2, by omega⟩ : Fin n).val + 1, hp⟩ : Fin n) =
      ⟨n - 1, by omega⟩ := by
    apply Fin.ext
    show n - 2 + 1 = n - 1
    omega
  simp only [hidxq, hidxp]
  have hsub1 : ¬ a.val + 2 = n := by
    intro h
    exact hap (Fin.ext (by show a.val = n - 2; omega))
  have hsub2 : ¬ a.val + 1 = n := by
    intro h
    exact haq (Fin.ext (by show a.val = n - 1; omega))
  have hswap : (Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) a = a :=
    Equiv.swap_apply_of_ne_of_ne hap haq
  have hif : ¬ (a.val + 2 = n ∨ a.val + 1 = n) := by
    rintro (h | h)
    · exact hsub1 h
    · exact hsub2 h
  rw [Function.update_of_ne haq]
  simp only [Function.comp_apply]
  rw [hswap, Function.update_of_ne haq, if_neg hif]
  ring

private theorem w135c2_omfPBound_stdReflD_conj_last {n : ℕ} (hn : 2 ≤ n) (e : Fin n → ℤ) :
    stdReflD n (⟨n - 2, by omega⟩ : Fin n) e =
      Function.update (stdReflD n (⟨n - 1, by omega⟩ : Fin n)
        (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
        ⟨n - 1, by omega⟩
        (-(stdReflD n (⟨n - 1, by omega⟩ : Fin n)
          (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) := by
  funext a
  by_cases haq : a = ⟨n - 1, by omega⟩
  · subst haq
    exact w135c2_omfPBound_stdReflD_conj_last_q hn e
  · by_cases hap : a = ⟨n - 2, by omega⟩
    · subst hap
      exact w135c2_omfPBound_stdReflD_conj_last_p hn e
    · exact w135c2_omfPBound_stdReflD_conj_last_ne hn e haq hap


private theorem w135c2_omfPBound_stdReflD_conj_ne {n : ℕ} (hn : 2 ≤ n) {i : Fin n}
    (hip : i ≠ ⟨n - 2, by omega⟩) (hiq : i ≠ ⟨n - 1, by omega⟩) (e : Fin n → ℤ) :
    stdReflD n i e =
      Function.update (stdReflD n i (Function.update e ⟨n - 1, by omega⟩
        (-e ⟨n - 1, by omega⟩))) ⟨n - 1, by omega⟩
        (-(stdReflD n i (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) := by
  have hlt : i.val + 1 < n := by
    have hi : i.val ≠ n - 1 := fun h => hiq (Fin.ext h)
    have hlt := i.isLt
    omega
  simp only [stdReflD_of_lt n hlt]
  have hSq : (Equiv.swap i ⟨i.val + 1, hlt⟩) ⟨n - 1, by omega⟩ =
      ⟨n - 1, by omega⟩ := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      exact hiq h.symm
    · intro h
      apply hip
      apply Fin.ext
      show i.val = n - 2
      have hv := congrArg Fin.val h
      simp only at hv
      omega
  have hSa : ∀ a : Fin n, a ≠ ⟨n - 1, by omega⟩ →
      (Equiv.swap i ⟨i.val + 1, hlt⟩) a ≠ ⟨n - 1, by omega⟩ := by
    intro a ha h
    apply ha
    have h2 := congrArg (Equiv.swap i ⟨i.val + 1, hlt⟩) h
    rw [Equiv.swap_apply_self, hSq] at h2
    exact h2
  funext a
  by_cases haq : a = ⟨n - 1, by omega⟩
  · subst haq
    simp only [Function.comp_apply, hSq, Function.update_self]
    ring
  · rw [Function.update_of_ne haq]
    simp only [Function.comp_apply]
    rw [Function.update_of_ne (hSa a haq)]


private theorem w135c2_omfPBound_stdReflD_omGraphSwap {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    (e : Fin n → ℤ) :
    stdReflD n (omGraphSwap hn i) e =
      Function.update (stdReflD n i (Function.update e ⟨n - 1, by omega⟩
        (-e ⟨n - 1, by omega⟩))) ⟨n - 1, by omega⟩
        (-(stdReflD n i (Function.update e ⟨n - 1, by omega⟩ (-e ⟨n - 1, by omega⟩)))
          ⟨n - 1, by omega⟩) := by
  by_cases h2 : i = ⟨n - 2, by omega⟩
  · subst h2
    rw [omGraphSwap, Equiv.swap_apply_left]
    exact w135c2_omfPBound_stdReflD_conj_two hn e
  · by_cases h1 : i = ⟨n - 1, by omega⟩
    · subst h1
      rw [omGraphSwap, Equiv.swap_apply_right]
      exact w135c2_omfPBound_stdReflD_conj_last hn e
    · rw [omGraphSwap, Equiv.swap_apply_of_ne_of_ne h2 h1]
      exact w135c2_omfPBound_stdReflD_conj_ne hn h2 h1 e

private theorem w135c2_omfPBound_weylAction_simple_omGraphSwap {n : ℕ} (hn : 3 ≤ n)
    (i : Fin n) (γ : Fin n → ℤ) :
    weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple
          (omGraphSwap (by omega) i)) γ =
      weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple i)
        (γ ∘ omGraphSwap (by omega)) ∘ omGraphSwap (by omega) := by
  apply toStdD_injective n
  simp only [weylAction_simple]
  rw [toStdD_reflection, toStdD_comp_omGraphSwap (by omega),
    toStdD_reflection, toStdD_comp_omGraphSwap (by omega)]
  exact w135c2_omfPBound_stdReflD_omGraphSwap (by omega) i (toStdD n γ)

private theorem w135c2_omfPBound_nW_simple {n : ℕ} (hn : 3 ≤ n) (s : Fin n) :
    (omPlusCurtisDatum n F hn).nW
      ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple s) =
      (omPlusCurtisDatum n F hn).n s := by
  let cs := (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem
  have hlen : cs.length (cs.simple s * 1) =
      cs.length (1 : (coxeterMatrix (isFiniteType_cartanD n)).Group) + 1 := by
    rw [mul_one, cs.length_simple, cs.length_one]
  have h := (omPlusCurtisDatum n F hn).nW_simple_mul 1 s hlen
  simpa [cs, (omPlusCurtisDatum n F hn).nW_one] using h

private theorem w135c2_omfPBound_graphSpin_nW_wordProd_map (hF : Nat.card F = 2) {n : ℕ}
    (hn : 3 ≤ n)
    (ω : List (Fin n)) :
    graphSpin n F ⟨n - 1, by omega⟩
        ((omPlusCurtisDatum n F hn).nW
          ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd ω)) =
      (omPlusCurtisDatum n F hn).nW
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd
          (ω.map (omGraphSwap (by omega)))) := by
  induction ω with
  | nil => simp [CoxeterSystem.wordProd_nil, (omPlusCurtisDatum n F hn).nW_one]
  | cons i ω ih =>
      rw [List.map_cons, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
        omPlusCurtisDatum_two_nW_mul hF hn, omPlusCurtisDatum_two_nW_mul hF hn,
        map_mul, ih, w135c2_omfPBound_nW_simple hn i,
        w135c2_omfPBound_nW_simple hn (omGraphSwap (by omega) i), graphSpin_n_omPlus hn i]

private theorem w135c2_omfPBound_weylAction_wordProd_map {n : ℕ} (hn : 3 ≤ n)
    (ω : List (Fin n)) (γ : Fin n → ℤ) :
    weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd
          (ω.map (omGraphSwap (by omega)))) γ =
      weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd ω)
        (γ ∘ omGraphSwap (by omega)) ∘ omGraphSwap (by omega) := by
  induction ω generalizing γ with
  | nil =>
      funext a
      simp [CoxeterSystem.wordProd_nil, Function.comp_apply, omGraphSwap,
        Equiv.swap_apply_self]
  | cons i ω ih =>
      rw [List.map_cons, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
        weylAction_mul_apply, weylAction_mul_apply,
        w135c2_omfPBound_weylAction_simple_omGraphSwap hn i]
      have hih : weylAction (isFiniteType_cartanD n)
            ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd
              (ω.map (omGraphSwap (by omega)))) γ ∘ omGraphSwap (by omega) =
          weylAction (isFiniteType_cartanD n)
            ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd ω)
            (γ ∘ omGraphSwap (by omega)) := by
        rw [ih (γ := γ)]
        funext a
        simp [Function.comp_apply, omGraphSwap, Equiv.swap_apply_self]
      rw [hih]


theorem exists_graphSpin_nW_omPlus (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n)
    (w : (coxeterMatrix (isFiniteType_cartanD n)).Group) :
    ∃ w' : (coxeterMatrix (isFiniteType_cartanD n)).Group,
      graphSpin n F ⟨n - 1, by omega⟩ ((omPlusCurtisDatum n F hn).nW w) =
        (omPlusCurtisDatum n F hn).nW w' ∧
      ∀ γ, weylAction (isFiniteType_cartanD n) w' γ =
        weylAction (isFiniteType_cartanD n) w (γ ∘ omGraphSwap (by omega)) ∘
          omGraphSwap (by omega) := by
  obtain ⟨ω, -, rfl⟩ :=
    (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.exists_isReduced w
  exact ⟨(coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.wordProd
      (ω.map (omGraphSwap (by omega))),
    w135c2_omfPBound_graphSpin_nW_wordProd_map hF hn ω,
    w135c2_omfPBound_weylAction_wordProd_map hn ω⟩

end CFSG.LocalAnalysis.WeakClosure81
