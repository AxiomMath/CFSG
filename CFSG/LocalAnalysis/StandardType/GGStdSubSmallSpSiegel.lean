module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpBlock
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus

public section

namespace CFSG.StandardType

namespace StdSubSp

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank TableBSymp CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

section Siegel

theorem diagSp_conj_leviEmbedSL_transvection {i j : Fin n} (hij : i ≠ j) (u : Fin n → Kˣ)
    (b : K) :
    diagSp K n u * leviEmbedSL K n (SpecialLinearGroup.transvection hij b) * (diagSp K n u)⁻¹ =
      leviEmbedSL K n
        (SpecialLinearGroup.transvection hij ((u i : K) * b * (((u j)⁻¹ : Kˣ) : K))) := by
  have key : TauCeti.diagGL u * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij b) *
      (TauCeti.diagGL u)⁻¹ = SpecialLinearGroup.toGL
        (SpecialLinearGroup.transvection hij ((u i : K) * b * (((u j)⁻¹ : Kˣ) : K))) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← map_inv, TauCeti.diagGL_coe, TauCeti.diagGL_coe]
    change diagonal _ * Matrix.transvection i j b * diagonal _ = Matrix.transvection i j _
    rw [TauCeti.diagonal_mul_transvection_mul_diagonal]
    · simp
    · intro a
      simp
  rw [diagSp_apply, leviEmbedSL, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
    ← map_mul, ← map_mul, key]

@[expose] noncomputable def swapSL [CharP K 2] {i j : Fin n} (hij : i ≠ j) : SL(n, K) :=
  ⟨(Equiv.swap i j).permMatrix K, by
    rw [Matrix.det_permutation, Equiv.Perm.sign_swap hij]
    simp [CharTwo.neg_eq]⟩

theorem swapSL_conj_diagSp [CharP K 2] {i j : Fin n} (hij : i ≠ j) (u : Fin n → Kˣ) :
    leviEmbedSL K n (swapSL hij) * diagSp K n u * (leviEmbedSL K n (swapSL hij))⁻¹ =
      diagSp K n (u ∘ Equiv.swap i j) := by
  rw [diagSp_apply, diagSp_apply, leviEmbedSL, MonoidHom.comp_apply, ← map_inv, ← map_mul,
    ← map_mul]
  congr 1
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (SpecialLinearGroup.toGL (swapSL hij))
    (Equiv.swap i j) rfl u, mul_inv_cancel_right]

variable {p : ℕ} {ζ : Kˣ}

theorem swapSL_conj_spTorusSt [CharP K 2] (hζ : ζ ^ p = 1) {i j : Fin n} (hij : i ≠ j)
    (g : Fin n → Multiplicative (ZMod p)) :
    leviEmbedSL K n (swapSL hij) * spTorusSt hζ g * (leviEmbedSL K n (swapSL hij))⁻¹ =
      spTorusSt hζ (g ∘ Equiv.swap i j) := by
  rw [spTorusSt_eq_diagSp, spTorusSt_eq_diagSp, swapSL_conj_diagSp]
  rfl

theorem units_mul_self_ne_one_of_pow {s : Kˣ} (hs : s ≠ 1) (hsp : s ^ p = 1) (hp : Odd p) :
    s * s ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := hp
  apply hs
  have h2 : s ^ 2 = 1 := by rw [sq]; exact h
  have h3 : s ^ p = (s ^ 2) ^ m * s := by rw [hm, pow_succ s (2 * m), pow_mul s 2 m]
  rw [h3, h2, one_pow, one_mul] at hsp
  exact hsp

theorem mulSingle_mul_pow_val [NeZero p] (i₀ i₁ : Fin n) (δ : Multiplicative (ZMod p)) :
    (Pi.mulSingle i₀ (Multiplicative.ofAdd (1 : ZMod p)) *
        Pi.mulSingle i₁ (Multiplicative.ofAdd (1 : ZMod p))⁻¹ : Fin n → Multiplicative (ZMod p)) ^ (Multiplicative.toAdd δ).val =
      (Pi.mulSingle i₀ δ * Pi.mulSingle i₁ δ⁻¹ : Fin n → Multiplicative (ZMod p)) := by
  have hx : Multiplicative.ofAdd (1 : ZMod p) ^ (Multiplicative.toAdd δ).val = δ := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, inv_pow, hx]

theorem ggStdSubEltData_siegel [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {c : Multiplicative (ZMod p)}
    (hc : c ≠ 1) :
    GGStdSubEltData p (spTorusSt (n := n) hζ).range (spTorusSt hζ fun _ => c) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  set s := zmodPowHom hζ c with hs
  have hs1 : s * s ≠ 1 := by
    refine units_mul_self_ne_one_of_pow (fun h => hc ((zmodPowHom_eq_one_iff hζ hζo).mp h)) ?_
      (hp.odd_of_ne_two hp2)
    rw [hs, ← map_pow]
    have : c ^ p = 1 := by
      rw [← ofAdd_toAdd c, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
    rw [this, map_one]
  have ha : spTorusSt hζ (fun _ : Fin n => c) = diagSp K n (fun _ => s) := by
    rw [spTorusSt_eq_diagSp]
  set X : Multiplicative K →* StatedSp n K :=
    (leviEmbedSL K n).comp (SpecialLinearGroup.transvectionHom h01) with hX
  have hXapp : ∀ b, X b = leviEmbedSL K n (SpecialLinearGroup.transvection h01
      (Multiplicative.toAdd b)) := fun b => by
    rw [hX, MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply]
  have hXinj : Function.Injective X := by
    intro b b' h
    rw [hXapp, hXapp] at h
    exact Multiplicative.toAdd.injective
      (SpecialLinearGroup.transvection_injective h01 (leviEmbedSL_injective h))
  have hT : ∀ y ∈ (spTorusSt (n := n) hζ).range, ∀ u ∈ X.range, y * u * y⁻¹ ∈ X.range := by
    rintro _ ⟨g, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨Multiplicative.ofAdd (((zmodPowHom hζ (g i₀) : Kˣ) : K) * Multiplicative.toAdd b *
      (((zmodPowHom hζ (g i₁))⁻¹ : Kˣ) : K)), ?_⟩
    rw [hXapp, hXapp, spTorusSt_eq_diagSp, diagSp_conj_leviEmbedSL_transvection, toAdd_ofAdd]
  set x₁ : Multiplicative (ZMod p) := Multiplicative.ofAdd 1 with hx₁
  set g₀ : Fin n → Multiplicative (ZMod p) := Pi.mulSingle i₀ x₁ * Pi.mulSingle i₁ x₁⁻¹
    with hg₀
  have hg₀₀ : g₀ i₀ = x₁ := by
    rw [hg₀, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, mul_one]
  have hg₀₁ : g₀ i₁ = x₁⁻¹ := by
    rw [hg₀, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm h01), one_mul]
  set tb := spTorusSt (K := K) hζ g₀ with htb
  have htbD : tb ∈ siegelLevi K n := by
    have hprod : ∏ i, g₀ i = 1 := by
      rw [hg₀]
      simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle',
        ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), mul_inv_cancel]
    have hdet : (diagonal fun i => ((zmodPowHom hζ (g₀ i) : Kˣ) : K)).det = 1 := by
      rw [det_diagonal, ← Units.coe_prod, ← map_prod, hprod, map_one, Units.val_one]
    set X₀ : SL(n, K) := ⟨_, hdet⟩ with hX₀
    refine ⟨X₀, ?_⟩
    rw [htb, spTorusSt_eq_diagSp, diagSp_apply]
    show leviEmbedGL K n (SpecialLinearGroup.toGL X₀) = _
    congr 1
    apply Units.ext
    rw [TauCeti.diagGL_coe]
    rfl
  set w := leviEmbedSL K n (swapSL (K := K) h01) with hw
  refine ⟨siegelLevi K n, ?_, ?_, isQuasisimple_siegelLevi hK hn, X.range, ?_, ?_, ?_, hT,
    tb, htbD, ?_, ?_, ?_, ⟨X (Multiplicative.ofAdd 1), ⟨_, rfl⟩, ?_⟩, w, ⟨_, rfl⟩, ?_, ?_⟩
  · intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff, ha]
    exact ((Subgroup.mem_centralizer_iff.mp (siegelLeviGL_le_centralizer_siegelTorus
      (siegelLevi_le_siegelLeviGL hd))) _ (diagSp_const_mem_siegelTorus s)).symm
  · intro c' hc' d hd
    have hc'' : c' * diagSp K n (fun _ => s) = diagSp K n (fun _ => s) * c' := by
      rw [← ha]
      exact Subgroup.mem_centralizer_singleton_iff.mp hc'
    have h1 := commutator_mem_siegelLevi (mem_siegelLeviGL_of_commute hs1 hc'')
      (siegelLevi_le_siegelLeviGL hd)
    have e : c' * d * c'⁻¹ = (c' * d * c'⁻¹ * d⁻¹) * d := by group
    rw [e]
    exact mul_mem h1 hd
  · rintro _ ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  · intro h
    have hmem : X (Multiplicative.ofAdd 1) ∈ X.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one X] at hmem
    have h2 := congrArg Multiplicative.toAdd (hXinj hmem)
    rw [toAdd_ofAdd, toAdd_one] at h2
    exact one_ne_zero h2
  · rintro ⟨_, b, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← map_pow]
    have : b ^ 2 = 1 := by
      rw [← ofAdd_toAdd b, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [this, map_one]
    rfl
  · rw [htb, ← map_pow]
    have : g₀ ^ p = 1 := by
      have hx : x₁ ^ p = 1 := by
        rw [hx₁, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
      rw [hg₀, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, inv_pow, hx, inv_one,
        Pi.mulSingle_one, Pi.mulSingle_one, one_mul]
    rw [this, map_one]
  · rintro _ ⟨g, rfl⟩
    rw [htb, ← map_mul, ← map_mul, mul_comm]
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact hT tb ⟨g₀, rfl⟩ u
    · intro hu
      have := hT tb⁻¹ ⟨g₀⁻¹, by rw [map_inv]⟩ _ hu
      simpa [mul_assoc] using this
  · intro hcomm
    have h1 : tb * X (Multiplicative.ofAdd 1) * tb⁻¹ = X (Multiplicative.ofAdd 1) := by
      rw [hcomm, mul_inv_cancel_right]
    rw [hXapp, htb, spTorusSt_eq_diagSp, diagSp_conj_leviEmbedSL_transvection, hg₀₀, hg₀₁,
      hx₁, zmodPowHom_ofAdd_one, map_inv, zmodPowHom_ofAdd_one, inv_inv, toAdd_ofAdd] at h1
    have h2 := SpecialLinearGroup.transvection_injective h01 (leviEmbedSL_injective h1)
    rw [mul_one] at h2
    exact units_mul_self_ne_one hp hp2 hζo h2
  · rw [hw, swapSL_conj_spTorusSt, ← map_inv]
    congr 1
    funext j
    by_cases hj0 : j = i₀
    · subst hj0
      rw [Function.comp_apply, Equiv.swap_apply_left, hg₀₁, Pi.inv_apply, hg₀₀]
    · by_cases hj1 : j = i₁
      · subst hj1
        rw [Function.comp_apply, Equiv.swap_apply_right, hg₀₀, Pi.inv_apply, hg₀₁, inv_inv]
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hj0 hj1, Pi.inv_apply, hg₀,
          Pi.mul_apply, Pi.mulSingle_eq_of_ne hj0, Pi.mulSingle_eq_of_ne hj1, one_mul, inv_one]
  · rintro _ ⟨g, rfl⟩
    rw [hw, swapSL_conj_spTorusSt, ← map_inv, ← map_mul]
    set δ := (g i₀)⁻¹ * g i₁ with hδ
    have hg : g⁻¹ * (g ∘ Equiv.swap i₀ i₁) =
        (Pi.mulSingle i₀ δ * Pi.mulSingle i₁ δ⁻¹ : Fin n → Multiplicative (ZMod p)) := by
      funext j
      by_cases hj0 : j = i₀
      · subst hj0
        simp [Pi.mulSingle_eq_of_ne h01, hδ]
      · by_cases hj1 : j = i₁
        · subst hj1
          simp [Pi.mulSingle_eq_of_ne (Ne.symm h01), hδ, mul_comm]
        · simp [Equiv.swap_apply_of_ne_of_ne hj0 hj1, Pi.mulSingle_eq_of_ne hj0,
            Pi.mulSingle_eq_of_ne hj1]
    rw [hg]
    refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd δ).val : ℤ), ?_⟩
    rw [zpow_natCast, htb, ← map_pow, hg₀, hx₁, mulSingle_mul_pow_val]

end Siegel

section Swap

@[expose] def pairSwapOn (S : Finset (Fin n)) : Equiv.Perm (Fin n ⊕ Fin n) where
  toFun := Sum.elim (fun i => if i ∈ S then Sum.inr i else Sum.inl i)
    (fun i => if i ∈ S then Sum.inl i else Sum.inr i)
  invFun := Sum.elim (fun i => if i ∈ S then Sum.inr i else Sum.inl i)
    (fun i => if i ∈ S then Sum.inl i else Sum.inr i)
  left_inv := by
    intro x
    rcases x with i | i <;> by_cases hi : i ∈ S <;> simp [hi]
  right_inv := by
    intro x
    rcases x with i | i <;> by_cases hi : i ∈ S <;> simp [hi]

theorem pairSwapOn_inl (S : Finset (Fin n)) (i : Fin n) :
    pairSwapOn S (Sum.inl i) = if i ∈ S then Sum.inr i else Sum.inl i := rfl

theorem pairSwapOn_inr (S : Finset (Fin n)) (i : Fin n) :
    pairSwapOn S (Sum.inr i) = if i ∈ S then Sum.inl i else Sum.inr i := rfl

theorem pairSwapOn_symm_apply (S : Finset (Fin n)) (x : Fin n ⊕ Fin n) :
    (pairSwapOn S).symm x = pairSwapOn S x := rfl

theorem largeEvenSpForm_pairSwapOn [CharP K 2] (S : Finset (Fin n)) (x y : Fin n ⊕ Fin n) :
    LargeEvenSpForm K n (pairSwapOn S x) (pairSwapOn S y) = LargeEvenSpForm K n x y := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  rw [largeEvenSpForm_apply, largeEvenSpForm_apply]
  rcases x with a | a <;> rcases y with b | b <;> by_cases hab : a = b
  all_goals first
    | (subst hab; by_cases ha : a ∈ S <;> simp [pairSwapOn_inl, pairSwapOn_inr, ha, hneg])
    | (by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
        simp [pairSwapOn_inl, pairSwapOn_inr, ha, hb, hab])

@[expose] noncomputable def spSwapOnSt [CharP K 2] (S : Finset (Fin n)) : StatedSp n K :=
  ⟨TauCeti.permutationGL (pairSwapOn S), permutationGL_mem_sp _ (largeEvenSpForm_pairSwapOn S)⟩

theorem spSwapOnSt_conj_spTorusSt [CharP K 2] {p : ℕ} {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (S : Finset (Fin n)) (g : Fin n → Multiplicative (ZMod p)) :
    spSwapOnSt S * spTorusSt hζ g * (spSwapOnSt S)⁻¹ =
      spTorusSt hζ (fun i => if i ∈ S then (g i)⁻¹ else g i) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  show TauCeti.permutationGL (pairSwapOn S) * spTorusGL hζ g *
      (TauCeti.permutationGL (pairSwapOn S))⁻¹ = spTorusGL hζ _
  rw [spTorusGL_apply, spTorusGL_apply, TauCeti.mul_diagGL_of_coe_eq_permMatrix
    (TauCeti.permutationGL (pairSwapOn S)) (pairSwapOn S)⁻¹ (TauCeti.permutationGL_coe _),
    mul_inv_cancel_right]
  congr 1
  funext x
  rcases x with i | i <;> by_cases hi : i ∈ S <;>
    simp [pairedUnits, pairSwapOn_symm_apply, pairSwapOn_inl, pairSwapOn_inr, hi]

end Swap

section Pair

variable {p : ℕ} {ζ : Kˣ}

theorem spTorusSt_injective [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (spTorusSt (K := K) (n := n) hζ) := by
  intro f f' h
  rw [spTorusSt_eq_diagSp, spTorusSt_eq_diagSp] at h
  have h1 := diagSp_injective h
  funext i
  have h2 : zmodPowHom hζ (f i) = zmodPowHom hζ (f' i) := congrFun h1 i
  have h3 : zmodPowHom hζ (f i / f' i) = 1 := by rw [map_div, h2, div_self']
  exact div_eq_one.mp ((zmodPowHom_eq_one_iff hζ hζo).mp h3)

theorem ne_inv_of_ne_one (hp : p.Prime) (hp2 : p ≠ 2) {v : Multiplicative (ZMod p)}
    (hv : v ≠ 1) : v ≠ v⁻¹ := by
  intro h
  apply hv
  have h2 : v ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel v
  have hpw : v ^ p = 1 := by
    rw [← ofAdd_toAdd v, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have h3 : v ^ (2 * m + 1) = 1 := by rw [← hm]; exact hpw
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h3
  exact h3

theorem zpow_eq_one_of_zpow_eq_one (hp : p.Prime) {v : Multiplicative (ZMod p)} (hv : v ≠ 1)
    {k : ℤ} (h : v ^ k = 1) (w : Multiplicative (ZMod p)) : w ^ k = 1 := by
  have := Fact.mk hp
  have h1 := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow, toAdd_one, zsmul_eq_mul] at h1
  have hk0 : (k : ZMod p) = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [← ofAdd_toAdd v, h2, ofAdd_zero]) hv
  rw [← ofAdd_toAdd (w ^ k), toAdd_zpow, zsmul_eq_mul, hk0, zero_mul, ofAdd_zero]

theorem ofAdd_one_ne_one (hp : p.Prime) : Multiplicative.ofAdd (1 : ZMod p) ≠ 1 := by
  have := Fact.mk hp
  intro h
  have h1 := congrArg Multiplicative.toAdd h
  rw [toAdd_ofAdd, toAdd_one] at h1
  exact one_ne_zero h1

theorem eq_or_eq_inv_of_central (hp : p.Prime) (hp2 : p ≠ 2) (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) {f : Fin n → Multiplicative (ZMod p)} (hf : ∀ i, f i ≠ 1)
    (hcent : ∀ g : Fin n → Multiplicative (ZMod p),
      (∀ c ∈ Subgroup.centralizer ({spTorusSt hζ f} : Set (StatedSp n K)),
        spTorusSt hζ g * c = c * spTorusSt hζ g) →
      spTorusSt hζ g ∈ Subgroup.zpowers (spTorusSt hζ f))
    (i j : Fin n) : f j = f i ∨ f j = (f i)⁻¹ := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  rw [not_or] at hcon
  have hfi : f i ≠ (f i)⁻¹ := ne_inv_of_ne_one hp hp2 (hf i)
  set φ : Multiplicative (ZMod p) → Multiplicative (ZMod p) := fun v =>
    if v = f i then Multiplicative.ofAdd 1 else
      if v = (f i)⁻¹ then Multiplicative.ofAdd (-1) else 1 with hφ
  have hφinv : ∀ v, φ v⁻¹ = (φ v)⁻¹ := by
    intro v
    rcases eq_or_ne v (f i) with h1 | h1
    · rw [h1]
      simp [hφ, Ne.symm hfi, ofAdd_neg]
    · rcases eq_or_ne v (f i)⁻¹ with h2 | h2
      · rw [h2]
        simp [hφ, Ne.symm hfi, ofAdd_neg]
      · have h3 : v⁻¹ ≠ f i := fun h => h2 (by rw [← h]; simp)
        have h4 : v⁻¹ ≠ (f i)⁻¹ := fun h => h1 (inv_injective h)
        simp [hφ, h1, h2, h3, h4]
  set g : Fin n → Multiplicative (ZMod p) := fun k => φ (f k) with hg
  set χ := zmodPowHom (L' := Kˣ) hζ with hχ
  set ε : Fin n ⊕ Fin n → Multiplicative (ZMod p) := Sum.elim f (fun k => (f k)⁻¹) with hε
  have hα : ∀ x, diagSpEntry (fun k => χ (f k)) x = ((χ (ε x) : Kˣ) : K) := by
    intro x
    rcases x with k | k <;> simp [hε, map_inv]
  have hβ : ∀ x, diagSpEntry (fun k => χ (g k)) x = ((χ (φ (ε x)) : Kˣ) : K) := by
    intro x
    rcases x with k | k
    · simp [hε, hg]
    · simp [hε, hg, hφinv, map_inv]
  have hχinj : ∀ a b, ((χ a : Kˣ) : K) = ((χ b : Kˣ) : K) → a = b := by
    intro a b h
    have h1 : χ (a / b) = 1 := by rw [map_div, Units.ext h, div_self']
    exact div_eq_one.mp ((zmodPowHom_eq_one_iff hζ hζo).mp h1)
  have hcomm : ∀ c ∈ Subgroup.centralizer ({spTorusSt hζ f} : Set (StatedSp n K)),
      spTorusSt hζ g * c = c * spTorusSt hζ g := by
    intro c hc
    refine commute_of_diag_of_forall (mat_spTorusSt hζ f) (mat_spTorusSt hζ g)
      (fun a b hab => ?_) (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hab' : ε a = ε b := hχinj _ _ (by rw [← hα, ← hα]; exact hab)
    show diagSpEntry (fun k => χ (g k)) a = diagSpEntry (fun k => χ (g k)) b
    rw [hβ, hβ, hab']
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcent g hcomm)
  rw [← map_zpow] at hk
  have hfk := spTorusSt_injective hζ hζo hk
  have hj : f j ^ k = 1 := by
    have h1 := congrFun hfk j
    rw [Pi.pow_apply] at h1
    rw [h1]
    simp [hg, hφ, hcon.1, hcon.2]
  have hi : f i ^ k = Multiplicative.ofAdd 1 := by
    have h1 := congrFun hfk i
    rw [Pi.pow_apply] at h1
    rw [h1]
    simp [hg, hφ]
  rw [zpow_eq_one_of_zpow_eq_one hp (hf j) hj (f i)] at hi
  exact ofAdd_one_ne_one hp hi.symm

end Pair

section CaseTwo

variable {p : ℕ} {ζ : Kˣ}

theorem ggStdSubEltData_of_ne_one [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {f : Fin n → Multiplicative (ZMod p)} (hf : ∀ i, f i ≠ 1)
    (hcent : ∀ g : Fin n → Multiplicative (ZMod p),
      (∀ c ∈ Subgroup.centralizer ({spTorusSt hζ f} : Set (StatedSp n K)),
        spTorusSt hζ g * c = c * spTorusSt hζ g) →
      spTorusSt hζ g ∈ Subgroup.zpowers (spTorusSt hζ f)) :
    GGStdSubEltData p (spTorusSt (n := n) hζ).range (spTorusSt hζ f) := by
  classical
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set c := f i₀ with hc
  have hfc : ∀ j, f j = c ∨ f j = c⁻¹ := eq_or_eq_inv_of_central hp hp2 hζo hζ hf hcent i₀
  set S : Finset (Fin n) := Finset.univ.filter fun j => f j ≠ c with hS
  set σ := spSwapOnSt (K := K) S with hσ
  have hσf : σ * spTorusSt hζ f * σ⁻¹ = spTorusSt hζ fun _ => c := by
    rw [hσ, spSwapOnSt_conj_spTorusSt]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · have hj' : f j ≠ c := by simpa [hS] using hj
      rw [ite_eq_left hj, (hfc j).resolve_left hj', inv_inv]
    · have hj' : f j = c := by simpa [hS] using hj
      rw [ite_eq_right hj, hj']
  have hσT : (spTorusSt (n := n) hζ).range.map (MulAut.conj σ).toMonoidHom =
      (spTorusSt (n := n) hζ).range := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, (spSwapOnSt_conj_spTorusSt hζ S g).symm⟩
    · rintro _ ⟨g, rfl⟩
      refine ⟨spTorusSt hζ (fun i => if i ∈ S then (g i)⁻¹ else g i), ⟨_, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hσ, spSwapOnSt_conj_spTorusSt]
      congr 1
      funext i
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi, ite_eq_left hi, inv_inv]
      · rw [ite_eq_right hi, ite_eq_right hi]
  apply GGStdSubEltData.of_mulEquiv (MulAut.conj σ)
  rw [hσT, MulAut.conj_apply, hσf]
  exact ggStdSubEltData_siegel hK hn hp hp2 hζo hζ (hf i₀)

theorem ggStdSubEltData_spTorusSt [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 2 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (f : Fin n → Multiplicative (ZMod p))
    (hcent : ∀ g : Fin n → Multiplicative (ZMod p),
      (∀ c ∈ Subgroup.centralizer ({spTorusSt hζ f} : Set (StatedSp n K)),
        spTorusSt hζ g * c = c * spTorusSt hζ g) →
      spTorusSt hζ g ∈ Subgroup.zpowers (spTorusSt hζ f)) :
    GGStdSubEltData p (spTorusSt (n := n) hζ).range (spTorusSt hζ f) := by
  by_cases h : ∃ k, f k = 1
  · obtain ⟨k, hk⟩ := h
    exact ggStdSubEltData_of_eq_one hK hp hp2 hζo hζ hk
  · simp only [not_exists] at h
    exact ggStdSubEltData_of_ne_one hK hn hp hp2 hζo hζ h hcent

end CaseTwo

end StdSubSp

end CFSG.StandardType

end
