module

public import CFSG.RankThree.Classical.SteinbergBJCharacterSpaces
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.RankThree.Classical

section Basic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
variable {Γ : Type*} [CommGroup Γ] {p : ℕ} {ρ : Γ →* Module.End K V} {ζ : K}

theorem mem_charSpace_zero {v : V} (hv : ∀ g, ρ g v = v) :
    v ∈ charSpace ρ ζ (0 : Additive Γ →+ ZMod p) :=
  mem_charSpace.mpr fun g => by simp [hv g]

theorem eq_of_mem_charSpace_zero {v : V} (hv : v ∈ charSpace ρ ζ (0 : Additive Γ →+ ZMod p))
    (g : Γ) : ρ g v = v := by
  have := mem_charSpace.mp hv g
  simpa using this

theorem Q_eq_zero_of_mem_charSpace [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ p) (hρQ : ∀ g v, Q (ρ g v) = Q v) {χ : Additive Γ →+ ZMod p}
    (hχ : χ ≠ 0) {v : V} (hv : v ∈ charSpace ρ ζ χ) : Q v = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : Γ, χ (Additive.ofMul g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hχ (AddMonoidHom.ext fun x => hcon (Additive.toMul x))
  have h1 := mem_charSpace.mp hv g
  have h2 := hρQ g v
  rw [h1, map_smul_eq_sq] at h2
  have hne : (ζ ^ (χ (Additive.ofMul g)).val) ^ 2 ≠ 1 := by
    intro h
    rw [_root_.sq, ← root_pow_val_add hζ.pow_eq_one] at h
    have h4 := (root_pow_val_eq_one_iff hζ _).mp h
    have : Fact p.Prime := ⟨hp⟩
    have h5 : (2 : ZMod p) ≠ 0 := by
      intro h6
      have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h6)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have h6 : (2 : ZMod p) * χ (Additive.ofMul g) = 0 := by rw [two_mul]; exact h4
    exact hg ((mul_eq_zero.mp h6).resolve_left h5)
  have h7 : ((ζ ^ (χ (Additive.ofMul g)).val) ^ 2 - 1) * Q v = 0 := by
    rw [sub_mul, one_mul, h2, sub_self]
  exact (mul_eq_zero.mp h7).resolve_left (sub_ne_zero.mpr hne)

theorem polar_eq_zero_of_eigen {g : Γ} {u s : V} {c : K} (hc : c ≠ 0) (hu : ρ g u = c • u)
    (hB : ∀ g u w, polar Q (ρ g u) (ρ g w) = polar Q u w) (h : polar Q u s = 0) :
    polar Q u (ρ g s) = 0 := by
  have h1 := hB g u s
  rw [hu, polar_smul_left_eq, h] at h1
  exact (mul_eq_zero.mp h1).resolve_left hc

end Basic

section Main

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}
variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {p : ℕ} [NeZero p] {ρ : Γ →* Module.End K V}
  {ζ : K}

omit [FiniteDimensional K V] [NeZero p] in
theorem charIdem_mem {S : Submodule K V} (hSinv : ∀ g, ∀ s ∈ S, ρ g s ∈ S)
    (χ : Additive Γ →+ ZMod p) {v : V} (hv : v ∈ S) : charIdem ρ ζ χ v ∈ S := by
  unfold charIdem
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  refine S.smul_mem _ (S.sum_mem fun g _ => ?_)
  rw [LinearMap.smul_apply]
  exact S.smul_mem _ (hSinv g v hv)

theorem exists_adapted_hypPairs [Fintype (Additive Γ →+ ZMod p)] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : (Fintype.card Γ : K) ≠ 0)
    (hρQ : ∀ g v, Q (ρ g v) = Q v) :
    ∀ S : Submodule K V, (∀ g, ∀ s ∈ S, ρ g s ∈ S) → PolarNondegOn Q S →
      ∃ (r : ℕ) (P : Fin r → HypPair Q) (χ : Fin r → Additive Γ →+ ZMod p),
        (∀ i, (P i).e ∈ S ∧ (P i).f ∈ S) ∧
        (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
        (∀ i, (P i).e ∈ charSpace ρ ζ (χ i) ∧ (P i).f ∈ charSpace ρ ζ (-χ i)) ∧
        (∀ x ∈ S, x ∈ pairsPerp P → Q x = 0 → x = 0) ∧
        (∀ g, ∀ x ∈ S, x ∈ pairsPerp P → ρ g x = x) := by
  classical
  have hρB : ∀ g u w, polar Q (ρ g u) (ρ g w) = polar Q u w := fun g u w => by
    simp only [QuadraticMap.polar, ← map_add, hρQ]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
  have hpowne : ∀ (χ : Additive Γ →+ ZMod p) (g : Γ), ζ ^ (χ (Additive.ofMul g)).val ≠ 0 :=
    fun χ g => pow_ne_zero _ hζ0
  intro S
  induction' hn : finrank K S using Nat.strong_induction_on with n ih generalizing S
  intro hSinv hS
  have step : ∀ (P₀ : HypPair Q) (χ₀ : Additive Γ →+ ZMod p), P₀.e ∈ S → P₀.f ∈ S →
      P₀.e ∈ charSpace ρ ζ χ₀ → P₀.f ∈ charSpace ρ ζ (-χ₀) →
      (∀ g, ∀ s ∈ S ⊓ P₀.perp, ρ g s ∈ S ⊓ P₀.perp) →
      ∃ (r : ℕ) (P : Fin r → HypPair Q) (χ : Fin r → Additive Γ →+ ZMod p),
        (∀ i, (P i).e ∈ S ∧ (P i).f ∈ S) ∧
        (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
        (∀ i, (P i).e ∈ charSpace ρ ζ (χ i) ∧ (P i).f ∈ charSpace ρ ζ (-χ i)) ∧
        (∀ x ∈ S, x ∈ pairsPerp P → Q x = 0 → x = 0) ∧
        (∀ g, ∀ x ∈ S, x ∈ pairsPerp P → ρ g x = x) := by
    intro P₀ χ₀ heS hfS heχ hfχ hinv
    have hlt : finrank K ↥(S ⊓ P₀.perp) < n := by
      have := finrank_inf_perp_add_two P₀ heS hfS
      omega
    obtain ⟨r, P, χ, h1, h2, h3, h4, h5⟩ :=
      ih _ hlt (S ⊓ P₀.perp) rfl hinv (hS.inf_perp P₀ heS hfS)
    have h0 : ∀ j, P₀.Orth (P j) := fun j => HypPair.orth_of_mem_perp (h1 j).1.2 (h1 j).2.2
    have hperp : ∀ x, x ∈ pairsPerp (Fin.cons P₀ P : Fin (r + 1) → HypPair Q) →
        x ∈ P₀.perp ∧ x ∈ pairsPerp P := fun x hx =>
      ⟨by simpa using (mem_pairsPerp _).mp hx 0,
        (mem_pairsPerp _).mpr fun j => by simpa using (mem_pairsPerp _).mp hx j.succ⟩
    refine ⟨r + 1, Fin.cons P₀ P, Fin.cons χ₀ χ, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => exact ⟨heS, hfS⟩
      | succ j => exact ⟨(h1 j).1.1, (h1 j).2.1⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => exact h0 j
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (h0 i).symm
        | succ j => exact h2 i j fun h => hij (by rw [h])
    · intro i
      induction i using Fin.cases with
      | zero => exact ⟨heχ, hfχ⟩
      | succ j => exact h3 j
    · intro x hxS hx hQx
      exact h4 x ⟨hxS, (hperp x hx).1⟩ (hperp x hx).2 hQx
    · intro g x hxS hx
      exact h5 g x ⟨hxS, (hperp x hx).1⟩ (hperp x hx).2
  by_cases hA : ∃ χ : Additive Γ →+ ZMod p, χ ≠ 0 ∧ ∃ v ∈ S, v ∈ charSpace ρ ζ χ ∧ v ≠ 0
  ·
    obtain ⟨χ, hχ, v, hvS, hvχ, hv0⟩ := hA
    have hQv : Q v = 0 := Q_eq_zero_of_mem_charSpace hp hp2 hζ hρQ hχ hvχ
    obtain ⟨y, hyS, hvy⟩ := hS.exists_polar_ne_zero hvS hv0
    have hsum := eq_sum_charIdem_apply (ρ := ρ) hp hζ hexp hΓ y
    have hy' : polar Q v (charIdem ρ ζ (-χ) y) ≠ 0 := by
      intro h0
      apply hvy
      rw [hsum, polar_sum_right]
      refine Finset.sum_eq_zero fun ψ _ => ?_
      by_cases hψ : ψ = -χ
      · rw [hψ]
        exact h0
      · exact apply_eq_zero_of_mem_charSpace hζ (polarBilin Q) hρB
          (fun h => hψ (eq_neg_of_add_eq_zero_right h)) hvχ
          (charIdem_apply_mem hζ.pow_eq_one ψ y)
    set y' := charIdem ρ ζ (-χ) y with hy'def
    set c := polar Q v y' with hc
    have hy'S : y' ∈ S := charIdem_mem hSinv _ hyS
    have hy'χ : y' ∈ charSpace ρ ζ (-χ) := charIdem_apply_mem hζ.pow_eq_one _ y
    have hwS : c⁻¹ • y' ∈ S := S.smul_mem _ hy'S
    have hwχ : c⁻¹ • y' ∈ charSpace ρ ζ (-χ) := Submodule.smul_mem _ _ hy'χ
    have hQw : Q (c⁻¹ • y') = 0 :=
      Q_eq_zero_of_mem_charSpace hp hp2 hζ hρQ (neg_ne_zero.mpr hχ) hwχ
    have hvw : polar Q v (c⁻¹ • y') = 1 := by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hy']
    refine step ⟨v, c⁻¹ • y', hQv, hQw, hvw⟩ χ hvS hwS hvχ hwχ ?_
    rintro g s ⟨hsS, hsP⟩
    refine ⟨hSinv g s hsS, ?_⟩
    obtain ⟨hs1, hs2⟩ := HypPair.mem_perp.mp hsP
    exact HypPair.mem_perp.mpr
      ⟨polar_eq_zero_of_eigen (hpowne χ g) (mem_charSpace.mp hvχ g) hρB hs1,
        polar_eq_zero_of_eigen (hpowne (-χ) g) (mem_charSpace.mp hwχ g) hρB hs2⟩
  · push Not at hA
    have hfix : ∀ g, ∀ s ∈ S, ρ g s = s := by
      intro g s hsS
      have hs := eq_sum_charIdem_apply (ρ := ρ) hp hζ hexp hΓ s
      have hterm : ∀ χ : Additive Γ →+ ZMod p, ρ g (charIdem ρ ζ χ s) = charIdem ρ ζ χ s := by
        intro χ
        by_cases hχ : χ = 0
        · subst hχ
          exact eq_of_mem_charSpace_zero (charIdem_apply_mem hζ.pow_eq_one 0 s) g
        · have h0 : charIdem ρ ζ χ s = 0 :=
            hA χ hχ _ (charIdem_mem hSinv χ hsS) (charIdem_apply_mem hζ.pow_eq_one χ s)
          rw [h0, map_zero]
      calc ρ g s = ρ g (∑ χ : Additive Γ →+ ZMod p, charIdem ρ ζ χ s) := congrArg (ρ g) hs
        _ = ∑ χ : Additive Γ →+ ZMod p, charIdem ρ ζ χ s := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun χ _ => hterm χ
        _ = s := hs.symm
    by_cases hB1 : ∃ x ∈ S, x ≠ 0 ∧ Q x = 0
    · obtain ⟨x, hxS, hx0, hQx⟩ := hB1
      obtain ⟨y, hyS, hxy⟩ := hS.exists_polar_ne_zero hxS hx0
      have hhS : (polar Q x y)⁻¹ • y ∈ S := S.smul_mem _ hyS
      have hxh : polar Q x ((polar Q x y)⁻¹ • y) = 1 := by
        rw [polar_smul_right_eq, inv_mul_cancel₀ hxy]
      have hfS : (HypPair.ofPolarEqOne hQx hxh).f ∈ S :=
        S.sub_mem hhS (S.smul_mem _ hxS)
      have heχ : (HypPair.ofPolarEqOne hQx hxh).e ∈ charSpace ρ ζ (0 : Additive Γ →+ ZMod p) :=
        mem_charSpace_zero fun g => hfix g x hxS
      have hfχ : (HypPair.ofPolarEqOne hQx hxh).f ∈
          charSpace ρ ζ (-(0 : Additive Γ →+ ZMod p)) := by
        rw [neg_zero]
        exact mem_charSpace_zero fun g => hfix g _ hfS
      refine step _ 0 hxS hfS heχ hfχ ?_
      intro g s hs
      rw [hfix g s hs.1]
      exact hs
    · refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, ?_, ?_⟩
      · intro x hxS _ hQx
        by_contra hx0
        exact hB1 ⟨x, hxS, hx0, hQx⟩
      · intro g x hxS _
        exact hfix g x hxS

end Main

end CFSG.RankThree.PartOne.KCOrthogonal
