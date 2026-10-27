module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusWitness

public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

section Roots

variable {r : ℕ} {K : Type} [Field K] {x : StatedSp r K} {h : primaryFactors (spEnd x)} {p : ℕ}

theorem exists_unit_root (hp : 0 < p) (hnt : orderOf (AdjoinRoot.root (h : K[X])) = p) :
    ∃ lam : (AdjoinRoot (h : K[X]))ˣ, (lam : AdjoinRoot (h : K[X])) =
      AdjoinRoot.root (h : K[X]) ∧ orderOf lam = p := by
  have hfin : IsOfFinOrder (AdjoinRoot.root (h : K[X])) :=
    orderOf_pos_iff.mp (by rw [hnt]; exact hp)
  obtain ⟨lam, hlam⟩ := hfin.isUnit
  exact ⟨lam, hlam, by rw [← orderOf_units, hlam, hnt]⟩

end Roots

section Paired

variable {r : ℕ} {K : Type} [Field K] {x : StatedSp r K} {h : primaryFactors (spEnd x)} {p : ℕ}

theorem nonempty_torusBlock_of_paired {ℓ f : ℕ} (hP : SpPairedBlock ℓ f p x h) (hp : 0 < p)
    (hnt : orderOf (AdjoinRoot.root (h : K[X])) = p) :
    Nonempty (TorusBlock x h p (primaryMultiplicity (spEnd x) (h : K[X]))) := by
  obtain ⟨φ, hφ, -⟩ := hP.factor
  obtain ⟨lam, -, hlamo⟩ := exists_unit_root hp hnt
  let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot (h : K[X]))
    (primaryComponent (spEnd x) (h : K[X]))
  let ψ := gl.toMonoidHom.comp φ.toMonoidHom
  have hsurj : Function.Surjective ψ := gl.surjective.comp φ.surjective
  have hrange : ∀ d, d ∈ ψ.range := fun d => MonoidHom.mem_range.2 (hsurj d)
  exact ⟨{
    F := spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}
    ψ := ψ
    injective := gl.injective.comp φ.injective
    act := fun g w => hφ g w w.2
    basis := Module.finBasis _ _
    lam := lam
    lam_pow := by rw [← hlamo]; exact pow_orderOf_eq_one lam
    lam_order := hlamo
    diag := fun c _ => hrange _
    perm := fun τ => hrange _
    sign := fun i => hrange _ }⟩

end Paired

section SelfDual

variable {r : ℕ} {K : Type} [Field K] {x : StatedSp r K} {h : primaryFactors (spEnd x)} {p : ℕ}

theorem nonempty_torusBlock_of_selfDual {ℓ f : ℕ} (hS : SpSelfDualBlock ℓ f p x h) (hp : 0 < p)
    (hnt : orderOf (AdjoinRoot.root (h : K[X])) = p) :
    Nonempty (TorusBlock x h p (primaryMultiplicity (spEnd x) (h : K[X]))) := by
  obtain ⟨d, -, -, σ, -, -, -, hσroot, -, hE, hbar, Hf, -, -, -, ⟨e, he⟩, φ, hφ⟩ :=
    hS.exists_half
  obtain ⟨lam, hlam, hlamo⟩ := exists_unit_root hp hnt
  let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot (h : K[X]))
    (primaryComponent (spEnd x) (h : K[X]))
  let ψ := gl.toMonoidHom.comp ((sesqUnitaryGroup Hf).subtype.comp φ.toMonoidHom)
  have hcoe : ∀ (δ : primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
      primaryComponent (spEnd x) (h : K[X])) u,
      (((gl.symm δ : blockGL (spEnd x) (h : K[X])) :
        Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) u) = δ u :=
    fun δ u => congrArg (fun f => f u) (gl.apply_symm_apply δ)
  have key : ∀ δ : primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
      primaryComponent (spEnd x) (h : K[X]), (∀ u v, Hf (δ u) (δ v) = Hf u v) → δ ∈ ψ.range := by
    intro δ hδ
    have hmem : gl.symm δ ∈ sesqUnitaryGroup Hf :=
      mem_sesqUnitaryGroup.2 fun u v => by rw [hcoe, hcoe]; exact hδ u v
    refine MonoidHom.mem_range.2 ⟨φ.symm ⟨gl.symm δ, hmem⟩, ?_⟩
    change gl ((φ (φ.symm ⟨gl.symm δ, hmem⟩) : sesqUnitaryGroup Hf) :
      blockGL (spEnd x) (h : K[X])) = δ
    rw [MulEquiv.apply_symm_apply]
    exact gl.apply_symm_apply δ
  have hu0 : (lam : AdjoinRoot (h : K[X])) ≠ 0 := lam.ne_zero
  have hσlam : hE.bar (lam : AdjoinRoot (h : K[X])) = (lam : AdjoinRoot (h : K[X]))⁻¹ := by
    rw [hbar, hlam, hσroot]
  have hnorm : ∀ c : (AdjoinRoot (h : K[X]))ˣ, c ∈ Subgroup.zpowers lam →
      hE.bar (c : AdjoinRoot (h : K[X])) * (c : AdjoinRoot (h : K[X])) = 1 := by
    rintro c ⟨k, rfl⟩
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hσlam, ← mul_zpow, inv_mul_cancel₀ hu0, one_zpow]
  exact ⟨{
    F := spSupported x {(h : K[X])}
    ψ := ψ
    injective := gl.injective.comp (Subtype.val_injective.comp φ.injective)
    act := fun g w => hφ g w w.2
    basis := e
    lam := lam
    lam_pow := by rw [← hlamo]; exact pow_orderOf_eq_one lam
    lam_order := hlamo
    diag := fun c hc => key _ (herm_diag e Hf he c (fun i => hnorm _ (hc i)))
    perm := fun τ => key _ (herm_perm e Hf he τ)
    sign := fun i => key _ (herm_diag e Hf he (Function.update 1 i (-1)) (fun j => by
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj])) }⟩

end SelfDual

end CFSG.RankThree.PartOne.KCSymplectic

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.Assembly.RankThreeEven
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

theorem symplectic_primary_multiplicity_actual_central_cover_local_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) {r : ℕ}
    (hr : 2 ≤ r) (φ : Y →* StatedProj (StatedSp r K)) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (a : StatedProj (StatedSp r K)) (ha : orderOf a = p)
    (x : StatedSp r K) (hxa : proj r K x = a) (hxp : orderOf x = p)
    (h : primaryFactors (spEnd x)) (hh : (h : K[X]) ≠ X - 1) :
    (2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) →
      (if ℓ = 2 then primaryMultiplicity (spEnd x) (h : K[X]) - 1
        else primaryMultiplicity (spEnd x) (h : K[X])) ≤ localRank p G) ∧
    (localRank p G ≤ 3 →
      primaryMultiplicity (spEnd x) (h : K[X]) ≤ (if ℓ = 2 then 4 else 3) ∧
        primaryMultiplicity (spEnd x) (h : K[X]) < p) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h4 | h4
    · have : p = 4 := by omega
      subst this
      exact absurd hp (by norm_num)
    · exact h4
  have hcharK : CharP K ℓ := by
    have := Fintype.ofFinite K
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ
    (by omega) a ha
  have blocks := hblocks x hxa hxp
  have hnt : orderOf (AdjoinRoot.root (h : K[X])) = p := blocks.nontrivial h h.2 hh
  have hp0 : 0 < p := hp.pos
  have key : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) →
      (if ℓ = 2 then primaryMultiplicity (spEnd x) (h : K[X]) - 1
        else primaryMultiplicity (spEnd x) (h : K[X])) ≤ localRank p G := by
    intro hm2
    obtain ⟨T⟩ : Nonempty (KCSymplectic.TorusBlock x h p
        (primaryMultiplicity (spEnd x) (h : K[X]))) := by
      by_cases hself : reciprocalPolynomial (h : K[X]) = h
      · exact KCSymplectic.nonempty_torusBlock_of_selfDual (blocks.selfDual h hh hself) hp0 hnt
      · exact KCSymplectic.nonempty_torusBlock_of_paired (blocks.paired h (Ne.symm hself)) hp0 hnt
    by_cases hℓ2 : ℓ = 2
    · have h2 : (2 : K) = 0 := by
        have := (CharP.cast_eq_zero_iff K ℓ 2).2 (by rw [hℓ2])
        simpa using this
      obtain ⟨u, -, -, A, -, -, -, hrank⟩ := T.witness_even Y φ hφ hker hp hp2 (by omega) h2
        (by omega)
      simpa [hℓ2] using hrank
    · have h2 : (2 : K) ≠ 0 := by
        intro h0
        have := (CharP.cast_eq_zero_iff K ℓ 2).1 (by simpa using h0)
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
      obtain ⟨u, -, -, A, -, -, -, hrank⟩ := T.witness_odd Y φ hφ hker hp hp2 (by omega) h2 hm2
      simpa [hℓ2] using hrank
  refine ⟨key, fun hr3 => ?_⟩
  by_cases hm2 : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X])
  · have h1 := key hm2
    split_ifs at h1 ⊢ <;> omega
  · split_ifs <;> omega

end CFSG.RankThree.PartOne
