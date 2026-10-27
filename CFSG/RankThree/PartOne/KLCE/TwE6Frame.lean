module

public import CFSG.RankThree.PartOne.KE.E6TwFourFamily
public import CFSG.RankThree.PartOne.KE.A1TwE6Ten

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)

open scoped MatrixGroups Polynomial

section Iterate

variable {G : Type*} [Group G]

def normSeq (n₀ : G) (F₀ : G →* G) : ℕ → G
  | 0 => 1
  | k + 1 => n₀ * F₀ (normSeq n₀ F₀ k)

theorem iterate_lang_normSeq {F₀ : G →* G} {g₀ n₀ : G} (hg : F₀ g₀ = g₀ * n₀) (k : ℕ) :
    (⇑F₀)^[k] g₀ = g₀ * normSeq n₀ F₀ k := by
  induction k with
  | zero => simp [normSeq]
  | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, hg, normSeq, mul_assoc]

theorem iterate_conj_normSeq (F₀ : G →* G) (n₀ : G) (k : ℕ) (w : G) :
    (fun v => n₀ * F₀ v * n₀⁻¹)^[k] w =
      normSeq n₀ F₀ k * (⇑F₀)^[k] w * (normSeq n₀ F₀ k)⁻¹ := by
  induction k generalizing w with
  | zero => simp [normSeq]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_mul,
      map_inv, normSeq]
    group

theorem normSeq_conj_fixed {F₀ : G →* G} {n₀ u : G} (hu : n₀ * F₀ u * n₀⁻¹ = u) (k : ℕ) :
    normSeq n₀ F₀ k * (⇑F₀)^[k] u * (normSeq n₀ F₀ k)⁻¹ = u := by
  rw [← iterate_conj_normSeq]
  exact Function.iterate_fixed hu k

end Iterate

section E6

variable {L : Type} [Field L]

theorem twistE6_twistE6 (σ σ' : L →+* L) (g : ModGL Tag.E6 L) :
    twistE6 σ (twistE6 σ' g) = Units.map (entrywiseHom (σ.comp σ')) g := by
  have hσP : Units.map (entrywiseHom σ) (diagE6 L) = diagE6 L :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.E6) σ
  have hcomp : ∀ g : ModGL Tag.E6 L, Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ') g) =
      Units.map (entrywiseHom (σ.comp σ')) g := fun g =>
    units_map_entrywiseHom_comp (t := TwistTag.E6) σ σ' g
  rw [twistE6_apply, twistE6_apply, map_mul, map_mul, map_inv, hσP, hcomp]
  have hP : diagE6 L * diagE6 L = 1 := diagramMap_E6_mul_self
  have hPi : (diagE6 L)⁻¹ = diagE6 L := inv_eq_of_mul_eq_one_right hP
  rw [hPi]
  calc diagE6 L * (diagE6 L * Units.map (entrywiseHom (σ.comp σ')) g * diagE6 L) * diagE6 L
      = (diagE6 L * diagE6 L) * Units.map (entrywiseHom (σ.comp σ')) g * (diagE6 L * diagE6 L) := by
        group
    _ = _ := by rw [hP, one_mul, mul_one]

theorem twistE6_iterate_even (ℓ f₀ : ℕ) [ExpChar L ℓ] (m : ℕ) (h : ModGL Tag.E6 L) :
    (⇑(twistE6 (iterateFrobenius L ℓ f₀)))^[2 * m] h =
      Units.map (entrywiseHom (iterateFrobenius L ℓ (f₀ * (2 * m)))) h := by
  induction m generalizing h with
  | zero =>
    rw [Nat.mul_zero, Nat.mul_zero, iterateFrobenius_zero, Function.iterate_zero, id_eq]
    exact (Units.ext (entrywise_id _)).symm
  | succ m ih =>
    have hF2 : ∀ u, (⇑(twistE6 (iterateFrobenius L ℓ f₀)))^[2] u =
        twistE6 (iterateFrobenius L ℓ f₀) (twistE6 (iterateFrobenius L ℓ f₀) u) := fun u => rfl
    rw [show 2 * (m + 1) = 2 + 2 * m by ring, Function.iterate_add_apply, ih, hF2,
      twistE6_twistE6]
    have hcomp : ∀ (a b : L →+* L) (g : ModGL Tag.E6 L),
        Units.map (entrywiseHom a) (Units.map (entrywiseHom b) g) =
          Units.map (entrywiseHom (a.comp b)) g := fun a b g =>
      units_map_entrywiseHom_comp (t := TwistTag.E6) a b g
    rw [hcomp, show f₀ * (2 + 2 * m) = f₀ + f₀ + f₀ * (2 * m) by ring, iterateFrobenius_add,
      iterateFrobenius_add]

theorem twistE6_iterate_odd (ℓ f₀ : ℕ) [ExpChar L ℓ] (m : ℕ) (h : ModGL Tag.E6 L) :
    (⇑(twistE6 (iterateFrobenius L ℓ f₀)))^[2 * m + 1] h =
      twistE6 (iterateFrobenius L ℓ (f₀ * (2 * m + 1))) h := by
  have hcomp : ∀ (a b : L →+* L) (g : ModGL Tag.E6 L),
      Units.map (entrywiseHom a) (Units.map (entrywiseHom b) g) =
        Units.map (entrywiseHom (a.comp b)) g := fun a b g =>
    units_map_entrywiseHom_comp (t := TwistTag.E6) a b g
  rw [Function.iterate_succ_apply', twistE6_iterate_even, twistE6_apply, twistE6_apply,
    show f₀ * (2 * m + 1) = f₀ + f₀ * (2 * m) by ring, iterateFrobenius_add, hcomp]

end E6


section Action

variable {L : Type} [Field L] {M : Type*} [Group M]

theorem normSeq_action (F₀ : M →* M) (n₀ : M) (ρ : SL(2, L) →* M) (Φ : SL(2, L) →* SL(2, L))
    (hΦ : Function.Surjective Φ) (J : SL(2, L)) (hΦJ : Φ J = J)
    (hF : ∀ B, F₀ (ρ B) = ρ (Φ B)) (hn : ∀ B, n₀ * ρ B * n₀⁻¹ = ρ (J * B * J⁻¹)) (k : ℕ)
    (B : SL(2, L)) :
    normSeq n₀ F₀ k * ρ B * (normSeq n₀ F₀ k)⁻¹ = ρ (J ^ k * B * (J ^ k)⁻¹) := by
  induction k generalizing B with
  | zero => simp [normSeq]
  | succ k ih =>
    obtain ⟨B', rfl⟩ := hΦ B
    have h1 : F₀ (normSeq n₀ F₀ k) * ρ (Φ B') * (F₀ (normSeq n₀ F₀ k))⁻¹ =
        ρ (J ^ k * Φ B' * (J ^ k)⁻¹) := by
      have e1 : ρ (Φ B') = F₀ (ρ B') := (hF B').symm
      have e2 : F₀ (normSeq n₀ F₀ k) * F₀ (ρ B') * (F₀ (normSeq n₀ F₀ k))⁻¹ =
          F₀ (normSeq n₀ F₀ k * ρ B' * (normSeq n₀ F₀ k)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [e1, e2, ih, hF]
      congr 1
      rw [map_mul, map_mul, map_inv, map_pow, hΦJ]
    calc normSeq n₀ F₀ (k + 1) * ρ (Φ B') * (normSeq n₀ F₀ (k + 1))⁻¹
        = n₀ * (F₀ (normSeq n₀ F₀ k) * ρ (Φ B') * (F₀ (normSeq n₀ F₀ k))⁻¹) * n₀⁻¹ := by
          rw [normSeq]
          group
      _ = ρ (J ^ (k + 1) * Φ B' * (J ^ (k + 1))⁻¹) := by
          rw [h1, hn, pow_succ']
          congr 1
          group

end Action


section E6Action

variable {L : Type} [Field L]

theorem e6_twist_rootSL2 (Φ : L →+* L) (B : SL(2, L)) :
    twistHom TwistTag.E6 L Φ (rootSL2 TwistTag.E6.tag L e6HighestRoot B) =
      rootSL2 TwistTag.E6.tag L e6HighestRoot (SpecialLinearGroup.map Φ B) := by
  obtain ⟨-, -, -, -, hrange, hPfix, -⟩ := E6_highest_root_graph_fixed_and_signed_order_five_descent L
  have hρmem : ∀ B : SL(2, L), rootSL2 TwistTag.E6.tag L e6HighestRoot B ∈
      rootSubgroup TwistTag.E6.tag L e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag L (-e6HighestRoot) := fun B => by
    rw [← hrange]
    exact ⟨B, rfl⟩
  rw [twistHom_apply, entrywise_rootSL2_of_field Φ e6HighestRoot B]
  exact hPfix _ (hρmem _)

theorem e6_rootSL2_conj (B : SL(2, L)) :
    e6HRn L * rootSL2 TwistTag.E6.tag L e6HighestRoot B * (e6HRn L)⁻¹ =
      rootSL2 TwistTag.E6.tag L e6HighestRoot (WSL * B * WSL⁻¹) := by
  obtain ⟨-, -, -, -, hrange, hPfix, -, htw, -⟩ :=
    E6_highest_root_graph_fixed_and_signed_order_five_descent L
  have hρmem : rootSL2 TwistTag.E6.tag L e6HighestRoot B ∈
      rootSubgroup TwistTag.E6.tag L e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag L (-e6HighestRoot) := by
    rw [← hrange]
    exact ⟨B, rfl⟩
  have h := htw (RingEquiv.refl L) B
  have hmapid : SpecialLinearGroup.map (RingEquiv.refl L).toRingHom B = B := by
    ext i j
    simp [SpecialLinearGroup.map_apply_coe]
  have e : Units.map (entrywiseHom (RingEquiv.refl L).toRingHom)
      (rootSL2 TwistTag.E6.tag L e6HighestRoot B) = rootSL2 TwistTag.E6.tag L e6HighestRoot B :=
    Units.ext (entrywise_id _)
  rw [e6HRTwist, e, hmapid] at h
  calc e6HRn L * rootSL2 TwistTag.E6.tag L e6HighestRoot B * (e6HRn L)⁻¹
      = e6HRn L * (diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
        (diagramMap TwistTag.E6 L)⁻¹) * (e6HRn L)⁻¹ := by rw [hPfix _ hρmem]
    _ = e6HRn L * diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
        (diagramMap TwistTag.E6 L)⁻¹ * (e6HRn L)⁻¹ := by group
    _ = rootSL2 TwistTag.E6.tag L e6HighestRoot (WSL * B * WSL⁻¹) := h

end E6Action


section Rational


theorem twE6_rational {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ k : ℕ, (∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
        X ≤ adjointGroup TwistTag.E6.tag L →
        (∀ x ∈ X, twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) x = x) →
        ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range.relIndex X ∣
            3 ^ k ∧
          (∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
            IsPGroup p' P →
              P ≤ ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range) ∧
          ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → ⁅P, P⁆ = P →
            P ≤ ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range) ∧
      ∀ p : ℕ, p.Prime → 3 < p →
        p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
          p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
            ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, hRcard, hpp⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R := twistedFixedGroup TwistTag.E6 L Fr with hR
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R).Normal := by
    have e : C'.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
      have h1 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup R), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨k, fun X _ hXC hXF => ?_, fun p hp hp3 => ?_⟩
  · have hXR : X ≤ R := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    refine ⟨relIndex_dvd_of_le_of_index_dvd hXR (hk ▸ dvd_rfl), fun p' hp' hp'3 P hPX hP => ?_,
      fun P hPX hPP => ?_⟩
    · have : Finite P :=
        Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
      exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp' Nat.prime_three (by omega) hk hP
    · have hPR : P ≤ R := hPX.trans hXR
      calc P = ⁅P, P⁆ := hPP.symm
        _ ≤ ⁅R, R⁆ := Subgroup.commutator_mono hPR hPR
        _ = C' := hder
  · have h1 := hpp p hp hp3
    have h2 : Nat.card C' = Nat.card (twistedE6RootGroup K σ) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [h2, hRcard] at h1
    exact h1

end Rational


section SignedBlock


open Polynomial in
@[expose] def twE6SignedBlock (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    A1BlockData .E6 (δ • e6O5W) e6O5Theta where
  c := fun j => if (j : ℕ) = 0 then e6O5Theta else ((δ • e6O5W) ^ ((j : ℕ) - 1)) *ᵥ e6O5Beta
  β := e6O5Beta
  P := X ^ 5 - C δ
  hk := by decide
  hlin := (KE.e6FiveSignedBlock_basis δ hδ).1
  hspan := (KE.e6FiveSignedBlock_basis δ hδ).2
  hc0 := by simp
  hβ := fun j hj => by
    have h : (j : ℕ) ≠ 0 := by omega
    simp [h]
  hθM := ⟨δ, by
    rw [Matrix.smul_mulVec, E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.1]⟩
  hP := Polynomial.monic_X_pow_sub_C δ (by norm_num)
  hPdeg := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    rfl
  hrel := by
    have h5 : e6O5W ^ 5 = 1 := by
      rw [← E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.1]
      exact pow_orderOf_eq_one _
    have hδ5 : δ ^ 5 = δ := by rcases hδ with rfl | rfl <;> norm_num
    have h0 : Polynomial.aeval (δ • e6O5W) (X ^ 5 - C δ : ℤ[X]) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, _root_.smul_pow, h5, hδ5,
        Algebra.algebraMap_eq_smul_one, sub_self]
    rw [h0, Matrix.zero_mulVec]
  hdet := by
    rcases hδ with rfl | rfl <;> simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow]

end SignedBlock

section Frame


theorem twE6_frame {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 10).eval ((ℓ ^ f : ℕ) : ℤ)) :
    7 < p ∧ ¬ p ∣ Nat.card (WeylGroup TwistTag.E6.tag) ∧
    (∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ subtorusA1 (e6HRn L)
        (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) e6O5Theta →
      orderOf (rootDiagUnit TwistTag.E6.tag b) = p →
      rootCharKernel b ⊆ {e6O5Theta, -e6O5Theta}) ∧
    ∀ g₀ : ModGL TwistTag.E6.tag L, g₀ ∈ adjointGroup TwistTag.E6.tag L →
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) g₀ = g₀ * e6HRn L →
      ∀ y : twistedE6RootGroup K σ, orderOf y = p →
        ∃ c : twistedE6RootGroup K σ, c * y * c⁻¹ ∈
          subtorusImage ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) g₀
            (subtorusA1 (e6HRn L) (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f))
              e6O5Theta) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) (Fact.out : ℓ.Prime).one_lt
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  have hpf' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 4 - ((ℓ ^ f : ℕ) : ℤ) ^ 3 + ((ℓ ^ f : ℕ) : ℤ) ^ 2 -
      ((ℓ ^ f : ℕ) : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord10, hΦ5⟩ := CTE6.twE6Ten_data hp hp5 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup TwistTag.E6.tag) :=
    not_dvd_card_weylGroup_E (τ := .E6) hp hp7 (Or.inl rfl)
  obtain ⟨-, -, -, -, hrange, hPfix, ⟨hn, hπ, hv1, hv2⟩, htw, -⟩ :=
    E6_highest_root_graph_fixed_and_signed_order_five_descent L
  set n : ModGL TwistTag.E6.tag L := e6HRn L with hndef
  have hnC : n ∈ adjointGroup TwistTag.E6.tag L := monomialSubgroup_le_adjointGroup' hn
  set v := weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ with hvdef
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ,
      v • x = (((-1 : ℤ)) • e6O5W) *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [hv1 x, smul_neg, e6HRw_smul, neg_one_smul, Matrix.neg_mulVec]
    rfl
  have hθroot : IsRoot TwistTag.E6.tag e6O5Theta :=
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
  have hθ : e6HighestRoot = e6O5Theta := rfl
  have hT := twistedTorus_E6_eq_map_of_weylImage Fr hn v rfl ((-1 : ℤ) • e6O5W) hv
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.E6.tag L) := rootDiagUnit_injective
  set D := twE6SignedBlock (-1) (Or.inr rfl) with hD
  have hq5 : (1 : ℤ) < ((ℓ ^ f : ℕ) : ℤ) ^ 5 := by
    have : (2 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast hq2
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 5 := by norm_num
      _ ≤ ((ℓ ^ f : ℕ) : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
  have hne : D.P.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    show (Polynomial.X ^ 5 - Polynomial.C (-1) : ℤ[X]).eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := D.isCyclic_and_card Fr hFr (Fact.out : ℓ.Prime) hℓq hne
  have hZcyc : IsCyclic (subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom TwistTag.E6.tag L) hinj0).isCyclic.1
      hcycB
  have hZcard : Nat.card (subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta) =
      (ℓ ^ f) ^ 5 + 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0]
    refine hcardB.trans ?_
    show ((Polynomial.X ^ 5 - Polynomial.C (-1) : ℤ[X]).eval ((ℓ ^ f : ℕ) : ℤ)).natAbs = _
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have e : ((ℓ ^ f : ℕ) : ℤ) ^ 5 - -1 = (((ℓ ^ f) ^ 5 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [e, Int.natAbs_natCast]
  have hN : (ℓ ^ f) ^ 5 + 1 ≠ 0 := by omega
  have hord := CTTw.ordProj_twisted_ten hp hq2 hpq hord10
  have hz' : ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
      (((-1 : ℤ) • e6O5W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
        {α | IsRoot Tag.E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := fun z hz0 hzM =>
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.2.2.2.2 p hp hp5
      (-((ℓ ^ f : ℕ) : ZMod p)) hΦ5 z hz0 (transpose_eigen_neg e6O5W _ z hzM)
  have hz : ∀ z : Fin TwistTag.E6.tag.rank → ZMod p, z ≠ 0 →
      (((-1 : ℤ) • e6O5W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
        {α | IsRoot TwistTag.E6.tag α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} :=
    fun z hz0 hzM => hz' z hz0 hzM
  have hkerZ : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta →
      orderOf (rootDiagUnit TwistTag.E6.tag b) = p →
      rootCharKernel b ⊆ {e6O5Theta, -e6O5Theta} := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz hb'.1
      (KE.pow_eq_one_of_orderOf_rootDiagUnit hbp) (KE.ne_one_of_orderOf_rootDiagUnit hp hbp)).le

  refine ⟨hp7, hordW, hkerZ, fun g₀ hg₀C hg₀ y hy => ?_⟩
  obtain ⟨k, hrat, hpp⟩ := twE6_rational hf K hK σ hσ L
  have hordC : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ ((ℓ ^ f) ^ 5 + 1).factorization p := (hpp p hp (by omega)).trans hord
  have hι : Function.Injective
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrat2 : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L →
      (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range.relIndex X ∣
          3 ^ k ∧
        ∀ p' : ℕ, p'.Prime → 3 < p' → ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X →
          IsPGroup p' P →
            P ≤ ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range :=
    fun X _ hXC hXF => by
    have h := hrat X hXC hXF
    exact ⟨h.1, h.2.1⟩
  have hZle : subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta ≤
      twistedTorusOf n (twistHom TwistTag.E6 L Fr) := subtorusA1_le_twistedTorusOf _ _ _
  obtain ⟨-, -, -, -, -, hconj⟩ := sylow_conjugacy_of_subtorus (3 ^ k) _ hι
    (twistHom TwistTag.E6 L Fr) n g₀ hg₀C hg₀ hp (by omega) hN hrat2 _ hZle hZcyc hZcard hordC
  exact hconj y hy

end Frame

end CFSG.RankThree.PartOne.KLCE
