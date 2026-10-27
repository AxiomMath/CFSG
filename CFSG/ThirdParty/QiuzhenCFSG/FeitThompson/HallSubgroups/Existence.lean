module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Bracket
import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Notation.Defs
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Sylow
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Basic
import Mathlib.Tactic.TypeStar

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Complements

namespace CFSG
end CFSG
open CFSG


/-
**Kind**: Theorem
**Note**: Proposition 1.5
**Stmt**:
Let $G$ be a finite solvable group.
Let $A$ be an operator group on $G$ with $gcd(|A|, |G|) = 1$.
Let $\pi$ be a set of primes.
(a) $A$ fixes some Hall $\pi$-subgroup of $G$.
(b) Every $A$-invariant $\pi$-subgroup of $G$ is contained in an $A$-invariant Hall $\pi$-subgroup of $G$.
(c) If $H_1$ and $H_2$ are $A$-invariant Hall $\pi$-subgroups of $G$, then $H_1$ and $H_2$ are conjugate by an element of $C_G(A)$.
(d) If $H$ is any $A$-invariant normal subgroup of $G$, then $C_{G/H}(A)$ is the image of $C_G(A)$ in $G/H$.
(e) If $C_G(A)$ contains a Hall $\pi'$-subgroup of $G$, then $[G, A] \subset \mathcal{O}_{\pi}(G)$.
-/

universe u v

open scoped IsMulCommutative


-- Proposition 1.5(b)
/-- If `K` is an `A`-invariant `π`-subgroup of a finite solvable `G` with coprime operator group
`A`, then `K` is contained in an `A`-invariant Hall `π`-subgroup of `G`. -/
public theorem CFSG.exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ K : Subgroup G, IsPiSubgroup (G := G) π K → IsInvariant A G K →
      ∃ H : Subgroup G, IsHallSubgroup π H ∧ IsInvariant A G H ∧ K ≤ H := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  -- Strong induction on |G|
  let P : ℕ → Prop := fun n =>
    ∀ (G' : Type u) [Group G'] [Finite G'] [MulDistribMulAction A G'],
      Nat.card G' = n → Group.IsSolvable G' → Nat.Coprime (Nat.card A) (Nat.card G') →
        ∀ (π' : Set Nat.Primes) (K' : Subgroup G'),
          IsPiSubgroup π' K' → IsInvariant A G' K' →
            ∃ H' : Subgroup G', IsHallSubgroup π' H' ∧ IsInvariant A G' H' ∧ K' ≤ H'
  have main : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G' _ _ _ hcard hsolv' hcop' π' K' hK'π hK'inv
    classical
    let _ : Group G' := ‹Group G'›
    let _ : Finite G' := ‹Finite G'›
    let _ : MulDistribMulAction A G' := ‹MulDistribMulAction A G'›
    -- If K' is already a Hall π'-subgroup, we are done.
    by_cases hK'hall : IsHallSubgroup π' K'
    · exact ⟨K', hK'hall, hK'inv, le_rfl⟩
    -- Trivial group case.
    by_cases hG' : Nat.card G' = 1
    · have hK'card : Nat.card K' = 1 := by
        have : Nat.card K' ∣ Nat.card G' := Subgroup.card_subgroup_dvd_card K'
        rw [hG'] at this
        exact Nat.eq_one_of_dvd_one this
      refine ⟨⊤, isHallSubgroup_top_of_card_eq_one (G := G') (π := π') hG', ?_, le_top⟩
      refine ⟨?_⟩
      intro a g
      simp only [Subgroup.mem_top]
    have hG'_pos : 0 < Nat.card G' := Nat.card_pos (α := G')
    have hG'_one_lt : 1 < Nat.card G' :=
      lt_of_le_of_ne (Nat.succ_le_iff.mp hG'_pos) (Ne.symm hG')
    -- Choose a minimal `i` with `derivedSeries G' i = ⊥`; then `N := derivedSeries G' (i-1)` is
    -- a nontrivial abelian characteristic subgroup.
    let pds : ℕ → Prop := fun i => derivedSeries G' i = ⊥
    have hpds : ∃ i, pds i := hsolv'.solvable
    let i : ℕ := Nat.find hpds
    have hi_spec : derivedSeries G' i = ⊥ := Nat.find_spec hpds
    have hi_ne_zero : i ≠ 0 := by
      intro hi0
      have h0 : derivedSeries G' 0 = ⊥ := by simpa [i, hi0] using hi_spec
      have htop : (⊤ : Subgroup G') = (⊥ : Subgroup G') := by
        simpa [derivedSeries_zero] using h0
      have hcard' : Nat.card G' = 1 := by
        have : Nat.card (⊤ : Subgroup G') = 1 := by
          exact (Subgroup.card_eq_one (H := (⊤ : Subgroup G'))).2 htop
        simpa using this
      exact (ne_of_gt hG'_one_lt) hcard'
    let N : Subgroup G' := derivedSeries G' (i - 1)
    have hN_ne_bot : N ≠ ⊥ := by
      have hi_lt : i - 1 < i := Nat.sub_one_lt hi_ne_zero
      have : ¬ pds (i - 1) := Nat.find_min hpds hi_lt
      exact fun hN_bot => this (by simp only [pds, N, hN_bot])
    have _ : N.Normal := derivedSeries_normal (G := G') (i - 1)
    have _ : N.Characteristic := derivedSeries_characteristic (G := G') (i - 1)
    have _ : IsInvariant A G' N := isInvariant_of_characteristic (A := A) (G := G') N
    -- `N` is abelian since its commutator is `derivedSeries G' i = ⊥`.
    have hcomm_bot : ⁅N, N⁆ = ⊥ := by
      have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi_ne_zero)
      have hderived : derivedSeries G' i = ⁅N, N⁆ := by
        calc
          derivedSeries G' i = derivedSeries G' (i - 1 + 1) := by simp only [hi1]
          _ = ⁅derivedSeries G' (i - 1), derivedSeries G' (i - 1)⁆ := by simp only [derivedSeries_succ]
          _ = ⁅N, N⁆ := by simp only [N]
      simpa [hderived] using hi_spec
    have _ : IsMulCommutative (↥N) := by
      have hN_le_centralizer : N ≤ Subgroup.centralizer (N : Set G') :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := N) (H₂ := N)).1 hcomm_bot
      exact (Subgroup.le_centralizer_iff_isMulCommutative (K := N)).1 hN_le_centralizer
    -- Pick a prime `p` dividing `|N|`.
    have hN_card_ne_one : Nat.card (↥N) ≠ 1 := by
      have : 1 < Nat.card (↥N) := (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN_ne_bot
      exact ne_of_gt this
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (↥N)) hN_card_ne_one
    have _ : Fact p.Prime := ⟨hp_prime⟩
    -- Let `P₀` be a Sylow `p`-subgroup of `N`, and view it as a normal characteristic subgroup of `N`.
    let P₀ : Sylow p N := Classical.choice (Sylow.nonempty (p := p) (G := N))
    have hP₀_ne_bot : (P₀ : Subgroup N) ≠ ⊥ := Sylow.ne_bot_of_dvd_card (G := N) P₀ (by
      simpa using hp_dvd)
    have hP₀_normal : (P₀ : Subgroup N).Normal := by
      simpa using (Subgroup.normal_of_isMulCommutative (H := (P₀ : Subgroup N)))
    have _ : Unique (Sylow p N) := Sylow.unique_of_normal (G := N) (p := p) P₀ hP₀_normal
    have _ : Subsingleton (Sylow p N) := by infer_instance
    have _ : (P₀ : Subgroup N).Characteristic := Sylow.characteristic_of_subsingleton (G := N) P₀
    -- Map `P₀` into `G'`.
    let Psub : Subgroup G' := (P₀ : Subgroup N).map N.subtype
    have _ : Psub.Normal := by infer_instance
    have _ : IsInvariant A N (P₀ : Subgroup N) :=
      isInvariant_of_characteristic (A := A) (G := N) (P₀ : Subgroup N)
    have _ : IsInvariant A G' Psub := isInvariant_map_subtype (A := A) (G := G') N (P₀ : Subgroup N)
    -- Put the descended action on the quotient `G' ⧸ Psub`.
    let Q := G' ⧸ Psub
    let _ : Group Q := by infer_instance
    let _ : Finite Q := by infer_instance
    let _ : MulDistribMulAction A Q :=
      quotientMulDistribMulAction (A := A) (G := G') Psub (inferInstance : IsInvariant A G' Psub)
    let _ : Group.IsSolvable G' := hsolv'
    have hQ_solv : Group.IsSolvable Q := by infer_instance
    have hQ_coprime : Nat.Coprime (Nat.card A) (Nat.card Q) := by
      have hdvd : Nat.card Q ∣ Nat.card G' := Subgroup.card_quotient_dvd_card (s := Psub)
      exact Nat.Coprime.of_dvd_right hdvd hcop'
    -- `|Q| < |G'|` since `Psub` is nontrivial.
    have hQ_lt : Nat.card Q < n := by
      have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G') (s := Psub))
      have hPsub_ne_bot : Psub ≠ ⊥ := by
        intro hbot
        have hmap_bot : (P₀ : Subgroup N).map N.subtype = ⊥ := by simpa [Psub] using hbot
        have hP0_bot : (P₀ : Subgroup N) = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (H := (P₀ : Subgroup N)) (f := N.subtype)
            N.subtype_injective).1 hmap_bot
        exact hP₀_ne_bot hP0_bot
      have hPsub_one_lt : 1 < Nat.card Psub :=
        (Subgroup.one_lt_card_iff_ne_bot (H := Psub)).2 hPsub_ne_bot
      have hQ_pos : 0 < Nat.card Q := Nat.card_pos (α := Q)
      have hlt : Nat.card Q < Nat.card Q * Nat.card Psub := by
        simpa [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hPsub_one_lt hQ_pos
      have : Nat.card Q * Nat.card Psub = n := by simpa [hcard] using hmul.symm
      simpa [this] using hlt
    -- Consider the image of K' in Q.
    let f : G' →* Q := QuotientGroup.mk' Psub
    have hf : Function.Surjective f := by
      simpa only [f, Q] using QuotientGroup.mk'_surjective Psub
    have hker : f.ker = Psub := QuotientGroup.ker_mk' Psub
    have _ : MulAction.QuotientAction A Psub :=
      quotientAction_of_isInvariant (A := A) (G := G') Psub inferInstance
    let K'_image : Subgroup Q := K'.map f
    have hK'_image_pi : IsPiSubgroup π' K'_image := by
      intro p hp
      apply hK'π p
      have : Nat.card K'_image ∣ Nat.card K' := card_map_dvd_card (f := f) (H := K')
      exact hp.trans this
    have hK'_image_inv : IsInvariant A Q K'_image := by
      refine ⟨?_⟩
      intro a q
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨a • g, (IsInvariant.invariant (A := A) (G := G') (H := K') a g).1 hg, ?_⟩
        exact MulAction.Quotient.smul_mk (H := Psub) a g
      · rintro ⟨g, hg, hq⟩
        refine ⟨a⁻¹ • g, (IsInvariant.invariant (A := A) (G := G') (H := K') a⁻¹ g).1 hg, ?_⟩
        have : f (a⁻¹ • g) = a⁻¹ • f g := by
          exact MulAction.Quotient.smul_mk (H := Psub) (a⁻¹) g
        simp [this, hq]
    have _ : IsInvariant A Q K'_image := hK'_image_inv
    -- Apply the induction hypothesis to the quotient with K'_image.
    obtain ⟨Hbar, hHbar_hall, hHbar_inv, hK'_image_le⟩ :=
      (ih (Nat.card Q) hQ_lt) Q rfl hQ_solv hQ_coprime π' K'_image hK'_image_pi hK'_image_inv
    have _ := hHbar_inv
    -- Pull back `Hbar` to a subgroup of `G'`.
    let K0 : Subgroup G' := Hbar.comap f
    have hK0_hall_index : K0.index = Hbar.index := by
      simpa [K0] using (Subgroup.index_comap_of_surjective (H := Hbar) (f := f) hf)

    have _ : IsInvariant A G' K0 :=
      ⟨by
        intro a g
        simp [K0, Subgroup.mem_comap]
        have hsmul : a • f g = f (a • g) := by
          simpa only [f, Q, QuotientGroup.mk'_apply] using
            MulAction.Quotient.smul_mk (H := Psub) a g
        rw [← hsmul]
        exact hHbar_inv.invariant a (f g)⟩
    have hK'_le_K0 : K' ≤ K0 := by
      intro g hg
      have : f g ∈ K'_image := by
        refine ⟨g, hg, rfl⟩
      exact hK'_image_le this
    -- Case split on whether `p` lies in `π'`.
    let p' : Nat.Primes := ⟨p, hp_prime⟩
    by_cases hp_mem : p' ∈ π'
    ·
      -- If `p ∈ π'`, the preimage `K0` is already a Hall `π'`-subgroup.
      refine ⟨K0, ?_, inferInstance, hK'_le_K0⟩
      classical
      let _ : Fintype G' := Fintype.ofFinite G'
      have _ : Finite K0 := by infer_instance
      have _ : Subgroup.FiniteIndex K0 := by infer_instance
      refine isHallSubgroup_of (G := G') (π := π') (H := K0) (hcard := ?_) (hindex := ?_)
      ·
        intro q hq_dvd
        let Pk : Subgroup K0 := Psub.subgroupOf K0
        have hmulK : Nat.card K0 = Nat.card (K0 ⧸ Pk) * Nat.card Pk := by
          simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := K0) (s := Pk))
        have hq_dvd_prod : q.val ∣ Nat.card (K0 ⧸ Pk) * Nat.card Pk := by
          rw [← hmulK]; exact hq_dvd
        have hq_dvd_left_or_right := q.property.dvd_or_dvd hq_dvd_prod
        rcases hq_dvd_left_or_right with hq_dvd_quot | hq_dvd_Pk
        ·
          have hcard_congr : Nat.card (K0 ⧸ Pk) = Nat.card Hbar := by
            simpa [K0, Pk, f, hker] using card_quotient_subgroupOf_comap_eq (f := f) (hf := hf) (H := Hbar)
          have hq_dvd_Hbar : q.val ∣ Nat.card Hbar := by rw [← hcard_congr]; exact hq_dvd_quot
          exact IsHallSubgroup.p_in_pi_of_p_dvd_card (π := π') (H := Hbar) q hq_dvd_Hbar
        ·
          have hP0_p : IsPGroup p (P₀ : Subgroup N) := P₀.isPGroup'
          have hPsub_p : IsPGroup p Psub := by
            simpa [Psub] using (IsPGroup.map (p := p) (H := (P₀ : Subgroup N)) hP0_p N.subtype)
          have hPk_p : IsPGroup p Pk := by
            change IsPGroup p (Psub.comap K0.subtype)
            exact IsPGroup.comap_subtype (p := p) (H := Psub) hPsub_p (K := K0)
          rcases hPk_p.exists_card_eq with ⟨k, hk⟩
          have hq_dvd_pow : q.val ∣ p ^ k := by
            rw [hk] at hq_dvd_Pk
            exact hq_dvd_Pk
          have hq_eq : q.val = p := Nat.prime_eq_prime_of_dvd_pow q.property hp_prime hq_dvd_pow
          have : q = p' := by apply Subtype.ext; simpa [p'] using hq_eq
          simpa [this] using hp_mem
      ·
        intro q hq_mem hq_dvd_idx
        have : q ∉ π' := hHbar_hall.p_in_pi_of_p_dvd_index q (by simpa [hK0_hall_index] using hq_dvd_idx)
        exact this hq_mem
    ·
      -- If `p ∉ π'`, apply the invariant complement lemma inside `K0` to remove the `p`-part.
      classical
      let Pk : Subgroup K0 := Psub.subgroupOf K0
      have _ : Pk.Normal := by simpa [Pk] using (Subgroup.Normal.subgroupOf (H := Psub) (K := K0) inferInstance)
      have _ : IsMulCommutative (↥Pk) := by infer_instance
      have _ : IsInvariant A K0 Pk := by
        refine ⟨?_⟩
        intro a x
        change (x.1 ∈ Psub) ↔ (a • x.1 ∈ Psub)
        exact IsInvariant.invariant (A := A) (G := G') (H := Psub) a x.1
      have hPk_coprime_index : Nat.Coprime (Nat.card Pk) Pk.index := by
        classical
        have hcard_congr : Nat.card (K0 ⧸ Pk) = Nat.card Hbar := by
          simpa [K0, Pk, f, hker] using card_quotient_subgroupOf_comap_eq (f := f) (hf := hf) (H := Hbar)
        have hP0_p : IsPGroup p (P₀ : Subgroup N) := P₀.isPGroup'
        have hPsub_p : IsPGroup p Psub := by
          simpa [Psub] using (IsPGroup.map (p := p) (H := (P₀ : Subgroup N)) hP0_p N.subtype)
        have hPk_p : IsPGroup p Pk := by
          change IsPGroup p (Psub.comap K0.subtype)
          exact IsPGroup.comap_subtype (p := p) (H := Psub) hPsub_p (K := K0)
        refine Nat.coprime_of_dvd ?_
        intro q hqprime hq_dvd_card hq_dvd_idx
        rcases hPk_p.exists_card_eq with ⟨k, hk⟩
        have hq_dvd_pow : q ∣ p ^ k := by simpa [hk] using hq_dvd_card
        have hq_eq : q = p := Nat.prime_eq_prime_of_dvd_pow hqprime hp_prime hq_dvd_pow
        have hp_dvd_idx : p ∣ Pk.index := by simpa [hq_eq] using hq_dvd_idx
        have hp_dvd_quot : p ∣ Nat.card (K0 ⧸ Pk) := by
          have : Pk.index = Nat.card (K0 ⧸ Pk) := by simp [Subgroup.index_eq_card]
          simpa [this] using hp_dvd_idx
        have hp_dvd_Hbar : p ∣ Nat.card Hbar := by simpa [hcard_congr] using hp_dvd_quot
        have : (⟨p, hp_prime⟩ : Nat.Primes) ∈ π' :=
          hHbar_hall.p_in_pi_of_p_dvd_card ⟨p, hp_prime⟩ hp_dvd_Hbar
        exact hp_mem this
      have hA_coprime_Pk : Nat.Coprime (Nat.card A) (Nat.card Pk) := by
        have hdvd : Nat.card Pk ∣ Nat.card G' := by
          have hdvd' : Nat.card (Pk.map K0.subtype) ∣ Nat.card G' := by
            simpa using (Subgroup.card_subgroup_dvd_card (s := (Pk.map K0.subtype)) (α := G'))
          have hcard_map : Nat.card (Pk.map K0.subtype) = Nat.card Pk := by
            simpa using (Subgroup.card_map_of_injective (G := K0) (H := G') (K := Pk) (f := K0.subtype)
              K0.subtype_injective)
          exact hcard_map.symm ▸ hdvd'
        exact Nat.Coprime.of_dvd_right hdvd hcop'
      let Kk : Subgroup K0 := K'.subgroupOf K0
      have hcard_Kk : Nat.card Kk = Nat.card K' := by
        simpa [Kk] using
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := K') (K := K0) hK'_le_K0).toEquiv
      have hP0_p : IsPGroup p (P₀ : Subgroup N) := P₀.isPGroup'
      have hPsub_p : IsPGroup p Psub := by
        simpa [Psub] using (IsPGroup.map (p := p) (H := (P₀ : Subgroup N)) hP0_p N.subtype)
      have hPk_p : IsPGroup p Pk := by
        change IsPGroup p (Psub.comap K0.subtype)
        exact IsPGroup.comap_subtype (p := p) (H := Psub) hPsub_p (K := K0)
      have hKk_coprime_Pk : Nat.Coprime (Nat.card Kk) (Nat.card Pk) := by
        refine Nat.coprime_of_dvd ?_
        intro q hqprime hq_dvd_Kk hq_dvd_Pk
        have hq_dvd_K' : q ∣ Nat.card K' := by
          simpa [hcard_Kk] using hq_dvd_Kk
        have hq_mem : (⟨q, hqprime⟩ : Nat.Primes) ∈ π' :=
          hK'π ⟨q, hqprime⟩ hq_dvd_K'
        rcases hPk_p.exists_card_eq with ⟨k, hk⟩
        have hq_dvd_pow : q ∣ p ^ k := by
          simpa [hk] using hq_dvd_Pk
        have hq_eq : q = p := Nat.prime_eq_prime_of_dvd_pow hqprime hp_prime hq_dvd_pow
        apply hp_mem
        have : (⟨q, hqprime⟩ : Nat.Primes) = p' := by
          apply Subtype.ext
          simpa [p'] using hq_eq
        rw [this] at hq_mem
        exact hq_mem
      have _ : IsInvariant A K0 Kk := by
        refine ⟨?_⟩
        intro a x
        change (x.1 ∈ K') ↔ (a • x.1 ∈ K')
        exact IsInvariant.invariant (A := A) (G := G') (H := K') a x.1
      let B := Kk ⋊[MulDistribMulAction.toMulAut A Kk] A
      have hB_card : Nat.card B = Nat.card Kk * Nat.card A := by
        simp [B]
      have hB_coprime_Pk : Nat.Coprime (Nat.card B) (Nat.card Pk) := by
        rw [hB_card]
        exact Nat.Coprime.mul_left hKk_coprime_Pk hA_coprime_Pk
      let _ : Fintype Kk := Fintype.ofFinite Kk
      let _ : Fintype B := Fintype.ofEquiv (Kk × A)
        (SemidirectProduct.equivProd (N := Kk) (G := A) (φ := MulDistribMulAction.toMulAut A Kk)).symm
      have _ : Finite B := by infer_instance
      let conjHomKk : Kk →* MulAut K0 :=
        (MulAut.conj (G := K0)).comp Kk.subtype
      have hsemi :
          ∀ a : A,
            conjHomKk.comp ((MulDistribMulAction.toMulAut A Kk) a).toMonoidHom =
              (MulAut.conj ((MulDistribMulAction.toMulAut A K0) a)).toMonoidHom.comp conjHomKk := by
        intro a
        ext k x
        have hk : ((a • k : Kk) : K0) = a • (k : K0) := rfl
        simp [conjHomKk, MulAut.conj_apply, hk, smul_mul', smul_inv_smul, mul_assoc]
      let semiToMulAut : B →* MulAut K0 :=
        SemidirectProduct.lift (fn := conjHomKk)
          (fg := MulDistribMulAction.toMulAut A K0) hsemi
      let _ : MulDistribMulAction B K0 :=
        MulDistribMulAction.compHom K0 semiToMulAut
      have hB_inv_Pk : IsInvariant B K0 Pk := by
        refine ⟨?_⟩
        intro b x
        have h_inr (a : A) (y : K0) :
            y ∈ Pk ↔ ((SemidirectProduct.inr a : B) • y) ∈ Pk := by
          have hsmul :
              ((SemidirectProduct.inr a : B) • y) = a • y := by
            change ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
              (SemidirectProduct.inr a)) y = a • y
            exact semidirect_lift_inr_apply (conjHomKk := conjHomKk) (hsemi := hsemi) (a := a) (x := y)
          rw [hsmul]
          simpa using (IsInvariant.invariant (A := A) (G := K0) (H := Pk) a y)
        have h_inl (n : Kk) (y : K0) :
            y ∈ Pk ↔ ((SemidirectProduct.inl n : B) • y) ∈ Pk := by
          have hsmul :
              ((SemidirectProduct.inl n : B) • y) =
                (n : K0) * y * (n : K0)⁻¹ := by
            change ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
              (SemidirectProduct.inl n)) y = _
            calc
              ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
                (SemidirectProduct.inl n)) y
                  = (conjHomKk n) y := by
                      exact semidirect_lift_inl_apply (conjHomKk := conjHomKk) (hsemi := hsemi)
                        (n := n) (x := y)
              _ = (n : K0) * y * (n : K0)⁻¹ := by
                    simp [conjHomKk, MulAut.conj_apply]
          rw [hsmul]
          constructor
          · intro hy
            exact (inferInstance : Pk.Normal).conj_mem y hy (n : K0)
          · intro hy
            have hy' := (inferInstance : Pk.Normal).conj_mem ((n : K0) * y * (n : K0)⁻¹) hy
              ((n : K0)⁻¹)
            simpa [mul_assoc] using hy'
        have hb : b = SemidirectProduct.inl b.left * SemidirectProduct.inr b.right :=
          (SemidirectProduct.inl_left_mul_inr_right b).symm
        rw [hb, mul_smul]
        constructor
        · intro hx
          exact (h_inl b.left ((SemidirectProduct.inr b.right : B) • x)).1
            ((h_inr b.right x).1 hx)
        · intro hx
          exact (h_inr b.right x).2
            ((h_inl b.left ((SemidirectProduct.inr b.right : B) • x)).2 hx)
      let _ : IsInvariant B K0 Pk := hB_inv_Pk
      obtain ⟨L, hcomp, hLinvar⟩ :=
        Subgroup.quotientDiff.exists_invariant_complement' (G := K0) (A := B) (H := Pk)
          (hH := inferInstance) hPk_coprime_index hB_coprime_Pk
      have hsmul_inr (a : A) (x : K0) :
          ((SemidirectProduct.inr a : B) • x) = a • x := by
        change ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
          (SemidirectProduct.inr a)) x = a • x
        exact semidirect_lift_inr_apply (conjHomKk := conjHomKk) (hsemi := hsemi) (a := a) (x := x)
      have hsmul_inl (n : Kk) (x : K0) :
          ((SemidirectProduct.inl n : B) • x) = (n : K0) * x * (n : K0)⁻¹ := by
        change ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
          (SemidirectProduct.inl n)) x = _
        calc
          ((SemidirectProduct.lift (fn := conjHomKk) (fg := MulDistribMulAction.toMulAut A K0) hsemi)
            (SemidirectProduct.inl n)) x
              = (conjHomKk n) x := by
                  exact semidirect_lift_inl_apply (conjHomKk := conjHomKk) (hsemi := hsemi)
                    (n := n) (x := x)
          _ = (n : K0) * x * (n : K0)⁻¹ := by
                simp [conjHomKk, MulAut.conj_apply]
      have hLinvarA : IsInvariant A K0 L := by
        refine ⟨?_⟩
        intro a x
        rw [← hsmul_inr (a := a) (x := x)]
        exact IsInvariant.invariant (A := B) (G := K0) (H := L) (SemidirectProduct.inr a) x
      have hKk_le_normalizerL : Kk ≤ Subgroup.normalizer L := by
        intro n hn
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [← hsmul_inl (n := ⟨n, hn⟩) (x := y)]
        exact IsInvariant.invariant (A := B) (G := K0) (H := L) (SemidirectProduct.inl ⟨n, hn⟩) y
      have hKk_le_L : Kk ≤ L := by
        let Ks : Subgroup ↥(Kk ⊔ L) := Kk.subgroupOf (Kk ⊔ L)
        let Ls : Subgroup ↥(Kk ⊔ L) := L.subgroupOf (Kk ⊔ L)
        have hsup_top : (Ks ⊔ Ls : Subgroup ↥(Kk ⊔ L)) = ⊤ := by
          have hs : (Kk ⊔ L).subgroupOf (Kk ⊔ L) = Kk.subgroupOf (Kk ⊔ L) ⊔ L.subgroupOf (Kk ⊔ L) :=
            Subgroup.subgroupOf_sup (A := Kk) (A' := L) (B := Kk ⊔ L) le_sup_left le_sup_right
          simpa [Ks, Ls] using hs.symm
        have hsup_le_normalizer : Kk ⊔ L ≤ Subgroup.normalizer L := by
          exact sup_le hKk_le_normalizerL Subgroup.le_normalizer
        have hLs_normal : Ls.Normal := by
          exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := L) (K := Kk ⊔ L) le_sup_right).2
            hsup_le_normalizer
        let _ : Ls.Normal := hLs_normal
        have hIso : Ks ⧸ Ls.subgroupOf Ks ≃* (Ks ⊔ Ls : Subgroup ↥(Kk ⊔ L)) ⧸ Ls.subgroupOf (Ks ⊔ Ls) :=
          QuotientGroup.quotientInfEquivProdNormalQuotient Ks Ls
        have hidx_dvd_cardKk : (L.subgroupOf (Kk ⊔ L)).index ∣ Nat.card Kk := by
          have hdiv1 : Nat.card ((Ks ⊔ Ls : Subgroup ↥(Kk ⊔ L)) ⧸ Ls.subgroupOf (Ks ⊔ Ls)) ∣ Nat.card Kk := by
            have hcard1 : Nat.card ((Ks ⊔ Ls : Subgroup ↥(Kk ⊔ L)) ⧸ Ls.subgroupOf (Ks ⊔ Ls)) =
                Nat.card (Ks ⧸ Ls.subgroupOf Ks) := Nat.card_congr hIso.toEquiv |>.symm
            have hdiv : Nat.card (Ks ⧸ Ls.subgroupOf Ks) ∣ Nat.card Ks := by
              have : Nat.card (Ks ⧸ Ls.subgroupOf Ks) = (Ls.subgroupOf Ks).index := by
                simp [Subgroup.index_eq_card]
              rw [this]
              exact Subgroup.index_dvd_card (H := (Ls.subgroupOf Ks))
            have hKs_card : Nat.card Ks = Nat.card Kk := by
              simpa [Ks] using
                Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Kk) (K := Kk ⊔ L) le_sup_left).toEquiv
            rw [hcard1]
            exact hKs_card ▸ hdiv
          have hdiv2 : (Ls.subgroupOf (Ks ⊔ Ls)).index ∣ Nat.card Kk := by
            have hcard : Nat.card ((Ks ⊔ Ls : Subgroup ↥(Kk ⊔ L)) ⧸ Ls.subgroupOf (Ks ⊔ Ls)) =
                (Ls.subgroupOf (Ks ⊔ Ls)).index := by
              simp [Subgroup.index_eq_card]
            exact hcard.symm ▸ hdiv1
          have hidx_eq : (Ls.subgroupOf (Ks ⊔ Ls)).index = Ls.index := by
            rw [hsup_top] at *
            have hmap : (Ls.subgroupOf (⊤ : Subgroup ↥(Kk ⊔ L))).map (Subgroup.subtype (⊤ : Subgroup ↥(Kk ⊔ L))) = Ls := by simp
            have hidx := Subgroup.index_map_subtype (K := Ls.subgroupOf (⊤ : Subgroup ↥(Kk ⊔ L)))
            rw [hmap, Subgroup.index_top, Nat.mul_one] at hidx
            exact hidx.symm
          exact hidx_eq.symm ▸ hdiv2
        have hidx_dvd_cardPk : (L.subgroupOf (Kk ⊔ L)).index ∣ Nat.card Pk := by
          have hidx_dvd_Lidx : (L.subgroupOf (Kk ⊔ L)).index ∣ L.index := by
            let Lsub : Subgroup ↥(Kk ⊔ L) := L.subgroupOf (Kk ⊔ L)
            have hmap : Lsub.map (Subgroup.subtype (Kk ⊔ L)) = L := by simp [Lsub]
            have hidx := Subgroup.index_map_subtype (K := Lsub)
            rw [hmap] at hidx
            exact ⟨(Kk ⊔ L).index, hidx⟩
          exact (hcomp.index_eq_card).symm ▸ hidx_dvd_Lidx
        have hidx_eq_one : (L.subgroupOf (Kk ⊔ L)).index = 1 :=
          Nat.eq_one_of_dvd_coprimes hKk_coprime_Pk hidx_dvd_cardKk hidx_dvd_cardPk
        have hLsub_top : L.subgroupOf (Kk ⊔ L) = ⊤ := (Subgroup.index_eq_one).1 hidx_eq_one
        have hsup_le_L : Kk ⊔ L ≤ L := (Subgroup.subgroupOf_eq_top).1 hLsub_top
        exact le_trans le_sup_left hsup_le_L
      have _ : IsInvariant A K0 L := hLinvarA
      -- Map the complement back into `G'`.
      let L' : Subgroup G' := L.map K0.subtype
      have _ : IsInvariant A G' L' := isInvariant_map_subtype (A := A) (G := G') K0 L
      -- Show that K' ≤ L'
      have hK'_le_L' : K' ≤ L' := by
        intro g hg
        have hgK0 : g ∈ K0 := hK'_le_K0 hg
        have hgKk : (⟨g, hgK0⟩ : K0) ∈ Kk := by
          change g ∈ K'
          exact hg
        have hgL : (⟨g, hgK0⟩ : K0) ∈ L := hKk_le_L hgKk
        exact ⟨⟨g, hgK0⟩, hgL, rfl⟩
      refine ⟨L', ?_, inferInstance, hK'_le_L'⟩
      have _ : Finite L' := by infer_instance
      have _ : Subgroup.FiniteIndex L' := by infer_instance
      refine isHallSubgroup_of (G := G') (π := π') (H := L') (hcard := ?_) (hindex := ?_)
      ·
        intro q hq_dvd
        have hcard_map : Nat.card L' = Nat.card L := by
          simpa [L'] using (Subgroup.card_map_of_injective (G := K0) (H := G') (K := L) (f := K0.subtype)
              K0.subtype_injective)
        have hq_dvd_L : q.val ∣ Nat.card L := by simpa [hcard_map] using hq_dvd
        have hL_card : Nat.card L = Pk.index := (hcomp.symm.index_eq_card).symm
        have hq_dvd_index : q.val ∣ Pk.index := by simpa [hL_card] using hq_dvd_L
        have hcard_congr : Nat.card (K0 ⧸ Pk) = Nat.card Hbar := by
          simpa [K0, Pk, f, hker] using card_quotient_subgroupOf_comap_eq (f := f) (hf := hf) (H := Hbar)
        have hq_dvd_Hbar : q.val ∣ Nat.card Hbar := by
          have : Pk.index = Nat.card (K0 ⧸ Pk) := by simp [Subgroup.index_eq_card]
          simpa [this, hcard_congr] using hq_dvd_index
        exact IsHallSubgroup.p_in_pi_of_p_dvd_card (π := π') (H := Hbar) q hq_dvd_Hbar
      ·
        intro q hq_mem hq_dvd_idx
        have hidx : L'.index = L.index * K0.index := by simp [L', Subgroup.index_map_subtype]
        have hq_dvd_prod : q.val ∣ L.index * K0.index := by simpa [hidx] using hq_dvd_idx
        have hq_dvd_left_or_right := q.property.dvd_or_dvd hq_dvd_prod
        cases hq_dvd_left_or_right with
        | inl hq_dvd_Lidx =>
            have hL_index : L.index = Nat.card Pk := hcomp.index_eq_card
            have hpq : q.val ≠ p := by
              intro hqp
              apply hp_mem
              have : q = p' := by apply Subtype.ext; simpa [p'] using hqp
              simpa [this] using hq_mem
            have hP0_p : IsPGroup p (P₀ : Subgroup N) := P₀.isPGroup'
            have hPsub_p : IsPGroup p Psub := by
              simpa [Psub] using (IsPGroup.map (p := p) (H := (P₀ : Subgroup N)) hP0_p N.subtype)
            have hPk_p : IsPGroup p Pk := by
              change IsPGroup p (Psub.comap K0.subtype)
              exact IsPGroup.comap_subtype (p := p) (H := Psub) hPsub_p (K := K0)
            rcases hPk_p.exists_card_eq with ⟨k, hk⟩
            have hq_dvd_pow : q.val ∣ p ^ k := by simpa [hL_index, hk] using hq_dvd_Lidx
            have hq_eq : q.val = p := Nat.prime_eq_prime_of_dvd_pow q.property hp_prime hq_dvd_pow
            exact hpq hq_eq
        | inr hq_dvd_K0idx =>
            have : q ∉ π' := hHbar_hall.p_in_pi_of_p_dvd_index q (by simpa [hK0_hall_index] using hq_dvd_K0idx)
            exact this hq_mem
  exact @main (Nat.card G) G (by infer_instance) (by infer_instance) (by infer_instance) rfl hsolv hcoprime π

-- Proposition 1.5(a)
public theorem CFSG.exists_isHallSubgroup_isInvariant
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧ IsInvariant A G H := by
  have hbot_pi : IsPiSubgroup (G := G) π (⊥ : Subgroup G) := by
    intro p hp
    exfalso
    have : p.val ∣ (1 : ℕ) := by
      simpa using hp
    exact p.property.not_dvd_one this
  have hbot_inv : IsInvariant A G (⊥ : Subgroup G) :=
    isInvariant_of_characteristic (A := A) (G := G) (⊥ : Subgroup G)
  obtain ⟨H, hHall, hInv, _hbot_le⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := G) (A := A) hsolv hcoprime π (⊥ : Subgroup G) hbot_pi hbot_inv
  exact ⟨H, hHall, hInv⟩
