module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_7

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.3.3, IV.3.4, and IV.3.7

This module contains the Grun focal-control interfaces used before Huppert
IV.5.4.  The three theorem-number files in this section re-export this core in
book order.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise
open scoped IsMulCommutative
set_option maxHeartbeats 0

universe u v


/-- Grün IV.3.7 residual-extension consequence.

The source theorem gives the quotient comparison
`Q / Q'(q) ~= N_Q(Z(S)) / N_Q(Z(S))'(q)`.  In the later minimal-counterexample
use this comparison is used to show that `Q'(q)` is a proper subgroup; the
minimality hypothesis then supplies a normal `q`-complement in `Q'(q)`.  Once
that residual complement is available, IV.3.2 gives that `Q / Q'(q)` is a
`q`-group, and the standard extension lemma lifts the complement to `Q`.
This replaces the deleted non-source focal-bottom claim. -/
private theorem hkt_grun_iv37_abelian_residual_extension_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcomp_residual : HasNormalPComplement q (hktAbelianPResidual q Q)) :
    HasNormalPComplement q Q := by
  classical
  let A : Subgroup Q := hktAbelianPResidual q Q
  haveI : A.Normal := by
    simpa [A] using hktAbelianPResidual_normal (Q := Q) (q := q)
  let ZN : Subgroup Q :=
    Subgroup.normalizer
      ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
  have _h37 :
      letI : (hktAbelianPResidual q Q).Normal :=
        hktAbelianPResidual_normal (Q := Q) (q := q)
      letI : (hktAbelianPResidual q ZN).Normal :=
        hktAbelianPResidual_normal (Q := ZN) (q := q)
      Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
        (ZN ⧸ hktAbelianPResidual q ZN)) :=
    huppert_IV_3_7_second_grun (Q := Q) (q := q) S hpnormal
  have hquot : IsPGroup q (Q ⧸ A) := by
    simpa [A] using hktAbelianPResidual_quotient_isPGroup (Q := Q) (q := q)
  exact hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient
    (G := Q) (p := q) A hquot (by simpa [A] using hcomp_residual)

/-- Grün IV.3.4/IV.3.7 normal-complement consequence in the form used after the
book's residual-properness step: under `q`-normality, a normal `q`-complement in
`N_Q(Z(S))`, and the minimal-counterexample complement for `Q'(q)`, `Q` has a
normal `q`-complement. -/
private theorem hkt_grun_iv34_hasNormalPComplement_core_source
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcomp_ZN :
      HasNormalPComplement q
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)))
    (hcomp_residual : HasNormalPComplement q (hktAbelianPResidual q Q)) :
    HasNormalPComplement q Q := by
  classical
  by_cases hQp : IsPGroup q Q
  · exact hkt_hasNormalPComplement_of_isPGroup (Q := Q) (p := q) hQp
  · let ZN : Subgroup Q :=
      Subgroup.normalizer
        ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
    by_cases hZNtop : ZN = ⊤
    · exact hkt_hasNormalPComplement_of_subgroup_eq_top
        (Q := Q) (q := q) ZN hZNtop (by simpa [ZN] using hcomp_ZN)
    · exact hkt_grun_iv37_abelian_residual_extension_source
        (Q := Q) (q := q) S hpnormal hcomp_residual
/-- If a finite group has a normal `q`-complement and `q` divides its order,
then Huppert's abelian `q`-residual is proper.  This is the formal version of
the book's assertion that the abelian residual quotient is nontrivial in the
`q`-nilpotent proper-normalizer branch. -/
public theorem hktAbelianPResidual_ne_top_of_hasNormalPComplement_of_dvd_card
    {G : Type u} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (hcomp : HasNormalPComplement q G) (hq_dvd : q ∣ Nat.card G) :
    hktAbelianPResidual q G ≠ (⊤ : Subgroup G) := by
  classical
  rcases hcomp with ⟨N, hNnorm, hNcop, hquotp⟩
  letI : N.Normal := hNnorm
  have hq_dvd_quot : q ∣ Nat.card (G ⧸ N) := by
    have hcard : Nat.card G = Nat.card (G ⧸ N) * Nat.card N := by
      simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := N))
    have hq_dvd_mul : q ∣ Nat.card (G ⧸ N) * Nat.card N := by
      simpa [hcard] using hq_dvd
    rcases (Fact.out : Nat.Prime q).dvd_mul.mp hq_dvd_mul with hquot | hN
    · exact hquot
    · exact False.elim (((Fact.out : Nat.Prime q).coprime_iff_not_dvd.mp hNcop) hN)
  have hquot_nontriv : Nontrivial (G ⧸ N) := by
    by_contra hnt
    have hnot_lt : ¬ 1 < Nat.card (G ⧸ N) := by
      intro hlt
      exact hnt (Finite.one_lt_card_iff_nontrivial.mp hlt)
    have hcard_le : Nat.card (G ⧸ N) ≤ 1 := Nat.le_of_not_gt hnot_lt
    have hcard_pos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    have hcard_one : Nat.card (G ⧸ N) = 1 := by omega
    exact (Fact.out : Nat.Prime q).not_dvd_one (by simpa [hcard_one] using hq_dvd_quot)
  letI : Nontrivial (G ⧸ N) := hquot_nontriv
  have hcomm_ne_top : commutator (G ⧸ N) ≠ (⊤ : Subgroup (G ⧸ N)) := by
    haveI : Group.IsNilpotent (G ⧸ N) := IsPGroup.isNilpotent (p := q) hquotp
    haveI : IsSolvable (G ⧸ N) := IsNilpotent.to_isSolvable
    exact (IsSolvable.commutator_lt_top_of_nontrivial (G := G ⧸ N)).ne
  let φ : G →* ((G ⧸ N) ⧸ commutator (G ⧸ N)) :=
    (QuotientGroup.mk' (commutator (G ⧸ N))).comp (QuotientGroup.mk' N)
  have hφ_surj : Function.Surjective φ := by
    intro y
    rcases QuotientGroup.mk'_surjective (commutator (G ⧸ N)) y with ⟨z, rfl⟩
    rcases QuotientGroup.mk'_surjective N z with ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hφker_ne_top : φ.ker ≠ (⊤ : Subgroup G) := by
    intro htop
    have hsubsingleton_target : Subsingleton ((G ⧸ N) ⧸ commutator (G ⧸ N)) := by
      refine ⟨?_⟩
      intro a b
      rcases hφ_surj a with ⟨x, rfl⟩
      rcases hφ_surj b with ⟨y, rfl⟩
      have hx : x ∈ φ.ker := by simp [htop]
      have hy : y ∈ φ.ker := by simp [htop]
      rw [MonoidHom.mem_ker] at hx hy
      rw [hx, hy]
    have hcomm_top : commutator (G ⧸ N) = (⊤ : Subgroup (G ⧸ N)) := by
      apply eq_top_iff.mpr
      intro x hx
      have hxq : QuotientGroup.mk' (commutator (G ⧸ N)) x = 1 := by
        have hsub : Subsingleton ((G ⧸ N) ⧸ commutator (G ⧸ N)) := hsubsingleton_target
        exact Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff (N := commutator (G ⧸ N)) (x := x)).1 hxq
    exact hcomm_ne_top hcomm_top
  have hab_le_ker : hktAbelianPResidual q G ≤ φ.ker := by
    have hcomm_le : commutator G ≤ φ.ker := by
      haveI : IsMulCommutative ((G ⧸ N) ⧸ commutator (G ⧸ N)) :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le
          (N := commutator (G ⧸ N))).mpr le_rfl
      exact Abelianization.commutator_subset_ker (f := φ)
    have hquot_ker_p : IsPGroup q (G ⧸ φ.ker) := by
      let e : G ⧸ φ.ker ≃* φ.range := QuotientGroup.quotientKerEquivRange φ
      have hrange_p : IsPGroup q φ.range := by
        have hab_p : IsPGroup q ((G ⧸ N) ⧸ commutator (G ⧸ N)) :=
          hquotp.to_quotient (commutator (G ⧸ N))
        exact hab_p.to_subgroup φ.range
      exact hrange_p.of_equiv e.symm
    exact hktAbelianPResidual_le (Q := G) (q := q) (N := φ.ker)
      hcomm_le (hktPResidual_le (Q := G) (q := q) φ.ker inferInstance hquot_ker_p)
  intro htop
  exact hφker_ne_top (top_unique (by simpa [htop] using hab_le_ker))

/-- In a minimal counterexample, the proper abelian residual has the normal
`q`-complement supplied by the induction/minimality hypothesis; if its order is
not divisible by `q`, it is already a normal `q`-complement. -/
public theorem hktAbelianPResidual_hasNormalPComplement_of_minimal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (hres_ne_top : hktAbelianPResidual q Q ≠ (⊤ : Subgroup Q)) :
    HasNormalPComplement q (hktAbelianPResidual q Q) := by
  classical
  let A : Subgroup Q := hktAbelianPResidual q Q
  by_cases hqA : q ∣ Nat.card A
  · have hA_ne_bot : A ≠ ⊥ := by
      intro hbot
      have hcard_one : Nat.card A = 1 := by
        rw [hbot]
        exact Subgroup.card_bot
      exact (Fact.out : Nat.Prime q).not_dvd_one (by simpa [hcard_one] using hqA)
    exact hproper A hA_ne_bot (by simpa [A] using hres_ne_top) hqA
  · exact hkt_hasNormalPComplement_of_not_dvd_card (Q := A) (p := q) hqA
/-- If the center normalizer has a normal `q`-complement and its order is
divisible by `q`, then Grün IV.3.7 transfers the nontrivial abelian residual
quotient back to the ambient group.  This is the formal form of the
proper-center-normalizer sentence used in IV.5.4(a). -/
public theorem hktAbelianPResidual_ne_top_of_center_normalizer_hasNormalPComplement
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcomp_ZN :
      HasNormalPComplement q
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)))
    (hq_dvd_ZN :
      q ∣ Nat.card
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q))) :
    hktAbelianPResidual q Q ≠ (⊤ : Subgroup Q) := by
  classical
  let ZN : Subgroup Q :=
    Subgroup.normalizer
      ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)
  have hZNres_ne_top : hktAbelianPResidual q ZN ≠ (⊤ : Subgroup ZN) := by
    exact hktAbelianPResidual_ne_top_of_hasNormalPComplement_of_dvd_card
      (G := ZN) (q := q) (by simpa [ZN] using hcomp_ZN) (by simpa [ZN] using hq_dvd_ZN)
  haveI : (hktAbelianPResidual q Q).Normal :=
    hktAbelianPResidual_normal (Q := Q) (q := q)
  haveI : (hktAbelianPResidual q ZN).Normal :=
    hktAbelianPResidual_normal (Q := ZN) (q := q)
  have h37 :
      Nonempty ((Q ⧸ hktAbelianPResidual q Q) ≃*
        (ZN ⧸ hktAbelianPResidual q ZN)) := by
    simpa [ZN] using
      huppert_IV_3_7_second_grun (Q := Q) (q := q) S hpnormal
  obtain ⟨e⟩ := h37
  intro hres_top
  have hleft_subsingleton : Subsingleton (Q ⧸ hktAbelianPResidual q Q) := by
    rw [hres_top]
    exact QuotientGroup.subsingleton_quotient_top (G := Q)
  letI : Subsingleton (Q ⧸ hktAbelianPResidual q Q) := hleft_subsingleton
  have hright_subsingleton : Subsingleton (ZN ⧸ hktAbelianPResidual q ZN) := by
    refine ⟨?_⟩
    intro a b
    exact e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))
  have hZNres_top : hktAbelianPResidual q ZN = (⊤ : Subgroup ZN) :=
    QuotientGroup.subgroup_eq_top_of_subsingleton
      (hktAbelianPResidual q ZN) hright_subsingleton
  exact hZNres_ne_top hZNres_top

/-- Minimality supplies the normal `q`-complement in the ambient abelian
residual once IV.3.7 and the proper center normalizer show that residual is
proper. -/
public theorem hktAbelianPResidual_hasNormalPComplement_of_center_normalizer_minimal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hproper :
      ∀ H : Subgroup Q, H ≠ ⊥ → H ≠ ⊤ → q ∣ Nat.card H →
        HasNormalPComplement q H)
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcomp_ZN :
      HasNormalPComplement q
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)))
    (hq_dvd_ZN :
      q ∣ Nat.card
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q))) :
    HasNormalPComplement q (hktAbelianPResidual q Q) := by
  classical
  exact hktAbelianPResidual_hasNormalPComplement_of_minimal
    (Q := Q) (q := q) hproper
    (hktAbelianPResidual_ne_top_of_center_normalizer_hasNormalPComplement
      (Q := Q) (q := q) S hpnormal hcomp_ZN hq_dvd_ZN)
private theorem hkt_grun_iv34_kernel_control_center_normalizer
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)) :
    HasNormalPComplement q
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)) →
      HasNormalPComplement q (hktAbelianPResidual q Q) →
      HasNormalPComplement q Q := by
  classical
  intro hcomp_ZN hcomp_residual
  exact hkt_grun_iv34_hasNormalPComplement_core_source
    (Q := Q) (q := q) S hpnormal hcomp_ZN hcomp_residual

/-- Grün's second theorem IV.3.7 in the normal-complement consequence form
actually used here, after the book's residual-properness/minimality step. -/
private theorem hkt_grun_iv37_hasNormalPComplement_of_center_normalizer
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcomp_ZN :
      HasNormalPComplement q
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)))
    (hcomp_residual : HasNormalPComplement q (hktAbelianPResidual q Q)) :
    HasNormalPComplement q Q := by
  classical
  exact hkt_grun_iv34_kernel_control_center_normalizer
    (Q := Q) (q := q) S hpnormal hcomp_ZN hcomp_residual

/-- Grün's second theorem in the normal-complement consequence form actually
used here: IV.3.7 supplies the residual comparison, and the later
minimal-counterexample argument supplies the normal `q`-complement in
`Q'(q)`.  The ambient complement then follows by extension. -/
public theorem hkt_grun_second_hasNormalPComplement_of_center_normalizer
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hpnormal : ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q))
    (hcomp_ZN :
      HasNormalPComplement q
        (Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)))
    (hcomp_residual : HasNormalPComplement q (hktAbelianPResidual q Q)) :
    HasNormalPComplement q Q := by
  classical
  exact hkt_grun_iv37_hasNormalPComplement_of_center_normalizer
    (Q := Q) (q := q) S hpnormal hcomp_ZN hcomp_residual

end External
end CFSG.BenderSuzuki
