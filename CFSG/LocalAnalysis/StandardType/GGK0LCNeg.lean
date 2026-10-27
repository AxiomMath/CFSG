module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs
public import CFSG.LocalAnalysis.StandardType.GGK0LCAct
public import CFSG.LocalAnalysis.StandardType.GGK0LCAffine

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace KacPt


theorem neg_node_zero
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) (j : Fin τ.rank) (h : AffNeg (K.act z (simpleAff j))) : K.s j = 0 := by
  have hroot : IsRoot τ (z • (Pi.single j 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (isRoot_single τ j) z
  have hspec : (K.p : ℤ) * K.shift z (Pi.single j 1) =
      (K.s j : ℤ) - K.lam (z • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
    rw [K.shift_spec hz (Pi.single j 1), K.lam_single]
  change AffNeg (z • (Pi.single j 1 : Fin τ.rank → ℤ),
      (0 : ℤ) + K.shift z (Pi.single j 1)) at h
  rw [zero_add] at h
  rcases h with hneg | ⟨hzero, hht⟩
  · have hdle : K.shift z (Pi.single j 1) ≤ -1 := by omega
    have hp : (0 : ℤ) < (K.p : ℤ) := by exact_mod_cast K.p_pos
    have hle := abs_lam_le hT K hroot
    have hlam : K.lam (z • (Pi.single j 1 : Fin τ.rank → ℤ)) ≤ (K.p : ℤ) := (abs_le.1 hle).2
    have hs : (K.s j : ℤ) ≤ 0 := by
      nlinarith [hspec, hdle, hp, hlam]
    omega
  · have hzero' : K.shift z (Pi.single j 1) = 0 := hzero
    have hht' : height (z • (Pi.single j 1 : Fin τ.rank → ℤ)) < 0 := hht
    have hlam_eq : K.lam (z • (Pi.single j 1 : Fin τ.rank → ℤ)) = (K.s j : ℤ) := by
      have hs := hspec
      rw [hzero', mul_zero] at hs
      linarith
    have hall : ∀ i, (z • (Pi.single j 1 : Fin τ.rank → ℤ)) i ≤ 0 :=
      (IsRoot.height_neg_iff hroot).1 hht'
    have hnonneg : 0 ≤ K.lam (-(z • (Pi.single j 1 : Fin τ.rank → ℤ))) :=
      K.lam_nonneg_of_nonneg (fun i => by
        have hi := hall i
        simp only [Pi.neg_apply]
        omega)
    have hneg_lam : K.lam (-(z • (Pi.single j 1 : Fin τ.rank → ℤ))) =
        -K.lam (z • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
      have hm := K.lam_smul (-1) (z • (Pi.single j 1 : Fin τ.rank → ℤ))
      simpa using hm
    have hs : (K.s j : ℤ) ≤ 0 := by
      rw [hneg_lam, hlam_eq] at hnonneg
      linarith
    omega

theorem neg_ext_zero
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) (h : AffNeg (K.act z (extAff τ))) : K.s0 = 0 := by
  have hrootθ : IsRoot τ (theta τ) := hT.2.1
  have hroot : IsRoot τ (z • theta τ) := IsRoot.smul hrootθ z
  have hle := abs_lam_le hT K hroot
  have hp : (0 : ℤ) < (K.p : ℤ) := by exact_mod_cast K.p_pos
  have hsh : K.shift z (-theta τ) = -K.shift z (theta τ) := by
    have hm := K.shift_smul hz (-1) (theta τ)
    simpa using hm
  have hact : K.act z (extAff τ) = (-(z • theta τ), 1 - K.shift z (theta τ)) := by
    simp only [KacPt.act, extAff]
    rw [smul_neg, hsh]
    simp [sub_eq_add_neg]
  rw [hact] at h
  have hshift : (K.p : ℤ) * K.shift z (theta τ) =
      (K.p : ℤ) - (K.s0 : ℤ) - K.lam (z • theta τ) := by
    have hm := K.shift_spec hz (theta τ)
    rw [K.lam_theta] at hm
    linarith
  have hkey : (K.p : ℤ) * (1 - K.shift z (theta τ)) =
      (K.s0 : ℤ) + K.lam (z • theta τ) := by
    have hm : (K.p : ℤ) * (1 - K.shift z (theta τ)) =
        (K.p : ℤ) - (K.p : ℤ) * K.shift z (theta τ) := by ring
    rw [hm, hshift]; ring
  rcases h with hneg | ⟨hzero, hht⟩
  · have hle1 : (1 : ℤ) - K.shift z (theta τ) ≤ -1 := by omega
    have hu : -(K.p : ℤ) ≤ K.lam (z • theta τ) := by
      have hm := (abs_le.1 hle).1
      linarith
    have hs : (K.s0 : ℤ) ≤ 0 := by
      nlinarith [hkey, hle1, hp, hu]
    omega
  · have hzero' : (1 : ℤ) - K.shift z (theta τ) = 0 := hzero
    have hht' : height (-(z • theta τ)) < 0 := hht
    have hsum : (K.s0 : ℤ) + K.lam (z • theta τ) = 0 := by
      have hm := hkey
      rw [hzero', mul_zero] at hm
      linarith
    have hposu : 0 ≤ K.lam (z • theta τ) := by
      apply K.lam_nonneg_of_nonneg
      intro i
      have hpos : 0 < height (z • theta τ) := by
        have hm := hht'
        rw [height_neg] at hm
        linarith
      exact (IsRoot.height_pos_iff hroot).1 hpos i
    have hs : (K.s0 : ℤ) ≤ 0 := by linarith
    omega

theorem inv_finite
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) : (K.inv z).Finite := by
  have hfin : ({v : Fin τ.rank → ℤ | IsRoot τ v} ×ˢ Set.Icc (0 : ℤ) 2).Finite :=
    (finite_setOf_isRoot τ).prod (Set.finite_Icc (0 : ℤ) 2)
  refine hfin.subset ?_
  rintro ⟨γ, k⟩ ha
  change IsRoot τ γ ∧ AffPos (γ, k) ∧ AffNeg (K.act z (γ, k)) at ha
  obtain ⟨hroot, hpos, hneg⟩ := ha
  rw [Set.mem_prod]
  refine ⟨hroot, ?_⟩
  have hk0 : 0 ≤ k := by
    rcases hpos with hk | ⟨hk, -⟩
    · exact le_of_lt hk
    · exact le_of_eq hk.symm
  have hk2 : k ≤ 2 := by
    have hsh := abs_shift_le hT K hz hroot
    change AffNeg (z • γ, k + K.shift z γ) at hneg
    rcases hneg with hkneg | ⟨hkneg, -⟩
    · have h1 : k < -(K.shift z γ) := by linarith
      have h2 : -(K.shift z γ) ≤ 2 := by
        have hm := (abs_le.1 hsh).1
        linarith
      linarith
    · have hk : k = -(K.shift z γ) := by linarith
      rw [hk]
      have h2 : -(K.shift z γ) ≤ 2 := by
        have hm := (abs_le.1 hsh).1
        linarith
      exact h2
  exact ⟨hk0, hk2⟩

theorem exists_neg_simple
    {τ : Tag} (hT : KacBox τ) (K : KacPt τ) {z : WeylGroup τ}
    (hz : z ∈ K.stab) (hne : (K.inv z).Nonempty) :
    (∃ j, AffNeg (K.act z (simpleAff j))) ∨ AffNeg (K.act z (extAff τ)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnotex, hext⟩ := hcon
  rw [not_exists] at hnotex
  have h0 : AffPos (K.act z (extAff τ)) :=
    (affPos_iff_not_affNeg (IsRoot.smul (IsRoot.neg hT.2.1) z)).2 hext
  have hx : ∀ i, AffPos (K.act z (simpleAff i)) := fun i =>
    (affPos_iff_not_affNeg (IsRoot.smul (isRoot_single τ i) z)).2 (hnotex i)
  obtain ⟨a, ha⟩ := hne
  change IsRoot τ a.1 ∧ AffPos a ∧ AffNeg (K.act z a) at ha
  obtain ⟨haroot, hapos, haneg⟩ := ha
  obtain ⟨n0, n, hdecomp, hnecoe⟩ := aff_pos_decomp hT haroot hapos
  have hsum : K.act z (∑ i, (n i : ℤ) • simpleAff i) =
      ∑ i, (n i : ℤ) • K.act z (simpleAff i) := by
    rw [K.act_sum hz]
    exact Finset.sum_congr rfl (fun i _ => by rw [K.act_smul hz])
  have hact : K.act z a =
      (n0 : ℤ) • K.act z (extAff τ) + ∑ i, (n i : ℤ) • K.act z (simpleAff i) := by
    rw [hdecomp, K.act_add hz, K.act_smul hz, hsum]
  have hposact : AffPos (K.act z a) := by
    rw [hact]
    exact affPos_combo n0 n h0 hx hnecoe
  have hrootact : IsRoot τ (K.act z a).1 := IsRoot.smul haroot z
  exact (affPos_iff_not_affNeg hrootact).1 hposact haneg

end KacPt

end CFSG.StandardType.GGK0LC

end
