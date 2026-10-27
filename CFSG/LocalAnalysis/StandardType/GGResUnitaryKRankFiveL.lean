module

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryKRankFiveLDefs
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryRankNineK3
public import CFSG.LocalAnalysis.StandardType.GGResE6TwoUnitaryK3
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGResThreeCensusLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem dvd_sub_or_eq_one_of_split_three_untwisted {lab : LargeEvenLabel}
    (hs : LargeEvenSplit 3 lab) (hu : LargeEvenUntwisted lab.tag) :
    3 ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 := by
  rcases hs with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact absurd hu h
  · rcases h with h | h <;> rw [h] at hu <;> simp [LargeEvenUntwisted] at hu
  · exact Or.inr h

theorem ggTBTorRow_three_of_bounds {lab : LargeEvenLabel} {r m N : ℕ}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt 3 lab r m N C M) (hs : LargeEvenSplit 3 lab) (hr : r ≤ 3)
    (hN : 4 ≤ N) :
    GGSpEightOmegaEightTwoLabel 3 lab ∨ (lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 3 ∣ 2 ^ lab.n + 1) := by
  have h1 := ggTorEnn_le_one 3 lab
  have hE : ggTorEnn 3 lab = 1 → 3 ∣ 2 ^ lab.n + 1 := by
    intro h
    by_contra hq
    have h0 : ggTorEnn 3 lab = 0 := by
      unfold ggTorEnn
      rw [if_neg hq]
    omega
  have hpm : 3 ∣ 2 ^ lab.n - 1 → ¬ 3 ∣ 2 ^ lab.n + 1 :=
    not_dvd_two_pow_add_one_of_dvd_sub (by norm_num) (by norm_num)
  cases hrow with
  | aDep _ h2 h3 _ h5 =>
    exfalso
    have hr5 : lab.rank = 5 := by
      rcases (show lab.rank = 4 ∨ lab.rank = 5 by omega) with h | h
      · rw [h] at h3
        norm_num at h3
      · exact h
    exact h5 ⟨rfl, hr5, hE (by omega)⟩
  | e6Three _ _ _ => omega
  | e8Three _ _ => omega
  | aInd ht _ h3 =>
    have hq := hE (by omega)
    rcases ht with ht | ht
    · exfalso
      have hq' : 3 ∣ 2 ^ lab.n - 1 := by simpa [ggTorM, ht] using h3
      exact hpm hq' hq
    · exact Or.inr ⟨ht, by omega, hq⟩
  | c ht _ =>
    have hq := hE (by omega)
    have hu : LargeEvenUntwisted lab.tag := by rcases ht with ht | ht <;> rw [ht] <;> trivial
    rcases dvd_sub_or_eq_one_of_split_three_untwisted hs hu with hq' | hn
    · exact absurd hq (hpm hq')
    · exact Or.inl ⟨by rcases ht with ht | ht <;> simp [ht], by omega, hn⟩
  | d ht =>
    have hq := hE (by omega)
    rcases ht with ⟨ht, -⟩ | ⟨-, -, hodd⟩
    · rcases dvd_sub_or_eq_one_of_split_three_untwisted hs (by rw [ht]; trivial) with hq' | hn
      · exact absurd hq (hpm hq')
      · exact Or.inl ⟨Or.inr (Or.inr ht), by omega, hn⟩
    · exfalso
      obtain ⟨k, hk⟩ := hodd
      omega
  | e6Ind h _ _ => exact absurd rfl h
  | e7 _ _ => omega
  | e8Ind h _ _ => exact absurd rfl h
  | f4 _ _ h3 => exact absurd ⟨rfl, hE (by omega)⟩ h3
  | g2 _ _ => omega
  | relD _ => omega
  | relE6 h _ => exact absurd rfl h
  | relA5 _ _ => omega

theorem not_twASplit_three_of_split {lab : LargeEvenLabel} (hs : LargeEvenSplit 3 lab) :
    ¬ GGTwASplitLabel 3 lab := by
  rintro ⟨ht, -, hq⟩
  rcases hs with ⟨hu, -⟩ | ⟨-, -, hq'⟩ | ⟨h, -⟩ | ⟨hn, -⟩
  · rw [ht] at hu
    exact hu
  · exact not_dvd_two_pow_add_one_of_dvd_sub (by norm_num) (by norm_num) hq hq'
  · rcases h with h | h <;> rw [ht] at h <;> cases h
  · rw [hn] at hq
    norm_num at hq

section Cert


theorem GGResHyp.spEightOmegaEightTwo_L_of_rankFiveK3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (hLs : ¬ GGInnerDiagOnLabel ggThreeSettledLabelL p Bs L)
    (hsm : ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L)
    (hF4 : ¬ GGInnerDiagOnLabel GGF4ThreeLabel p Bs L) :
    GGInnerDiagOnLabel GGSpEightOmegaEightTwoLabel p Bs L := by
  classical
  obtain ⟨_F, _iF, _iFin, _n, _θK, _ψK, _δ, -, -, -, -, -, hp3, -, -, -, -, -, -, -⟩ :=
    hH.rankFiveK3_original_facts hU h3
  subst hp3
  have hp : Nat.Prime 3 := Fact.out
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hU4 : GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
      p ∣ 2 ^ lab.n + 1) 3 Bs K :=
    GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, by omega, h.2.2.1, h.2.2.2⟩) hU
  have hKres : GGInnerDiagOnLabel ggThreeResidualLabelK 3 Bs K :=
    GGInnerDiagOnLabel.mono_label
      (fun _ h => ⟨h.1, by omega, by rw [h.2.1]; norm_num, h.2.2.2⟩) hU
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  have hst : LargeEvenStandardType 3 B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hPl⟩ := largeEvenMarking_exists_hasLabel hst.1
  have hall : ∀ S : ℕ → LargeEvenLabel → Prop, S 3 lab → GGInnerDiagOnLabel S 3 Bs L := by
    intro S hS'
    refine largeEvenMarking_mono ?_
      (ggInnerDiagOn_relabel ggLabelRigidInput_holds hH.2.2.1.1 hlab hhas)
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨hS', h2, h3⟩
  have hs : LargeEvenSplit 3 lab := hPl.1
  have hE6 : lab.tag = .E6 → 3 ∣ 2 ^ lab.n - 1 → False := fun ht hq =>
    hH.not_exactThree_K_of_original_L_marking_qGeFour
      (Or.inr (hall (fun _ lab' => lab'.tag = .E6 ∧ 3 ∣ 2 ^ lab'.n - 1) ⟨ht, hq⟩)) hU4 hN h3
  have htwE6 : lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 → False := fun ht hq =>
    hH.not_exactThree_K_of_twE6_qplus_L_qGeFour
      (hall (fun _ lab' => lab'.tag = .twE6 ∧ 3 ∣ 2 ^ lab'.n + 1) ⟨ht, hq⟩) hU4 h3
  rcases ggThreeCensus_label_L hp hp2 hlab hs with hnb | hS | hsm' | hE6L | hres
  · rcases hnb with ⟨⟨r, m, N, C, M, hrow⟩, -⟩ | hF4' | htw
    · obtain ⟨-, hr3, hN4⟩ := hH.tbTorRow_bounds_five_of_unitary_exactThree_K
        (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds
        (hall (fun p lab => GGTBTorRowAt p lab r m N C M) hrow) hU h3
      rcases ggTBTorRow_three_of_bounds hrow hs hr3 hN4 with h | ⟨ht, hl, hq⟩
      · exact hall _ h
      · exact (hLs (hall _ (Or.inr (Or.inl ⟨ht, hl, hq⟩)))).elim
    · exact (hF4 (hall _ hF4')).elim
    · exact (not_twASplit_three_of_split hs htw).elim
  · exact (hLs (hall _ hS)).elim
  · exact (hsm (hall _ hsm')).elim
  ·
    obtain ⟨-, hdep⟩ := hE6L
    rcases hdep with ⟨ht, hq⟩ | ⟨ht, hq⟩ | ⟨ht, hq⟩ | ⟨ht, hq⟩
    · exact (hE6 ht hq).elim
    · exact (htwE6 ht hq).elim
    ·
      exfalso
      rcases hs with ⟨hu, -⟩ | ⟨-, -, hq'⟩ | ⟨h, -⟩ | ⟨hn, -⟩
      · rw [ht] at hu
        exact hu
      · exact not_dvd_two_pow_add_one_of_dvd_sub (by norm_num) (by norm_num) hq hq'
      · rcases h with h | h <;> rw [ht] at h <;> cases h
      · rw [hn] at hq
        norm_num at hq
    ·
      rcases dvd_sub_or_eq_one_of_split_three_untwisted hs (by rw [ht]; trivial) with hq' | hn
      · exact (not_dvd_two_pow_add_one_of_dvd_sub (by norm_num) (by norm_num) hq' hq).elim
      · exact (hH.not_exactThree_K_of_e6Two_L_residual_K
          (hall (fun _ lab' => lab'.tag = .E6 ∧ lab'.n = 1) ⟨ht, hn⟩) hKres h3).elim
  ·
    obtain ⟨-, ht, hn, -⟩ := hres
    have he : lab = ⟨.A, lab.rank, 1⟩ := by
      calc lab = ⟨lab.tag, lab.rank, lab.n⟩ := rfl
        _ = ⟨.A, lab.rank, 1⟩ := by rw [ht, hn]
    exact (hH.not_exactThree_K_of_original_L_marking_qGeFour
      (Or.inl ⟨lab.rank, 1, by norm_num, hall (fun _ lab' => lab' = ⟨.A, lab.rank, 1⟩) he⟩)
      hU4 hN h3).elim

theorem ggResMultiNodeRestThreeKUnitaryQGeFourRestInput_of_fieldTwo
    (h : GGResMultiNodeRestThreeKUnitaryQGeFourFieldTwoInput) :
    GGResMultiNodeRestThreeKUnitaryQGeFourRestInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hdata
  obtain ⟨hDK, ⟨lab, hlab, hr5, hn2, hmark⟩, hnK, hE6K, hL2K, hLnK, hLsK, hsetL, hsmL, hF4,
    hKs, hres, htwo, hC2, hSU2⟩ := hdata
  have hU : GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧
      p ∣ 2 ^ lab.n + 1) p Bs K := by
    refine GGInnerDiagOnLabel.mono_label (S := fun _ lab' => lab' = lab) ?_ hmark
    intro lab' hlab'
    subst lab'
    exact ⟨hlab.1, hr5, hn2, hlab.2.2.2⟩
  exact h G p B Bs x L D J y K hH hF hS hE
    ⟨⟨hDK, ⟨lab, hlab, hr5, hn2, hmark⟩, hnK, hE6K, hL2K, hLnK, hLsK, hsetL, hsmL, hF4, hKs,
      hres, htwo, hC2, hSU2⟩, hH.spEightOmegaEightTwo_L_of_rankFiveK3 hU hDK hsetL hsmL hF4⟩

end Cert

end CFSG.StandardType

end
