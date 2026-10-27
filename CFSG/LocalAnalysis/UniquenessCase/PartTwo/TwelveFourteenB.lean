module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qa
import CFSG.RankThree.GF2n.Assembly
import CFSG.LocalAnalysis.WeakClosure81.EightFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveFourteen

theorem mem_hSet_of_f12Hyp124 (D : Data G) {H₀ : Subgroup G} (h : F12.Hyp124 D H₀) :
    H₀ ∈ RankThreeUC.hSet D.T D.M := by
  refine ⟨h.le_T, h.not_le_M, ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.generalizedFitting ↥H₀ = CFSG.pCore 2 ↥H₀ := by
    have h1 := h.fstar
    unfold Fstar pCoreOf at h1
    rw [CFSG.Adapters.genFittingFStar_eq_foundations] at h1
    exact Subgroup.map_injective H₀.subtype_injective h1
  have hc : CFSG.IsCharacteristicP 2 ↥H₀ :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H₀ 2).2 hF
  rintro x ⟨hxH, hxC⟩
  have hx' : (⟨x, hxH⟩ : ↥H₀) ∈ centralizer (CFSG.pCore 2 ↥H₀ : Set ↥H₀) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxC (y : G) ⟨y, hy, rfl⟩
  exact ⟨⟨x, hxH⟩, hc hx', rfl⟩

theorem hyp124_of_f12Hyp124 (D : Data G) {H₀ : Subgroup G} (h : F12.Hyp124 D H₀) :
    RankThreeUC.Hyp124 D.M H₀ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨L, _, hL, n, hn, h1, hP⟩
    refine h.noOddRankOne ⟨n, hn, h1, L, inferInstance, hL, ?_⟩
    rcases hP with hP | hP | hP
    · exact Or.inl hP
    · exact Or.inr (Or.inr hP)
    · exact Or.inr (Or.inl hP)
  · intro hs ⟨L, _, hL, hP⟩
    refine h.noBig hs ⟨L, inferInstance, hL, ?_⟩
    rcases hP with ⟨t, m, n, hn, hP⟩ | hP | hP | hP | hP | hP | hP
    · exact Or.inl ⟨n, hn, t, m, hP⟩
    · exact Or.inr (Or.inl hP)
    · exact Or.inr (Or.inr (Or.inl hP))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hP)))))

theorem isTI_of_three_mem_sig3 (D : Data G) (h61 : UC6.R6_1 D) (h611 : UC6.R6_11Used D)
    (h3 : 3 ∈ D.sig3) {V : Subgroup G} (hV : InCalV D.M V) : IsTI V := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3sig : 3 ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inr h3
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨hshape, -, -, h5, -⟩ := h611 h3 P hP
  obtain ⟨e⟩ := hshape
  obtain ⟨Q, hQ, hPQ, hVQ⟩ := UC6.uc22p22q_exists_Q hP.isPGroup hP.le hV.2.2.1
    hV.2.1 (uc22p22e_isPGroup_of_elem hV.2.2.2)
  have hPV : P ≤ normalizer (V : Set G) := hP.le.trans hV.2.2.1
  have hcent := h5 Q hQ hPQ V hVQ hV.2.2.2.1 hPV
  obtain ⟨B, hB, hBp, hBc⟩ := uc22p22q_wreath_Z2 e
  have hBP : B ≤ P := hB.trans (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  exact uc22p22n_isTI_of_noncyclic D h61 h3sig hV (hBP.trans hP.le) hBp hBc
    (fun b hb => by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcent b (hB hb) v hv).symm)

theorem wClos_zero_ne_self (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hTI : IsTI V) (h4 : 4 ≤ Nat.card V) : E3.wClos V 0 D.T ≠ V := by
  intro hW
  haveI := D.standing.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNV : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hV2 : IsPGroup 2 V := uc22p22e_isPGroup_of_elem hV.2.2.2
  have hwc : ∀ g : G, conjSubgroup V g ≤ D.M → conjSubgroup V g = V := by
    intro g hg
    obtain ⟨m, hmM, hm⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM hg
      (E3.isPGroup_conjSubgroup hV2 g)
    have hle : conjSubgroup V (g * m) ≤ D.T := by
      rw [← conjSubgroup_conjSubgroup]
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have := hm _ hx
      simpa [mul_assoc] using this
    have hVgm : conjSubgroup V (g * m) = V :=
      Subgroup.eq_of_le_of_card_ge ((conjSubgroup_le_wClos_zero hle).trans hW.le)
        (E3.card_conjSubgroup V (g * m)).ge
    have hVm : conjSubgroup V m⁻¹ = V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hV.2.2.1 (by simpa using hmM))
    calc conjSubgroup V g = conjSubgroup (conjSubgroup V (g * m)) m⁻¹ := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel_right]
      _ = V := by rw [hVgm, hVm]
  have hlist := hTim G D.standing.nonab V hV.2.2.2 h4 (fun g => hTI g⁻¹)
    (fun g hg => hwc g (hg.trans hNV.le))
  exact hcat (CFSG.RankThree.GF2n.catalog_of_listGroup hlist)

theorem exists_noncyclic_le_centralizer (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀)
    {p : ℕ} (hp : p ∈ D.sig) {U : Subgroup G} (hU : InCalV D.M U) (hTI : IsTI U) :
    ∃ E : Subgroup G, E ≤ D.M ∧ IsPGroup p E ∧ ¬ IsCyclic E ∧
      E ≤ centralizer (U : Set G) := by
  have hpP : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  by_contra hno
  have hrk : CFSG.Open.pRank p (D.M ⊓ centralizer (U : Set G)) ≤ 1 := by
    by_contra hlt
    obtain ⟨E, hEC, hEel, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank hpP.one_lt (D.M ⊓ centralizer (U : Set G))
    refine hno ⟨E, hEC.trans inf_le_left, uc22p22e_isPGroup_of_elem hEel, ?_,
      hEC.trans inf_le_right⟩
    refine uc22p22n_not_isCyclic_of_card hpP hEel ?_
    rw [hEcard]
    exact Nat.pow_le_pow_right hpP.pos (by omega)
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hpP.one_lt D.M
  have hk3 : 3 ≤ CFSG.Open.pRank p D.M := hx.three_le p hp
  have hAel : IsElemAbelian p (E ⊓ centralizer (U : Set G)) :=
    uc22p22n_isElemAbelian_of_le inf_le_left hEel
  have hAcard : Nat.card ↥(E ⊓ centralizer (U : Set G)) ≤ p := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hAel)
    have h1 : j ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (U : Set G)) :=
      CFSG.SectionRank.le_pRank hpP.one_lt (le_inf (inf_le_left.trans hEM) inf_le_right) hAel hj
    rw [hj]
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hpP.pos (by omega)
      _ = p := pow_one p
  obtain ⟨P, hPE, hPA, hcardP⟩ := uc22p22nb_exists_complement hpP hEel inf_le_left hAcard
  have hPel : IsElemAbelian p P := uc22p22n_isElemAbelian_of_le hPE hEel
  have hPU : P ⊓ centralizer (U : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : x ∈ P ⊓ (E ⊓ centralizer (U : Set G)) := ⟨hx.1, hPE hx.1, hx.2⟩
    rw [hPA] at hmem
    exact hmem
  have hP2 : p ^ 2 ≤ Nat.card P := by
    rw [hEcard] at hcardP
    have h3 : p ^ 3 ≤ p ^ CFSG.Open.pRank p D.M := Nat.pow_le_pow_right hpP.pos hk3
    have h4 : p * p ^ 2 ≤ p * Nat.card P := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ p * Nat.card P := h3.trans hcardP
    exact Nat.le_of_mul_le_mul_left h4 hpP.pos
  have hPM : P ≤ D.M := hPE.trans hEM
  have h8 : 8 ≤ Nat.card U := by
    by_contra hlt
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp3 : 3 ≤ p := by
      have h2 := hpP.two_le
      have h3 := (D.sig_prime p hp).2
      omega
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hU.2.2.2)
    have h4 : Nat.card U ≤ 4 := by
      rw [hm] at hlt ⊢
      by_contra h5
      have h6 : 3 ≤ m := by
        by_contra h7
        have h8 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show m ≤ 2 by omega)
        omega
      have h9 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h6
      omega
    exact uc22p22nb_false_of_card_le_four (hPM.trans hU.2.2.1) hPU h4
      (le_trans (by nlinarith) hP2)
  exact (h127 h124 U hU hTI h8).1 (uc22p22nc_inCalV1_of_good D h61 hp hU hPM
    (uc22p22e_isPGroup_of_elem hPel) (uc22p22n_not_isCyclic_of_card hpP hPel hP2) hPU)

theorem conjSubgroup_inf_eq_bot (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {U₁ U₂ E : Subgroup G} (hU₁ : InCalV D.M U₁) (hTI₁ : IsTI U₁) (hEM : E ≤ D.M)
    (hEp : IsPGroup p E) (hEc : ¬ IsCyclic E) (hEU₂ : E ≤ centralizer (U₂ : Set G))
    {g : G} (hg : g ∉ D.M) : conjSubgroup U₁ g ⊓ U₂ = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  by_contra hu1
  obtain ⟨hug, huU₂⟩ := Subgroup.mem_inf.1 hu
  have hNU : normalizer (U₁ : Set G) = D.M := normalizer_eq_of_inCalV D hU₁
  have hEC : E ≤ centralizer ({u} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp (hEU₂ he) u huU₂
  have hEMg : E ≤ uniqueFourConj g D.M := by
    intro e he
    have heN : e ∈ normalizer (conjSubgroup U₁ g : Set G) :=
      centralizer_le_normalizer_conj hTI₁ g hug hu1 (hEC he)
    rw [UC6.mem_uniqueFourConj_iff, ← hNU, Subgroup.mem_normalizer_iff]
    intro v
    rw [Subgroup.mem_normalizer_iff] at heN
    have h1 := heN (g⁻¹ * v * g)
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff] at h1
    have e1 : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
    have e2 : g * (e * (g⁻¹ * v * g) * e⁻¹) * g⁻¹ = g * e * g⁻¹ * v * (g * e * g⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  have hmem : uniqueFourConj g D.M ∈ calMOf E := ⟨UC6.isMaxTwoLocal_conj D.maxLocal g, hEMg⟩
  rw [h61 p hp E hEM hEp hEc] at hmem
  have hgN : g ∈ normalizer (D.M : Set G) :=
    UC6.uniqueFourConj_eq_self_iff.mp (Set.mem_singleton_iff.mp hmem)
  apply hg
  rw [← UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal]
  exact hgN

theorem conjSubgroup_inf_self_eq_bot (D : Data G) {U : Subgroup G} (hU : InCalV D.M U)
    (hTI : IsTI U) {g : G} (hg : g ∉ D.M) : conjSubgroup U g ⊓ U = ⊥ := by
  have hc : conjSubgroup U g = CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ U := rfl
  rw [inf_comm, hc]
  rcases hTI g⁻¹ with h | h
  · exact h
  · exfalso
    apply hg
    have hle : U ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ U := inf_eq_left.1 h
    have hcard : Nat.card (CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ U) = Nat.card U := by
      rw [← hc]
      exact E3.card_conjSubgroup U g
    have heq : U = CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ U :=
      Subgroup.eq_of_le_of_card_ge hle hcard.le
    have hn : g⁻¹ ∈ normalizer (U : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 heq.symm
    rw [← normalizer_eq_of_inCalV D hU]
    simpa using (normalizer (U : Set G)).inv_mem hn

end TwelveFourteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
