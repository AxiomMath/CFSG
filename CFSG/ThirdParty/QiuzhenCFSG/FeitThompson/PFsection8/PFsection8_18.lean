module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_13
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_17

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8
universe u
universe v
universe w

@[expose] public def theorem_8_18_statement
    {G : Type u} [Group G] [Finite G]
    (S T SF TF SS TT : Subgroup G)
    (AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G)
    (AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G)
    (RS RT : G → Subgroup G) : Prop :=
  IsMinCE G →
    theorem_8_18_source_notation_data S T SF TF SS TT
        AS A0S A1S DS tildeAS tildeA0S tildeA1S
        AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT →
      (supportsSubgroupSource S T DS ↔ (A1S ∩ AT).Nonempty) ∧
        (∀ x : G, x ∈ A1S ∩ AT →
          ¬ Subgroup.centralizer ({x} : Set G) ≤ S ∧
            Subgroup.centralizer ({x} : Set G) ≤ T) ∧
        ((∃ g : G, supportsSubgroupSource S (T.conjBy g) DS) ↔
          (tildeA1S ∩ tildeAT).Nonempty) ∧
        (Disjoint tildeA1S tildeAT ∨ Disjoint tildeA1T tildeAS)


open scoped Pointwise

private theorem theorem_8_18_conjugates_univ_eq_section14ConjugacyClosure
    {G : Type u} [Group G]
    (X : Set G) :
    section16ConjugatesOfSetBySet X Set.univ = section14ConjugacyClosure X := by
  ext z
  constructor
  · rintro ⟨x, hx, g, _hg, rfl⟩
    refine ⟨x, hx, g⁻¹, ?_⟩
    simp [mul_assoc]
  · rintro ⟨x, hx, g, rfl⟩
    refine ⟨x, hx, g⁻¹, by simp, ?_⟩
    simp [mul_assoc]

private theorem theorem_8_18_tildeM_section14R_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M : Subgroup G) :
    section16TildeM M (fun x : G => section14R x) = section14Tilde M := by
  ext y
  constructor
  · rintro ⟨x, hxMσ, hxne, r, hr, rfl⟩
    exact ⟨x, hxMσ, hxne, r, hr, rfl⟩
  · rintro ⟨x, hxMσ, hxne, r, hr, rfl⟩
    exact ⟨x, hxMσ, hxne, r, hr, rfl⟩

private theorem theorem_8_18_tildeA1_eq_section14ConjugacyClosure
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    tildeA1 = section14ConjugacyClosure (section14Tilde M) := by
  calc
    tildeA1 =
        section16ConjugatesOfSetBySet
          (section16TildeM M (fun x : G => section14R x)) Set.univ :=
      theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R_public
        (G := G) hRep
    _ = section14ConjugacyClosure
        (section16TildeM M (fun x : G => section14R x)) := by
      rw [theorem_8_18_conjugates_univ_eq_section14ConjugacyClosure]
    _ = section14ConjugacyClosure (section14Tilde M) := by
      rw [theorem_8_18_tildeM_section14R_eq]

public theorem theorem_8_18_tildeA1_disjoint_of_nonconj
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT) :
    Disjoint tildeA1S tildeA1T := by
  rcases hData with ⟨hNonconj, hS10, _hSmem, hT10, _hTmem, hS14, hT14⟩
  rcases hS10 with ⟨hSmax, hSF, hSS, hA1S, hScases⟩
  rcases hT10 with ⟨hTmax, hTF, hTT, hA1T, hTcases⟩
  have hSclosure :
      tildeA1S = section14ConjugacyClosure (section14Tilde S) :=
    theorem_8_18_tildeA1_eq_section14ConjugacyClosure
      (G := G)
      (hRep := ⟨⟨hSmax, hSF, hSS, hA1S, hScases⟩, hS14⟩)
  have hTclosure :
      tildeA1T = section14ConjugacyClosure (section14Tilde T) :=
    theorem_8_18_tildeA1_eq_section14ConjugacyClosure
      (G := G)
      (hRep := ⟨⟨hTmax, hTF, hTT, hA1T, hTcases⟩, hT14⟩)
  have hnot14 : ¬ section14ConjugateSubgroups T S := by
    intro hconj
    rcases hconj with ⟨g, hg⟩
    exact hNonconj ⟨g, by simp, hg⟩
  have hdisTS :
      section14ConjugacyClosure (section14Tilde T) ∩
          section14ConjugacyClosure (section14Tilde S) = ∅ :=
    section14_conjClosure_tilde_disjoint_of_not_conjugate_public
      (G := G) (M₁ := S) (M₂ := T) hSmax hTmax hnot14
  rw [Set.disjoint_iff_inter_eq_empty]
  calc
    tildeA1S ∩ tildeA1T =
        section14ConjugacyClosure (section14Tilde S) ∩
          section14ConjugacyClosure (section14Tilde T) := by
      rw [hSclosure, hTclosure]
    _ = section14ConjugacyClosure (section14Tilde T) ∩
          section14ConjugacyClosure (section14Tilde S) := by
      rw [Set.inter_comm]
    _ = ∅ := hdisTS

private theorem theorem_8_18_source_data_swap
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT) :
    theorem_8_18_source_data T S TF SF TT SS
      AT A0T A1T DT tildeAT tildeA0T tildeA1T
      AS A0S A1S DS tildeAS tildeA0S tildeA1S RT RS := by
  rcases hData with ⟨hNonconj, hS10, hSmem, hT10, hTmem, hS14, hT14⟩
  have hNonconj' :
      ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) T S := by
    rintro ⟨g, _hg, hEq⟩
    apply hNonconj
    refine ⟨g⁻¹, by simp, ?_⟩
    calc
      T = (T.conjBy g).conjBy g⁻¹ := (Subgroup.conjBy_inv T g).symm
      _ = S.conjBy g⁻¹ := by rw [← hEq]
  exact ⟨hNonconj', hT10, hTmem, hS10, hSmem, hT14, hS14⟩

private theorem theorem_8_18_tildeAT_witness_diff_A1_of_inter
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {y : G} (hy : y ∈ tildeA1S ∩ tildeAT) :
    ∃ a : G, a ∈ AT \ A1T ∧
      y ∈ section16ConjugatesOfSetBySet
        (section16LeftCosetSet a (RT a)) Set.univ ∧
      RT a = (⊥ : Subgroup G) := by
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := hData
  rcases hData with ⟨_hNonconj, _hS10, _hSmem, hT10, _hTmem, _hS14, hT14⟩
  rcases hT14 with
    ⟨_hA1TA, hATA0T, hDT, hRTbot, _hTUnique, _hRTeq,
      htildeAT, _htildeA0T, htildeA1T⟩
  rcases hT10 with ⟨_hTmax, _hTF, _hTT, _hA1T, _hTcases⟩
  have hDis : Disjoint tildeA1S tildeA1T :=
    theorem_8_18_tildeA1_disjoint_of_nonconj (G := G) hData'
  rw [htildeAT] at hy
  rcases hy.2 with ⟨a, haAT, hya⟩
  have haNotA1T : a ∉ A1T := by
    intro haA1T
    have hyA1T : y ∈ tildeA1T := by
      rw [htildeA1T]
      exact ⟨a, haA1T, hya⟩
    exact (Set.disjoint_left.mp hDis hy.1) hyA1T
  have h13T :=
    (theorem_8_13 (G := G) T TF TT AT A0T A1T A0T)
      (inferInstance : IsMinCE G)
      ⟨_hTmax, _hTF, _hTT, _hA1T, _hTcases⟩
      (Or.inr rfl)
  have haA0T : a ∈ A0T := hATA0T haAT
  have haNotDT : a ∉ DT := by
    intro haDT
    have haDSet : a ∈ section8DSet T A0T := by
      simpa [hDT] using haDT
    exact haNotA1T (h13T.2.1 haDSet)
  exact ⟨a, ⟨haAT, haNotA1T⟩, hya, hRTbot a ⟨haA0T, haNotDT⟩⟩

private theorem theorem_8_18_mem_conj_leftCoset_bot
    {G : Type u} [Group G]
    {a y : G}
    (hy :
      y ∈ section16ConjugatesOfSetBySet
        (section16LeftCosetSet a (⊥ : Subgroup G)) Set.univ) :
    ∃ g : G, y = g * a * g⁻¹ := by
  rcases hy with ⟨z, hz, g, _hg, hyEq⟩
  rcases hz with ⟨r, hr, rfl⟩
  have hr1 : r = 1 := by
    simpa using hr
  subst r
  exact ⟨g, by simpa using hyEq⟩

private theorem theorem_8_18_tildeA1S_witness_eq_of_mem
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {y : G} (hy : y ∈ tildeA1S) :
    ∃ b r g : G, b ∈ A1S ∧ r ∈ RS b ∧ y = g * (b * r) * g⁻¹ := by
  rcases hData with ⟨_hNonconj, _hS10, _hSmem, _hT10, _hTmem, hS14, _hT14⟩
  rcases hS14 with
    ⟨_hA1SA, _hASA0S, _hDS, _hRSbot, _hSUnique, _hRSeq,
      _htildeAS, _htildeA0S, htildeA1S⟩
  rw [htildeA1S] at hy
  rcases hy with ⟨b, hbA1S, z, hz, g, _hg, hyEq⟩
  rcases hz with ⟨r, hrRS, hzEq⟩
  refine ⟨b, r, g, hbA1S, hrRS, ?_⟩
  rw [hyEq, hzEq]

private theorem theorem_8_18_tilde_inter_local_coset_conj
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {y : G} (hy : y ∈ tildeA1S ∩ tildeAT) :
    ∃ a b r c : G, a ∈ AT \ A1T ∧ b ∈ A1S ∧ r ∈ RS b ∧
      RT a = (⊥ : Subgroup G) ∧ a = c * (b * r) * c⁻¹ := by
  rcases theorem_8_18_tildeAT_witness_diff_A1_of_inter (G := G) hData hy with
    ⟨a, haDiff, hya, hRTa⟩
  rcases theorem_8_18_mem_conj_leftCoset_bot (by simpa [hRTa] using hya) with
    ⟨gT, hyT⟩
  rcases theorem_8_18_tildeA1S_witness_eq_of_mem (G := G) hData hy.1 with
    ⟨b, r, gS, hbA1S, hrRS, hyS⟩
  refine ⟨a, b, r, gT⁻¹ * gS, haDiff, hbA1S, hrRS, hRTa, ?_⟩
  calc
    a = gT⁻¹ * y * gT := by
      rw [hyT]
      group
    _ = (gT⁻¹ * gS) * (b * r) * (gT⁻¹ * gS)⁻¹ := by
      rw [hyS]
      group

private theorem theorem_8_18_mem_zpowers_mul_of_commute_of_coprime_order
    {G : Type u} [Group G]
    {a b : G} (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) :
    a ∈ Subgroup.zpowers (a * b) := by
  have hbpow : b ^ orderOf b = 1 := pow_orderOf_eq_one b
  have hpow : (a * b) ^ orderOf b = a ^ orderOf b := by
    rw [hab.mul_pow, hbpow, mul_one]
  have hamem : a ∈ Subgroup.zpowers (a ^ orderOf b) := by
    rw [mem_zpowers_pow_iff]
    simpa [Nat.gcd_comm] using hcop.gcd_eq_one
  rcases hamem with ⟨n, hn⟩
  refine ⟨(orderOf b : ℤ) * n, ?_⟩
  calc
    (a * b) ^ ((orderOf b : ℤ) * n) =
        ((a * b) ^ (orderOf b : ℤ)) ^ n := by
          rw [zpow_mul]
    _ = ((a * b) ^ orderOf b) ^ n := by
          rw [zpow_natCast]
    _ = (a ^ orderOf b) ^ n := by
          rw [hpow]
    _ = a := by
          simpa using hn

private theorem theorem_8_18_mem_left_of_A1
    {G : Type u} [Group G] [Finite G]
    {S SF SS : Subgroup G} {AS A0S A1S : Set G} {b : G}
    (hS10 : notation_8_10_source_data S SF SS AS A0S A1S)
    (hbA1S : b ∈ A1S) :
    b ∈ S := by
  rcases hS10 with ⟨_hSmax, hSF, hSS, hA1S, _hCases⟩
  have hbSS : b ∈ SS := by
    have hbSS_ne : b ∈ SS ∧ b ≠ 1 := by
      simpa [hA1S, a1Set, section16NonidentityElements] using hbA1S
    exact hbSS_ne.1
  rcases hSS with hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · rcases hTypeI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hSS_eq⟩
    exact hSF.1.1 (by simpa [hSS_eq] using hbSS)
  · rcases hTypeII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hSS_eq⟩
    exact hSF.1.1 (by simpa [hSS_eq] using hbSS)
  · rcases hTypeIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, _hnotV, hSS_eq⟩
    exact section12_ambientDerivedSubgroup_le (G := G) (E := S)
      (by simpa [hSS_eq] using hbSS)
  · rcases hTypeIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, _hnotV, hSS_eq⟩
    exact section12_ambientDerivedSubgroup_le (G := G) (E := S)
      (by simpa [hSS_eq] using hbSS)
  · rcases hTypeV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hSS_eq⟩
    exact hSF.1.1 (by simpa [hSS_eq] using hbSS)

private theorem theorem_8_18_mem_A_mem_left
    {G : Type u} [Group G] [Finite G]
    {S SF SS : Subgroup G} {AS A0S A1S : Set G} {a : G}
    (hS10 : notation_8_10_source_data S SF SS AS A0S A1S)
    (haAS : a ∈ AS) :
    a ∈ S := by
  rcases hS10 with ⟨_hSmax, hSF, _hSS, _hA1S, hCases⟩
  rcases hCases with hTypeI | hTypeP
  · rcases hTypeI with ⟨_hTypeI, hAS, _hA0S⟩
    rw [hAS, section8CentralizerUnion] at haAS
    rcases haAS with ⟨_z, _hz, haCent⟩
    exact haCent.1.1
  · rcases hTypeP with ⟨_U, _W1, _W2, _hP, _hSourceType, hAS, _hA0S, _hLate⟩
    rw [hAS, section8CentralizerUnion] at haAS
    rcases haAS with ⟨_z, _hz, haCent⟩
    exact section12_ambientDerivedSubgroup_le (G := G) (E := S) haCent.1.1

private theorem theorem_8_18_left_mem_zpowers_mul_localR
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {b r : G} (hbA1S : b ∈ A1S) (hrRS : r ∈ RS b) :
    b ∈ Subgroup.zpowers (b * r) := by
  rcases hData with ⟨_hNonconj, hS10, _hSmem, _hT10, _hTmem, hS14, _hT14⟩
  rcases hS14 with
    ⟨hA1SA, hASA0S, hDS, hRSbot, _hSUnique, hRSeq,
      _htildeAS, _htildeA0S, _htildeA1S⟩
  have hbA0S : b ∈ A0S := hASA0S (hA1SA hbA1S)
  by_cases hbDS : b ∈ DS
  · have h13S :=
      (theorem_8_13 (G := G) S SF SS AS A0S A1S A0S)
        (inferInstance : IsMinCE G) hS10 (Or.inr rfl)
    have hbDSet : b ∈ section8DSet S A0S := by
      simpa [hDS] using hbDS
    rcases h13S.2.2.1 b hbDSet with ⟨L, hLmem, _hLuniq⟩
    rcases h13S.2.2.2 b hbDSet L hLmem with ⟨LF, hSupp⟩
    rcases hSupp with
      ⟨_hLmax, hLF, hUniqueSet, _hSemiL, _hSemiC, hCoprime, _hCases⟩
    have hRS_eq : RS b = elementCentralizerIn LF b :=
      hRSeq b hbDS L LF hUniqueSet hLF
    have hrCent : r ∈ elementCentralizerIn LF b := by
      simpa [hRS_eq] using hrRS
    have hcomm : Commute b r := by
      exact (Subgroup.mem_centralizer_singleton_iff.mp hrCent.2).symm
    have hbS : b ∈ S := theorem_8_18_mem_left_of_A1 hS10 hbA1S
    have hbCent : b ∈ elementCentralizerIn S b := by
      refine ⟨hbS, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl b)
    have horder_b :
        orderOf b ∣ Nat.card (elementCentralizerIn S b) :=
      Subgroup.orderOf_dvd_natCard (elementCentralizerIn S b) hbCent
    have horder_r : orderOf r ∣ Nat.card LF :=
      Subgroup.orderOf_dvd_natCard LF hrCent.1
    have hcop : Nat.Coprime (orderOf b) (orderOf r) :=
      Nat.Coprime.of_dvd horder_b horder_r (hCoprime b hbA0S).symm
    exact theorem_8_18_mem_zpowers_mul_of_commute_of_coprime_order hcomm hcop
  · have hRS_eq : RS b = (⊥ : Subgroup G) := hRSbot b ⟨hbA0S, hbDS⟩
    have hr_one : r = 1 := by
      simpa [hRS_eq] using hrRS
    simp [hr_one]

private theorem theorem_8_18_tilde_inter_left_mem_zpowers_conj
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {y : G} (hy : y ∈ tildeA1S ∩ tildeAT) :
    ∃ a b c : G, a ∈ AT \ A1T ∧ b ∈ A1S ∧ RT a = (⊥ : Subgroup G) ∧
      b ∈ Subgroup.zpowers (c⁻¹ * a * c) := by
  rcases theorem_8_18_tilde_inter_local_coset_conj (G := G) hData hy with
    ⟨a, b, r, c, haDiff, hbA1S, hrRS, hRTa, hEq⟩
  have hbPow : b ∈ Subgroup.zpowers (b * r) :=
    theorem_8_18_left_mem_zpowers_mul_localR (G := G) hData hbA1S hrRS
  have hconj_eq : c⁻¹ * a * c = b * r := by
    rw [hEq]
    group
  exact ⟨a, b, c, haDiff, hbA1S, hRTa, by simpa [hconj_eq] using hbPow⟩

private theorem theorem_8_18_mem_conj_zpowers_of_mem_zpowers_conj
    {G : Type u} [Group G] {a b c : G}
    (hb : b ∈ Subgroup.zpowers (c⁻¹ * a * c)) :
    c * b * c⁻¹ ∈ Subgroup.zpowers a := by
  rcases Subgroup.mem_zpowers_iff.mp hb with ⟨n, hbEq⟩
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  rw [← hbEq]
  simpa [mul_assoc] using
    (conj_zpow (i := n) (a := c) (b := c⁻¹ * a * c))

private theorem theorem_8_18_zpowers_conjBy
    {G : Type u} [Group G] (x g : G) :
    Subgroup.zpowers (g * x * g⁻¹) = (Subgroup.zpowers x).conjBy g := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, hyEq⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨x ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, ?_⟩
    rw [← hyEq]
    simpa [MulAut.conj_apply, mul_assoc] using
      (conj_zpow (i := n) (a := g) (b := x)).symm
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hzEq⟩
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← hzEq]
    simpa [MulAut.conj_apply, mul_assoc] using
      (conj_zpow (i := n) (a := g) (b := x))

private theorem theorem_8_18_zpowers_conjBy_back
    {G : Type u} [Group G] {b c z : G}
    (hz : z = c * b * c⁻¹) :
    (Subgroup.zpowers z).conjBy c⁻¹ = Subgroup.zpowers b := by
  rw [hz]
  rw [theorem_8_18_zpowers_conjBy]
  exact Subgroup.conjBy_inv (Subgroup.zpowers b) c

private theorem theorem_8_18_unique_conj_back
    {G : Type u} [Group G] [Finite G] {T : Subgroup G} {b z c : G}
    (hT : T ∈ section9MaximalSubgroups G)
    (hz : z = c * b * c⁻¹)
    (hUniqueZ :
      section9MaximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G)) = {T}) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer ({b} : Set G)) =
      {T.conjBy c⁻¹} := by
  have hUniqueZzp :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) = {T} := by
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hUniqueZ
  have hConj :=
    section16_maximalSubgroupsContaining_centralizer_conjBy
      (G := G) (X := Subgroup.zpowers z) (M := T) hT c⁻¹ hUniqueZzp
  have hZpow : (Subgroup.zpowers z).conjBy c⁻¹ = Subgroup.zpowers b :=
    theorem_8_18_zpowers_conjBy_back (G := G) hz
  have hUniqueBzp :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)) =
          {T.conjBy c⁻¹} := by
    simpa [hZpow] using hConj
  simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hUniqueBzp

private theorem theorem_8_18_section8CentralizerUnion_zpow_mem
    {G : Type u} [Group G]
    {C X : Subgroup G} {a z : G}
    (ha : a ∈ section8CentralizerUnion C X)
    (hz : z ∈ Subgroup.zpowers a)
    (hz_ne : z ≠ 1) :
    z ∈ section8CentralizerUnion C X := by
  rcases ha with ⟨x, hxX, haCentSharp⟩
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hzEq⟩
  refine ⟨x, hxX, ?_⟩
  have haCent := haCentSharp.1
  have hzC : z ∈ C := by
    rw [← hzEq]
    exact C.zpow_mem haCent.1 n
  have hzCent : z ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [← hzEq]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Commute a x :=
      Subgroup.mem_centralizer_singleton_iff.mp haCent.2
    exact (hcomm.zpow_left n).eq
  exact ⟨⟨hzC, hzCent⟩, hz_ne⟩

private theorem theorem_8_18_mem_AT_of_zpowers_diff
    {G : Type u} [Group G] [Finite G]
    {T TF TT : Subgroup G}
    {AT A0T A1T : Set G} {a z : G}
    (hT10 : notation_8_10_source_data T TF TT AT A0T A1T)
    (ha : a ∈ AT \ A1T)
    (hz : z ∈ Subgroup.zpowers a)
    (hz_ne : z ≠ 1) :
    z ∈ AT := by
  rcases hT10 with ⟨_hTmax, _hTF, _hTT, _hA1T, hCases⟩
  rcases hCases with hTypeI | hTypeP
  · rcases hTypeI with ⟨_hTypeI, hAT, _hA0T⟩
    rw [hAT] at ha ⊢
    exact theorem_8_18_section8CentralizerUnion_zpow_mem ha.1 hz hz_ne
  · rcases hTypeP with
      ⟨_U, _W1, _W2, _hP, hSourceType, hAT, _hA0T, hLate⟩
    rcases hSourceType with hTypeII | hTypeIII | hTypeIV | hTypeV
    · rw [hAT] at ha ⊢
      exact theorem_8_18_section8CentralizerUnion_zpow_mem ha.1 hz hz_ne
    · exact False.elim (ha.2 (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inl hTypeIII)).2
        simpa [hA_eq_A1] using ha.1))
    · exact False.elim (ha.2 (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inr (Or.inl hTypeIV))).2
        simpa [hA_eq_A1] using ha.1))
    · exact False.elim (ha.2 (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inr (Or.inr hTypeV))).2
        simpa [hA_eq_A1] using ha.1))

private theorem theorem_8_18_not_mem_A1_of_order_coprime
    {G : Type u} [Group G] [Finite G]
    {TT : Subgroup G} {A1T : Set G} {z : G}
    (hA1T : A1T = a1Set TT)
    (hcop : Nat.Coprime (orderOf z) (Nat.card TT))
    (hz_ne : z ≠ 1) :
    z ∉ A1T := by
  rw [hA1T, a1Set]
  intro hzA1T
  have horder_dvd : orderOf z ∣ Nat.card TT :=
    Subgroup.orderOf_dvd_natCard TT hzA1T.1
  have horder_one : orderOf z = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl horder_dvd
  exact hz_ne (orderOf_eq_one_iff.mp horder_one)

private theorem theorem_8_18_nonconj_right_conjBy
    {G : Type u} [Group G]
    {S T : Subgroup G} (k : G)
    (hNonconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) S T) :
    ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) S (T.conjBy k) := by
  rintro ⟨h, _hh, hEq⟩
  apply hNonconj
  refine ⟨k⁻¹ * h, by simp, ?_⟩
  calc
    T = (T.conjBy k).conjBy k⁻¹ := (Subgroup.conjBy_inv T k).symm
    _ = (S.conjBy h).conjBy k⁻¹ := by rw [hEq]
    _ = S.conjBy (k⁻¹ * h) := Subgroup.conjBy_conjBy S h k⁻¹

private theorem theorem_8_18_mfSubgroup_eq
    {G : Type u} [Group G] [Finite G]
    {M MF NF : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hNF : section16MFSubgroup M NF) :
    MF = NF := by
  exact le_antisymm (hNF.2 MF hMF.1) (hMF.2 NF hNF.1)

private theorem theorem_8_18_subgroupPrimeSet_conjBy
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) :
    subgroupPrimeSet (H.conjBy g) = subgroupPrimeSet H := by
  ext p
  have hcard : Nat.card (H.conjBy g) = Nat.card H := by
    simpa [Subgroup.conjBy] using
      (Subgroup.card_map_of_injective (K := H) (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective)
  simp [subgroupPrimeSet, hcard]

private theorem theorem_8_18_subgroupOf_conjBy
    {G : Type u} [Group G]
    {H M : Subgroup G} (g : G) (hHM : H ≤ M) :
    Subgroup.map ((MulAut.conj g).subgroupMap M).toMonoidHom (H.subgroupOf M) =
      (H.conjBy g).subgroupOf (M.conjBy g) := by
  apply le_antisymm
  · intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, hyEq⟩
    change ((z : M.conjBy g) : G) ∈ H.conjBy g
    rw [← hyEq]
    exact Subgroup.mem_map.mpr ⟨(y : G), hy, rfl⟩
  · intro z hz
    change ((z : M.conjBy g) : G) ∈ H.conjBy g at hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hyH, hyEq⟩
    have hyM : y ∈ M := hHM hyH
    refine Subgroup.mem_map.mpr ⟨⟨y, hyM⟩, hyH, ?_⟩
    ext
    exact hyEq

private theorem theorem_8_18_nilpotentNormalHallIn_conjBy
    {G : Type u} [Group G] [Finite G]
    {H M : Subgroup G} (g : G)
    (hH : section16NilpotentNormalHallIn H M) :
    section16NilpotentNormalHallIn (H.conjBy g) (M.conjBy g) := by
  rcases hH with ⟨hHM, hHnorm, hHnil, hHHall⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Subgroup.conjBy] using
      (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hHM)
  · let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
    have hsub :
        Subgroup.map eM.toMonoidHom (H.subgroupOf M) =
          (H.conjBy g).subgroupOf (M.conjBy g) :=
      theorem_8_18_subgroupOf_conjBy (G := G) g hHM
    have hnormMap := hHnorm.map eM.toMonoidHom eM.surjective
    rw [hsub] at hnormMap
    exact hnormMap
  · let eH : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
    letI : Group.IsNilpotent H := hHnil
    exact Group.nilpotent_of_surjective eH.toMonoidHom eH.surjective
  · let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
    have hsub :
        Subgroup.map eM.toMonoidHom (H.subgroupOf M) =
          (H.conjBy g).subgroupOf (M.conjBy g) :=
      theorem_8_18_subgroupOf_conjBy (G := G) g hHM
    have hHallMap :
        IsHallSubgroup (subgroupPrimeSet H)
          (Subgroup.map eM.toMonoidHom (H.subgroupOf M)) :=
      by
        refine isHallSubgroup_of (G := M.conjBy g) (π := subgroupPrimeSet H)
          (H := Subgroup.map eM.toMonoidHom (H.subgroupOf M)) ?_ ?_
        · intro q hq_dvd
          have hcard_map :
              Nat.card (Subgroup.map eM.toMonoidHom (H.subgroupOf M)) =
                Nat.card (H.subgroupOf M) :=
            Subgroup.card_map_of_injective (K := H.subgroupOf M)
              (f := eM.toMonoidHom) eM.injective
          exact hHHall.p_in_pi_of_p_dvd_card q (by simpa [← hcard_map] using hq_dvd)
        · intro q hq_mem hq_dvd_idx
          have hidx_map :
              (Subgroup.map eM.toMonoidHom (H.subgroupOf M)).index =
                (H.subgroupOf M).index :=
            Subgroup.index_map_equiv (H := H.subgroupOf M) eM
          exact (hHHall.p_in_pi_of_p_dvd_index q
            (by simpa [hidx_map] using hq_dvd_idx)) hq_mem
    have hPrime : subgroupPrimeSet (H.conjBy g) = subgroupPrimeSet H :=
      theorem_8_18_subgroupPrimeSet_conjBy (G := G) H g
    rw [hsub] at hHallMap
    simpa [hPrime] using hHallMap

public theorem theorem_8_18_mfSubgroup_conjBy
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G} (g : G)
    (hMF : section16MFSubgroup M MF) :
    section16MFSubgroup (M.conjBy g) (MF.conjBy g) := by
  refine ⟨theorem_8_18_nilpotentNormalHallIn_conjBy (G := G) g hMF.1, ?_⟩
  intro H hH
  have hHback : section16NilpotentNormalHallIn (H.conjBy g⁻¹) M := by
    have hback :=
      theorem_8_18_nilpotentNormalHallIn_conjBy (G := G) g⁻¹ hH
    simpa [Subgroup.conjBy_inv] using hback
  have hleBack : H.conjBy g⁻¹ ≤ MF := hMF.2 (H.conjBy g⁻¹) hHback
  intro x hxH
  have hxBack : g⁻¹ * x * g ∈ H.conjBy g⁻¹ :=
    Subgroup.mem_map.mpr ⟨x, hxH, by simp [mul_assoc]⟩
  have hxMF : g⁻¹ * x * g ∈ MF := hleBack hxBack
  exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hxMF, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem theorem_8_18_ambientDerivedSubgroup_conjBy
    {G : Type u} [Group G]
    (H : Subgroup G) (g : G) :
    ambientDerivedSubgroup (H.conjBy g) = (ambientDerivedSubgroup H).conjBy g := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    let e : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
    have hmap : (derivedSubgroup H).map e.toMonoidHom =
        derivedSubgroup (H.conjBy g) := by
      change (derivedSeries H 1).map e.toMonoidHom =
        derivedSeries (H.conjBy g) 1
      exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1
    have hy' : y ∈ (derivedSubgroup H).map e.toMonoidHom := hmap.symm ▸ hy
    rcases Subgroup.mem_map.mp hy' with ⟨z, hz, hzy⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(z : H), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem H.subtype hz
    · rw [← hyx, ← hzy]
      rfl
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    let e : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
    have hmap : (derivedSubgroup H).map e.toMonoidHom =
        derivedSubgroup (H.conjBy g) := by
      change (derivedSeries H 1).map e.toMonoidHom =
        derivedSeries (H.conjBy g) 1
      exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1
    refine Subgroup.mem_map.mpr ?_
    refine ⟨e z, ?_, ?_⟩
    · exact hmap ▸ Subgroup.mem_map_of_mem e.toMonoidHom hz
    · rw [← hyx, ← hzy]
      rfl

private theorem theorem_8_18_section12ComplementIn_conjBy
    {G : Type u} [Group G]
    {H K L : Subgroup G} (g : G)
    (hcomp : section12ComplementIn H K L) :
    section12ComplementIn (H.conjBy g) (K.conjBy g) (L.conjBy g) := by
  rcases hcomp with ⟨hKH, hLH, hH, hDis⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKH
  · simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hLH
  · calc
      H.conjBy g = (K ⊔ L).conjBy g := by rw [hH]
      _ = K.conjBy g ⊔ L.conjBy g := by
        simpa [Subgroup.conjBy] using
          (Subgroup.map_sup K L (MulAut.conj g).toMonoidHom)
  · rw [disjoint_iff] at hDis ⊢
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxK, hxL⟩
      rcases Subgroup.mem_map.mp hxK with ⟨k, hkK, hkx⟩
      rcases Subgroup.mem_map.mp hxL with ⟨l, hlL, hlx⟩
      have hk_eq_l : k = l := by
        have hconj_eq : g * k * g⁻¹ = g * l * g⁻¹ := by
          simpa [MulAut.conj_apply] using hkx.trans hlx.symm
        have hback := congrArg (fun z : G => g⁻¹ * z * g) hconj_eq
        simpa [mul_assoc] using hback
      have hk_bot : k ∈ (⊥ : Subgroup G) := by
        have hk_inter : k ∈ K ⊓ L := ⟨hkK, by simpa [hk_eq_l] using hlL⟩
        simpa [hDis] using hk_inter
      have hk_one : k = 1 := by simpa using hk_bot
      rw [← hkx]
      simp [MulAut.conj_apply, hk_one]
    · intro x hx
      have hx_one : x = 1 := by simpa using hx
      simp [hx_one]

private theorem theorem_8_18_section10NormalIn_conjBy
    {G : Type u} [Group G]
    {K L : Subgroup G} (g : G)
    (hNorm : section10NormalIn K L) :
    section10NormalIn (K.conjBy g) (L.conjBy g) := by
  rcases hNorm with ⟨hKL, hNormal⟩
  refine ⟨?_, ?_⟩
  · simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hKL
  · let eL : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
    have hsub :
        Subgroup.map eL.toMonoidHom (K.subgroupOf L) =
          (K.conjBy g).subgroupOf (L.conjBy g) :=
      theorem_8_18_subgroupOf_conjBy (G := G) g hKL
    have hmap := hNormal.map eL.toMonoidHom eL.surjective
    rwa [hsub] at hmap

private theorem theorem_8_18_elementCentralizerIn_conjBy
    {G : Type u} [Group G]
    (H : Subgroup G) (x g : G) :
    elementCentralizerIn (H.conjBy g) (g * x * g⁻¹) =
      (elementCentralizerIn H x).conjBy g := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyH, hyCent⟩
    rcases Subgroup.mem_map.mp hyH with ⟨z, hzH, hzy⟩
    refine Subgroup.mem_map.mpr ⟨z, ?_, ?_⟩
    · refine ⟨hzH, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hzy' : g * z * g⁻¹ = y := by
        simpa [MulAut.conj_apply] using hzy
      have hcent : y * (g * x * g⁻¹) = (g * x * g⁻¹) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCent
      have hback := congrArg (fun t : G => g⁻¹ * t * g) hcent
      simpa [← hzy', mul_assoc] using hback
    · exact hzy
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    rcases hz with ⟨hzH, hzCent⟩
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨z, hzH, hzy⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hzy' : g * z * g⁻¹ = y := by
        simpa [MulAut.conj_apply] using hzy
      have hcent : z * x = x * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hzCent
      calc
        y * (g * x * g⁻¹) = (g * z * g⁻¹) * (g * x * g⁻¹) := by rw [hzy']
        _ = g * (z * x) * g⁻¹ := by group
        _ = g * (x * z) * g⁻¹ := by rw [hcent]
        _ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * x * g⁻¹) * y := by rw [hzy']

private theorem theorem_8_18_isFrobeniusGroupWithKernelComplement_map_mulEquiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) {K R : Subgroup A}
    (hFrob : IsFrobeniusGroupWithKernelComplement K R) :
    IsFrobeniusGroupWithKernelComplement
      (K.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  classical
  rcases hFrob with ⟨hKnorm, hComp, hDisj, hKne, hRne⟩
  have hKmap_ne : K.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hKne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := K) (f := e.toMonoidHom) e.injective).1 hbot)
  have hRmap_ne : R.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hRne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := R) (f := e.toMonoidHom) e.injective).1 hbot)
  have hKmap_norm : (K.map e.toMonoidHom).Normal :=
    hKnorm.map e.toMonoidHom e.surjective
  have hCompMap :
      (K.map e.toMonoidHom).IsComplement' (R.map e.toMonoidHom) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxR
      rcases Subgroup.mem_map.mp hxK with ⟨k, hkK, hkx⟩
      rcases Subgroup.mem_map.mp hxR with ⟨r, hrR, hrx⟩
      have hkr : k = r := e.injective (hkx.trans hrx.symm)
      have hkbot : k ∈ (⊥ : Subgroup A) :=
        hComp.disjoint.le_bot ⟨hkK, by simpa [hkr] using hrR⟩
      have hxone : x = 1 := by
        rw [← hkx]
        simpa using congrArg e hkbot
      simp [hxone]
    · rw [Set.eq_univ_iff_forall]
      intro b
      let a : A := e.symm b
      rcases hComp.2 a with ⟨kr, hkr⟩
      rcases kr with ⟨k, r⟩
      rcases k with ⟨k, hkK⟩
      rcases r with ⟨r, hrR⟩
      refine ⟨e k, Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩,
        e r, Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩, ?_⟩
      calc
        e k * e r = e (k * r) := (e.map_mul k r).symm
        _ = e a := by
          have hkrA : k * r = a := by
            simpa using hkr
          rw [hkrA]
        _ = b := e.apply_symm_apply b
  refine (lemma_3_1 (K.map e.toMonoidHom) (R.map e.toMonoidHom)
    hKmap_ne hRmap_ne hKmap_norm hCompMap).mpr ?_
  intro x hxne
  rcases x.property with ⟨r, hrR, hrx⟩
  let rSub : R := ⟨r, hrR⟩
  have hrne : rSub ≠ 1 := by
    intro hrone
    apply hxne
    apply Subtype.ext
    rw [← hrx]
    have hrA : r = 1 := by
      exact congrArg (fun x : R => (x : A)) hrone
    simp [hrA]
  have hcentral :=
    (lemma_3_1 K R hKne hRne hKnorm hComp).mp
      ⟨hKnorm, hComp, hDisj, hKne, hRne⟩ rSub hrne
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyK, hyCent⟩
  rcases Subgroup.mem_map.mp hyK with ⟨k, hkK, hky⟩
  have hkCent : k ∈ elementCentralizerIn K (r : A) := by
    refine ⟨hkK, ?_⟩
    change k ∈ Subgroup.centralizer ({r} : Set A)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    have hcommB : y * (x : B) = (x : B) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyCent
    rw [← hky, ← hrx] at hcommB
    simpa using hcommB
  have hkbot : k ∈ (⊥ : Subgroup A) := by
    rw [← hcentral]
    exact hkCent
  have hkone : k = 1 := by
    simpa using hkbot
  rw [← hky, hkone]
  simp

private theorem theorem_8_18_section12FrobeniusJoinWithKernel_conjBy
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G} (g : G)
    (hFrob : section12FrobeniusJoinWithKernel K R) :
    section12FrobeniusJoinWithKernel (K.conjBy g) (R.conjBy g) := by
  let S : Subgroup G := K ⊔ R
  let eS : S ≃* S.conjBy g := (MulAut.conj g).subgroupMap S
  have hFrobS :
      IsFrobeniusGroupWithKernelComplement
        (K.subgroupOf S) (R.subgroupOf S) := by
    simpa [section12FrobeniusJoinWithKernel, S] using hFrob
  have hmap :
      IsFrobeniusGroupWithKernelComplement
        ((K.subgroupOf S).map eS.toMonoidHom)
        ((R.subgroupOf S).map eS.toMonoidHom) :=
    theorem_8_18_isFrobeniusGroupWithKernelComplement_map_mulEquiv
      (e := eS) hFrobS
  have hKmap :
      (K.subgroupOf S).map eS.toMonoidHom =
        (K.conjBy g).subgroupOf (S.conjBy g) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
      change ((x : S.conjBy g) : G) ∈ K.conjBy g
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(k : S), ?_, ?_⟩
      · exact hkK
      · change g * ((k : S) : G) * g⁻¹ = (x : G)
        have hkxG := congrArg Subtype.val hkx
        change g * ((k : S) : G) * g⁻¹ = (x : G) at hkxG
        exact hkxG
    · intro hx
      change ((x : S.conjBy g) : G) ∈ K.conjBy g at hx
      rcases Subgroup.mem_map.mp hx with ⟨k, hkK, hkx⟩
      refine Subgroup.mem_map.mpr ⟨⟨k, ?_⟩, hkK, ?_⟩
      · exact (le_sup_left : K ≤ K ⊔ R) hkK
      · apply Subtype.ext
        change g * k * g⁻¹ = (x : G)
        exact hkx
  have hRmap :
      (R.subgroupOf S).map eS.toMonoidHom =
        (R.conjBy g).subgroupOf (S.conjBy g) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨r, hrR, hrx⟩
      change ((x : S.conjBy g) : G) ∈ R.conjBy g
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(r : S), ?_, ?_⟩
      · exact hrR
      · change g * ((r : S) : G) * g⁻¹ = (x : G)
        have hrxG := congrArg Subtype.val hrx
        change g * ((r : S) : G) * g⁻¹ = (x : G) at hrxG
        exact hrxG
    · intro hx
      change ((x : S.conjBy g) : G) ∈ R.conjBy g at hx
      rcases Subgroup.mem_map.mp hx with ⟨r, hrR, hrx⟩
      refine Subgroup.mem_map.mpr ⟨⟨r, ?_⟩, hrR, ?_⟩
      · exact (le_sup_right : R ≤ K ⊔ R) hrR
      · apply Subtype.ext
        change g * r * g⁻¹ = (x : G)
        exact hrx
  have hSconj : S.conjBy g = K.conjBy g ⊔ R.conjBy g := by
    simpa [S, Subgroup.conjBy] using
      (Subgroup.map_sup (f := (MulAut.conj g).toMonoidHom) K R)
  rw [section12FrobeniusJoinWithKernel]
  rw [← hSconj]
  rw [hKmap, hRmap] at hmap
  exact hmap

private theorem theorem_8_18_section16NonidentityElements_conjBy
    {G : Type u} [Group G]
    (H : Subgroup G) (g : G) :
    section16NonidentityElements (H.conjBy g : Set G) =
      section16ConjugateSet (section16NonidentityElements (H : Set G)) g := by
  ext y
  constructor
  · rintro ⟨hyH, hyne⟩
    rcases Subgroup.mem_map.mp hyH with ⟨x, hxH, rfl⟩
    refine ⟨x, ⟨hxH, ?_⟩, rfl⟩
    intro hx
    exact hyne (by simp [hx])
  · rintro ⟨x, ⟨hxH, hxne⟩, rfl⟩
    refine ⟨Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩, ?_⟩
    intro hx
    apply hxne
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by simp [hx]

private theorem theorem_8_18_section16TISubset_conj_back
    {G : Type u} [Group G]
    {X : Set G} (g : G)
    (hTI : section16TISubset (section16ConjugateSet X g)) :
    section16TISubset X := by
  intro a
  rcases hTI (g * a * g⁻¹) with hEq | hSub
  · left
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, hxy⟩
      have hgy : g * y * g⁻¹ ∈
          section16ConjugateSet (section16ConjugateSet X g) (g * a * g⁻¹) := by
        refine ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, ?_⟩
        rw [hxy]
        group
      have hgy' : g * y * g⁻¹ ∈ section16ConjugateSet X g := by
        simpa [hEq] using hgy
      rcases hgy' with ⟨z, hz, hzy⟩
      have hyz : y = z := by
        calc
          y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = z := by rw [hzy]; group
      simpa [hyz] using hz
    · intro hy
      have hgy : g * y * g⁻¹ ∈ section16ConjugateSet X g :=
        ⟨y, hy, rfl⟩
      have hgy' : g * y * g⁻¹ ∈
          section16ConjugateSet (section16ConjugateSet X g) (g * a * g⁻¹) := by
        simpa [hEq] using hgy
      rcases hgy' with ⟨z, hz, hzy⟩
      rcases hz with ⟨x, hx, hxz⟩
      refine ⟨x, hx, ?_⟩
      calc
        y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = a * x * a⁻¹ := by rw [hzy, hxz]; group
  · right
    intro y hy
    have hgy_left : g * y * g⁻¹ ∈ section16ConjugateSet X g :=
      ⟨y, hy.1, rfl⟩
    have hgy_right : g * y * g⁻¹ ∈
        section16ConjugateSet (section16ConjugateSet X g) (g * a * g⁻¹) := by
      rcases hy.2 with ⟨x, hx, hxy⟩
      refine ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, ?_⟩
      rw [hxy]
      group
    have hgy_one : g * y * g⁻¹ ∈ ({1} : Set G) :=
      hSub ⟨hgy_left, hgy_right⟩
    simp only [Set.mem_singleton_iff] at hgy_one ⊢
    calc
      y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by simp [hgy_one]

private theorem theorem_8_18_section10PPrimeCore_isCyclic_conj_back
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) (p : Nat.Primes)
    (hCyc : IsCyclic (section10PPrimeCore p (H.conjBy g))) :
    IsCyclic (section10PPrimeCore p H) := by
  let eH : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
  have hcomp :
      (H.conjBy g).subtype.comp eH.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  have hcore :
      section10PPrimeCore p (H.conjBy g) =
        (section10PPrimeCore p H).conjBy g := by
    have hraw :=
      piCore_map_iso (π := section10PPrimeSet p)
        (G := H) (G' := H.conjBy g) eH
    have hraw' :=
      congrArg
        (fun K : Subgroup (H.conjBy g) => K.map (H.conjBy g).subtype)
        hraw.symm
    rw [Subgroup.map_map, hcomp] at hraw'
    simpa only [section10PPrimeCore, piCoreIn, Subgroup.conjBy,
      Subgroup.map_map] using hraw'
  have hCycMap : IsCyclic ((section10PPrimeCore p H).conjBy g) := by
    exact hcore ▸ hCyc
  let eCore : section10PPrimeCore p H ≃*
      (section10PPrimeCore p H).conjBy g :=
    (MulAut.conj g).subgroupMap (section10PPrimeCore p H)
  exact eCore.isCyclic.2 hCycMap

private theorem theorem_8_18_fittingSubgroup_map_mulEquiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm
  · refine le_sSup ?_
    constructor
    · exact (show (fittingSubgroup A).Normal from inferInstance).map
        e.toMonoidHom e.surjective
    · haveI : Group.IsNilpotent (fittingSubgroup A) := inferInstance
      exact Group.nilpotent_of_mulEquiv (e.subgroupMap (fittingSubgroup A))
  · have hpre :
        (fittingSubgroup B).map e.symm.toMonoidHom ≤ fittingSubgroup A := by
      refine le_sSup ?_
      constructor
      · exact (show (fittingSubgroup B).Normal from inferInstance).map
          e.symm.toMonoidHom e.symm.surjective
      · haveI : Group.IsNilpotent (fittingSubgroup B) := inferInstance
        exact Group.nilpotent_of_mulEquiv
          (e.symm.subgroupMap (fittingSubgroup B))
    intro b hb
    refine Subgroup.mem_map.mpr ?_
    refine ⟨e.symm b, hpre ?_, by simp⟩
    exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩

private theorem theorem_8_18_section8FittingSubgroup_conjBy
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) :
    section8FittingSubgroup (H.conjBy g) =
      (section8FittingSubgroup H).conjBy g := by
  let eH : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
  have hcomp :
      (H.conjBy g).subtype.comp eH.toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  have hmap :
      (fittingSubgroup H).map eH.toMonoidHom =
        fittingSubgroup (H.conjBy g) :=
    theorem_8_18_fittingSubgroup_map_mulEquiv eH
  have hmapG :=
    congrArg
      (fun K : Subgroup (H.conjBy g) => K.map (H.conjBy g).subtype)
      hmap.symm
  rw [Subgroup.map_map, hcomp] at hmapG
  simpa only [section8FittingSubgroup, fittingSubgroupOf, Subgroup.conjBy,
    Subgroup.map_map] using hmapG

private theorem theorem_8_18_section16SecondDerivedSubgroup_conjBy
    {G : Type u} [Group G]
    (H : Subgroup G) (g : G) :
    section16SecondDerivedSubgroup (H.conjBy g) =
      (section16SecondDerivedSubgroup H).conjBy g := by
  rw [section16SecondDerivedSubgroup]
  calc
    ambientDerivedSubgroup (ambientDerivedSubgroup (H.conjBy g)) =
        ambientDerivedSubgroup ((ambientDerivedSubgroup H).conjBy g) := by
      rw [theorem_8_18_ambientDerivedSubgroup_conjBy (G := G) H g]
    _ = (ambientDerivedSubgroup (ambientDerivedSubgroup H)).conjBy g :=
      theorem_8_18_ambientDerivedSubgroup_conjBy (G := G)
        (ambientDerivedSubgroup H) g

private theorem theorem_8_18_section16ConjugateSet_subgroup
    {G : Type u} [Group G]
    (H : Subgroup G) (g : G) :
    section16ConjugateSet (H : Set G) g = (H.conjBy g : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hxH, rfl⟩
    exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxH, hxy⟩
    exact ⟨x, hxH, by simpa [MulAut.conj_apply] using hxy.symm⟩

private theorem theorem_8_18_normalizer_section16ConjugateSet
    {G : Type u} [Group G]
    (X : Set G) (g : G) :
    Subgroup.normalizer (section16ConjugateSet X g) =
      (Subgroup.normalizer X).conjBy g := by
  ext y
  constructor
  · intro hy
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g⁻¹ * y * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    change ∀ x, x ∈ X ↔ (g⁻¹ * y * g) * x * (g⁻¹ * y * g)⁻¹ ∈ X
    intro x
    constructor
    · intro hx
      have hxConj : g * x * g⁻¹ ∈ section16ConjugateSet X g :=
        ⟨x, hx, rfl⟩
      have hyConj :
          y * (g * x * g⁻¹) * y⁻¹ ∈ section16ConjugateSet X g :=
        (hy (g * x * g⁻¹)).1 hxConj
      rcases hyConj with ⟨z, hzX, hzEq⟩
      have htarget :
          (g⁻¹ * y * g) * x * (g⁻¹ * y * g)⁻¹ = z := by
        calc
          (g⁻¹ * y * g) * x * (g⁻¹ * y * g)⁻¹ =
              g⁻¹ * (y * (g * x * g⁻¹) * y⁻¹) * g := by group
            _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hzEq]
            _ = z := by group
      exact htarget.symm ▸ hzX
    · intro hx
      have hxConj :
          y * (g * x * g⁻¹) * y⁻¹ ∈ section16ConjugateSet X g := by
        refine ⟨(g⁻¹ * y * g) * x * (g⁻¹ * y * g)⁻¹, hx, ?_⟩
        group
      have hxBack :
          g * x * g⁻¹ ∈ section16ConjugateSet X g :=
        (hy (g * x * g⁻¹)).2 hxConj
      rcases hxBack with ⟨z, hzX, hzEq⟩
      have hxz : x = z := by
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hzEq]
          _ = z := by group
      simpa [hxz] using hzX
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨n, hn, hny⟩
    have hny' : y = g * n * g⁻¹ := by
      simpa [MulAut.conj_apply] using hny.symm
    change ∀ z, z ∈ section16ConjugateSet X g ↔
      y * z * y⁻¹ ∈ section16ConjugateSet X g
    intro z
    constructor
    · rintro ⟨x, hxX, rfl⟩
      refine ⟨n * x * n⁻¹, ?_, ?_⟩
      · exact (hn x).1 hxX
      · rw [hny']
        group
    · rintro ⟨x, hxX, hxz⟩
      refine ⟨n⁻¹ * x * n, ?_, ?_⟩
      · exact (hn (n⁻¹ * x * n)).2 (by
          simpa [mul_assoc] using hxX)
      · rw [hny'] at hxz
        have hback := congrArg
          (fun t : G => (g * n * g⁻¹)⁻¹ * t * (g * n * g⁻¹)) hxz
        simpa [mul_assoc] using hback

private theorem theorem_8_18_section16HatW_conjBy
    {G : Type u} [Group G]
    (W1 W2 : Subgroup G) (g : G) :
    section16ConjugateSet (section16HatW W1 W2) g =
      section16HatW (W1.conjBy g) (W2.conjBy g) := by
  ext y
  constructor
  · rintro ⟨x, hxHat, rfl⟩
    rcases hxHat with ⟨hxSup, hxNot⟩
    constructor
    · have hxMap : g * x * g⁻¹ ∈ (W1 ⊔ W2).conjBy g :=
        Subgroup.mem_map.mpr ⟨x, hxSup, rfl⟩
      have hSup : (W1 ⊔ W2).conjBy g = W1.conjBy g ⊔ W2.conjBy g := by
        simpa [Subgroup.conjBy] using
          (Subgroup.map_sup W1 W2 (MulAut.conj g).toMonoidHom)
      simpa [section16HatW, hSup] using hxMap
    · intro hyUnion
      rcases hyUnion with hyW1 | hyW2
      · rcases Subgroup.mem_map.mp hyW1 with ⟨w, hw, hwEq⟩
        apply hxNot
        left
        have hcancel :
            g⁻¹ * (g * x * g⁻¹) * g =
              g⁻¹ * (g * w * g⁻¹) * g := by
          simpa [MulAut.conj_apply] using hwEq.symm
        have hxw : x = w := by simpa [mul_assoc] using hcancel
        simpa [hxw] using hw
      · rcases Subgroup.mem_map.mp hyW2 with ⟨w, hw, hwEq⟩
        apply hxNot
        right
        have hcancel :
            g⁻¹ * (g * x * g⁻¹) * g =
              g⁻¹ * (g * w * g⁻¹) * g := by
          simpa [MulAut.conj_apply] using hwEq.symm
        have hxw : x = w := by simpa [mul_assoc] using hcancel
        simpa [hxw] using hw
  · intro hyHat
    rcases hyHat with ⟨hySup, hyNot⟩
    have hSup : (W1 ⊔ W2).conjBy g = W1.conjBy g ⊔ W2.conjBy g := by
      simpa [Subgroup.conjBy] using
        (Subgroup.map_sup W1 W2 (MulAut.conj g).toMonoidHom)
    have hySup' : y ∈ (W1 ⊔ W2).conjBy g := by
      simpa [section16HatW, hSup] using hySup
    rcases Subgroup.mem_map.mp hySup' with ⟨x, hxSup, hxEq⟩
    refine ⟨x, ?_, by simpa [MulAut.conj_apply] using hxEq.symm⟩
    constructor
    · exact hxSup
    · intro hxUnion
      apply hyNot
      rcases hxUnion with hxW1 | hxW2
      · left
        exact Subgroup.mem_map.mpr ⟨x, hxW1, hxEq⟩
      · right
        exact Subgroup.mem_map.mpr ⟨x, hxW2, hxEq⟩

private theorem theorem_8_18_section16HallSubgroupOf_conjBy
    {G : Type u} [Group G] [Finite G]
    {H M : Subgroup G} (g : G)
    (hHall : section16HallSubgroupOf H M) :
    section16HallSubgroupOf (H.conjBy g) (M.conjBy g) := by
  rcases hHall with ⟨hHM, hHallHM⟩
  refine ⟨?_, ?_⟩
  · simpa [Subgroup.conjBy] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hHM
  · let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
    have hsub :
        Subgroup.map eM.toMonoidHom (H.subgroupOf M) =
          (H.conjBy g).subgroupOf (M.conjBy g) :=
      theorem_8_18_subgroupOf_conjBy (G := G) g hHM
    have hHallMap :
        IsHallSubgroup (subgroupPrimeSet H)
          (Subgroup.map eM.toMonoidHom (H.subgroupOf M)) :=
      by
        refine isHallSubgroup_of (G := M.conjBy g) (π := subgroupPrimeSet H)
          (H := Subgroup.map eM.toMonoidHom (H.subgroupOf M)) ?_ ?_
        · intro q hq_dvd
          have hcard_map :
              Nat.card (Subgroup.map eM.toMonoidHom (H.subgroupOf M)) =
                Nat.card (H.subgroupOf M) :=
            Subgroup.card_map_of_injective (K := H.subgroupOf M)
              (f := eM.toMonoidHom) eM.injective
          exact hHallHM.p_in_pi_of_p_dvd_card q
            (by simpa [← hcard_map] using hq_dvd)
        · intro q hq_mem hq_dvd_idx
          have hidx_map :
              (Subgroup.map eM.toMonoidHom (H.subgroupOf M)).index =
                (H.subgroupOf M).index :=
            Subgroup.index_map_equiv (H := H.subgroupOf M) eM
          exact (hHallHM.p_in_pi_of_p_dvd_index q
            (by simpa [hidx_map] using hq_dvd_idx)) hq_mem
    have hPrime : subgroupPrimeSet (H.conjBy g) = subgroupPrimeSet H :=
      theorem_8_18_subgroupPrimeSet_conjBy (G := G) H g
    rw [hsub] at hHallMap
    simpa [hPrime] using hHallMap

private theorem theorem_8_18_section16HasPrimeOrder_conjBy
    {G : Type u} [Group G] [Finite G]
    {A : Subgroup G} (g : G)
    (hA : section16HasPrimeOrder A) :
    section16HasPrimeOrder (A.conjBy g) := by
  rcases hA with ⟨p, hcardA⟩
  exact ⟨p, by simpa [section11_card_conjBy (G := G) A g] using hcardA⟩


public theorem theorem_8_18_typeFData_conj_back
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G} (g : G)
    (hF : typeFData (M.conjBy g) (MF.conjBy g) U U1 U0) :
    typeFData M MF
      (U.conjBy g⁻¹) (U1.conjBy g⁻¹) (U0.conjBy g⁻¹) := by
  classical
  rcases hF with
    ⟨hSolv, hOdd, hMFg, hMFposg, hMFltg, hUne, hComp, hU1le,
      hU1comm, hU1norm, hCent, hU0le, hExp, hFrob⟩
  have hMF : section16MFSubgroup M MF := by
    have hback := theorem_8_18_mfSubgroup_conjBy (G := G) g⁻¹ hMFg
    simpa [Subgroup.conjBy_inv] using hback
  refine ⟨?_, ?_, hMF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
    let : Group.IsSolvable (M.conjBy g) := hSolv
    exact Group.isSolvable_of_surjective (f := eM.symm.toMonoidHom) eM.symm.surjective
  · have hcard : Nat.card (M.conjBy g) = Nat.card M :=
      section11_card_conjBy (G := G) M g
    simpa [hcard] using hOdd
  · refine bot_lt_iff_ne_bot.2 ?_
    intro hbot
    exact (ne_of_gt hMFposg) (by simp [hbot, Subgroup.conjBy])
  · rcases hMF.1 with ⟨hMFM, _hNorm, _hNil, _hHall⟩
    refine lt_of_le_of_ne hMFM ?_
    intro hEq
    exact (ne_of_gt hMFltg) (by simp [hEq])
  · exact section12_conjBy_ne_bot hUne g⁻¹
  · have hCompBack :=
      theorem_8_18_section12ComplementIn_conjBy (G := G) g⁻¹ hComp
    simpa [Subgroup.conjBy_inv] using hCompBack
  · exact Subgroup.map_mono hU1le
  · letI : IsMulCommutative U1 := hU1comm
    change IsMulCommutative
      (U1.map (MulAut.conj g⁻¹).toMonoidHom)
    exact Subgroup.map_isMulCommutative
      (f := (MulAut.conj g⁻¹).toMonoidHom) (H := U1)
  · have hNormBack :=
      theorem_8_18_section10NormalIn_conjBy (G := G) g⁻¹ hU1norm
    simpa [Subgroup.conjBy_inv] using hNormBack
  · intro x hxMF hxne z hz
    have hxMFg : g * x * g⁻¹ ∈ MF.conjBy g :=
      Subgroup.mem_map.mpr ⟨x, hxMF, rfl⟩
    have hxne_g : g * x * g⁻¹ ≠ 1 := by
      intro hxone
      apply hxne
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by simp [hxone]
    have hzConj :
        g * z * g⁻¹ ∈ elementCentralizerIn U (g * x * g⁻¹) := by
      have hzMap :
          g * z * g⁻¹ ∈
            (elementCentralizerIn (U.conjBy g⁻¹) x).conjBy g :=
        Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      have hCentEq :
          elementCentralizerIn U (g * x * g⁻¹) =
            (elementCentralizerIn (U.conjBy g⁻¹) x).conjBy g := by
        have hUback : (U.conjBy g⁻¹).conjBy g = U := by
          simpa using (Subgroup.conjBy_inv U g⁻¹)
        simpa [hUback] using
          (theorem_8_18_elementCentralizerIn_conjBy
            (G := G) (H := U.conjBy g⁻¹) (x := x) (g := g))
      simpa [hCentEq] using hzMap
    have hzU1 : g * z * g⁻¹ ∈ U1 :=
      hCent (g * x * g⁻¹) hxMFg hxne_g hzConj
    exact Subgroup.mem_map.mpr ⟨g * z * g⁻¹, hzU1, by simp [mul_assoc]⟩
  · exact Subgroup.map_mono hU0le
  · let eU0 : U0 ≃* U0.conjBy g⁻¹ := (MulAut.conj g⁻¹).subgroupMap U0
    let eU : U ≃* U.conjBy g⁻¹ := (MulAut.conj g⁻¹).subgroupMap U
    have hU0exp :
        Monoid.exponent (U0.conjBy g⁻¹) = Monoid.exponent U0 := by
      simpa using (Monoid.exponent_eq_of_mulEquiv eU0).symm
    have hUexp :
        Monoid.exponent (U.conjBy g⁻¹) = Monoid.exponent U := by
      simpa using (Monoid.exponent_eq_of_mulEquiv eU).symm
    rw [hU0exp, hUexp, hExp]
  · have hFrobBack :
        section12FrobeniusJoinWithKernel
          ((MF.conjBy g).conjBy g⁻¹) (U0.conjBy g⁻¹) := by
      exact theorem_8_18_section12FrobeniusJoinWithKernel_conjBy
        (G := G) g⁻¹ hFrob
    simpa [Subgroup.conjBy_inv] using hFrobBack

public theorem theorem_8_18_typePDefinitionData_conj_back
    {G : Type u} [Group G] [Finite G]
    {M MF LF U W1 W2 : Subgroup G} (g : G)
    (hMF : section16MFSubgroup M MF)
    (hLF : section16MFSubgroup (M.conjBy g) LF)
    (hP : typePDefinitionData (M.conjBy g) LF U W1 W2) :
    typePDefinitionData M MF
      (U.conjBy g⁻¹) (W1.conjBy g⁻¹) (W2.conjBy g⁻¹) := by
  classical
  have hMFg : section16MFSubgroup (M.conjBy g) (MF.conjBy g) :=
    theorem_8_18_mfSubgroup_conjBy (G := G) g hMF
  have hLF_eq : LF = MF.conjBy g :=
    theorem_8_18_mfSubgroup_eq (G := G) hLF hMFg
  subst LF
  rcases hP with
    ⟨_hMFg, hW1cyc, hW1ne, hW1Hall, hW1Comp, hUleD, hUnil,
      hW1norm, hCompDU, hMFnotCyclic, hSecondLe, hFitEq, hFitLeD,
      hW2le, hW2cyc, hW2ne, hCent, hHat⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDg : ambientDerivedSubgroup (M.conjBy g) = D.conjBy g := by
    simpa [D] using theorem_8_18_ambientDerivedSubgroup_conjBy (G := G) M g
  have hMback : (M.conjBy g).conjBy g⁻¹ = M :=
    section11_conjBy_inv (G := G) M g
  have hMFback : (MF.conjBy g).conjBy g⁻¹ = MF :=
    section11_conjBy_inv (G := G) MF g
  have hDback : (ambientDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ = D := by
    rw [hDg]
    exact section11_conjBy_inv (G := G) D g
  have hSecondBack :
      (section16SecondDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ =
        section16SecondDerivedSubgroup M := by
    rw [theorem_8_18_section16SecondDerivedSubgroup_conjBy (G := G) M g]
    exact section11_conjBy_inv (G := G)
      (section16SecondDerivedSubgroup M) g
  have hCentBack :
      (subgroupCentralizerIn (M.conjBy g) (MF.conjBy g)).conjBy g⁻¹ =
        subgroupCentralizerIn M MF := by
    rw [section11_subgroupCentralizerIn_conjBy (G := G) M MF g]
    exact section11_conjBy_inv (G := G) (subgroupCentralizerIn M MF) g
  have hFitBack :
      (section8FittingSubgroup (M.conjBy g)).conjBy g⁻¹ =
        section8FittingSubgroup M := by
    rw [theorem_8_18_section8FittingSubgroup_conjBy (G := G) M g]
    exact section11_conjBy_inv (G := G) (section8FittingSubgroup M) g
  have hMFcentBack :
      ((MF.conjBy g) ⊔
          subgroupCentralizerIn (M.conjBy g) (MF.conjBy g)).conjBy g⁻¹ =
        MF ⊔ subgroupCentralizerIn M MF := by
    calc
      ((MF.conjBy g) ⊔ subgroupCentralizerIn (M.conjBy g) (MF.conjBy g)).conjBy g⁻¹ =
          (MF.conjBy g).conjBy g⁻¹ ⊔
            (subgroupCentralizerIn (M.conjBy g) (MF.conjBy g)).conjBy g⁻¹ := by
        simpa [Subgroup.conjBy] using
          (Subgroup.map_sup (MF.conjBy g)
            (subgroupCentralizerIn (M.conjBy g) (MF.conjBy g))
            (MulAut.conj g⁻¹).toMonoidHom)
      _ = MF ⊔ subgroupCentralizerIn M MF := by
        rw [hMFback, hCentBack]
  have hMFSecondBack :
      ((MF.conjBy g) ⊓
          section16SecondDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ =
        MF ⊓ section16SecondDerivedSubgroup M := by
    calc
      ((MF.conjBy g) ⊓ section16SecondDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ =
          (MF.conjBy g).conjBy g⁻¹ ⊓
            (section16SecondDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ := by
        simpa [Subgroup.conjBy] using
          (Subgroup.map_inf (MF.conjBy g)
            (section16SecondDerivedSubgroup (M.conjBy g))
            (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)
      _ = MF ⊓ section16SecondDerivedSubgroup M := by
        rw [hMFback, hSecondBack]
  refine ⟨hMF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let eW1g : W1.conjBy g⁻¹ ≃* (W1.conjBy g⁻¹).conjBy g :=
      (MulAut.conj g).subgroupMap (W1.conjBy g⁻¹)
    let eW1 : W1.conjBy g⁻¹ ≃* W1 :=
      eW1g.trans (MulEquiv.subgroupCongr (by
        simpa using (Subgroup.conjBy_inv W1 g⁻¹)))
    exact eW1.isCyclic.2 hW1cyc
  · exact section12_conjBy_ne_bot hW1ne g⁻¹
  · have hHallBack :=
      theorem_8_18_section16HallSubgroupOf_conjBy (G := G) g⁻¹ hW1Hall
    simpa [Subgroup.conjBy_inv] using hHallBack
  · have hComp' :
        section12ComplementIn (M.conjBy g) (D.conjBy g) W1 := by
      simpa [hDg] using hW1Comp
    have hBack := theorem_8_18_section12ComplementIn_conjBy (G := G) g⁻¹ hComp'
    simpa [D, Subgroup.conjBy_inv] using hBack
  · have hBack := Subgroup.map_mono
      (f := (MulAut.conj g⁻¹).toMonoidHom) hUleD
    have hBack' :
        U.conjBy g⁻¹ ≤
          (ambientDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using hBack
    simpa [hDback] using hBack'
  · let eU : U ≃* U.conjBy g⁻¹ := (MulAut.conj g⁻¹).subgroupMap U
    letI : Group.IsNilpotent U := hUnil
    exact Group.nilpotent_of_surjective eU.toMonoidHom eU.surjective
  · have hBack := Subgroup.map_mono
      (f := (MulAut.conj g⁻¹).toMonoidHom) hW1norm
    have hEq :=
      section12_subgroupNormalizerIn_conjBy_eq_local
        (G := G) (H := M.conjBy g) (Y := U) g⁻¹
    have hBack' :
        W1.conjBy g⁻¹ ≤
          (subgroupNormalizerIn (M.conjBy g) (U : Set G)).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using hBack
    rw [← hEq] at hBack'
    simpa [hMback] using hBack'
  · have hComp' :
        section12ComplementIn (D.conjBy g) (MF.conjBy g) U := by
      simpa [hDg] using hCompDU
    have hBack := theorem_8_18_section12ComplementIn_conjBy (G := G) g⁻¹ hComp'
    simpa [D, Subgroup.conjBy_inv] using hBack
  · intro hMFcyc
    let eMF : MF ≃* MF.conjBy g := (MulAut.conj g).subgroupMap MF
    exact hMFnotCyclic (eMF.isCyclic.1 hMFcyc)
  · have hBack := Subgroup.map_mono
      (f := (MulAut.conj g⁻¹).toMonoidHom) hSecondLe
    have hBack' :
        (section16SecondDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ ≤
          ((MF.conjBy g) ⊔
            subgroupCentralizerIn (M.conjBy g) (MF.conjBy g)).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using hBack
    simpa [hSecondBack, hMFcentBack] using hBack'
  · have hBack := congrArg (fun H : Subgroup G => H.conjBy g⁻¹) hFitEq
    simpa [hMFcentBack, hFitBack] using hBack
  · have hBack := Subgroup.map_mono
      (f := (MulAut.conj g⁻¹).toMonoidHom) hFitLeD
    have hBack' :
        (section8FittingSubgroup (M.conjBy g)).conjBy g⁻¹ ≤
          (ambientDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using hBack
    simpa [hFitBack, hDback] using hBack'
  · have hBack := Subgroup.map_mono
      (f := (MulAut.conj g⁻¹).toMonoidHom) hW2le
    have hBack' :
        W2.conjBy g⁻¹ ≤
          ((MF.conjBy g) ⊓
            section16SecondDerivedSubgroup (M.conjBy g)).conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using hBack
    simpa [hMFSecondBack] using hBack'
  · let eW2g : W2.conjBy g⁻¹ ≃* (W2.conjBy g⁻¹).conjBy g :=
      (MulAut.conj g).subgroupMap (W2.conjBy g⁻¹)
    let eW2 : W2.conjBy g⁻¹ ≃* W2 :=
      eW2g.trans (MulEquiv.subgroupCongr (by
        simpa using (Subgroup.conjBy_inv W2 g⁻¹)))
    exact eW2.isCyclic.2 hW2cyc
  · exact section12_conjBy_ne_bot hW2ne g⁻¹
  · intro x hxW1 hxne
    have hxW1g : g * x * g⁻¹ ∈ W1 := by
      have hxMap : g * x * g⁻¹ ∈ (W1.conjBy g⁻¹).conjBy g :=
        Subgroup.mem_map.mpr ⟨x, hxW1, rfl⟩
      have hW1back : (W1.conjBy g⁻¹).conjBy g = W1 :=
        section11_conjBy_inv' (G := G) W1 g
      simpa [hW1back] using hxMap
    have hxne_g : g * x * g⁻¹ ≠ 1 := by
      intro hxone
      apply hxne
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by simp [hxone]
    have hSource := hCent (g * x * g⁻¹) hxW1g hxne_g
    have hCentConj :
        elementCentralizerIn (ambientDerivedSubgroup (M.conjBy g)) (g * x * g⁻¹) =
          (elementCentralizerIn D x).conjBy g := by
      simpa [D, hDg] using
        theorem_8_18_elementCentralizerIn_conjBy
          (G := G) (H := D) (x := x) (g := g)
    have hConjEq : (elementCentralizerIn D x).conjBy g = W2 := by
      simpa [hCentConj] using hSource
    have hBack := congrArg (fun H : Subgroup G => H.conjBy g⁻¹) hConjEq
    simpa [D, Subgroup.conjBy_inv] using hBack
  · intro X hXne hXsub
    let Xg : Set G := section16ConjugateSet X g
    have hXgne : Xg.Nonempty := by
      rcases hXne with ⟨x, hx⟩
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩⟩
    have hHatConj :
        section16ConjugateSet
            (section16HatW (W1.conjBy g⁻¹) (W2.conjBy g⁻¹)) g =
          section16HatW W1 W2 := by
      have hW1back : (W1.conjBy g⁻¹).conjBy g = W1 :=
        section11_conjBy_inv' (G := G) W1 g
      have hW2back : (W2.conjBy g⁻¹).conjBy g = W2 :=
        section11_conjBy_inv' (G := G) W2 g
      simpa [hW1back, hW2back] using
        theorem_8_18_section16HatW_conjBy
          (G := G) (W1.conjBy g⁻¹) (W2.conjBy g⁻¹) g
    have hXgsub : Xg ⊆ section16HatW W1 W2 := by
      intro y hy
      rcases hy with ⟨x, hxX, rfl⟩
      have hxHat : x ∈ section16HatW (W1.conjBy g⁻¹) (W2.conjBy g⁻¹) :=
        hXsub hxX
      have hconj :
        g * x * g⁻¹ ∈
          section16ConjugateSet
            (section16HatW (W1.conjBy g⁻¹) (W2.conjBy g⁻¹)) g :=
        ⟨x, hxHat, rfl⟩
      simpa [hHatConj] using hconj
    have hSource : Subgroup.normalizer Xg = W1 ⊔ W2 :=
      hHat Xg hXgne hXgsub
    have hNormConj :
        Subgroup.normalizer Xg = (Subgroup.normalizer X).conjBy g := by
      simpa [Xg] using theorem_8_18_normalizer_section16ConjugateSet
        (G := G) X g
    have hConjEq : (Subgroup.normalizer X).conjBy g = W1 ⊔ W2 := by
      simpa [hNormConj] using hSource
    have hBack := congrArg (fun H : Subgroup G => H.conjBy g⁻¹) hConjEq
    have hNormBack : ((Subgroup.normalizer X).conjBy g).conjBy g⁻¹ =
        Subgroup.normalizer X :=
      section11_conjBy_inv (G := G) (Subgroup.normalizer X) g
    have hSupBack :
        (W1 ⊔ W2).conjBy g⁻¹ =
          W1.conjBy g⁻¹ ⊔ W2.conjBy g⁻¹ := by
      simpa [Subgroup.conjBy] using
        (Subgroup.map_sup W1 W2 (MulAut.conj g⁻¹).toMonoidHom)
    calc
      Subgroup.normalizer X =
          ((Subgroup.normalizer X).conjBy g).conjBy g⁻¹ := hNormBack.symm
      _ = (W1 ⊔ W2).conjBy g⁻¹ := hBack
      _ = W1.conjBy g⁻¹ ⊔ W2.conjBy g⁻¹ := hSupBack

private theorem theorem_8_18_typeIIToIVSourceCondition_conj_back
    {G : Type u} [Group G] [Finite G]
    {M U W1 : Subgroup G} (g : G)
    (hCond : typeIIToIVSourceCondition (M.conjBy g) U W1) :
    typeIIToIVSourceCondition M (U.conjBy g⁻¹) (W1.conjBy g⁻¹) := by
  classical
  rcases hCond with ⟨hUne, hPrime, hTI⟩
  refine ⟨?_, ?_, ?_⟩
  · exact section12_conjBy_ne_bot hUne g⁻¹
  · exact theorem_8_18_section16HasPrimeOrder_conjBy (G := G) g⁻¹ hPrime
  · have hFit :
        section8FittingSubgroup (M.conjBy g) =
          (section8FittingSubgroup M).conjBy g :=
      theorem_8_18_section8FittingSubgroup_conjBy (G := G) M g
    have hNonid :
        section16NonidentityElements
            (section8FittingSubgroup (M.conjBy g) : Set G) =
          section16ConjugateSet
            (section16NonidentityElements
              (section8FittingSubgroup M : Set G)) g := by
      simpa [hFit] using
        theorem_8_18_section16NonidentityElements_conjBy
          (G := G) (section8FittingSubgroup M) g
    exact theorem_8_18_section16TISubset_conj_back
      (G := G)
      (X := section16NonidentityElements
        (section8FittingSubgroup M : Set G)) g
      (by simpa [hNonid] using hTI)

public theorem theorem_8_18_typeIIDefinitionData_conj_back
    {G : Type u} [Group G] [Finite G]
    {M MF LF : Subgroup G} (g : G)
    (hMF : section16MFSubgroup M MF)
    (hLF : section16MFSubgroup (M.conjBy g) LF)
    (hType : typeIIDefinitionData (M.conjBy g) LF) :
    typeIIDefinitionData M MF := by
  classical
  have hMFg : section16MFSubgroup (M.conjBy g) (MF.conjBy g) :=
    theorem_8_18_mfSubgroup_conjBy (G := G) g hMF
  have hLF_eq : LF = MF.conjBy g :=
    theorem_8_18_mfSubgroup_eq (G := G) hLF hMFg
  subst LF
  rcases hType with ⟨U, W1, W2, U1, U0, hP, hCond, hComm, hNorm, hF⟩
  refine ⟨U.conjBy g⁻¹, W1.conjBy g⁻¹, W2.conjBy g⁻¹,
    U1.conjBy g⁻¹, U0.conjBy g⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem_8_18_typePDefinitionData_conj_back
      (G := G) (M := M) (MF := MF) (g := g) hMF hMFg hP
  · exact theorem_8_18_typeIIToIVSourceCondition_conj_back
      (G := G) (M := M) (g := g) hCond
  · letI : IsMulCommutative U := hComm
    change IsMulCommutative
      (U.map (MulAut.conj g⁻¹).toMonoidHom)
    exact Subgroup.map_isMulCommutative
      (f := (MulAut.conj g⁻¹).toMonoidHom) (H := U)
  · intro hle
    apply hNorm
    have hNormLe :
        (Subgroup.normalizer (U.conjBy g⁻¹ : Set G)).conjBy g ≤ M.conjBy g := by
      simpa [Subgroup.conjBy] using
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle
    have hSetConj :
        section16ConjugateSet (U.conjBy g⁻¹ : Set G) g = (U : Set G) := by
      have hUback : (U.conjBy g⁻¹).conjBy g = U :=
        section11_conjBy_inv' (G := G) U g
      simpa [hUback] using
        theorem_8_18_section16ConjugateSet_subgroup
          (G := G) (U.conjBy g⁻¹) g
    have hNormEq :
        Subgroup.normalizer (U : Set G) =
          (Subgroup.normalizer (U.conjBy g⁻¹ : Set G)).conjBy g := by
      simpa [hSetConj] using
        theorem_8_18_normalizer_section16ConjugateSet
          (G := G) (U.conjBy g⁻¹ : Set G) g
    simpa [hNormEq] using hNormLe
  · have hDg :
        ambientDerivedSubgroup (M.conjBy g) =
          (ambientDerivedSubgroup M).conjBy g :=
      theorem_8_18_ambientDerivedSubgroup_conjBy (G := G) M g
    have hF' :
        typeFData ((ambientDerivedSubgroup M).conjBy g) (MF.conjBy g)
          U U1 U0 := by
      simpa [hDg] using hF
    exact theorem_8_18_typeFData_conj_back (G := G) g hF'

public theorem theorem_8_18_typeIDefinitionData_conj_back
    {G : Type u} [Group G] [Finite G]
    {M MF LF : Subgroup G} (g : G)
    (hMF : section16MFSubgroup M MF)
    (hLF : section16MFSubgroup (M.conjBy g) LF)
    (hType : typeIDefinitionData (M.conjBy g) LF) :
    typeIDefinitionData M MF := by
  classical
  have hMFg : section16MFSubgroup (M.conjBy g) (MF.conjBy g) :=
    theorem_8_18_mfSubgroup_conjBy (G := G) g hMF
  have hLF_eq : LF = MF.conjBy g :=
    theorem_8_18_mfSubgroup_eq (G := G) hLF hMFg
  subst LF
  rcases hType with ⟨U, U1, U0, hF, hAlt⟩
  refine ⟨U.conjBy g⁻¹, U1.conjBy g⁻¹, U0.conjBy g⁻¹, ?_, ?_⟩
  · rcases hF with
      ⟨hSolv, hOdd, _hMFg, hMFposg, hMFltg, hUne, hComp, hU1le,
        hU1comm, hU1norm, hCent, hU0le, hExp, hFrob⟩
    refine ⟨?_, ?_, hMF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · let eM : M ≃* M.conjBy g := (MulAut.conj g).subgroupMap M
      let : Group.IsSolvable (M.conjBy g) := hSolv
      exact Group.isSolvable_of_surjective (f := eM.symm.toMonoidHom) eM.symm.surjective
    · have hcard : Nat.card (M.conjBy g) = Nat.card M := by
        simpa [Subgroup.conjBy] using
          (Subgroup.card_map_of_injective
            (K := M) (f := (MulAut.conj g).toMonoidHom)
            (MulAut.conj g).injective)
      simpa [hcard] using hOdd
    · refine bot_lt_iff_ne_bot.2 ?_
      intro hbot
      exact (ne_of_gt hMFposg) (by simp [hbot, Subgroup.conjBy])
    · rcases hMF.1 with ⟨hMFM, _hNorm, _hNil, _hHall⟩
      refine lt_of_le_of_ne hMFM ?_
      intro hEq
      exact (ne_of_gt hMFltg) (by simp [hEq])
    · exact section12_conjBy_ne_bot hUne g⁻¹
    · have hCompBack :=
        theorem_8_18_section12ComplementIn_conjBy (G := G) g⁻¹ hComp
      simpa [Subgroup.conjBy_inv] using hCompBack
    · exact Subgroup.map_mono hU1le
    · letI : IsMulCommutative U1 := hU1comm
      change IsMulCommutative
        (U1.map (MulAut.conj g⁻¹).toMonoidHom)
      exact Subgroup.map_isMulCommutative
        (f := (MulAut.conj g⁻¹).toMonoidHom) (H := U1)
    · have hNormBack :=
        theorem_8_18_section10NormalIn_conjBy (G := G) g⁻¹ hU1norm
      simpa [Subgroup.conjBy_inv] using hNormBack
    · intro x hxMF hxne z hz
      have hxMFg : g * x * g⁻¹ ∈ MF.conjBy g :=
        Subgroup.mem_map.mpr ⟨x, hxMF, rfl⟩
      have hxne_g : g * x * g⁻¹ ≠ 1 := by
        intro hxone
        apply hxne
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by simp [hxone]
      have hzConj :
          g * z * g⁻¹ ∈ elementCentralizerIn U (g * x * g⁻¹) := by
        have hzMap :
            g * z * g⁻¹ ∈
              (elementCentralizerIn (U.conjBy g⁻¹) x).conjBy g :=
          Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        have hCentEq :
            elementCentralizerIn U (g * x * g⁻¹) =
              (elementCentralizerIn (U.conjBy g⁻¹) x).conjBy g := by
          have hUback : (U.conjBy g⁻¹).conjBy g = U := by
            simpa using (Subgroup.conjBy_inv (U) g⁻¹)
          simpa [hUback] using
            (theorem_8_18_elementCentralizerIn_conjBy
              (G := G) (H := U.conjBy g⁻¹) (x := x) (g := g))
        simpa [hCentEq] using hzMap
      have hzU1 : g * z * g⁻¹ ∈ U1 :=
        hCent (g * x * g⁻¹) hxMFg hxne_g hzConj
      exact Subgroup.mem_map.mpr ⟨g * z * g⁻¹, hzU1, by simp [mul_assoc]⟩
    · exact Subgroup.map_mono hU0le
    · let eU0 : U0 ≃* U0.conjBy g⁻¹ := (MulAut.conj g⁻¹).subgroupMap U0
      let eU : U ≃* U.conjBy g⁻¹ := (MulAut.conj g⁻¹).subgroupMap U
      have hU0exp :
          Monoid.exponent (U0.conjBy g⁻¹) = Monoid.exponent U0 := by
        simpa using (Monoid.exponent_eq_of_mulEquiv eU0).symm
      have hUexp :
          Monoid.exponent (U.conjBy g⁻¹) = Monoid.exponent U := by
        simpa using (Monoid.exponent_eq_of_mulEquiv eU).symm
      rw [hU0exp, hUexp, hExp]
    · have hFrobBack :
          section12FrobeniusJoinWithKernel
            ((MF.conjBy g).conjBy g⁻¹) (U0.conjBy g⁻¹) := by
        exact theorem_8_18_section12FrobeniusJoinWithKernel_conjBy
          (G := G) g⁻¹ hFrob
      simpa [Subgroup.conjBy_inv] using hFrobBack
  · rcases hAlt with hTI | hRest
    · left
      have hNonid :
          section16NonidentityElements (MF.conjBy g : Set G) =
            section16ConjugateSet
              (section16NonidentityElements (MF : Set G)) g :=
        theorem_8_18_section16NonidentityElements_conjBy (G := G) MF g
      exact theorem_8_18_section16TISubset_conj_back
        (G := G) (X := section16NonidentityElements (MF : Set G)) g
        (by simpa [hNonid] using hTI)
    · rcases hRest with hRank | hCore
      · right
        left
        let eMF : MF ≃* MF.conjBy g := (MulAut.conj g).subgroupMap MF
        have hComm : IsMulCommutative MF :=
          section12_isMulCommutative_of_mulEquiv eMF hRank.1
        have hRankEq : groupRank MF = groupRank (MF.conjBy g) :=
          le_antisymm
            (groupRank_le_of_equiv eMF.symm)
            (groupRank_le_of_equiv eMF)
        exact ⟨hComm, by rw [hRankEq, hRank.2]⟩
      · right
        right
        rcases hCore with ⟨hExpDvd, hCyc⟩
        constructor
        · intro p hp
          have hpG : p ∈ subgroupPrimeSet (MF.conjBy g) := by
            simpa [theorem_8_18_subgroupPrimeSet_conjBy (G := G) MF g] using hp
          let eU : U ≃* U.conjBy g⁻¹ := (MulAut.conj g⁻¹).subgroupMap U
          have hUexp :
              Monoid.exponent (U.conjBy g⁻¹) = Monoid.exponent U := by
            simpa using (Monoid.exponent_eq_of_mulEquiv eU).symm
          simpa [hUexp] using hExpDvd p hpG
        · rcases hCyc with ⟨p, hpG, hCycG⟩
          have hp : p ∈ subgroupPrimeSet MF := by
            simpa [theorem_8_18_subgroupPrimeSet_conjBy (G := G) MF g] using hpG
          exact ⟨p, hp,
            theorem_8_18_section10PPrimeCore_isCyclic_conj_back
              (G := G) MF g p hCycG⟩

private theorem theorem_8_18_support_conclusion_source_type_mem
    {G : Type u} [Group G] [Finite G]
    {S T SF TF LF : Subgroup G} {A0S : Set G} {x : G}
    (hTF : section16MFSubgroup T TF)
    (hSupp : supportConclusionDataSource S SF S A0S x T LF) :
    (typeIDefinitionData T TF ∧
        x ∈ section8CentralizerUnion T TF \ a1Set TF) ∨
      (typeIIDefinitionData T TF ∧
        x ∈ section8CentralizerUnion (ambientDerivedSubgroup T) TF \ a1Set TF ∧
          section8FrobeniusGroupWithKernel S SF) := by
  rcases hSupp with
    ⟨_hTmax, hLF, _hUnique, _hSemiT, _hSemiC, _hCoprime, hCases⟩
  have hLF_eq_TF : LF = TF :=
    theorem_8_18_mfSubgroup_eq (G := G) hLF hTF
  rcases hCases with hTypeI | hTypeII
  · rcases hTypeI with ⟨hTypeI, hx⟩
    left
    exact ⟨by simpa [hLF_eq_TF] using hTypeI,
      by simpa [hLF_eq_TF] using hx⟩
  · rcases hTypeII with ⟨hTypeII, hx, hFrob⟩
    right
    exact ⟨by simpa [hLF_eq_TF] using hTypeII,
      by simpa [hLF_eq_TF] using hx, hFrob⟩

private theorem theorem_8_18_support_witness_unique
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hSupp : supportsSubgroupSource S T DS) :
    ∃ x : G, x ∈ DS ∧
      T ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
      ∀ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) →
          L = T := by
  rcases hData with ⟨_hNonconj, _hS10, _hSmem, _hT10, _hTmem, hS14, _hT14⟩
  rcases hS14 with
    ⟨_hA1A, _hAA0, _hD, _hRbot, hUnique, _hReq,
      _htildeA, _htildeA0, _htildeA1⟩
  rcases hSupp with ⟨hTmax, x, hxD, hxCentT⟩
  have hTmem :
      T ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
    ⟨hTmax, hxCentT⟩
  rcases hUnique x hxD with ⟨L0, _hL0, huniq⟩
  have hT_eq_L0 : T = L0 := huniq T hTmem
  refine ⟨x, hxD, hTmem, ?_⟩
  intro L hL
  exact (huniq L hL).trans hT_eq_L0.symm


private theorem theorem_8_18_support_witness_type_mem_left
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hSupp : supportsSubgroupSource S T DS) :
    ∃ x : G, x ∈ A1S ∧
      T ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
      ((typeIDefinitionData T TF ∧
          x ∈ section8CentralizerUnion T TF \ a1Set TF) ∨
        (typeIIDefinitionData T TF ∧
          x ∈ section8CentralizerUnion (ambientDerivedSubgroup T) TF \ a1Set TF ∧
            section8FrobeniusGroupWithKernel S SF)) := by
  rcases hData with ⟨hNonconj, hS10, hSmem, hT10, hTmem, hS14, hT14⟩
  rcases hS10 with ⟨_hSmax, _hSF, _hSS, _hA1S, _hScases⟩
  rcases hT10 with ⟨_hTmax, hTF, _hTT, _hA1T, _hTcases⟩
  rcases hS14 with
    ⟨_hA1A, _hAA0, hDS, _hRbot, _hUnique, _hReq,
      _htildeA, _htildeA0, _htildeA1⟩
  rcases theorem_8_18_support_witness_unique
      (G := G)
      (hData := ⟨hNonconj,
        ⟨_hSmax, _hSF, _hSS, _hA1S, _hScases⟩,
        hSmem,
        ⟨_hTmax, hTF, _hTT, _hA1T, _hTcases⟩,
        hTmem,
        ⟨_hA1A, _hAA0, hDS, _hRbot, _hUnique, _hReq,
          _htildeA, _htildeA0, _htildeA1⟩,
        hT14⟩)
      hSupp with
    ⟨x, hxD, hTmem, _huniqT⟩
  have h13S :=
    (theorem_8_13 (G := G) S SF SS AS A0S A1S A0S)
      (inferInstance : IsMinCE G)
      ⟨_hSmax, _hSF, _hSS, _hA1S, _hScases⟩
      (Or.inr rfl)
  have hxD' : x ∈ section8DSet S A0S := by
    simpa [hDS] using hxD
  rcases h13S.2.2.2 x hxD' T hTmem with ⟨LF, hSuppData⟩
  have hxA1S : x ∈ A1S := h13S.2.1 hxD'
  exact ⟨x, hxA1S, hTmem,
    theorem_8_18_support_conclusion_source_type_mem (G := G) hTF hSuppData⟩

private theorem theorem_8_18_support_witness_mem_AT_left
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hSupp : supportsSubgroupSource S T DS) :
    ∃ x : G, x ∈ A1S ∧ x ∈ AT ∧
      T ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
  rcases hData with ⟨hNonconj, hS10, hSmem, hT10, hTmem, hS14, hT14⟩
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT :=
    ⟨hNonconj, hS10, hSmem, hT10, hTmem, hS14, hT14⟩
  rcases theorem_8_18_support_witness_type_mem_left (G := G) hData' hSupp with
    ⟨x, hxA1S, hTmemMax, hxTypeMem⟩
  have hxAT : x ∈ AT := by
    rcases hxTypeMem with hxTypeI | hxTypeII
    · exact hTmem.1 x hxTypeI.1 hxTypeI.2.1
    · exact hTmem.2 x hxTypeII.1 hxTypeII.2.1.1
  exact ⟨x, hxA1S, hxAT, hTmemMax⟩

private theorem theorem_8_18_support_implies_inter_nonempty
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hSupp : supportsSubgroupSource S T DS) :
    (A1S ∩ AT).Nonempty := by
  rcases theorem_8_18_support_witness_mem_AT_left (G := G) hData hSupp with
    ⟨x, hxA1S, hxAT, _hTmem⟩
  exact ⟨x, hxA1S, hxAT⟩

private theorem theorem_8_18_mem_tildeA1S_of_mem_A1S
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {x : G} (hxA1S : x ∈ A1S) :
    x ∈ tildeA1S := by
  rcases hData with ⟨_hNonconj, _hS10, _hSmem, _hT10, _hTmem, hS14, _hT14⟩
  rcases hS14 with
    ⟨_hA1SA, _hASA0S, _hDS, _hRSbot, _hSUnique, _hRSeq,
      _htildeAS, _htildeA0S, htildeA1S⟩
  rw [htildeA1S]
  refine ⟨x, hxA1S, ?_⟩
  refine ⟨x, ?_, 1, by simp, ?_⟩
  · exact ⟨1, (RS x).one_mem, by simp⟩
  · simp

private theorem theorem_8_18_mem_tildeAT_of_conj_mem_AT
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {a g : G} (haAT : a ∈ AT) :
    g * a * g⁻¹ ∈ tildeAT := by
  rcases hData with ⟨_hNonconj, _hS10, _hSmem, _hT10, _hTmem, _hS14, hT14⟩
  rcases hT14 with
    ⟨_hA1TA, _hATA0T, _hDT, _hRTbot, _hTUnique, _hRTeq,
      htildeAT, _htildeA0T, _htildeA1T⟩
  rw [htildeAT]
  refine ⟨a, haAT, ?_⟩
  refine ⟨a, ?_, g, by simp, rfl⟩
  exact ⟨1, (RT a).one_mem, by simp⟩

private theorem theorem_8_18_section8CentralizerUnion_conj_back
    {G : Type u} [Group G]
    {C X : Subgroup G} {g y : G}
    (hy : y ∈ section8CentralizerUnion C X) :
    g⁻¹ * y * g ∈
      section8CentralizerUnion (C.conjBy g⁻¹) (X.conjBy g⁻¹) := by
  rcases hy with ⟨x, hxXSharp, hyCentSharp⟩
  refine ⟨g⁻¹ * x * g, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨x, hxXSharp.1, by simp⟩
    · intro hx_one
      apply hxXSharp.2
      have hx_back := congrArg (fun z : G => g * z * g⁻¹) hx_one
      simpa [mul_assoc] using hx_back
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨y, hyCentSharp.1.1, by simp⟩
      · change g⁻¹ * y * g ∈ Subgroup.centralizer ({g⁻¹ * x * g} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : y * x = x * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hyCentSharp.1.2
        calc
          (g⁻¹ * y * g) * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
          _ = g⁻¹ * (x * y) * g := by rw [hcomm]
          _ = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
    · intro hy_one
      apply hyCentSharp.2
      have hy_back := congrArg (fun z : G => g * z * g⁻¹) hy_one
      simpa [mul_assoc] using hy_back

private theorem theorem_8_18_section8CentralizerUnion_mono_left
    {G : Type u} [Group G]
    {C D X : Subgroup G}
    (hCD : C ≤ D) :
    section8CentralizerUnion C X ⊆ section8CentralizerUnion D X := by
  intro y hy
  rcases hy with ⟨x, hxX, hyCent⟩
  refine ⟨x, hxX, ?_⟩
  exact ⟨⟨hCD hyCent.1.1, hyCent.1.2⟩, hyCent.2⟩

private theorem theorem_8_18_section8CentralizerUnion_mono_right
    {G : Type u} [Group G]
    {C X Y : Subgroup G}
    (hXY : X ≤ Y) :
    section8CentralizerUnion C X ⊆ section8CentralizerUnion C Y := by
  intro z hz
  rcases hz with ⟨x, hxX, hzCent⟩
  refine ⟨x, ?_, hzCent⟩
  exact ⟨hXY hxX.1, hxX.2⟩

private theorem theorem_8_18_not_typeI_of_msChoiceSource_tail
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hTail :
      (¬ typeIDefinitionData M MF ∧
          typeIIDefinitionData M MF ∧
          ¬ typeIIIDefinitionData M MF ∧
          ¬ typeIVDefinitionData M MF ∧
          ¬ typeVDefinitionData M MF ∧
          Ms = MF) ∨
        (¬ typeIDefinitionData M MF ∧
          ¬ typeIIDefinitionData M MF ∧
          typeIIIDefinitionData M MF ∧
          ¬ typeIVDefinitionData M MF ∧
          ¬ typeVDefinitionData M MF ∧
          Ms = ambientDerivedSubgroup M) ∨
        (¬ typeIDefinitionData M MF ∧
          ¬ typeIIDefinitionData M MF ∧
          ¬ typeIIIDefinitionData M MF ∧
          typeIVDefinitionData M MF ∧
          ¬ typeVDefinitionData M MF ∧
          Ms = ambientDerivedSubgroup M) ∨
        (¬ typeIDefinitionData M MF ∧
          ¬ typeIIDefinitionData M MF ∧
          ¬ typeIIIDefinitionData M MF ∧
          ¬ typeIVDefinitionData M MF ∧
          typeVDefinitionData M MF ∧
          Ms = MF)) :
    ¬ typeIDefinitionData M MF := by
  intro hTypeI
  rcases hTail with hTypeII | hRest
  · exact hTypeII.1 hTypeI
  rcases hRest with hTypeIII | hRest
  · exact hTypeIII.1 hTypeI
  rcases hRest with hTypeIV | hTypeV
  · exact hTypeIV.1 hTypeI
  · exact hTypeV.1 hTypeI

private theorem theorem_8_18_source_choice_mf_le_ms_of_non_typeI
    {G : Type u} [Group G] [Finite G]
    {M MF Ms U W1 W2 : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hNotTypeI : ¬ typeIDefinitionData M MF)
    (hTypeP : typePDefinitionData M MF U W1 W2) :
    MF ≤ Ms := by
  rcases hChoice with hTypeI | hTail
  · exact False.elim (hNotTypeI hTypeI.1)
  rcases hTail with hTypeII | hTail
  · simp [hTypeII.2.2.2.2.2]
  rcases hTail with hTypeIII | hTail
  · rcases hTypeP with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD,
        _hUnil, _hW1norm, hMFcompD, _hMFnoncyc, _hSecond,
        _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
        _hCent, _hNorm⟩
    simpa [hTypeIII.2.2.2.2.2] using hMFcompD.1
  rcases hTail with hTypeIV | hTypeV
  · rcases hTypeP with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD,
        _hUnil, _hW1norm, hMFcompD, _hMFnoncyc, _hSecond,
        _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
        _hCent, _hNorm⟩
    simpa [hTypeIV.2.2.2.2.2] using hMFcompD.1
  · simp [hTypeV.2.2.2.2.2]

private theorem theorem_8_18_support_conclusion_conj_back_mem_AT_of_non_typeI_typeII_case
    {G : Type u} [Group G] [Finite G]
    {T TF TT LF : Subgroup G} {AT A0T A1T : Set G} {x g : G}
    (hT10 : notation_8_10_source_data T TF TT AT A0T A1T)
    (hNotTypeI : ¬ typeIDefinitionData T TF)
    (hLF : section16MFSubgroup (T.conjBy g) LF)
    (hx :
      x ∈ section8CentralizerUnion (ambientDerivedSubgroup (T.conjBy g)) LF \
        a1Set LF) :
    g⁻¹ * x * g ∈ AT := by
  rcases hT10 with ⟨_hTmax, hTF, hChoice, _hA1T, hCases⟩
  have hTFg : section16MFSubgroup (T.conjBy g) (TF.conjBy g) :=
    theorem_8_18_mfSubgroup_conjBy (G := G) g hTF
  have hLF_eq : LF = TF.conjBy g :=
    theorem_8_18_mfSubgroup_eq (G := G) hLF hTFg
  have hxUnion :
      x ∈ section8CentralizerUnion
        (ambientDerivedSubgroup (T.conjBy g)) (TF.conjBy g) := by
    simpa [hLF_eq] using hx.1
  have hxBack :=
    theorem_8_18_section8CentralizerUnion_conj_back
      (G := G) (C := ambientDerivedSubgroup (T.conjBy g))
      (X := TF.conjBy g) (g := g) hxUnion
  have hD :
      ambientDerivedSubgroup (T.conjBy g) =
        (ambientDerivedSubgroup T).conjBy g :=
    theorem_8_18_ambientDerivedSubgroup_conjBy (G := G) T g
  have hxOriginal :
      g⁻¹ * x * g ∈ section8CentralizerUnion (ambientDerivedSubgroup T) TF := by
    simpa [hD, Subgroup.conjBy_inv] using hxBack
  rcases hCases with hTypeI | hTypePCase
  · exact False.elim (hNotTypeI hTypeI.1)
  rcases hTypePCase with
    ⟨U, W1, W2, hTypeP, _hTypeAny, hAT, _hA0T, _hA1AT⟩
  have hTFleTT : TF ≤ TT :=
    theorem_8_18_source_choice_mf_le_ms_of_non_typeI
      (G := G) hChoice hNotTypeI hTypeP
  rw [hAT]
  exact theorem_8_18_section8CentralizerUnion_mono_right
    (G := G) (C := ambientDerivedSubgroup T) hTFleTT hxOriginal

private theorem theorem_8_18_support_conclusion_conj_back_mem_centralizerUnion
    {G : Type u} [Group G] [Finite G]
    {S T SF TF LF : Subgroup G} {A0S : Set G} {x g : G}
    (hTF : section16MFSubgroup T TF)
    (hSupp : supportConclusionDataSource S SF S A0S x (T.conjBy g) LF) :
    g⁻¹ * x * g ∈ section8CentralizerUnion T TF := by
  rcases hSupp with
    ⟨_hTmax, hLF, _hUnique, _hSemiT, _hSemiC, _hCoprime, hCases⟩
  have hTFg : section16MFSubgroup (T.conjBy g) (TF.conjBy g) :=
    theorem_8_18_mfSubgroup_conjBy (G := G) g hTF
  have hLF_eq : LF = TF.conjBy g :=
    theorem_8_18_mfSubgroup_eq (G := G) hLF hTFg
  have hback :
      x ∈ section8CentralizerUnion (T.conjBy g) (TF.conjBy g) := by
    rcases hCases with hTypeI | hTypeII
    · exact by
        rcases hTypeI with ⟨_hTypeI, hx⟩
        simpa [hLF_eq] using hx.1
    · rcases hTypeII with ⟨_hTypeII, hx, _hFrob⟩
      exact theorem_8_18_section8CentralizerUnion_mono_left
        (G := G)
        (C := ambientDerivedSubgroup (T.conjBy g))
        (D := T.conjBy g)
        (X := TF.conjBy g)
        (section12_ambientDerivedSubgroup_le (G := G) (E := T.conjBy g))
        (by simpa [hLF_eq] using hx.1)
  have hconj :=
    theorem_8_18_section8CentralizerUnion_conj_back
      (G := G) (C := T.conjBy g) (X := TF.conjBy g) (g := g) hback
  simpa [Subgroup.conjBy_inv] using hconj

private theorem theorem_8_18_support_conclusion_conj_back_mem_AT_of_typeI
    {G : Type u} [Group G] [Finite G]
    {S T SF TF LF : Subgroup G} {A0S AT : Set G} {x g : G}
    (hTF : section16MFSubgroup T TF)
    (hTmem : notation_8_10_source_membership_data T TF AT)
    (hTypeI : typeIDefinitionData T TF)
    (hSupp : supportConclusionDataSource S SF S A0S x (T.conjBy g) LF) :
    g⁻¹ * x * g ∈ AT :=
  hTmem.1 (g⁻¹ * x * g) hTypeI
    (theorem_8_18_support_conclusion_conj_back_mem_centralizerUnion
      (G := G) hTF hSupp)


private theorem theorem_8_18_support_conj_implies_tilde_inter_of_right_typeI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hTypeI : typeIDefinitionData T TF)
    {g : G} (hSupp : supportsSubgroupSource S (T.conjBy g) DS) :
    (tildeA1S ∩ tildeAT).Nonempty := by
  rcases hData with ⟨hNonconj, hS10, hSmem, hT10, hTmem, hS14, hT14⟩
  rcases hS14 with
    ⟨hA1SA, hASA0S, hDS, hRSbot, hSUnique, hRSeq,
      htildeAS, htildeA0S, htildeA1S⟩
  rcases hT10 with ⟨_hTmax, hTF, _hTT, _hA1T, _hTcases⟩
  rcases hSupp with ⟨hTgmax, x, hxD, hxCentTg⟩
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT :=
    ⟨hNonconj, hS10, hSmem, ⟨_hTmax, hTF, _hTT, _hA1T, _hTcases⟩,
      hTmem,
      ⟨hA1SA, hASA0S, hDS, hRSbot, hSUnique, hRSeq,
        htildeAS, htildeA0S, htildeA1S⟩,
      hT14⟩
  have h13S :=
    (theorem_8_13 (G := G) S SF SS AS A0S A1S A0S)
      (inferInstance : IsMinCE G) hS10 (Or.inr rfl)
  have hxD' : x ∈ section8DSet S A0S := by
    simpa [hDS] using hxD
  have hxA1S : x ∈ A1S := h13S.2.1 hxD'
  have hTgmem :
      T.conjBy g ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
    ⟨hTgmax, hxCentTg⟩
  rcases h13S.2.2.2 x hxD' (T.conjBy g) hTgmem with ⟨LF, hSuppData⟩
  have hxATback : g⁻¹ * x * g ∈ AT :=
    theorem_8_18_support_conclusion_conj_back_mem_AT_of_typeI
      (G := G) (S := S) (T := T) (SF := SF) (TF := TF)
      (A0S := A0S) (AT := AT) (x := x) (g := g)
      hTF hTmem hTypeI hSuppData
  refine ⟨x, ?_, ?_⟩
  · exact theorem_8_18_mem_tildeA1S_of_mem_A1S (G := G) hData' hxA1S
  · have hxTilde :
        g * (g⁻¹ * x * g) * g⁻¹ ∈ tildeAT :=
      theorem_8_18_mem_tildeAT_of_conj_mem_AT
        (G := G) (hData := hData') (a := g⁻¹ * x * g) (g := g) hxATback
    simpa [mul_assoc] using hxTilde


private theorem theorem_8_18_order_coprime_of_prime_disjoint
    {G : Type u} [Group G] [Finite G]
    {SS TT : Subgroup G} {A1S : Set G} {x : G}
    (hA1S : A1S = a1Set SS)
    (hPrimeDisj : Disjoint (subgroupPrimeSet SS) (subgroupPrimeSet TT))
    (hxA1S : x ∈ A1S) :
    Nat.Coprime (orderOf x) (Nat.card TT) := by
  rw [hA1S, a1Set] at hxA1S
  refine Nat.coprime_of_dvd ?_
  intro p hpprime hpOrder hpTT
  let q : Nat.Primes := ⟨p, hpprime⟩
  have hqS : q ∈ subgroupPrimeSet SS := by
    rw [subgroupPrimeSet]
    exact hpOrder.trans (Subgroup.orderOf_dvd_natCard SS hxA1S.1)
  have hqT : q ∈ subgroupPrimeSet TT := by
    change p ∣ Nat.card TT
    exact hpTT
  exact (Set.disjoint_left.mp hPrimeDisj hqS) hqT

private theorem theorem_8_18_not_mem_A1_right_of_prime_disjoint
    {G : Type u} [Group G] [Finite G]
    {SS TT : Subgroup G} {A1S A1T : Set G} {x : G}
    (hA1S : A1S = a1Set SS)
    (hA1T : A1T = a1Set TT)
    (hPrimeDisj : Disjoint (subgroupPrimeSet SS) (subgroupPrimeSet TT))
    (hxA1S : x ∈ A1S) :
    x ∉ A1T := by
  rw [hA1S, a1Set] at hxA1S
  rw [hA1T, a1Set]
  intro hxA1T
  have horder_ne_one : orderOf x ≠ 1 := by
    intro horder
    exact hxA1S.2 (orderOf_eq_one_iff.mp horder)
  have horder_gt_one : 1 < orderOf x :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Nat.ne_of_gt (orderOf_pos x), horder_ne_one⟩
  rcases Nat.exists_prime_and_dvd horder_gt_one.ne' with ⟨p, hpprime, hpOrder⟩
  let q : Nat.Primes := ⟨p, hpprime⟩
  have hqS : q ∈ subgroupPrimeSet SS := by
    rw [subgroupPrimeSet]
    exact hpOrder.trans (Subgroup.orderOf_dvd_natCard SS hxA1S.1)
  have hqT : q ∈ subgroupPrimeSet TT := by
    rw [subgroupPrimeSet]
    exact hpOrder.trans (Subgroup.orderOf_dvd_natCard TT hxA1T.1)
  exact (Set.disjoint_left.mp hPrimeDisj hqS) hqT

private theorem theorem_8_18_prime_disjoint_consequences
    {G : Type u} [Group G] [Finite G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hPrimeDisj : Disjoint (subgroupPrimeSet SS) (subgroupPrimeSet TT))
    {x : G} (hx : x ∈ A1S ∩ AT) :
    Nat.Coprime (orderOf x) (Nat.card TT) ∧ x ∉ A1T := by
  rcases hData with ⟨_hNonconj, hS10, _hSmem, hT10, _hTmem, _hS14, _hT14⟩
  rcases hS10 with ⟨_hSmax, _hSF, _hSS, hA1S, _hScases⟩
  rcases hT10 with ⟨_hTmax, _hTF, _hTT, hA1T, _hTcases⟩
  exact ⟨
    theorem_8_18_order_coprime_of_prime_disjoint hA1S hPrimeDisj hx.1,
    theorem_8_18_not_mem_A1_right_of_prime_disjoint hA1S hA1T hPrimeDisj hx.1⟩

private theorem theorem_8_18_section12NotConjugate_right_left
    {G : Type u} [Group G]
    {S T : Subgroup G}
    (hNonconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) S T) :
    section12NotConjugate T S := by
  intro g hTgS
  apply hNonconj
  refine ⟨g⁻¹, by simp, ?_⟩
  calc
    T = (T.conjBy g).conjBy g⁻¹ := (Subgroup.conjBy_inv T g).symm
    _ = S.conjBy g⁻¹ := by rw [hTgS]

private theorem theorem_8_18_prime_disjoint_of_nonconj
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT) :
    Disjoint (subgroupPrimeSet SS) (subgroupPrimeSet TT) := by
  rcases hData with ⟨hNonconj, hS10, _hSmem, hT10, _hTmem, _hS14, _hT14⟩
  rcases hS10 with ⟨hSmax, _hSF, _hSS, _hA1S, _hScases⟩
  rcases hT10 with ⟨hTmax, _hTF, _hTT, _hA1T, _hTcases⟩
  have hSigmaDisj : Disjoint (section10SigmaPrimes S) (section10SigmaPrimes T) :=
    theorem_13_9 (G := G) hSmax hTmax
      (theorem_8_18_section12NotConjugate_right_left (G := G) hNonconj)
  have hSSsigma : subgroupPrimeSet SS = section10SigmaPrimes S :=
    theorem_8_17_subgroupPrimeSet_msigma_eq (G := G)
      ⟨hSmax, _hSF, _hSS, _hA1S, _hScases⟩
  have hTTsigma : subgroupPrimeSet TT = section10SigmaPrimes T :=
    theorem_8_17_subgroupPrimeSet_msigma_eq (G := G)
      ⟨hTmax, _hTF, _hTT, _hA1T, _hTcases⟩
  simpa [hSSsigma, hTTsigma] using hSigmaDisj

private theorem theorem_8_18_prime_consequences_of_nonconj
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {x : G} (hx : x ∈ A1S ∩ AT) :
    Nat.Coprime (orderOf x) (Nat.card TT) ∧ x ∉ A1T :=
  theorem_8_18_prime_disjoint_consequences (G := G) hData
    (theorem_8_18_prime_disjoint_of_nonconj (G := G) hData) hx

private theorem theorem_8_18_msChoiceSource_eq_mf_of_typeI
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hTypeI : typeIDefinitionData M MF) :
    Ms = MF := by
  rcases hChoice with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs⟩
    exact hMs
  · exact False.elim (hII.1 hTypeI)
  · exact False.elim (hIII.1 hTypeI)
  · exact False.elim (hIV.1 hTypeI)
  · exact False.elim (hV.1 hTypeI)

private theorem theorem_8_18_msChoiceSource_eq_mf_of_typeII
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    (hChoice : msChoiceSource M MF Ms)
    (hTypeII : typeIIDefinitionData M MF) :
    Ms = MF := by
  rcases hChoice with hI | hII | hIII | hIV | hV
  · exact False.elim (hI.2.1 hTypeII)
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs⟩
    exact hMs
  · exact False.elim (hIII.2.1 hTypeII)
  · exact False.elim (hIV.2.1 hTypeII)
  · exact False.elim (hV.2.1 hTypeII)

private theorem theorem_8_18_right_typeI_or_typeII_of_diff
    {G : Type u} [Group G] [Finite G]
    {T TF TT : Subgroup G}
    {AT A0T A1T : Set G} {x : G}
    (hT10 : notation_8_10_source_data T TF TT AT A0T A1T)
    (hxAT : x ∈ AT)
    (hxNotA1T : x ∉ A1T) :
    typeIDefinitionData T TF ∨ typeIIDefinitionData T TF := by
  rcases hT10 with ⟨_hTmax, _hTF, _hTT, _hA1T, hCases⟩
  rcases hCases with hTypeI | hTypeP
  · exact Or.inl hTypeI.1
  · rcases hTypeP with
      ⟨_U, _W1, _W2, _hP, hSourceType, _hAT, _hA0T, hLate⟩
    rcases hSourceType with hTypeII | hTypeIII | hTypeIV | hTypeV
    · exact Or.inr hTypeII
    · exact False.elim (hxNotA1T (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inl hTypeIII)).2
        simpa [hA_eq_A1] using hxAT))
    · exact False.elim (hxNotA1T (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inr (Or.inl hTypeIV))).2
        simpa [hA_eq_A1] using hxAT))
    · exact False.elim (hxNotA1T (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inr (Or.inr hTypeV))).2
        simpa [hA_eq_A1] using hxAT))

private theorem theorem_8_18_right_theorem_8_12_source_data_of_diff
    {G : Type u} [Group G] [Finite G]
    {T TF TT : Subgroup G}
    {AT A0T A1T : Set G} {x : G}
    (hT10 : notation_8_10_source_data T TF TT AT A0T A1T)
    (hxAT : x ∈ AT)
    (hxNotA1T : x ∉ A1T) :
    ∃ U : Subgroup G, theorem_8_12_source_data T TF U TT AT A0T A1T := by
  rcases hT10 with ⟨hTmax, hTF, hTT, hA1T, hCases⟩
  rcases hCases with hTypeI | hTypeP
  · rcases hTypeI with ⟨hTypeI, hAT, hA0T⟩
    rcases hTypeI with ⟨U, U1, U0, hF, hAlt⟩
    have hTypeI' : typeIDefinitionData T TF := ⟨U, U1, U0, hF, hAlt⟩
    have hTT_eq : TT = TF :=
      theorem_8_18_msChoiceSource_eq_mf_of_typeI hTT hTypeI'
    have hA1TF : A1T = a1Set TF := by
      simpa [hTT_eq] using hA1T
    refine ⟨U, ?_⟩
    exact ⟨⟨hTmax, hTF, hTT, hA1T, Or.inl ⟨hTypeI', hAT, hA0T⟩⟩,
      Or.inl ⟨⟨U1, U0, hF, hAlt⟩, hAT, hA1TF⟩⟩
  · rcases hTypeP with
      ⟨UP, W1P, W2P, hP, hSourceType, hAT, hA0T, hLate⟩
    have hNotation : notation_8_10_source_data T TF TT AT A0T A1T :=
      ⟨hTmax, hTF, hTT, hA1T,
        Or.inr ⟨UP, W1P, W2P, hP, hSourceType, hAT, hA0T, hLate⟩⟩
    rcases hSourceType with hTypeII | hTypeIII | hTypeIV | hTypeV
    · rcases hTypeII with ⟨U, W1, W2, U1, U0, hPsrc, hCond, hComm, hNorm, hF⟩
      have hTypeII' : typeIIDefinitionData T TF :=
        ⟨U, W1, W2, U1, U0, hPsrc, hCond, hComm, hNorm, hF⟩
      have hTT_eq : TT = TF :=
        theorem_8_18_msChoiceSource_eq_mf_of_typeII hTT hTypeII'
      have hATTF :
          AT = section8CentralizerUnion (ambientDerivedSubgroup T) TF := by
        simpa [hTT_eq] using hAT
      have hA1TF : A1T = a1Set TF := by
        simpa [hTT_eq] using hA1T
      refine ⟨U, ?_⟩
      exact ⟨hNotation,
        Or.inr ⟨⟨W1, W2, U1, U0, hPsrc, hCond, hComm, hNorm, hF⟩,
          hATTF, hA1TF⟩⟩
    · exact False.elim (hxNotA1T (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inl hTypeIII)).2
        simpa [hA_eq_A1] using hxAT))
    · exact False.elim (hxNotA1T (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inr (Or.inl hTypeIV))).2
        simpa [hA_eq_A1] using hxAT))
    · exact False.elim (hxNotA1T (by
        have hA_eq_A1 : AT = A1T := (hLate (Or.inr (Or.inr hTypeV))).2
        simpa [hA_eq_A1] using hxAT))


private theorem theorem_8_18_unique_overgroup_right_of_inter
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    {x : G} (hx : x ∈ A1S ∩ AT) :
    section9MaximalSubgroupsContaining
      (Subgroup.centralizer ({x} : Set G)) = {T} := by
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := hData
  rcases hData with ⟨_hNonconj, _hS10, _hSmem, hT10, _hTmem, _hS14, _hT14⟩
  rcases theorem_8_18_prime_consequences_of_nonconj (G := G) hData' hx with
    ⟨hcop, hxNotA1T⟩
  rcases theorem_8_18_right_theorem_8_12_source_data_of_diff
      (G := G) hT10 hx.2 hxNotA1T with
    ⟨U, hSrc12⟩
  exact theorem_8_12_unique_maximal_of_source_diff_coprime
    (G := G) (M := T) (MF := TF) (U := U) (Ms := TT)
    (A := AT) (A0 := A0T) (A1 := A1T) hSrc12 ⟨hx.2, hxNotA1T⟩ hcop

private theorem theorem_8_18_support_and_centralizer_of_unique
    {G : Type u} [Group G] [Finite G]
    {S T : Subgroup G} {A0S A1S DS : Set G} {x : G}
    (hNonconj : ¬ section16ConjugateSubgroupsIn ⊤ S T)
    (hSmax : S ∈ section9MaximalSubgroups G)
    (hA1SA0S : A1S ⊆ A0S)
    (hDS : DS = section8DSet S A0S)
    (hxA1S : x ∈ A1S)
    (hUnique :
      section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {T}) :
    supportsSubgroupSource S T DS ∧
      ¬ Subgroup.centralizer ({x} : Set G) ≤ S ∧
        Subgroup.centralizer ({x} : Set G) ≤ T := by
  classical
  have hTmem :
      T ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
    rw [hUnique]
    simp
  have hNotS : ¬ Subgroup.centralizer ({x} : Set G) ≤ S := by
    intro hCentS
    have hSmem :
        S ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      ⟨hSmax, hCentS⟩
    have hS_eq_T : S = T := by
      have hSsingleton : S ∈ ({T} : Set (Subgroup G)) := by
        simpa [hUnique] using hSmem
      simpa using hSsingleton
    exact hNonconj ⟨1, by simp, by simp [section8_conjBy_one, hS_eq_T]⟩
  have hxDS : x ∈ DS := by
    rw [hDS]
    exact ⟨hA1SA0S hxA1S, hNotS⟩
  exact ⟨⟨hTmem.1, x, hxDS, hTmem.2⟩, hNotS, hTmem.2⟩

private theorem theorem_8_18_part_a_of_unique
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hUnique :
      ∀ x : G, x ∈ A1S ∩ AT →
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {T}) :
    (supportsSubgroupSource S T DS ↔ (A1S ∩ AT).Nonempty) ∧
      (∀ x : G, x ∈ A1S ∩ AT →
        ¬ Subgroup.centralizer ({x} : Set G) ≤ S ∧
          Subgroup.centralizer ({x} : Set G) ≤ T) := by
  rcases hData with ⟨hNonconj, hS10, hSmem, hT10, hTmem, hS14, hT14⟩
  rcases hS10 with ⟨hSmax, hSF, hSS, hA1S, hScases⟩
  rcases hS14 with
    ⟨hA1SA, hASA0S, hDS, hRSbot, hSUnique, hRSeq,
      htildeAS, htildeA0S, htildeA1S⟩
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT :=
    ⟨hNonconj, ⟨hSmax, hSF, hSS, hA1S, hScases⟩, hSmem, hT10, hTmem,
      ⟨hA1SA, hASA0S, hDS, hRSbot, hSUnique, hRSeq,
        htildeAS, htildeA0S, htildeA1S⟩,
      hT14⟩
  have hA1SA0S : A1S ⊆ A0S := fun x hx => hASA0S (hA1SA hx)
  constructor
  · constructor
    · intro hSupp
      exact theorem_8_18_support_implies_inter_nonempty (G := G) hData' hSupp
    · intro hInter
      rcases hInter with ⟨x, hx⟩
      exact (theorem_8_18_support_and_centralizer_of_unique
        (G := G) (S := S) (T := T) (A0S := A0S) (A1S := A1S) (DS := DS)
        (x := x) hNonconj hSmax hA1SA0S hDS hx.1 (hUnique x hx)).1
  · intro x hx
    exact (theorem_8_18_support_and_centralizer_of_unique
      (G := G) (S := S) (T := T) (A0S := A0S) (A1S := A1S) (DS := DS)
      (x := x) hNonconj hSmax hA1SA0S hDS hx.1 (hUnique x hx)).2

private theorem theorem_8_18_support_conjugate_of_tilde_inter_nonempty
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hInter : (tildeA1S ∩ tildeAT).Nonempty) :
    ∃ g : G, supportsSubgroupSource S (T.conjBy g) DS := by
  classical
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := hData
  rcases hData with ⟨hNonconj, hS10, _hSmem, hT10, _hTmem, hS14, _hT14⟩
  rcases hS10 with ⟨hSmax, hSF, hSS, hA1S, hScases⟩
  rcases hT10 with ⟨hTmax, hTF, hTT, hA1T, hTcases⟩
  rcases hS14 with
    ⟨hA1SA, hASA0S, hDS, hRSbot, hSUnique, hRSeq,
      htildeAS, htildeA0S, htildeA1S⟩
  rcases hInter with ⟨y, hy⟩
  rcases theorem_8_18_tilde_inter_left_mem_zpowers_conj (G := G) hData' hy with
    ⟨a, b, c, haDiff, hbA1S, _hRTa, hbPow⟩
  let z : G := c * b * c⁻¹
  have hb_ne : b ≠ 1 := by
    have hbSS_ne : b ∈ SS ∧ b ≠ 1 := by
      simpa [hA1S, a1Set, section16NonidentityElements] using hbA1S
    exact hbSS_ne.2
  have hz_ne : z ≠ 1 := by
    intro hz_one
    apply hb_ne
    have hz_back := congrArg (fun t : G => c⁻¹ * t * c) hz_one
    simpa [z, mul_assoc] using hz_back
  have hzPow : z ∈ Subgroup.zpowers a := by
    exact theorem_8_18_mem_conj_zpowers_of_mem_zpowers_conj (G := G) hbPow
  have hT10' : notation_8_10_source_data T TF TT AT A0T A1T :=
    ⟨hTmax, hTF, hTT, hA1T, hTcases⟩
  have hzAT : z ∈ AT :=
    theorem_8_18_mem_AT_of_zpowers_diff (G := G) hT10' haDiff hzPow hz_ne
  have hPrimeDisj : Disjoint (subgroupPrimeSet SS) (subgroupPrimeSet TT) :=
    theorem_8_18_prime_disjoint_of_nonconj (G := G) hData'
  have hbCop : Nat.Coprime (orderOf b) (Nat.card TT) :=
    theorem_8_18_order_coprime_of_prime_disjoint hA1S hPrimeDisj hbA1S
  have hzOrder : orderOf z = orderOf b := by
    simpa [z, MulAut.conj_apply] using (MulAut.conj c).orderOf_eq b
  have hzCop : Nat.Coprime (orderOf z) (Nat.card TT) := by
    simpa [hzOrder] using hbCop
  have hzNotA1T : z ∉ A1T :=
    theorem_8_18_not_mem_A1_of_order_coprime hA1T hzCop hz_ne
  rcases theorem_8_18_right_theorem_8_12_source_data_of_diff
      (G := G) hT10' hzAT hzNotA1T with
    ⟨U, hSrc12⟩
  have hUniqueZ :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({z} : Set G)) = {T} :=
    theorem_8_12_unique_maximal_of_source_diff_coprime
      (G := G) (M := T) (MF := TF) (U := U) (Ms := TT)
      (A := AT) (A0 := A0T) (A1 := A1T)
      hSrc12 ⟨hzAT, hzNotA1T⟩ hzCop
  have hUniqueB :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer ({b} : Set G)) = {T.conjBy c⁻¹} :=
    theorem_8_18_unique_conj_back (G := G) hTmax (z := z) (b := b) (c := c) rfl hUniqueZ
  have hA1SA0S : A1S ⊆ A0S := fun x hx => hASA0S (hA1SA hx)
  have hNonconjConj :
      ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) S (T.conjBy c⁻¹) :=
    theorem_8_18_nonconj_right_conjBy (G := G) c⁻¹ hNonconj
  refine ⟨c⁻¹, ?_⟩
  exact (theorem_8_18_support_and_centralizer_of_unique
    (G := G) (S := S) (T := T.conjBy c⁻¹) (A0S := A0S)
    (A1S := A1S) (DS := DS) (x := b)
    hNonconjConj hSmax hA1SA0S hDS hbA1S hUniqueB).1

private theorem theorem_8_18_support_conjugate_implies_tilde_inter_nonempty
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT) :
    (∃ g : G, supportsSubgroupSource S (T.conjBy g) DS) →
      (tildeA1S ∩ tildeAT).Nonempty := by
  rintro ⟨g, hSupp⟩
  rcases hData with ⟨hNonconj, hS10, hSmem, hT10, hTmem, hS14, hT14⟩
  rcases hT10 with ⟨hTmax, hTF, hTT, hA1T, hTcases⟩
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT :=
    ⟨hNonconj, hS10, hSmem, ⟨hTmax, hTF, hTT, hA1T, hTcases⟩,
      hTmem, hS14, hT14⟩
  rcases hTT with hTypeIChoice | hNotTypeI
  · exact theorem_8_18_support_conj_implies_tilde_inter_of_right_typeI
      (G := G) hData' hTypeIChoice.1 hSupp
  · have hTnotI : ¬ typeIDefinitionData T TF :=
      theorem_8_18_not_typeI_of_msChoiceSource_tail hNotTypeI
    have hT10Tail : notation_8_10_source_data T TF TT AT A0T A1T :=
      ⟨hTmax, hTF, Or.inr hNotTypeI, hA1T, hTcases⟩
    rcases hS14 with
      ⟨_hA1SA, _hASA0S, hDS, _hRSbot, _hSUnique, _hRSeq,
        _htildeAS, _htildeA0S, _htildeA1S⟩
    rcases hSupp with ⟨hTgmax, x, hxD, hxCentTg⟩
    have h13S :=
      (theorem_8_13 (G := G) S SF SS AS A0S A1S A0S)
        (inferInstance : IsMinCE G) hS10 (Or.inr rfl)
    have hxD' : x ∈ section8DSet S A0S := by
      simpa [hDS] using hxD
    have hxA1S : x ∈ A1S := h13S.2.1 hxD'
    have hTgmem :
        T.conjBy g ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      ⟨hTgmax, hxCentTg⟩
    rcases h13S.2.2.2 x hxD' (T.conjBy g) hTgmem with ⟨LF, hSuppData⟩
    rcases hSuppData with
      ⟨_hTgmax', hLF, _hUnique, _hSemiT, _hSemiC, _hCoprime, hCases⟩
    rcases hCases with hTypeIConj | hTypeIIConj
    · exact False.elim
        (hTnotI
          (theorem_8_18_typeIDefinitionData_conj_back
            (G := G) (M := T) (MF := TF) (LF := LF) g hTF hLF hTypeIConj.1))
    · have hxATback : g⁻¹ * x * g ∈ AT :=
        theorem_8_18_support_conclusion_conj_back_mem_AT_of_non_typeI_typeII_case
          (G := G) (T := T) (TF := TF) (TT := TT) (LF := LF)
          (AT := AT) (A0T := A0T) (A1T := A1T) (x := x) (g := g)
          hT10Tail hTnotI hLF hTypeIIConj.2.1
      refine ⟨x, ?_, ?_⟩
      · exact theorem_8_18_mem_tildeA1S_of_mem_A1S (G := G) hData' hxA1S
      · have hxTilde :
            g * (g⁻¹ * x * g) * g⁻¹ ∈ tildeAT :=
          theorem_8_18_mem_tildeAT_of_conj_mem_AT
            (G := G) (hData := hData') (a := g⁻¹ * x * g) (g := g) hxATback
        simpa [mul_assoc] using hxTilde

private theorem theorem_8_18_left_tilde_inter_support_coprime
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hInter : (tildeA1S ∩ tildeAT).Nonempty) :
    ∀ a : G, a ∈ A0S →
      Nat.Coprime (Nat.card TT) (Nat.card (elementCentralizerIn S a)) := by
  classical
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := hData
  rcases hData with ⟨_hNonconj, hS10, _hSmem, hT10, _hTmem, _hS14, _hT14⟩
  rcases hT10 with ⟨_hTmax, hTF, hTT, _hA1T, _hTcases⟩
  rcases hInter with ⟨y0, hy0⟩
  rcases theorem_8_18_tildeAT_witness_diff_A1_of_inter (G := G) hData' hy0 with
    ⟨aT, haTDiff, _hyaT, _hRTaT⟩
  have hTT_eq_TF : TT = TF := by
    rcases theorem_8_18_right_typeI_or_typeII_of_diff
        (G := G) ⟨_hTmax, hTF, hTT, _hA1T, _hTcases⟩
        haTDiff.1 haTDiff.2 with hTypeI | hTypeII
    · exact theorem_8_18_msChoiceSource_eq_mf_of_typeI hTT hTypeI
    · exact theorem_8_18_msChoiceSource_eq_mf_of_typeII hTT hTypeII
  rcases theorem_8_18_support_conjugate_of_tilde_inter_nonempty
      (G := G) hData' ⟨y0, hy0⟩ with
    ⟨g, hSupp⟩
  rcases hSupp with ⟨hTgmax, x, hxD, hxCentTg⟩
  have h13S :=
    (theorem_8_13 (G := G) S SF SS AS A0S A1S A0S)
      (inferInstance : IsMinCE G) hS10 (Or.inr rfl)
  rcases _hS14 with
    ⟨_hA1SA, _hASA0S, hDS, _hRSbot, _hSUnique, _hRSeq,
      _htildeAS, _htildeA0S, _htildeA1S⟩
  have hxD' : x ∈ section8DSet S A0S := by
    simpa [hDS] using hxD
  have hTgmem :
      T.conjBy g ∈
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
    ⟨hTgmax, hxCentTg⟩
  rcases h13S.2.2.2 x hxD' (T.conjBy g) hTgmem with ⟨LF, hSuppData⟩
  rcases hSuppData with
    ⟨_hTgmax', hLF, _hUnique, _hSemiT, _hSemiC, hCoprime, _hCases⟩
  have hTFg : section16MFSubgroup (T.conjBy g) (TF.conjBy g) :=
    theorem_8_18_mfSubgroup_conjBy (G := G) g hTF
  have hLF_eq : LF = TF.conjBy g :=
    theorem_8_18_mfSubgroup_eq (G := G) hLF hTFg
  have hcardLF : Nat.card LF = Nat.card TT := by
    calc
      Nat.card LF = Nat.card (TF.conjBy g) := by rw [hLF_eq]
      _ = Nat.card TF := section11_card_conjBy (G := G) TF g
      _ = Nat.card TT := by rw [hTT_eq_TF]
  intro a haA0S
  simpa [hcardLF] using hCoprime a haA0S

private theorem theorem_8_18_not_right_tilde_inter_of_left
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT)
    (hLeft : (tildeA1S ∩ tildeAT).Nonempty) :
    ¬ (tildeA1T ∩ tildeAS).Nonempty := by
  classical
  intro hRight
  have hData' : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := hData
  have hSwap :
      theorem_8_18_source_data T S TF SF TT SS
        AT A0T A1T DT tildeAT tildeA0T tildeA1T
        AS A0S A1S DS tildeAS tildeA0S tildeA1S RT RS :=
    theorem_8_18_source_data_swap (G := G) hData'
  have hCoprime :=
    theorem_8_18_left_tilde_inter_support_coprime (G := G) hData' hLeft
  rcases hData with ⟨_hNonconj, hS10, _hSmem, hT10, _hTmem, hS14, _hT14⟩
  rcases hS14 with
    ⟨hA1SA, hASA0S, _hDS, _hRSbot, _hSUnique, _hRSeq,
      _htildeAS, _htildeA0S, _htildeA1S⟩
  rcases hT10 with ⟨_hTmax, _hTF, _hTT, hA1T, _hTcases⟩
  rcases hRight with ⟨y, hy⟩
  rcases theorem_8_18_tilde_inter_left_mem_zpowers_conj (G := G) hSwap hy with
    ⟨a, b, c, haASDiff, hbA1T, _hRSa, hbPow⟩
  let z : G := c * b * c⁻¹
  have hzPow : z ∈ Subgroup.zpowers a :=
    theorem_8_18_mem_conj_zpowers_of_mem_zpowers_conj (G := G) hbPow
  have hb_ne : b ≠ 1 := by
    have hbTT_ne : b ∈ TT ∧ b ≠ 1 := by
      simpa [hA1T, a1Set, section16NonidentityElements] using hbA1T
    exact hbTT_ne.2
  have hz_ne : z ≠ 1 := by
    intro hz_one
    apply hb_ne
    have hz_back := congrArg (fun t : G => c⁻¹ * t * c) hz_one
    simpa [z, mul_assoc] using hz_back
  have haA0S : a ∈ A0S := hASA0S haASDiff.1
  have haS : a ∈ S := theorem_8_18_mem_A_mem_left hS10 haASDiff.1
  have hzS : z ∈ S := (Subgroup.zpowers_le.2 haS) hzPow
  have hzCentA : z ∈ Subgroup.centralizer ({a} : Set G) := by
    rcases Subgroup.mem_zpowers_iff.mp hzPow with ⟨n, hzEq⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hzEq]
    exact ((Commute.refl a).zpow_left n).eq
  have hzCent : z ∈ elementCentralizerIn S a := ⟨hzS, hzCentA⟩
  have hzOrderDvdCent :
      orderOf z ∣ Nat.card (elementCentralizerIn S a) :=
    Subgroup.orderOf_dvd_natCard (elementCentralizerIn S a) hzCent
  have hbTT : b ∈ TT := by
    have hbTT_ne : b ∈ TT ∧ b ≠ 1 := by
      simpa [hA1T, a1Set, section16NonidentityElements] using hbA1T
    exact hbTT_ne.1
  have hbOrderDvdTT : orderOf b ∣ Nat.card TT :=
    Subgroup.orderOf_dvd_natCard TT hbTT
  have hzOrder : orderOf z = orderOf b := by
    simpa [z, MulAut.conj_apply] using (MulAut.conj c).orderOf_eq b
  have hzOrderDvdTT : orderOf z ∣ Nat.card TT := by
    simpa [hzOrder] using hbOrderDvdTT
  have hzOrderNeOne : orderOf z ≠ 1 := by
    intro hzOrderOne
    exact hz_ne (orderOf_eq_one_iff.mp hzOrderOne)
  have hzOrderGt : 1 < orderOf z :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Nat.ne_of_gt (orderOf_pos z), hzOrderNeOne⟩
  exact (Nat.not_coprime_of_dvd_of_dvd hzOrderGt hzOrderDvdTT hzOrderDvdCent)
    (hCoprime a haA0S)

private theorem theorem_8_18_tilde_disjoint_or
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {S T SF TF SS TT : Subgroup G}
    {AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G}
    {RS RT : G → Subgroup G}
    (hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT) :
    Disjoint tildeA1S tildeAT ∨ Disjoint tildeA1T tildeAS := by
  by_cases hLeft : (tildeA1S ∩ tildeAT).Nonempty
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    ext y
    constructor
    · intro hy
      exact False.elim
        (theorem_8_18_not_right_tilde_inter_of_left
          (G := G) hData hLeft ⟨y, hy⟩)
    · intro hy
      exact False.elim hy
  · left
    rw [Set.disjoint_iff_inter_eq_empty]
    ext y
    constructor
    · intro hy
      exact False.elim (hLeft ⟨y, hy⟩)
    · intro hy
      exact False.elim hy

public theorem theorem_8_18
    {G : Type u} [Group G] [Finite G]
    (S T SF TF SS TT : Subgroup G)
    (AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G)
    (AT A0T A1T DT tildeAT tildeA0T tildeA1T : Set G)
    (RS RT : G → Subgroup G) :
    theorem_8_18_statement S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT := by
  intro hG hDataNotation
  letI : IsMinCE G := hG
  have hData : theorem_8_18_source_data S T SF TF SS TT
      AS A0S A1S DS tildeAS tildeA0S tildeA1S
      AT A0T A1T DT tildeAT tildeA0T tildeA1T RS RT :=
    theorem_8_18_source_data_of_notation_data hDataNotation
  have hUnique :
      ∀ x : G, x ∈ A1S ∩ AT →
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) = {T} := by
    intro x hx
    exact theorem_8_18_unique_overgroup_right_of_inter
      (G := G) (S := S) (T := T) (SF := SF) (TF := TF) (SS := SS) (TT := TT)
      (AS := AS) (A0S := A0S) (A1S := A1S) (DS := DS)
      (tildeAS := tildeAS) (tildeA0S := tildeA0S) (tildeA1S := tildeA1S)
      (AT := AT) (A0T := A0T) (A1T := A1T) (DT := DT)
      (tildeAT := tildeAT) (tildeA0T := tildeA0T) (tildeA1T := tildeA1T)
      (RS := RS) (RT := RT) hData hx
  have hPartA :=
    theorem_8_18_part_a_of_unique
      (G := G) (S := S) (T := T) (SF := SF) (TF := TF) (SS := SS) (TT := TT)
      (AS := AS) (A0S := A0S) (A1S := A1S) (DS := DS)
      (tildeAS := tildeAS) (tildeA0S := tildeA0S) (tildeA1S := tildeA1S)
      (AT := AT) (A0T := A0T) (A1T := A1T) (DT := DT)
      (tildeAT := tildeAT) (tildeA0T := tildeA0T) (tildeA1T := tildeA1T)
      (RS := RS) (RT := RT) hData hUnique
  refine ⟨hPartA.1, hPartA.2, ?_, ?_⟩
  · constructor
    · exact theorem_8_18_support_conjugate_implies_tilde_inter_nonempty
        (G := G) (S := S) (T := T) (SF := SF) (TF := TF) (SS := SS) (TT := TT)
        (AS := AS) (A0S := A0S) (A1S := A1S) (DS := DS)
        (tildeAS := tildeAS) (tildeA0S := tildeA0S) (tildeA1S := tildeA1S)
        (AT := AT) (A0T := A0T) (A1T := A1T) (DT := DT)
        (tildeAT := tildeAT) (tildeA0T := tildeA0T) (tildeA1T := tildeA1T)
        (RS := RS) (RT := RT) hData
    · intro hInter
      exact theorem_8_18_support_conjugate_of_tilde_inter_nonempty
        (G := G) (S := S) (T := T) (SF := SF) (TF := TF) (SS := SS) (TT := TT)
        (AS := AS) (A0S := A0S) (A1S := A1S) (DS := DS)
        (tildeAS := tildeAS) (tildeA0S := tildeA0S) (tildeA1S := tildeA1S)
        (AT := AT) (A0T := A0T) (A1T := A1T) (DT := DT)
        (tildeAT := tildeAT) (tildeA0T := tildeA0T) (tildeA1T := tildeA1T)
        (RS := RS) (RT := RT) hData hInter
  · exact theorem_8_18_tilde_disjoint_or
      (G := G) (S := S) (T := T) (SF := SF) (TF := TF) (SS := SS) (TT := TT)
      (AS := AS) (A0S := A0S) (A1S := A1S) (DS := DS)
      (tildeAS := tildeAS) (tildeA0S := tildeA0S) (tildeA1S := tildeA1S)
      (AT := AT) (A0T := A0T) (A1T := A1T) (DT := DT)
      (tildeAT := tildeAT) (tildeA0T := tildeA0T) (tildeA1T := tildeA1T)
      (RS := RS) (RT := RT) hData

end CFSG.Section8
