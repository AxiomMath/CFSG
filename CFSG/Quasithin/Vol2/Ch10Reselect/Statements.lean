module

public import CFSG.Quasithin.Vol2.Ch10SecA1010C
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

section Defs

variable {G : Type} [Group G]

@[expose] def Concl326A (T L I : Subgroup G) : Prop :=
  ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
    fsuUL T L I ⊔ CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I = fsuVM T L I ∧
    (fsuUL T L I ⊔ fsuCVM T L I) ⊓ (CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I) =
      fsuCVM T L I ∧
    fsuUL T L I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G)

@[expose] def Case3_2_6_ivA (T L I : Subgroup G) [IsMulCommutative ↥(fsuVM T L I)] : Prop :=
  Concl326A T L I ∧ Case3_2_6_iv T L I

@[expose] def Concl326ThreeIvA (T L I : Subgroup G) [IsMulCommutative ↥(fsuVM T L I)] : Prop :=
  Concl326A T L I ∧ Concl326ThreeIv T L I

theorem concl326ThreeIvA_iff (T L I : Subgroup G) [IsMulCommutative ↥(fsuVM T L I)] :
    Concl326ThreeIvA T L I ↔ Case3_2_6_ivA T L I :=
  Iff.rfl

theorem concl326A_of_cab [Finite G] {T L V₀ : Subgroup G}
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] (h : Concl326Cab T L V₀) :
    Concl326A T L V₀ :=
  h.1

end Defs

section Statements

variable {G : Type} [Group G] [Finite G]

@[expose] def Concl326ThreeCA (T L I : Subgroup G) : Prop :=
  (∃ x ∈ T, Concl326Three T L (CFSG.conjugate I x)) ∨
    ∃ _ : IsMulCommutative ↥(fsuVM T L I), Concl326ThreeIvA T L I

@[expose] def Concl701FourA (T L I : Subgroup G) : Prop :=
  L < fsuL0 T L ∧ Shape701 L ∧ Concl326ThreeCA T L I

theorem concl326ThreeC_of_A {T L I : Subgroup G} (h : Concl326ThreeCA T L I) :
    Concl326ThreeC T L I :=
  h.imp_right fun ⟨hc, _, hiv⟩ => ⟨hc, hiv⟩

theorem concl701Four_of_A {T L I : Subgroup G} (h : Concl701FourA T L I) : Concl701Four T L I :=
  ⟨h.1, h.2.1, concl326ThreeC_of_A h.2.2⟩

@[expose] def Stmt7_0_1A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I →
    ∃ _ : IsMulCommutative ↥(fsuV T I), IsElemAbelian 2 (fsuV T I) ∧
      fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      (Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I ∨ Concl701FourA T L I)

theorem stmt7_0_1_of_A (h : Stmt7_0_1A) : Stmt7_0_1 := by
  intro G _ _ T L I hfsu
  obtain ⟨hc, hab, hn, h4⟩ := h G T L I hfsu
  exact ⟨hc, hab, hn, h4.imp_right fun h => h.imp_right fun h => h.imp_right
    concl701Four_of_A⟩

end Statements

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

@[expose] def Stmt10_1_0CA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I → Concl326ThreeCA T L I

theorem rows_false_of_concl {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) (hc : IsMulCommutative ↥(fsuV T I))
    (hnFF : AS_p696_notFF) (hconcl : Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I)
    (hrow : (∃ n : ℕ, Row711OmegaPlus T L I n) ∨ Row711L3Wreath T L I) : False := by
  rcases hconcl with hFF | hJ4 | ⟨a, ha, hOrth⟩
  · exact hnFF G T L I hfsu hlt hc hrow hFF
  · have hV := hJ4.2.2.1
    rcases hrow with ⟨n, hn⟩ | hw
    · rw [SecA.card_fsuV_of_omegaPlus hn] at hV
      have := Nat.pow_right_injective (le_refl 2) hV
      omega
    · rw [SecA.card_fsuV_of_l3Wreath hw] at hV
      norm_num at hV
  · have hA := SecA.card_autOn_of_orth hOrth
    rcases hrow with ⟨n, hn⟩ | hw
    · rw [SecA.card_autOn_of_omegaPlus hn] at hA
      exact SecA.omegaPlus_orth_card_ne hn.2.1 (by omega) hA
    · rw [SecA.card_autOn_of_l3Wreath hw] at hA
      exact SecA.l3Wreath_orth_card_ne ha hA

theorem stmt10_1_0CA_of (h326 : Stmt3_2_6C) (hnFF : AS_p696_notFF) : Stmt10_1_0CA := by
  intro G _ _ T L I hfsu hlt hc hconcl
  rcases stmt10_1_0C_of h326 hnFF G T L I hfsu hlt hc hconcl with hx | ⟨hcVM, hiv⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hcVM, ?_, hiv⟩
    obtain ⟨⟨hcV, -⟩, hcVM', -, hcases⟩ := h326 G T L I hfsu hlt.ne
    rcases hcases with ⟨n, K, _, _, hcard, hlie, hV0, hVVM, hreal⟩ | ⟨-, hV0, hVVM, hreal⟩ |
      ⟨⟨ha, -, -⟩, -⟩
    ·
      refine (rows_false_of_concl hfsu hlt hc hnFF hconcl (Or.inl ⟨n, hlt,
        two_le_of_lieModel_psl_two hlie, K, inferInstance, inferInstance, hcard, ?_⟩)).elim
      rw [← tensorNatModel_eq]
      exact realizesMod_of_eq hVVM _ _ hreal
    ·
      refine (rows_false_of_concl hfsu hlt hc hnFF hconcl (Or.inr ⟨hlt, ?_⟩)).elim
      rw [← tensorNatModel_eq]
      exact realizesMod_of_eq hVVM _ _ hreal
    · exact ha

@[expose] def Ch10Reselect : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    ∀ _ : IsMulCommutative ↥(fsuVM T L I), Concl326A T L I → Case3_2_6_iv T L I →
      ∃ J : Subgroup G, FSU G T L J ∧ J ≤ fsuVM T L I ∧ fsuVM T L J = fsuV T J ∧
        fsuUL T L J = J ∧
        ∀ x ∈ T, ∀ _ : IsMulCommutative ↥(fsuVM T L (CFSG.conjugate J x)),
          ¬ Case3_2_6_iv T L (CFSG.conjugate J x)

theorem exists_hyp10C_reselect (hfsu : StmtFSUChoice) (h701 : Stmt7_0_1A)
    (h1010 : Stmt10_1_0CA) (hR : Ch10Reselect) {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hq : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hmax : quasithinIsMaximalLocal T L) (hf : quasithinIsFaithfulLocal T L)
    (hqs : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hnot : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ I : Subgroup G, Hyp10 G T L I := by
  obtain ⟨I, hI⟩ := hfsu G T L hs hn hq hT hmax hf hqs
  have hlt : L < fsuL0 T L := by
    refine lt_of_le_of_ne (le_conjClosure L T) fun h => hnot ?_
    have h' : L = conjClosure L T := h
    have hT0 : T ≤ Subgroup.normalizer (conjClosure L T : Set G) := le_normalizer_conjClosure L T
    rwa [← h'] at hT0
  have hfin : ∀ I' : Subgroup G, FSU G T L I' → (∃ x ∈ T, Concl326Three T L (CFSG.conjugate I' x)) →
      ∃ I'' : Subgroup G, Hyp10 G T L I'' := by
    rintro I' hI' ⟨x, hx, h3⟩
    exact ⟨CFSG.conjugate I' x, ⟨fsu_conjugate hI' hx, hnot, hlt, h3⟩⟩
  have h3 : Concl326ThreeCA T L I := by
    obtain ⟨hc, -, -, h4⟩ := h701 G T L I hI
    rcases h4 with h | h | h | h
    · exact h1010 G T L I hI hlt hc (Or.inl h)
    · exact h1010 G T L I hI hlt hc (Or.inr (Or.inl h))
    · exact h1010 G T L I hI hlt hc (Or.inr (Or.inr h))
    · exact h.2.2
  rcases h3 with h3 | ⟨hcVM, hA, hiv⟩
  · exact hfin I hI h3
  ·
    obtain ⟨J, hJ, -, -, -, hJiv⟩ := hR G T L I hI hlt hcVM hA hiv
    have hJ3 : Concl326ThreeCA T L J := by
      obtain ⟨hc, -, -, h4⟩ := h701 G T L J hJ
      rcases h4 with h | h | h | h
      · exact h1010 G T L J hJ hlt hc (Or.inl h)
      · exact h1010 G T L J hJ hlt hc (Or.inr (Or.inl h))
      · exact h1010 G T L J hJ hlt hc (Or.inr (Or.inr h))
      · exact h.2.2
    rcases hJ3 with h3 | ⟨hcVMJ, -, hivJ⟩
    · exact hfin J hJ h3
    · exfalso
      have h1 := hJiv 1 T.one_mem
      rw [SecA.conjugate_one] at h1
      exact h1 hcVMJ hivJ

theorem stmt10_0_1_of_stepsR (hfsu : StmtFSUChoice) (h701 : Stmt7_0_1A) (h1010 : Stmt10_1_0CA)
    (hR : Ch10Reselect) (h10213 : Stmt10_2_13) (hclose : StmtClose10) : Stmt10_0_1 := by
  intro G _ _ T L hs hn hq hT hmax hf hqs
  by_contra hnot
  obtain ⟨I, hI⟩ := exists_hyp10C_reselect hfsu h701 h1010 hR hs hn hq hT hmax hf hqs hnot
  obtain ⟨K, hKmax, hKf, hKqs, hKnot, ⟨eA⟩⟩ := hclose G T L I hI
  obtain ⟨J, hJ⟩ := exists_hyp10C_reselect hfsu h701 h1010 hR hs hn hq hT hKmax hKf hKqs hKnot
  obtain ⟨⟨⟨eL⟩, -⟩, -, -⟩ := h10213 G T K J hJ
  exact not_sl_three_two_equiv_alternating_five (eL.symm.trans eA)

@[expose] def Ch10CaseIVFFA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Concl701FF T L I ∨ Concl701FourA T L I →
      ∀ _ : IsMulCommutative ↥(fsuVM T L I), ¬ Case3_2_6_ivA T L I

theorem ch10CaseIVFFA_of_stmt10_0_1 (h : Stmt10_0_1) : Ch10CaseIVFFA := by
  intro G _ _ T L I hfsu hlt
  exfalso
  have hT := h G T L hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow hfsu.maximal
    hfsu.faithful hfsu.quasisimple
  exact hlt.ne (le_antisymm (le_conjClosure L T) (conjClosure_le fun _ hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (hT hg) z).mp hz))

end CFSG.Quasithin.Vol2.Ch10
