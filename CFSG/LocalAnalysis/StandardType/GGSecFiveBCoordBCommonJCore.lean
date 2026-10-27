module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJAsm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowLinTwo
import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveBCoordBCommonJCoreInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J → B = Bs →
      ∀ (n : ℕ), 4 ≤ n → ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
        GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L →
          GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
            ((GGSecFiveBCoordDense eta i0 D ∧
                LargeEvenMarking J
                  (fun labJ _ _ _ _ _ => GGSecFiveBCoordBJDenseLabelCore L n p lab labJ)) ∨
              (GGSecFiveBCoordSparse eta i0 D ∧
                LargeEvenMarking J
                  (fun labJ _ _ _ _ _ => GGSecFiveBCoordBJSparseLabel n p lab labJ)))) p Bs L := by
  intro G _ _ p B Bs x L D J hcfg hB n hn eta i0 hA hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 3 ≤ m := by omega
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hcomm, lab, hlam, hraw⟩ := hL
  have hX : (GGSecFiveBCoordDense eta i0 D ∧
      LargeEvenMarking J (fun labJ _ _ _ _ _ =>
        GGSecFiveBCoordBJDenseLabelCore L (m + 1) p lab labJ)) ∨
    (GGSecFiveBCoordSparse eta i0 D ∧
      LargeEvenMarking J (fun labJ _ _ _ _ _ =>
        GGSecFiveBCoordBJSparseLabel (m + 1) p lab labJ)) := by
    obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, -, θ₀, hblab, -, -⟩ := hQ₀
    rcases hblab with ⟨hbc, hrank, hq⟩ | ⟨htwD, hrank, hq⟩ |
      ⟨hD, hrank, hodd, hn1, hp3⟩ | ⟨hAtag, hrA, hn1, hp3⟩
    ·
      obtain ⟨tag, rank, nlab⟩ := lab
      dsimp only at hbc hrank
      have hrankm : rank = m := by omega
      rw [hrankm] at hraw ⊢
      have hdata : ∃ (K : Type) (_ : Field K) (_ : Finite K),
          Nat.card K = 2 ^ nlab ∧
          IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K m)) ∧
          (∃ a b : LargeEvenProj (LargeEvenSpGroup K m), a * b ≠ b * a) ∧
          ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSpGroup K m),
            Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
              (LargeEvenGSpSet K m),
              LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
        rcases hbc with rfl | rfl
        · dsimp only [LargeEvenRawDatumLegacy] at hraw
          obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
          obtain ⟨hRs, hna, θ, -, hBsN, hind⟩ := hQ
          exact ⟨K, hf, hfin, hK, hRs, hna, θ, hBsN, hind⟩
        · dsimp only [LargeEvenRawDatumLegacy] at hraw
          obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
          obtain ⟨hRs, hna, θ, -, hBsN, hind⟩ := hQ
          exact ⟨K, hf, hfin, hK, hRs, hna, θ, hBsN, hind⟩
      obtain ⟨K, hKfield, hKfin, hK, hRs, hna, θ, hBsN, hind⟩ := hdata
      haveI : CharP K 2 := charP_two_of_card hK
      have hI : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
          (LargeEvenGSpSet K m) ⊆ Set.range MulAut.conj := TableBSymp.sp_I_subset_inn
      rcases hq with hpq | ⟨hn1, hp3⟩
      · have hrow : GGSecFiveBNativeRow (LargeEvenProj (LargeEvenSpGroup K m)) p m
            (fun labJ => labJ = ⟨.A, m - 1, nlab⟩)
            (fun labJ => labJ = ⟨.C, m - 1, nlab⟩) :=
          ggSecFiveBNativeRow_spSplit hK hp hp2 hpq hm
        have hSD : ∀ labJ, labJ = ⟨.A, m - 1, nlab⟩ →
            GGSecFiveBCoordBJDenseLabel (m + 1) p ⟨tag, m, nlab⟩ labJ ∨
              ((tag = .B ∨ tag = .C ∨ tag = .D) ∧ m + 1 = 5 ∧ nlab = 1 ∧
                labJ = ⟨.twA, 3, 1⟩ ∧ p = 3) := by
          rintro labJ rfl
          exact Or.inl (Or.inl ⟨by tauto, hpq, rfl⟩)
        have hSS : ∀ labJ, labJ = ⟨.C, m - 1, nlab⟩ →
            GGSecFiveBCoordBJSparseLabel (m + 1) p ⟨tag, m, nlab⟩ labJ := by
          rintro labJ rfl
          exact Or.inl ⟨hbc, Or.inl rfl⟩
        have hsp : tag = .B ∨ tag = .C ∨ tag = .D → m + 1 = 5 → nlab = 1 → p = 3 →
            GGSecFiveBNativeSparseRow (LargeEvenProj (LargeEvenSpGroup K m)) p m := by
          rintro - - hn1 hp3
          rw [hn1] at hpq
          norm_num at hpq
          exact absurd hpq hp.ne_one
        exact CommonJ.ggCommonJ_core_of_rowData hcfg hB hm eta i0 hA hRs hna hI θ hBsN
          hind hrow hSD hSS hsp
      · subst hn1
        subst hp3
        have hK2 : Nat.card K = 2 := by simpa using hK
        have hrow : GGSecFiveBNativeRow (LargeEvenProj (LargeEvenSpGroup K m)) 3 m
            (fun labJ => labJ = ⟨.twA, m - 1, 1⟩)
            (fun labJ => labJ = ⟨.C, m - 1, 1⟩ ∨ (m = 3 ∧ labJ = ⟨.B2der, 0, 1⟩)) :=
          ggSecFiveBNativeRow_spTwo hK2 hm
        have hSD : ∀ labJ, labJ = ⟨.twA, m - 1, 1⟩ →
            GGSecFiveBCoordBJDenseLabel (m + 1) 3 ⟨tag, m, 1⟩ labJ ∨
              ((tag = .B ∨ tag = .C ∨ tag = .D) ∧ m + 1 = 5 ∧ 1 = 1 ∧
                labJ = ⟨.twA, 3, 1⟩ ∧ 3 = 3) := by
          rintro labJ rfl
          by_cases hm4 : m = 4
          · right
            subst hm4
            exact ⟨by tauto, rfl, rfl, rfl, rfl⟩
          · left
            refine Or.inr (Or.inl ⟨by tauto, ?_, rfl, ?_⟩)
            · norm_num
            · rintro ⟨h5, -⟩
              omega
        have hSS : ∀ labJ, labJ = ⟨.C, m - 1, 1⟩ ∨ (m = 3 ∧ labJ = ⟨.B2der, 0, 1⟩) →
            GGSecFiveBCoordBJSparseLabel (m + 1) 3 ⟨tag, m, 1⟩ labJ := by
          rintro labJ (rfl | ⟨hm3, rfl⟩)
          · exact Or.inl ⟨hbc, Or.inl rfl⟩
          · subst hm3
            exact Or.inl ⟨hbc, Or.inr ⟨rfl, rfl, rfl⟩⟩
        have hsp : tag = .B ∨ tag = .C ∨ tag = .D → m + 1 = 5 → 1 = 1 → 3 = 3 →
            GGSecFiveBNativeSparseRow (LargeEvenProj (LargeEvenSpGroup K m)) 3 m := by
          rintro - hm5 - -
          have hm4 : m = 4 := by omega
          subst hm4
          exact ggSecFiveBNativeSparseRow_spTwo hK2
        exact CommonJ.ggCommonJ_core_of_rowData hcfg hB hm eta i0 hA hRs hna hI θ hBsN
          hind hrow hSD hSS hsp
    ·
      obtain ⟨tag, rank, nlab⟩ := lab
      dsimp only at htwD hrank
      subst htwD
      have hrankm : rank = m + 1 := by omega
      rw [hrankm] at hraw ⊢
      let Q : LargeEvenRawCont := fun R _ I F =>
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
            GGSecFiveBCoordBLabel (m + 1) p ⟨.twD, m + 1, nlab⟩ ∧
              Bs ≤ Subgroup.normalizer (L : Set G) ∧
              ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
      have hrawR : LargeEvenRecipeOmegaMinus m (2 ^ nlab) Q := by
        dsimp only [LargeEvenRawDatumLegacy] at hraw
        rw [if_neg (by omega : ¬ m + 1 = 2), if_neg (by omega : ¬ m + 1 = 3)] at hraw
        exact hraw
      obtain ⟨K, hKfield, hKfin, hK, b, c, hirr, hQ⟩ := hrawR
      obtain ⟨hRs, hna, θ, -, hBsN, hind⟩ := hQ
      haveI : CharP K 2 := charP_two_of_card hK
      have hI : LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) ⊆
          Set.range MulAut.conj := fun _ hx => hx
      rcases hq with hpq | ⟨heven, hpq⟩
      · have hrow : GGSecFiveBNativeRow
            (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) p m
            (fun labJ => labJ = ⟨.A, m - 1, nlab⟩)
            (fun labJ => labJ = ⟨.twD, m, nlab⟩) :=
          ggSecFiveBNativeRow_omMinusSplit hK hp hp2 hpq hm hirr
        have hSD : ∀ labJ, labJ = ⟨.A, m - 1, nlab⟩ →
            GGSecFiveBCoordBJDenseLabel (m + 1) p ⟨.twD, m + 1, nlab⟩ labJ ∨
              ((LargeEvenLieTag.twD = .B ∨ LargeEvenLieTag.twD = .C ∨
                  LargeEvenLieTag.twD = .D) ∧ m + 1 = 5 ∧ nlab = 1 ∧
                labJ = ⟨.twA, 3, 1⟩ ∧ p = 3) := by
          rintro labJ rfl
          exact Or.inl (Or.inl ⟨Or.inr (Or.inr rfl), hpq, rfl⟩)
        have hSS : ∀ labJ, labJ = ⟨.twD, m, nlab⟩ →
            GGSecFiveBCoordBJSparseLabel (m + 1) p ⟨.twD, m + 1, nlab⟩ labJ := by
          rintro labJ rfl
          exact Or.inr (Or.inl ⟨rfl, hpq, rfl⟩)
        have hsp : (LargeEvenLieTag.twD = .B ∨ LargeEvenLieTag.twD = .C ∨
            LargeEvenLieTag.twD = .D) → m + 1 = 5 → nlab = 1 → p = 3 →
            GGSecFiveBNativeSparseRow
              (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) p m := by
          rintro (h | h | h) <;> simp at h
        exact CommonJ.ggCommonJ_core_of_rowData hcfg hB hm eta i0 hA hRs hna hI θ hBsN
          hind hrow hSD hSS hsp
      · have hmo : Odd m := by
          rw [Nat.odd_iff]
          have h' := Nat.even_iff.mp heven
          omega
        have hrow : GGSecFiveBNativeRow
            (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) p m
            (fun labJ => labJ = ⟨.twA, m - 1, nlab⟩)
            (fun labJ => labJ = ⟨.D, m, nlab⟩) :=
          ggSecFiveBNativeRow_omMinusNonsplit hK hp hp2 hpq hm hmo hirr
        have hSD : ∀ labJ, labJ = ⟨.twA, m - 1, nlab⟩ →
            GGSecFiveBCoordBJDenseLabel (m + 1) p ⟨.twD, m + 1, nlab⟩ labJ ∨
              ((LargeEvenLieTag.twD = .B ∨ LargeEvenLieTag.twD = .C ∨
                  LargeEvenLieTag.twD = .D) ∧ m + 1 = 5 ∧ nlab = 1 ∧
                labJ = ⟨.twA, 3, 1⟩ ∧ p = 3) := by
          rintro labJ rfl
          refine Or.inl (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), hpq, rfl, ?_⟩))
          rintro ⟨h5, -⟩
          rw [h5] at heven
          norm_num at heven
        have hSS : ∀ labJ, labJ = ⟨.D, m, nlab⟩ →
            GGSecFiveBCoordBJSparseLabel (m + 1) p ⟨.twD, m + 1, nlab⟩ labJ := by
          rintro labJ rfl
          exact Or.inr (Or.inr (Or.inl ⟨rfl, hpq, rfl⟩))
        have hsp : (LargeEvenLieTag.twD = .B ∨ LargeEvenLieTag.twD = .C ∨
            LargeEvenLieTag.twD = .D) → m + 1 = 5 → nlab = 1 → p = 3 →
            GGSecFiveBNativeSparseRow
              (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) p m := by
          rintro (h | h | h) <;> simp at h
        exact CommonJ.ggCommonJ_core_of_rowData hcfg hB hm eta i0 hA hRs hna hI θ hBsN
          hind hrow hSD hSS hsp
    ·
      obtain ⟨tag, rank, nlab⟩ := lab
      dsimp only at hD hrank hodd hn1 hp3
      subst hD
      have hrankm : rank = m + 1 := by omega
      rw [hrankm] at hraw ⊢
      subst hn1
      subst hp3
      let Q : LargeEvenRawCont := fun R _ I F =>
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
            GGSecFiveBCoordBLabel (m + 1) 3 ⟨.D, m + 1, 1⟩ ∧
              Bs ≤ Subgroup.normalizer (L : Set G) ∧
              ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
      have hrawR : LargeEvenRecipeOmegaPlus (m + 1) 2 Q := by
        dsimp only [LargeEvenRawDatumLegacy] at hraw
        rw [if_neg (by omega : ¬ m + 1 = 3)] at hraw
        exact hraw
      obtain ⟨K, hKfield, hKfin, hK, hQ⟩ := hrawR
      have hK2 : Nat.card K = 2 := by simpa using hK
      obtain ⟨hRs, hna, θ, -, hBsN, hind⟩ := hQ
      haveI : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
      have hI : LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (m + 1)))) ⊆
          Set.range MulAut.conj := fun _ hx => hx
      have hme : Even m := by
        rw [Nat.even_iff]
        have h' := Nat.odd_iff.mp hodd
        omega
      have hm4 : 4 ≤ m := by
        rcases hodd with ⟨k, hk⟩
        omega
      have hrow : GGSecFiveBNativeRow
          (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (m + 1)))) 3 m
          (fun labJ => labJ = ⟨.twA, m - 1, 1⟩)
          (fun labJ => labJ = ⟨.twD, m, 1⟩) :=
        ggSecFiveBNativeRow_omPlusTwo hK2 hm4 hme
      have hSD : ∀ labJ, labJ = ⟨.twA, m - 1, 1⟩ →
          GGSecFiveBCoordBJDenseLabel (m + 1) 3 ⟨.D, m + 1, 1⟩ labJ ∨
            ((LargeEvenLieTag.D = .B ∨ LargeEvenLieTag.D = .C ∨
                LargeEvenLieTag.D = .D) ∧ m + 1 = 5 ∧ 1 = 1 ∧
              labJ = ⟨.twA, 3, 1⟩ ∧ 3 = 3) := by
        rintro labJ rfl
        by_cases hm4 : m = 4
        · right
          subst hm4
          exact ⟨Or.inr (Or.inr rfl), rfl, rfl, rfl, rfl⟩
        · left
          refine Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr rfl)), ?_, rfl, ?_⟩)
          · norm_num
          · rintro ⟨h5, -⟩
            omega
      have hSS : ∀ labJ, labJ = ⟨.twD, m, 1⟩ →
          GGSecFiveBCoordBJSparseLabel (m + 1) 3 ⟨.D, m + 1, 1⟩ labJ := by
        rintro labJ rfl
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      have hsp : (LargeEvenLieTag.D = .B ∨ LargeEvenLieTag.D = .C ∨
          LargeEvenLieTag.D = .D) → m + 1 = 5 → 1 = 1 → 3 = 3 →
          GGSecFiveBNativeSparseRow
            (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (m + 1)))) 3 m := by
        rintro - hm5 - -
        have hm4 : m = 4 := by omega
        subst hm4
        exact ggSecFiveBNativeSparseRow_omPlusTwo hK2
      exact CommonJ.ggCommonJ_core_of_rowData hcfg hB hm eta i0 hA hRs hna hI θ hBsN
        hind hrow hSD hSS hsp
    ·
      obtain ⟨tag, rank, nlab⟩ := lab
      dsimp only at hAtag hrA hn1 hp3
      subst hAtag
      subst hn1
      subst hp3
      let Q : LargeEvenRawCont := fun R _ I F =>
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
            GGSecFiveBCoordBLabel (m + 1) 3 ⟨.A, rank, 1⟩ ∧
              Bs ≤ Subgroup.normalizer (L : Set G) ∧
              ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
      have hrawR : LargeEvenRecipeLinear (rank + 1) 2 Q := by
        dsimp only [LargeEvenRawDatumLegacy] at hraw
        exact hraw
      obtain ⟨K, hKfield, hKfin, hK, hQ⟩ := hrawR
      have hK2 : Nat.card K = 2 := by simpa using hK
      obtain ⟨hRs, hna, θ, -, hBsN, hind⟩ := hQ
      haveI : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
      have hd : rank + 1 = 2 * m ∨ rank + 1 = 2 * m + 1 := by omega
      have hrow : GGSecFiveBNativeRow (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)) 3 m
          (fun labJ => labJ = ⟨.A, m - 1, 2⟩)
          (fun labJ => labJ = ⟨.A, rank - 2, 1⟩) :=
        ggSecFiveBNativeRow_linTwo hK2 hm hd
      have hI : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (rank + 1)) K))
          Set.univ ⊆ Set.range MulAut.conj := by
        refine matConjImage_gl_subset_inn (d := rank + 1) ?_
        rw [Nat.card_units, hK2]
        simpa using Nat.coprime_one_left (rank + 1)
      have hSD : ∀ labJ, labJ = ⟨.A, m - 1, 2⟩ →
          GGSecFiveBCoordBJDenseLabel (m + 1) 3 ⟨.A, rank, 1⟩ labJ ∨
            ((LargeEvenLieTag.A = .B ∨ LargeEvenLieTag.A = .C ∨
                LargeEvenLieTag.A = .D) ∧ m + 1 = 5 ∧ 1 = 1 ∧
              labJ = ⟨.twA, 3, 1⟩ ∧ 3 = 3) := by
        rintro labJ rfl
        exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have hSS : ∀ labJ, labJ = ⟨.A, rank - 2, 1⟩ →
          GGSecFiveBCoordBJSparseLabel (m + 1) 3 ⟨.A, rank, 1⟩ labJ := by
        rintro labJ rfl
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      have hsp : (LargeEvenLieTag.A = .B ∨ LargeEvenLieTag.A = .C ∨
          LargeEvenLieTag.A = .D) → m + 1 = 5 → 1 = 1 → 3 = 3 →
          GGSecFiveBNativeSparseRow (LargeEvenProj (LargeEvenSLGroup (Fin (rank + 1)) K)) 3 m := by
        rintro (h | h | h) <;> simp at h
      exact CommonJ.ggCommonJ_core_of_rowData hcfg hB hm eta i0 hA hRs hna hI θ hBsN
        hind hrow hSD hSS hsp
  refine ⟨hcomm, lab, hlam, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hRs, hna, θ, hlabB, hBsN, hind⟩
  exact ⟨hRs, hna, θ, ⟨hlabB, hX⟩, hBsN, hind⟩

private theorem bCoordCommonJCore_dense_or_sparse
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n p : ℕ}
    (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hn : 4 ≤ n) {lab : LargeEvenLabel} (hlab : GGSecFiveBCoordBLabel n p lab)
    (hL : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    (huniv : ∀ lab' : LargeEvenLabel, GGLabelIso lab' lab → lab' = lab) :
    (GGSecFiveBCoordDense eta i0 D ∧
        LargeEvenMarking J (fun labJ _ _ _ _ _ =>
          GGSecFiveBCoordBJDenseLabelCore L n p lab labJ)) ∨
      (GGSecFiveBCoordSparse eta i0 D ∧
        LargeEvenMarking J (fun labJ _ _ _ _ _ =>
          GGSecFiveBCoordBJSparseLabel n p lab labJ)) := by
  have hLcore : GGInnerDiagOnLabel
      (fun _ lab' => GGSecFiveBCoordBLabel n p lab') p Bs L := by
    refine largeEvenMarking_mono ?_ hL
    rintro lab' R _ I F θ ⟨hEq, hBsN, hind⟩
    subst lab'
    exact ⟨hlab, hBsN, hind⟩
  obtain ⟨labL, hlamL, hhasL, R₀, _, I₀, F₀, θ₀, hPL⟩ :=
    largeEvenMarking_exists_hasLabel hL
  have hLabLEq : labL = lab := hPL.1
  have hCoreMarking : GGInnerDiagOnLabel
      (fun p lab' => GGSecFiveBCoordBLabel n p lab' ∧
        ((GGSecFiveBCoordDense eta i0 D ∧
            LargeEvenMarking J (fun labJ _ _ _ _ _ =>
              GGSecFiveBCoordBJDenseLabelCore L n p lab' labJ)) ∨
          (GGSecFiveBCoordSparse eta i0 D ∧
            LargeEvenMarking J (fun labJ _ _ _ _ _ =>
              GGSecFiveBCoordBJSparseLabel n p lab' labJ)))) p Bs L :=
    ggSecFiveBCoordBCommonJCoreInput_holds (G := G) (p := p) (B := B) (Bs := Bs)
      (x := x) (L := L) (D := D) (J := J) hcfg hB n hn eta i0 hLB hLcore
  obtain ⟨labCore, hlamCore, hhasCore, R₁, _, I₁, F₁, θ₁, hPCore⟩ :=
    largeEvenMarking_exists_hasLabel hCoreMarking
  have hiso : GGLabelIso labCore labL :=
    hRig labCore labL (↥L ⧸ Subgroup.center ↥L) hlamCore hlamL hhasCore hhasL
  have hLabCoreEq : labCore = lab :=
    huniv labCore (by simpa only [hLabLEq] using hiso)
  subst labCore
  exact hPCore.1.2

theorem GGConfig.bCoordSparse_and_J_label_of_twD_four_one
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))) (i0 : Fin 4)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twD, 4, 1⟩) 3 Bs L) :
    GGSecFiveBCoordSparse eta i0 D ∧
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab = ⟨.D, 3, 1⟩) := by
  classical
  have huniv : ∀ lab' : LargeEvenLabel, GGLabelIso lab' ⟨.twD, 4, 1⟩ →
      lab' = ⟨.twD, 4, 1⟩ := by
    intro lab' hiso
    rcases hiso with h | h | h | h | h | h | h | h
    · exact h
    all_goals simp [LargeEvenLabel.mk.injEq] at h
  have hlab : GGSecFiveBCoordBLabel 4 3 (⟨.twD, 4, 1⟩ : LargeEvenLabel) := by
    refine Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩)
  rcases bCoordCommonJCore_dense_or_sparse hRig hcfg hB eta i0 hLB (by norm_num)
      hlab hL huniv with ⟨hDense, hJDense⟩ | ⟨hSparse, hJSparse⟩
  · exfalso
    obtain ⟨labJD, hlamJD, hhasJD, RJD, _, IJD, FJD, θJD, hPDense⟩ :=
      largeEvenMarking_exists_hasLabel hJDense
    unfold GGSecFiveBCoordBJDenseLabelCore at hPDense
    rcases hPDense with hDenseLabel | hSpecial
    · unfold GGSecFiveBCoordBJDenseLabel at hDenseLabel
      rcases hDenseLabel with ⟨_, hdiv, _⟩ | ⟨_, _, hJeq, _⟩ | ⟨htag, _⟩
      · norm_num at hdiv
      · have hJ : labJD = ⟨.twA, 2, 1⟩ := by simpa using hJeq
        rw [hJ] at hlamJD
        unfold LargeEvenInLambda2 at hlamJD
        norm_num at hlamJD
      · simp at htag
    · omega
  · refine ⟨hSparse, largeEvenMarking_mono ?_ hJSparse⟩
    intro labJ R _ I F θ hP
    unfold GGSecFiveBCoordBJSparseLabel at hP
    rcases hP with h | h | h | h | h <;> simp_all

theorem GGConfig.bCoordSparse_and_J_label_of_D_five_one
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin 5 → Multiplicative (ZMod 3))) (i0 : Fin 5)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 5 3 i0)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.D, 5, 1⟩) 3 Bs L)
    (hZ : Subgroup.center L = ⊥) :
    GGSecFiveBCoordSparse eta i0 D ∧
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab = ⟨.twD, 4, 1⟩) := by
  classical
  have huniv : ∀ lab' : LargeEvenLabel, GGLabelIso lab' ⟨.D, 5, 1⟩ →
      lab' = ⟨.D, 5, 1⟩ := by
    intro lab' hiso
    rcases hiso with h | h | h | h | h | h | h | h
    · exact h
    all_goals simp [LargeEvenLabel.mk.injEq] at h
  have hlab : GGSecFiveBCoordBLabel 5 3 (⟨.D, 5, 1⟩ : LargeEvenLabel) := by
    refine Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num, rfl, rfl⟩))
  rcases bCoordCommonJCore_dense_or_sparse hRig hcfg hB eta i0 hLB (by norm_num)
      hlab hL huniv with ⟨hDense, hJDense⟩ | ⟨hSparse, hJSparse⟩
  · exfalso
    obtain ⟨labJD, hlamJD, hhasJD, RJD, _, IJD, FJD, θJD, hPDense⟩ :=
      largeEvenMarking_exists_hasLabel hJDense
    unfold GGSecFiveBCoordBJDenseLabelCore at hPDense
    rcases hPDense with hDenseLabel | hSpecial
    · unfold GGSecFiveBCoordBJDenseLabel at hDenseLabel
      rcases hDenseLabel with ⟨htag, _, _⟩ | ⟨_, _, _, hne⟩ | ⟨htag, _⟩
      · simp at htag
      · exact hne ⟨rfl, rfl⟩
      · simp at htag
    · exact hSpecial.2.2.2.2 hZ
  · refine ⟨hSparse, largeEvenMarking_mono ?_ hJSparse⟩
    intro labJ R _ I F θ hP
    unfold GGSecFiveBCoordBJSparseLabel at hP
    rcases hP with h | h | h | h | h <;> simp_all

end CFSG.StandardType

end
