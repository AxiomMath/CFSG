module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPShape
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymSimple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

theorem card_eq_two_of_sevenElevenAlt {X : Type} [Group X] [Finite X] {S : Subgroup X}
    {m : ℕ} (hm : 3 < m)
    (hodd : Odd (Nat.card (Subgroup.center X))) (h : IsSymGp (X ⧸ fusionOddCore X) m)
    (halt : SevenElevenAlt X S) : Nat.card S = 2 := by
  have hZO : Subgroup.center X ≤ fusionOddCore X :=
    CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
  rcases halt with ⟨⟨n', h1⟩, -⟩ | h2 | ⟨-, h3⟩ | ⟨hS2, -⟩ | ⟨hS2, -⟩ | ⟨hS2, -⟩
  · rcases h1 with ⟨m', hsp, hroot⟩ | ⟨m', hpsu, huroot⟩ | ⟨hsz, -⟩
    ·
      obtain ⟨hcardS, k, hmk, F, hFld, hFin, hFcard, e, hQ⟩ := hroot
      letI : Field F := hFld
      letI : Finite F := hFin
      by_cases hn'1 : n' = 1
      · simp [hcardS, hn'1]
      · exfalso
        have hn'2 : 2 ≤ n' := by
          have := one_le_of_isSpGp hsp
          omega
        by_cases hm'2 : 2 ≤ m'
        · exact false_of_isSimpleGroup_center_quot_symGp (by omega) hodd h
            (isSimpleGroup_of_isSpGp hsp hm'2 (Or.inl hn'2))
        · have hm'0 : m' = 0 := by omega
          have hk0 : k = 0 := by omega
          subst hk0
          obtain ⟨eS⟩ := h
          haveI hsubZ : Subsingleton (X ⧸ Subgroup.center X) :=
            ⟨fun a b => e.injective (Subtype.ext (Units.ext (Subsingleton.elim _ _)))⟩
          have hZtop : Subgroup.center X = ⊤ := by
            ext x
            simp only [Subgroup.mem_top, iff_true]
            exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
          have hOtop : fusionOddCore X = ⊤ := le_antisymm le_top (hZtop ▸ hZO)
          haveI : Subsingleton (X ⧸ fusionOddCore X) := by
            rw [hOtop]
            exact QuotientGroup.subsingleton_quotient_top
          haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
          exact not_subsingleton_iff_nontrivial.mpr inferInstance
            (eS.toEquiv.symm.subsingleton)
    ·
      obtain ⟨hcardS, F, hFld, hFin, hFcard, e, hQ⟩ := huroot
      haveI : Field F := hFld
      haveI : Finite F := hFin
      obtain ⟨hm'3, hn'1⟩ := three_le_of_isPSUGp hpsu
      by_cases hn'one : n' = 1
      · simp [hcardS, hn'one]
      · exfalso
        have hn'2 : 2 ≤ n' := by omega
        have hm4 : 4 ≤ m' ∨ (m' = 3 ∧ 2 ≤ n') := by
          rcases eq_or_lt_of_le hm'3 with h | h
          · exact Or.inr ⟨h.symm, hn'2⟩
          · exact Or.inl (by omega)
        exact false_of_isSimpleGroup_center_quot_symGp (by omega) hodd h
          (isSimpleGroup_of_isPSUGp hpsu hm4)
    ·
      exfalso
      exact false_of_isSimpleGroup_center_quot_symGp (by omega) hodd h
        ((CFSG.LieType.Simplicity.fam_2b2_simplicity (X ⧸ Subgroup.center X) 2 n' hsz).2)
  ·
    obtain ⟨m', n', hm'3, hL, -, -⟩ := h2
    exfalso
    have hclass : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL m' 2 n' :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega : m' ≠ 0) hL
    exact false_of_isSimpleGroup_center_quot_symGp (by omega) hodd h
      ((CFSG.LieType.Simplicity.fam_PSL_simplicity (X ⧸ Subgroup.center X) m' 2 n'
        hclass).2)
  ·
    obtain ⟨⟨eA6⟩, -, -⟩ := h3
    exfalso
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact false_of_isSimpleGroup_center_quot_symGp (by omega) hodd h
      (MulEquiv.isSimpleGroup eA6)
  · exact hS2
  · exact hS2
  · exact hS2

theorem sevenElevenAlt_of_shapeData (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (d : ShapeData V H T φ) : SevenElevenAlt X (barSub (kGenIn V H) φ V) := by
  obtain ⟨φ', hφ', hS⟩ := exists_ambient_barMap d.hyp83 d.eq_sup d.bar
  have hAlt := ((h711 H) _ _ _ (AmbientH.hyp711 d.hyp83 d.eq_sup)).2 X φ' hφ'
  rw [hS] at hAlt
  exact hAlt

theorem card_barSub_eq_two_of_symGp (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (d : ShapeData V H T φ) {m : ℕ} (hm : 3 < m) (h : IsSymGp (X ⧸ fusionOddCore X) m) :
    Nat.card (barSub (kGenIn V H) φ V) = 2 := by
  haveI := d.finite
  exact card_eq_two_of_sevenElevenAlt hm d.odd_card_center h (sevenElevenAlt_of_shapeData h711 d)

end CFSG.LocalAnalysis.WeakClosure81

end
