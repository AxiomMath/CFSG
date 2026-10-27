module

public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Certificate9701
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Monster.Schur

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native TauCeti

@[expose] noncomputable def m12h1 : ↥CFSG.Blueprint.NativeSporadic.M24 :=
  wordProd (img2 m24a m24b) m12w1

@[expose] noncomputable def m12h2 : ↥CFSG.Blueprint.NativeSporadic.M24 :=
  wordProd (img2 m24a m24b) m12w2

theorem rep_a_inv : CFSG.Sporadic.Th.Rep 24 m24Data.tA (m24a⁻¹) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_b_inv : CFSG.Sporadic.Th.Rep 24 m24TabBinv (m24b⁻¹) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_h1 : CFSG.Sporadic.Th.Rep 24 m12TabH1 m12h1 :=
  rep_wordTab (by norm_num) rep_m24a rep_a_inv rep_m24b rep_b_inv m12w1

theorem rep_h2 : CFSG.Sporadic.Th.Rep 24 m12TabH2 m12h2 :=
  rep_wordTab (by norm_num) rep_m24a rep_a_inv rep_m24b rep_b_inv m12w2

theorem m12Check_parts :
    relCheck 24 m12TabH1 (invT 24 m12TabH1) m12TabH2 (invT 24 m12TabH2)
      [m12R1, m12R2, m12R3] = true ∧ invOK 24 m12TabH1 (invT 24 m12TabH1) = true ∧
    invOK 24 m12TabH2 (invT 24 m12TabH2) = true ∧ ap m12TabH1 1 ≠ 1 := by
  have h := Certificates.certificate9701
  unfold m12Check at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem m12_relators :
    ∀ v ∈ [m12R1, m12R2, m12R3], wordProd (img2 m12h1 m12h2) v = 1 := by
  obtain ⟨h1, h2, h3, -⟩ := m12Check_parts
  exact wordProd_eq_one_of_relCheck (by norm_num) rep_h1 (rep_h1.inv_of_invOK h2) rep_h2
    (rep_h2.inv_of_invOK h3) h1

theorem m12h1_ne_one : m12h1 ≠ 1 := by
  obtain ⟨-, -, -, h4⟩ := m12Check_parts
  intro h
  apply h4
  have := rep_h1 1 (by norm_num)
  rw [h, CFSG.Sporadic.Th.idx_one] at this
  exact this

theorem tc_relators :
    ∀ v ∈ Sporadic.m12Presentation.relatorLetters, wordProd (img2 m12h1 m12h2) v = 1 := by
  rw [Sporadic.m12Presentation_relatorLetters]
  exact m12_relators

@[expose] noncomputable def m12Hom :
    Sporadic.m12Presentation.Group →* ↥CFSG.Blueprint.NativeSporadic.M24 :=
  PresentedGroup.toGroup (lift_relator Sporadic.m12Presentation (img2 m12h1 m12h2) tc_relators)

theorem m12Hom_of
    (i : Fin Sporadic.m12Presentation.generatorCount) :
    m12Hom (PresentedGroup.of i) = img2 m12h1 m12h2 i.val :=
  PresentedGroup.toGroup.of (lift_relator Sporadic.m12Presentation (img2 m12h1 m12h2) tc_relators)

theorem simple_m12Presentation :
    IsSimpleGroup Sporadic.m12Presentation.Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  obtain ⟨-, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  have := hs
  exact MulEquiv.isSimpleGroup e.symm

theorem m12Hom_injective :
    Function.Injective m12Hom := by
  have := simple_m12Presentation
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal m12Hom.ker with h | h
  · exact h
  · exfalso
    have hgen : 0 < Sporadic.m12Presentation.generatorCount := by
      rw [CFSG.Sporadic.Bridge.M12.generatorCount_eq]; norm_num
    have h0 : m12Hom (PresentedGroup.of ⟨0, hgen⟩) = 1 := by
      rw [← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top _
    rw [m12Hom_of] at h0
    exact m12h1_ne_one h0

theorem card_m12Presentation : Nat.card Sporadic.m12Presentation.Group = 95040 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M12.finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M12.le_card_native
  have h3 : Nat.card (↥CFSG.Blueprint.NativeSporadic.M12) =
      Nat.card Sporadic.m12Presentation.Group := Nat.card_congr e.toEquiv
  omega

theorem range_m12Hom :
    m12Hom.range = Subgroup.closure {m12h1, m12h2} := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := i
    have hi2 : i < 2 := by
      rw [← CFSG.Sporadic.Bridge.M12.generatorCount_eq]; exact hi
    show m12Hom (PresentedGroup.of ⟨i, hi⟩) ∈ _
    rw [m12Hom_of]
    interval_cases i
    · exact Subgroup.subset_closure (by simp [img2])
    · exact Subgroup.subset_closure (by simp [img2])
  · rw [Subgroup.closure_le]
    have hgen : 1 < Sporadic.m12Presentation.generatorCount := by
      rw [CFSG.Sporadic.Bridge.M12.generatorCount_eq]; norm_num
    rintro _ (rfl | rfl)
    · exact ⟨PresentedGroup.of ⟨0, by omega⟩, by rw [m12Hom_of]; simp [img2]⟩
    · exact ⟨PresentedGroup.of ⟨1, hgen⟩, by rw [m12Hom_of]; simp [img2]⟩

theorem m12_card :
    Nat.card (Subgroup.closure ({m12h1, m12h2} :
      Set ↥CFSG.Blueprint.NativeSporadic.M24)) = 95040 := by
  rw [← range_m12Hom, ← card_m12Presentation]
  exact (Nat.card_congr (MonoidHom.ofInjective m12Hom_injective).toEquiv).symm

theorem m12_index :
    ¬ 3 ∣ (Subgroup.closure ({m12h1, m12h2} :
      Set ↥CFSG.Blueprint.NativeSporadic.M24)).index := by
  have h := Subgroup.index_mul_card (Subgroup.closure ({m12h1, m12h2} :
    Set ↥CFSG.Blueprint.NativeSporadic.M24))
  rw [m12_card, CFSG.Sporadic.Mathieu.card_M24] at h
  have h2 : (Subgroup.closure ({m12h1, m12h2} :
      Set ↥CFSG.Blueprint.NativeSporadic.M24)).index * 95040 = 2576 * 95040 := by
    rw [h]
  rw [Nat.eq_of_mul_eq_mul_right (by norm_num) h2]
  norm_num

end CFSG.Monster.Schur
