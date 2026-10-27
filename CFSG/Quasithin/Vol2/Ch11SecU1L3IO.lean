module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IF

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.GorensteinWalter
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_index_eq_two)
open scoped MatrixGroups

section Values

variable {p : ℕ} [Fact p.Prime]

theorem isOddPrimePower_zmod (hp2 : p ≠ 2) : IsOddPrimePower (Nat.card (ZMod p)) :=
  ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, le_rfl, by simp⟩

theorem nParam_psl2_zmod_le_one
    (hp7 : 7 ≤ p) : nParam (⊤ : Subgroup (PSL2 (ZMod p))) ≤ 1 := by
  have hK : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp (((Fact.out : p.Prime).eq_two_or_odd').resolve_left (by omega))
  by_cases hp8 : p % 8 = 1 ∨ p % 8 = 7
  · by_cases h7 : p = 7
    · subst h7
      exact E22L2.nParam_psl2_seven_le_one hK
    · exact E22L2.nParam_psl2_prime_le_one hp8 (E22L2.e22pl2_le_of_ne_seven hp8 hp7 h7) hK
  · exact nParam_psl2_pm_three hK (by omega) (by omega)

theorem nParam_pgl2_zmod_le_one
    (hp7 : 7 ≤ p) : nParam (⊤ : Subgroup (PGL2 (ZMod p))) ≤ 1 := by
  have := E22L2.e22pl2pgl_finite (ZMod p)
  have hK : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp (((Fact.out : p.Prime).eq_two_or_odd').resolve_left (by omega))
  by_cases hp8 : p % 8 = 1 ∨ p % 8 = 7
  · by_cases h7 : p = 7
    · subst h7
      exact E22L2.nParam_pgl2_seven_le_one hK
    · exact E22L2.nParam_pgl2_prime_le_one hp8 (E22L2.e22pl2_le_of_ne_seven hp8 hp7 h7) hK
  · exact nParam_pgl2_pm_three hK (by omega) (by omega)

theorem nParam_pslRange_le_one
    (hp7 : 7 ≤ p) : nParam (pslRange (ZMod p)) ≤ 1 := by
  have := E22L2.e22pl2pgl_finite (ZMod p)
  let e : PSL2 (ZMod p) ≃* ↥(pslRange (ZMod p)) := MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := ZMod p))
  have h1 : nParam (pslRange (ZMod p)) = nParam (⊤ : Subgroup ↥(pslRange (ZMod p))) :=
    nParam_subgroupOf _
  have h2 : nParam (⊤ : Subgroup ↥(pslRange (ZMod p))) = nParam (⊤ : Subgroup (PSL2 (ZMod p))) :=
    (E1.Eleven.nParam_top_mulEquiv e).symm
  rw [h1, h2]
  exact nParam_psl2_zmod_le_one hp7

theorem nParam_le_one_of_pslRange_le
    (hp7 : 7 ≤ p) {X : Subgroup (PGL2 (ZMod p))}
    (hX : pslRange (ZMod p) ≤ X) : nParam X ≤ 1 := by
  have := E22L2.e22pl2pgl_finite (ZMod p)
  have hodd := isOddPrimePower_zmod (p := p) (by omega)
  have hidx := pslRange_index_eq_two hodd
  have hdvd : X.index ∣ (pslRange (ZMod p)).index := Subgroup.index_dvd_of_le hX
  rw [hidx] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · have hXt : X = ⊤ := Subgroup.index_eq_one.mp h1
    rw [hXt]
    exact nParam_pgl2_zmod_le_one hp7
  · have hXeq : X = pslRange (ZMod p) := by
      have hrel : (pslRange (ZMod p)).relIndex X = 1 := by
        have h := Subgroup.relIndex_mul_index hX
        rw [hidx, h2] at h
        omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hX
    rw [hXeq]
    exact nParam_pslRange_le_one hp7

end Values

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
