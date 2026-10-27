module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalTorus
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalTorusL
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalCellSixL
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalSubfieldL
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_smul_one_of_conjAut_pow_three {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 3 ≤ n) {B : GL (Fin n) F} (hB : conjAut n F B ^ 3 = 1) :
    ∃ c : F, c ≠ 0 ∧
      (B : Matrix (Fin n) (Fin n) F) ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F) := by
  have h3 : conjAut n F (B ^ 3) = 1 := by rw [map_pow, hB]
  obtain ⟨u, hu⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff hn (B ^ 3)).mp h3
  refine ⟨(u : F), u.ne_zero, ?_⟩
  have hcoe : ((B ^ 3 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (B : Matrix (Fin n) (Fin n) F) ^ 3 :=
    (Units.coeHom (Matrix (Fin n) (Fin n) F)).map_pow B 3
  rw [← hcoe, hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem fixedTooBig_projectiveSL_linear {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL n F))) {B : GL (Fin n) F}
    (hβ : conjAut n F B ^ 3 = 1)
    (hout : ∀ k : projectiveSL n F, conjAut n F B ≠ MulAut.conj k) :
    FixedTooBig (conjAut n F B) := by
  by_cases h3g : 3 ∣ Nat.gcd n (Nat.card F - 1)
  · obtain ⟨c, hcne, hB3⟩ := exists_smul_one_of_conjAut_pow_three hn hβ
    have h3n : 3 ∣ n := dvd_trans h3g (gcd_dvd_left n (Nat.card F - 1))
    have h3F1 : 3 ∣ Nat.card F - 1 := dvd_trans h3g (gcd_dvd_right n (Nat.card F - 1))
    have hpos : 0 < Nat.card F := Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
    have h3F : ¬ 3 ∣ Nat.card F := by
      rintro ⟨m, hm⟩
      obtain ⟨k, hk⟩ := h3F1
      omega
    have hn3 : n ≠ 3 := by
      rintro rfl
      have hle := pRank_projectiveSL_three_le_two (F := F) h3F
      omega
    have hn6 : 6 ≤ n := by
      obtain ⟨m, hm⟩ := h3n
      rcases m with _ | _ | m
      · omega
      · exact absurd (by omega) hn3
      · omega
    by_cases hcube : ∃ b : F, b ^ 3 = c
    · obtain ⟨b, hb⟩ := hcube
      have hbne : b ≠ 0 := by
        rintro rfl
        exact hcne (by simpa using hb.symm)
      have hB' : (B : Matrix (Fin n) (Fin n) F) ^ 3 = (b ^ 3) • 1 := by
        rw [hb]; exact hB3
      obtain ⟨T, hT, hfix⟩ := exists_torus_fixed_of_cube (F := F) (n := n)
        (B := B) (b := b) (by omega) h3F1 hbne hB'
      exact fixedTooBig_of_torus T hT hfix
    · have hc : ∀ x : F, x ^ 3 ≠ c := fun x hx => hcube ⟨x, hx⟩
      obtain ⟨x, hxord, hxfix⟩ := exists_order_nine_fixed_of_nonCube (F := F) (n := n)
        (B := B) (c := c) hn6 hB3 hc
      exact Or.inr (Or.inr ⟨x, hxfix, hxord⟩)
  · exfalso
    have hmem : conjAut n F B ∈ CFSG.RankThree.PartOne.OutStructure.Inn (projectiveSL n F) :=
      CFSG.RankThree.PartOne.OutStructure.linear_D2 (p := 3) (K := F) (n := n)
        (by norm_num) hn h3g (conjAut n F B) (conjAut_mem_linearAutGroup B) 1 (by
          rw [pow_one, hβ]
          exact Subgroup.one_mem _)
    obtain ⟨k, hk⟩ := hmem
    exact absurd hk.symm (hout k)

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial in
theorem outerThreeBig_projectiveSL {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n) :
    OuterThreeBig (LinearFlag.projectiveSL n F) := by
  intro h4 β hβ hout
  by_cases hlin : ∃ B : GL (Fin n) F, LinearFlag.conjAut n F B = β
  · obtain ⟨B, rfl⟩ := hlin
    exact fixedTooBig_projectiveSL_linear hn h4 hβ hout
  · obtain ⟨F₀, _, _, ψ, hcard, hinj, hfix⟩ := exists_subfield_embedding_fixed hn hβ hlin
    exact fixedTooBig_of_embedding ψ hinj hfix
      (twentySeven_dvd_card_projectiveSL_of_cube hn hcard h4)

end CFSG.StandardType.FF81.CatQ1
