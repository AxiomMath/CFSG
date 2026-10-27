module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FinAKer
import CFSG.LocalAnalysis.UniquenessCase.UC22P2014d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabCore
import CFSG.RankThree.PartTwo.Sec19.KF1923L3Par
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Blueprint (LieModel)

section NormalForm

private theorem map_conj_map_conj {X : Type} [Group X] (P : Subgroup X) (a b : X) :
    (P.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      P.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_mulAut_map_eq_pointStab {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : Nat.card K = 2 ^ f) {J : Subgroup (projectiveSL 3 K)}
    (hpar : IsParabolicTwo (projectiveSL 3 K) J) (hJ : J ≠ ⊤) (hns : ¬ Group.IsSolvable ↥J) :
    ∃ α : MulAut (projectiveSL 3 K),
      J.map α.toMonoidHom = projStabilizer (flagSpace 3 K 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hpar
  have hne : J ≠ Subgroup.normalizer ((S : Subgroup (projectiveSL 3 K)) :
      Set (projectiveSL 3 K)) := by
    intro h
    apply hns
    rw [h]
    exact PartOne.Theorem82.isSolvable_normalizer_sylow hf S
  obtain ⟨g, d, hd, hJg⟩ :=
    CFSG.AGLEmbedding.LinearThreeKit.eq_map_conj_projStabilizer_of_sylow 2 S J hS hne hJ
  rcases hd with rfl | rfl
  · refine ⟨MulAut.conj g⁻¹, ?_⟩
    rw [hJg, map_conj_map_conj, inv_mul_cancel]
    convert Subgroup.map_id (projStabilizer (flagSpace 3 K 1))
    ext x
    simp
  · let δ : MulAut (projectiveSL 3 K) := dualAut 3 K
    have h1 : J.map δ.toMonoidHom = (projStabilizer (dotOrth (flagSpace 3 K 2))).map
        (MulAut.conj (δ g)).toMonoidHom := by
      rw [hJg, CFSG.RankThree.PartTwo.Late.kfl3_map_conj_map δ]
      congr 1
      exact CFSG.RankThree.PartTwo.Late.kfl3_tr_dual _
    have hdim : Module.finrank K ↥(dotOrth (flagSpace 3 K 2)) =
        Module.finrank K ↥(flagSpace 3 K 1) := by
      rw [finrank_dotOrth, finrank_flagSpace (by norm_num), finrank_flagSpace (by norm_num)]
    obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.Late.kfl3_stab_conj_of_finrank hdim
    refine ⟨MulAut.conj (y * (δ g)⁻¹) * δ, ?_⟩
    have h2 : J.map ((MulAut.conj (y * (δ g)⁻¹) * δ : MulAut (projectiveSL 3 K)).toMonoidHom) =
        (J.map δ.toMonoidHom).map (MulAut.conj (y * (δ g)⁻¹)).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h2, h1, map_conj_map_conj, inv_mul_cancel_right]
    exact hy.symm

end NormalForm

theorem exists_field_equiv_projectiveSL_three {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : LieModel X .PSL 3 2 m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ m ∧
      Nonempty (X ≃* projectiveSL 3 K) := by
  have ht : (CFSG.Open.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel := LieModel.statedClassicalModel h ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨-, K, hfield, hfinite, hcard, ⟨e₀⟩⟩ := hmodel
  let : Field K := hfield
  let : Finite K := hfinite
  let : Fintype K := Fintype.ofFinite K
  have hEven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hcard]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr hEven
  have : CharP K 2 := ringChar.of_eq hchar
  exact ⟨K, hfield, hfinite, this, hcard, ⟨e₀.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_model (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) {R Y : Subgroup G}
    (hR : R ∈ calL D.T D.M) {m : ℕ} (hm : 2 < m)
    (hLie : LieModel (Bar2 R ⧸ center (Bar2 R)) .PSL 3 2 m) (hYR : Y ≤ R) (hYM : Y ≤ D.M)
    (hq : CFSG.Open.IsQuasisimple (Bar2 Y)) (hZ : center (Bar2 Y) = ⊥) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (φ : ↥R →* projectiveSL 3 K),
      Nat.card K = 2 ^ m ∧ Function.Surjective φ ∧
      (∀ r : ↥R, φ r = 1 ↔ (QuotientGroup.mk r : Bar2 R) ∈ center (Bar2 R)) ∧
      (∀ r : ↥R, φ r ∈ projStabilizer (flagSpace 3 K 1) ↔ (r : G) ∈ D.M) := by
  obtain ⟨K, hfield, hfinite, hchar, hcard, ⟨e⟩⟩ :=
    exists_field_equiv_projectiveSL_three (by omega) hLie
  let : Field K := hfield
  let : Finite K := hfinite
  let π : ↥R →* Bar2 R := QuotientGroup.mk' (CFSG.pCore 2 ↥R)
  let ζ : Bar2 R →* Bar2 R ⧸ center (Bar2 R) := QuotientGroup.mk' (center (Bar2 R))
  let ε : Bar2 R →* projectiveSL 3 K := e.toMonoidHom.comp ζ
  let θ : ↥R →* projectiveSL 3 K := ε.comp π
  have hεs : Function.Surjective ε := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hθs : Function.Surjective θ := hεs.comp (QuotientGroup.mk'_surjective _)
  have hεker : ∀ b : Bar2 R, ε b = 1 ↔ b ∈ center (Bar2 R) := by
    intro b
    simp only [ε, ζ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hθker : ∀ r : ↥R, θ r = 1 ↔ (QuotientGroup.mk r : Bar2 R) ∈ center (Bar2 R) :=
    fun r => hεker (π r)
  let Pb : Subgroup (Bar2 R) := barImage R (D.M ⊓ R)
  have hpar : IsParabolicTwo (Bar2 R) Pb := uc22p2014d_isParabolicTwo D hB h1930 hR
  have hZP : center (Bar2 R) ≤ Pb := hpar.center_le
  let J : Subgroup (projectiveSL 3 K) := Pb.map ε
  have hmem : ∀ r : ↥R, θ r ∈ J ↔ (r : G) ∈ D.M := by
    intro r
    constructor
    · rintro ⟨b, hb, hbr⟩
      have hc : b⁻¹ * π r ∈ center (Bar2 R) := by
        rw [← hεker, map_mul, map_inv, hbr]
        simp [θ]
      have : π r ∈ Pb := by
        have h := Pb.mul_mem hb (hZP hc)
        simpa using h
      exact (uc22p2014d_mem_barImage_iff D hR r).1 this
    · intro hr
      exact ⟨π r, (uc22p2014d_mem_barImage_iff D hR r).2 hr, rfl⟩
  have hJpar : IsParabolicTwo (projectiveSL 3 K) J := hpar.map ε hεs
  have hJtop : J ≠ ⊤ := by
    intro h
    refine uc22p20i_not_le_M D hR fun x hx => ?_
    exact (hmem ⟨x, hx⟩).1 (h ▸ Subgroup.mem_top _)
  have hJns : ¬ Group.IsSolvable ↥J := by
    intro hs
    have hle : (Y.subgroupOf R).map θ ≤ J := by
      rintro _ ⟨r, hr, rfl⟩
      exact (hmem r).2 (hYM (Subgroup.mem_subgroupOf.1 hr))
    have : Group.IsSolvable ↥((Y.subgroupOf R).map θ) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact not_isSolvable_image hYR hq hZ θ (fun r hr => (hθker r).1 hr) this
  obtain ⟨α, hα⟩ := exists_mulAut_map_eq_pointStab hcard hJpar hJtop hJns
  refine ⟨K, hfield, hfinite, hchar, α.toMonoidHom.comp θ, hcard, ?_, ?_, ?_⟩
  · exact α.surjective.comp hθs
  · intro r
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]
    exact hθker r
  · intro r
    rw [← hα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply]
    exact hmem r
