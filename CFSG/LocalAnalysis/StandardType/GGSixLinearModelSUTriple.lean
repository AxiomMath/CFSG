module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUCoords
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUComp
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRestTriple
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr SUid_eq_statedSU conjEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

namespace SUModel

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] {m : ℕ}
  {G : Type} [Group G]

theorem mem_suInducedPairs_of_frameActs (hF : Nat.card K = (2 ^ f) ^ 2)
    {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G} {P : GL (Fin (m + 1)) K}
    (hP : conjTr (unitaryInvolution K 2 f) (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = antidiag (m + 1))
    {b : G} {d : Fin (m + 1) → Kˣ} (hb : SURep.GGFrameActs (SURep.ggFrameU hF ψ P hP) b d) :
    (b, LinFusion.ggFrameDiag P d) ∈ UFusion.suInducedPairs ψ := by
  have hd : ∀ i, unitaryInvolution K 2 f ((d i : Kˣ) : K) * (d i : K) = 1 := fun i => by
    rw [unitaryInvolution_apply, ← pow_succ]
    exact hb.1 i
  have hA := UFusion.isJUnitary_frame hP (UFusion.isIdUnitary_diagGL hd)
  refine ⟨hA, fun u => ?_⟩
  set E := SURep.ggFrameEquiv hF P hP with hE
  have h1 := hb.2 (E u) (E (InnerDiagSU.conjSU _ hA u)) (by
    change P * ((InnerDiagSU.conjSU _ hA u : SU (unitaryInvolution K 2 f) (m + 1)) :
      GL (Fin (m + 1)) K) * P⁻¹ = diagHom (m + 1) d * (P * (u : GL (Fin (m + 1)) K) * P⁻¹) *
        (diagHom (m + 1) d)⁻¹
    rw [InnerDiagSU.coe_conjSU, diagHom_eq_diagGL]
    group)
  rwa [SURep.ggFrameU_apply, SURep.ggFrameU_apply, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply] at h1

omit [Fact (Nat.Prime 2)] in
theorem range_conj_comp' {U : Type*} [Group U] {ψ : U →* G} {g : G}
    (hg : g ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ((MulAut.conj g).toMonoidHom.comp ψ).range = ψ.range := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg (ψ u)).mp ⟨u, rfl⟩
  · intro hx
    have h1 : g⁻¹ * x * g ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
        (by rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group])
    obtain ⟨u, hu⟩ := h1
    refine ⟨u, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
    group

theorem card_suBlock_le (hF : Nat.card K = (2 ^ f) ^ 2) (h : UnitaryFieldData 2 f K)
    {P : GL (Fin (m + 1)) K}
    (hP : conjTr (unitaryInvolution K 2 f) (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = antidiag (m + 1))
    {I : Finset (Fin (m + 1))} (hI : I.card = 2) :
    Nat.card (UFusion.suBlock (σ := unitaryInvolution K 2 f) P I) ≤
      2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  set E := SURep.ggFrameEquiv hF P hP with hE
  have hmem : ∀ u : UFusion.suBlock (σ := unitaryInvolution K 2 f) P I,
      E (u : SU (unitaryInvolution K 2 f) (m + 1)) ∈ TableBUE.blockSU (K := K) (n := f) I :=
    fun u => UFusion.mem_glBlock.mp (UFusion.mem_suBlock.mp u.2)
  have hinj : Function.Injective (fun u : UFusion.suBlock (σ := unitaryInvolution K 2 f) P I =>
      (⟨E u, hmem u⟩ : TableBUE.blockSU (K := K) (n := f) I)) := by
    intro u v huv
    apply Subtype.ext
    apply E.injective
    exact congrArg Subtype.val huv
  calc Nat.card (UFusion.suBlock (σ := unitaryInvolution K 2 f) P I)
      ≤ Nat.card (TableBUE.blockSU (K := K) (n := f) I) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card ↥(unitarySU 2 f K I.card) :=
        (Nat.card_congr (TableBUE.blockSUEquiv I h).toEquiv).symm
    _ = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
        rw [hI]
        exact CFSG.RankThree.SubgroupLists.card_statedSU_two hF


theorem tripleValue_of_component [Finite G] (hF : Nat.card K = (2 ^ f) ^ 2)
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ m + 1) (hnq : (m + 1, 2 ^ f) ≠ (3, 2)) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : SU (unitaryInvolution K 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) (m + 1)))
    {P : GL (Fin (m + 1)) K}
    (hP : conjTr (unitaryInvolution K 2 f) (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (P : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = antidiag (m + 1))
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζN : (ζ : K) ^ (2 ^ f + 1) = 1)
    {b : G} {d : Fin (m + 1) → Kˣ} (hb : SURep.GGFrameActs (SURep.ggFrameU hF ψ P hP) b d)
    {g : G} (hg : g ∈ Subgroup.normalizer (ψ.range : Set G)) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {g * b * g⁻¹})) (hLA : GGTypeAk f L) :
    ∃ j₁ j₂ j₃ : Fin (m + 1), j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧ d j₁ = d j₂ ∧ d j₁ = d j₃ := by
  set ψ' := (MulAut.conj g).toMonoidHom.comp ψ with hψ'
  have hrange : ψ'.range = ψ.range := range_conj_comp' hg
  have hker' : ψ'.ker ≤ Subgroup.center (SU (unitaryInvolution K 2 f) (m + 1)) := by
    intro u hu
    apply hker
    rw [MonoidHom.mem_ker] at hu ⊢
    simpa [hψ'] using hu
  have hgbJ : (g * b * g⁻¹, LinFusion.ggFrameDiag P d) ∈ UFusion.suInducedPairs ψ' := by
    obtain ⟨hA, hbA⟩ := mem_suInducedPairs_of_frameActs hF hP hb
    refine ⟨hA, fun u => ?_⟩
    simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hbA u]
    group
  have hS : ({g * b * g⁻¹} : Set G) ⊆ UFusion.uFrameTorus ψ' P := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨d, hgbJ⟩
  have hL' : IsComponentOf L (ψ'.range ⊓ Subgroup.centralizer ({g * b * g⁻¹} : Set G)) := by
    rw [hrange]
    exact hL
  have hζσ : unitaryInvolution K 2 f (ζ : K) * ζ = 1 := by
    rw [unitaryInvolution_apply, ← pow_succ]
    exact hζN
  obtain ⟨I, hLI, he⟩ := UFusion.exists_le_uFrameBlock_of_isComponentOf hker' hP hζ1 hζσ hS hL'
  obtain ⟨e, he1, he2⟩ := he _ (Set.mem_singleton _)
  have hSU := SUid_eq_statedSU hF (m + 1)
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  have hkerΦ := SUTorus.ker_comp_symm_le hker' Φ
  have hconj : ∀ x : Fin (m + 1) → Kˣ,
      P * LinFusion.ggFrameDiag P x * P⁻¹ = diagHom (m + 1) x := fun x => by
    rw [LinFusion.ggFrameDiag, diagHom_eq_diagGL]
    group
  have hd' := SUTorus.mem_suPairs_transfer P hP hSU hgbJ.1 hgbJ.2
  have he' := SUTorus.mem_suPairs_transfer P hP hSU he1.1 he1.2
  rw [hconj] at hd' he'
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_mul_of_mem_suPairs h hn hnq hp hpq hkerΦ hd' he'
  rw [diagHom_eq_diagGL, diagHom_eq_diagGL, LinModel.scalar_mul_diagGL] at hc
  have hed : ∀ i, e i = c * d i := fun i => congrFun (LinModel.diagGL_injective hc) i
  have hde : ∀ i ∈ I, ∀ j ∈ I, d i = d j := fun i hi j hj => by
    have h1 := he2 i hi j hj
    rw [hed i, hed j] at h1
    exact mul_left_cancel h1
  by_cases h3 : 2 < I.card
  · obtain ⟨j₁, hj₁, j₂, hj₂, j₃, hj₃, h12, h13, h23⟩ := Finset.two_lt_card.mp h3
    exact ⟨j₁, j₂, j₃, h12, h13, h23, hde j₁ hj₁ j₂ hj₂, hde j₁ hj₁ j₃ hj₃⟩
  · exfalso
    obtain ⟨hf, hdvd⟩ := LinModel.pow_three_dvd_card_of_ggTypeAk hLA
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hsq : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hblock : Nat.card (UFusion.uFrameBlock ψ' P I) ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rcases (by omega : I.card ≤ 1 ∨ I.card = 2) with h1 | h2
      · rw [UFusion.uFrameBlock_eq_bot_of_card_le_one ψ' P h1, Subgroup.card_bot]
        have : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · exact (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans
          (card_suBlock_le hF h hP h2)
    have h1 : Nat.card (↥L ⧸ Subgroup.center ↥L) ≤ Nat.card L :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h2 : Nat.card L ≤ Nat.card (UFusion.uFrameBlock ψ' P I) := Subgroup.card_le_of_le hLI
    have h4 : (2 ^ f) ^ 3 ≤ Nat.card (↥L ⧸ Subgroup.center ↥L) := Nat.le_of_dvd Nat.card_pos hdvd
    have hlt : 2 ^ f * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 3 := by
      calc 2 ^ f * ((2 ^ f) ^ 2 - 1) < 2 ^ f * (2 ^ f) ^ 2 :=
            Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ = (2 ^ f) ^ 3 := by ring
    omega

end SUModel

end CFSG.StandardType
