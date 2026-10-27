module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105AutOddU5
public import CFSG.RankThree.PartOne.KF.R6LeviA
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU5
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU5Line
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec21.Item222ProofStar
import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

open Matrix Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.RankThree.PartOne (suQ isCentralPQuot_suQ)
open CFSG.RankThree.PartOne.KFU (bA6 b6 suBlock6 coe_b6 diagU_pow diagU_one dvec5
  perfectResidual_centralizer_b6)

theorem kOf8103_map_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') (B : Subgroup G) :
    F08.KOf8103 ⊤ (B.map e.toMonoidHom) = (F08.KOf8103 ⊤ B).map e.toMonoidHom := by
  have hcen : Subgroup.centralizer ((B.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (B : Set G)).map e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := e.surjective x
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : e b ∈ B.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      have h := hx (e b) hb'
      rw [← map_mul, ← map_mul] at h
      exact e.injective h
    · rintro ⟨y, hy, rfl⟩
      have hy' : ∀ b ∈ B, b * y = y * b := Subgroup.mem_centralizer_iff.mp hy
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hz
      rw [← map_mul, ← map_mul]
      exact congrArg e.toMonoidHom (hy' b hb)
  unfold F08.KOf8103
  change inSubgroup perfectResidual (⊤ ⊓ Subgroup.centralizer
      ((B.map e.toMonoidHom : Subgroup G') : Set G')) =
    (inSubgroup perfectResidual (⊤ ⊓ Subgroup.centralizer (B : Set G))).map e.toMonoidHom
  rw [show (⊤ ⊓ Subgroup.centralizer ((B.map e.toMonoidHom : Subgroup G') : Set G')) =
        (⊤ ⊓ Subgroup.centralizer (B : Set G)).map e.toMonoidHom from by
      rw [top_inf_eq, top_inf_eq, hcen]]
  exact (CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual e.toMonoidHom _).symm

theorem notationB8103_map_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') {n : ℕ} {B : Subgroup G} (h : F08.NotationB8103 ⊤ ⊤ n B) :
    F08.NotationB8103 ⊤ ⊤ n (B.map e.toMonoidHom) := by
  obtain ⟨hcard, -, hL2⟩ := h
  refine ⟨?_, le_top, ?_⟩
  · rw [Subgroup.card_map_of_injective (K := B) e.injective, hcard]
  · have hA' : F08.KOf8103 ⊤ (B.map e.toMonoidHom) =
        (F08.KOf8103 ⊤ B).map e.toMonoidHom := kOf8103_map_mulEquiv e B
    let eA : ↥(F08.KOf8103 ⊤ B) ≃* ↥(F08.KOf8103 ⊤ (B.map e.toMonoidHom)) :=
      ((F08.KOf8103 ⊤ B).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hA').symm
    let e' : Bar2 (F08.KOf8103 ⊤ B) ≃* Bar2 (F08.KOf8103 ⊤ (B.map e.toMonoidHom)) :=
      QuotientGroup.congr _ _ eA (CFSG.pCore_map_iso 2 eA)
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e' hL2

theorem mem_kOf8103_suQ_suBlock6 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (A : SpecialLinearGroup (Fin 2) K) :
    suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
      (unitaryInvolution_involutive hK) A) ∈
      F08.KOf8103 ⊤ (Subgroup.zpowers
        (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))) := by
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  have hb3 : b6 (unitaryInvolution K 2 2) ζ hζ ^ 3 = 1 := by
    apply Subtype.ext
    change ((b6 (unitaryInvolution K 2 2) ζ hζ : ↥(SU (unitaryInvolution K 2 2) 5)) :
      GL (Fin 5) K) ^ 3 = 1
    rw [CFSG.RankThree.PartOne.KFU.coe_b6, CFSG.RankThree.PartOne.KFU.diagU_pow,
      ← CFSG.RankThree.PartOne.KFU.diagU_one]
    congr 1
    funext i
    fin_cases i <;> simp [CFSG.RankThree.PartOne.KFU.dvec5, Pi.pow_apply, inv_pow, h3]
  have hq : CFSG.RankThree.PartOne.KFU.IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hK
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hmap : F08.KOf8103 ⊤ (Subgroup.zpowers
        (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))) =
      ((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK)).range).map (suQ 5 hK) := by
    unfold F08.KOf8103
    change inSubgroup perfectResidual
      (⊤ ⊓ Subgroup.centralizer (Subgroup.zpowers
        (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) : Set
        (StatedProj (StatedSU 5 (2 ^ 2) K)))) = _
    rw [top_inf_eq,
      CFSG.RankThree.PartTwo.Sec21.Item222Proof.centralizer_zpowers_eq]
    rw [← hq.map_centralizer hb3]
    rw [← CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual (suQ 5 hK)
      (Subgroup.centralizer ({b6 (unitaryInvolution K 2 2) ζ hζ} :
        Set ↥(SU (unitaryInvolution K 2 2) 5)))]
    rw [CFSG.RankThree.PartOne.KFU.perfectResidual_centralizer_b6
      (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) hK4 hζ h1 h2]
  rw [hmap]
  exact Subgroup.mem_map_of_mem _ ⟨A, rfl⟩

theorem eq_one_of_fix_suQ_b6_map_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (β : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K)))
    (hβ : ∃ k : ℕ, β ^ 2 ^ k = 1) (g : StatedProj (StatedSU 5 (2 ^ 2) K))
    (hb : β ((MulAut.conj g) (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))) =
      (MulAut.conj g) (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)))
    (hL : ∀ A : SpecialLinearGroup (Fin 2) K,
      β ((MulAut.conj g) (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A))) =
      (MulAut.conj g) (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A))) :
    β = 1 := by
  let cg : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K)) := MulAut.conj g
  let β' : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K)) := cg⁻¹ * β * cg
  have hβ'pow : ∃ k : ℕ, β' ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hβ
    refine ⟨k, ?_⟩
    have hβ'eq : β' = MulAut.conj cg⁻¹ β := by
      simp [β']
    rw [hβ'eq, ← map_pow (MulAut.conj cg⁻¹) β (2 ^ k), hk, map_one]
  have hb' : β' (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) =
      suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ) := by
    have hbcg : β (cg (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))) =
        cg (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) := hb
    change (cg⁻¹ * β * cg) (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) = _
    rw [MulAut.mul_apply, MulAut.mul_apply, hbcg]
    simp
  have hL' : ∀ A : SpecialLinearGroup (Fin 2) K,
      β' (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A)) =
        suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
          (unitaryInvolution_involutive hK) A) := by
    intro A
    have hLcg : β (cg (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A))) =
        cg (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
          (unitaryInvolution_involutive hK) A)) := hL A
    change (cg⁻¹ * β * cg) (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
      (unitaryInvolution_involutive hK) A)) = _
    rw [MulAut.mul_apply, MulAut.mul_apply, hLcg]
    simp
  have hβ'1 : β' = 1 :=
    eq_one_of_fix_suBlock6_b6 hK hζ h1 h3 β' hβ'pow hb' hL'
  have h : cg * β' * cg⁻¹ = β := by
    show cg * (cg⁻¹ * β * cg) * cg⁻¹ = β
    group
  rw [hβ'1] at h
  simpa using h.symm

theorem not_notationB8103_zpowers_bA6_map_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (g : StatedProj (StatedSU 5 (2 ^ 2) K)) :
    ¬ F08.NotationB8103 ⊤ ⊤ 2
      ((Subgroup.zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ))).map
        (MulAut.conj g).toMonoidHom) := by
  intro hB
  refine CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u5_not_notationB_bA6
    hK hζ h1 h3 ?_
  have hback := notationB8103_map_mulEquiv (MulAut.conj g)⁻¹ hB
  have hmap : ((Subgroup.zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ))).map
      (MulAut.conj g).toMonoidHom).map (MulAut.conj g)⁻¹.toMonoidHom =
      Subgroup.zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ)) := by
    rw [Subgroup.map_map]
    have hcomp : ((MulAut.conj g)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  rwa [hmap] at hback

theorem eq_one_of_isU5_of_fix_of_line_six {X : Type} [Group X] [Finite X]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ 2) ^ 2)
    {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (E : X ≃* StatedProj (StatedSU 5 (2 ^ 2) K)) {B₀ : Subgroup X} (α : MulAut X)
    (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) (hKfix : ∀ x ∈ F08.KOf8103 ⊤ B₀, α x = x)
    (hB₀ : ∀ x ∈ B₀, α x = x) {g : StatedProj (StatedSU 5 (2 ^ 2) K)}
    (hℓ : B₀.map E.toMonoidHom =
      (Subgroup.zpowers (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))).map
        (MulAut.conj g).toMonoidHom) :
    α = 1 := by
  let B' : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)) := B₀.map E.toMonoidHom
  let β : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K)) := MulAut.congr E α
  have hβ : ∃ k : ℕ, β ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hcongr : ∀ x : X, β (E.toMonoidHom x) = E.toMonoidHom (α x) := by
    intro x
    change MulAut.congr E α (E x) = E (α x)
    simp [MulAut.congr]
  have hβB' : ∀ y ∈ B', β y = y := by
    intro y hy
    have hy' : y ∈ B₀.map E.toMonoidHom := by simpa [B'] using hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy'
    rw [hcongr, hB₀ x hx]
  have hβK' : ∀ y ∈ F08.KOf8103 ⊤ B', β y = y := by
    intro y hy
    have hy' : y ∈ F08.KOf8103 ⊤ (B₀.map E.toMonoidHom) := by simpa [B'] using hy
    rw [kOf8103_map_mulEquiv E B₀] at hy'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy'
    rw [hcongr, hKfix x hx]
  have hb : β ((MulAut.conj g) (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))) =
      (MulAut.conj g) (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) := by
    have hmem : (MulAut.conj g) (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) ∈ B' := by
      dsimp only [B']
      rw [hℓ]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers _)
    exact hβB' _ hmem
  have hL : ∀ A : SpecialLinearGroup (Fin 2) K,
      β ((MulAut.conj g) (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A))) =
      (MulAut.conj g) (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A)) := by
    intro A
    have hmem : suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A) ∈
        F08.KOf8103 ⊤ (Subgroup.zpowers
          (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))) :=
      mem_kOf8103_suQ_suBlock6 hK hζ h1 h3 A
    have hmem' : (MulAut.conj g) (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A)) ∈ F08.KOf8103 ⊤ B' := by
      dsimp only [B']
      rw [hℓ, kOf8103_map_mulEquiv (MulAut.conj g)
        (Subgroup.zpowers (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)))]
      exact Subgroup.mem_map_of_mem _ hmem
    exact hβK' _ hmem'
  have hβ1 : β = 1 := eq_one_of_fix_suQ_b6_map_conj hK hζ h1 h3 β hβ g hb hL
  have h : MulAut.congr E α = MulAut.congr E 1 := by
    rw [map_one]
    exact hβ1
  exact (MulAut.congr E).injective h

theorem eq_one_of_isU5_of_fix {X : Type} [Group X] [Finite X] (hX : IsU5 X 2)
    {B₀ : Subgroup X} (hB : F08.NotationB8103 ⊤ ⊤ 2 B₀) (α : MulAut X)
    (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) (hK : ∀ x ∈ F08.KOf8103 ⊤ B₀, α x = x)
    (hB₀ : ∀ x ∈ B₀, α x = x) : α = 1 := by
  let K := GaloisField 2 (2 * 2)
  have hKcard : Nat.card K = (2 ^ 2) ^ 2 := by
    dsimp [K]
    exact CFSG.RankThree.PartTwo.Sec21.U4Lines.card_galoisField_two_mul 2 (by norm_num)
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Blueprint.LieModel.admissible hX) (MulEquiv.refl _))
  let E : X ≃* StatedProj (StatedSU 5 (2 ^ 2) K) :=
    e.trans (CFSG.PGLModel.projSUEquivStatedProj 5 2 2)
  let B' : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)) := B₀.map E.toMonoidHom
  have hB' : F08.NotationB8103 ⊤ ⊤ 2 B' := by
    simpa [B'] using notationB8103_map_mulEquiv E hB
  have hKcard_roots : Nat.card (rootsOfUnity 3 K) = 3 := by
    dsimp [K]
    exact CFSG.RankThree.PartTwo.Sec21.U4Lines.card_rootsOfUnity_three even_two hKcard
  have : Nontrivial (rootsOfUnity 3 K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hKcard_roots]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (1 : rootsOfUnity 3 K)
  let ζ : Kˣ := u
  have hζ : unitaryInvolution K 2 2 (ζ : K) = ζ := by
    dsimp [ζ]
    exact CFSG.RankThree.PartTwo.Sec21.U4Lines.unitaryInvolution_rootsOfUnity even_two u
  have h1 : ζ ≠ 1 := by
    intro h
    apply hu
    exact Subtype.ext h
  have h3 : ζ ^ 3 = 1 := by
    dsimp [ζ]
    exact (mem_rootsOfUnity 3 _).mp u.2
  obtain ⟨g, hg | hg⟩ := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u5_conj_line
    hKcard hζ h1 h3 hB'.1
  · exact (not_notationB8103_zpowers_bA6_map_conj hKcard hζ h1 h3 g (hg ▸ hB')).elim
  · exact eq_one_of_isU5_of_fix_of_line_six hKcard hζ h1 h3 E α hα hK hB₀ hg

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

end
