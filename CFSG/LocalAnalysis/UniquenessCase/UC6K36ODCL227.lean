module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddDefChar
import CFSG.LocalAnalysis.UniquenessCase.UC6K38AL
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylowUnique
import CFSG.LargeExtraspecial.Bender
public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup

namespace ODC

section Generic

variable {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem smul_le_of_le {Y : Subgroup K} {z : K} (hz : z ∈ Y) {P : Sylow p K}
    (hP : (P : Subgroup K) ≤ Y) : ((z • P : Sylow p K) : Subgroup K) ≤ Y := by
  intro x hx
  rw [Sylow.smul_def, K38B.mem_smul_iff] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [MulAut.conj_apply]
  exact Y.mul_mem (Y.mul_mem hz (hP ht)) (Y.inv_mem hz)

theorem eq_top_of_le_of_not_le_normalizer [IsSimpleGroup K] (T : Sylow p K)
    (hTI : ∀ P : Sylow p K, P = T ∨ (P : Subgroup K) ⊓ T = ⊥)
    (hcount : Nat.card (Sylow p K) = Nat.card T + 1) {Y : Subgroup K}
    (hTY : (T : Subgroup K) ≤ Y) {y : K} (hyY : y ∈ Y)
    (hyN : y ∉ normalizer ((T : Subgroup K) : Set K)) : Y = ⊤ := by
  classical
  set P₀ : Sylow p K := y • T with hP₀
  have hP₀T : P₀ ≠ T := fun h => hyN (Sylow.smul_eq_iff_mem_normalizer.1 h)
  have hP₀Y : (P₀ : Subgroup K) ≤ Y := smul_le_of_le hyY hTY
  have hinf : (T : Subgroup K) ⊓ P₀ = ⊥ := by
    rcases hTI P₀ with h | h
    · exact absurd h hP₀T
    · rw [inf_comm]
      exact h
  have hcount' : Nat.card (Sylow p K) = Nat.card P₀ + 1 := by
    rw [hcount, Sylow.card_eq_multiplicity T, Sylow.card_eq_multiplicity P₀]
  have hall : ∀ P : Sylow p K, (P : Subgroup K) ≤ Y := by
    intro P
    by_cases hPT : P = T
    · rw [hPT]
      exact hTY
    · obtain ⟨x, hxT, hx⟩ := K38B.exists_smul_eq_of_ne hP₀T hinf hcount' hPT
      rw [← hx]
      exact smul_le_of_le (hTY hxT) hP₀Y
  have hncl : normalClosure ((T : Subgroup K) : Set K) ≤ Y := by
    refine (closure_le Y).2 fun x hx => ?_
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hax
    refine hall (c • T) ?_
    rw [Sylow.smul_def, K38B.mem_smul_iff]
    exact ⟨a, ha, by rw [MulAut.conj_apply]⟩
  have hT1 : (T : Subgroup K) ≠ ⊥ := by
    intro hbot
    apply hyN
    rw [mem_normalizer_iff]
    intro z
    rw [hbot]
    simp only [SetLike.mem_coe, mem_bot]
    constructor
    · rintro rfl
      group
    · intro h
      have h1 : z = y⁻¹ * (y * z * y⁻¹) * y := by group
      rw [h1, h]
      group
  have htop : normalClosure ((T : Subgroup K) : Set K) = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (normalClosure ((T : Subgroup K) : Set K))).resolve_left fun h => hT1 ?_
    rw [eq_bot_iff]
    exact le_normalClosure.trans h.le
  rw [eq_top_iff, ← htop]
  exact hncl

end Generic

section Model

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.RankThree.PartTwo.KFacts

theorem card_galoisField_three_three : Nat.card (GaloisField 3 3) = 27 := by
  rw [GaloisField.card 3 3 (by norm_num)]
  norm_num

@[expose] noncomputable def weylSL (R : Type*) [CommRing R] : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def weylPSL (R : Type*) [CommRing R] : PSL2 R :=
  QuotientGroup.mk' (Subgroup.center _) (weylSL R)

variable {F : Type} [Field F]

theorem psl2FieldAut_weylPSL (σ : F ≃+* F) : psl2FieldAut F σ (weylPSL F) = weylPSL F := by
  rw [psl2FieldAut_apply, weylPSL, psl2RingEquiv_mk]
  congr 1
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [weylSL]

theorem orderOf_weylPSL (h2 : (2 : F) ≠ 0) : orderOf (weylPSL F) = 2 := by
  have hsq : weylPSL F ^ 2 = 1 := by
    rw [weylPSL, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylSL, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hne : weylPSL F ≠ 1 := by
    rw [weylPSL, Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    rintro ⟨r, -, hr⟩
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 1) hr
    simp [weylSL] at h01
  exact orderOf_eq_prime hsq hne

theorem isOddPrimePower_card_galoisField : IsOddPrimePower (Nat.card (GaloisField 3 3)) :=
  ⟨3, 3, Nat.prime_three, ⟨1, rfl⟩, by norm_num, by rw [card_galoisField_three_three]; norm_num⟩

theorem exists_fixed_involution (α : MulAut (PSL2 (GaloisField 3 3))) (h3 : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : PSL2 (GaloisField 3 3) →* MulAut (PSL2 (GaloisField 3 3))).range) :
    ∃ c : PSL2 (GaloisField 3 3), α c = c ∧ orderOf c = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : α ∉ (pglAction (GaloisField 3 3)).range := by
    rintro ⟨g, rfl⟩
    apply hout
    obtain ⟨x, hx⟩ := sq_mem_of_index_two
      (pgl2_psl2Range_index_eq_two (GaloisField 3 3) isOddPrimePower_card_galoisField) g
    refine ⟨x ^ 2, ?_⟩
    have h4 : pglAction (GaloisField 3 3) g = pglAction (GaloisField 3 3) g ^ 4 := by
      rw [pow_succ, h3, one_mul]
    rw [h4, ← map_pow, show g ^ 4 = (g ^ 2) ^ 2 by rw [← pow_mul], ← hx, ← map_pow,
      pglAction_toPGL]
  have hα3 : orderOf α = 3 :=
    orderOf_eq_prime h3 fun h1 => hout ⟨1, by rw [map_one, h1]⟩
  obtain ⟨σ, -, g, hαg⟩ := linear_two_prime_order_field_descent Nat.prime_three α hα3 hD
  have h2 : (2 : GaloisField 3 3) ≠ 0 := by
    have : ringChar (GaloisField 3 3) = 3 := ringChar.eq (GaloisField 3 3) 3
    exact Ring.two_ne_zero (by rw [this]; norm_num)
  refine ⟨pglAction (GaloisField 3 3) g (weylPSL (GaloisField 3 3)), ?_, ?_⟩
  · rw [hαg, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_def, MulEquiv.symm_apply_apply,
      psl2FieldAut_weylPSL]
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_weylPSL h2

theorem card_psl2_galoisField : Nat.card (PSL2 (GaloisField 3 3)) = 9828 := by
  have : Fintype (GaloisField 3 3) := Fintype.ofFinite _
  have h2 : (2 : GaloisField 3 3) ≠ 0 := by
    have : ringChar (GaloisField 3 3) = 3 := ringChar.eq (GaloisField 3 3) 3
    exact Ring.two_ne_zero (by rw [this]; norm_num)
  have h : Nat.card (PSL2 (GaloisField 3 3)) * 2 =
      Fintype.card (GaloisField 3 3) * (Fintype.card (GaloisField 3 3) ^ 2 - 1) :=
    CFSG.PSL2Table.card_PSL h2
  rw [← Nat.card_eq_fintype_card, card_galoisField_three_three] at h
  norm_num at h
  omega

theorem statedClassicalModel_psl2_galoisField :
    CFSG.Open.StatedClassicalModel (PSL2 (GaloisField 3 3)) .PSL 2 3 3 :=
  ⟨⟨Nat.prime_three, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 3 3, inferInstance,
    inferInstance, by rw [card_galoisField_three_three]; norm_num,
    ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 3)⟩⟩

theorem closure_eq_top_psl2_galoisField (α : MulAut (PSL2 (GaloisField 3 3))) (h3 : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : PSL2 (GaloisField 3 3) →* MulAut (PSL2 (GaloisField 3 3))).range)
    (S : Sylow 3 (PSL2 (GaloisField 3 3))) :
    closure ((S : Set (PSL2 (GaloisField 3 3))) ∪ {k | α k = k}) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (PSL2 (GaloisField 3 3)) :=
    CFSG.AGLEmbedding.isSimpleGroup_psl2GF (by norm_num)
  obtain ⟨c, hc, hc2⟩ := exists_fixed_involution α h3 hout
  have hS27 : Nat.card S = 27 := by
    rw [(CFSG.AGLEmbedding.psl2GF_sylow 3 3 (by norm_num) S).2]
    norm_num
  have hsyl : Nat.card (Sylow 3 (PSL2 (GaloisField 3 3))) = 28 :=
    CFSG.LargeExtraspecial.Bender.card_sylow_of_psl2 _ 3 3 statedClassicalModel_psl2_galoisField
  have hTI : ∀ P : Sylow 3 (PSL2 (GaloisField 3 3)), P = S ∨
      (P : Subgroup (PSL2 (GaloisField 3 3))) ⊓ S = ⊥ := by
    intro P
    by_cases hPS : P = S
    · exact Or.inl hPS
    · refine Or.inr ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
      by_contra hg1
      exact hPS (psl2_sylow_eq_of_mem_nontrivial (GaloisField 3 3) (r := 3) (f := 3)
        (by rw [card_galoisField_three_three]; norm_num) P S g hg.1 hg1 hg.2)
  refine eq_top_of_le_of_not_le_normalizer S hTI (by rw [hsyl, hS27])
    (fun x hx => subset_closure (Or.inl hx)) (subset_closure (Or.inr hc)) fun hcN => ?_
  have hidx : (normalizer ((S : Subgroup (PSL2 (GaloisField 3 3))) :
      Set (PSL2 (GaloisField 3 3)))).index = 28 := by
    rw [← hsyl]
    exact (Sylow.card_eq_index_normalizer S).symm
  have hN : Nat.card (normalizer ((S : Subgroup (PSL2 (GaloisField 3 3))) :
      Set (PSL2 (GaloisField 3 3)))) = 351 := by
    have h := (normalizer ((S : Subgroup (PSL2 (GaloisField 3 3))) :
      Set (PSL2 (GaloisField 3 3)))).card_mul_index
    rw [hidx, card_psl2_galoisField] at h
    omega
  have hdvd := orderOf_dvd_natCard (⟨c, hcN⟩ : normalizer ((S : Subgroup (PSL2 (GaloisField 3 3))) :
      Set (PSL2 (GaloisField 3 3))))
  rw [Subgroup.orderOf_mk, hc2, hN] at hdvd
  omega

end Model

end ODC

open CFSG.RankThree.PartTwo.KFacts in
theorem l227Generation_holds : L227Generation := by
  intro d he27 ε hε3 hout S
  obtain ⟨e⟩ := he27
  haveI : Finite (CatGrp d) := Finite.of_equiv _ e.symm.toEquiv
  set α : MulAut (CFSG.AGLEmbedding.PSL2GF 3 3) := MulAut.congr e ε with hαdef
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hε3, map_one]
  have hαout : α ∉ (MulAut.conj : CFSG.AGLEmbedding.PSL2GF 3 3 →*
      MulAut (CFSG.AGLEmbedding.PSL2GF 3 3)).range := fun h =>
    hout ((isInnerAut_congr e ε).1 h)
  set S' : Sylow 3 (CFSG.AGLEmbedding.PSL2GF 3 3) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective with hS'
  have htop := ODC.closure_eq_top_psl2_galoisField α hα3 hαout S'
  have himg : e.toMonoidHom '' ((S : Set (CatGrp d)) ∪ {k | ε k = k}) =
      (S' : Set (CFSG.AGLEmbedding.PSL2GF 3 3)) ∪ {k | α k = k} := by
    have h1 : e.toMonoidHom '' (S : Set (CatGrp d)) =
        (S' : Set (CFSG.AGLEmbedding.PSL2GF 3 3)) := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        show e.toMonoidHom k ∈ (S : Subgroup (CatGrp d)).map e.toMonoidHom
        exact Subgroup.mem_map_of_mem _ hk
      · intro hy
        have hy' : y ∈ (S : Subgroup (CatGrp d)).map e.toMonoidHom := hy
        obtain ⟨k, hk, rfl⟩ := hy'
        exact ⟨k, hk, rfl⟩
    have h2 : e.toMonoidHom '' {k | ε k = k} = {k | α k = k} := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        change (MulAut.congr e ε) (e k) = e k
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        exact congrArg e hk
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        change ε (e.symm y) = e.symm y
        have hy' : (MulAut.congr e ε) y = y := hy
        simp only [MulAut.congr_apply, MulEquiv.trans_apply] at hy'
        apply e.injective
        rw [MulEquiv.apply_symm_apply]
        exact hy'
    rw [Set.image_union, h1, h2]
  rw [eq_top_iff]
  intro x _
  have hx : e.toMonoidHom x ∈ closure ((S' : Set (CFSG.AGLEmbedding.PSL2GF 3 3)) ∪
      {k | α k = k}) := by
    rw [htop]
    exact mem_top _
  rw [← himg, ← MonoidHom.map_closure] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [e.injective hyx] at hy

end CFSG.LocalAnalysis.UniquenessCase.UCK
