module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofHighWit
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofRankTwo
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofSp62
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofOuterLin
public import CFSG.RankThree.PartTwo.Sec4.Item426RestInner

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projImage)
open CFSG.Blueprint Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace HighInv

variable {Y : Type} [Group Y]

theorem finite (h : HighInv Y) : Finite Y :=
  Nat.finite_of_card_ne_zero (by have := h.card; omega)

theorem of_mulEquiv {M : Type} [Group M] (e : Y ≃* M) (h : HighInv M) : HighInv Y := by
  obtain ⟨⟨E, hE, hE81, hEZ⟩, ⟨g, hg⟩, hcard⟩ := h
  refine ⟨⟨E.map e.symm.toMonoidHom, Item223CensusResProof.isElemAbelian_map_hom _ hE, ?_, ?_⟩,
    ⟨e.symm g, by rw [MulEquiv.orderOf_eq]; exact hg⟩,
    by rw [Nat.card_congr e.toEquiv]; exact hcard⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hE81]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨y, hy, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
    have hyc : y ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro z
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact hc (e.symm z)
    have : y ∈ E ⊓ Subgroup.center M := Subgroup.mem_inf.mpr ⟨hy, hyc⟩
    rw [hEZ, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, MulEquiv.coe_toMonoidHom, this, map_one]

theorem exists_inner (h : HighInv Y) : ∃ B : Subgroup (MulAut Y),
    CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = 81 ∧
      B ≤ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨E, hE, hE81, hEZ⟩ := h.elem
  set φ := (MulAut.conj : Y →* MulAut Y).comp E.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Sec4.ker_conj_eq_center] at hx
    have : (x : Y) ∈ E ⊓ Subgroup.center Y := Subgroup.mem_inf.mpr ⟨x.2, hx⟩
    rw [hEZ, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Item223CensusResProof.isElemAbelian_map_hom _ hE
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hE81]
  · rw [MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _

theorem false_of_inner (h : HighInv Y) {M : Type*} [Group M] (e : Y ≃* M)
    (hM : ∀ F : Subgroup (MulAut M), CFSG.Assembly.IsElemAbelian 3 F →
      F ≤ (MulAut.conj : M →* MulAut M).range → Nat.card F ≤ 27) : False := by
  obtain ⟨B, hB, hB81, hBi⟩ := h.exists_inner
  have h1 := hM (B.map (MulAut.congr e).toMonoidHom)
    (Item223CensusResProof.isElemAbelian_map_hom _ hB) (by
      rintro _ ⟨σ, hσ, rfl⟩
      obtain ⟨y, rfl⟩ := hBi hσ
      exact ⟨e y, (KFacts.congr_mulAutConj e y).symm⟩)
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hB81] at h1
  norm_num at h1

theorem false_of_pRank (h : HighInv Y) {S : Type*} [Group S] (e : Y ⧸ Subgroup.center Y ≃* S)
    (hS : CFSG.pRank 3 S ≤ 3) : False := by
  have := h.finite
  have : Finite S := Finite.of_equiv _ e.toEquiv
  obtain ⟨B, hB, hB81, hBi⟩ := h.exists_inner
  have h1 := Sec4.le_pRank_of_le_inner e hB hBi (k := 4) (by rw [hB81]; norm_num)
  omega

theorem false_of_pRank_mulAut (h : HighInv Y) (hS : CFSG.pRank 3 (MulAut Y) ≤ 3) : False := by
  have := h.finite
  obtain ⟨B, hB, hB81, -⟩ := h.exists_inner
  have h1 := Sec4.le_pRank_mulAut (MulEquiv.refl Y) hB (k := 4) (by rw [hB81]; norm_num)
  omega

theorem false_of_hom (h : HighInv Y) {G' : Type*} [Group G'] (φ : Y →* G')
    (hφ : Function.Injective φ)
    (hG : ∀ P : Subgroup G', P ≤ φ.range → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
      (∀ x ∈ P, x ^ 3 = 1) → Nat.card P ≤ 27) : False := by
  obtain ⟨E, hE, hE81, -⟩ := h.elem
  have hEm := Item223CensusResProof.isElemAbelian_map_hom φ hE
  have h1 := hG (E.map φ) (Subgroup.map_le_range _ _)
    (fun x hx y hy => congrArg Subtype.val (hEm.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)) hEm.2
  rw [Subgroup.card_map_of_injective hφ, hE81] at h1
  norm_num at h1

theorem false_of_card_lt (h : HighInv Y) (hY : Nat.card Y < 10 ^ 13) : False := by
  have := h.card
  omega

theorem false_of_not_dvd (h : HighInv Y) (hY : ¬ 81 ∣ Nat.card Y) : False := by
  obtain ⟨E, -, hE81, -⟩ := h.elem
  exact hY (hE81 ▸ Subgroup.card_subgroup_dvd_card E)

theorem false_of_no_nine (h : HighInv Y) (hY : ∀ g : Y, orderOf g ≠ 9) : False := by
  obtain ⟨g, hg⟩ := h.nine
  exact hY g hg

end HighInv

namespace Item223CensusResProof

theorem sq_eq_zero_of_isNilpotent {K : Type*} [Field K] {N : Matrix (Fin 2) (Fin 2) K}
    (h : IsNilpotent N) : N ^ 2 = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h2 : N.charpoly = Polynomial.X ^ 2 := by
    rw [← sub_eq_zero]
    simpa using h1.eq_zero
  have := Matrix.aeval_self_charpoly N
  rwa [h2, map_pow, Polynomial.aeval_X] at this

theorem orderOf_ne_nine_PSL2 {K : Type*} [Field K] [CharP K 3]
    (g : ProjectiveSpecialLinearGroup (Fin 2) K) : orderOf g ≠ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h9
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  have h1 : ((A ^ 9 : SpecialLinearGroup (Fin 2) K) :
      ProjectiveSpecialLinearGroup (Fin 2) K) = 1 := by
    rw [QuotientGroup.mk_pow, ← h9, pow_orderOf_eq_one]
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K)
  have h18 : M ^ 18 = 1 := by
    have h9' : M ^ 9 = Matrix.scalar (Fin 2) r := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← hr]
    rw [show 18 = 9 * 2 from rfl, pow_mul, h9', ← map_pow]
    rw [Fintype.card_fin] at hr2
    rw [hr2, map_one]
  have hN : (M ^ 2 - 1) ^ 9 = 0 := by
    rw [show 9 = 3 ^ 2 from rfl, sub_pow_char_pow_of_commute 3 2 (Commute.one_right _),
      one_pow, ← pow_mul, show 2 * 3 ^ 2 = 18 from rfl, h18, sub_self]
  have hN2 := sq_eq_zero_of_isNilpotent ⟨9, hN⟩
  have h6 : M ^ 6 = 1 := by
    have h1' : M ^ 2 = 1 + (M ^ 2 - 1) := by abel
    calc M ^ 6 = (M ^ 2) ^ 3 := by rw [← pow_mul]
      _ = (1 + (M ^ 2 - 1)) ^ 3 := by rw [← h1']
      _ = 1 ^ 3 + (M ^ 2 - 1) ^ 3 := add_pow_char_of_commute _ (Commute.one_left _)
      _ = 1 := by rw [one_pow, pow_succ, hN2, zero_mul, add_zero]
  have h6' : ((A : SpecialLinearGroup (Fin 2) K) : ProjectiveSpecialLinearGroup (Fin 2) K) ^ 6
      = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : A ^ 6 = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact h6)
    rw [this]
    exact Subgroup.one_mem _
  have := orderOf_dvd_of_pow_eq_one h6'
  rw [h9] at this
  norm_num at this

theorem det_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSL n K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem det_of_mem_statedSU {n q : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSU n q K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

theorem false_of_det_three {Y : Type} [Group Y] (h : HighInv Y) {K : Type} [Field K] [Finite K]
    (h3 : (3 : K) ≠ 0) {H : Subgroup (GL (Fin 3) K)}
    (hH : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) (e : Y ≃* H) : False := by
  refine h.false_of_hom (H.subtype.comp e.toMonoidHom)
    (Subtype.val_injective.comp e.injective) fun P hPr hcomm hexp => ?_
  have : Finite P := Finite.of_injective _ Subtype.val_injective
  have h1 := Sec4.card_le_of_det_eq_one h3 0 P hcomm hexp fun x hx => by
    obtain ⟨y, rfl⟩ := hPr hx
    exact hH _ (e y).2
  simp only [Fintype.card_fin] at h1
  omega

theorem pRank_projSp_two_le {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : 4 ≤ p ^ f) :
    CFSG.pRank 3 (projSp 2 (GaloisField p f) ⧸ Subgroup.center (projSp 2 (GaloisField p f))) ≤
      3 := by
  set F := GaloisField p f
  have hF : Nat.card F = p ^ f := GaloisField.card p f (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out hp3 hF
  have hs : IsSimpleGroup (projSp 2 F) := by
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hF]; exact hq)))
    exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm.isSimpleGroup
  refine le_trans (Item223CensusProof.pRank_le_two_of_card_le_nine fun B hB =>
    Sec4.card_le_of_projImage _ hs (m := 2) (by norm_num)
      (fun c hc => Sec4.sq_of_scalar_mem_closure_sp (by norm_num) hc) (by norm_num)
      (fun P hPH hcomm hexp => by
        have h := Sec4.card_sq_le_of_mem_closure_sp h3 P hPH hcomm hexp
        norm_num at h
        nlinarith) B hB) (by norm_num)

theorem card_le_of_dvd_of_mulEquiv {Y S : Type*} [Group Y] [Group S] (e : Y ≃* S) {N : ℕ}
    (hN : Nat.card S ∣ N) (hN0 : 0 < N) : Nat.card Y ≤ N := by
  rw [Nat.card_congr e.toEquiv]
  exact Nat.le_of_dvd hN0 hN

theorem card_dvd_of_mulEquiv {Y S : Type*} [Group Y] [Group S] (e : Y ≃* S) {N : ℕ}
    (hN : Nat.card S ∣ N) : Nat.card Y ∣ N := by
  rw [Nat.card_congr e.toEquiv]
  exact hN

theorem card_projSL_dvd_formula (n : ℕ) [NeZero n] (F : Type) [Field F] [Fintype F] :
    Nat.card (projSL n F) ∣
      (∏ i : Fin n, (Fintype.card F ^ n - Fintype.card F ^ (i : ℕ))) / (Fintype.card F - 1) := by
  have h1 := Sec4.card_projSL_dvd n F
  rwa [Matrix.card_SL_field] at h1


open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
theorem not_highInv_of_isList46 (hG2 : G2OddThreeRankTwo) (hExc : ExcEvenThreeRankTwo)
    {Y : Type} [Group Y] (hL : Sec4.IsList46 Y) (h : HighInv Y) : False := by
  have hY := h.finite
  rcases hL with ⟨p, e, _, hp2, he, ⟨eY⟩⟩ | ⟨p, e, _, hp3, he1, he2, hSL | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩⟩ |
      ⟨p, _, hp3, hG2' | ⟨⟨eY⟩⟩ | ⟨hp1, ⟨eY⟩⟩ | ⟨hp2, ⟨eY⟩⟩⟩ |
      (⟨n, hn, ⟨eY⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨eY⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, hn, hSL⟩) | (⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩) |
      ((⟨e, he1, he2, ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩⟩) | ⟨⟨eY⟩⟩ | ⟨hZ3, hG23 | ⟨⟨eY⟩⟩⟩)
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact h.false_of_no_nine fun g hg => orderOf_ne_nine_PSL2
        ((eY.trans (Sec4.projSLEquivPSLn 2 _)) g) (by rw [MulEquiv.orderOf_eq]; exact hg)
    · exact h.false_of_inner (eY.trans (Sec4.projSLEquivPSLn 2 _)) fun F hF hFi =>
        (Item223CensusProof.card_le_nine_inner_PSL2 (Sec4.three_ne_zero_of_card Fact.out hp3
          (GaloisField.card p e (by omega))) F hF hFi).trans (by norm_num)
  ·
    obtain ⟨K, _, _, ⟨hK, ⟨eY⟩⟩ | ⟨hK, ⟨eY⟩⟩⟩ := hSL
    · exact false_of_det_three h (Sec4.three_ne_zero_of_card Fact.out (by omega) hK)
        (fun A hA => det_of_mem_statedSL hA) eY
    · exact false_of_det_three h (Sec4.three_ne_zero_of_card Fact.out (by omega)
        (show Nat.card K = p ^ (2 * e) by rw [hK, ← pow_mul, mul_comm]))
        (fun A hA => det_of_mem_statedSU hA) eY
  ·
    exact h.false_of_inner (eY.trans (Sec4.projSLEquivProjectiveSL 3 _)) fun F hF hFi =>
      (Item223CensusProof.card_le_nine_inner_projectiveSL3 (Sec4.three_ne_zero_of_card Fact.out
        (by omega) (GaloisField.card p e (by omega))) F hF hFi).trans (by norm_num)
  ·
    have hU := Sec4.unitaryFieldData_galoisField p e he1
    have := hU.finite
    exact h.false_of_inner (eY.trans (Sec4.projSUEquivUnitaryPSU p e hU)) fun F hF hFi =>
      (Item223CensusProof.card_le_nine_inner_unitaryPSU (Sec4.three_ne_zero_of_card Fact.out
        (by omega) (GaloisField.card p (2 * e) (by omega))) F hF hFi).trans (by norm_num)
  ·
    exact h.false_of_pRank (MulEquiv.refl _) ((hG2 p hp3 Y hG2').trans (by norm_num))
  ·
    exact h.false_of_pRank (Sec4.quotientCenterCongr eY) (Sec4.rankSp4_holds p hp3)
  ·
    exact h.false_of_pRank (Sec4.quotientCenterCongr eY) (Sec4.rankU4_holds p hp3 hp1)
  ·
    exact h.false_of_pRank (Sec4.quotientCenterCongr eY) (Sec4.rankL4_holds p hp3 hp2)
  ·
    refine h.false_of_card_lt ?_
    rw [Nat.card_congr eY.toEquiv]
    calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
          Subgroup.card_le_card_group _
      _ = n.factorial := by rw [Nat.card_perm, Nat.card_fin]
      _ ≤ (9 : ℕ).factorial := Nat.factorial_le hn
      _ < 10 ^ 13 := by decide
  ·
    refine h.false_of_card_lt ?_
    rw [Item223CensusProof.card_of_isExtOf_three hA6, nat_card_alternatingGroup, Nat.card_fin]
    decide
  ·
    refine h.false_of_card_lt ?_
    rw [Item223CensusProof.card_of_isExtOf_three hA7, nat_card_alternatingGroup, Nat.card_fin]
    decide
  ·
    simp only [Sec4.sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
    have hcY := Nat.card_congr eY.toEquiv
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 : Nat.card (NativeSporadic.Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .M12) = 95040 := KFacts.KS14.card_nativeM12
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := KFacts.KS14.card_nativeM22
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .M23) = 10200960 :=
        CFSG.Sporadic.Schreier.m23_card
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 :=
        CFSG.Sporadic.Mathieu.card_M24
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .J1) = 175560 := CFSG.Sporadic.J1.card_J1
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .J3) = 50232960 := CFSG.Sporadic.J3.card_J3
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
        CFSG.Sporadic.J4.card_J4
      exact h.false_of_not_dvd (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .McL) = 898128000 := CFSG.Sporadic.McL.card_McL
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
      exact h.false_of_card_lt (by rw [hcY, h1]; norm_num)
  ·
    simp only [Sec4.sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    have hc := Item223CensusProof.card_of_isExtOf_three hext
    rcases hs with rfl | rfl | rfl | rfl
    · have h1 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := KFacts.KS14.card_nativeM22
      exact h.false_of_card_lt (by rw [hc, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .J3) = 50232960 := CFSG.Sporadic.J3.card_J3
      exact h.false_of_card_lt (by rw [hc, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .McL) = 898128000 := CFSG.Sporadic.McL.card_McL
      exact h.false_of_card_lt (by rw [hc, h1]; norm_num)
    · have h1 : Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 :=
        CFSG.Sporadic.ON.card_ON
      exact h.false_of_card_lt (by rw [hc, h1]; norm_num)
  ·
    rcases hchev with ⟨n, hn, ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩ | ⟨⟨eY⟩⟩⟩ |
        ⟨f, hG2'' | hD4 | hSz | hF4 | hTits⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact h.false_of_inner (eY.trans (Sec4.projSLEquivPSLn 2 _)) fun F hF hFi =>
        (Item223CensusProof.card_le_nine_inner_PSL2 (Sec4.three_ne_zero_of_card Nat.prime_two
          (by norm_num) (GaloisField.card 2 n (by omega))) F hF hFi).trans (by norm_num)
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact h.false_of_inner (eY.trans (Sec4.projSLEquivProjectiveSL 3 _)) fun F hF hFi =>
        (Item223CensusProof.card_le_nine_inner_projectiveSL3 (Sec4.three_ne_zero_of_card
          Nat.prime_two (by norm_num) (GaloisField.card 2 n (by omega))) F hF hFi).trans
          (by norm_num)
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hU := Sec4.unitaryFieldData_galoisField 2 n hn
      have := hU.finite
      exact h.false_of_inner (eY.trans (Sec4.projSUEquivUnitaryPSU 2 n hU)) fun F hF hFi =>
        (Item223CensusProof.card_le_nine_inner_unitaryPSU (Sec4.three_ne_zero_of_card
          Nat.prime_two (by norm_num) (GaloisField.card 2 (2 * n) (by omega))) F hF hFi).trans
          (by norm_num)
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact h.false_of_card_lt (by
          rw [Nat.card_congr eY.toEquiv, Item223CensusProof.card_projSp_two_two]; norm_num)
      · exact h.false_of_pRank (Sec4.quotientCenterCongr eY) (pRank_projSp_two_le (by norm_num)
          hn ((Nat.pow_le_pow_right (by norm_num) hn2).trans' (by norm_num)))
    · exact h.false_of_pRank (Sec4.quotientCenterCongr eY) (Sec4.rankU4Even_holds n hn)
    · exact h.false_of_pRank (MulEquiv.refl _) ((hExc Y f (Or.inl hG2'')).trans (by norm_num))
    · exact h.false_of_pRank (MulEquiv.refl _)
        ((hExc Y f (Or.inr (Or.inl hD4))).trans (by norm_num))
    · exact h.false_of_pRank_mulAut ((KFacts.KP7.pRank_three_mulAut_le_one hSz).trans
        (by norm_num))
    · exact h.false_of_pRank (MulEquiv.refl _)
        ((hExc Y f (Or.inr (Or.inr hF4))).trans (by norm_num))
    · obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y 2 f hTits
      exact h.false_of_card_lt (by
        rw [Nat.card_congr eT.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]; norm_num)
  ·
    obtain ⟨K, _, _, ⟨hK, ⟨eY⟩⟩ | ⟨hK, ⟨eY⟩⟩⟩ := hSL
    · exact false_of_det_three h (Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hK)
        (fun A hA => det_of_mem_statedSL hA) eY
    · exact false_of_det_three h (Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num)
        (show Nat.card K = 2 ^ (2 * n) by rw [hK, ← pow_mul, mul_comm]))
        (fun A hA => det_of_mem_statedSU hA) eY
  ·
    have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
    have h1 := card_projSL_dvd_formula 5 (GaloisField 2 1)
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)] at h1
    norm_num [Fin.prod_univ_succ] at h1
    exact h.false_of_card_lt ((card_le_of_dvd_of_mulEquiv eY h1 (by norm_num)).trans_lt
      (by norm_num))
  ·
    exact h.false_of_card_lt (by rw [Nat.card_congr eY.toEquiv, card_projSp_three_two]; norm_num)
  ·
    have hU := Sec4.unitaryFieldData_galoisField 2 2 (by norm_num)
    have hSU := CFSG.RankThree.PartTwo.Census.card_statedSU_five_four hU
    have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) (GaloisField 2 (2 * 2))) :=
      Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
    have h1 := card_dvd_of_mulEquiv eY (Sec4.card_projSU_dvd 5 2 2)
    rw [hSU] at h1
    exact h.false_of_not_dvd fun h81 => by
      have := h81.trans h1
      norm_num at this
  ·
    have : Fintype (GaloisField 3 e) := Fintype.ofFinite _
    have h1 := card_projSL_dvd_formula 3 (GaloisField 3 e)
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 e (by omega)] at h1
    rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl <;>
      norm_num [Fin.prod_univ_succ] at h1 <;>
      exact h.false_of_card_lt ((card_le_of_dvd_of_mulEquiv eY h1 (by norm_num)).trans_lt
        (by norm_num))
  ·
    have h1 := KFacts.KS14.card_projSU_three_mul_gcd 3 e he1
    have hpos : 0 < Nat.gcd 3 (3 ^ e + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    refine h.false_of_card_lt ?_
    rw [Nat.card_congr eY.toEquiv]
    have h2 : Nat.card (projSU 3 3 e) ≤ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1)) :=
      h1 ▸ Nat.le_mul_of_pos_right _ hpos
    have h3 : 3 ^ e ≤ 9 := by
      calc 3 ^ e ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) he2
        _ = 9 := by norm_num
    calc Nat.card (projSU 3 3 e) ≤ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1)) := h2
      _ ≤ 9 ^ 3 * ((9 ^ 2 - 1) * (9 ^ 3 + 1)) := by gcongr
      _ < 10 ^ 13 := by norm_num
  ·
    have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    have h1 := card_projSL_dvd_formula 4 (GaloisField 3 1)
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)] at h1
    norm_num [Fin.prod_univ_succ] at h1
    exact h.false_of_card_lt ((card_le_of_dvd_of_mulEquiv eY h1 (by norm_num)).trans_lt
      (by norm_num))
  ·
    refine h.false_of_card_lt ?_
    have h1 := Sec4.Item426Rest.card_dvd_of_G2_three hG23
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
    rw [h2]
    calc Nat.card (Y ⧸ Subgroup.center Y) * Nat.card (Subgroup.center Y) ≤ 4245696 * 3 :=
          Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) h1) hZ3
      _ < 10 ^ 13 := by norm_num
  ·
    refine h.false_of_card_lt ?_
    have h1 : Nat.card (Y ⧸ Subgroup.center Y) = 3265920 := by
      rw [Nat.card_congr eY.toEquiv, Sec4.Item426Rest.card_projSU_four_three]
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
    rw [h2, h1]
    calc 3265920 * Nat.card (Subgroup.center Y) ≤ 3265920 * 3 := Nat.mul_le_mul_left _ hZ3
      _ < 10 ^ 13 := by norm_num

end Item223CensusResProof

open Item223CensusResProof

theorem outer223High_of
    (hG2 : G2OddThreeRankTwo) (hExc : ExcEvenThreeRankTwo) : Outer223High := by
  intro Y _ hL n K _ _ hn4 h3n hK
  have hn6 : 6 ≤ n := by
    obtain ⟨k, rfl⟩ := h3n
    omega
  exact ⟨⟨fun e => not_highInv_of_isList46 hG2 hExc hL
      ((highInv_projectiveSL hn6 hK).of_mulEquiv e)⟩,
    ⟨fun e => not_highInv_of_isList46 hG2 hExc hL ((highInv_SL hn6 hK).of_mulEquiv e)⟩⟩

end CFSG.RankThree.PartTwo.Sec21
