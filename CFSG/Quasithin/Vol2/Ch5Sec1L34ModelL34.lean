module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs522
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem exists_mulEquiv_projectiveSL_of_lieModel {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 2) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
      Nonempty (X ≃* projectiveSL 3 k) := by
  obtain ⟨k, hk, hfin, hcard, he⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  exact ⟨k, hk, hfin, by rw [hcard]; norm_num, he⟩

theorem l34ElemNineFact : L34ElemNineFact := by
  intro X _ h
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel h
  refine ⟨(CFSG.RankThree.PartTwo.KFacts.L34.eZero k).map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_eZero hk
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, CFSG.RankThree.PartTwo.KFacts.L34.commute_of_mem_eZero hk ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, CFSG.RankThree.PartTwo.KFacts.L34.pow_three_of_mem_eZero hk ha, map_one]

section Borel

variable {k : Type} [Field k]

@[expose] noncomputable def diagUnit (A : upperTriangular 3 k) (i : Fin 3) : kˣ where
  val := ((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i
  inv := (((A : SpecialLinearGroup (Fin 3) k)⁻¹ : SpecialLinearGroup (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k) i i
  val_inv := coe_inv_apply_self_of_isUpperTriangular
    (mem_upperTriangular_iff_isUpperTriangular.mp A.2) i
  inv_val := by
    rw [mul_comm]
    exact coe_inv_apply_self_of_isUpperTriangular
      (mem_upperTriangular_iff_isUpperTriangular.mp A.2) i

theorem val_diagUnit (A : upperTriangular 3 k) (i : Fin 3) :
    (diagUnit A i : k) = ((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) i i :=
  rfl

@[expose] noncomputable def diagTwo : upperTriangular 3 k →* kˣ × kˣ where
  toFun A := (diagUnit A 0, diagUnit A 1)
  map_one' := by
    ext <;> simp [val_diagUnit]
  map_mul' A B := by
    have hA := mem_upperTriangular_iff_isUpperTriangular.mp A.2
    have hB := mem_upperTriangular_iff_isUpperTriangular.mp B.2
    ext
    · simp only [Prod.fst_mul, Units.val_mul, val_diagUnit, Subgroup.coe_mul]
      exact mul_apply_self_of_isUpperTriangular hA hB 0
    · simp only [Prod.snd_mul, Units.val_mul, val_diagUnit, Subgroup.coe_mul]
      exact mul_apply_self_of_isUpperTriangular hA hB 1

theorem diagTwo_apply_fst (A : upperTriangular 3 k) :
    ((diagTwo A).1 : k) = ((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 :=
  rfl

theorem diagTwo_apply_snd (A : upperTriangular 3 k) :
    ((diagTwo A).2 : k) = ((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 1 :=
  rfl

theorem mem_unitriangular_of_diagTwo_eq_one {A : upperTriangular 3 k} (hA : diagTwo A = 1) :
    (A : SpecialLinearGroup (Fin 3) k) ∈ unitriangular 3 k := by
  have hU := mem_upperTriangular_iff_isUpperTriangular.mp A.2
  have h0 : ((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 0 0 = 1 := by
    have := congrArg (fun p : kˣ × kˣ => (p.1 : k)) hA
    simpa [diagTwo_apply_fst] using this
  have h1 : ((A : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) 1 1 = 1 := by
    have := congrArg (fun p : kˣ × kˣ => (p.2 : k)) hA
    simpa [diagTwo_apply_snd] using this
  have hdet := (A : SpecialLinearGroup (Fin 3) k).2
  rw [Matrix.det_of_isUpperTriangular hU, Fin.prod_univ_three, h0, h1, one_mul, one_mul] at hdet
  refine ⟨fun i j hij => hU hij, fun i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact hdet

variable [Finite k]

theorem card_dvd_of_le_upperTriangular [CharP k 2] {Y : Subgroup (SpecialLinearGroup (Fin 3) k)}
    (hY : Y ≤ upperTriangular 3 k) (hodd : Odd (Nat.card Y)) :
    Nat.card Y ∣ Nat.card kˣ * Nat.card kˣ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := k) 2 (n := 3) (by norm_num)
  have hU2 : IsPGroup 2 (unitriangular 3 k) := by rw [← hP]; exact P.isPGroup'
  set f : ↥Y →* kˣ × kˣ := diagTwo.comp (Subgroup.inclusion hY) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyU : (y : SpecialLinearGroup (Fin 3) k) ∈ unitriangular 3 k :=
      mem_unitriangular_of_diagTwo_eq_one (A := Subgroup.inclusion hY y) hy
    obtain ⟨m, hm⟩ := hU2 ⟨_, hyU⟩
    have hm' : y ^ 2 ^ m = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
    have hcop : Nat.Coprime (2 ^ m) (Nat.card Y) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have h1 : orderOf y ∣ Nat.gcd (2 ^ m) (Nat.card Y) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_natCard y)
    rw [hcop] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  rw [← Nat.card_prod]
  exact Subgroup.card_dvd_of_injective f hinj

theorem card_scalars_three (hk : Nat.card k = 4) : Nat.card (scalars 3 k) = 3 := by
  have hdvd : Nat.card (scalars 3 k) ∣ 3 := by
    have := card_scalars_dvd (K := k) (n := 3) (by norm_num)
    rwa [hk] at this
  have hu : Nat.card kˣ = 3 := by rw [Nat.card_units, hk]
  obtain ⟨ω, hω⟩ : ∃ ω : kˣ, ω ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Nat.card kˣ ≤ 1 := by
      have : Subsingleton kˣ := ⟨fun a b => (hall a).trans (hall b).symm⟩
      exact Finite.card_le_one_iff_subsingleton.mpr this
    omega
  have hω3 : ω ^ 3 = 1 := by
    have := pow_card_eq_one' (G := kˣ) (x := ω)
    rwa [hu] at this
  have hne : scalarElement ω hω3 ≠ 1 := by
    intro h1
    apply hω
    have := congrArg (fun A : SpecialLinearGroup (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k) 0 0) h1
    simp only [coe_scalarElement] at this
    exact Units.ext (by simpa [scalar_apply] using this)
  have h2 : 2 ≤ Nat.card (scalars 3 k) := by
    have hnt : Nontrivial (scalars 3 k) :=
      ⟨⟨⟨_, scalarElement_mem_scalars ω hω3⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card (scalars 3 k) <;> simp_all

end Borel

theorem l34BorelFact : L34BorelFact := by
  intro X _ _ hX S Y hS hYN hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP k 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card (n := 2)
      (by rw [hk]; norm_num)
  set P := projectiveSL 3 k
  have hS2 : IsPGroup 2 (S.map e.toMonoidHom) := hS.2.1.map _
  have hSi : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    have := hS.2.2
    change ¬ 2 ∣ S.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  let PS : Sylow 2 P := hS2.toSylow hSi
  obtain ⟨PU, hPU⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq P PU PS
  have hPS : (PS : Subgroup P) = (projUnitriangular 3 k).map (MulAut.conj x : P →* P) := by
    rw [← hx, coe_sylow_smul, hPU]
  have hYN' : Y.map e.toMonoidHom ≤
      (projUpperTriangular 3 k).map (MulAut.conj x : P →* P) := by
    have h1 : Y.map e.toMonoidHom ≤
        Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup P) : Set P) := by
      rw [← Subgroup.map_equiv_normalizer_eq S e]
      exact Subgroup.map_mono hYN
    have h2 : (S.map e.toMonoidHom : Subgroup P) = (PS : Subgroup P) := rfl
    rw [h2, hPS, normalizer_map_conj, normalizer_projUnitriangular 2] at h1
    exact h1
  set Y₀ := (Y.map e.toMonoidHom).map (MulAut.conj x⁻¹ : P →* P) with hY₀
  have hY₀B : Y₀ ≤ projUpperTriangular 3 k := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb, hby⟩ := hYN' hy
    rw [← hby]
    change (MulAut.conj x⁻¹) ((MulAut.conj x) b) ∈ _
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    exact hb
  have hcardY₀ : Nat.card Y₀ = Nat.card Y := by
    rw [hY₀, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective,
      Subgroup.card_map_of_injective e.injective]
  have hpk : ∀ A, proj 3 k A = 1 ↔ A ∈ scalars 3 k := fun A => QuotientGroup.eq_one_iff A
  set Ŷ := Y₀.comap (proj 3 k) with hŶ
  have hŶB : Ŷ ≤ upperTriangular 3 k := by
    intro A hA
    obtain ⟨B, hB, hBA⟩ := hY₀B hA
    have hBA' : B⁻¹ * A ∈ scalars 3 k := by
      rw [← hpk, map_mul, map_inv, hBA, inv_mul_cancel]
    have := (upperTriangular 3 k).mul_mem hB (scalars_le_upperTriangular 3 k hBA')
    rwa [mul_inv_cancel_left] at this
  have hZŶ : scalars 3 k ≤ Ŷ := by
    intro A hA
    show proj 3 k A ∈ Y₀
    rw [(hpk A).mpr hA]
    exact Y₀.one_mem
  have hcardŶ : Nat.card Ŷ = Nat.card (scalars 3 k) * Nat.card Y₀ := by
    have h := Subgroup.card_ker_mul_card_range ((proj 3 k).comp Ŷ.subtype)
    have hker : ((proj 3 k).comp Ŷ.subtype).ker = (scalars 3 k).subgroupOf Ŷ := by
      ext A
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
      exact hpk A
    have hrange : ((proj 3 k).comp Ŷ.subtype).range = Y₀ := by
      apply le_antisymm
      · rintro _ ⟨A, rfl⟩
        exact A.2
      · intro y hy
        obtain ⟨A, rfl⟩ := proj_surjective 3 k y
        exact ⟨⟨A, hy⟩, rfl⟩
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZŶ).toEquiv] at h
    exact h.symm
  have hZ3 := card_scalars_three hk
  have hu : Nat.card kˣ = 3 := by rw [Nat.card_units, hk]
  have hoddŶ : Odd (Nat.card Ŷ) := by
    rw [hcardŶ, hZ3, hcardY₀]
    exact Odd.mul (Nat.odd_iff.mpr rfl) hodd
  have h9 := card_dvd_of_le_upperTriangular hŶB hoddŶ
  rw [hcardŶ, hZ3, hu, hcardY₀] at h9
  exact Nat.dvd_of_mul_dvd_mul_left (show 0 < 3 by norm_num) h9

end CFSG.Quasithin.H13
