module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvectionCore
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open Matrix CFSG.SeitzReduction.UnitaryPilot
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj

variable {K : Type} [Field K]

private lemma test_center (hK : Nat.card K = 4) :
    Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = ⊥ := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup U :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 (by rw [hK]; norm_num) 6
      (by norm_num) (by norm_num)
  have hnc : ¬ IsMulCommutative U := by
    intro hU
    haveI := hU
    haveI hcomm : IsMulCommutative (blockFourU hK) := inferInstance
    have hprime := (Group.is_simple_iff_prime_card).mp (isSimpleGroup_blockFourU hK)
    rw [card_blockFourU hK] at hprime
    norm_num at hprime
  haveI : (Subgroup.center U).Normal := inferInstance
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center U) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc

private lemma test_conj_inj (hK : Nat.card K = 4) :
    Function.Injective (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) := by
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  intro a b hab
  have hZ := test_center hK
  have h : MulAut.conj (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hz : a * b⁻¹ ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun f : MulAut U => f g) h
    have hg : (a * b⁻¹) * g * (a * b⁻¹)⁻¹ = g := h2
    calc g * (a * b⁻¹) = ((a * b⁻¹) * g * (a * b⁻¹)⁻¹) * (a * b⁻¹) := by rw [hg]
      _ = (a * b⁻¹) * g := by group
  rw [hZ, Subgroup.mem_bot] at hz
  exact mul_inv_eq_one.mp hz

lemma card_Oinn_le (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))}
    (hH : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H)
    (h2 : ((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range.subgroupOf H).index ≤ 2) :
    Nat.card ↥(pCoreOf 2 (H ⊓ Subgroup.centralizer {MulAut.conj (tZero hK)}) ⊓
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range) ≤ 2 ^ 9 := by
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  letI : Field K := inferInstance
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let t : U := tZero hK
  let ct : MulAut U := MulAut.conj t
  let Inn : Subgroup (MulAut U) := (MulAut.conj : U →* MulAut U).range
  let G : Subgroup (MulAut U) := H ⊓ Subgroup.centralizer ({ct} : Set (MulAut U))
  let O : Subgroup (MulAut U) := pCoreOf 2 G
  let Kc : Subgroup U := Subgroup.centralizer ({t} : Set U)
  let Q0 : Subgroup U := pCoreOf 2 Kc
  have hG_def : G = H ⊓ Subgroup.centralizer ({ct} : Set (MulAut U)) := rfl
  have hInn_le_H : Inn ≤ H := hH
  have hO_le_G : O ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hinj := test_conj_inj hK
  have hO_norm : (O.subgroupOf G).Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_G).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  have hInn_norm : Inn.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    change n ∈ (MulAut.conj : U →* MulAut U).range at hn
    change g * n * g⁻¹ ∈ (MulAut.conj : U →* MulAut U).range
    rw [MonoidHom.mem_range] at hn ⊢
    obtain ⟨y, rfl⟩ := hn
    refine ⟨g y, ?_⟩
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
  let Qpre : Subgroup U := (O ⊓ Inn).comap (MulAut.conj : U →* MulAut U)
  have hQpre_le : Qpre ≤ Kc := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    have hxG : MulAut.conj x ∈ G := hO_le_G hx.1
    have hxcomm : MulAut.conj x * ct = ct * MulAut.conj x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxG.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : MulAut.conj (x * t) = MulAut.conj (t * x) := by
      rw [map_mul, map_mul]
      exact hxcomm
    exact hinj hc
  have hQpre_norm : (Qpre.subgroupOf Kc).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn k
    have hn' : (n : U) ∈ Qpre := by simpa [Subgroup.mem_subgroupOf] using hn
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap] at hn' ⊢
    have hkCI : (k : U) ∈ Subgroup.centralizer ({t} : Set U) := k.2
    have hck_range : MulAut.conj (k : U) ∈ Inn := by
      change MulAut.conj (k : U) ∈ (MulAut.conj : U →* MulAut U).range
      exact ⟨(k : U), rfl⟩
    have hck_cent : MulAut.conj (k : U) ∈ Subgroup.centralizer ({ct} : Set (MulAut U)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkt : (k : U) * t = t * (k : U) :=
        Subgroup.mem_centralizer_singleton_iff.mp hkCI
      rw [← map_mul, ← map_mul, hkt]
    have hckG : MulAut.conj (k : U) ∈ G := ⟨hInn_le_H hck_range, hck_cent⟩
    constructor
    · have hOnormG : G ≤ Subgroup.normalizer (O : Set (MulAut U)) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
      have hcO : MulAut.conj (k : U) * MulAut.conj (n : U) * (MulAut.conj (k : U))⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hOnormG hckG) (MulAut.conj (n : U))).mp hn'.1
      simpa [map_mul, map_inv] using hcO
    · have hcI := hInn_norm.conj_mem (MulAut.conj (n : U)) hn'.2 (MulAut.conj (k : U))
      simpa [map_mul, map_inv] using hcI
  have hQpre_p : IsPGroup 2 Qpre := by
    have hOp : IsPGroup 2 ↥(O ⊓ Inn) := by
      simpa [O] using (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).to_inf_left
    exact hOp.comap_of_injective (MulAut.conj : U →* MulAut U) hinj
  have hQpre_le_Q0 : Qpre ≤ Q0 := by
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hQpre_le hQpre_norm hQpre_p
  have hmap : Subgroup.map (MulAut.conj : U →* MulAut U) Qpre = O ⊓ Inn := by
    exact Subgroup.map_comap_eq_self (by exact inf_le_right)
  have hcard : Nat.card ↥(O ⊓ Inn) = Nat.card ↥Qpre := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective hinj
  calc Nat.card ↥(O ⊓ Inn) = Nat.card ↥Qpre := hcard
    _ ≤ Nat.card ↥Q0 := Subgroup.card_le_of_le hQpre_le_Q0
    _ = 2 ^ 9 := card_pCoreOf_centralizer_tZero hK

lemma comap_Oinn_le_pCore (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))}
    (hH : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H) :
    ((pCoreOf 2 (H ⊓ Subgroup.centralizer {MulAut.conj (tZero hK)}) ⊓
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range).comap
      (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) ≤
      pCoreOf 2 (Subgroup.centralizer {tZero hK}) := by
  let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let t : U := tZero hK
  let ct : MulAut U := MulAut.conj t
  let Inn : Subgroup (MulAut U) := (MulAut.conj : U →* MulAut U).range
  let G : Subgroup (MulAut U) := H ⊓ Subgroup.centralizer ({ct} : Set (MulAut U))
  let O : Subgroup (MulAut U) := pCoreOf 2 G
  let Kc : Subgroup U := Subgroup.centralizer ({t} : Set U)
  let Q0 : Subgroup U := pCoreOf 2 Kc
  have hInn_le_H : Inn ≤ H := hH
  have hO_le_G : O ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hinj := test_conj_inj (K := K) hK
  have h1 : t = tZero hK := rfl
  have hInn_norm : Inn.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    change n ∈ (MulAut.conj : U →* MulAut U).range at hn
    change g * n * g⁻¹ ∈ (MulAut.conj : U →* MulAut U).range
    rw [MonoidHom.mem_range] at hn ⊢
    obtain ⟨y, rfl⟩ := hn
    refine ⟨g y, ?_⟩
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
  let Qpre : Subgroup U := (O ⊓ Inn).comap (MulAut.conj : U →* MulAut U)
  have hQpre_le : Qpre ≤ Kc := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    have hxG : MulAut.conj x ∈ G := hO_le_G hx.1
    have hxcomm : MulAut.conj x * ct = ct * MulAut.conj x :=
      Subgroup.mem_centralizer_singleton_iff.mp hxG.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : MulAut.conj (x * t) = MulAut.conj (t * x) := by
      rw [map_mul, map_mul]
      exact hxcomm
    exact hinj hc
  have hQpre_norm : (Qpre.subgroupOf Kc).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn k
    have hn' : (n : U) ∈ Qpre := by simpa [Subgroup.mem_subgroupOf] using hn
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap] at hn' ⊢
    have hkCI : (k : U) ∈ Subgroup.centralizer ({t} : Set U) := k.2
    have hck_range : MulAut.conj (k : U) ∈ Inn := by
      change MulAut.conj (k : U) ∈ (MulAut.conj : U →* MulAut U).range
      exact ⟨(k : U), rfl⟩
    have hck_cent : MulAut.conj (k : U) ∈ Subgroup.centralizer ({ct} : Set (MulAut U)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkt : (k : U) * t = t * (k : U) :=
        Subgroup.mem_centralizer_singleton_iff.mp hkCI
      rw [← map_mul, ← map_mul, hkt]
    have hckG : MulAut.conj (k : U) ∈ G := ⟨hInn_le_H hck_range, hck_cent⟩
    constructor
    · have hOnormG : G ≤ Subgroup.normalizer (O : Set (MulAut U)) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
      have hcO : MulAut.conj (k : U) * MulAut.conj (n : U) * (MulAut.conj (k : U))⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hOnormG hckG) (MulAut.conj (n : U))).mp hn'.1
      simpa [map_mul, map_inv] using hcO
    · have hcI := hInn_norm.conj_mem (MulAut.conj (n : U)) hn'.2 (MulAut.conj (k : U))
      simpa [map_mul, map_inv] using hcI
  have hQpre_p : IsPGroup 2 Qpre := by
    have hOp : IsPGroup 2 ↥(O ⊓ Inn) := by
      simpa [O] using (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).to_inf_left
    exact hOp.comap_of_injective (MulAut.conj : U →* MulAut U) hinj
  have hQpre_le_Q0 : Qpre ≤ Q0 :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hQpre_le hQpre_norm hQpre_p
  simpa [Qpre, O, Inn, G, ct, Kc, Q0, t, U, h1] using hQpre_le_Q0

lemma test_mem_inn_uConjAut_iff (hK : Nat.card K = 4)
    (A : ↥(uU (fieldDataFour hK) 6)) :
    uConjAut (fieldDataFour hK) one_le_six A ∈
      (MulAut.conj : StatedProj (StatedSU 6 (2 ^ 1) K) →*
        MulAut (StatedProj (StatedSU 6 (2 ^ 1) K))).range ↔
      Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K)) = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [inn_eq_map_SUu hK]
  constructor
  · rintro ⟨B, hB, hBA⟩
    have hBdet : Matrix.GeneralLinearGroup.det ((B : GL (Fin 6) K)) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact (mem_SU_iff (fieldDataFour hK)).mp ((mem_SUu hK).mp hB) |>.1
    have h1 : uConjAut (fieldDataFour hK) one_le_six (A * B⁻¹) = 1 := by
      rw [map_mul, map_inv, hBA, mul_inv_cancel]
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff (fieldDataFour hK) three_le_six (A * B⁻¹)).mp h1
    have hc6 : c ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, cube_unit_eq_one hK c, one_pow]
    have hdet := congrArg (fun x : GL (Fin 6) K => Matrix.GeneralLinearGroup.det x) hc
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hc6] at hdet
    simpa [hBdet] using hdet
  · intro hdet
    have hASU : A ∈ SUu hK := by
      rw [mem_SUu]
      refine (mem_SU_iff (fieldDataFour hK)).mpr ⟨?_, (mem_uU (fieldDataFour hK)).mp A.2⟩
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      simpa using congrArg Units.val hdet
    exact Subgroup.mem_map.mpr ⟨A, hASU, rfl⟩

lemma B1_decomp (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))}
    (hH : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H)
    (h2 : ((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range.subgroupOf H).index ≤ 2)
    {x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hxG : x ∈ H ⊓ Subgroup.centralizer {MulAut.conj (tZero hK)})
    (hxInn : x ∉ (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range) :
    ∃ (A : ↥(uU (fieldDataFour hK) 6)) (φ : K ≃+* K), φ ≠ 1 ∧
      x = uConjAut (fieldDataFour hK) one_le_six A * uFieldAut (fieldDataFour hK) one_le_six φ := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let U := StatedProj (StatedSU 6 (2 ^ 1) K)
  let H' : Subgroup (MulAut U) := H
  let Inn : Subgroup (MulAut U) := (MulAut.conj : U →* MulAut U).range
  let x' : MulAut U := x
  have hH' : Inn ≤ H' := hH
  have h2' : (Inn.subgroupOf H').index ≤ 2 := h2
  have hxG' : x' ∈ H' ⊓ Subgroup.centralizer ({MulAut.conj (tZero hK)} : Set (MulAut U)) := hxG
  have hxInn' : x' ∉ Inn := hxInn
  have hxH : x' ∈ H' := hxG'.1
  haveI : Finite U := inferInstance
  haveI : Finite (MulAut U) := inferInstance
  haveI : (Inn.subgroupOf H').FiniteIndex := Subgroup.finiteIndex_of_finite
  have hidx2 : (Inn.subgroupOf H').index = 2 := by
    have hpos : (Inn.subgroupOf H').index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hne1 : (Inn.subgroupOf H').index ≠ 1 := by
      intro h1
      have htop : Inn.subgroupOf H' = ⊤ := Subgroup.index_eq_one.mp h1
      have hxmem : (⟨x', hxH⟩ : H') ∈ Inn.subgroupOf H' := by
        rw [htop]
        exact Subgroup.mem_top (⟨x', hxH⟩ : H')
      exact hxInn' (by simpa [Subgroup.mem_subgroupOf] using hxmem)
    omega
  obtain ⟨A, φ, hxA⟩ :=
    exists_uConjAut_mul_uFieldAut (fieldDataFour hK) three_le_six six_not_exception x'
  by_cases hφ : φ = 1
  · exfalso
    have hx2sub : (⟨x', hxH⟩ : H') ^ 2 ∈ Inn.subgroupOf H' :=
      Subgroup.sq_mem_of_index_two hidx2 ⟨x', hxH⟩
    have hx2 : x' ^ 2 ∈ Inn := by
      simpa [Subgroup.mem_subgroupOf, Subgroup.coe_pow] using hx2sub
    have hx2eq : x' ^ 2 = uConjAut (fieldDataFour hK) one_le_six (A * A) := by
      rw [hxA, hφ, map_one, mul_one, pow_two, ← map_mul]
    rw [hx2eq] at hx2
    change uConjAut (fieldDataFour hK) one_le_six (A * A) ∈
      (MulAut.conj : StatedProj (StatedSU 6 (2 ^ 1) K) →*
        MulAut (StatedProj (StatedSU 6 (2 ^ 1) K))).range at hx2
    have hdet2 : Matrix.GeneralLinearGroup.det
        ((A * A : ↥(uU (fieldDataFour hK) 6)) : GL (Fin 6) K) = 1 :=
      (test_mem_inn_uConjAut_iff hK (A * A)).mp hx2
    have hdet : Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K)) = 1 := by
      have hA2 : Matrix.GeneralLinearGroup.det
          ((A * A : ↥(uU (fieldDataFour hK) 6)) : GL (Fin 6) K) =
          Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K)) *
            Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K)) := by
        rw [Subgroup.coe_mul, map_mul]
      have hcube : (Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K))) ^ 3 = 1 :=
        cube_unit_eq_one hK _
      have hsq : (Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K))) ^ 2 = 1 := by
        rw [pow_two, ← hA2, hdet2]
      have hord : orderOf (Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K))) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hsq
      have hord3 : orderOf (Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K))) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one hcube
      have h1 : orderOf (Matrix.GeneralLinearGroup.det ((A : GL (Fin 6) K))) = 1 := by
        have hdvd := Nat.dvd_gcd hord hord3
        rw [show Nat.gcd 2 3 = 1 by norm_num] at hdvd
        exact Nat.dvd_one.mp hdvd
      exact orderOf_eq_one_iff.mp h1
    have hxinn : x' ∈ Inn := by
      rw [hxA, hφ, map_one, mul_one]
      exact (test_mem_inn_uConjAut_iff hK A).mpr hdet
    exact hxInn' hxinn
  · exact ⟨A, φ, hφ, hxA⟩

lemma tZeroSU_eq_tv (hK : Nat.card K = 4) :
    tZeroSU hK = tvTransSU (fieldDataFour hK) (by decide : (0 : Fin 6) ≠ 1) := by
  haveI := charP_two_of_card_four hK
  apply eq_of_coe_eq
  rw [tZeroSU, coe_permSU, coe_tvTransSU]
  ext i j
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Matrix.add_apply,
    Matrix.one_apply, tvNil, Matrix.vecMulVec, tvVec_apply, Pi.add_apply]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
    subst_vars <;> simp_all [Equiv.swap_apply_def, Pi.single_apply, eq_comm, two_eq_zero hK,
      one_add_one_eq_zero hK]

lemma glAut_tZeroSU (hK : Nat.card K = 4) (φ : K ≃+* K) :
    glAut φ ((tZeroSU hK : GL (Fin 6) K)) = (tZeroSU hK : GL (Fin 6) K) := by
  apply Units.ext
  rw [coe_glAut, tZeroSU, coe_permSU]
  ext i j
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Matrix.map_apply]
  by_cases hij : (Equiv.swap (0 : Fin 6) 1) i = j <;> simp [hij]

lemma hmat_exists (hK : Nat.card K = 4) (A : ↥(uU (fieldDataFour hK) 6))
    (φ : K ≃+* K)
    (x : MulAut (StatedProj (StatedSU 6 (2 ^ 1) K)))
    (t : StatedProj (StatedSU 6 (2 ^ 1) K))
    (Pt : ↥(StatedSU 6 (2 ^ 1) K)) (ht : t = projH (StatedSU 6 (2 ^ 1) K) Pt)
    (hφPt : glAut φ ((Pt : GL (Fin 6) K)) = (Pt : GL (Fin 6) K))
    (hxA : x = uConjAut (fieldDataFour hK) one_le_six A *
      uFieldAut (fieldDataFour hK) one_le_six φ)
    (hxcent : x * MulAut.conj t = MulAut.conj t * x) :
    ∃ c : K, ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((Pt : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      c • ((Pt : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let M : ↥(StatedSU 6 (2 ^ 1) K) :=
    ⟨(A : GL (Fin 6) K) * (Pt : GL (Fin 6) K) * ((A : GL (Fin 6) K))⁻¹,
      uConjSU_mem (fieldDataFour hK) A Pt⟩
  have hxP : x t = t := by
    have hconj : MulAut.conj (x t) = MulAut.conj t := by
      calc MulAut.conj (x t) = x * MulAut.conj t * x⁻¹ := by
            ext y; simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
        _ = MulAut.conj t := by rw [hxcent]; group
    have hZ : Subgroup.center (StatedProj (StatedSU 6 (2 ^ 1) K)) = ⊥ := by
      haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
      exact (show Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = ⊥ from by
        let U := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hsimple : IsSimpleGroup U :=
          CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1
            (by rw [hK]; norm_num) 6 (by norm_num) (by norm_num)
        have hnc : ¬ IsMulCommutative U := by
          intro hU
          haveI := hU
          haveI hcomm : IsMulCommutative (blockFourU hK) := inferInstance
          have hprime := (Group.is_simple_iff_prime_card).mp (isSimpleGroup_blockFourU hK)
          rw [card_blockFourU hK] at hprime
          norm_num at hprime
        haveI : (Subgroup.center U).Normal := inferInstance
        rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center U) with h | h
        · exact h
        · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc)
    have hinj : Function.Injective (MulAut.conj :
        StatedProj (StatedSU 6 (2 ^ 1) K) →*
          MulAut (StatedProj (StatedSU 6 (2 ^ 1) K))) := by
      intro a b hab
      have h : MulAut.conj (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      have hz : a * b⁻¹ ∈ Subgroup.center (StatedProj (StatedSU 6 (2 ^ 1) K)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h2 := congrArg (fun f : MulAut (StatedProj (StatedSU 6 (2 ^ 1) K)) => f g) h
        have hg : (a * b⁻¹) * g * (a * b⁻¹)⁻¹ = g := h2
        calc g * (a * b⁻¹) = ((a * b⁻¹) * g * (a * b⁻¹)⁻¹) * (a * b⁻¹) := by rw [hg]
          _ = (a * b⁻¹) * g := by group
      rw [hZ, Subgroup.mem_bot] at hz
      exact mul_inv_eq_one.mp hz
    exact hinj hconj
  have hfP : (uFieldAut (fieldDataFour hK) one_le_six φ)
      (projH (StatedSU 6 (2 ^ 1) K) Pt) = projH (StatedSU 6 (2 ^ 1) K) Pt := by
    rw [uFieldAut_proj]
    exact congrArg (projH (StatedSU 6 (2 ^ 1) K)) (Subtype.ext hφPt)
  have hxM : x t = (M : StatedProj (StatedSU 6 (2 ^ 1) K)) := by
    rw [ht, hxA, MulAut.mul_apply, hfP, uConjAut_proj]
    rfl
  have hπ : (M : StatedProj (StatedSU 6 (2 ^ 1) K)) =
      (Pt : StatedProj (StatedSU 6 (2 ^ 1) K)) := by
    rw [← hxM, hxP]
    exact ht
  have hmem : (M / Pt) ∈ (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K) :=
    QuotientGroup.eq_iff_div_mem.mp hπ
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  have hMgl : (M : GL (Fin 6) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * (Pt : GL (Fin 6) K) := by
    calc (M : GL (Fin 6) K) = ((M / Pt : ↥(StatedSU 6 (2 ^ 1) K)) : GL (Fin 6) K) *
          (Pt : GL (Fin 6) K) := by
          rw [Subgroup.coe_div, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (Pt : GL (Fin 6) K) := by rw [hc]
  have hmat := congrArg (fun g : GL (Fin 6) K => ((g : Matrix (Fin 6) (Fin 6) K))) hMgl
  simp only [Matrix.GeneralLinearGroup.coe_mul, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Subgroup.coe_inv] at hmat ⊢
  show ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      c • ((Pt : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  rw [hmat, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  rw [Units.smul_def]

lemma AN_comm (hK : Nat.card K = 4) (A : ↥(uU (fieldDataFour hK) 6))
    (φ : K ≃+* K)
    (x : MulAut (StatedProj (StatedSU 6 (2 ^ 1) K)))
    (t : StatedProj (StatedSU 6 (2 ^ 1) K)) (ht0 : t = tZero hK)
    (hxA : x = uConjAut (fieldDataFour hK) one_le_six A *
      uFieldAut (fieldDataFour hK) one_le_six φ)
    (hxcent : x * MulAut.conj t = MulAut.conj t * x) :
    ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI := charP_two_of_card_four hK
  let Pt : ↥(StatedSU 6 (2 ^ 1) K) := tZeroSU hK
  have ht : t = projH (StatedSU 6 (2 ^ 1) K) Pt := by rw [ht0]; rfl
  have hφPt : glAut φ ((Pt : GL (Fin 6) K)) = (Pt : GL (Fin 6) K) := by
    exact glAut_tZeroSU hK φ
  have hxcent' : x * MulAut.conj t = MulAut.conj t * x := hxcent
  obtain ⟨c, hmat⟩ := hmat_exists hK A φ x t Pt ht hφPt hxA hxcent'
  set N : Matrix (Fin 6) (Fin 6) K := tvNil (K := K) (n := 6) 0 1 with hNdef
  have hN : N * N = 0 := by
    rw [hNdef, tvNil, vecMulVec_mul_vecMulVec]
    simp [tvVec_dotProduct_self (by decide : (0:Fin 6) ≠ 1)]
  have hPmat : ((Pt : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 + N := by
    change ((tZeroSU hK : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 + N
    rw [hNdef, tZeroSU_eq_tv hK, coe_tvTransSU]
  have hAinvA : ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      (inv_mul_cancel (A : GL (Fin 6) K))
    simpa [Matrix.GeneralLinearGroup.coe_mul] using this
  have hAA : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      (mul_inv_cancel (A : GL (Fin 6) K))
    simpa [Matrix.GeneralLinearGroup.coe_mul] using this
  have hmat' : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (1 + N) *
        ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      c • (1 + N) := by
    rw [← hPmat, hmat]
  have hAN : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
        ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (c + 1) • (1 : Matrix (Fin 6) (Fin 6) K) + c • N := by
    have hplus := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M + 1) hmat'
    have h11 : (1 : Matrix (Fin 6) (Fin 6) K) + 1 = 0 := by
      ext i j
      simp [Matrix.add_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij, one_add_one_eq_zero hK]
    have hL : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (1 + N) *
          ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) + 1 =
        ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
          ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAA]
      rw [add_assoc, add_comm (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
        ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 1, ← add_assoc, h11, zero_add]
    have hR : c • (1 + N) + 1 =
        (c + 1) • (1 : Matrix (Fin 6) (Fin 6) K) + c • N := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
      ring
    rw [hL, hR] at hplus
    exact hplus
  have hc_eq_one : c = 1 := by
    by_contra hc
    have hc' : c + 1 ≠ 0 := by
      intro h
      apply hc
      linear_combination h - one_add_one_eq_zero hK
    have hu : IsUnit ((c + 1) • (1 : Matrix (Fin 6) (Fin 6) K)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one,
        Fintype.card_fin]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero 6 hc')
    have hnilR : IsNilpotent (c • N) := by
      refine ⟨2, ?_⟩
      rw [pow_two, smul_mul_smul, hN, smul_zero]
    have hcomm : Commute ((c + 1) • (1 : Matrix (Fin 6) (Fin 6) K)) (c • N) := by
      rw [Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply]
      exact Matrix.scalar_commute (c + 1) (fun _ => Commute.all _ _) (c • N)
    have hunit : IsUnit ((c + 1) • (1 : Matrix (Fin 6) (Fin 6) K) + c • N) :=
      IsNilpotent.isUnit_add_left_of_commute hnilR hu hcomm.symm
    have hnilL : IsNilpotent (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
        ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
      refine ⟨2, ?_⟩
      rw [pow_two]
      calc (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
              ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
            (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
              ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
          = ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
              (((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
                ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * N *
              ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by noncomm_ring
        _ = ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N * 1 * N *
              ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by rw [hAinvA]
        _ = ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (N * N) *
              ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by noncomm_ring
        _ = 0 := by rw [hN]; simp
    rw [hAN] at hnilL
    exact IsNilpotent.not_isUnit hnilL hunit
  have hAcommP : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (1 + N) *
      ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 + N := by
    rw [← hPmat, hmat, hc_eq_one, one_smul]
  have hANP : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
      ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = N := by
    have hplus := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M + 1) hAcommP
    have h11 : (1 : Matrix (Fin 6) (Fin 6) K) + 1 = 0 := by
      ext i j
      simp [Matrix.add_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij, one_add_one_eq_zero hK]
    have hL : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (1 + N) *
          ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) + 1 =
        ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
          ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAA]
      rw [add_assoc, add_comm (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
        ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 1, ← add_assoc, h11, zero_add]
    have hR : (1 + N : Matrix (Fin 6) (Fin 6) K) + 1 = N := by
      calc 1 + N + 1 = (1 + 1) + N := by abel
        _ = N := by rw [h11, zero_add]
    rw [hL, hR] at hplus
    exact hplus
  calc ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N
      = ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
          (((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by rw [hAinvA, mul_one]
    _ = (((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * N *
          ((A⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
          ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by noncomm_ring
    _ = N * ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by rw [hANP]

lemma tvBlock_mul_of_commute_tvNil (hK : Nat.card K = 4)
    {M M' : Matrix (Fin 6) (Fin 6) K}
    (hM : M * tvNil (K := K) (n := 6) 0 1 = tvNil (K := K) (n := 6) 0 1 * M)
    (hM' : M' * tvNil (K := K) (n := 6) 0 1 = tvNil (K := K) (n := 6) 0 1 * M') :
    tvBlock (0 : Fin 6) 1 (M * M') =
      tvBlock (0 : Fin 6) 1 M * tvBlock (0 : Fin 6) 1 M' := by
  haveI := charP_two_of_card_four hK
  have h01 : (0 : Fin 6) ≠ 1 := by decide
  have hrow : ∀ k ∈ ({0, 1}ᶜ : Finset (Fin 6)), M k 0 = M k 1 := by
    obtain ⟨μ, h1, -⟩ := (commute_tvNil_iff (i := 0) (j := 1) h01 (M := M)).mp hM
    exact fun k hk => eq_of_mulVec_tvVec h1 hk
  have hcol : ∀ l ∈ ({0, 1}ᶜ : Finset (Fin 6)), M' 0 l = M' 1 l := by
    obtain ⟨μ, -, h2⟩ := (commute_tvNil_iff (i := 0) (j := 1) h01 (M := M')).mp hM'
    exact fun l hl => eq_of_vecMul_tvVec h2 hl
  exact tvBlock_mul h01 hrow hcol

lemma scalar_of_proj_eq (hK : Nat.card K = 4) {M P : ↥(StatedSU 6 (2 ^ 1) K)}
    (h : (M : StatedProj (StatedSU 6 (2 ^ 1) K)) = (P : StatedProj (StatedSU 6 (2 ^ 1) K))) :
    ∃ c : Kˣ, (M : GL (Fin 6) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c * (P : GL (Fin 6) K) := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hmem : (M / P) ∈ (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K) :=
    QuotientGroup.eq_iff_div_mem.mp h
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
  obtain ⟨c : Kˣ, hc⟩ := hmem
  refine ⟨c, ?_⟩
  calc (M : GL (Fin 6) K) = ((M / P : ↥(StatedSU 6 (2 ^ 1) K)) : GL (Fin 6) K) *
        (P : GL (Fin 6) K) := by
        rw [Subgroup.coe_div, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
    _ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * (P : GL (Fin 6) K) := by rw [hc]

lemma trace_tvBlock_unitaryBlockEquiv (hK : Nat.card K = 4)
    (X : ↥(unitarySU 2 1 K ({0, 1}ᶜ : Finset (Fin 6)).card)) :
    (tvBlock (0 : Fin 6) 1
      ((((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
        ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
        ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace =
      (((X : GL (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K)) :
        Matrix (Fin ({0, 1}ᶜ : Finset (Fin 6)).card)
          (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K).trace := by
  have hblock : tvBlock (0 : Fin 6) 1
      ((((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
        ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
        ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.reindex ({0, 1}ᶜ : Finset (Fin 6)).equivFin.symm
        ({0, 1}ᶜ : Finset (Fin 6)).equivFin.symm
        (((X : GL (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K) :
          Matrix (Fin ({0, 1}ᶜ : Finset (Fin 6)).card)
            (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K)) := by
    rw [coe_unitaryBlockEquiv, coe_unitaryBlockEmbed]
    ext a b
    rw [tvBlock_apply, CFSG.SeitzReduction.LinearPilot.blockMatrix_apply, dif_pos ⟨a.2, b.2⟩]
  rw [hblock]
  exact (by
    simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Fintype.sum_equiv ({0, 1}ᶜ : Finset (Fin 6)).equivFin.symm]
    intro i
    simp)

lemma det_tvBlock_unitaryBlockEquiv (hK : Nat.card K = 4)
    (X : ↥(unitarySU 2 1 K ({0, 1}ᶜ : Finset (Fin 6)).card)) :
    (tvBlock (0 : Fin 6) 1
      ((((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
        ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
        ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).det = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hblock : tvBlock (0 : Fin 6) 1
      ((((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
        ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
        ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.reindex ({0, 1}ᶜ : Finset (Fin 6)).equivFin.symm
        ({0, 1}ᶜ : Finset (Fin 6)).equivFin.symm
        (((X : GL (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K) :
          Matrix (Fin ({0, 1}ᶜ : Finset (Fin 6)).card)
            (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K)) := by
    rw [coe_unitaryBlockEquiv, coe_unitaryBlockEmbed]
    ext a b
    rw [tvBlock_apply, CFSG.SeitzReduction.LinearPilot.blockMatrix_apply, dif_pos ⟨a.2, b.2⟩]
  rw [hblock, Matrix.det_reindex_self]
  have hX : ((X : GL (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K) :
      Matrix (Fin ({0, 1}ᶜ : Finset (Fin 6)).card)
        (Fin ({0, 1}ᶜ : Finset (Fin 6)).card) K).det = 1 := by
    have := (mem_unitarySU_iff (fieldDataFour hK)).mp X.2
    simpa using this.1
  exact hX

lemma block_eq (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))}
    (hH : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H)
    {x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hxO : x ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer
      ({MulAut.conj (tZero hK)} :
        Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))))
    {A : ↥(uU (fieldDataFour hK) 6)} {φ : K ≃+* K}
    (hxA : x = uConjAut (fieldDataFour hK) one_le_six A *
      uFieldAut (fieldDataFour hK) one_le_six φ)
    (hxcent : x * MulAut.conj (tZero hK) = MulAut.conj (tZero hK) * x)
    (hAcommN : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      tvNil (K := K) (n := 6) 0 1 = tvNil (K := K) (n := 6) 0 1 *
        ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    (X : ↥(unitarySU 2 1 K ({0, 1}ᶜ : Finset (Fin 6)).card)) :
    let k : ↥(unitarySU 2 1 K 6) :=
      ((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
        ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
        ↥(unitarySU 2 1 K 6))
    tvBlock (0 : Fin 6) 1 ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (tvBlock (0 : Fin 6) 1 ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).map φ *
        tvBlock (0 : Fin 6) 1 (((A⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) =
      tvBlock (0 : Fin 6) 1 ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  dsimp only
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let U := StatedProj (StatedSU 6 (2 ^ 1) K)
  let t0 : ↥(unitarySU 2 1 K 6) := tZeroSU hK
  let t : U := tZero hK
  let H' : Subgroup (MulAut U) := H
  let Inn : Subgroup (MulAut U) := (MulAut.conj : U →* MulAut U).range
  let ct : MulAut U := MulAut.conj t
  let G : Subgroup (MulAut U) := H' ⊓ Subgroup.centralizer ({ct} : Set (MulAut U))
  let O : Subgroup (MulAut U) := pCoreOf 2 G
  let Q0 : Subgroup U := pCoreOf 2 (Subgroup.centralizer ({t} : Set U))
  let h01 : (0 : Fin 6) ≠ 1 := by decide
  let R : Subgroup ↥(unitarySU 2 1 K 6) := tvRadical (fieldDataFour hK) h01
  let proj : ↥(unitarySU 2 1 K 6) →* U := LargeEvenProjMk _
  let x' : MulAut U := x
  set k : ↥(unitarySU 2 1 K 6) :=
    ((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
      ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
      ↥(unitarySU 2 1 K 6)) with hkdef
  have hxO' : x' ∈ O := by
    change x' ∈ pCoreOf 2 (H' ⊓ Subgroup.centralizer ({MulAut.conj t} : Set (MulAut U)))
    exact hxO
  have hxG' : x' ∈ G := (CFSG.LieType.BorelTits.pCoreOf_le 2 G) hxO'
  have hQ0eq : Q0 = R.map proj := by
    dsimp [Q0, R, h01, t, U, proj]
    exact pCoreOf_centralizer_tZero_eq hK
  have hcomap : (O ⊓ Inn).comap (MulAut.conj : U →* MulAut U) ≤ Q0 := by
    have h := comap_Oinn_le_pCore (K := K) hK hH
    dsimp [O, Inn, G, H', ct, t, U] at h ⊢
    exact h
  have hkblock : k ∈ unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) := by
    rw [hkdef]
    exact (unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X).2
  have hk_cent : (k : ↥(unitarySU 2 1 K 6)) ∈
      Subgroup.centralizer ({tvTransSU (fieldDataFour hK) h01} : Set ↥(unitarySU 2 1 K 6)) := by
    exact unitaryBlock_le_centralizer_tvTransSU (fieldDataFour hK) h01 hkblock
  have hkMcomm : ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    obtain ⟨μ, h1, h2⟩ := (mem_centralizer_tvTransSU_iff (fieldDataFour hK) h01).mp hk_cent
    exact (commute_tvNil_iff (i := 0) (j := 1) h01
      (M := ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))).mpr ⟨μ, h1, h2⟩
  have hkSU : (k : ↥(unitarySU 2 1 K 6)) * t0 = t0 * k := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Units.val_mul]
    have hkM : ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((t0 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((t0 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      change ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((tZeroSU hK : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((tZeroSU hK : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
      rw [tZeroSU_eq_tv hK, coe_tvTransSU]
      rw [mul_add, mul_one, hkMcomm, add_mul, one_mul]
    exact hkM
  have hkt : (k : U) * t = t * (k : U) := by
    change ((k * t0 : ↥(unitarySU 2 1 K 6)) : U) = ((t0 * k : ↥(unitarySU 2 1 K 6)) : U)
    exact congrArg (fun s : ↥(unitarySU 2 1 K 6) => (s : U)) hkSU
  have hkct : MulAut.conj (k : U) * ct = ct * MulAut.conj (k : U) := by
    dsimp [ct]
    rw [← map_mul, ← map_mul]
    exact congrArg MulAut.conj hkt
  have hkG : MulAut.conj (k : U) ∈ G := by
    refine ⟨?_, ?_⟩
    · exact hH ⟨(k : U), rfl⟩
    · simpa [Subgroup.mem_centralizer_singleton_iff] using hkct
  have hInn_norm : Inn.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    change n ∈ (MulAut.conj : U →* MulAut U).range at hn
    change g * n * g⁻¹ ∈ (MulAut.conj : U →* MulAut U).range
    rw [MonoidHom.mem_range] at hn ⊢
    obtain ⟨y, rfl⟩ := hn
    refine ⟨g y, ?_⟩
    ext z
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
  have hkInn : MulAut.conj (k : U) ∈ Inn := ⟨(k : U), rfl⟩
  have hOnorm : G ≤ Subgroup.normalizer (O : Set (MulAut U)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have hcommO : x' * MulAut.conj (k : U) * x'⁻¹ * (MulAut.conj (k : U))⁻¹ ∈ O := by
    have hinner : MulAut.conj (k : U) * x'⁻¹ * (MulAut.conj (k : U))⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOnorm hkG) (x'⁻¹)).mp (inv_mem hxO')
    simpa [mul_assoc] using mul_mem hxO' hinner
  have hcommInn : x' * MulAut.conj (k : U) * x'⁻¹ * (MulAut.conj (k : U))⁻¹ ∈ Inn := by
    have hconj : x' * MulAut.conj (k : U) * x'⁻¹ ∈ Inn :=
      hInn_norm.conj_mem (MulAut.conj (k : U)) hkInn x'
    exact mul_mem hconj (inv_mem hkInn)
  have hcomm_mem : x' * MulAut.conj (k : U) * x'⁻¹ * (MulAut.conj (k : U))⁻¹ ∈ O ⊓ Inn :=
    ⟨hcommO, hcommInn⟩
  have hconj_y : MulAut.conj (x' (k : U) * (k : U)⁻¹) =
      x' * MulAut.conj (k : U) * x'⁻¹ * (MulAut.conj (k : U))⁻¹ := by
    ext u
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, mul_assoc]
  have hyQ0 : x' (k : U) * (k : U)⁻¹ ∈ Q0 := by
    apply hcomap
    rw [Subgroup.mem_comap]
    rw [hconj_y]
    exact hcomm_mem
  have hyQ0' : x' (k : U) * (k : U)⁻¹ ∈ R.map proj := by
    rwa [hQ0eq] at hyQ0
  rw [Subgroup.mem_map] at hyQ0'
  obtain ⟨r, hrR, hr_eq⟩ := hyQ0'
  have hxkeq : x' (k : U) = proj r * (k : U) := by
    calc x' (k : U) = (x' (k : U) * (k : U)⁻¹) * (k : U) := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = proj r * (k : U) := by rw [← hr_eq]
  let φk : ↥(unitarySU 2 1 K 6) :=
    ⟨glAut φ (k : GL (Fin 6) K), uFieldSU_mem (fieldDataFour hK) φ k⟩
  let M : ↥(unitarySU 2 1 K 6) :=
    ⟨(A : GL (Fin 6) K) * (glAut φ (k : GL (Fin 6) K)) * (A : GL (Fin 6) K)⁻¹,
      uConjSU_mem (fieldDataFour hK) A φk⟩
  have hxA' : x' = uConjAut (fieldDataFour hK) one_le_six A *
      uFieldAut (fieldDataFour hK) one_le_six φ := by
    dsimp [x']
    exact hxA
  have hxkeqM : x' (k : U) = proj M := by
    calc x' (k : U) = (uConjAut (fieldDataFour hK) one_le_six A *
          uFieldAut (fieldDataFour hK) one_le_six φ) (k : U) := by rw [hxA']
      _ = uConjAut (fieldDataFour hK) one_le_six A
            (uFieldAut (fieldDataFour hK) one_le_six φ (k : U)) := rfl
      _ = uConjAut (fieldDataFour hK) one_le_six A (proj φk) := by
            congr 1
      _ = proj M := by
            change uConjAut (fieldDataFour hK) one_le_six A (projH _ φk) = projH _ M
            rw [uConjAut_proj]
  have hquot : (M : U) = ((r * k : ↥(unitarySU 2 1 K 6)) : U) := by
    change proj M = proj (r * k)
    rw [← hxkeqM, hxkeq]
    change proj r * proj k = proj (r * k)
    rw [← map_mul]
  obtain ⟨c, hc⟩ := scalar_of_proj_eq (K := K) hK hquot
  let Mk : Matrix (Fin 6) (Fin 6) K := ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  let Mφ : Matrix (Fin 6) (Fin 6) K := Mk.map φ
  let Minv : Matrix (Fin 6) (Fin 6) K := (((A⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K)
  let MA : Matrix (Fin 6) (Fin 6) K := ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  have hAA : MA * Minv = 1 := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      (mul_inv_cancel (A : GL (Fin 6) K))
    simpa [MA, Minv, Matrix.GeneralLinearGroup.coe_mul] using this
  have hAinvA : Minv * MA = 1 := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      (inv_mul_cancel (A : GL (Fin 6) K))
    simpa [MA, Minv, Matrix.GeneralLinearGroup.coe_mul] using this
  have hAinvCommN : Minv * tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * Minv := by
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) K => Minv * X * Minv) hAcommN
    simpa [MA, Minv, Matrix.mul_assoc, hAA, hAinvA] using h.symm
  have hNmap : (tvNil (K := K) (n := 6) 0 1).map φ = tvNil (K := K) (n := 6) 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tvNil, tvVec, vecMulVec_apply]
  have hMφcomm : Mφ * tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * Mφ := by
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) K => X.map φ) hkMcomm
    simpa [Mφ, Mk, Matrix.map_mul, hNmap] using h
  have hA_Mφ_comm : (MA * Mφ) * tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * (MA * Mφ) := by
    calc (MA * Mφ) * tvNil 0 1 = MA * (Mφ * tvNil 0 1) := by noncomm_ring
      _ = MA * (tvNil 0 1 * Mφ) := by rw [hMφcomm]
      _ = (MA * tvNil 0 1) * Mφ := by noncomm_ring
      _ = (tvNil 0 1 * MA) * Mφ := by rw [hAcommN]
      _ = tvNil 0 1 * (MA * Mφ) := by noncomm_ring
  have hMblock : tvBlock (0 : Fin 6) 1 ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      tvBlock (0 : Fin 6) 1 MA * (tvBlock (0 : Fin 6) 1 Mk).map φ *
        tvBlock (0 : Fin 6) 1 Minv := by
    change tvBlock (0 : Fin 6) 1 (MA * Mφ * Minv) =
      tvBlock (0 : Fin 6) 1 MA * (tvBlock (0 : Fin 6) 1 Mk).map φ *
        tvBlock (0 : Fin 6) 1 Minv
    rw [tvBlock_mul_of_commute_tvNil (K := K) hK hA_Mφ_comm hAinvCommN]
    rw [tvBlock_mul_of_commute_tvNil (K := K) hK hAcommN hMφcomm]
    have hmap : tvBlock (0 : Fin 6) 1 Mφ = (tvBlock (0 : Fin 6) 1 Mk).map φ := by
      ext i j
      simp [Mφ, tvBlock_apply]
    rw [hmap]
  have hrcomm : ((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * ((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have hrC : r ∈ Subgroup.centralizer ({tvTransSU (fieldDataFour hK) h01} :
        Set ↥(unitarySU 2 1 K 6)) := tvRadical_le_centralizer (fieldDataFour hK) h01 hrR
    obtain ⟨μ, h1, h2⟩ := (mem_centralizer_tvTransSU_iff (fieldDataFour hK) h01).mp hrC
    exact (commute_tvNil_iff (i := 0) (j := 1) h01
      (M := ((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))).mpr ⟨μ, h1, h2⟩
  have hrblock : tvBlock (0 : Fin 6) 1 ((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have h := (mem_tvRadical (fieldDataFour hK) (hij := h01) (g := r)).mp hrR
    exact h.2.2
  have hRkblock : tvBlock (0 : Fin 6) 1
      (((r * k : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      tvBlock (0 : Fin 6) 1 ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
    rw [tvBlock_mul_of_commute_tvNil (K := K) hK hrcomm hkMcomm, hrblock, one_mul]
  have hcM : ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (c : K) • (((r * k : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) := by
    have h := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hc
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hblockM : tvBlock (0 : Fin 6) 1 ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (c : K) • tvBlock (0 : Fin 6) 1 ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [hcM]
    change tvBlock (0 : Fin 6) 1 ((c : K) • (((r * k : ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)) = _
    rw [show tvBlock (0 : Fin 6) 1 ((c : K) • (((r * k : ↥(unitarySU 2 1 K 6)) :
        GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
        (c : K) • tvBlock (0 : Fin 6) 1 (((r * k : ↥(unitarySU 2 1 K 6)) :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) by
      ext i j
      rfl]
    rw [hRkblock]
  have hkJdet : (tvBlock (0 : Fin 6) 1 Mk).det = 1 := by
    dsimp [Mk]
    simpa [hkdef] using det_tvBlock_unitaryBlockEquiv (K := K) hK X
  have hAJdet : (tvBlock (0 : Fin 6) 1 MA).det *
      (tvBlock (0 : Fin 6) 1 Minv).det = 1 := by
    have hmul : tvBlock (0 : Fin 6) 1 MA * tvBlock (0 : Fin 6) 1 Minv = 1 := by
      rw [← tvBlock_mul_of_commute_tvNil (K := K) hK hAcommN hAinvCommN, hAA,
        tvBlock_one]
    have := congrArg (fun N : Matrix (({0, 1}ᶜ : Finset (Fin 6))) (({0, 1}ᶜ : Finset (Fin 6))) K =>
      N.det) hmul
    simpa [Matrix.det_mul] using this
  have hLdet : (tvBlock (0 : Fin 6) 1 ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).det = 1 := by
    rw [hMblock]
    rw [Matrix.det_mul, Matrix.det_mul]
    have hmapdet : ((tvBlock (0 : Fin 6) 1 Mk).map φ).det = 1 := by
      change (φ.mapMatrix (tvBlock (0 : Fin 6) 1 Mk)).det = 1
      rw [← RingEquiv.map_det, hkJdet, map_one]
    rw [hmapdet, mul_one]
    simpa [mul_comm] using hAJdet
  have hc4 : (c : K) ^ 4 = 1 := by
    have hdet := congrArg
      (fun N : Matrix (({0, 1}ᶜ : Finset (Fin 6))) (({0, 1}ᶜ : Finset (Fin 6))) K =>
      N.det) hblockM
    rw [hLdet, Matrix.det_smul, hkJdet, mul_one] at hdet
    rw [show Fintype.card ↥({0, 1}ᶜ : Finset (Fin 6)) = 4 by decide] at hdet
    exact hdet.symm
  have hc0 : (c : K) ≠ 0 := by
    intro h0
    rw [h0] at hc4
    norm_num at hc4
  let u : Kˣ := Units.mk0 (c : K) hc0
  have hu4 : u ^ 4 = 1 := by
    apply Units.ext
    simpa [u] using hc4
  have hu1 : u = 1 := by
    have h3 := cube_unit_eq_one (K := K) hK u
    calc u = u ^ 3 * u := by rw [h3, one_mul]
      _ = u ^ 4 := (pow_succ u 3).symm
      _ = 1 := hu4
  have hc_one : (c : K) = 1 := by
    have := congrArg (fun v : Kˣ => (v : K)) hu1
    simpa [u] using this
  rw [← hMblock]
  simpa [hc_one] using hblockM

lemma B45 (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))}
    (hH : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H)
    {x : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hxO : x ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer
      ({MulAut.conj (tZero hK)} :
        Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))))))
    {A : ↥(uU (fieldDataFour hK) 6)} {φ : K ≃+* K} (hφ : φ ≠ 1)
    (hxA : x = uConjAut (fieldDataFour hK) one_le_six A *
      uFieldAut (fieldDataFour hK) one_le_six φ)
    (hxcent : x * MulAut.conj (tZero hK) = MulAut.conj (tZero hK) * x)
    (hAcommN : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      tvNil (K := K) (n := 6) 0 1 = tvNil (K := K) (n := 6) 0 1 *
        ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) : False := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI := charP_two_of_card_four hK
  obtain ⟨ω, hω⟩ := exists_root_omega (K := K) hK
  let d : Fin 4 → K := ![ω, ω, ω, 1]
  have hd : ∀ k, (fieldDataFour hK).norm (d k) = 1 := by
    intro k
    rw [UnitaryFieldData.norm, fieldDataFour_bar hK]
    fin_cases k <;> simp [d]
    · rw [show ω * ω ^ 2 = ω ^ 3 by ring, omega_cube hω]
    · rw [show ω * ω ^ 2 = ω ^ 3 by ring, omega_cube hω]
    · rw [show ω * ω ^ 2 = ω ^ 3 by ring, omega_cube hω]
  have hdet : ∏ k, d k = 1 := by
    simp [d, Fin.prod_univ_four]
    rw [show ω * ω * ω = ω ^ 3 by ring, omega_cube hω]
  let X4 : ↥(unitarySU 2 1 K 4) := diagSU (fieldDataFour hK) d hd hdet
  let X : ↥(unitarySU 2 1 K ({0, 1}ᶜ : Finset (Fin 6)).card) := X4
  have htraceX : (∑ i : Fin 4, d i) = ω ^ 2 := by
    simp [d, Fin.sum_univ_four]
    have hsq : ω ^ 2 = ω + 1 := by
      have h := omega_add_sq hK hω
      calc ω ^ 2 = 0 + ω ^ 2 := by rw [zero_add]
        _ = (ω + ω) + ω ^ 2 := by rw [CharTwo.add_self_eq_zero, zero_add]
        _ = ω + (ω + ω ^ 2) := by abel
        _ = ω + 1 := by rw [h]
    calc ω + ω + ω + 1 = (ω + ω) + (ω + 1) := by abel
      _ = ω + 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
      _ = ω ^ 2 := hsq.symm
  have hblock := block_eq (K := K) hK hH hxO hxA hxcent hAcommN X
  let k : ↥(unitarySU 2 1 K 6) :=
    ((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
      ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
      ↥(unitarySU 2 1 K 6))
  let MA : Matrix (Fin 6) (Fin 6) K := ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  let Minv : Matrix (Fin 6) (Fin 6) K := (((A⁻¹ : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K)
  let Mk : Matrix (Fin 6) (Fin 6) K := ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  have hblock' : tvBlock (0 : Fin 6) 1 MA * (tvBlock (0 : Fin 6) 1 Mk).map φ *
      tvBlock (0 : Fin 6) 1 Minv = tvBlock (0 : Fin 6) 1 Mk := by
    simpa [MA, Minv, Mk, k] using hblock
  have hAA : MA * Minv = 1 := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      (mul_inv_cancel (A : GL (Fin 6) K))
    simpa [MA, Minv, Matrix.GeneralLinearGroup.coe_mul] using this
  have hAinvA : Minv * MA = 1 := by
    have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      (inv_mul_cancel (A : GL (Fin 6) K))
    simpa [MA, Minv, Matrix.GeneralLinearGroup.coe_mul] using this
  have hAcommN' : MA * tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * MA := by simpa [MA] using hAcommN
  have hAinvCommN : Minv * tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * Minv := by
    have h := congrArg (fun X : Matrix (Fin 6) (Fin 6) K => Minv * X * Minv) hAcommN'
    simpa [MA, Minv, Matrix.mul_assoc, hAA, hAinvA] using h.symm
  have hkMcomm : Mk * tvNil (K := K) (n := 6) 0 1 =
      tvNil (K := K) (n := 6) 0 1 * Mk := by
    dsimp [Mk]
    have hkblock : k ∈ unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) := by
      dsimp [k]
      exact (unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X).2
    have hk_cent : k ∈ Subgroup.centralizer
      ({tvTransSU (fieldDataFour hK) (by decide : (0:Fin 6) ≠ 1)} :
        Set ↥(unitarySU 2 1 K 6)) :=
      unitaryBlock_le_centralizer_tvTransSU (fieldDataFour hK) (by decide) hkblock
    obtain ⟨μ, h1, h2⟩ := (mem_centralizer_tvTransSU_iff (fieldDataFour hK) (by decide)).mp hk_cent
    exact (commute_tvNil_iff (i := 0) (j := 1) (by decide)
      (M := ((k : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))).mpr ⟨μ, h1, h2⟩
  have hAJmul : tvBlock (0 : Fin 6) 1 MA * tvBlock (0 : Fin 6) 1 Minv = 1 := by
    rw [← tvBlock_mul_of_commute_tvNil (K := K) hK hAcommN' hAinvCommN, hAA, tvBlock_one]
  have hAJunit : IsUnit (tvBlock (0 : Fin 6) 1 MA) := by
    have hdetu : IsUnit (tvBlock (0 : Fin 6) 1 MA).det := Matrix.isUnit_det_of_right_inverse hAJmul
    rw [Matrix.isUnit_iff_isUnit_det]
    exact hdetu
  have hAJinv : (tvBlock (0 : Fin 6) 1 MA)⁻¹ = tvBlock (0 : Fin 6) 1 Minv :=
    Matrix.inv_eq_right_inv hAJmul
  have htrace := congrArg
    (fun N : Matrix (({0, 1}ᶜ : Finset (Fin 6))) (({0, 1}ᶜ : Finset (Fin 6))) K =>
    N.trace) hblock'
  have htrace' : (tvBlock (0 : Fin 6) 1 Mk).trace =
      ((tvBlock (0 : Fin 6) 1 Mk).map φ).trace := by
    rw [← hAJinv] at htrace
    rw [Matrix.trace_conj hAJunit] at htrace
    exact htrace.symm
  have hmap_trace : ((tvBlock (0 : Fin 6) 1 Mk).map φ).trace =
      φ ((tvBlock (0 : Fin 6) 1 Mk).trace) := by
    simp [Matrix.trace, Matrix.map_apply, map_sum]
  have htrace_k : (tvBlock (0 : Fin 6) 1 Mk).trace = ω ^ 2 := by
    dsimp [Mk]
    change (tvBlock (0 : Fin 6) 1
      ((((unitaryBlockEquiv (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)) X :
        ↥(unitaryBlock (fieldDataFour hK) ({0, 1}ᶜ : Finset (Fin 6)))) :
        ↥(unitarySU 2 1 K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).trace = ω ^ 2
    rw [trace_tvBlock_unitaryBlockEquiv (K := K) hK X]
    change (Matrix.diagonal d).trace = ω ^ 2
    rw [Matrix.trace_diagonal]
    exact htraceX
  have hφω : φ ω = ω ^ 2 := by
    rcases ringEquiv_fixes_one_or_swaps (K := K) (ω := ω) hK hω (φ := φ) with h | h
    · exfalso
      exact hφ (ringEquiv_fixes_all (K := K) (ω := ω) hK hω h)
    · exact h
  have hφsq : φ (ω ^ 2) = ω := by
    rw [map_pow, hφω]
    rw [show (ω ^ 2) ^ 2 = ω ^ 4 by ring]
    rw [show ω ^ 4 = ω ^ 3 * ω by ring, omega_cube hω, one_mul]
  have hcontra : ω ^ 2 = ω := by
    calc ω ^ 2 = (tvBlock (0 : Fin 6) 1 Mk).trace := htrace_k.symm
      _ = ((tvBlock (0 : Fin 6) 1 Mk).map φ).trace := htrace'
      _ = φ ((tvBlock (0 : Fin 6) 1 Mk).trace) := hmap_trace
      _ = φ (ω ^ 2) := by rw [htrace_k]
      _ = ω := hφsq
  exact omega_sq_ne_omega (K := K) (ω := ω) hK hω hcontra

theorem card_pCoreOf_inf_centralizer_le (hK : Nat.card K = 4)
    {H : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))}
    (hH : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range ≤ H)
    (h2 : ((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))).range.subgroupOf H).index ≤ 2) :
    Nat.card (pCoreOf 2 (H ⊓ Subgroup.centralizer {MulAut.conj (tZero hK)})) ≤ 2 ^ 9 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let U := StatedProj (StatedSU 6 (2 ^ 1) K)
  let H' : Subgroup (MulAut U) := H
  let t : U := tZero hK
  let Inn : Subgroup (MulAut U) := (MulAut.conj : U →* MulAut U).range
  let ct : MulAut U := MulAut.conj t
  let G : Subgroup (MulAut U) := H' ⊓ Subgroup.centralizer ({ct} : Set (MulAut U))
  let O : Subgroup (MulAut U) := pCoreOf 2 G
  have hH' : Inn ≤ H' := hH
  have h2' : (Inn.subgroupOf H').index ≤ 2 := h2
  change Nat.card ↥(pCoreOf 2 (H' ⊓
    Subgroup.centralizer ({MulAut.conj t} : Set (MulAut U)))) ≤ 2 ^ 9
  have hcardOinn : Nat.card ↥(O ⊓ Inn) ≤ 2 ^ 9 := by
    have h := card_Oinn_le (K := K) hK hH h2
    dsimp [O, Inn, G, ct, H', t, U] at h ⊢
    exact h
  have hO_le_Inn : O ≤ Inn := by
    by_contra hnot
    rw [SetLike.le_def] at hnot
    push Not at hnot
    obtain ⟨x, hxO, hxInn⟩ := hnot
    have hxG : x ∈ G := (CFSG.LieType.BorelTits.pCoreOf_le 2 G) hxO
    have hxcent : x * MulAut.conj t = MulAut.conj t * x := by
      have := hxG.2
      simpa [ct, Subgroup.mem_centralizer_singleton_iff] using this
    have hHpos : ((Inn.subgroupOf H').index) ≠ 0 := by
      haveI : Finite (MulAut U) := inferInstance
      haveI : (Inn.subgroupOf H').FiniteIndex := Subgroup.finiteIndex_of_finite
      exact Subgroup.FiniteIndex.index_ne_zero
    have hHneq1 : ((Inn.subgroupOf H').index) ≠ 1 := by
      intro h1
      have htop : Inn.subgroupOf H' = ⊤ := Subgroup.index_eq_one.mp h1
      have hxH : x ∈ H' := hxG.1
      have hxmem : (⟨x, hxH⟩ : H') ∈ Inn.subgroupOf H' := by
        rw [htop]; exact Subgroup.mem_top (⟨x, hxH⟩ : H')
      exact hxInn (by simpa [Subgroup.mem_subgroupOf] using hxmem)
    have hHidx2 : ((Inn.subgroupOf H').index) = 2 := by omega
    obtain ⟨A, φ, hφ, hxA⟩ := B1_decomp (K := K) hK hH' h2' hxG hxInn
    have hAcommN : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        tvNil (K := K) (n := 6) 0 1 = tvNil (K := K) (n := 6) 0 1 *
          ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      exact AN_comm (K := K) hK A φ x t rfl hxA hxcent
    exact B45 (K := K) hK hH' hxO hφ hxA hxcent hAcommN
  have hO_eq : O = O ⊓ Inn :=
    le_antisymm (le_inf le_rfl hO_le_Inn) inf_le_left
  calc Nat.card ↥(pCoreOf 2 (H' ⊓ Subgroup.centralizer ({MulAut.conj t} : Set (MulAut U))))
      = Nat.card ↥O := rfl
    _ = Nat.card ↥(O ⊓ Inn) := by conv_lhs => rw [hO_eq]
    _ ≤ 2 ^ 9 := hcardOinn

end CFSG.StandardType.USixTwo

end
