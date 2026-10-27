module

public import CFSG.Quasithin.Vol2.Ch3E213MG41D2
public import CFSG.Quasithin.Vol2.E2StatementsAS
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.Quasithin.E2

namespace Sp4Z

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.Quasithin.Ch3E213M CFSG.Quasithin.Ch3E213M.G41

variable {K : Type} [Field K]

@[expose] def swapMat01 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def swapMat12 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

theorem swapMat01_mul_self : swapMat01 (K := K) * swapMat01 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat01, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapMat12_mul_self : swapMat12 (K := K) * swapMat12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat12, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapMat01_mem : (swapMat01 (K := K))ᵀ * minorJ K * swapMat01 = minorJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat01, minorJ_apply, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapMat12_mem : (swapMat12 (K := K))ᵀ * minorJ K * swapMat12 = minorJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat12, minorJ_apply, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def swapElt01 : antiSp K :=
  ⟨⟨swapMat01, swapMat01, swapMat01_mul_self, swapMat01_mul_self⟩, swapMat01_mem⟩

@[expose] def swapElt12 : antiSp K :=
  ⟨⟨swapMat12, swapMat12, swapMat12_mul_self, swapMat12_mul_self⟩, swapMat12_mem⟩

theorem natAct_swapElt01 (v : Fin 4 → K) :
    Ch3E213M.natAct (swapElt01 (K := K)) v = ![v 1, v 0, v 3, v 2] := by
  ext i
  fin_cases i <;> simp [Ch3E213M.natAct, swapElt01, swapMat01, glMat, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

theorem natAct_swapElt12 (v : Fin 4 → K) :
    Ch3E213M.natAct (swapElt12 (K := K)) v = ![v 0, v 2, v 1, v 3] := by
  ext i
  fin_cases i <;> simp [Ch3E213M.natAct, swapElt12, swapMat12, glMat, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four]

variable [CharP K 2]

theorem natAct_uElt (a b c d : K) (v : Fin 4 → K) :
    Ch3E213M.natAct (uElt a b c d) v = ![v 0 + a * v 1 + b * v 2 + c * v 3,
      v 1 + d * v 2 + (b + a * d) * v 3, v 2 + a * v 3, v 3] := by
  ext i
  fin_cases i <;>
    simp [Ch3E213M.natAct, glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem swapElt01_conj (b c : K) :
    swapElt01 * uElt 0 b c 0 * swapElt01⁻¹ = uElt 0 b 0 c := by
  apply antiSp_ext
  show swapMat01 * uMat 0 b c 0 * swapMat01 = uMat 0 b 0 c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat01, uMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapElt12_conj (b c : K) :
    swapElt12 * uElt 0 b c 0 * swapElt12⁻¹ = uElt b 0 c 0 := by
  apply antiSp_ext
  show swapMat12 * uMat 0 b c 0 * swapMat12 = uMat b 0 c 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat12, uMat, Matrix.mul_apply, Fin.sum_univ_four]

variable (K) in
@[expose] def zConjSet : Set (antiSp K) :=
  {x | ∀ z ∈ antiUnipotentCenter K, x * z * x⁻¹ ∈ antiUnipotent K}

theorem mem_zConjSet_of_mem {u : antiSp K} (hu : u ∈ antiUnipotent K) : u ∈ zConjSet K := by
  intro z hz
  obtain ⟨hzU, hzc⟩ := (mem_antiUnipotentCenter_iff_central z).1 hz
  rw [← hzc u hu, mul_inv_cancel_right]
  exact hzU

theorem swapElt01_mem_zConjSet : swapElt01 ∈ zConjSet K := by
  rintro _ ⟨b, c, rfl⟩
  rw [swapElt01_conj]
  exact uElt_mem_antiUnipotent _ _ _ _

theorem swapElt12_mem_zConjSet : swapElt12 ∈ zConjSet K := by
  rintro _ ⟨b, c, rfl⟩
  rw [swapElt12_conj]
  exact uElt_mem_antiUnipotent _ _ _ _

theorem exists_mem_closure_natAct_eq_of_ne_zero {v : Fin 4 → K} (hv : v 3 ≠ 0) :
    ∃ h ∈ Subgroup.closure (zConjSet K), ∃ l : K, Ch3E213M.natAct h v = Pi.single 0 l := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set a := v 2 / v 3
  set b := v 1 / v 3
  set c := (v 0 + a * v 1 + b * v 2) / v 3
  have hu := uElt_mem_antiUnipotent a b c 0
  have hw : swapElt01 * swapElt12 * swapElt01 ∈ Subgroup.closure (zConjSet K) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure swapElt01_mem_zConjSet)
      (Subgroup.subset_closure swapElt12_mem_zConjSet))
      (Subgroup.subset_closure swapElt01_mem_zConjSet)
  refine ⟨swapElt01 * swapElt12 * swapElt01 * uElt a b c 0,
    Subgroup.mul_mem _ hw (Subgroup.subset_closure (mem_zConjSet_of_mem hu)), v 3, ?_⟩
  have e2 : v 2 + a * v 3 = 0 := by
    rw [div_mul_cancel₀ _ hv]
    linear_combination v 2 * h2
  have e1 : v 1 + 0 * v 2 + (b + a * 0) * v 3 = 0 := by
    rw [zero_mul, add_zero, mul_zero, add_zero, div_mul_cancel₀ _ hv]
    linear_combination v 1 * h2
  have e0 : v 0 + a * v 1 + b * v 2 + c * v 3 = 0 := by
    rw [div_mul_cancel₀ _ hv]
    linear_combination (v 0 + a * v 1 + b * v 2) * h2
  rw [Ch3E213M.natAct_mul, Ch3E213M.natAct_mul, Ch3E213M.natAct_mul, natAct_uElt, e0, e1, e2,
    natAct_swapElt01, natAct_swapElt12, natAct_swapElt01]
  ext i
  fin_cases i <;> simp

theorem exists_mem_closure_natAct_eq (v : Fin 4 → K) :
    ∃ h ∈ Subgroup.closure (zConjSet K), ∃ l : K, Ch3E213M.natAct h v = Pi.single 0 l := by
  by_cases h3 : v 3 = 0
  · by_cases h2 : v 2 = 0
    · by_cases h1 : v 1 = 0
      · refine ⟨1, Subgroup.one_mem _, v 0, ?_⟩
        rw [Ch3E213M.natAct_one]
        ext i
        fin_cases i <;> simp [h1, h2, h3]
      ·
        obtain ⟨h, hh, l, hl⟩ := exists_mem_closure_natAct_eq_of_ne_zero
          (v := Ch3E213M.natAct (swapElt01 * swapElt12) v)
          (by rw [Ch3E213M.natAct_mul, natAct_swapElt12, natAct_swapElt01]; simpa using h1)
        refine ⟨h * (swapElt01 * swapElt12), Subgroup.mul_mem _ hh (Subgroup.mul_mem _
          (Subgroup.subset_closure swapElt01_mem_zConjSet)
          (Subgroup.subset_closure swapElt12_mem_zConjSet)), l, ?_⟩
        rw [Ch3E213M.natAct_mul, hl]
    ·
      obtain ⟨h, hh, l, hl⟩ :=
        exists_mem_closure_natAct_eq_of_ne_zero (v := Ch3E213M.natAct swapElt01 v)
          (by rw [natAct_swapElt01]; simpa using h2)
      refine ⟨h * swapElt01, Subgroup.mul_mem _ hh
        (Subgroup.subset_closure swapElt01_mem_zConjSet), l, ?_⟩
      rw [Ch3E213M.natAct_mul, hl]
  · exact exists_mem_closure_natAct_eq_of_ne_zero h3

theorem trv_single_eq (l c : K) : trv (Pi.single 0 l) c = uElt 0 0 (c * l * l) 0 := by
  apply ext_act
  intro x
  rw [act_trv, natAct_uElt]
  have hb : spBil x (Pi.single 0 l) = l * x 3 := by
    rw [show (Pi.single 0 l : Fin 4 → K) = l • Pi.single 0 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], LinearMap.map_smul, bil_single]
    rfl
  rw [hb]
  ext i
  fin_cases i <;> simp
  ring

theorem closure_zConjSet_eq_top : Subgroup.closure (zConjSet K) = ⊤ := by
  rw [eq_top_iff, ← closure_trv_eq_top K, Subgroup.closure_le]
  rintro _ ⟨v, c, rfl⟩
  obtain ⟨h, hh, l, hl⟩ := exists_mem_closure_natAct_eq v
  have e : trv v c = h⁻¹ * trv (Ch3E213M.natAct h v) c * h := by
    rw [← conj_trv]
    group
  rw [SetLike.mem_coe, e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) ?_) hh
  rw [hl, trv_single_eq]
  exact Subgroup.subset_closure (mem_zConjSet_of_mem (uElt_mem_antiUnipotent _ _ _ _))

theorem exists_mulEquiv_antiSp_of_isSp4C {X : Type} [Group X] {k : ℕ}
    (h : ASInputs.IsSp4C k X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nonempty (X ≃* antiSp F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with h | ⟨-, ⟨e⟩⟩
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have : CharP F 2 := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
    exact ⟨F, inferInstance, inferInstance, inferInstance, ⟨e.trans
      ((CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := F) (n := 2) (by norm_num)).trans
        (antiSpEquiv F).symm)⟩⟩
  · obtain ⟨ω⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
      (k := ZMod 2) (by rw [ZMod.card])
    exact ⟨ZMod 2, inferInstance, inferInstance, inferInstance,
      ⟨e.trans (ω.symm.trans (antiSpEquiv (ZMod 2)).symm)⟩⟩

theorem closure_conj_center_eq_top {X : Type} [Group X] [Finite X] {k : ℕ}
    (h : ASInputs.IsSp4C k X) {S : Subgroup X} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    Subgroup.closure
      {x : X | ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), x * z * x⁻¹ ∈ S} = ⊤ := by
  obtain ⟨F, _, _, _, ⟨θ₁⟩⟩ := exists_mulEquiv_antiSp_of_isSp4C h
  have hT1 := B6.isSylowTwoOf_map_top (φ := θ₁.toMonoidHom) θ₁.surjective hS
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj (card_and_isSylowTwoOf_antiUnipotent (K := F)).2
    hT1
  set θ := θ₁.trans (MulAut.conj c⁻¹) with hθ
  have hθapp : ∀ x, θ x = c⁻¹ * θ₁ x * c⁻¹⁻¹ := fun x => rfl
  have hθS : ∀ x, x ∈ S ↔ θ x ∈ antiUnipotent F := by
    intro x
    rw [hθapp, inv_inv, ← B6.mem_conjSub, ← hc]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', he⟩
      rwa [θ₁.injective he] at hx'
  have hθZ : ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), θ z ∈ antiUnipotentCenter F := by
    rintro z ⟨hzS, hzc⟩
    refine (mem_antiUnipotentCenter_iff_central _).2 ⟨(hθS z).1 hzS, fun u hu => ?_⟩
    obtain ⟨y, rfl⟩ := θ.surjective u
    have hyS := (hθS y).2 hu
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hzc y hyS).symm]
  have hsub : θ.symm.toMonoidHom '' zConjSet F ⊆
      {x : X | ∀ z ∈ S ⊓ Subgroup.centralizer (S : Set X), x * z * x⁻¹ ∈ S} := by
    rintro _ ⟨y, hy, rfl⟩ z hz
    rw [hθS, map_mul, map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hy (θ z) (hθZ z hz)
  have htop : Subgroup.closure (θ.symm.toMonoidHom '' zConjSet F) = ⊤ := by
    rw [← MonoidHom.map_closure, closure_zConjSet_eq_top]
    exact Subgroup.map_top_of_surjective _ fun y => ⟨θ y, by simp⟩
  exact eq_top_iff.mpr (htop.symm.le.trans (Subgroup.closure_mono hsub))

end Sp4Z

end CFSG.Quasithin.E2
