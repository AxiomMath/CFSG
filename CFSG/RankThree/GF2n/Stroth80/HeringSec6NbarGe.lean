module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Index
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Dim
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaConsumers

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS6

theorem Vt_le_Wt (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hel := hc.Vt_isElemAbelian h35 hs.mem hs.notQ
  intro v hv
  refine ⟨hc.Vt_le_Q t hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact congrArg Subtype.val (hel.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem card_Vt_sq_le (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) :
    Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Vt M (LB M Q B) B Z t) ≤
      Nat.card Q * Nat.card Z := by
  calc Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Vt M (LB M Q B) B Z t)
      ≤ Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t) :=
        Nat.mul_le_mul_right _ (Subgroup.card_le_of_le (Vt_le_Wt h34 hc hs))
    _ = Nat.card Q * Nat.card Z := hc.card_Wt_mul_card_Vt t

theorem four_le_of_omegaPlus_two (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (h : OmegaPlusNat hc t 2) : 4 ≤ n := by
  obtain ⟨K, fK, finK, hK, hnat⟩ := h
  have hV := card_of_naturalRep hnat sec39_Z_le_Vt hK
  have hsq := card_Vt_sq_le h34 hc hs
  have hcardι : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.width
  rw [hV, hcardι, hw] at hsq
  have h1 : Nat.card Z ^ 10 ≤ Nat.card Z ^ (2 * n + 2) := by
    calc Nat.card Z ^ 10 = (Nat.card Z * Nat.card Z ^ 4) * (Nat.card Z * Nat.card Z ^ 4) := by
          ring
      _ ≤ Nat.card Z ^ (2 * n + 1) * Nat.card Z := hsq
      _ = Nat.card Z ^ (2 * n + 2) := by ring
  have := (Nat.pow_le_pow_iff_right (by have := two_le_card_Z hc; omega)).mp h1
  omega

theorem card_CN_ge_of_relIndex (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {k : ℕ} (hidx : (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ k)
    (hk : k + 2 ≤ n) : Nat.card Q * Nat.card Z ≤ Nat.card ↥(hc.CN t) := by
  have hLB := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.2.1
  have hmul := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
  rw [hidx, hLB] at hmul
  have hq := two_le_card_Z hc
  obtain ⟨d, hd⟩ : ∃ d, n - 1 = k + (d + 1) := ⟨n - 1 - k - 1, by omega⟩
  have hA : Nat.card ↥(hc.CN t ⊓ LB M Q B) = Nat.card Q * Nat.card Z ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < Nat.card Z) k)
    calc Nat.card Z ^ k * Nat.card ↥(hc.CN t ⊓ LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) :=
          hmul
      _ = Nat.card Z ^ k * (Nat.card Q * Nat.card Z ^ (d + 1)) := by rw [hd, pow_add]; ring
  calc Nat.card Q * Nat.card Z = Nat.card Q * Nat.card Z ^ 1 := by rw [pow_one]
    _ ≤ Nat.card Q * Nat.card Z ^ (d + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ = Nat.card ↥(hc.CN t ⊓ LB M Q B) := hA.symm
    _ ≤ Nat.card ↥(hc.CN t) := Subgroup.card_le_of_le inf_le_left

theorem card_CN_ge_of_hypPlane (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnatSO : SpNat hc t ∨ OmegaNat hc t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    Nat.card Q * Nat.card Z ≤ Nat.card ↥(hc.CN t) := by
  obtain ⟨-, hcard, -, hopp⟩ := h51 G M Q Z B hc n t hs hnatSO r hr hplane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t) rfl rfl rfl rfl rfl
  rw [← hcard]
  exact Subgroup.card_le_of_le (hopp.1.trans hopp.2.1)

theorem card_CN_ge_omegaPlus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ}
    (hm : 3 ≤ m) (h : OmegaPlusNat hc t m) : Nat.card Q * Nat.card Z ≤ Nat.card ↥(hc.CN t) := by
  obtain ⟨K, fK, finK, hK, hnat⟩ := h
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_orth h34 hRoot hs hnatSO hK
    (ElemMatrixIso.plus hm) (nondegenerate_polarBilin_quadPlus m K) h3
    (addCommutantScalar_statedOmegaPlus hm)
    (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm)
      (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm)) hnat
  exact card_CN_ge_of_hypPlane h51 hc hs hnatSO hr hplane

theorem card_CN_ge_omegaMinus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ}
    (hm : 2 ≤ m) (h : OmegaMinusNat hc t m) : Nat.card Q * Nat.card Z ≤ Nat.card ↥(hc.CN t) := by
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := h
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]; omega
  obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_orth h34 hRoot hs hnatSO hK
    (ElemMatrixIso.minus hm hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
    (addCommutantScalar_statedOmegaMinus hm hirr)
    (hc.natSingular_of h34 hRoot hs hnatSO hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr)) hnat
  exact card_CN_ge_of_hypPlane h51 hc hs hnatSO hr hplane

theorem card_CN_ge_SL (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 2 ≤ m) (h : SLMNat hc t m) :
    Nat.card Q * Nat.card Z ≤ Nat.card ↥(hc.CN t) := by
  have hdim := stroth6SLDim_of_34 h34 G M Q Z B hc n t hs m hm (Or.inl h)
  obtain ⟨K, fK, finK, hK, hnat⟩ := h
  exact card_CN_ge_of_relIndex h34 hc hs (relIndex_SL h34 hc hs hK hm hnat) (by omega)

end HS6

theorem stroth6NbarGe_of_inputs (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement) : Stroth6NbarGeStatement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ
  have s5 : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  have hq := HS6.two_le_card_Z hc
  by_cases hRL : Rt M (LB M Q B) t = LB M Q B
  · have hCN := hc.CN_eq_LB_of_Rt_eq ht hRL
    have hLB := (stroth_3_5 h34 hc hw hn hno hgen).2.2.1
    rw [hCN, hLB]
    refine Nat.mul_le_mul_left _ ?_
    calc Nat.card Z = Nat.card Z ^ 1 := (pow_one _).symm
      _ ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  · rcases h310 G M Q Z B hc n hw hn hno hgen t ht htQ with hRL' | ⟨K, fK, finK, hK, hcase⟩
    · exact absurd hRL' hRL
    · rcases hcase with ⟨m, hm, hrep⟩ | ⟨m, hm, hrep⟩ | ⟨m, hm, hrep⟩ | ⟨m, b, c, hm, hbc, hrep⟩
      · exact HS6.card_CN_ge_SL h34 hc s5 hm ⟨K, fK, finK, hK, hrep⟩
      · by_cases hm1 : m = 1
        · subst hm1
          exact HS6.card_CN_ge_SL h34 hc s5 le_rfl
            ⟨K, fK, finK, hK, NaturalRep.sp_one_to_sl_two hrep⟩
        · have hSp : SpNat hc t := ⟨K, fK, finK, hK, m, by omega, hrep⟩
          obtain ⟨r, hr, hplane, -⟩ := hc.exists_hypPlane_sp h34 hRoot s5 hSp
          exact HS6.card_CN_ge_of_hypPlane h51 hc s5 (Or.inl hSp) hr hplane
      · by_cases hm2 : m = 2
        · subst hm2
          have hP : OmegaPlusNat hc t 2 := ⟨K, fK, finK, hK, hrep⟩
          exact HS6.card_CN_ge_of_relIndex h34 hc s5
            (HS6.relIndex_omegaPlus_four_of_ne h34 hc s5 hRL hP)
            (HS6.four_le_of_omegaPlus_two h34 hc s5 hP)
        · exact HS6.card_CN_ge_omegaPlus h34 hRoot h51 hc s5 (by omega) ⟨K, fK, finK, hK, hrep⟩
      · exact HS6.card_CN_ge_omegaMinus h34 hRoot h51 hc s5 hm ⟨K, fK, finK, hK, b, c, hbc, hrep⟩

end CFSG.RankThree.GF2n.Stroth80
