module

public import CFSG.RankThree.PartOne.KF.F128Cls
public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusUpper
public import CFSG.GroupTheory.WeirSylow.Orthogonal
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply coe_quadMinus)

theorem natCast_pow_eq_one_iff {p q k : ℕ} (hq : 1 ≤ q) :
    (q : ZMod p) ^ k = 1 ↔ p ∣ q ^ k - 1 := by
  have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, sub_eq_zero, Nat.cast_one]

theorem int_dvd_pow_add_neg_one_iff {p q k : ℕ} :
    (p : ℤ) ∣ (q : ℤ) ^ k + (-1) ↔ (q : ZMod p) ^ k = 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [← sub_eq_add_neg, sub_eq_zero]

theorem pRank_statedProj_statedOmegaMinus_four_le_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h1 : ¬ p ∣ Nat.card K - 1) (h2 : ¬ p ∣ Nat.card K + 1) :
    CFSG.pRank p (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK : ¬ p ∣ Nat.card K := by
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    rw [← hcard, hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  let Q : QuadraticForm K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := quadMinus 4 K b c
  have hdim : Module.finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) = 2 * 4 :=
    finrank_quadMinus_space (by norm_num)
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr
  have hmin : IsMinusType Q := by
    refine ⟨?_, not_isPlusType_quadMinus (by norm_num) hirr⟩
    let ι : (Fin (4 - 1) → K) →ₗ[K] (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :=
      { toFun := fun x => Sum.elim x (fun _ => 0)
        map_add' := fun x y => by
          funext j
          rcases j with j | j <;> simp
        map_smul' := fun a x => by
          funext j
          rcases j with j | j <;> simp }
    have hι : Function.Injective ι := fun x y h => funext fun i => congrFun h (Sum.inl i)
    refine ⟨LinearMap.range ι, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hι, Module.finrank_fin_fun, hdim]
    · rintro _ ⟨x, rfl⟩
      show quadMinus 4 K b c (Sum.elim x (fun _ => 0)) = 0
      rw [quadMinus_apply]
      simp
  have hε : ((-1 : ℤ) = 1 ∧ IsPlusType Q) ∨ ((-1 : ℤ) = -1 ∧ IsMinusType Q) := Or.inr ⟨rfl, hmin⟩
  have hp1 : Odd p := hp.odd_of_ne_two hp2
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [hcard]
  have : Finite (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := inferInstance
  have : Finite ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)) :=
    Finite.of_injective (fun f => (f : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) →
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K))) DFunLike.coe_injective
  set x : ZMod p := (Nat.card K : ZMod p) with hx
  have hx0 : x ≠ 0 := fun h => hpK ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hx1 : x ≠ 1 := fun h => h1 (by
    simpa using (natCast_pow_eq_one_iff (p := p) hq1 (k := 1)).1 (by rw [pow_one]; exact h))
  have hxm1 : x ≠ -1 := fun h => h2 (by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [← hx, h]; exact neg_add_cancel _)
  have hx2 : x ^ 2 ≠ 1 := fun h => by
    have h3 : (x - 1) * (x + 1) = 0 := by ring_nf; rw [h]; ring
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hx1 (sub_eq_zero.1 h4)
    · exact hxm1 (eq_neg_of_add_eq_zero_left h4)
  have he0 : 0 < orderOf x :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, Nat.sub_pos_of_lt hp.one_lt, ZMod.pow_card_sub_one_eq_one hx0⟩)
  have he1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.1 h)
  have he2 : orderOf x ≠ 2 := fun h => hx2 (by rw [← h]; exact pow_orderOf_eq_one _)
  have hcyc : ∀ P : Sylow p (TauCeti.QuadraticMap.orthogonalGroup Q), IsCyclic P := by
    intro P
    obtain ⟨c1, c2, c3⟩ := sylow_orthogonal_even hp1 hpK' (n := 4) (by norm_num) hdim Q hQ hε P
    by_cases hA : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 4 + (-1)
    ·
      have hB : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 4 - (-1) := c3.resolve_left (not_not.2 hA)
      have hx4 : x ^ 4 = 1 := by
        have := int_dvd_pow_add_neg_one_iff.1 hA
        rwa [hcard] at this
      have he4 : orderOf x = 4 := by
        have hd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
        have : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hd
        interval_cases h : orderOf x <;> omega
      let P' : Sylow p (StatedSp (4 - 1) K) := Classical.arbitrary _
      obtain ⟨ψ⟩ := c2 hB P'
      refine (MulEquiv.isCyclic ψ).2 (sylow_cyclic_Sp hp hp2 hpK ?_ P')
      show (if Even (orderOf x) then 2 * (4 - 1) else 4 - 1) / orderOf x ≤ 1
      rw [he4]
      decide
    ·
      let P' : Sylow p (StatedSp 4 K) := Classical.arbitrary _
      obtain ⟨ψ⟩ := c1 hA P'
      have hx4 : x ^ 4 ≠ 1 := fun h => hA (int_dvd_pow_add_neg_one_iff.2 (by rwa [hcard]))
      have hnd : ¬ orderOf x ∣ 4 := fun h => hx4 (orderOf_dvd_iff_pow_eq_one.1 h)
      refine (MulEquiv.isCyclic ψ).2 (sylow_cyclic_Sp hp hp2 hpK ?_ P')
      show (if Even (orderOf x) then 2 * 4 else 4) / orderOf x ≤ 1
      split_ifs with hev
      · obtain ⟨k, hk⟩ := hev
        have h4 : orderOf x ≠ 4 := fun h => hnd (by rw [h])
        refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul he0).2 ?_)
        omega
      · refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul he0).2 ?_)
        omega
  set Ω : Subgroup (GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K) :=
    StatedOmega (StatedQuadMinus 4 K b c) with hΩ
  let φ : ↥Ω →* ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    MonoidHom.codRestrict
      ((CFSG.RankThree.PartOne.LIT.glAut (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).comp Ω.subtype)
      (TauCeti.QuadraticMap.orthogonalGroup Q) (fun A =>
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => by
          show quadMinus 4 K b c (CFSG.RankThree.PartOne.LIT.glAut _ K (A : GL _ K) v) =
            quadMinus 4 K b c v
          rw [coe_quadMinus, CFSG.RankThree.PartOne.LIT.glAut_apply]
          exact CFSG.LieType.Steinberg.preserves_of_mem_statedOmega A.2 v)
  have hφ : Function.Injective φ := fun A B h =>
    Subtype.ext (CFSG.RankThree.PartOne.LIT.glAut_injective (congrArg Subtype.val h))
  have hrk : CFSG.pRank p ↥Ω ≤ 1 := pRank_le_one_of_injective φ hφ hcyc
  have hbot := KFU.statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot (K := K) (b := b) (c := c)
  rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt (KFU.equivProjOfScalarsBot Ω hbot)]
  exact hrk

end CFSG.RankThree.PartOne
