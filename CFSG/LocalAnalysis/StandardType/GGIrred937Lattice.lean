module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LieType.Chevalley.LangRootArithmeticDet

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem torusAct_simple' (τ : Tag) {p : ℕ} [NeZero p] (i : Fin τ.rank)
    (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p (simple τ i) x =
      x - (∑ j, ((τ.cartan i j : ℤ) : ZMod p) * x j) • Pi.single i 1 := by
  funext k
  simp only [TableBExc.torusAct, simple_smul, reflect, TableBExc.redMod, TableBExc.liftMod,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [ZMod.natCast_zmod_val, ZMod.cast_id', id_eq]
  congr 2
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_apply, h]

private theorem latticeIrred_of_refl {τ : Tag} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hconn : ∀ S : Finset (Fin τ.rank), S.Nonempty →
      (∀ i ∈ S, ∀ j, τ.cartan i j ≠ 0 → j ∈ S) → S = Finset.univ)
    (hent : ∀ i j, τ.cartan i j ≠ 0 → ((τ.cartan i j : ℤ) : ZMod p) ≠ 0)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (U : AddSubgroup (Fin τ.rank → ZMod p))
    (hU : ∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod p), x ∈ U →
      TableBExc.torusAct τ p (simple τ i) x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  have hfun : ∀ (i : Fin τ.rank) (v : Fin τ.rank → ZMod p),
      CFSG.RankThree.CentralCover.cartanFunctional τ p i v =
        ∑ j, ((τ.cartan i j : ℤ) : ZMod p) * v j := by
    intro i v
    rw [CFSG.RankThree.CentralCover.cartanFunctional_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hsymm i j]
  have hinv : ∀ (i : Fin τ.rank) (v : Fin τ.rank → ZMod p),
      Multiplicative.ofAdd v ∈ U.toSubgroup →
      Multiplicative.ofAdd (v - CFSG.RankThree.CentralCover.cartanFunctional τ p i v •
        Pi.single i 1) ∈ U.toSubgroup := by
    intro i v hv
    rw [Multiplicative.mem_toSubgroup] at hv ⊢
    have h2 : v - CFSG.RankThree.CentralCover.cartanFunctional τ p i v • Pi.single i 1 =
        TableBExc.torusAct τ p (simple τ i) v := by
      rw [hfun i v, torusAct_simple' τ i v]
    rw [h2]
    exact hU i v hv
  rcases NbrInnerRest.eq_bot_or_eq_top_of_refl τ hp hdet hconn hent U.toSubgroup hinv with
    hbot | htop
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : Multiplicative.ofAdd x ∈ U.toSubgroup := by
      rwa [Multiplicative.mem_toSubgroup]
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Multiplicative.ofAdd.injective (by simpa using hx')
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : Multiplicative.ofAdd x ∈ U.toSubgroup := by
      rw [htop]; exact Subgroup.mem_top _
    rwa [Multiplicative.mem_toSubgroup] at hx'

private def f4d : Fin Tag.F4.rank → ZMod 3 := fun i => if i = 0 ∨ i = 1 then 2 else 1

private theorem f4d_mul_self (i : Fin Tag.F4.rank) : f4d i * f4d i = 1 := by
  fin_cases i <;> decide

private def f4Twist : (Fin Tag.F4.rank → ZMod 3) ≃+ (Fin Tag.F4.rank → ZMod 3) where
  toFun v := fun i => f4d i * v i
  invFun v := fun i => f4d i * v i
  left_inv v := by
    funext i
    dsimp only
    rw [← mul_assoc, f4d_mul_self, one_mul]
  right_inv v := by
    funext i
    dsimp only
    rw [← mul_assoc, f4d_mul_self, one_mul]
  map_add' v w := by funext i; simp only [Pi.add_apply, mul_add]

private theorem f4Twist_apply (v : Fin Tag.F4.rank → ZMod 3) (i : Fin Tag.F4.rank) :
    f4Twist v i = f4d i * v i := rfl

private theorem f4d_cartan_comm (i j : Fin Tag.F4.rank) :
    ((Tag.F4.cartan i j : ℤ) : ZMod 3) * f4d i =
      ((Tag.F4.cartan j i : ℤ) : ZMod 3) * f4d j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem f4_coeff (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ZMod 3) :
    (∑ j, ((Tag.F4.cartan i j : ℤ) : ZMod 3) * v j) * f4d i =
      CFSG.RankThree.CentralCover.cartanFunctional Tag.F4 3 i (f4Twist v) := by
  rw [CFSG.RankThree.CentralCover.cartanFunctional_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [f4Twist_apply]
  calc ((Tag.F4.cartan i j : ℤ) : ZMod 3) * v j * f4d i
      = (((Tag.F4.cartan i j : ℤ) : ZMod 3) * f4d i) * v j := by ring
    _ = (((Tag.F4.cartan j i : ℤ) : ZMod 3) * f4d j) * v j := by rw [f4d_cartan_comm i j]
    _ = ((Tag.F4.cartan j i : ℤ) : ZMod 3) * (f4d j * v j) := by ring

private theorem f4Twist_smul_single (i : Fin Tag.F4.rank) (c : ZMod 3) :
    f4Twist (c • (Pi.single i 1 : Fin Tag.F4.rank → ZMod 3)) =
      (c * f4d i) • (Pi.single i 1 : Fin Tag.F4.rank → ZMod 3) := by
  funext k
  rw [f4Twist_apply]
  by_cases hk : k = i
  · subst hk
    simp only [Pi.smul_apply, Pi.single_eq_same, mul_one]
    ring
  · simp only [Pi.smul_apply, Pi.single_apply]
    simp [hk]

private theorem f4Twist_reflect (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ZMod 3) :
    f4Twist (v - (∑ j, ((Tag.F4.cartan i j : ℤ) : ZMod 3) * v j) • Pi.single i 1) =
      f4Twist v - CFSG.RankThree.CentralCover.cartanFunctional Tag.F4 3 i (f4Twist v) •
        Pi.single i 1 := by
  rw [map_sub, f4Twist_smul_single, f4_coeff]

theorem latticeIrred_E8 {p : ℕ} (hp : p = 3 ∨ p = 5) (U : AddSubgroup (Fin Tag.E8.rank → ZMod p))
    (hU : ∀ (i : Fin Tag.E8.rank) (x : Fin Tag.E8.rank → ZMod p), x ∈ U →
      TableBExc.torusAct Tag.E8 p (simple Tag.E8 i) x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  rcases hp with rfl | rfl
  · haveI : NeZero 3 := ⟨by norm_num⟩
    exact latticeIrred_of_refl (τ := Tag.E8) (p := 3) (by norm_num)
      (TableBExc.isUnit_det_cartan_of_eq (τ := Tag.E8) (by norm_num)
        CFSG.LieType.Chevalley.det_cartan_E8 (Nat.coprime_one_left 3))
      (fun S hS hcl => NbrInnerRest.cartanE_connected (by decide) S hS hcl)
      (fun i j h => NbrInnerRest.cartanE_entry_ne_zero (by norm_num) (by norm_num) i j h)
      (fun i j => by fin_cases i <;> fin_cases j <;> decide) U hU
  · haveI : NeZero 5 := ⟨by norm_num⟩
    exact latticeIrred_of_refl (τ := Tag.E8) (p := 5) (by norm_num)
      (TableBExc.isUnit_det_cartan_of_eq (τ := Tag.E8) (by norm_num)
        CFSG.LieType.Chevalley.det_cartan_E8 (Nat.coprime_one_left 5))
      (fun S hS hcl => NbrInnerRest.cartanE_connected (by decide) S hS hcl)
      (fun i j h => NbrInnerRest.cartanE_entry_ne_zero (by norm_num) (by norm_num) i j h)
      (fun i j => by fin_cases i <;> fin_cases j <;> decide) U hU

theorem latticeIrred_E7 {p : ℕ} (hp : p = 3 ∨ p = 5) (U : AddSubgroup (Fin Tag.E7.rank → ZMod p))
    (hU : ∀ (i : Fin Tag.E7.rank) (x : Fin Tag.E7.rank → ZMod p), x ∈ U →
      TableBExc.torusAct Tag.E7 p (simple Tag.E7 i) x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  rcases hp with rfl | rfl
  · haveI : NeZero 3 := ⟨by norm_num⟩
    exact latticeIrred_of_refl (τ := Tag.E7) (p := 3) (by norm_num)
      (TableBExc.isUnit_det_cartan_of_eq (τ := Tag.E7) (by norm_num)
        CFSG.LieType.Chevalley.det_cartan_E7 (by decide))
      (fun S hS hcl => NbrInnerRest.cartanE_connected (by decide) S hS hcl)
      (fun i j h => NbrInnerRest.cartanE_entry_ne_zero (by norm_num) (by norm_num) i j h)
      (fun i j => by fin_cases i <;> fin_cases j <;> decide) U hU
  · haveI : NeZero 5 := ⟨by norm_num⟩
    exact latticeIrred_of_refl (τ := Tag.E7) (p := 5) (by norm_num)
      (TableBExc.isUnit_det_cartan_of_eq (τ := Tag.E7) (by norm_num)
        CFSG.LieType.Chevalley.det_cartan_E7 (by decide))
      (fun S hS hcl => NbrInnerRest.cartanE_connected (by decide) S hS hcl)
      (fun i j h => NbrInnerRest.cartanE_entry_ne_zero (by norm_num) (by norm_num) i j h)
      (fun i j => by fin_cases i <;> fin_cases j <;> decide) U hU

theorem latticeIrred_F4 (U : AddSubgroup (Fin Tag.F4.rank → ZMod 3))
    (hU : ∀ (i : Fin Tag.F4.rank) (x : Fin Tag.F4.rank → ZMod 3), x ∈ U →
      TableBExc.torusAct Tag.F4 3 (simple Tag.F4 i) x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  haveI : NeZero 3 := ⟨by norm_num⟩
  set W : AddSubgroup (Fin Tag.F4.rank → ZMod 3) := U.map f4Twist.toAddMonoidHom with hW
  have hWstab : ∀ (i : Fin Tag.F4.rank) (y : Fin Tag.F4.rank → ZMod 3), y ∈ W →
      y - CFSG.RankThree.CentralCover.cartanFunctional Tag.F4 3 i y • Pi.single i 1 ∈ W := by
    intro i y hy
    rw [hW, AddSubgroup.mem_map] at hy ⊢
    obtain ⟨v, hv, rfl⟩ := hy
    refine ⟨v - (∑ j, ((Tag.F4.cartan i j : ℤ) : ZMod 3) * v j) • Pi.single i 1, ?_, ?_⟩
    · rw [show v - (∑ j, ((Tag.F4.cartan i j : ℤ) : ZMod 3) * v j) • Pi.single i 1 =
          TableBExc.torusAct Tag.F4 3 (simple Tag.F4 i) v from
        (torusAct_simple' Tag.F4 i v).symm]
      exact hU i v hv
    · simpa only [AddEquiv.coe_toAddMonoidHom] using f4Twist_reflect i v
  have hinv : ∀ (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ZMod 3),
      Multiplicative.ofAdd v ∈ W.toSubgroup →
      Multiplicative.ofAdd (v - CFSG.RankThree.CentralCover.cartanFunctional Tag.F4 3 i v •
        Pi.single i 1) ∈ W.toSubgroup := by
    intro i v hv
    rw [Multiplicative.mem_toSubgroup] at hv ⊢
    exact hWstab i v hv
  rcases eq_bot_or_eq_top_of_reflF4 (p := 3) Nat.prime_three (by norm_num) W.toSubgroup hinv with
    hbot | htop
  · left
    have hbot' : ∀ x ∈ W.toSubgroup, x = 1 := by
      rw [eq_bot_iff] at hbot
      exact hbot
    rw [eq_bot_iff]
    intro y hy
    have hyW : f4Twist y ∈ W := ⟨y, hy, rfl⟩
    have h1 : Multiplicative.ofAdd (f4Twist y) ∈ W.toSubgroup := by
      rw [Multiplicative.mem_toSubgroup, toAdd_ofAdd]
      exact hyW
    have h2 : f4Twist y = 0 := Multiplicative.ofAdd.injective (by simpa using hbot' _ h1)
    exact f4Twist.injective (by rw [h2, map_zero])
  · right
    rw [eq_top_iff]
    intro x _
    have hxW : f4Twist x ∈ W := by
      have hx' : Multiplicative.ofAdd (f4Twist x) ∈ W.toSubgroup := by
        rw [htop]; exact Subgroup.mem_top _
      rw [Multiplicative.mem_toSubgroup, toAdd_ofAdd] at hx'
      exact hx'
    rw [hW, AddSubgroup.mem_map] at hxW
    obtain ⟨u, hu, hux⟩ := hxW
    have hux' : u = x := f4Twist.injective (by simpa using hux)
    rwa [hux'] at hu

theorem ggWeylIrred_range_of_torusAct {τ : Tag} {p : ℕ} [NeZero p] {R : Type} [Group R]
    (ι : Multiplicative (Fin τ.rank → ZMod p) →* R) (hinj : Function.Injective ι)
    (m : Fin τ.rank → R)
    (hm : ∀ (i : Fin τ.rank) (s : Fin τ.rank → ZMod p),
      m i * ι (Multiplicative.ofAdd s) * (m i)⁻¹ =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p (simple τ i) s)))
    (hirr : ∀ U : AddSubgroup (Fin τ.rank → ZMod p),
      (∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod p), x ∈ U →
        TableBExc.torusAct τ p (simple τ i) x ∈ U) → U = ⊥ ∨ U = ⊤) :
    GGWeylIrred ι.range := by
  intro E' hE' hnorm
  have hm_norm : ∀ i : Fin τ.rank, m i ∈ Subgroup.normalizer (ι.range : Set R) := by
    intro i
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · rintro ⟨s, rfl⟩
      have h := hm i (Multiplicative.toAdd s)
      rw [ofAdd_toAdd s] at h
      exact ⟨_, h.symm⟩
    · rintro ⟨s, hs⟩
      refine ⟨Multiplicative.ofAdd
        (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s)), ?_⟩
      have h := hm i (Multiplicative.toAdd s)
      rw [ofAdd_toAdd s] at h
      have h2 : TableBExc.torusAct τ p (simple τ i)
            (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s)) =
          Multiplicative.toAdd s := by
        rw [← TableBExc.torusAct_mul, simple_mul_simple_self, TableBExc.torusAct_one]
      have h3 := hm i (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s))
      rw [h2, ofAdd_toAdd s] at h3
      have h4 : m i * ι (Multiplicative.ofAdd
            (TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd s))) * (m i)⁻¹ =
          m i * x * (m i)⁻¹ := by
        rw [h3, hs]
      exact mul_left_cancel (mul_right_cancel h4)
  let U : AddSubgroup (Fin τ.rank → ZMod p) := Subgroup.toAddSubgroup' (E'.comap ι)
  have hU : ∀ (i : Fin τ.rank) (x : Fin τ.rank → ZMod p), x ∈ U →
      TableBExc.torusAct τ p (simple τ i) x ∈ U := by
    intro i x hx
    change x ∈ Subgroup.toAddSubgroup' (E'.comap ι) at hx
    rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_comap] at hx
    change TableBExc.torusAct τ p (simple τ i) x ∈ Subgroup.toAddSubgroup' (E'.comap ι)
    rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_comap]
    rw [← hm i x]
    exact hnorm (m i) (hm_norm i) (ι (Multiplicative.ofAdd x)) hx
  rcases hirr U hU with hUbot | hUtop
  · left
    rw [eq_bot_iff]
    intro e he
    obtain ⟨s, hs⟩ := hE' he
    have hsE : s ∈ E'.comap ι := by
      rw [Subgroup.mem_comap, hs]; exact he
    have hsU : Multiplicative.toAdd s ∈ U := by
      change Multiplicative.toAdd s ∈ Subgroup.toAddSubgroup' (E'.comap ι)
      rw [Subgroup.mem_toAddSubgroup', ofAdd_toAdd]
      exact hsE
    rw [hUbot, AddSubgroup.mem_bot] at hsU
    have hs1 : s = 1 := by
      rw [← ofAdd_toAdd s, hsU, ofAdd_zero]
    rw [← hs, hs1, map_one]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hE' ?_
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hyU : Multiplicative.toAdd y ∈ U := by
      rw [hUtop]; exact AddSubgroup.mem_top _
    change Multiplicative.toAdd y ∈ Subgroup.toAddSubgroup' (E'.comap ι) at hyU
    rw [Subgroup.mem_toAddSubgroup', Subgroup.mem_comap] at hyU
    rw [ofAdd_toAdd, hy] at hyU
    exact hyU

end Irred937

end CFSG.StandardType

end
