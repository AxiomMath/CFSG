module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Interface
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Sp64
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesL44
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCenter

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Assembly.RankThreeEven (projSL projSp)
open Matrix

@[expose] def InvE9 (S : Type) [Group S] : Prop :=
  ∃ F F' : Subgroup S, F ≤ F' ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
    Late.IsE27 F' ∧ ∃ t : S, t ≠ 1 ∧ t ^ 2 = 1 ∧ ∀ f ∈ F, t * f = f * t

theorem InvE9.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : InvE9 Y) :
    InvE9 X := by
  obtain ⟨F, F', hFF', hF, hF9, hF', t, ht1, ht2, htF⟩ := h
  refine ⟨F.map e.symm.toMonoidHom, F'.map e.symm.toMonoidHom, Subgroup.map_mono hFF',
    isElemAbelian_map _ hF, by rw [Subgroup.card_map_of_injective e.symm.injective, hF9],
    ⟨isElemAbelian_map _ hF'.1, by rw [Subgroup.card_map_of_injective e.symm.injective, hF'.2]⟩,
    e.symm t, by rw [Ne, map_eq_one_iff _ e.symm.injective]; exact ht1,
    by rw [← map_pow, ht2, map_one], ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  change e.symm t * e.symm f = e.symm f * e.symm t
  rw [← map_mul, ← map_mul, htF f hf]


section L44

open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4 M units_pow_three card_units_F4 two_eq_zero)

theorem invE9_M : InvE9 M := by
  have hFe : CFSG.Assembly.IsElemAbelian 3 KFacts.KS21.L44.diagHom.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      apply Subtype.ext
      change KFacts.KS21.L44.diagHom x * KFacts.KS21.L44.diagHom y = KFacts.KS21.L44.diagHom y * KFacts.KS21.L44.diagHom x
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow, show x ^ 3 = 1 from Prod.ext (units_pow_three _) (units_pow_three _),
        map_one]
  have hF9 : Nat.card KFacts.KS21.L44.diagHom.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective KFacts.KS21.L44.diagHom_injective).toEquiv, Nat.card_prod,
      card_units_F4]
  set u : M := Sec21.TablesL44.δ (Multiplicative.ofAdd ![1, 1, 1]) with hu
  have hu3 : u ^ 3 = 1 := Sec21.TablesL44.δ_pow_three _
  have hcu : ∀ a ∈ KFacts.KS21.L44.diagHom.range, a * u = u * a := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, KFacts.KS21.L44.coe_diagHom, hu,
      Sec21.TablesL44.coe_δ, Sec21.TablesL44.dg, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have huF : u ∉ KFacts.KS21.L44.diagHom.range := by
    rintro ⟨x, hx⟩
    have h := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) hx
    simp only [KFacts.KS21.L44.coe_diagHom, hu, Sec21.TablesL44.coe_δ, Sec21.TablesL44.dg] at h
    have h0 := congrFun₂ h 0 0
    have h3 := congrFun₂ h 3 3
    simp only [diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_three] at h0 h3
    have h03 : Sec21.TablesL44.eω (Sec21.TablesL44.ext ![1, 1, 1] 0) =
        Sec21.TablesL44.eω (Sec21.TablesL44.ext ![1, 1, 1] 3) := by
      rw [← h0, ← h3]
      rfl
    have := Sec21.TablesL44.eω_injective h03
    revert this
    decide
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hF'e, hF'c⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers (p := 3)
    hFe huF hu3 hcu
  let t : M := ⟨transvection (0 : Fin 4) 3 (1 : F4),
    det_transvection_of_ne (0 : Fin 4) 3 (by decide) (1 : F4)⟩
  refine ⟨KFacts.KS21.L44.diagHom.range, KFacts.KS21.L44.diagHom.range ⊔ Subgroup.zpowers u, le_sup_left, hFe, hF9,
    ⟨hF'e, by rw [hF'c, hF9]⟩, t, ?_, ?_, ?_⟩
  · intro h
    have := congrFun₂ (congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) h) 0 3
    simp [t, transvection] at this
  · apply Subtype.ext
    change transvection (0 : Fin 4) 3 (1 : F4) ^ 2 = 1
    rw [sq, transvection_mul_transvection_same (0 : Fin 4) 3 (by decide),
      one_add_one_eq_two, two_eq_zero, transvection_zero]
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, KFacts.KS21.L44.coe_diagHom]
    change transvection (0 : Fin 4) 3 (1 : F4) * _ = _ * transvection (0 : Fin 4) 3 (1 : F4)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transvection, Matrix.mul_apply, single_apply, diagonal_apply, Fin.sum_univ_four,
        add_mul, mul_add]

end L44

section Sp64

open CFSG.RankThree.PartTwo.KFacts.KS21.Sp64 (F4 Sp e9Hom e9Hom_injective vecHom isSupp_e9Hom
  zElt mat_zElt isSupp_zMat_zero orderOf_zElt mem_centralizer_of_isSupp disjoint_four_two
  card_F4_units units_pow_three)

theorem invE9_Sp : InvE9 Sp := by
  let τT : (Fin 3 → F4ˣ) →* Sp :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom (r := 3) (k := F4)
  have hτT : Function.Injective τT :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom_injective
  have hFe : CFSG.Assembly.IsElemAbelian 3 e9Hom.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      apply Subtype.ext
      change e9Hom x * e9Hom y = e9Hom y * e9Hom x
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow, show x ^ 3 = 1 from Prod.ext (units_pow_three _) (units_pow_three _),
        map_one]
  have hF'e : CFSG.Assembly.IsElemAbelian 3 τT.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      apply Subtype.ext
      change τT x * τT y = τT y * τT x
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow, show x ^ 3 = 1 from funext fun i => units_pow_three (x i), map_one]
  refine ⟨e9Hom.range, τT.range, ?_, hFe, ?_, ⟨hF'e, ?_⟩, zElt 1 0, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨vecHom x, rfl⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective e9Hom_injective).toEquiv, Nat.card_prod,
      card_F4_units]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hτT).toEquiv, Nat.card_fun, card_F4_units,
      Nat.card_fin]
    norm_num
  · intro h
    have := orderOf_zElt (a := (1 : F4)) (b := 0) (Or.inl one_ne_zero)
    rw [h, orderOf_one] at this
    norm_num at this
  · have h2 := orderOf_zElt (a := (1 : F4)) (b := 0) (Or.inl one_ne_zero)
    have h := pow_orderOf_eq_one (zElt (1 : F4) 0)
    rwa [h2] at h
  · rintro _ ⟨x, rfl⟩
    have h := mem_centralizer_of_isSupp (isSupp_e9Hom x)
      (by rw [mat_zElt]; exact isSupp_zMat_zero 1) disjoint_four_two
    exact (Subgroup.mem_centralizer_singleton_iff.mp h).symm

end Sp64


end CFSG.RankThree.PartTwo.Sec4.Ronan148L
