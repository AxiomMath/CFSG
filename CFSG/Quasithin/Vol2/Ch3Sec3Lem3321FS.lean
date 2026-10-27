module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FC

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open scoped commutatorElement IsMulCommutative

theorem tr_mem_one_rad {b : Fin 4} (hb : 1 ≤ (b : ℕ)) (h : (0 : Fin 4) ≠ b) :
    SpecialLinearGroup.transvection h (1 : ZMod 2) ∈ perfectCore (FLc.QI 4 {1}) :=
  L3318.transvection_mem_perfectCore_one le_rfl rfl hb h

theorem tr_mem_one_levi {a c : Fin 4} (ha : 1 ≤ (a : ℕ)) (hc : 1 ≤ (c : ℕ)) (h : a ≠ c) :
    SpecialLinearGroup.transvection h (1 : ZMod 2) ∈ perfectCore (FLc.QI 4 {1}) :=
  L3318.transvection_mem_perfectCore_levi_one le_rfl ha hc h

theorem tr_mem_three_levi {a c : Fin 4} (ha : (a : ℕ) < 3) (hc : (c : ℕ) < 3) (h : a ≠ c) :
    SpecialLinearGroup.transvection h (1 : ZMod 2) ∈ perfectCore (FLc.QI 4 {3}) := by
  have hno : ∀ c' ∈ ({3} : Set ℕ), ¬ (0 < c' ∧ c' < 0 + 3) := by
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    omega
  rw [L3318.transvection_eq_liftT (by norm_num) ha hc h]
  exact Ln2.liftT_mem_perfectCore (by norm_num) le_rfl hno _

theorem tr_mem_three_rad {a : Fin 4} (ha : (a : ℕ) < 3) (h : a ≠ 3) :
    SpecialLinearGroup.transvection h (1 : ZMod 2) ∈ perfectCore (FLc.QI 4 {3}) :=
  L3318.transvection_mem_perfectCore_three ha (by norm_num) h

theorem toAdd_actM_tr {a b : Fin 4} (h : a ≠ b) (x : Multiplicative (FLc.Vt 4)) :
    Multiplicative.toAdd (FLc.actM (SpecialLinearGroup.transvection h (1 : ZMod 2)) x) =
      (1 + single a b 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd x := by
  rw [FLc.toAdd_actM]
  show ((SpecialLinearGroup.transvection h (1 : ZMod 2) : SL4) :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ _ = _
  rw [SpecialLinearGroup.transvection_coe]

theorem toAdd_actDl_tr {a b : Fin 4} (h : a ≠ b) (x : Multiplicative (FLc.Vt 4)) :
    Multiplicative.toAdd (FLc.actDl (SpecialLinearGroup.transvection h (1 : ZMod 2)) x) =
      (1 + single b a 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd x := by
  rw [FLc.toAdd_actDl]
  show (((SpecialLinearGroup.transvection h (1 : ZMod 2))⁻¹ : SL4) :
    Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ _ = _
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
    show (-1 : ZMod 2) = 1 from rfl, transpose_add, transpose_one, transpose_single]

theorem closure_eq_top_of_single {S : Set (Multiplicative (FLc.Vt 4))}
    (h : ∀ k : Fin 4, Multiplicative.ofAdd (Pi.single k (1 : ZMod 2)) ∈ Subgroup.closure S) :
    Subgroup.closure S = ⊤ := by
  have key : ∀ x : FLc.Vt 4, Multiplicative.ofAdd x =
      (if x 0 = 1 then Multiplicative.ofAdd (Pi.single 0 1) else 1) *
        (if x 1 = 1 then Multiplicative.ofAdd (Pi.single 1 1) else 1) *
          (if x 2 = 1 then Multiplicative.ofAdd (Pi.single 2 1) else 1) *
            (if x 3 = 1 then Multiplicative.ofAdd (Pi.single 3 1) else 1) := by
    decide +kernel
  have hite : ∀ (p : Prop) [Decidable p] (k : Fin 4),
      (if p then Multiplicative.ofAdd (Pi.single k (1 : ZMod 2)) else 1) ∈ Subgroup.closure S := by
    intro p _ k
    split_ifs
    · exact h k
    · exact Subgroup.one_mem _
  rw [eq_top_iff]
  intro x _
  rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl, key]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hite _ 0) (hite _ 1))
    (hite _ 2)) (hite _ 3)

theorem fix_nat_one : ∀ x : FLc.Vt 4,
    (1 + single 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 2 3 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 3 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x → x = 0 ∨ x = Pi.single 0 1 := by
  decide +kernel

theorem fix_dual_one : ∀ x : FLc.Vt 4,
    (1 + single 1 0 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 2 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 3 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 1 3 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x → x = 0 := by
  decide +kernel

theorem fix_nat_three : ∀ x : FLc.Vt 4,
    (1 + single 0 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 2 0 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 2 3 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x → x = 0 := by
  decide +kernel

theorem fix_dual_three : ∀ x : FLc.Vt 4,
    (1 + single 1 0 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 2 1 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x →
    (1 + single 0 2 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = x → x = 0 ∨ x = Pi.single 3 1 := by
  decide +kernel

theorem actM_e0 {g : SL4} (hg : g ∈ FLc.QI 4 {1}) :
    FLc.actM g (Multiplicative.ofAdd (Pi.single 0 1)) = Multiplicative.ofAdd (Pi.single 0 1) := by
  have hg' : g ∈ stabilizer (flagSpace 4 (ZMod 2) 1) := by
    rw [← L3318.flagStabilizer_singleton]
    exact hg
  rw [L3318.stabilizer_one_iff (Nat.card_zmod 2) (by norm_num)] at hg'
  apply Multiplicative.toAdd.injective
  rw [FLc.toAdd_actM, toAdd_ofAdd]
  show (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1
  funext r
  rw [Matrix.mulVec_single_one, Matrix.col_apply,
    show ((0 : Fin 4)) = ⟨0, by norm_num⟩ from rfl, hg' r, Pi.single_apply]
  by_cases hr : (r : ℕ) = 0
  · rw [ite_eq_left hr, ite_eq_left (Fin.ext hr)]
  · rw [ite_eq_right hr, ite_eq_right (fun e => hr (by rw [e]))]

theorem actDl_e3 {g : SL4} (hg : g ∈ perfectCore (FLc.QI 4 {3})) :
    FLc.actDl g (Multiplicative.ofAdd (Pi.single 3 1)) = Multiplicative.ofAdd (Pi.single 3 1) := by
  have hg' : g⁻¹ ∈ perfectCore (FLc.QI 4 {3}) := Subgroup.inv_mem _ hg
  apply Multiplicative.toAdd.injective
  rw [FLc.toAdd_actDl, toAdd_ofAdd]
  show ((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ Pi.single 3 1 = Pi.single 3 1
  funext r
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply, Pi.single_apply]
  by_cases hr : (r : ℕ) < 3
  · rw [L3318.bl_eq_zero (perfectCore_le _ hg') (i := 3) (j := r) (by decide) hr, ite_eq_right]
    intro e
    rw [e] at hr
    exact absurd hr (by decide)
  · have hr3 : r = 3 := by
      have := r.isLt
      exact Fin.ext (by change (r : ℕ) = 3; omega)
    subst hr3
    rw [L3318.br_eq_ite (Nat.card_zmod 2) le_rfl (by norm_num) hg' (i := 3) (j := 3) (by decide)
      (by decide)]

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}
  {ρ : FLc.SLt 4 →* MulAut ↥(vPlus L T)} [IsMulCommutative ↥(vPlus L T)]

theorem card_vt4 : Nat.card (Multiplicative (FLc.Vt 4)) = 16 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem card_comm_ge_one (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U₁ : Subgroup ↥(vPlus L T)}
    (D₁ : FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a)) :
    16 ≤ Nat.card ↥⁅vPlus L T, liftCore α (FLc.QI 4 {1})⁆ := by
  rw [← card_vt4]
  refine card_le_comm D₁ (P := (perfectCore (FLc.QI 4 {1}) : Set SL4))
    (fun g hg => exists_mem_Y h hαs hαv hg) (closure_eq_top_of_single fun k => ?_)
  apply Subgroup.subset_closure
  have key : ∀ {a b : Fin 4} (hab : a ≠ b),
      SpecialLinearGroup.transvection hab (1 : ZMod 2) ∈ perfectCore (FLc.QI 4 {1}) →
      (1 + single a b 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single b 1 + -Pi.single b 1 =
        Pi.single a 1 →
      Multiplicative.ofAdd (Pi.single a (1 : ZMod 2)) ∈
        {x | ∃ g ∈ (perfectCore (FLc.QI 4 {1}) : Set SL4), ∃ b : Multiplicative (FLc.Vt 4),
          x = FLc.actM g b * b⁻¹} := by
    intro a b hab hmem he
    refine ⟨_, hmem, Multiplicative.ofAdd (Pi.single b 1), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_actM_tr, toAdd_ofAdd, toAdd_ofAdd, he]
  fin_cases k
  · exact key (b := 1) (by decide) (tr_mem_one_rad (by decide) _) (by decide)
  · exact key (b := 2) (by decide) (tr_mem_one_levi (by decide) (by decide) _) (by decide)
  · exact key (b := 3) (by decide) (tr_mem_one_levi (by decide) (by decide) _) (by decide)
  · exact key (b := 1) (by decide) (tr_mem_one_levi (by decide) (by decide) _) (by decide)

theorem card_comm_ge_three (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U₂ : Subgroup ↥(vPlus L T)}
    (D₂ : FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) :
    16 ≤ Nat.card ↥⁅vPlus L T, liftCore α (FLc.QI 4 {3})⁆ := by
  rw [← card_vt4]
  refine card_le_comm D₂ (P := (perfectCore (FLc.QI 4 {3}) : Set SL4))
    (fun g hg => exists_mem_Y h hαs hαv hg) (closure_eq_top_of_single fun k => ?_)
  apply Subgroup.subset_closure
  have key : ∀ {a b : Fin 4} (hab : a ≠ b),
      SpecialLinearGroup.transvection hab (1 : ZMod 2) ∈ perfectCore (FLc.QI 4 {3}) →
      (1 + single b a 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single a 1 + -Pi.single a 1 =
        Pi.single b 1 →
      Multiplicative.ofAdd (Pi.single b (1 : ZMod 2)) ∈
        {x | ∃ g ∈ (perfectCore (FLc.QI 4 {3}) : Set SL4), ∃ c : Multiplicative (FLc.Vt 4),
          x = FLc.actDl g c * c⁻¹} := by
    intro a b hab hmem he
    refine ⟨_, hmem, Multiplicative.ofAdd (Pi.single a 1), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_actDl_tr, toAdd_ofAdd, toAdd_ofAdd, he]
  fin_cases k
  · exact key (a := 1) (by decide) (tr_mem_three_levi (by decide) (by decide) _) (by decide)
  · exact key (a := 0) (by decide) (tr_mem_three_levi (by decide) (by decide) _) (by decide)
  · exact key (a := 0) (by decide) (tr_mem_three_levi (by decide) (by decide) _) (by decide)
  · exact key (a := 0) (by decide) (tr_mem_three_rad (by decide) _) (by decide)

omit [Finite G] [IsMulCommutative ↥(vPlus L T)] in
theorem hfix_nat_one : ∀ b : Multiplicative (FLc.Vt 4),
    (∀ g ∈ (perfectCore (FLc.QI 4 {1}) : Set SL4), FLc.actM g b = b) →
      b = 1 ∨ b = Multiplicative.ofAdd (Pi.single 0 1) := by
  intro b hb
  have e2 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_one_levi (a := 1) (c := 2) (by decide) (by decide) (by decide)))
  have e3 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_one_levi (a := 2) (c := 3) (by decide) (by decide) (by decide)))
  have e4 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_one_levi (a := 3) (c := 1) (by decide) (by decide) (by decide)))
  rw [toAdd_actM_tr] at e2 e3 e4
  rcases fix_nat_one _ e2 e3 e4 with h0 | h0
  · exact Or.inl (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
  · exact Or.inr (Multiplicative.toAdd.injective (by rw [h0, toAdd_ofAdd]))

omit [Finite G] [IsMulCommutative ↥(vPlus L T)] in
theorem hfix_dual_one : ∀ b : Multiplicative (FLc.Vt 4),
    (∀ g ∈ (perfectCore (FLc.QI 4 {1}) : Set SL4), FLc.actDl g b = b) → b = 1 := by
  intro b hb
  have e1 := congrArg Multiplicative.toAdd (hb _ (tr_mem_one_rad (b := 1) (by decide) (by decide)))
  have e2 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_one_levi (a := 1) (c := 2) (by decide) (by decide) (by decide)))
  have e3 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_one_levi (a := 2) (c := 3) (by decide) (by decide) (by decide)))
  have e4 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_one_levi (a := 3) (c := 1) (by decide) (by decide) (by decide)))
  rw [toAdd_actDl_tr] at e1 e2 e3 e4
  exact Multiplicative.toAdd.injective (by rw [fix_dual_one _ e1 e2 e3 e4, toAdd_one])

omit [Finite G] [IsMulCommutative ↥(vPlus L T)] in
theorem hfix_nat_three : ∀ b : Multiplicative (FLc.Vt 4),
    (∀ g ∈ (perfectCore (FLc.QI 4 {3}) : Set SL4), FLc.actM g b = b) → b = 1 := by
  intro b hb
  have e1 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_three_levi (a := 0) (c := 1) (by decide) (by decide) (by decide)))
  have e2 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_three_levi (a := 1) (c := 2) (by decide) (by decide) (by decide)))
  have e3 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_three_levi (a := 2) (c := 0) (by decide) (by decide) (by decide)))
  have e4 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_three_rad (a := 2) (by decide) (by decide)))
  rw [toAdd_actM_tr] at e1 e2 e3 e4
  exact Multiplicative.toAdd.injective (by rw [fix_nat_three _ e1 e2 e3 e4, toAdd_one])

omit [Finite G] [IsMulCommutative ↥(vPlus L T)] in
theorem hfix_dual_three : ∀ b : Multiplicative (FLc.Vt 4),
    (∀ g ∈ (perfectCore (FLc.QI 4 {3}) : Set SL4), FLc.actDl g b = b) →
      b = 1 ∨ b = Multiplicative.ofAdd (Pi.single 3 1) := by
  intro b hb
  have e1 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_three_levi (a := 0) (c := 1) (by decide) (by decide) (by decide)))
  have e2 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_three_levi (a := 1) (c := 2) (by decide) (by decide) (by decide)))
  have e3 := congrArg Multiplicative.toAdd
    (hb _ (tr_mem_three_levi (a := 2) (c := 0) (by decide) (by decide) (by decide)))
  rw [toAdd_actDl_tr] at e1 e2 e3
  rcases fix_dual_three _ e1 e2 e3 with h0 | h0
  · exact Or.inl (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
  · exact Or.inr (Multiplicative.toAdd.injective (by rw [h0, toAdd_ofAdd]))

omit [IsMulCommutative ↥(vPlus L T)] in
theorem fix_of_mem_centralizer (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {I : Set ℕ} {v : G}
    (hv : v ∈ vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 I) : Set G)) :
    ∀ g ∈ (perfectCore (FLc.QI 4 I) : Set SL4), ρ g ⟨v, hv.1⟩ = ⟨v, hv.1⟩ := by
  intro g hg
  obtain ⟨y, hyY, hy⟩ := exists_mem_Y h hαs hαv hg
  apply Subtype.ext
  rw [hy]
  show y * v * y⁻¹ = v
  rw [Subgroup.mem_centralizer_iff.1 hv.2 y hyY, mul_inv_cancel_right]

theorem card_centralizer_le_one (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U₁ U₂ : Subgroup ↥(vPlus L T)} (hsup : U₁ ⊔ U₂ = ⊤) (hdisj : U₁ ⊓ U₂ = ⊥)
    (D₁ : FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a))
    (D₂ : FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) :
    Nat.card ↥(vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G)) ≤ 2 := by
  classical
  have hU₁ : ∀ v (hv : v ∈ vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G)),
      (⟨v, hv.1⟩ : ↥(vPlus L T)) ∈ U₁ := by
    intro v hv
    have hvU : (⟨v, hv.1⟩ : ↥(vPlus L T)) ∈ U₁ ⊔ U₂ := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := Subgroup.mem_sup.1 hvU
    have hfix12 : ∀ g ∈ (perfectCore (FLc.QI 4 {1}) : Set SL4), ρ g v₁ = v₁ ∧ ρ g v₂ = v₂ :=
      fun g hg => FLc.fixed_of_two hdisj (ρ g) (fun u hu => D₁.inv g u hu)
        (fun u hu => D₂.inv g u hu) hv₁ hv₂
          (by rw [hv12]; exact fix_of_mem_centralizer h hαs hαv hv g hg)
    have hv2 : v₂ = 1 :=
      Subgroup.mem_bot.1 (mem_of_fix D₂ hfix_dual_one hv₂ fun g hg => (hfix12 g hg).2)
    rw [← hv12, hv2, mul_one]
    exact hv₁
  have hval : ∀ v (hv : v ∈ vPlus L T ⊓
      Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G)),
      D₁.β ⟨⟨v, hv.1⟩, hU₁ v hv⟩ ∈
        ({1, Multiplicative.ofAdd (Pi.single 0 1)} : Finset (Multiplicative (FLc.Vt 4))) := by
    intro v hv
    rcases hfix_nat_one _ (beta_fix D₁ (hU₁ v hv) (fix_of_mem_centralizer h hαs hαv hv)) with
      h1 | h1 <;> simp [h1]
  let f : ↥(vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G)) →
      ↥({1, Multiplicative.ofAdd (Pi.single 0 1)} : Finset (Multiplicative (FLc.Vt 4))) :=
    fun v => ⟨_, hval v v.2⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h2 := FLc.VModel.β_injective D₁ (congrArg Subtype.val hvw)
    exact Subtype.ext (congrArg (fun x : ↥U₁ => ((x : ↥(vPlus L T)) : G)) h2)
  calc Nat.card ↥(vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G))
      ≤ Nat.card ↥({1, Multiplicative.ofAdd (Pi.single 0 1)} :
        Finset (Multiplicative (FLc.Vt 4))) := Nat.card_le_card_of_injective f hf
    _ = ({1, Multiplicative.ofAdd (Pi.single 0 1)} : Finset (Multiplicative (FLc.Vt 4))).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 2 := Finset.card_le_two

theorem card_centralizer_le_three (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U₁ U₂ : Subgroup ↥(vPlus L T)} (hsup : U₁ ⊔ U₂ = ⊤) (hdisj : U₁ ⊓ U₂ = ⊥)
    (D₁ : FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a))
    (D₂ : FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) :
    Nat.card ↥(vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G)) ≤ 2 := by
  classical
  have hU₂ : ∀ v (hv : v ∈ vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G)),
      (⟨v, hv.1⟩ : ↥(vPlus L T)) ∈ U₂ := by
    intro v hv
    have hvU : (⟨v, hv.1⟩ : ↥(vPlus L T)) ∈ U₁ ⊔ U₂ := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := Subgroup.mem_sup.1 hvU
    have hfix12 : ∀ g ∈ (perfectCore (FLc.QI 4 {3}) : Set SL4), ρ g v₁ = v₁ ∧ ρ g v₂ = v₂ :=
      fun g hg => FLc.fixed_of_two hdisj (ρ g) (fun u hu => D₁.inv g u hu)
        (fun u hu => D₂.inv g u hu) hv₁ hv₂
          (by rw [hv12]; exact fix_of_mem_centralizer h hαs hαv hv g hg)
    have hv1 : v₁ = 1 :=
      Subgroup.mem_bot.1 (mem_of_fix D₁ hfix_nat_three hv₁ fun g hg => (hfix12 g hg).1)
    rw [← hv12, hv1, one_mul]
    exact hv₂
  have hval : ∀ v (hv : v ∈ vPlus L T ⊓
      Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G)),
      D₂.β ⟨⟨v, hv.1⟩, hU₂ v hv⟩ ∈
        ({1, Multiplicative.ofAdd (Pi.single 3 1)} : Finset (Multiplicative (FLc.Vt 4))) := by
    intro v hv
    rcases hfix_dual_three _ (beta_fix D₂ (hU₂ v hv) (fix_of_mem_centralizer h hαs hαv hv)) with
      h1 | h1 <;> simp [h1]
  let f : ↥(vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G)) →
      ↥({1, Multiplicative.ofAdd (Pi.single 3 1)} : Finset (Multiplicative (FLc.Vt 4))) :=
    fun v => ⟨_, hval v v.2⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h2 := FLc.VModel.β_injective D₂ (congrArg Subtype.val hvw)
    exact Subtype.ext (congrArg (fun x : ↥U₂ => ((x : ↥(vPlus L T)) : G)) h2)
  calc Nat.card ↥(vPlus L T ⊓ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G))
      ≤ Nat.card ↥({1, Multiplicative.ofAdd (Pi.single 3 1)} :
        Finset (Multiplicative (FLc.Vt 4))) := Nat.card_le_card_of_injective f hf
    _ = ({1, Multiplicative.ofAdd (Pi.single 3 1)} : Finset (Multiplicative (FLc.Vt 4))).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 2 := Finset.card_le_two

omit [Finite G] [IsMulCommutative ↥(vPlus L T)] in
theorem mem_comm_of_rho {Y : Subgroup G} {U' : Subgroup ↥(vPlus L T)} {g : SL4} {y : G}
    (hyY : y ∈ Y) (hy : ∀ v : ↥(vPlus L T), ((ρ g v : ↥(vPlus L T)) : G) = y * v * y⁻¹)
    (u : ↥U') (hmem : ρ g (u : ↥(vPlus L T)) ∈ U') :
    ((((⟨ρ g u, hmem⟩ * u⁻¹ : ↥U') : ↥(vPlus L T)) : G)) ∈ ⁅vPlus L T, Y⁆ := by
  have e1 : ((((⟨ρ g u, hmem⟩ * u⁻¹ : ↥U') : ↥(vPlus L T)) : G)) =
      ⁅y, (((u : ↥(vPlus L T))) : G)⁆ := by
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, hy]
  rw [e1, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hyY (u : ↥(vPlus L T)).2

theorem exists_fixed_comm_one (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U₁ : Subgroup ↥(vPlus L T)}
    (D₁ : FLc.VModel 4 ρ U₁ ⊥ (Multiplicative (FLc.Vt 4)) (fun g a => FLc.actM g a)) :
    ∃ c ∈ ⁅vPlus L T, liftCore α (FLc.QI 4 {1})⁆, c ≠ 1 ∧
      c ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {1}) : Set G) := by
  obtain ⟨u₀, hu₀⟩ := D₁.surj (Multiplicative.ofAdd (Pi.single 0 1))
  obtain ⟨u₁, hu₁⟩ := D₁.surj (Multiplicative.ofAdd (Pi.single 1 1))
  have hg := tr_mem_one_rad (b := 1) (by decide) (by decide)
  obtain ⟨y, hyY, hy⟩ := exists_mem_Y h hαs hαv hg
  have hmem := D₁.inv (SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 1) (by decide) 1)
    (u₁ : ↥(vPlus L T)) u₁.2
  have hw : (⟨ρ (SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := 1) (by decide) 1) u₁,
      hmem⟩ * u₁⁻¹ : ↥U₁) = u₀ := by
    apply FLc.VModel.β_injective D₁
    rw [map_mul, map_inv, D₁.equiv _ u₁ hmem, hu₁, hu₀]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_actM_tr, toAdd_ofAdd, toAdd_ofAdd]
    decide
  refine ⟨((u₀ : ↥(vPlus L T)) : G), ?_, ?_, ?_⟩
  · rw [← hw]
    exact mem_comm_of_rho hyY hy u₁ hmem
  · intro h1
    have h0 : u₀ = 1 := Subtype.ext (Subtype.ext h1)
    rw [h0, map_one] at hu₀
    have h2 := congrFun (congrArg Multiplicative.toAdd hu₀) 0
    simp at h2
  · rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    have hg' := L3318.mem_perfectCore_of_mem_liftCore hαs hy'
    have hmem' := D₁.inv (α ⟨y', liftCore_le α _ hy'⟩) (u₀ : ↥(vPlus L T)) u₀.2
    have hfix : (⟨ρ (α ⟨y', liftCore_le α _ hy'⟩) u₀, hmem'⟩ : ↥U₁) = u₀ := by
      apply FLc.VModel.β_injective D₁
      rw [D₁.equiv _ u₀ hmem', hu₀]
      exact actM_e0 (perfectCore_le _ hg')
    have h1 := congrArg (fun x : ↥U₁ => ((x : ↥(vPlus L T)) : G)) hfix
    simp only at h1
    rw [hαv, FLc.conjAct_coe] at h1
    calc y' * ((u₀ : ↥(vPlus L T)) : G) = (y' * u₀ * y'⁻¹) * y' := by group
      _ = u₀ * y' := by rw [h1]

theorem exists_fixed_comm_three (h : Hyp331 G T M L D) (hαs : Function.Surjective α)
    (hαv : ∀ l : ↥L, ρ (α l) = conjAct (vPlus L T) ⟨l, L3317.le_normalizer_vPlus h l.2⟩)
    {U₂ : Subgroup ↥(vPlus L T)}
    (D₂ : FLc.VModel 4 ρ U₂ ⊥ (Multiplicative (FLc.Vt 4)) FLc.actDl) :
    ∃ c ∈ ⁅vPlus L T, liftCore α (FLc.QI 4 {3})⁆, c ≠ 1 ∧
      c ∈ Subgroup.centralizer (liftCore α (FLc.QI 4 {3}) : Set G) := by
  obtain ⟨u₃, hu₃⟩ := D₂.surj (Multiplicative.ofAdd (Pi.single 3 1))
  obtain ⟨u₂, hu₂⟩ := D₂.surj (Multiplicative.ofAdd (Pi.single 2 1))
  have hg := tr_mem_three_rad (a := 2) (by decide) (by decide)
  obtain ⟨y, hyY, hy⟩ := exists_mem_Y h hαs hαv hg
  have hmem := D₂.inv (SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := 3) (by decide) 1)
    (u₂ : ↥(vPlus L T)) u₂.2
  have hw : (⟨ρ (SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := 3) (by decide) 1) u₂,
      hmem⟩ * u₂⁻¹ : ↥U₂) = u₃ := by
    apply FLc.VModel.β_injective D₂
    rw [map_mul, map_inv, D₂.equiv _ u₂ hmem, hu₂, hu₃]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_actDl_tr, toAdd_ofAdd, toAdd_ofAdd]
    decide
  refine ⟨((u₃ : ↥(vPlus L T)) : G), ?_, ?_, ?_⟩
  · rw [← hw]
    exact mem_comm_of_rho hyY hy u₂ hmem
  · intro h1
    have h0 : u₃ = 1 := Subtype.ext (Subtype.ext h1)
    rw [h0, map_one] at hu₃
    have h2 := congrFun (congrArg Multiplicative.toAdd hu₃) 3
    simp at h2
  · rw [Subgroup.mem_centralizer_iff]
    intro y' hy'
    have hg' := L3318.mem_perfectCore_of_mem_liftCore hαs hy'
    have hmem' := D₂.inv (α ⟨y', liftCore_le α _ hy'⟩) (u₃ : ↥(vPlus L T)) u₃.2
    have hfix : (⟨ρ (α ⟨y', liftCore_le α _ hy'⟩) u₃, hmem'⟩ : ↥U₂) = u₃ := by
      apply FLc.VModel.β_injective D₂
      rw [D₂.equiv _ u₃ hmem', hu₃]
      exact actDl_e3 hg'
    have h1 := congrArg (fun x : ↥U₂ => ((x : ↥(vPlus L T)) : G)) hfix
    simp only at h1
    rw [hαv, FLc.conjAct_coe] at h1
    calc y' * ((u₃ : ↥(vPlus L T)) : G) = (y' * u₃ * y'⁻¹) * y' := by group
      _ = u₃ * y' := by rw [h1]

omit [Finite G] [IsMulCommutative ↥(vPlus L T)] in
theorem isModO2Surj_comp {Y : Subgroup G} {ψ : ↥Y →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = CFSG.pCore 2 ↥Y) :
    IsModO2Surj Y ((specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom.comp ψ) :=
  ⟨by rw [MonoidHom.coe_comp]; exact (MulEquiv.surjective _).comp hψs,
    by rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hψk]⟩

end CFSG.Quasithin.H13.L3321
