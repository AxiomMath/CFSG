module

public import CFSG.Quasithin.Vol2.Ch7Sec77LieStmts
public import CFSG.RankThree.SubgroupLists.SymplecticReducible

public section

namespace CFSG.Quasithin.H13.Sp4Fix

open CFSG.RankThree.SubgroupLists Module Matrix

variable {F : Type} [Field F]

abbrev mat (g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

theorem mat_mul (g h : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) : mat (g * h) = mat g * mat h :=
  rfl

theorem mat_inv_mulVec (g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) (v : Fin 2 ⊕ Fin 2 → F) :
    mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
  rw [mulVec_mulVec, ← mat_mul, inv_mul_cancel]
  exact one_mulVec v

theorem sub_mem_orth {U : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    {g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)} (hg : ∀ u ∈ U, mat g *ᵥ u = u)
    (x : Fin 2 ⊕ Fin 2 → F) : mat g *ᵥ x - x ∈ orth U := by
  rw [mem_orth]
  intro u hu
  rw [map_sub, ← spForm_mulVec g.2 u x, hg u hu, sub_self]

theorem eq_one_of_fix {g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)}
    (hg : ∀ v, mat g *ᵥ v = v) : g = 1 := by
  apply Subtype.ext
  apply Units.ext
  show mat g = 1
  ext i j
  have h := congrFun (hg (Pi.single j 1)) i
  rw [mulVec_single_one] at h
  simpa [Matrix.one_apply, Pi.single_apply] using h

theorem fix_sup_span {U : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    {g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)} (hg : ∀ u ∈ U, mat g *ᵥ u = u)
    {x : Fin 2 ⊕ Fin 2 → F} (hx : mat g *ᵥ x = x) :
    ∀ v ∈ U ⊔ Submodule.span F {x}, mat g *ᵥ v = v := by
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [mulVec_add, mulVec_smul, hg u hu, hx]

theorem finrank_lt_sup_span {U : Submodule F (Fin 2 ⊕ Fin 2 → F)} {x : Fin 2 ⊕ Fin 2 → F}
    (hx : x ∉ U) : finrank F U < finrank F ↥(U ⊔ Submodule.span F {x}) := by
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left fun h => hx ?_)
  rw [h]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem finrank_le_four (U : Submodule F (Fin 2 ⊕ Fin 2 → F)) : finrank F U ≤ 4 := by
  have h := Submodule.finrank_le U
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h

variable [Fintype F]

theorem card_orth (hF : Fintype.card F = 4) (U : Submodule F (Fin 2 ⊕ Fin 2 → F)) :
    Nat.card ↥(orth U) = 4 ^ (4 - finrank F U) := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_orth, Nat.card_eq_fintype_card, hF]

theorem card_le_four_of_fix_three (hF : Fintype.card F = 4)
    (Y : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) (U : Submodule F (Fin 2 ⊕ Fin 2 → F))
    (hU : 3 ≤ finrank F U) (hfix : ∀ g ∈ Y, ∀ u ∈ U, mat g *ᵥ u = u) : Nat.card Y ≤ 4 := by
  classical
  by_cases hUt : U = ⊤
  · have hY : Y = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      exact Subgroup.mem_bot.2 (eq_one_of_fix fun v => hfix g hg v (by rw [hUt]; trivial))
    rw [hY, Subgroup.card_bot]
    norm_num
  · obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hUt)
    have hfull : U ⊔ Submodule.span F {x} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := finrank_lt_sup_span hx
      have h2 := finrank_le_four (U ⊔ Submodule.span F {x})
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    let f : ↥Y → ↥(orth U) := fun g => ⟨mat g *ᵥ x - x, sub_mem_orth (hfix g g.2) x⟩
    have hf : Function.Injective f := by
      intro g h hgh
      have h1 : mat g *ᵥ x = mat h *ᵥ x := by
        have := congrArg Subtype.val hgh
        simpa [f] using this
      have hk : (g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))⁻¹ *
          (h : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∈ Y :=
        Y.mul_mem (Y.inv_mem g.2) h.2
      have h2 : mat ((g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))⁻¹ *
          (h : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))) *ᵥ x = x := by
        rw [mat_mul, ← mulVec_mulVec, ← h1, mat_inv_mulVec]
      have h3 := eq_one_of_fix fun v =>
        fix_sup_span (hfix _ hk) h2 v (by rw [hfull]; trivial)
      exact Subtype.ext (inv_mul_eq_one.1 h3)
    have h1 := Nat.card_le_card_of_injective f hf
    rw [card_orth hF] at h1
    have h4 := finrank_le_four U
    have h5 : 4 - finrank F U ≤ 1 := by omega
    exact h1.trans (by
      calc 4 ^ (4 - finrank F U) ≤ 4 ^ 1 := Nat.pow_le_pow_right (by norm_num) h5
        _ = 4 := by norm_num)

end CFSG.Quasithin.H13.Sp4Fix

namespace CFSG.Quasithin.H13

open CFSG.RankThree.SubgroupLists Module Matrix Sp4Fix

theorem sp4PlaneFixFact_holds : Sp4PlaneFixFact := by
  intro F _ _ hF X W hW hfix
  classical
  by_cases h3 : 3 ≤ finrank F W
  · exact (card_le_four_of_fix_three hF X W h3 hfix).trans (by norm_num)
  · have hW2 : finrank F W = 2 := by omega
    have hWt : W ≠ ⊤ := by
      intro h
      have h1 := finrank_top F (Fin 2 ⊕ Fin 2 → F)
      rw [← h, hW2, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h1
      omega
    obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hWt)
    let Y : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
      { carrier := {g | g ∈ X ∧ mat g *ᵥ x = x}
        one_mem' := ⟨X.one_mem, one_mulVec x⟩
        mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, by
          rw [mat_mul, ← mulVec_mulVec, hb.2, ha.2]⟩
        inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, by
          conv_lhs => rw [← ha.2]
          exact mat_inv_mulVec a x⟩ }
    have hYX : Y ≤ X := fun g hg => hg.1
    have hYcard : Nat.card Y ≤ 4 := by
      refine card_le_four_of_fix_three hF Y (W ⊔ Submodule.span F {x}) ?_ ?_
      · have := finrank_lt_sup_span hx
        omega
      · intro g hg
        exact fix_sup_span (hfix g hg.1) hg.2
    have hidx : (Y.subgroupOf X).index ≤ 16 := by
      let f : ↥X ⧸ Y.subgroupOf X → ↥(orth W) :=
        Quotient.lift (fun g : ↥X => (⟨mat (g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) *ᵥ x - x,
          sub_mem_orth (hfix _ g.2) x⟩ : ↥(orth W))) (fun a b hab => by
            have hab' : a⁻¹ * b ∈ Y.subgroupOf X := QuotientGroup.leftRel_apply.mp hab
            have h1 : mat ((a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))⁻¹ *
                (b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))) *ᵥ x = x :=
              (Subgroup.mem_subgroupOf.mp hab').2
            have h2 : mat (b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) *ᵥ x =
                mat (a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) *ᵥ x := by
              have e : (b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) =
                  (a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) *
                    ((a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))⁻¹ *
                      (b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))) := by group
              rw [e, mat_mul, ← mulVec_mulVec, h1]
            exact Subtype.ext (by simp only; rw [h2]))
      have hf : Function.Injective f := by
        intro a b hab
        induction a using QuotientGroup.induction_on with
        | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
        have h1 : mat (a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) *ᵥ x =
            mat (b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) *ᵥ x := by
          have := congrArg Subtype.val hab
          simpa [f] using this
        refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ⟨(a⁻¹ * b).2, ?_⟩)
        show mat ((a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))⁻¹ *
          (b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))) *ᵥ x = x
        rw [mat_mul, ← mulVec_mulVec, ← h1, mat_inv_mulVec]
      have h1 := Nat.card_le_card_of_injective f hf
      rw [card_orth hF, hW2] at h1
      exact h1
    have hcard := Subgroup.card_mul_index (Y.subgroupOf X)
    have hY' : Nat.card (Y.subgroupOf X) = Nat.card Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
    rw [hY'] at hcard
    rw [← hcard]
    calc Nat.card Y * (Y.subgroupOf X).index ≤ 4 * 16 := Nat.mul_le_mul hYcard hidx
      _ = 64 := by norm_num

end CFSG.Quasithin.H13
