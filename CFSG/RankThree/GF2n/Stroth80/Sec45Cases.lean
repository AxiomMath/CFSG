module

public import CFSG.RankThree.GF2n.Stroth80.Sec4SwapCtx
public import CFSG.RankThree.GF2n.Stroth80.Sec45
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem eq_of_isQuasisimple_of_component {Γ : Type} [Group Γ] [Finite Γ] {X C : Subgroup Γ}
    (hX : CFSG.IsQuasisimple ↥X) (hCX : C ≤ X) (hC : IsComponent C)
    (hXN : X ≤ Subgroup.normalizer (C : Set Γ)) : X = C := by
  have hn : (C.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hXN
  rcases normal_le_center_or_eq_top hX hn with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hC
    apply hab
    apply Subtype.ext
    have := Subgroup.mem_center_iff.mp
      (h (show (⟨(a : Γ), hCX a.2⟩ : ↥X) ∈ C.subgroupOf X from a.2)) ⟨(b : Γ), hCX b.2⟩
    exact (congrArg Subtype.val this).symm
  · refine le_antisymm (fun x hx => ?_) hCX
    have : (⟨x, hx⟩ : ↥X) ∈ C.subgroupOf X := by rw [h]; exact Subgroup.mem_top _
    exact this

section Main


theorem stroth45_of_42_43 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hCQ : ClassicalQuasisimpleStatement)
    (h42 : Stroth42Statement) (h43 : Stroth43Statement) : Stroth45Statement := by
  intro G _ _ M Q Z B hN hc n hw hn hno hgen
  classical
  have hE0 : layer (Mbar M Q) ≠ ⊥ := stroth45_layer_ne_bot h34 h44 G M Q Z B hc n hw hn hno hgen
  refine ⟨hE0, ?_⟩
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hSL2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      CFSG.IsQuasisimple ↥(StatedSL 2 K) := by
    intro K _ _ hK
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
    exact (hCQ K (by rw [hK]; exact hq4)).1 2 le_rfl
  have hqSL : ∀ X : Subgroup (Mbar M Q), IsSLModel 2 (Nat.card Z) ↥X → CFSG.IsQuasisimple ↥X := by
    rintro X ⟨K, hF, hFin, hK, ⟨e⟩⟩
    exact isQuasisimple_of_mulEquiv' e.symm (hSL2 K hK)
  have hcs := hc.compSimple h34 h44 hw hn hno hgen
  have hΛ := hc.swapHyp hw hn hno
  have hEn : (layer (Mbar M Q)).Normal := by
    haveI := CFSG.LocalCores.layer_characteristic (G := Mbar M Q)
    infer_instance
  by_cases hasSL : ∃ C : Subgroup (Mbar M Q), IsComponent C ∧ IsSLModel 2 (Nat.card Z) ↥C
  swap
  ·
    left
    refine h42 G M Q Z B hc n hw hn hno hgen hE0 ?_
    rintro ⟨X, hXE, hXn, hXSL⟩
    apply hasSL
    exact ⟨X, ⟨hqSL X hXSL, Subgroup.IsSubnormal.trans hXE hXn.isSubnormal hEn.isSubnormal⟩,
      hXSL⟩
  obtain ⟨Y₁, hY₁c, hY₁SL⟩ := hasSL
  by_cases hu : ∀ C : Subgroup (Mbar M Q), IsComponent C → IsSLModel 2 (Nat.card Z) ↥C → C = Y₁
  · by_cases hEsl : IsSLModel 2 (Nat.card Z) ↥(layer (Mbar M Q))
    · exact Or.inl (hqSL _ hEsl)
    · exact Or.inr (Or.inl (h43 G M Q Z B hc n hw hn hno hgen
        ⟨Y₁, ⟨hY₁c, hY₁SL⟩, fun C hC => hu C hC.1 hC.2⟩ hEsl))
  push Not at hu
  obtain ⟨Y₂, hY₂c, hY₂SL, hY₂ne⟩ := hu
  right
  by_cases hmov : ∃ Zc : Subgroup (Mbar M Q), IsComponent Zc ∧ IsSLModel 2 (Nat.card Z) ↥Zc ∧
      ∃ s ∈ bar M Q (LB M Q B), conjSubgroup s Zc ≠ Zc
  ·
    obtain ⟨Zc, hZc, hZSL, s, hsΛ, hsne⟩ := hmov
    have hZ'c := isComponent_conjSubgroup s hZc
    have hlay : layer (Mbar M Q) = Zc ⊔ conjSubgroup s Zc := by
      refine le_antisymm (sSup_le fun C hC => ?_)
        (sup_le (CFSG.LocalCores.component_le_layer hZc)
          (CFSG.LocalCores.component_le_layer hZ'c))
      by_cases h1 : C = Zc
      · rw [h1]; exact le_sup_left
      by_cases h2 : C = conjSubgroup s Zc
      · rw [h2]; exact le_sup_right
      exact (hc.false_of_swap_third h34 h310 hCQ hw hn hno hgen hcs hZc hsΛ hsne hC h1 h2).elim
    refine Or.inl ⟨conjSubgroup s Zc, Zc, by rw [sup_comm]; exact hlay.symm, ?_, ?_, hZ'c.1, hZSL⟩
    · rw [inf_comm]; exact swap_inf_eq_bot hcs hZc hsne
    · intro x hx y hy
      exact (swap_comm hZc hsne y hy x hx).symm
  push Not at hmov
  have hΛY : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Y₁ : Set (Mbar M Q)) :=
    fun s hs => conjSubgroup_eq_self_iff.mp (hmov Y₁ hY₁c hY₁SL s hs)
  obtain ⟨tb, htb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (hc.inter_bar_LB_ne_bot h34 hw hn hno hgen hY₁c.1 hΛY)
  have htbΛ : (tb : Mbar M Q) ∈ bar M Q (LB M Q B) := tb.2.1
  have htbY : (tb : Mbar M Q) ∈ Y₁ := tb.2.2
  have htbne : (tb : Mbar M Q) ≠ 1 := fun h => htb1 (Subtype.ext h)
  obtain ⟨t', htLB, htQ, hmk⟩ := hc.exists_lift_ne_one htbΛ htbne
  set 𝒮 : Set (Subgroup (Mbar M Q)) := {C | IsComponent C ∧ C ≠ Y₁} with h𝒮
  set X : Subgroup (Mbar M Q) := sSup 𝒮 with hX
  obtain ⟨hXcent0, hEX0⟩ := CFSG.WholeGroup.layer_eq_sup_others hY₁c
  have hXcent : X ≤ Subgroup.centralizer (Y₁ : Set (Mbar M Q)) := hXcent0
  have hEX : layer (Mbar M Q) = Y₁ ⊔ X := hEX0
  have hXE : X ≤ layer (Mbar M Q) := sSup_le fun C hC => CFSG.LocalCores.component_le_layer hC.1
  have hXY : X ⊓ Y₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxY⟩
    exact Subgroup.mem_bot.mpr (hcs.eq_one_of_commutes hY₁c hxY fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hXcent hxX) y hy)
  have hXR : ∀ C ∈ 𝒮, C ≤ bar M Q (Rt M (LB M Q B) (t' : G)) := by
    intro C hC
    refine hc.component_le_bar_Rt h34 hw hn hno hgen hcs hC.1 htLB fun x hx => ?_
    rw [hmk]
    exact comm_of_ne_component hC.1 hY₁c hC.2 x hx tb htbY
  have hXle : X ≤ bar M Q (Rt M (LB M Q B) (t' : G)) := sSup_le hXR
  have hY₂𝒮 : Y₂ ∈ 𝒮 := ⟨hY₂c, hY₂ne⟩
  have hY₂X : Y₂ ≤ X := le_sSup hY₂𝒮
  have hRne : Rt M (LB M Q B) (t' : G) ≠ LB M Q B := by
    intro hRL
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hY₂c
    have hCΛ : Y₂ ≤ bar M Q (LB M Q B) := by
      have := hXR Y₂ hY₂𝒮
      rwa [hRL] at this
    exact hab (Subtype.ext (hΛ.comm _ (hCΛ a.2) _ (hCΛ b.2)))
  obtain ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl⟩ :=
    hc.classical_quotient h310 hw hn hno hgen htLB htQ hRne
  have hshape := hcl.shape hCQ (by rw [hK]; exact hq4)
  have hRfix : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t' : G)), conjSubgroup r Y₁ = Y₁ := by
    intro r hr
    by_contra hne
    have hcomm' := hc.bar_Rt_comm (t := t') r hr
    have h1 : (tb : Mbar M Q) ∈ conjSubgroup r Y₁ := by
      have := (mul_mem_conjSubgroup_iff (g := r) (T := Y₁)).mpr htbY
      have e : r * (tb : Mbar M Q) * r⁻¹ = tb := by
        rw [← hmk, hcomm']
        group
      rwa [e] at this
    have h2 : (tb : Mbar M Q) ∈ conjSubgroup r Y₁ ⊓ Y₁ := ⟨h1, htbY⟩
    rw [hcs.inf_eq_bot (isComponent_conjSubgroup r hY₁c) hY₁c hne, Subgroup.mem_bot] at h2
    exact htbne h2
  have hXnorm : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t' : G)), ∀ x ∈ X, r * x * r⁻¹ ∈ X := by
    intro r hr x hx
    have hmap : ∀ C ∈ 𝒮, conjSubgroup r C ∈ 𝒮 := by
      intro C hC
      refine ⟨isComponent_conjSubgroup r hC.1, fun h => hC.2 ?_⟩
      have h1 : conjSubgroup r⁻¹ (conjSubgroup r C) = C := by
        rw [← conjSubgroup_mul_sec4, inv_mul_cancel, conjSubgroup_one_sec4]
      have h2 : conjSubgroup r Y₁ = Y₁ := hRfix r hr
      calc C = conjSubgroup r⁻¹ (conjSubgroup r C) := h1.symm
        _ = conjSubgroup r⁻¹ Y₁ := by rw [h]
        _ = conjSubgroup r⁻¹ (conjSubgroup r Y₁) := by rw [h2]
        _ = Y₁ := by rw [← conjSubgroup_mul_sec4, inv_mul_cancel, conjSubgroup_one_sec4]
    have hle : X ≤ X.comap (MulAut.conj r).toMonoidHom := by
      refine sSup_le fun C hC => ?_
      exact Subgroup.map_le_iff_le_comap.mp (le_sSup (hmap C hC))
    exact hle hx
  have hinj : ∀ x : ↥X, π ⟨(x : Mbar M Q), hXle x.2⟩ = 1 → x = 1 := by
    intro x hx
    have h1 := (hπk ⟨(x : Mbar M Q), hXle x.2⟩).mp hx
    have h2 : (x : Mbar M Q) ∈ X ⊓ bar M Q (hc.CN (t' : G)) := ⟨x.2, h1⟩
    rw [hc.sSup_inf_CN_eq_bot h34 hw hn hno hgen hcs htLB 𝒮
      (fun C hC => ⟨hC.1, hXR C hC⟩), Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hns : ¬ Group.IsSolvable ↥X := by
    intro hs
    haveI := hs
    exact not_isSolvable_of_isQuasisimple hY₂c.1
      (solvable_of_solvable_injective (f := Subgroup.inclusion hY₂X)
        (Subgroup.inclusion_injective hY₂X))
  have hEnormX : layer (Mbar M Q) ≤ Subgroup.normalizer (X : Set (Mbar M Q)) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : X ≤ X.comap (MulAut.conj e).toMonoidHom := by
      refine sSup_le fun C hC c hc' => ?_
      have : e * c * e⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (CFSG.LocalCores.layer_le_normalizer hC.1 he) c).mp hc'
      exact le_sSup hC this
    exact hle hx
  have finish : CFSG.IsQuasisimple ↥X → ∃ X' Y' : Subgroup (Mbar M Q),
      X' ⊔ Y' = layer (Mbar M Q) ∧ X' ⊓ Y' = ⊥ ∧ (∀ x ∈ X', ∀ y ∈ Y', Commute x y) ∧
        CFSG.IsQuasisimple ↥X' ∧ IsSLModel 2 (Nat.card Z) ↥Y' := by
    intro hXq
    have hXeq : X = Y₂ := eq_of_isQuasisimple_of_component hXq hY₂X hY₂c fun x hx =>
      CFSG.LocalCores.layer_le_normalizer hY₂c (hXE hx)
    refine ⟨Y₂, Y₁, by rw [← hXeq, sup_comm]; exact hEX.symm, hcs.inf_eq_bot hY₂c hY₁c hY₂ne,
      fun x hx y hy => comm_of_ne_component hY₂c hY₁c hY₂ne x hx y hy, hY₂c.1, hY₁SL⟩
  have hSL2K : CFSG.IsQuasisimple ↥(StatedSL 2 K) := hSL2 K hK
  haveI : CharP K 2 := hK2
  rcases normal_embedding_cases hSL2K (R := bar M Q (Rt M (LB M Q B) (t' : G))) (X := X)
    π hπs hshape hXle hXnorm hinj hns with ⟨hq, ⟨e⟩⟩ | he | he
  · exact Or.inl (finish (isQuasisimple_of_mulEquiv' e.symm hq))
  · obtain ⟨e⟩ := he
    exact Or.inl (finish (isQuasisimple_of_mulEquiv' e.symm hSL2K))
  ·
    obtain ⟨e⟩ := he
    obtain ⟨Z₁, Z₂, hZ₁X, hZ₂X, hZ₁n, hZ₂n, hsup, -, hcomm, ⟨e₁⟩, ⟨e₂⟩⟩ :=
      exists_two_factors hSL2K e
    have hXsub : X.IsSubnormal := Subgroup.IsSubnormal.trans hXE
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXE).mpr hEnormX).isSubnormal
      hEn.isSubnormal
    have hZ₁c : IsComponent Z₁ :=
      ⟨isQuasisimple_of_mulEquiv' e₁.symm hSL2K,
        Subgroup.IsSubnormal.trans hZ₁X hZ₁n.isSubnormal hXsub⟩
    have hZ₂c : IsComponent Z₂ :=
      ⟨isQuasisimple_of_mulEquiv' e₂.symm hSL2K,
        Subgroup.IsSubnormal.trans hZ₂X hZ₂n.isSubnormal hXsub⟩
    have hZ₁SL : IsSLModel 2 (Nat.card Z) ↥Z₁ := ⟨K, hF, hFin, hK, ⟨e₁⟩⟩
    have hZ₂SL : IsSLModel 2 (Nat.card Z) ↥Z₂ := ⟨K, hF, hFin, hK, ⟨e₂⟩⟩
    have hY₁Z₁ : ∀ x ∈ Y₁, ∀ y ∈ Z₁, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hXcent (hZ₁X hy)) x hx
    have hY₁Z₂ : ∀ x ∈ Y₁, ∀ y ∈ Z₂, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hXcent (hZ₂X hy)) x hx
    have hQS : ∀ C : Subgroup (Mbar M Q), IsComponent C → IsSLModel 2 (Nat.card Z) ↥C →
        IsQSNormalIn C (bar M Q (Lgen M (LB M Q B))) := by
      intro C hC hCSL
      have hle : C ≤ bar M Q (Lgen M (LB M Q B)) :=
        component_le_of_not_centralizes hc.normal_bar_Lgen (hc.noComm h34 hw hn hno hgen) hC
      have hnorm : bar M Q (Lgen M (LB M Q B)) ≤ Subgroup.normalizer (C : Set (Mbar M Q)) :=
        hc.bar_Lgen_le_normalizer_of_forall fun g s hs =>
          conjSubgroup_eq_self_iff.mp (hmov _ (isComponent_conjSubgroup g hC)
            (isSLModel_conjSubgroup hCSL g) s hs)
      exact ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hnorm, hC.1⟩
    have h3 : (Y₁ ⊔ Z₁) ⊓ Z₂ = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx12, hx3⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hY₁Z₁ hx12
      have hxc1 : ∀ y ∈ Y₁, y * (a * b) = (a * b) * y := fun y hy => hY₁Z₂ y hy _ hx3
      have ha1 : a = 1 := by
        refine hcs.eq_one_of_commutes hY₁c ha fun y hy => ?_
        have hyb : y * b = b * y := hY₁Z₁ y hy b hb
        refine mul_right_cancel (b := b) ?_
        calc y * a * b = y * (a * b) := by group
          _ = (a * b) * y := hxc1 y hy
          _ = a * (b * y) := by group
          _ = a * (y * b) := by rw [hyb]
          _ = a * y * b := by group
      have hb1 : b = 1 := by
        refine hcs.eq_one_of_commutes hZ₁c hb fun z hz => ?_
        have haz : a * z = z * a := hY₁Z₁ a ha z hz
        have hzx : z * (a * b) = (a * b) * z := hcomm z hz _ hx3
        refine mul_left_cancel (a := a) ?_
        calc a * (z * b) = (a * z) * b := by group
          _ = (z * a) * b := by rw [haz]
          _ = z * (a * b) := by group
          _ = (a * b) * z := hzx
          _ = a * (b * z) := by group
      rw [ha1, hb1]
      exact Subgroup.mem_bot.mpr (by simp)
    refine Or.inr ⟨Y₁, Z₁, Z₂, ?_, ?_, h3, ?_, ?_, hY₁SL, hZ₁SL, hZ₂SL, hQS Y₁ hY₁c hY₁SL,
      hQS Z₁ hZ₁c hZ₁SL, hQS Z₂ hZ₂c hZ₂SL⟩
    · rw [sup_assoc, hsup]
      exact hEX.symm
    · rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      have : x ∈ X ⊓ Y₁ := ⟨hZ₁X hx2, hx1⟩
      rw [hXY, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr this
    · intro x hx y hy
      exact hY₁Z₁ x hx y hy
    · intro x hx y hy
      have hle : Y₁ ⊔ Z₁ ≤ Subgroup.centralizer ({y} : Set (Mbar M Q)) :=
        sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hY₁Z₂ a ha y hy))
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b hb y hy))
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

end Main

end CFSG.RankThree.GF2n.Stroth80
