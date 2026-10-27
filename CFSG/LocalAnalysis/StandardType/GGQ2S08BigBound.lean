module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

private theorem ggQ2s08bf2_card_bs (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) : Nat.card ↥Bs = 3 ^ n := by
  have hV : Nat.card M.V = 3 ^ n := by
    rw [Nat.card_congr κ.toEquiv]
    simp [Vn, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
    _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
    _ = 3 ^ n := hV

private theorem ggQ2s08bf2_comm (M : GGQ2LDatum 3 Bs L x) :
    ∀ a b : ↥Bs, a * b = b * a := by
  intro a b
  apply Additive.ofMul.injective
  apply M.model.injective
  rw [ofMul_mul, ofMul_mul, map_add, map_add]
  exact add_comm _ _

private theorem ggQ2s08bf2_card_comap (M : GGQ2LDatum 3 Bs L x) {n : ℕ}
    (κ : M.V ≃ₗ[ZMod 3] Vn n) (R : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n))
    (hR : R ≤ (ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ)) :
    Nat.card ↥(R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs) = Nat.card ↥R := by
  have hinj : Function.Injective (ggQ2CellLin M κ) := ggQ2CellLin_injective M κ
  have hmap : (R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ) = R := by
    apply le_antisymm
    · intro r hr
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hr
      exact hφ.1
    · intro r hr
      obtain ⟨φ, hφA, hφr⟩ := Subgroup.mem_map.mp (hR hr)
      refine Subgroup.mem_map.mpr ⟨φ, ⟨?_, hφA⟩, hφr⟩
      exact Subgroup.mem_comap.mpr (hφr ▸ hr)
  have hcard : Nat.card ↥((R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs).map
      (ggQ2CellLin M κ)) = Nat.card ↥(R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs) :=
    Subgroup.card_map_of_injective (f := ggQ2CellLin M κ) hinj
  rw [hmap] at hcard
  exact hcard.symm

theorem ggQ2s08_big_bound [Finite G]
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S)
    (M : GGQ2LDatum 3 Bs L x) (hF : M.ShapeFull) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab)
    (hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab))
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hMW : GGQ2LabelWeyl lab M.coxeter) (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1)) :
    (∀ R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)),
        R ≤ (ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ) →
        8 * Nat.card R < 3 ^ ((lab.rank + 1) * lab.rank / 2)) ∧
      (∀ (R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)))
        (H : Submodule (ZMod 3) (Vn (lab.rank + 1))),
        R ≤ (ggAutomizer ⊤ Bs).map (ggQ2CellLin M κ) →
        IsCompl H (Submodule.span (ZMod 3) {κ M.xV}) → (∀ a ∈ R, ∀ h ∈ H, a h ∈ H) →
        8 * Nat.card R < 3 ^ (lab.rank * (lab.rank - 1) / 2)) := by
  classical
  have hBs : Nat.card ↥Bs = 3 ^ (lab.rank + 1) := ggQ2s08bf2_card_bs M κ
  have hab : ∀ a b : ↥Bs, a * b = b * a := ggQ2s08bf2_comm M
  have hN : 10 ≤ lab.rank + 1 := by
    have h9 : 9 ≤ lab.rank := hlab.2.2
    omega
  have hW : 2 ^ lab.rank * lab.rank.factorial ≤
      2 ^ (lab.rank + 1 - 1) * (lab.rank + 1 - 1).factorial := by
    rw [Nat.add_sub_cancel]
  have h1 := ggQ2s08_stab_card_le_all hTBW hS hnc M.hx M (Or.inl hF) hlab hmark hInn hCen hOut
    hMW
  have hD := ggQ2s08_diagPerm_card_le (M := M.coxeter) hlab hMW M.isCartan
  have hC := ggQ2s08_card_automizer_le M hlab hMW
  have hstab : Nat.card ↥(ggAutomizer ⊤ Bs ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨x, M.hx⟩ : ↥Bs)) ≤
      4 * (2 ^ lab.rank * lab.rank.factorial) := by
    calc _ ≤ 2 * Nat.card {π : M.Λ ≃ M.Λ // GGQ2S08DiagPerm 3 M.cartan π} *
        Nat.card ↥(ggAutomizer L Bs) := h1
      _ ≤ 2 * 2 * (2 ^ lab.rank * lab.rank.factorial) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hD) hC
      _ = 4 * (2 ^ lab.rank * lab.rank.factorial) := by ring
  constructor
  · intro R hR
    let A' : Subgroup (MulAut ↥Bs) :=
      R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs
    have hcard : Nat.card ↥A' = Nat.card ↥R := ggQ2s08bf2_card_comap M κ R hR
    have hbound := ggQ2s08_hsmall_irr M.hx hN hBs hW hstab (A := A') inf_le_right
    rwa [hcard] at hbound
  · intro R H hR hH hpres
    let A' : Subgroup (MulAut ↥Bs) :=
      R.comap (ggQ2CellLin M κ) ⊓ ggAutomizer ⊤ Bs
    have hcard : Nat.card ↥A' = Nat.card ↥R := ggQ2s08bf2_card_comap M κ R hR
    let H' : Subgroup ↥Bs :=
      { carrier := {b | κ (M.model (Additive.ofMul b)) ∈ H}
        one_mem' := by
          show κ (M.model (Additive.ofMul (1 : ↥Bs))) ∈ H
          rw [ofMul_one, map_zero, map_zero]
          exact H.zero_mem
        mul_mem' := by
          intro a b ha hb
          show κ (M.model (Additive.ofMul (a * b))) ∈ H
          rw [ofMul_mul, map_add, map_add]
          exact H.add_mem ha hb
        inv_mem' := by
          intro a ha
          show κ (M.model (Additive.ofMul a⁻¹)) ∈ H
          rw [ofMul_inv, map_neg, map_neg]
          exact H.neg_mem ha }
    have hxV : M.xV ≠ 0 := by
      intro h0
      exact hF.2.2.1 (h0 ▸ M.coSpan.zero_mem)
    have hxVκ : κ M.xV ≠ 0 := by
      intro h0
      exact hxV (κ.injective (by simpa using h0))
    have hxH : (⟨x, M.hx⟩ : ↥Bs) ∉ H' := by
      intro hmem
      change κ (M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs))) ∈ H at hmem
      have hmemH : κ M.xV ∈ H := by
        rw [GGQ2LDatum.xV]
        exact hmem
      have hspan : κ M.xV ∈ Submodule.span (ZMod 3) {κ M.xV} :=
        Submodule.mem_span_singleton_self _
      have hboth : κ M.xV ∈ H ⊓ Submodule.span (ZMod 3) {κ M.xV} := ⟨hmemH, hspan⟩
      have hbot : κ M.xV ∈ (⊥ : Submodule (ZMod 3) (Vn (lab.rank + 1))) := by
        rwa [hH.inf_eq_bot] at hboth
      exact hxVκ (by simpa using hbot)
    have hcardH' : Nat.card ↥H' = 3 ^ lab.rank := by
      let eH : ↥H' ≃ ↥H :=
        { toFun := fun b => ⟨κ (M.model (Additive.ofMul (b : ↥Bs))), b.2⟩
          invFun := fun h =>
            ⟨Additive.toMul (M.model.symm (κ.symm (h : Vn (lab.rank + 1)))),
              by
                show κ (M.model (Additive.ofMul
                  (Additive.toMul (M.model.symm (κ.symm (h : Vn (lab.rank + 1))))))) ∈ H
                rw [ofMul_toMul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
                exact h.2⟩
          left_inv := by
            intro b
            apply Subtype.ext
            show Additive.toMul (M.model.symm (κ.symm
              (κ (M.model (Additive.ofMul (b : ↥Bs)))))) = (b : ↥Bs)
            rw [LinearEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, toMul_ofMul]
          right_inv := by
            intro h
            apply Subtype.ext
            show κ (M.model (Additive.ofMul
              (Additive.toMul (M.model.symm (κ.symm (h : Vn (lab.rank + 1))))))) =
              (h : Vn (lab.rank + 1))
            rw [ofMul_toMul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] }
      rw [Nat.card_congr eH]
      have h3 := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := ↥(H.toAddSubgroup))
      rw [Nat.card_zmod] at h3
      change Nat.card ↥(H.toAddSubgroup) = 3 ^ lab.rank
      rw [h3]
      congr 1
      have hcompl := Submodule.finrank_add_eq_of_isCompl hH
      change Module.finrank (ZMod 3) ↥(H.toAddSubgroup) +
        Module.finrank (ZMod 3) ↥(ZMod 3 ∙ κ M.xV) =
        Module.finrank (ZMod 3) (Vn (lab.rank + 1)) at hcompl
      have hspan1 : Module.finrank (ZMod 3) ↥(ZMod 3 ∙ κ M.xV) = 1 :=
        finrank_span_singleton hxVκ
      have hVn : Module.finrank (ZMod 3) (Vn (lab.rank + 1)) = lab.rank + 1 := by
        simp [Vn, Module.finrank_fin_fun]
      rw [hspan1, hVn] at hcompl
      omega
    have hidx : H'.index = 3 := by
      have h3 := Subgroup.card_mul_index H'
      rw [hcardH', hBs, pow_succ] at h3
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) lab.rank) h3
    have hinv : ∀ φ ∈ A', ∀ b ∈ H', φ b ∈ H' := by
      intro φ hφ b hb
      have hfR : ggQ2CellLin M κ φ ∈ R := Subgroup.mem_comap.mp hφ.1
      have hbH : κ (M.model (Additive.ofMul b)) ∈ H := hb
      have hmem := hpres (ggQ2CellLin M κ φ) hfR
        (κ (M.model (Additive.ofMul b))) hbH
      show κ (M.model (Additive.ofMul (φ b))) ∈ H
      rwa [ggQ2CellLin_apply, LinearEquiv.symm_apply_apply, ggLin_apply_ofMul] at hmem
    have hbound := ggQ2s08_hsmall_red M.hx hab hlab.2.2 hBs (le_refl _) hstab
      (A := A') inf_le_right hxH hidx hinv
    rwa [hcard] at hbound

end CFSG.StandardType

end

