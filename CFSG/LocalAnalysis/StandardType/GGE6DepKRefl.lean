module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelReflClass
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem kRefl_gensL_mulVec_xx (i : Fin 6) : (gensL i).mulVec xx = xx := by
  revert i
  decide +kernel

private theorem closureL_mulVec_xx {g : Mat6} (hg : g ∈ closureL) : g.mulVec xx = xx := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact kRefl_gensL_mulVec_xx i
  | one => exact Matrix.one_mulVec _
  | mul g h _ _ ihg ihh => rw [← Matrix.mulVec_mulVec, ihh, ihg]

private theorem kRefl_xx_eq_single : xx = Pi.single 5 (1 : ZMod 3) := by
  funext i
  fin_cases i <;> simp [xx]

private theorem kRefl_xx_five : xx 5 = (1 : ZMod 3) := by
  rw [kRefl_xx_eq_single, Pi.single_eq_same]

private theorem kRefl_hpart_eq (v : Vec6) : hpart v = v - v 5 • xx := by
  rw [hpart, ← kRefl_xx_eq_single]

private theorem kRefl_decomp (v : Vec6) : v = hpart v + v 5 • xx := by
  rw [kRefl_hpart_eq, sub_add_cancel]

private theorem kRefl_hpart_five (v : Vec6) : (hpart v) 5 = 0 := by
  simp [hpart, Pi.single_eq_same]

private theorem kRefl_add_smul_xx_five (h : Vec6) (c : ZMod 3) :
    (h + c • xx) 5 = h 5 + c := by
  rw [Pi.add_apply, Pi.smul_apply, kRefl_xx_five, smul_eq_mul, mul_one]

private theorem kRefl_add_smul_xx_five_zero (h : Vec6) (hh : h 5 = 0) (c : ZMod 3) :
    (h + c • xx) 5 = c := by
  rw [kRefl_add_smul_xx_five, hh, zero_add]

private theorem kRefl_hpart_add_smul_xx_of (h : Vec6) (hh : h 5 = 0) (c : ZMod 3) :
    hpart (h + c • xx) = h := by
  rw [kRefl_hpart_eq, kRefl_add_smul_xx_five, hh, zero_add, add_sub_assoc, sub_self, add_zero]

private theorem kRefl_mul_mulVec_self (g : Mat6) (hg : g ∈ closureL)
    (hH : ∀ v : Vec6, v 5 = 0 → g.mulVec (g.mulVec v) = v) (v : Vec6) :
    (g * g).mulVec v = v := by
  rw [← Matrix.mulVec_mulVec]
  conv_lhs => rw [kRefl_decomp v]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, closureL_mulVec_xx hg,
    Matrix.mulVec_add, Matrix.mulVec_smul, hH (hpart v) (kRefl_hpart_five v),
    closureL_mulVec_xx hg]
  exact (kRefl_decomp v).symm

private theorem mul_self_eq_one {g : Mat6} (hg : g ∈ closureL)
    (hH : ∀ v : Vec6, v 5 = 0 → g.mulVec (g.mulVec v) = v) : g * g = 1 := by
  refine Matrix.ext fun i j => ?_
  have key : ∀ v : Vec6, (g * g).mulVec v = v := fun v => kRefl_mul_mulVec_self g hg hH v
  have h := congrFun (key (Pi.single j (1 : ZMod 3))) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h

private theorem kRefl_phi_apply_self {Bs : Subgroup G} {φ : MulAut ↥Bs} (hφ2 : φ ^ 2 = 1)
    (b : ↥Bs) : φ (φ b) = b := by
  have h := congrArg (fun ψ : MulAut ↥Bs => ψ b) hφ2
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply] at h
  exact h

private theorem frameK_sq {Bs X : Subgroup G} {y : G} {κ : Additive ↥Bs →+ Vec6}
    (hκ : GGE6DepKFrame Bs X y κ) {φ : MulAut ↥Bs} (hφ2 : φ ^ 2 = 1) {g : Mat6}
    (hact : ActsAsK κ φ g) : ∀ v : Vec6, v 5 = 0 → g.mulVec (g.mulVec v) = v := by
  intro v hv
  obtain ⟨b, hb⟩ := hκ.2.2.1 v hv
  have h1 : g.mulVec v = κ (Additive.ofMul (φ b)) := by
    rw [← hb]
    exact (hact b).symm
  calc g.mulVec (g.mulVec v) = g.mulVec (κ (Additive.ofMul (φ b))) := by rw [h1]
    _ = κ (Additive.ofMul (φ (φ b))) := (hact (φ b)).symm
    _ = κ (Additive.ofMul b) := by rw [kRefl_phi_apply_self hφ2 b]
    _ = v := hb

private theorem kRefl_zpow_three {M : Type*} [Group M] {a : M} (ha : a ^ 3 = 1) (k : ℤ) :
    (a ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast (a ^ k) 3, ← zpow_mul a k ((3 : ℕ) : ℤ), mul_comm k ((3 : ℕ) : ℤ),
    zpow_mul a ((3 : ℕ) : ℤ) k, zpow_natCast a 3, ha, one_zpow]

private theorem frameK_fix_iff {Bs X : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy3 : y ^ 3 = 1)
    {κ : Additive ↥Bs →+ Vec6} (hκ : GGE6DepKFrame Bs X y κ) {φ : MulAut ↥Bs} (hφ2 : φ ^ 2 = 1)
    (hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩) {g : Mat6} (hact : ActsAsK κ φ g) (b : ↥Bs) :
    g.mulVec (κ (Additive.ofMul b)) = κ (Additive.ofMul b) ↔ φ b = b := by
  constructor
  · intro hg
    set u : ↥Bs := φ b * b⁻¹ with hu_def
    have huκ : κ (Additive.ofMul u) = 0 := by
      rw [hu_def, ofMul_mul, map_add, ofMul_inv, map_neg, hact b, hg]
      simp
    have hmem : (u : G) ∈ Subgroup.zpowers y := (hκ.1 u).mp huκ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hy3' : (⟨y, hyBs⟩ : ↥Bs) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      simpa using hy3
    have hu_eq : u = (⟨y, hyBs⟩ : ↥Bs) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    have huφu : φ u = u := by
      rw [hu_eq, map_zpow, hφy]
    have huφuinv : φ u = u⁻¹ := by
      rw [hu_def, map_mul, map_inv, kRefl_phi_apply_self hφ2 b, mul_inv_rev, inv_inv]
    have hsymm : u = u⁻¹ := huφu.symm.trans huφuinv
    have huu : u * u = 1 := by
      simpa [← hsymm] using mul_inv_cancel u
    have hu3 : u ^ 3 = 1 := by
      rw [hu_eq]
      exact kRefl_zpow_three hy3' k
    have huu3 : u ^ 3 = u := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, huu, one_mul]
    have hu1 : u = 1 := huu3.symm.trans hu3
    exact mul_inv_eq_one.mp (by rw [← hu_def]; exact hu1)
  · intro hb
    have h := hact b
    rw [hb] at h
    exact h.symm

private def kRefl_Fx {Bs : Subgroup G} (φ : MulAut ↥Bs) : AddSubgroup (Additive ↥Bs) where
  carrier := {a | φ (Additive.toMul a) = Additive.toMul a}
  zero_mem' := by
    change φ (Additive.toMul (0 : Additive ↥Bs)) = Additive.toMul (0 : Additive ↥Bs)
    rw [show Additive.toMul (0 : Additive ↥Bs) = 1 from rfl, map_one]
  add_mem' := by
    intro a b ha hb
    change φ (Additive.toMul (a + b)) = Additive.toMul (a + b)
    rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl,
      map_mul, ha, hb]
  neg_mem' := by
    intro a ha
    change φ (Additive.toMul (-a)) = Additive.toMul (-a)
    rw [show Additive.toMul (-a) = (Additive.toMul a)⁻¹ from rfl, map_inv, ha]

private def kRefl_fxEquiv {Bs : Subgroup G} (φ : MulAut ↥Bs) :
    ↥(kRefl_Fx φ) ≃ {b : ↥Bs // φ b = b} where
  toFun a := ⟨Additive.toMul (a.1 : Additive ↥Bs), a.2⟩
  invFun b := ⟨Additive.ofMul b.1, by
    change φ b.1 = b.1
    exact b.2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    rfl

private def kRefl_f {Bs : Subgroup G} (κ : Additive ↥Bs →+ Vec6) (φ : MulAut ↥Bs) :
    ↥(kRefl_Fx φ) →+ Vec6 :=
  κ.comp (kRefl_Fx φ).subtype

private noncomputable def kRefl_kerEquiv {Bs : Subgroup G} {y : G} (hyBs : y ∈ Bs)
    {κ : Additive ↥Bs →+ Vec6}
    (hκ0 : ∀ b : ↥Bs, κ (Additive.ofMul b) = 0 ↔ (b : G) ∈ Subgroup.zpowers y)
    {φ : MulAut ↥Bs} (hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩) :
    ↥(kRefl_f κ φ).ker ≃ Subgroup.zpowers y where
  toFun a := by
    have h : kRefl_f κ φ a.1 = 0 := AddMonoidHom.mem_ker.mp a.2
    have h2 : κ (a.1 : Additive ↥Bs) = 0 := h
    refine ⟨((Additive.toMul (a.1 : Additive ↥Bs) : ↥Bs) : G),
      (hκ0 (Additive.toMul (a.1 : Additive ↥Bs))).mp ?_⟩
    rwa [show Additive.ofMul (Additive.toMul (a.1 : Additive ↥Bs)) = (a.1 : Additive ↥Bs)
      from rfl]
  invFun gg := by
    have hgBs : (gg : G) ∈ Bs := (Subgroup.zpowers_le.mpr hyBs) gg.2
    have hfixy : φ (⟨(gg : G), hgBs⟩ : ↥Bs) = ⟨(gg : G), hgBs⟩ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp gg.2
      have hgb : (⟨(gg : G), hgBs⟩ : ↥Bs) = (⟨y, hyBs⟩ : ↥Bs) ^ k := by
        ext
        simpa [hk]
      rw [hgb, map_zpow, hφy]
    let x : ↥(kRefl_Fx φ) :=
      ⟨Additive.ofMul (⟨(gg : G), hgBs⟩ : ↥Bs), by
        change φ (⟨(gg : G), hgBs⟩ : ↥Bs) = (⟨(gg : G), hgBs⟩ : ↥Bs)
        exact hfixy⟩
    refine ⟨x, ?_⟩
    change κ (Additive.ofMul (⟨(gg : G), hgBs⟩ : ↥Bs)) = 0
    exact (hκ0 (⟨(gg : G), hgBs⟩ : ↥Bs)).mpr gg.2
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv gg := by
    apply Subtype.ext
    rfl

private theorem card_fixH {Bs X : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) {κ : Additive ↥Bs →+ Vec6} (hκ : GGE6DepKFrame Bs X y κ)
    (hcardBs : Nat.card Bs = 3 ^ 6) {φ : MulAut ↥Bs} (hφ : GGIsReflection 3 φ)
    (hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩) {g : Mat6}
    (hfix : ∀ b : ↥Bs,
      g.mulVec (κ (Additive.ofMul b)) = κ (Additive.ofMul b) ↔ φ b = b) :
    Nat.card {v : Vec6 // v 5 = 0 ∧ g.mulVec v = v} = 3 ^ 4 := by
  have hcardFx : Nat.card (kRefl_Fx φ) = 3 ^ 5 := by
    have hc : Nat.card {b : ↥Bs // φ b = b} = 3 ^ 5 := by
      have h : Nat.card {b : ↥Bs // φ b = b} * 3 = 3 ^ 5 * 3 := by
        rw [hφ.2, hcardBs]
        norm_num
      exact Nat.mul_right_cancel (show 0 < 3 by norm_num) h
    rwa [Nat.card_congr (kRefl_fxEquiv φ)]
  have hker : Nat.card (kRefl_f κ φ).ker = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [Nat.card_congr (kRefl_kerEquiv hyBs hκ.1 hφy), Nat.card_zpowers]
    exact orderOf_eq_prime hy3 hy1
  have hcardRange : Nat.card (kRefl_f κ φ).range = 3 ^ 4 := by
    have hcr := AddSubgroup.card_ker_mul_card_range (kRefl_f κ φ)
    rw [hker, hcardFx] at hcr
    have h : Nat.card (kRefl_f κ φ).range * 3 = 3 ^ 4 * 3 := by
      rw [mul_comm (Nat.card (kRefl_f κ φ).range) 3, hcr]
      norm_num
    exact Nat.mul_right_cancel (show 0 < 3 by norm_num) h
  have hsub : Nat.card {v : Vec6 // v 5 = 0 ∧ g.mulVec v = v} =
      Nat.card (kRefl_f κ φ).range := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro v
    constructor
    · rintro ⟨hv5, hgv⟩
      obtain ⟨b, hb⟩ := hκ.2.2.1 v hv5
      have hφb : φ b = b := (hfix b).mp (by rw [hb]; exact hgv)
      have hbFx : Additive.ofMul b ∈ kRefl_Fx φ := by
        change φ b = b
        exact hφb
      refine ⟨⟨Additive.ofMul b, hbFx⟩, ?_⟩
      change κ (Additive.ofMul b) = v
      exact hb
    · intro hv
      obtain ⟨a, ha⟩ := hv
      have hb5 : v 5 = 0 := by
        rw [← ha]
        exact hκ.2.1 (Additive.toMul (a.1 : Additive ↥Bs))
      have hbφ : φ (Additive.toMul (a.1 : Additive ↥Bs)) =
          Additive.toMul (a.1 : Additive ↥Bs) := a.2
      have hgv : g.mulVec v = v := by
        rw [← ha]
        exact (hfix (Additive.toMul (a.1 : Additive ↥Bs))).mpr hbφ
      exact ⟨hb5, hgv⟩
  rw [hsub, hcardRange]

private theorem card_fix_total {g : Mat6} (hg : g ∈ closureL)
    (h4 : Nat.card {v : Vec6 // v 5 = 0 ∧ g.mulVec v = v} = 3 ^ 4) :
    Fintype.card {v : Vec6 // g.mulVec v = v} * 3 = 3 ^ 6 := by
  let e : {v : Vec6 // g.mulVec v = v} ≃ {h : Vec6 // h 5 = 0 ∧ g.mulVec h = h} × ZMod 3 :=
    { toFun := fun v =>
        (⟨hpart v.1, kRefl_hpart_five v.1, by
            rw [kRefl_hpart_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, v.2,
              closureL_mulVec_xx hg]⟩,
          v.1 5)
      invFun := fun hc =>
        ⟨hc.1.1 + hc.2 • xx, by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, hc.1.2.2, closureL_mulVec_xx hg]⟩
      left_inv := fun v => Subtype.ext (kRefl_decomp v.1).symm
      right_inv := fun hc =>
        Prod.ext (Subtype.ext (kRefl_hpart_add_smul_xx_of hc.1.1 hc.1.2.1 hc.2))
          (kRefl_add_smul_xx_five_zero hc.1.1 hc.1.2.1 hc.2) }
  have hcard : Nat.card {v : Vec6 // g.mulVec v = v} = 3 ^ 4 * 3 := by
    rw [Nat.card_congr e, Nat.card_prod, h4, Nat.card_zmod]
  rw [← Nat.card_eq_fintype_card, hcard]
  decide

theorem ggE6Dep_frameK_refl {Bs X : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) (hcardBs : Nat.card Bs = 3 ^ 6) {κ : Additive ↥Bs →+ Vec6}
    (hκ : GGE6DepKFrame Bs X y κ) {φ : MulAut ↥Bs} (hφ : GGIsReflection 3 φ)
    (hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩) {g : Mat6} (hg : g ∈ closureL) (hact : ActsAsK κ φ g) :
    g ∈ refl36 :=
  eq_refl36_of_isRefl hg (mul_self_eq_one hg (frameK_sq hκ hφ.1 hact))
    (card_fix_total hg (card_fixH hyBs hy1 hy3 hκ hcardBs hφ hφy
      (frameK_fix_iff hyBs hy3 hκ hφ.1 hφy hact)))

end E6Dep

end CFSG.StandardType

end
