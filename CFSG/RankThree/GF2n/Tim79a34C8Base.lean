module

public import CFSG.RankThree.GF2n.Tim79a34C8Model
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GF2n.Tim79a34Hauptsatz

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa IsExtraspecial2 HasWidth)
open scoped commutatorElement Matrix

section C8Base

variable {G : Type} [Group G] {V H : Subgroup G} {n : ℕ}

@[expose] def c8W (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (u : Fin n ⊕ Fin n → GaloisField 2 1) : G :=
  ((Additive.toMul (ψ u) : ↥(wOf V H)) : G)

theorem c8W_add (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (x y : Fin n ⊕ Fin n → GaloisField 2 1) : c8W ψ (x + y) = c8W ψ x * c8W ψ y := by
  unfold c8W
  rw [map_add]
  rfl

theorem c8W_zero (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)) :
    c8W ψ 0 = 1 := by
  unfold c8W
  rw [map_zero]
  rfl

theorem c8W_mem (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (u : Fin n ⊕ Fin n → GaloisField 2 1) : c8W ψ u ∈ wOf V H :=
  (Additive.toMul (ψ u)).2

theorem c8W_inj (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    {x y : Fin n ⊕ Fin n → GaloisField 2 1} (h : c8W ψ x = c8W ψ y) : x = y :=
  ψ.injective (Additive.toMul.injective (Subtype.ext h))

theorem c8W_surj (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)) {w : G}
    (hw : w ∈ wOf V H) : ∃ u, c8W ψ u = w :=
  ⟨ψ.symm (Additive.ofMul ⟨w, hw⟩), by unfold c8W; rw [AddEquiv.apply_symm_apply]; rfl⟩

theorem c8W_comm (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (x y : Fin n ⊕ Fin n → GaloisField 2 1) : c8W ψ x * c8W ψ y = c8W ψ y * c8W ψ x := by
  rw [← c8W_add, ← c8W_add, add_comm]

theorem c8W_sq (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (x : Fin n ⊕ Fin n → GaloisField 2 1) : c8W ψ x * c8W ψ x = 1 := by
  rw [← c8W_add, vec_add_self, c8W_zero]

theorem c8W_inv (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (x : Fin n ⊕ Fin n → GaloisField 2 1) : (c8W ψ x)⁻¹ = c8W ψ x :=
  inv_eq_of_mul_eq_one_right (c8W_sq ψ x)

end C8Base

section C8Cfg

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

@[expose] noncomputable def c8E (cfg : QPCfg M V Q P H Φ ψ a T) (p : G) :
    ↥(StatedSp n (GaloisField 2 1)) :=
  haveI := Classical.propDecidable (p ∈ xOf V H)
  if hp : p ∈ xOf V H then Φ.symm (xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hp⟩) else 1

theorem c8E_of_mem (cfg : QPCfg M V Q P H Φ ψ a T) {p : G} (hp : p ∈ xOf V H) :
    c8E cfg p = Φ.symm (xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hp⟩) := by
  unfold c8E
  exact dif_pos hp

theorem c8E_mul (cfg : QPCfg M V Q P H Φ ψ a T) {p q : G} (hp : p ∈ xOf V H)
    (hq : q ∈ xOf V H) : c8E cfg (p * q) = c8E cfg p * c8E cfg q := by
  have hpq : p * q ∈ xOf V H := (xOf V H).mul_mem hp hq
  rw [c8E_of_mem cfg hpq, c8E_of_mem cfg hp, c8E_of_mem cfg hq, ← map_mul, ← map_mul]
  rfl

theorem c8E_one (cfg : QPCfg M V Q P H Φ ψ a T) : c8E cfg 1 = 1 := by
  rw [c8E_of_mem cfg (xOf V H).one_mem]
  have : (⟨1, (xOf V H).one_mem⟩ : ↥(xOf V H)) = 1 := rfl
  rw [this, map_one, map_one]

theorem c8E_inv (cfg : QPCfg M V Q P H Φ ψ a T) {p : G} (hp : p ∈ xOf V H) :
    c8E cfg p⁻¹ = (c8E cfg p)⁻¹ := by
  have hpi : p⁻¹ ∈ xOf V H := (xOf V H).inv_mem hp
  have h := c8E_mul cfg hpi hp
  rw [inv_mul_cancel, c8E_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem c8E_conj (cfg : QPCfg M V Q P H Φ ψ a T) {p : G} (hp : p ∈ xOf V H)
    (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    p * c8W ψ v * p⁻¹ = c8W ψ (SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *ᵥ v) := by
  rw [c8E_of_mem cfg hp]
  exact (cfg.nat.equiv ⟨p, hp⟩ v).symm

theorem c8E_eq_one_iff (cfg : QPCfg M V Q P H Φ ψ a T) {p : G} (hp : p ∈ xOf V H) :
    c8E cfg p = 1 ↔ p ∈ wOf V H := by
  rw [c8E_of_mem cfg hp]
  constructor
  · intro h
    have h1 : xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hp⟩ = 1 := by
      have h2 := Φ.apply_symm_apply (xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hp⟩)
      rw [h, map_one] at h2
      exact h2.symm
    have h3 : piBar V H (Subgroup.inclusion (xOf_le_H cfg.hyp.setup.mc.toMinCex.V_le_H)
        ⟨p, hp⟩) = 1 := by
      rw [← coe_xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hp⟩, h1, Subgroup.coe_one]
    exact (piBar_eq_one_iff _).mp h3
  · intro h
    have h3 : piBar V H (Subgroup.inclusion (xOf_le_H cfg.hyp.setup.mc.toMinCex.V_le_H)
        ⟨p, hp⟩) = 1 := (piBar_eq_one_iff _).mpr h
    have h1 : xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hp⟩ = 1 := by
      apply Subtype.ext
      rw [coe_xToXbar, h3, Subgroup.coe_one]
    rw [h1, map_one]

theorem c8E_surj (cfg : QPCfg M V Q P H Φ ψ a T) (g : ↥(StatedSp n (GaloisField 2 1))) :
    ∃ x ∈ xOf V H, c8E cfg x = g := by
  obtain ⟨x, hx⟩ := xToXbar_surjective cfg.hyp.setup.mc.toMinCex.V_le_H (Φ g)
  refine ⟨(x : G), x.2, ?_⟩
  rw [c8E_of_mem cfg x.2]
  have : (⟨(x : G), x.2⟩ : ↥(xOf V H)) = x := rfl
  rw [this, hx, MulEquiv.symm_apply_apply]

theorem c8_h11a (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T) :
    (∀ w, c8W ψ w ∈ P ↔ CaseM.spForm a w = 0) ∧
      Rbar V H P = (spRad a).map Φ.toMonoidHom ∧ xOf V H = H ∧ Nat.card ↥P = 2 ^ (4 * n - 2) :=
  h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point

theorem c8_P_le_X (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T) :
    P ≤ xOf V H := by
  rw [(c8_h11a h11a cfg).2.2.1]
  exact cfg.hyp.setup.mc.toMinCex.PleH

theorem c8_Q_eq_P (cfg : QPCfg M V Q P H Φ ψ a T) : Q = P :=
  le_antisymm cfg.qp cfg.hyp.setup.mc.toMinCex.P_le_Q

theorem c8E_mem_spRad (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T) {p : G}
    (hp : p ∈ P) : c8E cfg p ∈ spRad a := by
  have hpX : p ∈ xOf V H := c8_P_le_X h11a cfg hp
  have hmem : xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hpX⟩ ∈ Rbar V H P :=
    mem_Rbar.mpr (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H cfg.hyp.setup.mc.toMinCex.V_le_H)
      ⟨p, hpX⟩, hp, rfl⟩)
  rw [(c8_h11a h11a cfg).2.1] at hmem
  rw [c8E_of_mem cfg hpX]
  exact Subgroup.mem_map_equiv.mp hmem

theorem c8E_fix_a (cfg : QPCfg M V Q P H Φ ψ a T) {x : G} (hx : x ∈ xOf V H)
    (hxa : x * c8W ψ a = c8W ψ a * x) :
    SpExtras.mat n (GaloisField 2 1) (c8E cfg x) *ᵥ a = a := by
  have h := c8E_conj cfg hx a
  rw [hxa, mul_inv_cancel_right] at h
  exact (c8W_inj ψ h).symm

@[expose] noncomputable def c8Kvec (cfg : QPCfg M V Q P H Φ ψ a T)
    (b : Fin n ⊕ Fin n → GaloisField 2 1) (p : G) : Fin n ⊕ Fin n → GaloisField 2 1 :=
  SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *ᵥ b + b

theorem c8_comm_bG (cfg : QPCfg M V Q P H Φ ψ a T) (b : Fin n ⊕ Fin n → GaloisField 2 1)
    {p : G} (hp : p ∈ xOf V H) : ⁅p, c8W ψ b⁆ = c8W ψ (c8Kvec cfg b p) := by
  rw [commutatorElement_def, c8E_conj cfg hp]
  unfold c8Kvec
  rw [c8W_add, c8W_inv]

theorem c8Kvec_perp (cfg : QPCfg M V Q P H Φ ψ a T) {b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hb : CaseM.spForm a b = 1) {p : G}
    (hga : SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *ᵥ a = a) :
    CaseM.spForm a (c8Kvec cfg b p) = 0 := by
  unfold c8Kvec
  have h := spForm_mat_mulVec (c8E cfg p) a b
  rw [hga, hb] at h
  rw [spForm_add_right, h, hb]
  exact CharTwo.add_self_eq_zero _

theorem c8Kvec_mul (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {p q : G}
    (hp : p ∈ P) (hq : q ∈ P) :
    ∃ c : GaloisField 2 1, c8Kvec cfg b (p * q) = c8Kvec cfg b p + c8Kvec cfg b q + c • a := by
  have hpX := c8_P_le_X h11a cfg hp
  have hqX := c8_P_le_X h11a cfg hq
  have hgp := c8E_mem_spRad h11a cfg hp
  have hgq := c8E_mem_spRad h11a cfg hq
  have hkq := c8Kvec_perp cfg hb hgq.1
  obtain ⟨c, hc⟩ := hgp.2 _ hkq
  refine ⟨c, ?_⟩
  unfold c8Kvec at hc ⊢
  rw [c8E_mul cfg hpX hqX, map_mul, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_add] at hc
  have h2 := two_smul_vec_eq_zero
    (SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *ᵥ b)
  linear_combination (norm := module) hc + (-1 : GaloisField 2 1) • h2

theorem c8Kvec_conj (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {s p : G}
    (hs : s ∈ xOf V H) (hsa : SpExtras.mat n (GaloisField 2 1) (c8E cfg s) *ᵥ a = a)
    (hp : p ∈ P) :
    ∃ c : GaloisField 2 1, c8Kvec cfg b (s * p * s⁻¹) =
      SpExtras.mat n (GaloisField 2 1) (c8E cfg s) *ᵥ c8Kvec cfg b p + c • a := by
  have hpX := c8_P_le_X h11a cfg hp
  have hgp := c8E_mem_spRad h11a cfg hp
  have hsi : s⁻¹ ∈ xOf V H := (xOf V H).inv_mem hs
  have hspX : s * p ∈ xOf V H := (xOf V H).mul_mem hs hpX
  have hsia : SpExtras.mat n (GaloisField 2 1) (c8E cfg s)⁻¹ *ᵥ a = a := by
    have := mat_inv_mulVec_mat_mulVec (c8E cfg s) a
    rwa [hsa] at this
  have hz : CaseM.spForm a (SpExtras.mat n (GaloisField 2 1) (c8E cfg s)⁻¹ *ᵥ b + b) = 0 := by
    have h := spForm_mat_mulVec (c8E cfg s)⁻¹ a b
    rw [hsia, hb] at h
    rw [spForm_add_right, h, hb]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨c, hc⟩ := hgp.2 _ hz
  have hgsgsi : SpExtras.mat n (GaloisField 2 1) (c8E cfg s) *ᵥ
      (SpExtras.mat n (GaloisField 2 1) (c8E cfg s)⁻¹ *ᵥ b) = b :=
    mat_mulVec_mat_inv_mulVec (c8E cfg s) b
  have hmat : SpExtras.mat n (GaloisField 2 1) (c8E cfg (s * p * s⁻¹)) =
      SpExtras.mat n (GaloisField 2 1) (c8E cfg s) * SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *
        SpExtras.mat n (GaloisField 2 1) (c8E cfg s)⁻¹ := by
    rw [c8E_mul cfg hspX hsi, c8E_mul cfg hs hpX, map_mul, map_mul, c8E_inv cfg hs]
  refine ⟨c, ?_⟩
  unfold c8Kvec
  rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_add] at hc
  have hE : SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *ᵥ
      (SpExtras.mat n (GaloisField 2 1) (c8E cfg s)⁻¹ *ᵥ b) =
      SpExtras.mat n (GaloisField 2 1) (c8E cfg s)⁻¹ *ᵥ b + b + c • a +
        SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *ᵥ b := by
    linear_combination (norm := module) hc +
      (-1 : GaloisField 2 1) • two_smul_vec_eq_zero
        (SpExtras.mat n (GaloisField 2 1) (c8E cfg p) *ᵥ b)
  rw [hE, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, hgsgsi,
    hsa, Matrix.mulVec_add]
  linear_combination (norm := module) (1 : GaloisField 2 1) • two_smul_vec_eq_zero b

theorem c8_mem_VF (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {y : G} (hy : y ∈ P)
    (h : ∃ c : GaloisField 2 1, c8Kvec cfg b y = c • a) :
    ∃ v ∈ V, ∃ f ∈ P ⊓ wOf V H, y = v * f := by
  have hVH := cfg.hyp.setup.mc.toMinCex.V_le_H
  have hyX := c8_P_le_X h11a cfg hy
  have hg := c8E_mem_spRad h11a cfg hy
  obtain ⟨c, hc⟩ := h
  have hmat : SpExtras.mat n (GaloisField 2 1) (c8E cfg y) *ᵥ b = b + c • a := by
    unfold c8Kvec at hc
    have h2 := two_smul_vec_eq_zero b
    linear_combination (norm := module) hc + (-1 : GaloisField 2 1) • h2
  have hgT : c8E cfg y ∈ T :=
    c8_mem_trans_of_apply cfg.ne hb hg cfg.trans ⟨c, hmat⟩
  have hmem : xToXbar hVH ⟨y, hyX⟩ ∈ Vy V H := by
    have h1 := Subgroup.mem_map_of_mem Φ.toMonoidHom hgT
    rw [cfg.point] at h1
    rw [c8E_of_mem cfg hyX] at h1
    simpa using h1
  have hmem2 := Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨x, hxV, hxy⟩ := mem_barOf_iff.mp hmem2
  have hxy' : piBar V H x = piBar V H (Subgroup.inclusion (xOf_le_H hVH) ⟨y, hyX⟩) := by
    rw [hxy, coe_xToXbar]
  have hW : (x : G)⁻¹ * y ∈ wOf V H := by
    have h3 := QuotientGroup.eq.mp hxy'
    exact Subgroup.mem_subgroupOf.mp h3
  refine ⟨(x : G), hxV, (x : G)⁻¹ * y, Subgroup.mem_inf.mpr ⟨?_, hW⟩, ?_⟩
  · exact P.mul_mem (P.inv_mem (cfg.hyp.setup.mc.toMinCex.V_le_P hxV)) hy
  · rw [mul_inv_cancel_left]

theorem c8E_comm (cfg : QPCfg M V Q P H Φ ψ a T) {x y : G} (hx : x ∈ xOf V H)
    (hy : y ∈ xOf V H) : c8E cfg ⁅x, y⁆ = ⁅c8E cfg x, c8E cfg y⁆ := by
  have hxi : x⁻¹ ∈ xOf V H := (xOf V H).inv_mem hx
  have hyi : y⁻¹ ∈ xOf V H := (xOf V H).inv_mem hy
  rw [commutatorElement_def, commutatorElement_def,
    c8E_mul cfg ((xOf V H).mul_mem ((xOf V H).mul_mem hx hy) hxi) hyi,
    c8E_mul cfg ((xOf V H).mul_mem hx hy) hxi, c8E_mul cfg hx hy, c8E_inv cfg hx,
    c8E_inv cfg hy]

theorem c8Kvec_one (cfg : QPCfg M V Q P H Φ ψ a T) (b : Fin n ⊕ Fin n → GaloisField 2 1) :
    c8Kvec cfg b 1 = 0 := by
  unfold c8Kvec
  rw [c8E_one, map_one, Matrix.one_mulVec]
  exact vec_add_self b

theorem c8Kvec_W (cfg : QPCfg M V Q P H Φ ψ a T) (b : Fin n ⊕ Fin n → GaloisField 2 1) {f : G}
    (hf : f ∈ wOf V H) : c8Kvec cfg b f = 0 := by
  have hfX : f ∈ xOf V H := wOf_le_xOf V H hf
  unfold c8Kvec
  rw [(c8E_eq_one_iff cfg hfX).mpr hf, map_one, Matrix.one_mulVec]
  exact vec_add_self b

theorem c8Kvec_V (cfg : QPCfg M V Q P H Φ ψ a T) {b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hb : CaseM.spForm a b = 1) {v : G} (hv : v ∈ V) : ∃ c : GaloisField 2 1,
      c8Kvec cfg b v = c • a := by
  have hVH := cfg.hyp.setup.mc.toMinCex.V_le_H
  have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hv
  have hxmem : xToXbar hVH ⟨v, hvX⟩ ∈ Vy V H :=
    Subgroup.mem_subgroupOf.mpr
      (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩, hv, rfl⟩)
  have hmemT : xToXbar hVH ⟨v, hvX⟩ ∈ T.map Φ.toMonoidHom := by
    rw [cfg.point]
    exact hxmem
  have ht : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ∈ T := Subgroup.mem_map_equiv.mp hmemT
  rw [← c8E_of_mem cfg hvX] at ht
  obtain ⟨c, hc⟩ := (cfg.trans.1 _).1 ht
  refine ⟨c, ?_⟩
  unfold c8Kvec
  rw [hc, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, hb, mul_one]
  have h2 := two_smul_vec_eq_zero b
  linear_combination (norm := module) (1 : GaloisField 2 1) • h2

@[expose] noncomputable def c8R (cfg : QPCfg M V Q P H Φ ψ a T)
    (b : Fin n ⊕ Fin n → GaloisField 2 1) (ρ p : G) : Fin n ⊕ Fin n → GaloisField 2 1 :=
  c8Kvec cfg b (ρ * p * ρ⁻¹)

theorem c8R_perp (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {ρ p : G}
    (hρp : ρ * p * ρ⁻¹ ∈ P) : CaseM.spForm a (c8R cfg b ρ p) = 0 :=
  c8Kvec_perp cfg hb (c8E_mem_spRad h11a cfg hρp).1

theorem c8R_mul (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {ρ p q : G}
    (hρp : ρ * p * ρ⁻¹ ∈ P) (hρq : ρ * q * ρ⁻¹ ∈ P) :
    C8Cong a (c8R cfg b ρ (p * q)) (c8R cfg b ρ p + c8R cfg b ρ q) := by
  obtain ⟨c, hc⟩ := c8Kvec_mul h11a cfg hb hρp hρq
  refine ⟨c, ?_⟩
  unfold c8R
  rw [show ρ * (p * q) * ρ⁻¹ = (ρ * p * ρ⁻¹) * (ρ * q * ρ⁻¹) by group]
  exact hc

theorem c8R_conj (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {ρ r p : G}
    (hρp : ρ * p * ρ⁻¹ ∈ P) (hrX : r ∈ xOf V H)
    (hra : SpExtras.mat n (GaloisField 2 1) (c8E cfg r) *ᵥ a = a)
    (hrP : ∀ y ∈ P, r * y * r⁻¹ ∈ P) (hq : ρ * r * ρ⁻¹ * r⁻¹ ∈ P) :
    C8Cong a (c8R cfg b ρ (r * p * r⁻¹))
      (SpExtras.mat n (GaloisField 2 1) (c8E cfg r) *ᵥ c8R cfg b ρ p) := by
  set q₁ := ρ * r * ρ⁻¹ * r⁻¹ with hq₁
  have hq₁X : q₁ ∈ xOf V H := c8_P_le_X h11a cfg hq
  have hq₁sp := c8E_mem_spRad h11a cfg hq
  have hw : r * (ρ * p * ρ⁻¹) * r⁻¹ ∈ P := hrP _ hρp
  have hident : ρ * (r * p * r⁻¹) * ρ⁻¹ = q₁ * (r * (ρ * p * ρ⁻¹) * r⁻¹) * q₁⁻¹ := by
    rw [hq₁]
    group
  obtain ⟨c₁, hc₁⟩ := c8Kvec_conj h11a cfg hb hq₁X hq₁sp.1 hw
  obtain ⟨c₂, hc₂⟩ := c8Kvec_conj h11a cfg hb hrX hra hρp
  have hperp : CaseM.spForm a (c8Kvec cfg b (r * (ρ * p * ρ⁻¹) * r⁻¹)) = 0 :=
    c8Kvec_perp cfg hb (c8E_mem_spRad h11a cfg hw).1
  obtain ⟨c₃, hc₃⟩ := hq₁sp.2 _ hperp
  refine ⟨c₁ + c₃ + c₂, ?_⟩
  unfold c8R
  rw [hident, hc₁, hc₃, hc₂, add_smul, add_smul]
  abel

theorem c8_exists_gamma (cfg : QPCfg M V Q P H Φ ψ a T) {x y : Fin n ⊕ Fin n → GaloisField 2 1}
    (hax : CaseM.spForm a x = 0) (hay : CaseM.spForm a y = 0) (hxy : CaseM.spForm x y = 1) :
    ∃ x₁ ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ∃ x₂ ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      SpExtras.mat n (GaloisField 2 1) (c8E cfg ⁅x₁, x₂⁆) =
        CaseM.spTrans x 1 * CaseM.spTrans y 1 := by
  obtain ⟨g₁, g₂, hg₁, hg₂, hg₁a, hg₂a, hcomm⟩ := c8_commutator_lift hax hay hxy
  obtain ⟨x₁, hx₁X, hx₁⟩ := c8E_surj cfg g₁
  obtain ⟨x₂, hx₂X, hx₂⟩ := c8E_surj cfg g₂
  have hcent : ∀ {z : G} {g : ↥(StatedSp n (GaloisField 2 1))}, z ∈ xOf V H → c8E cfg z = g →
      SpExtras.mat n (GaloisField 2 1) g *ᵥ a = a →
      z ∈ Subgroup.centralizer ({c8W ψ a} : Set G) := by
    intro z g hz hzg hga
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    have h := c8E_conj cfg hz a
    rw [hzg, hga] at h
    calc c8W ψ a * z = (z * c8W ψ a * z⁻¹) * z := by rw [h]
      _ = z * c8W ψ a := by group
  refine ⟨x₁, Subgroup.mem_inf.mpr ⟨hx₁X, hcent hx₁X hx₁ hg₁a⟩, x₂,
    Subgroup.mem_inf.mpr ⟨hx₂X, hcent hx₂X hx₂ hg₂a⟩, ?_⟩
  rw [c8E_comm cfg hx₁X hx₂X, hx₁, hx₂]
  exact hcomm

theorem c8_cent_normalizes (h12 : Lemma12Statement) (cfg : QPCfg M V Q P H Φ ψ a T) :
    ∀ x ∈ Subgroup.centralizer ({c8W ψ a} : Set G), ∀ y ∈ P, x * y * x⁻¹ ∈ P := by
  intro x hx y hy
  have hM : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H cfg.hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hxM : x ∈ M := by
    rw [← hM]
    exact hx
  exact (Subgroup.mem_normalizer_iff.mp (cfg.hyp.setup.mc.toMinCex.M_le_normalizer_P hxM) y).mp hy

theorem c8_comm_normalizes {K P' : Subgroup G} (hK : ∀ x ∈ K, ∀ y ∈ P', x * y * x⁻¹ ∈ P')
    {x₁ x₂ : G} (h₁ : x₁ ∈ K) (h₂ : x₂ ∈ K) : ∀ y ∈ P', ⁅x₁, x₂⁆ * y * ⁅x₁, x₂⁆⁻¹ ∈ P' := by
  intro y hy
  have e : ⁅x₁, x₂⁆ * y * ⁅x₁, x₂⁆⁻¹ =
      x₁ * (x₂ * (x₁⁻¹ * (x₂⁻¹ * y * x₂⁻¹⁻¹) * x₁⁻¹⁻¹) * x₂⁻¹) * x₁⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hK x₁ h₁ _ (hK x₂ h₂ _ (hK x₁⁻¹ (K.inv_mem h₁) _ (hK x₂⁻¹ (K.inv_mem h₂) _ hy)))

theorem c8_card_two : Nat.card (GaloisField 2 1) = 2 := by
  rw [GaloisField.card 2 1 one_ne_zero, pow_one]

end C8Cfg

end CFSG.RankThree.GF2n.Tim79a
