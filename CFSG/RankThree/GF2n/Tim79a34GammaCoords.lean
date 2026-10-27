module

public import CFSG.RankThree.GF2n.Tim79a34Lemma12
public import CFSG.RankThree.GF2n.Tim79a34Lemma11b
public import CFSG.RankThree.GF2n.Tim79a34OddCore
public import CFSG.RankThree.GF2n.Tim79a34CXW
public import CFSG.RankThree.GF2n.Tim79a34GammaGroup
public import CFSG.RankThree.GF2n.Tim79a34GammaSp
public import CFSG.RankThree.GF2n.Tim79a34NatMod

public section

namespace CFSG.RankThree.GF2n.Tim79a.Gamma

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
  CFSG.RankThree.GF2n.Tim79a
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}

theorem exists_param_of_mem_P (h11a : Lemma11aStatement) (hH : TwoEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (hcP : cPbar V H P ≤ wOf V H) {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    (hNat : NatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ)
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {p : G} (hp : p ∈ P) :
    ∃ u, CaseM.spForm a u = 0 ∧ ∃ c : GaloisField 2 1, ∀ v,
      p * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * p⁻¹ =
        ((Additive.toMul (ψ (v + CaseM.spForm a v • u + CaseM.spForm u v • a +
          (c * CaseM.spForm a v) • a)) : ↥(wOf V H)) : G) := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨-, hRbar, hxOf, -⟩ := h11a G M V Q P H hH hZ hcP Φ ψ hNat a T ha hT hTV
  have hpX : p ∈ xOf V H := by rw [hxOf]; exact hc.PleH hp
  set x : ↥(xOf V H) := ⟨p, hpX⟩ with hx
  have hxR : xToXbar hVH x ∈ Rbar V H P := by
    rw [mem_Rbar, coe_xToXbar]
    exact mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) x, hp, rfl⟩
  rw [hRbar] at hxR
  obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp hxR
  have hgΦ : Φ.symm (xToXbar hVH x) = g := by
    rw [← hgx]
    exact Φ.symm_apply_apply g
  obtain ⟨u, hu, c, hgu⟩ := exists_spRad_param ha hg
  refine ⟨u, hu, c, fun v => ?_⟩
  have key := hNat.equiv x v
  rw [hgΦ, hgu v] at key
  exact key.symm

structure GCfg (M V Q P H : Subgroup G) {n : ℕ}
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (a : Fin n ⊕ Fin n → GaloisField 2 1) (T : Subgroup ↥(StatedSp n (GaloisField 2 1))) :
    Prop where
  hyp : TwoEndHyp M V Q P H
  centre : Subgroup.center (Xbar V H) = ⊥
  iw : cPbar V H P ≤ wOf V H
  nat : NatCfg V H hyp.setup.mc.toMinCex.V_le_H Φ ψ
  ne : a ≠ 0
  trans : CaseM.IsTransGroup a T
  point : T.map Φ.toMonoidHom = Vy V H
  two_le : 2 ≤ n

section Cfg

variable {n : ℕ} {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

omit [Finite G] in
theorem psi_mul (u v : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ (u + v)) : ↥(wOf V H)) : G) :=
  lemma11b_psi_mul ψ u v

theorem psi_inv (u : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ u) : ↥(wOf V H)) : G)⁻¹ = ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) :=
  inv_eq_of_mul_eq_one_right (qpCfg_psi_mul_self (ψ := ψ) u)

omit [Finite G] in
theorem psi_injective {u v : Fin n ⊕ Fin n → GaloisField 2 1}
    (h : ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) = ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)) :
    u = v :=
  ψ.injective (Additive.toMul.injective (Subtype.ext h))

omit [Finite G] in
theorem psi_zero : ((Additive.toMul (ψ 0) : ↥(wOf V H)) : G) = 1 := by
  simp

omit [Finite G] in
theorem gf2_add_self (x : GaloisField 2 1) : x + x = 0 := CharTwo.add_self_eq_zero x

omit [Finite G] in
theorem gf2_vec_add_self (x : Fin n ⊕ Fin n → GaloisField 2 1) : x + x = 0 := by
  funext i
  exact gf2_add_self (x i)

theorem comm_psi_eq (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {p : G} (hp : p ∈ P) :
    ∃ g ∈ spRad a, ∃ hpX : p ∈ xOf V H,
      Φ.symm (xToXbar cfg.hyp.setup.mc.toMinCex.V_le_H ⟨p, hpX⟩) = g ∧
      ∃ u, CaseM.spForm a u = 0 ∧ ∃ c : GaloisField 2 1,
        (∀ x, SpExtras.mat n (GaloisField 2 1) g *ᵥ x =
          x + CaseM.spForm a x • u + CaseM.spForm u x • a + (c * CaseM.spForm a x) • a) ∧
        ⁅p, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ =
          ((Additive.toMul (ψ (u + (CaseM.spForm u b + c) • a)) : ↥(wOf V H)) : G) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨-, hRbar, hxOf, -⟩ :=
    h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  have hpX : p ∈ xOf V H := by rw [hxOf]; exact hc.PleH hp
  have hxR : xToXbar hVH ⟨p, hpX⟩ ∈ Rbar V H P := by
    rw [mem_Rbar, coe_xToXbar]
    exact mem_barOf_iff.mpr ⟨⟨p, hc.PleH hp⟩, hp, rfl⟩
  rw [hRbar] at hxR
  obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp hxR
  have hgΦ : Φ.symm (xToXbar hVH ⟨p, hpX⟩) = g := by
    rw [← hgx]
    exact Φ.symm_apply_apply g
  obtain ⟨u, hu, c, hgu⟩ := exists_spRad_param cfg.ne hg
  refine ⟨g, hg, hpX, hgΦ, u, hu, c, hgu, ?_⟩
  have key := cfg.nat.equiv ⟨p, hpX⟩ b
  rw [hgΦ, hgu b, hb] at key
  rw [commutatorElement_def, ← key, psi_inv, psi_mul]
  congr 3
  have e : b + (1 : GaloisField 2 1) • u + CaseM.spForm u b • a + (c * 1) • a + b =
      u + (CaseM.spForm u b + c) • a + (b + b) := by
    rw [one_smul, mul_one, add_smul]
    abel
  rw [e, gf2_vec_add_self, add_zero]

theorem mem_W_of_comm_psi_eq_one (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {p : G} (hp : p ∈ P)
    (h : ⁅p, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ = 1) : p ∈ wOf V H := by
  have hVH : V ≤ H := cfg.hyp.setup.mc.toMinCex.V_le_H
  obtain ⟨g, -, hpX, hgΦ, u, hu, c, hgu, hcomm⟩ := comm_psi_eq h11a cfg hb hp
  rw [h, ← psi_zero (ψ := ψ)] at hcomm
  have h0 := (psi_injective hcomm).symm
  set μ := CaseM.spForm u b + c with hμ
  have hu' : u = μ • a := by
    calc u = u + (u + μ • a) := by rw [h0, add_zero]
      _ = (u + u) + μ • a := by abel
      _ = μ • a := by rw [gf2_vec_add_self, zero_add]
  have hub : CaseM.spForm u b = μ := by
    rw [hu', CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', hb, mul_one]
  have hc0 : c = 0 := by
    have e : μ = μ + c := by
      calc μ = CaseM.spForm u b + c := hμ
        _ = μ + c := by rw [hub]
    calc c = (μ + μ) + c := by rw [gf2_add_self, zero_add]
      _ = μ + (μ + c) := by abel
      _ = μ + μ := by rw [← e]
      _ = 0 := gf2_add_self μ
  have hg1 : g = 1 := by
    refine CFSG.Timmesfeld.Transvection.ModelRank.eq_of_mat_mulVec_eq fun x => ?_
    rw [hgu x, map_one, Matrix.one_mulVec, hc0, zero_mul, zero_smul, add_zero, hu',
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', smul_smul, add_assoc,
      ← add_smul, mul_comm (CaseM.spForm a x) μ, gf2_add_self, zero_smul, add_zero]
  have hx1 : xToXbar hVH ⟨p, hpX⟩ = 1 := by
    have := congrArg Φ hgΦ
    rw [MulEquiv.apply_symm_apply, hg1, map_one] at this
    exact this
  exact (cxw_xToXbar_eq_one hVH ⟨p, hpX⟩).mp hx1

theorem mul_self_eq_one_of_comm_psi_mem (h11a : Lemma11aStatement)
    (cfg : GCfg M V Q P H Φ ψ a T) {b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hb : CaseM.spForm a b = 1) {p : G} (hp : p ∈ P)
    (h : ⁅p, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ ∈ V ⊓ wOf V H) : p * p = 1 := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨g, -, hpX, hgΦ, u, hu, c, hgu, hcomm⟩ := comm_psi_eq h11a cfg hb hp
  set μ := CaseM.spForm u b + c with hμ
  clear_value μ
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  have haK : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V ⊓ wOf V H :=
    Subgroup.mem_inf.mpr ⟨cfg.nat.point a T cfg.ne cfg.trans cfg.point, (Additive.toMul (ψ a)).2⟩
  have haG1 : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ≠ 1 := by
    intro h1
    apply cfg.ne
    apply psi_injective (ψ := ψ)
    rw [h1, psi_zero]
  obtain ⟨ν, hν⟩ : ∃ ν : GaloisField 2 1, u = ν • a := by
    rw [hcomm] at h
    rcases l12_two_elt hVWcard haK haG1 _ h with h1 | h1
    · rw [← psi_zero (ψ := ψ)] at h1
      have h0 := psi_injective h1
      refine ⟨μ, ?_⟩
      calc u = u + (u + μ • a) := by rw [h0, add_zero]
        _ = (u + u) + μ • a := by abel
        _ = μ • a := by rw [gf2_vec_add_self, zero_add]
    · have h0 := psi_injective h1
      refine ⟨μ + 1, ?_⟩
      calc u = u + (u + μ • a) + a := by rw [h0, add_assoc, gf2_vec_add_self, add_zero]
        _ = (u + u) + (μ • a + a) := by abel
        _ = (μ + 1) • a := by rw [gf2_vec_add_self, zero_add, add_smul, one_smul]
  have hgt : SpExtras.mat n (GaloisField 2 1) g = CaseM.spTrans a c := by
    refine Matrix.ext_iff_mulVec.2 fun x => ?_
    rw [hgu x, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, hν,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', smul_smul,
      mul_comm (CaseM.spForm a x) ν, add_assoc x, gf2_vec_add_self, add_zero]
  have hgT : g ∈ T := (cfg.trans.1 g).mpr ⟨c, hgt⟩
  have hxV : xToXbar hVH ⟨p, hpX⟩ ∈ Vy V H := by
    rw [← cfg.point]
    refine Subgroup.mem_map.mpr ⟨g, hgT, ?_⟩
    rw [← hgΦ]
    exact Φ.apply_symm_apply _
  have hxV' : ((xToXbar hVH ⟨p, hpX⟩ : Xbar V H) : Hbar V H) ∈ barOf V H V :=
    Subgroup.mem_subgroupOf.mp hxV
  obtain ⟨y, hyV, hyp⟩ := mem_barOf_iff.mp hxV'
  rw [coe_xToXbar] at hyp
  have hw : (y : G)⁻¹ * p ∈ wOf V H := by
    have h1 : piBar V H (y⁻¹ * Subgroup.inclusion (xOf_le_H hVH) ⟨p, hpX⟩) = 1 := by
      rw [map_mul, map_inv, hyp, inv_mul_cancel]
    exact (piBar_eq_one_iff _).mp h1
  have hwP : (y : G)⁻¹ * p ∈ P := P.mul_mem (P.inv_mem (hc.V_le_P hyV)) hp
  have hwC : (y : G)⁻¹ * p ∈ Subgroup.centralizer (V : Set G) := by
    rw [hc.hP] at hwP
    exact (Subgroup.mem_inf.mp hwP).2
  have hy2 : (y : G) * (y : G) = 1 := by
    have := hc.elemAb.2 (y : G) hyV
    rwa [pow_two] at this
  have hw2 : ((y : G)⁻¹ * p) * ((y : G)⁻¹ * p) = 1 := by
    have := (MinCex.wOf_isElemAbelian hc).2 _ hw
    rwa [pow_two] at this
  have hcomm' : (y : G) * ((y : G)⁻¹ * p) = ((y : G)⁻¹ * p) * (y : G) :=
    (Subgroup.mem_centralizer_iff.mp hwC (y : G) hyV)
  calc p * p = ((y : G) * ((y : G)⁻¹ * p)) * ((y : G) * ((y : G)⁻¹ * p)) := by group
    _ = ((y : G) * (y : G)) * (((y : G)⁻¹ * p) * ((y : G)⁻¹ * p)) := by
        rw [mul_assoc, ← mul_assoc ((y : G)⁻¹ * p), ← hcomm']; group
    _ = 1 := by rw [hy2, hw2, one_mul]

theorem mul_self_mem_VW (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T) {p : G}
    (hp : p ∈ P) : p * p ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨-, hfr, -⟩ := h11b G M V Q P H cfg.hyp cfg.centre cfg.iw
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hfr]
  refine ⟨⟨p, hp⟩ ^ 2, CFSG.OrderReductions.FrattiniElementary.pow_mem_frattini 2
    hc.isPGroup_P _, ?_⟩
  simp [pow_two]

theorem exists_P_conj_of_comm_mem (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {q : G}
    (hq : ⁅q, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ ∈ P) :
    ∃ r ∈ P, q * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * q⁻¹ =
      r * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * r⁻¹ := by
  have hcov := (h11c G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans
    cfg.point b hb).2
  refine exists_conj_eq_of_comm_mem (A := V ⊓ wOf V H) (E := P ⊓ wOf V H)
    (qpCfg_psi_mul_self (ψ := ψ) b) (fun p hp => mul_self_mem_VW h11b cfg hp)
    (fun p hp h => mul_self_eq_one_of_comm_psi_mem h11a cfg hb hp h)
    (fun p hp h => Subgroup.mem_inf.mpr ⟨hp, mem_W_of_comm_psi_eq_one h11a cfg hb hp h⟩)
    hcov hq

theorem card_V (cfg : GCfg M V Q P H Φ ψ a T) : Nat.card ↥V = 4 := by
  have hH := cfg.hyp
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have h := twb_card_barOf_mul (V := V) (H := H) (K := V) hc.V_le_H
  have e1 : Nat.card ↥(barOf V H V) = 2 := hH.q_two
  have e2 : Nat.card ↥(V ⊓ wOf V H) = 2 := by rw [hH.module]; exact hH.q_two
  rw [e1, e2] at h
  omega

theorem aG_mem_VW (cfg : GCfg M V Q P H Φ ψ a T) :
    ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V ⊓ wOf V H ∧
      ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ≠ 1 := by
  refine ⟨Subgroup.mem_inf.mpr ⟨cfg.nat.point a T cfg.ne cfg.trans cfg.point,
    (Additive.toMul (ψ a)).2⟩, fun h1 => cfg.ne (psi_injective (ψ := ψ) ?_)⟩
  rw [h1, psi_zero]

theorem commute_aG_of_mem_M (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {m : G} (hm : m ∈ M) :
    m * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * m := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨hcomm', -, -⟩ := h11b G M V Q P H cfg.hyp cfg.centre cfg.iw
  have hconjK := l12_conj_comm hc.M_le_normalizer_P
  rw [hcomm'] at hconjK
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have h1 := hconjK m hm _ haK
  rcases l12_two_elt hVWcard haK haG1 _ h1 with h2 | h2
  · exfalso
    apply haG1
    calc ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)
        = m⁻¹ * (m * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * m⁻¹) * m := by group
      _ = 1 := by rw [h2]; group
  · exact mul_inv_eq_iff_eq_mul.mp h2

theorem conj_eq_of_mem_VW (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ V ⊓ wOf V H) : m * x * m⁻¹ = x := by
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  rcases l12_two_elt hVWcard haK haG1 x hx with h | h
  · rw [h, mul_one, mul_inv_cancel]
  · rw [h, commute_aG_of_mem_M h11b cfg hm, mul_inv_cancel_right]

theorem wOf_le_M (cfg : GCfg M V Q P H Φ ψ a T) : wOf V H ≤ M := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  intro w hw
  have hcomm := (MinCex.wOf_isElemAbelian hc).1.is_comm.comm ⟨w, hw⟩ (Additive.toMul (ψ a))
  exact hc.mem_M_of_commute (Subgroup.mem_inf.mp haK).1 haG1
    (congrArg Subtype.val hcomm)

theorem comm_mem_VW_of_mem_M (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {m : G} (hm : m ∈ M) {v : G} (hv : v ∈ V) : ⁅m, v⁆ ∈ V ⊓ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hmV : m * v * m⁻¹ ∈ V := by
    have hN : m ∈ Subgroup.normalizer (V : Set G) := by rw [hc.normalizer_eq]; exact hm
    exact (Subgroup.mem_normalizer_iff.mp hN v).mp hv
  set K : Subgroup ↥V := (V ⊓ wOf V H).subgroupOf V with hK
  have hKcard : Nat.card ↥K = 2 := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      V ⊓ wOf V H ≤ V)).toEquiv]
    exact cfg.hyp.module.trans cfg.hyp.q_two
  have hidx : K.index = 2 := by
    have h := K.card_mul_index
    rw [hKcard, card_V cfg] at h
    omega
  have hmemK : ∀ x : ↥V, x ∈ K ↔ (x : G) ∈ V ⊓ wOf V H := fun x => Subgroup.mem_subgroupOf
  have hiff : m * v * m⁻¹ ∈ V ⊓ wOf V H ↔ v ∈ V ⊓ wOf V H := by
    constructor
    · intro h
      have := conj_eq_of_mem_VW h11b cfg (M.inv_mem hm) h
      have e : m⁻¹ * (m * v * m⁻¹) * m⁻¹⁻¹ = v := by group
      rw [e] at this
      rw [this]
      exact h
    · intro h
      rw [conj_eq_of_mem_VW h11b cfg hm h]
      exact h
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨m * v * m⁻¹, hmV⟩)
    (b := (⟨v, hv⟩ : ↥V)⁻¹)
  have h1 : (⟨m * v * m⁻¹, hmV⟩ : ↥V) ∈ K ↔ m * v * m⁻¹ ∈ V ⊓ wOf V H := hmemK _
  have h2 : (⟨v, hv⟩ : ↥V)⁻¹ ∈ K ↔ v ∈ V ⊓ wOf V H := by
    rw [inv_mem_iff]
    exact hmemK _
  have hres := key.mpr (h1.trans (hiff.trans h2.symm))
  rw [hmemK] at hres
  have e : ((⟨m * v * m⁻¹, hmV⟩ * (⟨v, hv⟩ : ↥V)⁻¹ : ↥V) : G) = ⁅m, v⁆ := by
    rw [commutatorElement_def]
    rfl
  rw [e] at hres
  exact hres

theorem comm_mem_P_of_mem_W (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {w : G} (hw : w ∈ wOf V H) {q : G} (hq : q ∈ Q) : ⁅q, w⁆ ∈ P := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hQM : Q ≤ M := by rw [hc.hQ]; exact (inSubgroup_pCore_two M).2.1
  have hwM : w ∈ M := wOf_le_M cfg hw
  have hWab := (MinCex.wOf_isElemAbelian hc).1
  have hcommW : ∀ x ∈ wOf V H, ∀ y ∈ wOf V H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hWab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQV : ⁅Q, V⁆ ≤ V ⊓ wOf V H := by
    rw [Subgroup.commutator_le]
    intro x hx v hv
    exact comm_mem_VW_of_mem_M h11b cfg (hQM hx) hv
  have hwz : Subgroup.zpowers w ≤ wOf V H ⊓ M := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨hw, hwM⟩
  have hVw : ⁅V, Subgroup.zpowers w⁆ ≤ V ⊓ wOf V H := by
    rw [Subgroup.commutator_le]
    intro v hv y hy
    have hyW := (Subgroup.mem_inf.mp (hwz hy)).1
    have hyM := (Subgroup.mem_inf.mp (hwz hy)).2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hN : y ∈ Subgroup.normalizer (V : Set G) := by rw [hc.normalizer_eq]; exact hyM
      have h1 : y * v⁻¹ * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hN _).mp (V.inv_mem hv)
      rw [commutatorElement_def, mul_assoc (v * y), mul_assoc v]
      exact V.mul_mem hv (by simpa [mul_assoc] using h1)
    · have hvH : v ∈ H := hc.V_le_H hv
      have h1 : v * y * v⁻¹ ∈ wOf V H :=
        (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hvH) y).mp hyW
      rw [commutatorElement_def]
      exact (wOf V H).mul_mem h1 ((wOf V H).inv_mem hyW)
  have h1 : ⁅⁅Q, V⁆, Subgroup.zpowers w⁆ = ⊥ := by
    refine eq_bot_iff.mpr ((Subgroup.commutator_mono hQV le_rfl).trans (le_of_eq ?_))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcommW _ ((Subgroup.mem_inf.mp (hwz hy)).1) _ (Subgroup.mem_inf.mp hx).2
  have h2 : ⁅⁅V, Subgroup.zpowers w⁆, Q⁆ = ⊥ := by
    refine eq_bot_iff.mpr ((Subgroup.commutator_mono hVw le_rfl).trans (le_of_eq ?_))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := conj_eq_of_mem_VW h11b cfg (hQM hy) hx
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [this]
  have h3 : ⁅⁅Subgroup.zpowers w, Q⁆, V⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hle : ⁅Subgroup.zpowers w, Q⁆ ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h3
  have hwq : ⁅w, q⁆ ∈ Subgroup.centralizer (V : Set G) :=
    hle (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers w) hq)
  have hqw : ⁅q, w⁆ ∈ Subgroup.centralizer (V : Set G) := by
    have := Subgroup.inv_mem _ hwq
    rwa [commutatorElement_inv] at this
  have hqwQ : ⁅q, w⁆ ∈ Q := by
    have hN : w ∈ Subgroup.normalizer (Q : Set G) := by
      rw [hc.hQ]; exact (inSubgroup_pCore_two M).2.2 hwM
    have h4 : w * q⁻¹ * w⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hN _).mp (Q.inv_mem hq)
    rw [commutatorElement_def, mul_assoc (q * w), mul_assoc q]
    exact Q.mul_mem hq (by simpa [mul_assoc] using h4)
  rw [hc.hP]
  exact Subgroup.mem_inf.mpr ⟨hqwQ, hqw⟩

theorem exists_conj_aG_eq (cfg : GCfg M V Q P H Φ ψ a T) {w : G} (hw : w ∈ wOf V H)
    (hw1 : w ≠ 1) : ∃ x : ↥(xOf V H),
      (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G)⁻¹ = w := by
  have hVH : V ≤ H := cfg.hyp.setup.mc.toMinCex.V_le_H
  set v := ψ.symm (Additive.ofMul ⟨w, hw⟩) with hv
  have hψv : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) = w := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  have hv0 : v ≠ 0 := by
    intro h0
    apply hw1
    rw [← hψv, h0, psi_zero]
  obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero cfg.ne hv0
  obtain ⟨x, hx⟩ := xToXbar_surjective hVH (Φ g)
  refine ⟨x, ?_⟩
  have key := cfg.nat.equiv x a
  rw [hx, MulEquiv.symm_apply_apply, hg, hψv] at key
  exact key.symm

theorem conj_mem_W_of_commute (h11a : Lemma11aStatement) (h11c : Lemma11cStatement)
    (cfg : GCfg M V Q P H Φ ψ a T) {b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hb : CaseM.spForm a b = 1) {c : G} (hcM : c ∈ M)
    (hcb : c * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * c) {w : G} (hw : w ∈ wOf V H) :
    c * w * c⁻¹ ∈ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨hPiff, -, -, -⟩ :=
    h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  have hcov := (h11c G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans
    cfg.point b hb).2
  have hbW : ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) ∈ wOf V H := (Additive.toMul (ψ b)).2
  have hcbc : c * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * c⁻¹ =
      ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) := by rw [hcb, mul_inv_cancel_right]
  have hPW : ∀ u ∈ P ⊓ wOf V H, c * u * c⁻¹ ∈ wOf V H := by
    intro u hu
    obtain ⟨p, hp, hpu⟩ := hcov u hu
    have hp' : c * p * c⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hcM) p).mp hp
    have hp'H : c * p * c⁻¹ ∈ H := hc.PleH hp'
    have e : c * u * c⁻¹ = ⁅c * p * c⁻¹, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ := by
      calc c * u * c⁻¹ = c * (p * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * p⁻¹ *
            ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁻¹) * c⁻¹ := by
            rw [← hpu, commutatorElement_def]
        _ = (c * p * c⁻¹) * (c * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * c⁻¹) *
            (c * p * c⁻¹)⁻¹ * (c * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * c⁻¹)⁻¹ := by
            group
        _ = ⁅c * p * c⁻¹, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ := by
            rw [hcbc, commutatorElement_def]
    rw [e, commutatorElement_def]
    exact (wOf V H).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hp'H) _).mp hbW)
      ((wOf V H).inv_mem hbW)
  set v := ψ.symm (Additive.ofMul ⟨w, hw⟩) with hv
  have hψv : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) = w := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  rcases twl_gf2 (CaseM.spForm a v) with h0 | h1
  · exact hPW w (Subgroup.mem_inf.mpr ⟨hψv ▸ (hPiff v).mpr h0, hw⟩)
  ·
    have hsum : CaseM.spForm a (v + b) = 0 := by
      rw [CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right, h1, hb, gf2_add_self]
    have hwb : w * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) ∈ P ⊓ wOf V H := by
      rw [← hψv, psi_mul]
      exact Subgroup.mem_inf.mpr ⟨(hPiff _).mpr hsum, (Additive.toMul (ψ (v + b))).2⟩
    have h2 := hPW _ hwb
    have e : c * w * c⁻¹ = c * (w * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)) * c⁻¹ *
        (c * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * c⁻¹)⁻¹ := by group
    rw [e, hcbc]
    exact (wOf V H).mul_mem h2 ((wOf V H).inv_mem hbW)

theorem conjSubgroup_xOf_le (h11a : Lemma11aStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {c : G} (hcM : c ∈ M) (hcW : ∀ w ∈ wOf V H, c * w * c⁻¹ ∈ wOf V H) :
    conjSubgroup c (xOf V H) ≤ xOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨-, -, hxOf, -⟩ :=
    h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have haV := (Subgroup.mem_inf.mp haK).1
  have haW := (Subgroup.mem_inf.mp haK).2
  unfold conjSubgroup xOf
  rw [Subgroup.map_iSup]
  refine iSup_le fun U => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hU => ?_
  obtain ⟨h, hh, rfl⟩ := hU
  have hw : c * h * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (c * h)⁻¹ ∈ wOf V H := by
    have h1 : h * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * h⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hh) _).mp haW
    have := hcW _ h1
    simpa [mul_assoc] using this
  have hw1 : c * h * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (c * h)⁻¹ ≠ 1 := by
    intro h1
    apply haG1
    calc ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)
        = (c * h)⁻¹ * (c * h * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (c * h)⁻¹) *
            (c * h) := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨x, hx⟩ := exists_conj_aG_eq cfg hw hw1
  have hg : (x : G)⁻¹ * (c * h) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * ((x : G)⁻¹ * (c * h)) := by
    have e : c * h * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) =
        (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G)⁻¹ * (c * h) := by
      rw [hx]; group
    calc (x : G)⁻¹ * (c * h) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)
        = (x : G)⁻¹ * (c * h * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)) := by group
      _ = ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * ((x : G)⁻¹ * (c * h)) := by
          rw [e]; group
  have hgM : (x : G)⁻¹ * (c * h) ∈ M := hc.mem_M_of_commute haV haG1 hg
  have hgN : (x : G)⁻¹ * (c * h) ∈ Subgroup.normalizer (V : Set G) := by
    rw [hc.normalizer_eq]; exact hgM
  have hVeq : conjSubgroup ((x : G)⁻¹ * (c * h)) V = V := conjSubgroup_eq_self_iff.mpr hgN
  have hU : (conjSubgroup h V).map (MulAut.conj c).toMonoidHom = conjSubgroup (x : G) V := by
    have e1 : (conjSubgroup h V).map (MulAut.conj c).toMonoidHom =
        conjSubgroup c (conjSubgroup h V) := rfl
    rw [e1, conjSubgroup_conjSubgroup]
    calc conjSubgroup (c * h) V = conjSubgroup ((x : G) * ((x : G)⁻¹ * (c * h))) V := by
          congr 1; group
      _ = conjSubgroup (x : G) (conjSubgroup ((x : G)⁻¹ * (c * h)) V) :=
          (conjSubgroup_conjSubgroup _ _ _).symm
      _ = conjSubgroup (x : G) V := by rw [hVeq]
  rw [hU]
  have hxH : (x : G) ∈ H := xOf_le_H hc.V_le_H x.2
  exact le_xOf (conjSubgroup_mem_omegaOf hxH)

theorem exists_mem_V_not_mem_W (cfg : GCfg M V Q P H Φ ψ a T) :
    ∃ v₀ ∈ V, v₀ ∉ wOf V H := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ V ⊓ wOf V H := fun v hv => Subgroup.mem_inf.mpr ⟨hv, hcon v hv⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [card_V cfg, cfg.hyp.module.trans cfg.hyp.q_two] at h1
  omega

theorem conj_act_eq_trans (cfg : GCfg M V Q P H Φ ψ a T) (x : ↥(xOf V H)) {v₀ : G}
    (hv₀ : v₀ ∈ V) (hv₀W : v₀ ∉ wOf V H) {v : Fin n ⊕ Fin n → GaloisField 2 1}
    (hv : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) =
      (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G)⁻¹)
    (w : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((x : G) * v₀ * (x : G)⁻¹) * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) *
        ((x : G) * v₀ * (x : G)⁻¹)⁻¹ =
      ((Additive.toMul (ψ (w + CaseM.spForm v w • v)) : ↥(wOf V H)) : G) := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hVX : V ≤ xOf V H := le_xOf (V_mem_omegaOf V H)
  set z : ↥(xOf V H) := ⟨v₀, hVX hv₀⟩ with hz
  set y : ↥(xOf V H) := x * z * x⁻¹ with hy
  have hzV : xToXbar hVH z ∈ Vy V H := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [coe_xToXbar]
    exact mem_barOf_iff.mpr ⟨⟨v₀, hVH hv₀⟩, hv₀, rfl⟩
  rw [← cfg.point] at hzV
  obtain ⟨t, htT, htz⟩ := Subgroup.mem_map.mp hzV
  obtain ⟨c, hct⟩ := (cfg.trans.1 t).mp htT
  have hc1 : c = 1 := by
    rcases twl_gf2 c with h0 | h1
    · exfalso
      rw [h0, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_zero] at hct
      have ht1 : t = 1 := SpExtras.mat_injective (by rw [hct, map_one])
      have hz1 : xToXbar hVH z = 1 := by
        rw [← htz, ht1]
        exact map_one _
      exact hv₀W ((cxw_xToXbar_eq_one hVH z).mp hz1)
    · exact h1
  rw [hc1] at hct
  set g := Φ.symm (xToXbar hVH x) with hg
  have hga : SpExtras.mat n (GaloisField 2 1) g *ᵥ a = v := by
    have key := cfg.nat.equiv x a
    rw [← hg, ← hv] at key
    exact psi_injective key
  have htz' : Φ.symm (xToXbar hVH z) = t := by
    rw [← htz]
    exact Φ.symm_apply_apply t
  have hyΦ : Φ.symm (xToXbar hVH y) = g * t * g⁻¹ := by
    rw [hy]
    simp only [map_mul, map_inv]
    rw [htz', ← hg]
  have hymat : SpExtras.mat n (GaloisField 2 1) (Φ.symm (xToXbar hVH y)) =
      CaseM.spTrans v 1 := by
    rw [hyΦ, CaseM.mat_conj_of_mat_eq hct g, hga]
  have key := cfg.nat.equiv y w
  rw [hymat, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, one_mul] at key
  rw [key]
  rfl

omit [Finite G] in
noncomputable def lmap (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)) {q : G}
    (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H) (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    Fin n ⊕ Fin n → GaloisField 2 1 :=
  ψ.symm (Additive.ofMul ⟨q * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * q⁻¹,
    hq _ (Additive.toMul (ψ v)).2⟩)

omit [Finite G] in
theorem psi_lmap {q : G} (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H)
    (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ (lmap ψ hq v)) : ↥(wOf V H)) : G) =
      q * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * q⁻¹ := by
  unfold lmap
  rw [AddEquiv.apply_symm_apply]
  rfl

omit [Finite G] in
theorem lmap_add {q : G} (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H)
    (v w : Fin n ⊕ Fin n → GaloisField 2 1) :
    lmap ψ hq (v + w) = lmap ψ hq v + lmap ψ hq w := by
  apply psi_injective (ψ := ψ)
  rw [← psi_mul, psi_lmap, psi_lmap, psi_lmap, ← psi_mul]
  group

omit [Finite G] in
theorem lmap_zero {q : G} (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H) :
    lmap ψ hq 0 = 0 := by
  apply psi_injective (ψ := ψ)
  rw [psi_lmap, psi_zero]
  group

omit [Finite G] in
theorem lmap_smul {q : G} (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H) (c : GaloisField 2 1)
    (v : Fin n ⊕ Fin n → GaloisField 2 1) : lmap ψ hq (c • v) = c • lmap ψ hq v := by
  rcases twl_gf2 c with h | h
  · rw [h, zero_smul, zero_smul, lmap_zero]
  · rw [h, one_smul, one_smul]

omit [Finite G] in
theorem lmap_injective {q : G} (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H) :
    Function.Injective (lmap ψ hq) := by
  intro v w h
  have h1 := congrArg (fun u => ((Additive.toMul (ψ u) : ↥(wOf V H)) : G)) h
  simp only [psi_lmap] at h1
  exact psi_injective (mul_left_cancel (mul_right_cancel h1))

theorem exists_X_conj_of_mem_M (cfg : GCfg M V Q P H Φ ψ a T) {q : G} (hqM : q ∈ M)
    (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H) (x : ↥(xOf V H)) :
    ∃ x' : ↥(xOf V H), (x' : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x' : G)⁻¹ =
        q * ((x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G)⁻¹) * q⁻¹ ∧
      (x' : G)⁻¹ * (q * (x : G)) ∈ M := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have haV := (Subgroup.mem_inf.mp haK).1
  have haW := (Subgroup.mem_inf.mp haK).2
  have hxH : (x : G) ∈ H := xOf_le_H hc.V_le_H x.2
  have hw : q * ((x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G)⁻¹) * q⁻¹ ∈
      wOf V H :=
    hq _ ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hxH) _).mp haW)
  have hw1 : q * ((x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G)⁻¹) * q⁻¹ ≠ 1 := by
    intro h1
    apply haG1
    calc ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)
        = (q * (x : G))⁻¹ * (q * ((x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) *
            (x : G)⁻¹) * q⁻¹) * (q * (x : G)) := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨x', hx'⟩ := exists_conj_aG_eq cfg hw hw1
  refine ⟨x', hx', hc.mem_M_of_commute haV haG1 ?_⟩
  have e : q * (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) =
      (x' : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x' : G)⁻¹ * (q * (x : G)) := by
    rw [hx']; group
  calc (x' : G)⁻¹ * (q * (x : G)) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)
      = (x' : G)⁻¹ * (q * (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)) := by group
    _ = ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * ((x' : G)⁻¹ * (q * (x : G))) := by
        rw [e]; group

theorem conj_not_mem_W (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T) {g : G}
    (hg : g ∈ M) {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀W : v₀ ∉ wOf V H) :
    g * v₀ * g⁻¹ ∈ V ∧ g * v₀ * g⁻¹ ∉ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hN : g ∈ Subgroup.normalizer (V : Set G) := by rw [hc.normalizer_eq]; exact hg
  have h1 : g * v₀ * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hN v₀).mp hv₀
  refine ⟨h1, fun hW => hv₀W ?_⟩
  have hA : g * v₀ * g⁻¹ ∈ V ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨h1, hW⟩
  have := conj_eq_of_mem_VW h11b cfg (M.inv_mem hg) hA
  have e : g⁻¹ * (g * v₀ * g⁻¹) * g⁻¹⁻¹ = v₀ := by group
  rw [e] at this
  rw [this]
  exact hW

theorem spForm_lmap (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T) {q : G}
    (hqM : q ∈ M) (hq : ∀ w ∈ wOf V H, q * w * q⁻¹ ∈ wOf V H)
    (v w : Fin n ⊕ Fin n → GaloisField 2 1) :
    CaseM.spForm (lmap ψ hq v) (lmap ψ hq w) = CaseM.spForm v w := by
  by_cases hv0 : v = 0
  · rw [hv0, lmap_zero]
    simp [CaseM.spForm]
  have hψv1 : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) ≠ 1 := by
    intro h1
    apply hv0
    apply psi_injective (ψ := ψ)
    rw [h1, psi_zero]
  obtain ⟨x, hx⟩ := exists_conj_aG_eq cfg (Additive.toMul (ψ v)).2 hψv1
  obtain ⟨v₀, hv₀, hv₀W⟩ := exists_mem_V_not_mem_W cfg
  obtain ⟨x', hx', hgM⟩ := exists_X_conj_of_mem_M cfg hqM hq x
  obtain ⟨hv₀', hv₀'W⟩ := conj_not_mem_W h11b cfg hgM hv₀ hv₀W
  have hLv : ((Additive.toMul (ψ (lmap ψ hq v)) : ↥(wOf V H)) : G) =
      (x' : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x' : G)⁻¹ := by
    rw [hx', hx, psi_lmap]
  have h1 := conj_act_eq_trans cfg x hv₀ hv₀W hx.symm w
  have h2 := conj_act_eq_trans cfg x' hv₀' hv₀'W hLv (lmap ψ hq w)
  have e : (x' : G) * ((x' : G)⁻¹ * (q * (x : G)) * v₀ * ((x' : G)⁻¹ * (q * (x : G)))⁻¹) *
      (x' : G)⁻¹ = q * ((x : G) * v₀ * (x : G)⁻¹) * q⁻¹ := by group
  rw [e, psi_lmap] at h2
  have h3 : q * ((x : G) * v₀ * (x : G)⁻¹) * q⁻¹ *
      (q * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) * q⁻¹) *
      (q * ((x : G) * v₀ * (x : G)⁻¹) * q⁻¹)⁻¹ =
      q * (((x : G) * v₀ * (x : G)⁻¹) * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) *
        ((x : G) * v₀ * (x : G)⁻¹)⁻¹) * q⁻¹ := by group
  rw [h3, h1, ← psi_lmap hq, lmap_add, lmap_smul] at h2
  have h4 := psi_injective h2
  have h5 : CaseM.spForm v w • lmap ψ hq v =
      CaseM.spForm (lmap ψ hq v) (lmap ψ hq w) • lmap ψ hq v := add_left_cancel h4
  have hLv0 : lmap ψ hq v ≠ 0 := by
    intro h0
    apply hv0
    apply lmap_injective hq
    rw [h0, lmap_zero]
  exact (smul_left_injective (GaloisField 2 1) hLv0 h5).symm

omit [Finite G] in
theorem eq_one_of_mem_spRad_of_fix {b : Fin n ⊕ Fin n → GaloisField 2 1} (ha : a ≠ 0)
    (hb : CaseM.spForm a b = 1) {g : StatedSp n (GaloisField 2 1)} (hg : g ∈ spRad a)
    (hgb : SpExtras.mat n (GaloisField 2 1) g *ᵥ b = b) : g = 1 := by
  obtain ⟨u, hu, c, hgu⟩ := exists_spRad_param ha hg
  have h1 := hgu b
  rw [hgb, hb, one_smul, mul_one] at h1
  have h0 : u + (CaseM.spForm u b + c) • a = 0 := by
    have e : b + u + CaseM.spForm u b • a + c • a = b + (u + (CaseM.spForm u b + c) • a) := by
      rw [add_smul]; abel
    rw [e] at h1
    exact add_left_cancel (h1.symm.trans (add_zero b).symm)
  set μ := CaseM.spForm u b + c with hμ
  clear_value μ
  have hu' : u = μ • a := by
    calc u = u + (u + μ • a) := by rw [h0, add_zero]
      _ = (u + u) + μ • a := by abel
      _ = μ • a := by rw [gf2_vec_add_self, zero_add]
  have hub : CaseM.spForm u b = μ := by
    rw [hu', CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', hb, mul_one]
  have hc0 : c = 0 := by
    calc c = (μ + μ) + c := by rw [gf2_add_self, zero_add]
      _ = μ + (CaseM.spForm u b + c) := by rw [hub]; abel
      _ = μ + μ := by rw [← hμ]
      _ = 0 := gf2_add_self μ
  refine CFSG.Timmesfeld.Transvection.ModelRank.eq_of_mat_mulVec_eq fun x => ?_
  rw [hgu x, map_one, Matrix.one_mulVec, hc0, zero_mul, zero_smul, add_zero, hu',
    CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', smul_smul, add_assoc,
    ← add_smul, mul_comm (CaseM.spForm a x) μ, gf2_add_self, zero_smul, add_zero]

omit [Finite G] in
noncomputable def lmapEquiv (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    {q : G} (hq : q ∈ Subgroup.normalizer (wOf V H : Set G)) :
    (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ (Fin n ⊕ Fin n → GaloisField 2 1) where
  toFun := lmap ψ (fun w hw => (Subgroup.mem_normalizer_iff.mp hq w).mp hw)
  invFun := lmap ψ (fun w hw => (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hq) w).mp hw)
  left_inv v := by
    apply psi_injective (ψ := ψ)
    rw [psi_lmap, psi_lmap]
    group
  right_inv v := by
    apply psi_injective (ψ := ψ)
    rw [psi_lmap, psi_lmap]
    group
  map_add' := lmap_add _

omit [Finite G] in
theorem lmapEquiv_apply {q : G} (hq : q ∈ Subgroup.normalizer (wOf V H : Set G))
    (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ (lmapEquiv ψ hq v)) : ↥(wOf V H)) : G) =
      q * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * q⁻¹ :=
  psi_lmap (fun w hw => (Subgroup.mem_normalizer_iff.mp hq w).mp hw) v

theorem exists_sp_of_mem_M (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {q : G} (hqM : q ∈ M) (hqN : q ∈ Subgroup.normalizer (wOf V H : Set G)) :
    ∃ g : StatedSp n (GaloisField 2 1), ∀ v,
      SpExtras.mat n (GaloisField 2 1) g *ᵥ v = lmapEquiv ψ hqN v :=
  exists_statedSp_of_addEquiv (lmapEquiv ψ hqN)
    (fun v w => spForm_lmap h11b cfg hqM
      (fun w hw => (Subgroup.mem_normalizer_iff.mp hqN w).mp hw) v w)

theorem mem_M_of_mem_Q (cfg : GCfg M V Q P H Φ ψ a T) {k : G} (hk : k ∈ Q) : k ∈ M := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hQM : Q ≤ M := by rw [hc.hQ]; exact (inSubgroup_pCore_two M).2.1
  exact hQM hk

noncomputable def qRepFun (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    (k : ↥(Q ⊓ Subgroup.normalizer (wOf V H : Set G))) : StatedSp n (GaloisField 2 1) :=
  (exists_sp_of_mem_M h11b cfg (mem_M_of_mem_Q cfg (Subgroup.mem_inf.mp k.2).1)
    (Subgroup.mem_inf.mp k.2).2).choose

theorem qRepFun_spec (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    (k : ↥(Q ⊓ Subgroup.normalizer (wOf V H : Set G))) (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 1) (qRepFun h11b cfg k) *ᵥ v)) :
        ↥(wOf V H)) : G) =
      (k : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (k : G)⁻¹ := by
  unfold qRepFun
  rw [(exists_sp_of_mem_M h11b cfg (mem_M_of_mem_Q cfg (Subgroup.mem_inf.mp k.2).1)
    (Subgroup.mem_inf.mp k.2).2).choose_spec v, lmapEquiv_apply]

noncomputable def qRep (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T) :
    ↥(Q ⊓ Subgroup.normalizer (wOf V H : Set G)) →* StatedSp n (GaloisField 2 1) where
  toFun := qRepFun h11b cfg
  map_one' := by
    refine CFSG.Timmesfeld.Transvection.ModelRank.eq_of_mat_mulVec_eq fun v => ?_
    apply psi_injective (ψ := ψ)
    rw [qRepFun_spec, map_one, Matrix.one_mulVec]
    simp
  map_mul' k k' := by
    refine CFSG.Timmesfeld.Transvection.ModelRank.eq_of_mat_mulVec_eq fun v => ?_
    apply psi_injective (ψ := ψ)
    rw [qRepFun_spec, map_mul, ← Matrix.mulVec_mulVec, qRepFun_spec, qRepFun_spec]
    simp only [Subgroup.coe_mul]
    group

theorem qRep_spec (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    (k : ↥(Q ⊓ Subgroup.normalizer (wOf V H : Set G))) (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 1) (qRep h11b cfg k) *ᵥ v)) :
        ↥(wOf V H)) : G) =
      (k : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (k : G)⁻¹ :=
  qRepFun_spec h11b cfg k v

theorem qRep_range_le_spRad (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T) :
    (qRep h11b cfg).range ≤ spRad a := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  have haV := (Subgroup.mem_inf.mp haK).1
  have hQn : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := by
    intro m hm q hq
    rw [hc.hQ] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp ((inSubgroup_pCore_two M).2.2 hm) q).mp hq
  have hQp : IsPGroup 2 Q := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).1
  set S := (qRep h11b cfg).range with hS
  have hSa : ∀ s ∈ S, SpExtras.mat n (GaloisField 2 1) s *ᵥ a = a := by
    rintro _ ⟨k, rfl⟩
    apply psi_injective (ψ := ψ)
    rw [qRep_spec, commute_aG_of_mem_M h11b cfg (mem_M_of_mem_Q cfg (Subgroup.mem_inf.mp k.2).1),
      mul_inv_cancel_right]
  have hSN : S ≤ Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))) := by
    intro s hs
    rw [normalizer_eq_spLine cfg.ne cfg.trans]
    exact ⟨1, one_ne_zero, by rw [hSa s hs, one_smul]⟩
  have hfwd : ∀ n₁ ∈ Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))),
      ∀ s ∈ S, n₁ * s * n₁⁻¹ ∈ S := by
    intro n₁ hn₁ s hs
    rw [normalizer_eq_spLine cfg.ne cfg.trans] at hn₁
    obtain ⟨μ, hμ, hμa⟩ := hn₁
    rw [tw_eq_one_of_card_two hF2 hμ, one_smul] at hμa
    obtain ⟨x, hx⟩ := xToXbar_surjective hVH (Φ n₁)
    have hxn : Φ.symm (xToXbar hVH x) = n₁ := by rw [hx]; exact Φ.symm_apply_apply n₁
    have hxn' : Φ.symm (xToXbar hVH x⁻¹) = n₁⁻¹ := by rw [map_inv, map_inv, hxn]
    have hxa : (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) =
        ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G) := by
      have key := cfg.nat.equiv x a
      rw [hxn, hμa] at key
      calc (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G)
          = (x : G) * ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G)⁻¹ * (x : G) := by group
        _ = ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) * (x : G) := by rw [← key]
    have hxM : (x : G) ∈ M := hc.mem_M_of_commute haV haG1 hxa
    have hxH : (x : G) ∈ H := xOf_le_H hVH x.2
    obtain ⟨k, rfl⟩ := hs
    have hk := Subgroup.mem_inf.mp k.2
    have hk'Q : (x : G) * (k : G) * (x : G)⁻¹ ∈ Q := hQn x hxM k hk.1
    have hk'N : (x : G) * (k : G) * (x : G)⁻¹ ∈ Subgroup.normalizer (wOf V H : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (H_le_normalizer_wOf V H hxH) hk.2)
        (Subgroup.inv_mem _ (H_le_normalizer_wOf V H hxH))
    refine ⟨⟨(x : G) * (k : G) * (x : G)⁻¹, Subgroup.mem_inf.mpr ⟨hk'Q, hk'N⟩⟩, ?_⟩
    refine CFSG.Timmesfeld.Transvection.ModelRank.eq_of_mat_mulVec_eq fun v => ?_
    apply psi_injective (ψ := ψ)
    rw [qRep_spec, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e1 := cfg.nat.equiv x (SpExtras.mat n (GaloisField 2 1) (qRep h11b cfg k) *ᵥ
      (SpExtras.mat n (GaloisField 2 1) n₁⁻¹ *ᵥ v))
    rw [hxn] at e1
    rw [e1, qRep_spec]
    have e2 := cfg.nat.equiv x⁻¹ v
    rw [hxn'] at e2
    rw [e2]
    simp only [Subgroup.coe_inv]
    group
  have hSnorm' : Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 1))) ≤
      Subgroup.normalizer (S : Set ↥(StatedSp n (GaloisField 2 1))) := by
    intro n₁ hn₁
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · exact hfwd n₁ hn₁ s
    · intro hs
      have h1 := hfwd n₁⁻¹ (Subgroup.inv_mem _ hn₁) _ hs
      have e : n₁⁻¹ * (n₁ * s * n₁⁻¹) * n₁⁻¹⁻¹ = s := by group
      rwa [e] at h1
  have hSp : IsPGroup 2 S := by
    have hK : IsPGroup 2 ↥(Q ⊓ Subgroup.normalizer (wOf V H : Set G)) := hQp.to_le inf_le_left
    exact hK.of_surjective (qRep h11b cfg).rangeRestrict (qRep h11b cfg).rangeRestrict_surjective
  rw [← spCoreStmt_holds n (GaloisField 2 1) cfg.ne cfg.trans]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSN hSnorm' hSp

theorem centralizes_W_of_commute (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {c : G} (hcQ : c ∈ Q)
    (hcb : c * ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) =
      ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) * c) {w : G} (hw : w ∈ wOf V H) :
    c * w = w * c := by
  have hcM : c ∈ M := mem_M_of_mem_Q cfg hcQ
  have hcN : c ∈ Subgroup.normalizer (wOf V H : Set G) :=
    Subgroup.mem_normalizer_fintype fun w hw =>
      conj_mem_W_of_commute h11a h11c cfg hb hcM hcb hw
  set k : ↥(Q ⊓ Subgroup.normalizer (wOf V H : Set G)) :=
    ⟨c, Subgroup.mem_inf.mpr ⟨hcQ, hcN⟩⟩ with hk
  have hsR : qRep h11b cfg k ∈ spRad a := qRep_range_le_spRad h11b cfg ⟨k, rfl⟩
  have hsb : SpExtras.mat n (GaloisField 2 1) (qRep h11b cfg k) *ᵥ b = b := by
    apply psi_injective (ψ := ψ)
    rw [qRep_spec, hk]
    show c * _ * c⁻¹ = _
    rw [hcb, mul_inv_cancel_right]
  have hs1 := eq_one_of_mem_spRad_of_fix cfg.ne hb hsR hsb
  set v := ψ.symm (Additive.ofMul ⟨w, hw⟩) with hv
  have hψv : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) = w := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  have key := qRep_spec h11b cfg k v
  rw [hs1, map_one, Matrix.one_mulVec, hψv] at key
  calc c * w = c * w * c⁻¹ * c := by group
    _ = w * c := by rw [show c * w * c⁻¹ = w from key.symm]

theorem comm_mem_W_of_centralizes_W (cfg : GCfg M V Q P H Φ ψ a T) {c : G}
    (hcX : conjSubgroup c (xOf V H) ≤ xOf V H) (hcW : ∀ w ∈ wOf V H, c * w = w * c)
    {x : G} (hx : x ∈ xOf V H) : ⁅x, c⁆ ∈ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcx : c * x * c⁻¹ ∈ xOf V H := hcX ⟨x, hx, rfl⟩
  have hW : ∀ w ∈ wOf V H, c * w * c⁻¹ = w := fun w hw => by
    rw [hcW w hw, mul_inv_cancel_right]
  have hW' : ∀ w ∈ wOf V H, c⁻¹ * w * c = w := fun w hw => by
    have := hcW w hw
    calc c⁻¹ * w * c = c⁻¹ * (w * c) := by group
      _ = c⁻¹ * (c * w) := by rw [this]
      _ = w := by group
  have himg : xToXbar hVH ⟨c * x * c⁻¹, hcx⟩ = xToXbar hVH ⟨x, hx⟩ := by
    apply Φ.symm.injective
    refine CFSG.Timmesfeld.Transvection.ModelRank.eq_of_mat_mulVec_eq fun v => ?_
    apply psi_injective (ψ := ψ)
    rw [cfg.nat.equiv, cfg.nat.equiv]
    have hψW : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) ∈ wOf V H := (Additive.toMul (ψ v)).2
    have hxH : x ∈ H := xOf_le_H hVH hx
    have h1 : x * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * x⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hxH) _).mp hψW
    show c * x * c⁻¹ * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (c * x * c⁻¹)⁻¹ =
      x * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * x⁻¹
    calc c * x * c⁻¹ * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (c * x * c⁻¹)⁻¹
        = c * (x * (c⁻¹ * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * c) * x⁻¹) * c⁻¹ := by
          group
      _ = c * (x * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * x⁻¹) * c⁻¹ := by
          rw [hW' _ hψW]
      _ = x * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * x⁻¹ := hW _ h1
  have h2 := nm_mem_W_of_xToXbar_eq hVH himg
  have hxH : x ∈ H := xOf_le_H hVH hx
  have h3 : x * ((c * x * c⁻¹)⁻¹ * x) * x⁻¹ ∈ wOf V H :=
    (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hxH) _).mp
      (by simpa using h2)
  have e : ⁅x, c⁆ = x * ((c * x * c⁻¹)⁻¹ * x) * x⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact h3

omit [Finite G] in
theorem isMulCommutative_sup_of_commute {A B : Subgroup G}
    (hA : A ≤ Subgroup.centralizer (A : Set G)) (hB : B ≤ Subgroup.centralizer (B : Set G))
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) : IsMulCommutative ↥(A ⊔ B) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  have hBA : B ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer_iff.mp hAB
  have h1 : A ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le hA hBA)
  have h2 : B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le hAB hB)
  exact sup_le h1 h2

omit [Finite G] in
theorem conj_mem_commutator_of_normalizes {A B : Subgroup G} {m : G}
    (hA : m ∈ Subgroup.normalizer (A : Set G)) (hB : m ∈ Subgroup.normalizer (B : Set G))
    {z : G} (hz : z ∈ ⁅A, B⁆) : m * z * m⁻¹ ∈ ⁅A, B⁆ := by
  have hle : ⁅A, B⁆ ≤ (⁅A, B⁆ : Subgroup G).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap]
    show m * ⁅x, y⁆ * m⁻¹ ∈ ⁅A, B⁆
    have e : m * ⁅x, y⁆ * m⁻¹ = ⁅m * x * m⁻¹, m * y * m⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hA x).mp hx)
      ((Subgroup.mem_normalizer_iff.mp hB y).mp hy)
  exact hle hz

theorem mem_P_of_mem_W_Q (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) (cfg : GCfg M V Q P H Φ ψ a T) {c : G} (hcQ : c ∈ Q)
    (hcW : ∀ w ∈ wOf V H, c * w = w * c) (hcX : ∀ x ∈ xOf V H, ⁅x, c⁆ ∈ wOf V H)
    (hQ : ∀ q ∈ Q, q ∈ P ∨ c⁻¹ * q ∈ P) {w : G} (hwW : w ∈ wOf V H) (hwQ : w ∈ Q) :
    w ∈ P := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨hPiff, -, hxOf, -⟩ :=
    h11a G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point
  obtain ⟨hcomm', -, -⟩ := h11b G M V Q P H cfg.hyp cfg.centre cfg.iw
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hcM : c ∈ M := mem_M_of_mem_Q cfg hcQ
  have hPN : ∀ m ∈ M, m ∈ Subgroup.normalizer (P : Set G) := fun m hm =>
    hc.M_le_normalizer_P hm
  have hQN : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => by
    rw [hc.hQ]; exact (inSubgroup_pCore_two M).2.2 hm
  by_contra hwP
  set v := ψ.symm (Additive.ofMul ⟨w, hwW⟩) with hv
  have hψv : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) = w := by
    rw [hv, AddEquiv.apply_symm_apply]
    rfl
  have hv1 : CaseM.spForm a v = 1 := by
    rcases twl_gf2 (CaseM.spForm a v) with h0 | h1
    · exact absurd (hψv ▸ (hPiff v).mpr h0) hwP
    · exact h1
  have hcov := (h11c G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne cfg.trans
    cfg.point v hv1).2
  rw [hψv] at hcov
  have hPX : ∀ p ∈ P, p ∈ xOf V H := fun p hp => by rw [hxOf]; exact hc.PleH hp
  have hPc : ∀ p ∈ P, ⁅p, c⁆ ∈ P ⊓ wOf V H := by
    intro p hp
    refine Subgroup.mem_inf.mpr ⟨?_, hcX p (hPX p hp)⟩
    have h1 : c * p⁻¹ * c⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hPN c hcM) _).mp (P.inv_mem hp)
    rw [commutatorElement_def, mul_assoc (p * c), mul_assoc p]
    exact P.mul_mem hp (by simpa [mul_assoc] using h1)
  have hPP : ∀ p ∈ P, ∀ p' ∈ P, ⁅p, p'⁆ ∈ P ⊓ wOf V H := by
    intro p hp p' hp'
    have h1 : ⁅p, p'⁆ ∈ V ⊓ wOf V H := by
      rw [← hcomm']
      exact Subgroup.commutator_mem_commutator hp hp'
    exact Subgroup.mem_inf.mpr ⟨hc.V_le_P (Subgroup.mem_inf.mp h1).1, (Subgroup.mem_inf.mp h1).2⟩
  have hle : ⁅P, Q⁆ ≤ P ⊓ wOf V H := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rcases hQ q hq with hqP | hqP
    · exact hPP p hp q hqP
    ·
      set p' := c⁻¹ * q with hp'
      have hq' : q = c * p' := by rw [hp']; group
      rw [hq']
      have e : ⁅p, c * p'⁆ = ⁅p, c⁆ * (c * ⁅p, p'⁆ * c⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine (P ⊓ wOf V H).mul_mem (hPc p hp) ?_
      have h1 := hPP p hp p' hqP
      have hcW' : c * ⁅p, p'⁆ * c⁻¹ = ⁅p, p'⁆ := by
        rw [hcW _ (Subgroup.mem_inf.mp h1).2, mul_inv_cancel_right]
      rw [hcW']
      exact h1
  have hge : P ⊓ wOf V H ≤ ⁅P, Q⁆ := by
    intro u hu
    obtain ⟨p, hp, hpu⟩ := hcov u hu
    rw [← hpu]
    exact Subgroup.commutator_mem_commutator hp hwQ
  have hEq : ⁅P, Q⁆ = P ⊓ wOf V H := le_antisymm hle hge
  set U := V ⊔ (P ⊓ wOf V H) with hU
  have hUM : U ≤ M := sup_le (fun x hx => by
      have hN : x ∈ Subgroup.normalizer (V : Set G) :=
        (Subgroup.le_normalizer (H := V)) hx
      rw [hc.normalizer_eq] at hN
      exact hN)
    (fun x hx => wOf_le_M cfg (Subgroup.mem_inf.mp hx).2)
  have hMU : M ≤ Subgroup.normalizer (U : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hmV : m ∈ Subgroup.normalizer (V : Set G) := by rw [hc.normalizer_eq]; exact hm
    have hmPW : ∀ y ∈ P ⊓ wOf V H, m * y * m⁻¹ ∈ P ⊓ wOf V H := by
      intro y hy
      rw [← hEq] at hy ⊢
      exact conj_mem_commutator_of_normalizes (hPN m hm) (hQN m hm) hy
    have hmap : (V ⊔ (P ⊓ wOf V H)).map (MulAut.conj m).toMonoidHom ≤ V ⊔ (P ⊓ wOf V H) := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hmV y).mp hy
      · rintro _ ⟨y, hy, rfl⟩
        exact hmPW y hy
    exact hmap ⟨x, hx, rfl⟩
  have hUab : IsMulCommutative ↥U := by
    have hVab : V ≤ Subgroup.centralizer (V : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hc.elemAb.1
    have hWab : P ⊓ wOf V H ≤ Subgroup.centralizer ((P ⊓ wOf V H : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val ((MinCex.wOf_isElemAbelian hc).1.is_comm.comm
        ⟨y, (Subgroup.mem_inf.mp hy).2⟩ ⟨x, (Subgroup.mem_inf.mp hx).2⟩)
    have hVPW : V ≤ Subgroup.centralizer ((P ⊓ wOf V H : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyC : y ∈ Subgroup.centralizer (V : Set G) := by
        have := (Subgroup.mem_inf.mp hy).1
        rw [hc.hP] at this
        exact (Subgroup.mem_inf.mp this).2
      exact (Subgroup.mem_centralizer_iff.mp hyC x hx).symm
    exact isMulCommutative_sup_of_commute hVab hWab hVPW
  have hVU : V ≤ U := le_sup_left
  have hUV : U ≤ V := hc.maxAb.2 ⟨hUM, hMU, hUab⟩ hVU
  obtain ⟨b', hb'⟩ := exists_spForm_eq_one cfg.ne
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, b']
    (by simp only [Fintype.card_fin]; have := cfg.two_le; omega)
  have hya : CaseM.spForm a y = 0 := hy 0
  have hyb : CaseM.spForm b' y = 0 := hy 1
  have hyP : ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) ∈ P ⊓ wOf V H :=
    Subgroup.mem_inf.mpr ⟨(hPiff y).mpr hya, (Additive.toMul (ψ y)).2⟩
  have hyV : ((Additive.toMul (ψ y) : ↥(wOf V H)) : G) ∈ V ⊓ wOf V H :=
    Subgroup.mem_inf.mpr ⟨hUV ((le_sup_right : P ⊓ wOf V H ≤ U) hyP), (Additive.toMul (ψ y)).2⟩
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  rcases l12_two_elt hVWcard haK haG1 _ hyV with h1 | h1
  · apply hy0
    apply psi_injective (ψ := ψ)
    rw [h1, psi_zero]
  · have hyEq : y = a := psi_injective h1
    rw [hyEq, CFSG.Timmesfeld.ARS.CaseM.spForm_comm, hb'] at hyb
    exact one_ne_zero (neg_eq_zero.mp hyb)

theorem mem_Q_of_comm_mem_VW (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T)
    {u : G} (huM : u ∈ M) (huP : ∀ p ∈ P, ⁅u, p⁆ ∈ V ⊓ wOf V H) : u ∈ Q := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hPN : ∀ m ∈ M, m ∈ Subgroup.normalizer (P : Set G) := fun m hm =>
    hc.M_le_normalizer_P hm
  have hPA : ∀ p ∈ P, ∀ x ∈ V ⊓ wOf V H, p * x * p⁻¹ = x := by
    intro p hp x hx
    have hxC : x ∈ Subgroup.centralizer (P : Set G) := by
      rw [hc.centralizer_P_eq]; exact (Subgroup.mem_inf.mp hx).1
    rw [Subgroup.mem_centralizer_iff.mp hxC p hp, mul_inv_cancel_right]
  let K : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ∀ p ∈ P, ⁅m, p⁆ ∈ V ⊓ wOf V H}
      one_mem' := ⟨M.one_mem, fun p _ => by simp⟩
      mul_mem' := by
        rintro m m' ⟨hm, hmP⟩ ⟨hm', hm'P⟩
        refine ⟨M.mul_mem hm hm', fun p hp => ?_⟩
        have e : ⁅m * m', p⁆ = (m * ⁅m', p⁆ * m⁻¹) * ⁅m, p⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, conj_eq_of_mem_VW h11b cfg hm (hm'P p hp)]
        exact (V ⊓ wOf V H).mul_mem (hm'P p hp) (hmP p hp)
      inv_mem' := by
        rintro m ⟨hm, hmP⟩
        refine ⟨M.inv_mem hm, fun p hp => ?_⟩
        have hp' : m⁻¹ * p * m ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (hPN m⁻¹ (M.inv_mem hm)) p).mp hp
          simpa using this
        have h1 := hmP _ hp'
        have e : ⁅m⁻¹, p⁆ = ⁅m, m⁻¹ * p * m⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (V ⊓ wOf V H).inv_mem h1 }
  have huK : u ∈ K := ⟨huM, huP⟩
  have hKM : K ≤ M := fun m hm => hm.1
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    obtain ⟨hmM, hmP⟩ := hm
    refine ⟨M.mul_mem (M.mul_mem hg hmM) (M.inv_mem hg), fun p hp => ?_⟩
    have hp' : g⁻¹ * p * g⁻¹⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hPN g⁻¹ (M.inv_mem hg)) p).mp hp
    have e : ⁅g * m * g⁻¹, p⁆ = g * ⁅m, g⁻¹ * p * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, conj_eq_of_mem_VW h11b cfg hg (hmP _ hp')]
    exact hmP _ hp'
  have hKp : IsPGroup 2 ↥K := by
    intro k
    obtain ⟨hkM, hkP⟩ := k.2
    have hVp : IsPGroup 2 ↥V := hc.isPGroup_V
    obtain ⟨N, hN⟩ := exists_pow_eq_one_of_stabilizes (p := 2) (e := 1) (P := P)
      (A := V ⊓ wOf V H) (C := V) (k := (k : G))
      (fun x hx => by
        have := hc.elemAb.2 x (Subgroup.mem_inf.mp hx).1
        simpa using this)
      (fun x hx => conj_eq_of_mem_VW h11b cfg hkM hx)
      (fun x hx => hkP x hx) (le_of_eq hc.centralizer_P_eq) hVp
    exact ⟨N, Subtype.ext (by simpa using hN)⟩
  have hKQ : K ≤ Q := by
    rw [hc.hQ]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKM hMK hKp
  exact hKQ huK

omit [Finite G] in
noncomputable def toVec (ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H))
    (w : G) : Fin n ⊕ Fin n → GaloisField 2 1 :=
  @dite _ (w ∈ wOf V H) (Classical.propDecidable _)
    (fun h => ψ.symm (Additive.ofMul ⟨w, h⟩)) fun _ => 0

omit [Finite G] in
theorem psi_toVec {w : G} (hw : w ∈ wOf V H) :
    ((Additive.toMul (ψ (toVec ψ w)) : ↥(wOf V H)) : G) = w := by
  unfold toVec
  rw [dif_pos hw, AddEquiv.apply_symm_apply]
  rfl

omit [Finite G] in
theorem toVec_psi (v : Fin n ⊕ Fin n → GaloisField 2 1) :
    toVec ψ ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) = v := by
  apply psi_injective (ψ := ψ)
  rw [psi_toVec (Additive.toMul (ψ v)).2]

omit [Finite G] in
theorem toVec_mul {w w' : G} (hw : w ∈ wOf V H) (hw' : w' ∈ wOf V H) :
    toVec ψ (w * w') = toVec ψ w + toVec ψ w' := by
  apply psi_injective (ψ := ψ)
  rw [psi_toVec ((wOf V H).mul_mem hw hw'), ← psi_mul, psi_toVec hw, psi_toVec hw']

theorem toVec_mem_VW (cfg : GCfg M V Q P H Φ ψ a T) {w : G} (hw : w ∈ V ⊓ wOf V H) :
    toVec ψ w = 0 ∨ toVec ψ w = a := by
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  rcases l12_two_elt hVWcard haK haG1 w hw with h | h
  · left
    rw [h, ← psi_zero (ψ := ψ), toVec_psi]
  · right
    rw [h, toVec_psi]

theorem exists_V_mul_of_comm_psi_mem (h11a : Lemma11aStatement)
    (cfg : GCfg M V Q P H Φ ψ a T) {b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hb : CaseM.spForm a b = 1) {p : G} (hp : p ∈ P)
    (h : ⁅p, ((Additive.toMul (ψ b) : ↥(wOf V H)) : G)⁆ ∈ V ⊓ wOf V H) :
    ∃ y ∈ V, y⁻¹ * p ∈ P ⊓ wOf V H := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨g, -, hpX, hgΦ, u, hu, c, hgu, hcomm⟩ := comm_psi_eq h11a cfg hb hp
  set μ := CaseM.spForm u b + c with hμ
  clear_value μ
  have hVWcard : Nat.card ↥(V ⊓ wOf V H) = 2 := cfg.hyp.module.trans cfg.hyp.q_two
  obtain ⟨haK, haG1⟩ := aG_mem_VW cfg
  obtain ⟨ν, hν⟩ : ∃ ν : GaloisField 2 1, u = ν • a := by
    rw [hcomm] at h
    rcases l12_two_elt hVWcard haK haG1 _ h with h1 | h1
    · rw [← psi_zero (ψ := ψ)] at h1
      have h0 := psi_injective h1
      refine ⟨μ, ?_⟩
      calc u = u + (u + μ • a) := by rw [h0, add_zero]
        _ = (u + u) + μ • a := by abel
        _ = μ • a := by rw [gf2_vec_add_self, zero_add]
    · have h0 := psi_injective h1
      refine ⟨μ + 1, ?_⟩
      calc u = u + (u + μ • a) + a := by rw [h0, add_assoc, gf2_vec_add_self, add_zero]
        _ = (u + u) + (μ • a + a) := by abel
        _ = (μ + 1) • a := by rw [gf2_vec_add_self, zero_add, add_smul, one_smul]
  have hgt : SpExtras.mat n (GaloisField 2 1) g = CaseM.spTrans a c := by
    refine Matrix.ext_iff_mulVec.2 fun x => ?_
    rw [hgu x, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, hν,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', smul_smul,
      mul_comm (CaseM.spForm a x) ν, add_assoc x, gf2_vec_add_self, add_zero]
  have hgT : g ∈ T := (cfg.trans.1 g).mpr ⟨c, hgt⟩
  have hxV : xToXbar hVH ⟨p, hpX⟩ ∈ Vy V H := by
    rw [← cfg.point]
    refine Subgroup.mem_map.mpr ⟨g, hgT, ?_⟩
    rw [← hgΦ]
    exact Φ.apply_symm_apply _
  have hxV' : ((xToXbar hVH ⟨p, hpX⟩ : Xbar V H) : Hbar V H) ∈ barOf V H V :=
    Subgroup.mem_subgroupOf.mp hxV
  obtain ⟨y, hyV, hyp⟩ := mem_barOf_iff.mp hxV'
  rw [coe_xToXbar] at hyp
  have hw : (y : G)⁻¹ * p ∈ wOf V H := by
    have h1 : piBar V H (y⁻¹ * Subgroup.inclusion (xOf_le_H hVH) ⟨p, hpX⟩) = 1 := by
      rw [map_mul, map_inv, hyp, inv_mul_cancel]
    exact (piBar_eq_one_iff _).mp h1
  have hwP : (y : G)⁻¹ * p ∈ P := P.mul_mem (P.inv_mem (hc.V_le_P hyV)) hp
  exact ⟨y, hyV, Subgroup.mem_inf.mpr ⟨hwP, hw⟩⟩

theorem comm_mul_eq (h11b : Lemma11bStatement) (cfg : GCfg M V Q P H Φ ψ a T) {p p' z : G}
    (hp : p ∈ P) (hz' : ⁅p', z⁆ ∈ P ⊓ wOf V H) (hz : ⁅p, z⁆ ∈ wOf V H) :
    ∃ r ∈ V ⊓ wOf V H, ⁅p * p', z⁆ = ⁅p', z⁆ * ⁅p, z⁆ * r := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  obtain ⟨hcomm', -, -⟩ := h11b G M V Q P H cfg.hyp cfg.centre cfg.iw
  have hr : ⁅p, ⁅p', z⁆⁆ ∈ V ⊓ wOf V H := by
    rw [← hcomm']
    exact Subgroup.commutator_mem_commutator hp (Subgroup.mem_inf.mp hz').1
  refine ⟨⁅p, ⁅p', z⁆⁆, hr, ?_⟩
  have hWab := (MinCex.wOf_isElemAbelian hc).1
  have hcomm : ∀ x ∈ wOf V H, ∀ y ∈ wOf V H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hWab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have e : ⁅p * p', z⁆ = ⁅p, ⁅p', z⁆⁆ * ⁅p', z⁆ * ⁅p, z⁆ := by
    simp only [commutatorElement_def]
    group
  have hrW := (Subgroup.mem_inf.mp hr).2
  have hz'W := (Subgroup.mem_inf.mp hz').2
  rw [e, hcomm _ hrW _ hz'W, mul_assoc, hcomm _ hrW _ hz, ← mul_assoc]

end Cfg

end CFSG.RankThree.GF2n.Tim79a.Gamma
