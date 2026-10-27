module

public import CFSG.RankThree.GF2n.Tim79a34BigModel

import CFSG.RankThree.GF2n.Tim79a34BigRbarIso
public import CFSG.RankThree.GF2n.Tim79a34SpRad

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

theorem BigEndHyp.natCard_P_inf_wOf [Finite G] (h : BigEndHyp M V Q P H)
    (hf : 2 ^ f = qBar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)) :
    Nat.card ↥(P ⊓ wOf V H) = qBar V H ^ (2 * n - 1) := by
  have hq4 : 4 ≤ qBar V H := h.q_big
  have hqpos : 0 < qBar V H := by omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [← hf] at hq4
    norm_num at hq4
  have hFcard : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  have hWcard : Nat.card ↥(wOf V H) = qBar V H ^ (2 * n) := by
    have h1 : Nat.card (Fin n ⊕ Fin n → GaloisField 2 f) = Nat.card ↥(wOf V H) :=
      Nat.card_congr (ψ.toEquiv.trans Additive.toMul)
    rw [← h1, Nat.card_fun, Nat.card_sum, hFcard]
    simp [two_mul, Nat.card_eq_fintype_card]
  have hsplit := twistedWSplit_holds G M V Q P H h.setup h.concl
  rw [hWcard, h.module] at hsplit
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      subst h0
      have h1 : Nat.card ↥(P ⊓ wOf V H) * qBar V H = 1 := by
        simpa using hsplit.symm
      have hge := Nat.le_mul_of_pos_left (qBar V H)
        (Nat.card_pos (α := ↥(P ⊓ wOf V H)))
      rw [h1] at hge
      omega
    · exact hpos
  have h2 : qBar V H ^ (2 * n) = qBar V H ^ (2 * n - 1) * qBar V H := by
    rw [← pow_sub_mul_pow (qBar V H) (m := 1) (n := 2 * n) (by omega), pow_one]
  have h3 : Nat.card ↥(P ⊓ wOf V H) * qBar V H = qBar V H ^ (2 * n - 1) * qBar V H := by
    rw [← hsplit, h2]
  exact Nat.eq_of_mul_eq_mul_right hqpos h3

private theorem BigEndHyp.ncard_spForm_eq_zero (h : BigEndHyp M V Q P H)
    (hf : 2 ^ f = qBar V H) (ha : a ≠ 0) :
    Set.ncard {w : Fin n ⊕ Fin n → GaloisField 2 f | CaseM.spForm a w = 0} =
      qBar V H ^ (2 * n - 1) := by
  have hq4 : 4 ≤ qBar V H := h.q_big
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [← hf] at hq4
    norm_num at hq4
  have hFcard : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  have hKcard : Nat.card ↥(LinearMap.ker (spFormL a)) = qBar V H ^ (2 * n - 1) := by
    rw [natCard_ker_spFormL ha, hFcard]
  rw [← Nat.card_coe_set_eq, ← hKcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w =>
    (LinearMap.mem_ker (f := spFormL a) (y := w)).symm)

private theorem BigEndHyp.ncard_psi_mem_P [Finite G] (h : BigEndHyp M V Q P H)
    (hf : 2 ^ f = qBar V H)
    (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)) :
    Set.ncard {w : Fin n ⊕ Fin n → GaloisField 2 f |
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} = qBar V H ^ (2 * n - 1) := by
  have hPW : Nat.card ↥(P ⊓ wOf V H) = qBar V H ^ (2 * n - 1) :=
    h.natCard_P_inf_wOf hf ψ
  have hinj : Function.Injective (fun w : Fin n ⊕ Fin n → GaloisField 2 f =>
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)) := by
    intro w w' h
    apply ψ.injective
    apply Additive.toMul.injective
    exact Subtype.ext h
  have himg : (fun w : Fin n ⊕ Fin n → GaloisField 2 f =>
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)) ''
      {w | ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} =
        ((P ⊓ wOf V H : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨hw, (Additive.toMul (ψ w)).2⟩
    · intro hx
      have hx' : x ∈ P ⊓ wOf V H := hx
      have hxW : x ∈ wOf V H := (Subgroup.mem_inf.mp hx').2
      refine ⟨ψ.symm (Additive.ofMul ⟨x, hxW⟩), ?_, ?_⟩
      · show ((Additive.toMul (ψ (ψ.symm (Additive.ofMul ⟨x, hxW⟩))) : ↥(wOf V H)) : G) ∈ P
        rw [AddEquiv.apply_symm_apply]
        exact (Subgroup.mem_inf.mp hx').1
      · show ((Additive.toMul (ψ (ψ.symm (Additive.ofMul ⟨x, hxW⟩))) : ↥(wOf V H)) : G) = x
        rw [AddEquiv.apply_symm_apply]
        rfl
  have h1 := Set.ncard_image_of_injective
    {w : Fin n ⊕ Fin n → GaloisField 2 f | ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} hinj
  rw [himg] at h1
  rw [← h1, ← hPW]
  exact (Nat.card_coe_set_eq _).symm

private theorem BigEndHyp.psi_mem_P_imp_spForm_eq_zero [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (w : Fin n ⊕ Fin n → GaloisField 2 f)
    (hw : ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P) : CaseM.spForm a w = 0 := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨v, hvV, hvW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hvV
  have hxmem : xToXbar hVH ⟨v, hvX⟩ ∈ Vy V H :=
    Subgroup.mem_subgroupOf.mpr
      (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩, hvV, rfl⟩)
  have hmemT : xToXbar hVH ⟨v, hvX⟩ ∈ T.map Φ.toMonoidHom := by
    rw [hTV]
    exact hxmem
  have ht_mem : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ∈ T := Subgroup.mem_map_equiv.mp hmemT
  have ht1 : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ≠ 1 := by
    intro h1
    apply hvW
    have h2 : xToXbar hVH ⟨v, hvX⟩ = 1 := by
      have h3 := Φ.apply_symm_apply (xToXbar hVH ⟨v, hvX⟩)
      rw [h1, map_one] at h3
      exact h3.symm
    have h4 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩) = 1 := by
      rw [← coe_xToXbar hVH ⟨v, hvX⟩, h2, Subgroup.coe_one]
    exact (piBar_eq_one_iff _).mp h4
  obtain ⟨μ, hμ, hmat⟩ : ∃ μ : GaloisField 2 f,
      μ ≠ 0 ∧ SpExtras.mat n (GaloisField 2 f)
        (Φ.symm (xToXbar hVH ⟨v, hvX⟩)) = CaseM.spTrans a μ := by
    obtain ⟨c, hcmat⟩ := (hT.1 (Φ.symm (xToXbar hVH ⟨v, hvX⟩))).1 ht_mem
    refine ⟨c, ?_, hcmat⟩
    rintro rfl
    apply ht1
    apply SpExtras.mat_injective
    rw [hcmat, ModelRank.spTrans_zero, map_one]
  have key := hNat.equiv ⟨v, hvX⟩ w
  have hcomm := hc.commute_of_mem_P hw hvV
  have hval : ((⟨v, hvX⟩ : ↥(xOf V H)) : G) = v := rfl
  rw [hval, hcomm, mul_assoc, mul_inv_cancel, mul_one] at key
  have hσw := ψ.injective (Additive.toMul.injective (Subtype.ext key))
  rw [hmat, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec] at hσw
  have h0 : (μ * CaseM.spForm a w) • a = 0 := by
    have h5 := congrArg (fun y => y - w) hσw
    simpa using h5
  rcases smul_eq_zero.mp h0 with h | h
  · exact (mul_eq_zero.mp h).resolve_left hμ
  · exact absurd h ha

theorem BigEndHyp.psi_mem_P_iff [Finite G] (h : BigEndHyp M V Q P H)
    (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H (Φ := Φ) ψ)
    (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T)
    (hTV : T.map Φ.toMonoidHom = Vy V H)
    (w : Fin n ⊕ Fin n → GaloisField 2 f) :
    ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P ↔ CaseM.spForm a w = 0 := by
  have hsub : {w : Fin n ⊕ Fin n → GaloisField 2 f |
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} ⊆ {w | CaseM.spForm a w = 0} :=
    fun w hw => h.psi_mem_P_imp_spForm_eq_zero hNat ha hT hTV w hw
  have hSncard := h.ncard_spForm_eq_zero hf ha
  have hLncard := h.ncard_psi_mem_P hf ψ
  have hLS := Set.eq_of_subset_of_ncard_le hsub (by rw [hSncard, hLncard])
  exact Set.ext_iff.mp hLS w

theorem BigEndHyp.rbar_eq_map_spRad (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H) :
    Rbar V H P = (spRad a).map Φ.toMonoidHom := by
  have hπinj : Function.Injective (projZ V H) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ Subgroup.center (Xbar V H) := (QuotientGroup.eq_one_iff x).mp hx
    rw [hZ] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hΨbij : Function.Bijective ((projZ V H).comp Φ.toMonoidHom) :=
    ⟨hπinj.comp Φ.injective,
      (QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H))).comp Φ.surjective⟩
  have hVZ : VZ V H = T.map ((projZ V H).comp Φ.toMonoidHom) := by
    unfold VZ
    rw [← hTV, Subgroup.map_map]
  have hnorm : Subgroup.normalizer ((T.map ((projZ V H).comp Φ.toMonoidHom) :
      Subgroup (XbarZ V H)) : Set (XbarZ V H)) =
      (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f)))).map
        ((projZ V H).comp Φ.toMonoidHom) :=
    (Subgroup.map_normalizer_eq_of_bijective T hΨbij).symm
  have hpc : pCoreOf 2 ((Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f)))).map
      ((projZ V H).comp Φ.toMonoidHom)) =
      (pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f))))).map
        ((projZ V H).comp Φ.toMonoidHom) :=
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulEquiv.ofBijective _ hΨbij) _
  have hcore : pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f)))) =
      spRad a :=
    spCoreStmt_holds n (GaloisField 2 f) ha hT
  have hRt : Rtilde V H P = (spRad a).map ((projZ V H).comp Φ.toMonoidHom) := by
    have hP' : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :=
      h.tilde
    rw [hP', hVZ, hnorm, hpc, hcore]
  refine Subgroup.map_injective hπinj ?_
  rw [Subgroup.map_map]
  exact hRt

private theorem BigEndHyp.cPbar_centralizes_wOf (h : BigEndHyp M V Q P H) {c : G}
    (hc : c ∈ cPbar V H P) {w : G} (hw : w ∈ wOf V H) : c * w = w * c :=
  h.concl.2.2.comm (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hw)

private theorem BigEndHyp.exists_mem_xOf_mul_cPbar [Finite G] (h : BigEndHyp M V Q P H) {p : G}
    (hp : p ∈ P) :
    ∃ x ∈ xOf V H, ∃ c ∈ cPbar V H P, x * c = p := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcH : cPbar V H P ≤ H := inf_le_left.trans hc.PleH
  let Xh : Subgroup ↥H := (xOf V H).subgroupOf H
  let Ch : Subgroup ↥H := (cPbar V H P).subgroupOf H
  haveI : Xh.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (xOf_le_H hVH)).2 (H_le_normalizer_xOf V H)
  have hsup : Xh ⊔ Ch = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (xOf_le_H hVH) hcH, h.concl.2.1, Subgroup.subgroupOf_self]
  have hmem : (⟨p, hc.PleH hp⟩ : ↥H) ∈ Xh ⊔ Ch := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, c, hcx, hxc⟩ := (Subgroup.mem_sup_of_normal_left (s := Xh) (t := Ch)).mp hmem
  exact ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, (c : G), Subgroup.mem_subgroupOf.mp hcx,
    by simpa using congrArg Subtype.val hxc⟩

private theorem BigEndHyp.psi_mat_symm_xToXbar_spec [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) {p x c : G}
    (hxX : x ∈ xOf V H) (hcC : c ∈ cPbar V H P) (hxc : x * c = p)
    (v : Fin n ⊕ Fin n → GaloisField 2 f) :
    ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f)
      (Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H ⟨x, hxX⟩)) *ᵥ v)) :
        ↥(wOf V H)) : G) = p * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * p⁻¹ := by
  have hx := hNat.equiv ⟨x, hxX⟩ v
  have hcw : c * (((Additive.toMul (ψ v) : ↥(wOf V H)) : G)) * c⁻¹ =
      ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) := by
    rw [h.cPbar_centralizes_wOf hcC (Additive.toMul (ψ v)).2, mul_assoc, mul_inv_cancel,
      mul_one]
  rw [← hxc, hx]
  calc x * (((Additive.toMul (ψ v) : ↥(wOf V H)) : G)) * x⁻¹
      = x * (c * (((Additive.toMul (ψ v) : ↥(wOf V H)) : G)) * c⁻¹) * x⁻¹ := by rw [hcw]
    _ = (x * c) * (((Additive.toMul (ψ v) : ↥(wOf V H)) : G)) * (x * c)⁻¹ := by group

private theorem BigEndHyp.exists_bigPAct [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (p : ↥P) :
    ∃ s : ↥(StatedSp n (GaloisField 2 f)),
      ∀ v, ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) s *ᵥ v)) :
        ↥(wOf V H)) : G) = (p : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) *
          (p : G)⁻¹ := by
  obtain ⟨x, hxX, c, hcC, hxc⟩ := h.exists_mem_xOf_mul_cPbar p.2
  exact ⟨Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H ⟨x, hxX⟩),
    fun v => h.psi_mat_symm_xToXbar_spec hNat hxX hcC hxc v⟩

private theorem BigEndHyp.bigPAct_unique {p : ↥P}
    {s s' : ↥(StatedSp n (GaloisField 2 f))}
    (hs : ∀ v, ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) s *ᵥ v)) :
      ↥(wOf V H)) : G) = (p : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (p : G)⁻¹)
    (hs' : ∀ v, ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) s' *ᵥ v)) :
      ↥(wOf V H)) : G) = (p : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (p : G)⁻¹) :
    s = s' := by
  refine eq_of_mat_mulVec_eq fun v => ?_
  apply ψ.injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [hs v, hs' v]

theorem BigEndHyp.existsUnique_bigPAct [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (p : ↥P) :
    ∃! s : ↥(StatedSp n (GaloisField 2 f)),
      ∀ v, ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) s *ᵥ v)) :
        ↥(wOf V H)) : G) = (p : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) *
          (p : G)⁻¹ := by
  obtain ⟨s, hs⟩ := h.exists_bigPAct hNat p
  exact ⟨s, hs, fun s' hs' => bigPAct_unique hs' hs⟩

noncomputable def BigEndHyp.bigPAct [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) :
    ↥P →* ↥(StatedSp n (GaloisField 2 f)) :=
  MonoidHom.mk' (fun p => Classical.choose (h.existsUnique_bigPAct hNat p)) (by
    intro p q
    refine (h.existsUnique_bigPAct hNat (p * q)).unique ?_ ?_
    · exact (h.existsUnique_bigPAct hNat (p * q)).choose_spec.1
    · intro v
      have hp := (h.existsUnique_bigPAct hNat p).choose_spec.1
      have hq := (h.existsUnique_bigPAct hNat q).choose_spec.1
      rw [map_mul, ← Matrix.mulVec_mulVec, hp, hq, Subgroup.coe_mul]
      group)

theorem BigEndHyp.bigPAct_spec [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (p : ↥P) :
    ∀ v, ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) (h.bigPAct hNat p) *ᵥ v)) :
      ↥(wOf V H)) : G) = (p : G) * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (p : G)⁻¹ :=
  (h.existsUnique_bigPAct hNat p).choose_spec.1

private theorem BigEndHyp.bigPAct_eq_of_eq_mul [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) {p : ↥P} {x c : G}
    (hxX : x ∈ xOf V H) (hcC : c ∈ cPbar V H P) (hxc : x * c = (p : G)) :
    h.bigPAct hNat p = Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H ⟨x, hxX⟩) := by
  apply (h.existsUnique_bigPAct hNat p).unique (h.bigPAct_spec hNat p)
  intro v
  exact h.psi_mat_symm_xToXbar_spec hNat hxX hcC hxc v

theorem BigEndHyp.bigPAct_mem_spRad [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H) (p : ↥P) :
    h.bigPAct hNat p ∈ spRad a := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨x, hxX, c, hcC, hxc⟩ := h.exists_mem_xOf_mul_cPbar p.2
  have hxP : x ∈ P := by
    have hx_eq : x = (p : G) * c⁻¹ := by rw [← hxc]; group
    rw [hx_eq]
    exact P.mul_mem p.2 (P.inv_mem (Subgroup.mem_inf.mp hcC).1)
  have hxbar : xToXbar hVH ⟨x, hxX⟩ ∈ Rbar V H P := by
    rw [mem_Rbar, coe_xToXbar]
    exact mem_barOf_iff.mpr
      ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨x, hxX⟩, hxP, rfl⟩
  rw [h.rbar_eq_map_spRad hZ ha hT hTV] at hxbar
  have hxsp : Φ.symm (xToXbar hVH ⟨x, hxX⟩) ∈ spRad a := Subgroup.mem_map_equiv.mp hxbar
  rw [h.bigPAct_eq_of_eq_mul hNat hxX hcC hxc]
  exact hxsp

theorem BigEndHyp.bigPAct_eq_of_mem_xOf [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) {p : ↥P}
    (hp : (p : G) ∈ xOf V H) :
    h.bigPAct hNat p = Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H ⟨(p : G), hp⟩) := by
  apply (h.existsUnique_bigPAct hNat p).unique (h.bigPAct_spec hNat p)
  intro v
  exact hNat.equiv ⟨(p : G), hp⟩ v

theorem BigEndHyp.bigPAct_eq_one_iff [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (p : ↥P) :
    h.bigPAct hNat p = 1 ↔ (p : G) ∈ wOf V H ⊔ cPbar V H P := by
  constructor
  · intro h1
    obtain ⟨x, hxX, c, hcC, hxc⟩ := h.exists_mem_xOf_mul_cPbar p.2
    have hpcomm : ∀ w ∈ wOf V H, (p : G) * w = w * (p : G) := by
      intro w hw
      obtain ⟨v, hv⟩ := ψ.surjective (Additive.ofMul ⟨w, hw⟩)
      have hψv : ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) = w := by
        rw [hv]
        rfl
      have hs := h.bigPAct_spec hNat p v
      rw [h1, map_one, Matrix.one_mulVec, hψv] at hs
      have hpw : (p : G) * w * (p : G)⁻¹ = w := hs.symm
      calc (p : G) * w = ((p : G) * w * (p : G)⁻¹) * (p : G) := by group
        _ = w * (p : G) := by rw [hpw]
    have hxcomm : ∀ w ∈ wOf V H, x * w = w * x := by
      intro w hw
      have hcw : c * w = w * c := h.cPbar_centralizes_wOf hcC hw
      have hcinv : c⁻¹ * w = w * c⁻¹ := by
        calc c⁻¹ * w = c⁻¹ * (w * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * w) * c⁻¹ := by rw [← hcw]
          _ = w * c⁻¹ := by group
      have hx_eq : x = (p : G) * c⁻¹ := by rw [← hxc]; group
      calc x * w = ((p : G) * c⁻¹) * w := by rw [hx_eq]
        _ = (p : G) * (c⁻¹ * w) := by group
        _ = (p : G) * (w * c⁻¹) := by rw [hcinv]
        _ = ((p : G) * w) * c⁻¹ := by group
        _ = (w * (p : G)) * c⁻¹ := by rw [hpcomm w hw]
        _ = w * ((p : G) * c⁻¹) := by group
        _ = w * x := by rw [hx_eq]
    have hxW : x ∈ wOf V H := h.mem_wOf_of_commute hZ hxX hxcomm
    have hmem : x * c ∈ wOf V H ⊔ cPbar V H P := Subgroup.mul_mem_sup hxW hcC
    rwa [hxc] at hmem
  · intro hp
    apply (h.existsUnique_bigPAct hNat p).unique (h.bigPAct_spec hNat p)
    intro v
    rw [map_one, Matrix.one_mulVec]
    have hcomm := h.concl.2.2.comm hp
      (Subgroup.mem_sup_left (Additive.toMul (ψ v)).2)
    rw [hcomm]
    group

private theorem BigEndHyp.mem_sup_of_bigPAct_mem_T [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hTV : T.map Φ.toMonoidHom = Vy V H) (p : ↥P)
    (hTmem : h.bigPAct hNat p ∈ T) : (p : G) ∈ V ⊔ Eof V H P := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨x, hxX, c, hcC, hxc⟩ := h.exists_mem_xOf_mul_cPbar p.2
  have hbig := h.bigPAct_eq_of_eq_mul hNat hxX hcC hxc
  have hxT : Φ (h.bigPAct hNat p) ∈ Vy V H := by
    have h1 := Subgroup.mem_map_of_mem Φ.toMonoidHom hTmem
    rwa [hTV] at h1
  rw [hbig, Φ.apply_symm_apply] at hxT
  obtain ⟨v, hvV, hvx⟩ := bigRI_mem_Vy hVH hxT
  have hker : xToXbar hVH (v⁻¹ * ⟨x, hxX⟩) = 1 := by
    rw [map_mul, map_inv, hvx, inv_mul_cancel]
  have hwW : ((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) ∈ wOf V H := by
    have h1 : ((xToXbar hVH (v⁻¹ * ⟨x, hxX⟩) : Xbar V H) : Hbar V H) = 1 := by
      rw [hker]
      rfl
    rw [coe_xToXbar] at h1
    exact (piBar_eq_one_iff _).mp h1
  have hx_eq : x = (v : G) * ((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hw_eq : ((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) = (v : G)⁻¹ * x := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  have hwP : ((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) * c ∈ P := by
    have h_eq : ((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) * c = (v : G)⁻¹ * (p : G) := by
      rw [hw_eq, mul_assoc, hxc]
    rw [h_eq]
    exact P.mul_mem (P.inv_mem (hc.V_le_P hvV)) p.2
  have hE : ((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) * c ∈ Eof V H P :=
    Subgroup.mem_inf.mpr ⟨hwP, Subgroup.mul_mem_sup hwW hcC⟩
  have hp_eq : (p : G) = (v : G) * (((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) * c) := by
    calc (p : G) = x * c := hxc.symm
      _ = ((v : G) * ((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G)) * c := by
        nth_rewrite 1 [hx_eq]
        rfl
      _ = (v : G) * (((v⁻¹ * ⟨x, hxX⟩ : ↥(xOf V H)) : G) * c) := by group
  rw [hp_eq]
  exact Subgroup.mul_mem_sup hvV hE

private theorem BigEndHyp.bigPAct_mem_T_of_mem_sup [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hTV : T.map Φ.toMonoidHom = Vy V H) (p : ↥P)
    (hp : (p : G) ∈ V ⊔ Eof V H P) : h.bigPAct hNat p ∈ T := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hEofP : Eof V H P ≤ P := inf_le_left
  let Vp : Subgroup ↥P := V.subgroupOf P
  let Ep : Subgroup ↥P := (Eof V H P).subgroupOf P
  have hPc : P ≤ Subgroup.centralizer (V : Set G) := by
    rw [hc.hP]
    exact inf_le_right
  haveI : Vp.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hc.V_le_P).2
      (hPc.trans (Subgroup.centralizer_le_normalizer (V : Set G)))
  have hsup : Vp ⊔ Ep = (V ⊔ Eof V H P).subgroupOf P := by
    rw [Subgroup.subgroupOf_sup hc.V_le_P hEofP]
  have hmem : (⟨(p : G), p.2⟩ : ↥P) ∈ Vp ⊔ Ep := by
    rw [hsup]
    exact Subgroup.mem_subgroupOf.mpr hp
  obtain ⟨v, hv, e, he, hve⟩ := (Subgroup.mem_sup_of_normal_left (s := Vp) (t := Ep)).mp hmem
  have hvV : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
  have heE : (e : G) ∈ Eof V H P := Subgroup.mem_subgroupOf.mp he
  have hvX : (v : G) ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hvV
  have hvT : h.bigPAct hNat v ∈ T := by
    rw [h.bigPAct_eq_of_mem_xOf hNat hvX]
    refine Subgroup.mem_map_equiv.mp ?_
    rw [hTV]
    exact Subgroup.mem_subgroupOf.mpr
      (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨(v : G), hvX⟩, hvV, rfl⟩)
  have he1 : h.bigPAct hNat e = 1 :=
    (h.bigPAct_eq_one_iff hNat hZ e).mpr (Subgroup.mem_inf.mp heE).2
  have hp_eq : p = v * e := hve.symm
  rw [hp_eq, map_mul, he1, mul_one]
  exact hvT

theorem BigEndHyp.bigPAct_mem_T_iff [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hTV : T.map Φ.toMonoidHom = Vy V H) (p : ↥P) :
    h.bigPAct hNat p ∈ T ↔ (p : G) ∈ V ⊔ Eof V H P :=
  ⟨h.mem_sup_of_bigPAct_mem_T hNat hTV p, h.bigPAct_mem_T_of_mem_sup hNat hZ hTV p⟩

theorem BigEndHyp.exists_bigPAct_eq_of_mem_T [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hTV : T.map Φ.toMonoidHom = Vy V H)
    {t : ↥(StatedSp n (GaloisField 2 f))} (ht : t ∈ T) :
    ∃ v : G, ∃ hv : v ∈ V, h.bigPAct hNat ⟨v, h.setup.mc.toMinCex.V_le_P hv⟩ = t := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have htVy : Φ t ∈ Vy V H := by
    have h1 := Subgroup.mem_map_of_mem Φ.toMonoidHom ht
    rwa [hTV] at h1
  obtain ⟨v, hvV, hvx⟩ := bigRI_mem_Vy hVH htVy
  refine ⟨(v : G), hvV, ?_⟩
  rw [h.bigPAct_eq_of_mem_xOf hNat v.2]
  rw [hvx]
  exact Φ.symm_apply_apply t

theorem BigEndHyp.conj_mem_P_of_mem_M [Finite G] (h : BigEndHyp M V Q P H) {y : G}
    (hyM : y ∈ M) {p : G} (hp : p ∈ P) : y * p * y⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp (h.setup.mc.toMinCex.M_le_normalizer_P hyM) p).mp hp

theorem BigEndHyp.bigPAct_conj [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) {y : ↥(xOf V H)}
    (hyM : (y : G) ∈ M) (p : ↥P) :
    h.bigPAct hNat ⟨(y : G) * (p : G) * (y : G)⁻¹,
        h.conj_mem_P_of_mem_M hyM p.2⟩ =
      Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H y) * h.bigPAct hNat p *
        (Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H y))⁻¹ := by
  have hVH : V ≤ H := h.setup.mc.toMinCex.V_le_H
  set sy : ↥(StatedSp n (GaloisField 2 f)) :=
    Φ.symm (xToXbar hVH y) with hsydef
  have hsyinv : Φ.symm (xToXbar hVH y⁻¹) = sy⁻¹ := by
    rw [map_inv, map_inv]
  have hsy : ∀ v, ((Additive.toMul (ψ (SpExtras.mat n (GaloisField 2 f) sy⁻¹ *ᵥ v)) :
      ↥(wOf V H)) : G) = (y : G)⁻¹ * ((Additive.toMul (ψ v) : ↥(wOf V H)) : G) * (y : G) := by
    intro v
    simpa [hsyinv] using hNat.equiv y⁻¹ v
  apply (h.existsUnique_bigPAct hNat
    ⟨(y : G) * (p : G) * (y : G)⁻¹, h.conj_mem_P_of_mem_M hyM p.2⟩).unique
    (h.bigPAct_spec hNat _)
  intro v
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hNat.equiv y]
  rw [h.bigPAct_spec hNat p]
  rw [hsy]
  group

theorem BigEndHyp.exists_lift_normalizer_T [Finite G] (h : BigEndHyp M V Q P H)
    (hTV : T.map Φ.toMonoidHom = Vy V H)
    {g : ↥(StatedSp n (GaloisField 2 f))}
    (hg : g ∈ Subgroup.normalizer (T : Set ↥(StatedSp n (GaloisField 2 f)))) :
    ∃ y : ↥(xOf V H), (y : G) ∈ M ∧ Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H y) = g := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨y, hy⟩ := xToXbar_surjective hVH (Φ g)
  have hconjT : conjSubgroup g T = T := mem_normalizer_iff_conjSubgroup_eq.mp hg
  have hconj : conjSubgroup (Φ g) (Vy V H) = Vy V H := by
    calc conjSubgroup (Φ g) (Vy V H) = conjSubgroup (Φ g) (T.map Φ.toMonoidHom) := by
          rw [hTV]
      _ = (conjSubgroup g T).map Φ.toMonoidHom := conjSubgroup_map_hom Φ.toMonoidHom T g
      _ = T.map Φ.toMonoidHom := by rw [hconjT]
      _ = Vy V H := hTV
  set A : Subgroup (Hbar V H) := barOf V H V with hA
  set K : Subgroup (Hbar V H) := barOf V H (xOf V H) with hK
  have hAle : A ≤ K := barOf_mono (le_xOf (V_mem_omegaOf V H))
  have hconj_le : conjSubgroup (Φ g : Hbar V H) A ≤ K := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have hxK : (Φ g : Hbar V H) * ((Φ g : Hbar V H)⁻¹ * x * (Φ g : Hbar V H)) *
        (Φ g : Hbar V H)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (Φ g).2 (hAle hx)) (K.inv_mem (Φ g).2)
    rwa [show (Φ g : Hbar V H) * ((Φ g : Hbar V H)⁻¹ * x * (Φ g : Hbar V H)) *
        (Φ g : Hbar V H)⁻¹ = x by group] at hxK
  have hbarK : (conjSubgroup (Φ g : Hbar V H) A).subgroupOf K = A.subgroupOf K := by
    rw [subgroupOf_conjSubgroup]
    exact hconj
  have hbarEq : conjSubgroup (Φ g : Hbar V H) A = A := by
    have hEqInf := (Subgroup.subgroupOf_inj (H₁ := conjSubgroup (Φ g : Hbar V H) A)
      (H₂ := A) (K := K)).mp hbarK
    rwa [inf_eq_left.mpr hconj_le, inf_eq_left.mpr hAle] at hEqInf
  have hpi : piBar V H (Subgroup.inclusion (xOf_le_H hVH) y) = (Φ g : Hbar V H) := by
    rw [← coe_xToXbar hVH y, hy]
  have hbar : barOf V H (conjSubgroup (y : G) V) = barOf V H V := by
    have hbar' : barOf V H (conjSubgroup (y : G) V) =
        conjSubgroup (piBar V H (Subgroup.inclusion (xOf_le_H hVH) y)) (barOf V H V) :=
      (conjSubgroup_piBar_barOf (Subgroup.inclusion (xOf_le_H hVH) y) V).symm
    rw [hbar', hpi]
    exact hbarEq
  have hyV : conjSubgroup (y : G) V = V :=
    hc.conjSubgroup_eq_of_barOf_eq (xOf_le_H hVH y.2) hbar
  refine ⟨y, ?_, ?_⟩
  · rw [← hc.normalizer_eq]
    exact mem_normalizer_iff_conjSubgroup_eq.mpr hyV
  · rw [hy]
    exact Φ.symm_apply_apply g

end CFSG.RankThree.GF2n.Tim79a
