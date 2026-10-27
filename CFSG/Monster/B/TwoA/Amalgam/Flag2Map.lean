module

public import CFSG.Monster.B.TwoA.Amalgam.Flag2Plane
public import CFSG.Monster.B.TwoA.Amalgam.Kernels

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Classical.ThreePlane CFSG.Monster.B.TwoA.Unitary.LinThree
  CFSG.Monster.VisQuot CFSG.Monster.Lifts CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.Visible
open scoped Pointwise

attribute [local instance] vAction restAction

@[expose] def piTwo :
    Pc 1 →* Equiv.Perm Vsharp × SigmaL3 :=
  ((MulAction.toPermHom Ntwo Vsharp).comp Par2.inclH).prod (psi.toMonoidHom.comp Par2.psiH)

theorem coe_piTwo_fst
    (h : Pc 1) (v : Vsharp) :
    (((piTwo h).1 v : Vsharp) : Dfull) = (h : Dfull) * (v : Dfull) * (h : Dfull)⁻¹ := rfl

theorem piTwo_snd
    (h : Pc 1) : (piTwo h).2 = psi (Par2.psiH h) := rfl

theorem mem_Ntwo_of_Pc_one
    (h : Pc 1) : (h : Dfull) ∈ Ntwo := Par2.H2_le_Ntwo h.2

theorem mul_cQ_of_Pc_one
    (h : Pc 1) : (h : Dfull) * cQ = cQ * h :=
  Subgroup.mem_centralizer_singleton_iff.1 (Pc_le_centralizer 1 h.2)

theorem bigPhi_fst
    (h : Par2.H2) :
    (Par2.bigPhi h).1 = Equiv.permCongrHom vsharpEquiv (piTwo h).1 :=
  twoCoreEquiv_snd (Par2.inclH h)

theorem bigPhi_snd
    (h : Par2.H2) : (Par2.bigPhi h).2 = (piTwo h).2 := rfl

theorem piTwo_surjective :
    Function.Surjective piTwo := by
  rintro ⟨σ, s⟩
  obtain ⟨h, hh⟩ := Par2.bigPhi_surjective (Equiv.permCongrHom vsharpEquiv σ, s)
  refine ⟨h, Prod.ext ?_ ((bigPhi_snd h).symm.trans (congrArg Prod.snd hh))⟩
  exact (Equiv.permCongrHom vsharpEquiv).injective ((bigPhi_fst h).symm.trans
    (congrArg Prod.fst hh))

theorem piTwo_eq_one_iff
    (h : Par2.H2) : piTwo h = 1 ↔ Par2.bigPhi h = 1 := by
  constructor
  · intro e
    refine Prod.ext ((bigPhi_fst h).trans ?_) ((bigPhi_snd h).trans (congrArg Prod.snd e))
    rw [show (piTwo h).1 = 1 from congrArg Prod.fst e, map_one]
    rfl
  · intro e
    refine Prod.ext ?_ ((bigPhi_snd h).symm.trans (congrArg Prod.snd e))
    exact (MulEquiv.map_eq_one_iff _).1 ((bigPhi_fst h).symm.trans (congrArg Prod.fst e))

theorem ker_piTwo :
    piTwo.ker = CFSG.pCore 2 (Pc 1) := by
  ext h
  exact MonoidHom.mem_ker.trans ((piTwo_eq_one_iff h).trans
    (MonoidHom.mem_ker.symm.trans (SetLike.ext_iff.1 Par2.ker_bigPhi_eq_pCore h)))

theorem pCore_eq_subgroupOf :
    CFSG.pCore 2 (Pc 1) = (Nc 1).subgroupOf (Pc 1) :=
  (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _).symm

theorem ker_piTwo' :

    piTwo.ker = (Nc 1).subgroupOf (Pc 1) := ker_piTwo.trans pCore_eq_subgroupOf

theorem piTwo_snd_smul_j
    (h : Pc 1) (i : NativeCoord) :
    (piTwo h).2 • j i = j (restP (Par2.psiH h) i) := psi_smul_j _ i

theorem coe_restP_psiH
    (h : Pc 1) (i : NativeCoord) :
    ((restP (Par2.psiH h) i : NativeCoord) : Fin 24) =
      (((Par2.blockP (Par2.inclH h) : Ppair) : AutPerm) : Equiv.Perm (Fin 24)) i := rfl

theorem image_conj_block
    (h : Pc 1) (i : NativeCoord) :
    (fun d => (h : Dfull) * d * (h : Dfull)⁻¹) '' {d | ∃ v ∈ Vhat, dhat 0 i * v = d} =
      {d | ∃ v ∈ Vhat,
        dhat 0 (Unitary.LinThree.jEquiv.symm ((piTwo h).2 • j i) : Fin 24) * v = d} := by
  have e : Unitary.LinThree.jEquiv.symm ((piTwo h).2 • j i) = restP (Par2.psiH h) i := by
    rw [piTwo_snd_smul_j, ← Unitary.LinThree.jEquiv_apply, Equiv.symm_apply_apply]
  rw [e]
  exact Par2.image_conj_blk (Par2.inclH h) (Par2.nativeRest i)

theorem mem_Pc_zero_iff
    (h : Pc 1) : (h : Dfull) ∈ Pc 0 ↔ (piTwo h).1 vX = vX := by
  rw [Pc_zero, Subgroup.mem_inf, ← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff,
    ← Subtype.coe_inj, coe_piTwo_fst]
  change _ ↔ (h : Dfull) * xhat * (h : Dfull)⁻¹ = xhat
  rw [mul_inv_eq_iff_eq_mul]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, Pc_le_centralizer 1 h.2⟩⟩

theorem Pc_zero_subgroupOf :
    (Pc 0).subgroupOf (Pc 1) =
    ((MulAction.stabilizer (Equiv.Perm Vsharp) vX).prod ⊤).comap piTwo := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_Pc_zero_iff, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff]
  exact ⟨fun h1 => ⟨h1, Subgroup.mem_top _⟩, fun h1 => h1.1⟩

theorem rest3_ne_rest2 : Par3.rest3 ≠ Par2.rest2 := by decide

theorem zhat_mul_self :
    zhat * zhat = 1 :=
  Ehat_mul_self zhatE (by rw [psiW_zhat]; exact qV_pairW offPair23 0)

theorem coe_zhatE : ((zhatE : Ehat) : Dfull) = zhat := rfl

theorem mem_E3_cases
    {x : Dfull} (hx : x ∈ E3) : x ∈ Vhat ∨ zhat * x ∈ Vhat := by
  rw [E3_eq_EU] at hx
  obtain ⟨hE, hU⟩ := mem_EU.1 hx
  rcases (mem_Uplane_iff _).1 hU with h0 | h0 | h0 | h0
  · exact .inl (Par2.mem_Vhat_of_psiW ⟨x, hE⟩ (.inl h0))
  · exact .inl (Par2.mem_Vhat_of_psiW ⟨x, hE⟩ (.inr h0))
  · right
    have h1 := Par2.mem_Vhat_of_psiW (zhatE * ⟨x, hE⟩) (by
      rw [psiW_mul, psiW_zhat, h0]
      exact .inl (Par2.two_add_self sW))
    rwa [Subgroup.coe_mul, coe_zhatE] at h1
  · right
    have h1 := Par2.mem_Vhat_of_psiW (zhatE * ⟨x, hE⟩) (by
      rw [psiW_mul, psiW_zhat, h0]
      right
      rw [add_comm wFr sW, ← add_assoc, Par2.two_add_self, zero_add])
    rwa [Subgroup.coe_mul, coe_zhatE] at h1

theorem eq_of_cQ_mul_mem_E3
    {k : Rest} {d : Dfull} (hd : d ∈ Par2.blk k) (h : cQ * d ∈ E3) :
    k = Par2.rest2 ∨ k = Par3.rest3 := by
  rcases mem_E3_cases h with h1 | h1
  · left
    refine Par2.eq_of_mem_blk hd ⟨cQ * d, h1, ?_⟩
    change cQ * (cQ * d) = d
    rw [← mul_assoc, cQ_mul_self, one_mul]
  · right
    have e : cQ * d = cQ * (dhat 0 3 * (zhat * (cQ * d))) := by
      rw [← mul_assoc, ← zhat_eq, ← mul_assoc, zhat_mul_self, one_mul]
    exact Par2.eq_of_mem_blk hd ⟨_, h1, (mul_left_cancel e).symm⟩

theorem cQ_mul_mem_E3 {d : Dfull} (hd : d ∈ Par2.blk Par3.rest3) : cQ * d ∈ E3 := by
  obtain ⟨v, hv, rfl⟩ := hd
  change cQ * (dhat 0 3 * v) ∈ E3
  rw [← mul_assoc, ← zhat_eq]
  exact E3.mul_mem zhat_mem_E3 (Vhat_le_E3 hv)

theorem conj_zhat (h : Pc 1) :
    (h : Dfull) * zhat * (h : Dfull)⁻¹ = cQ * ((h : Dfull) * dhat 0 3 * (h : Dfull)⁻¹) := by
  rw [zhat_eq, ← mul_assoc, mul_cQ_of_Pc_one]
  group

theorem mem_K3_iff
    (h : Pc 1) :
    (h : Dfull) ∈ K3 ↔ Par2.blockP (Par2.inclH h) • Par3.rest3 = Par3.rest3 := by
  have hb := Par2.conj_blk_Ntwo (Par2.inclH h) (Par2.dhat_mem_blk Par3.rest3)
  change (h : Dfull) * dhat 0 3 * (h : Dfull)⁻¹ ∈ _ at hb
  constructor
  · intro hK
    have hz := (Subgroup.mem_normalizer_iff.1 hK zhat).1 zhat_mem_E3
    rw [conj_zhat] at hz
    rcases eq_of_cQ_mul_mem_E3 hb hz with h2 | h3
    · exfalso
      have e := h2.trans (Par2.blockP_inclH_rest2 h).symm
      exact rest3_ne_rest2 (smul_left_cancel _ e)
    · exact h3
  · intro hq
    rw [hq] at hb
    refine mem_normalizer_of_closure ?_
    rintro _ (rfl | rfl | rfl)
    · exact Vhat_le_E3 (conj_mem_Vhat (mem_Ntwo_of_Pc_one h) xhat_mem_Vhat)
    · exact Vhat_le_E3 (conj_mem_Vhat (mem_Ntwo_of_Pc_one h) yhat_mem_Vhat)
    · rw [conj_zhat]
      exact cQ_mul_mem_E3 hb

theorem restP_psiH_nc3_iff
    (h : Pc 1) :
    restP (Par2.psiH h) nc3 = nc3 ↔ Par2.blockP (Par2.inclH h) • Par3.rest3 = Par3.rest3 := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  rfl

theorem mem_Pc_two_iff
    (h : Pc 1) : (h : Dfull) ∈ Pc 2 ↔ (piTwo h).2 • pPt = pPt := by
  rw [Pc_two, Subgroup.mem_inf, ← j_three, piTwo_snd_smul_j, j_bijective.1.eq_iff,
    restP_psiH_nc3_iff, ← mem_K3_iff]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, Pc_le_centralizer 1 h.2⟩⟩

theorem Pc_two_subgroupOf_Pc_one :
    (Pc 2).subgroupOf (Pc 1) =
    ((⊤ : Subgroup (Equiv.Perm Vsharp)).prod (MulAction.stabilizer SigmaL3 pPt)).comap piTwo := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_Pc_two_iff, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff]
  exact ⟨fun h1 => ⟨Subgroup.mem_top _, h1⟩, fun h1 => h1.2⟩

theorem exists_ghat_decomp
    (n : Ntwo) :
    ∃ b ∈ Par2.Bh, ∃ r ∈ R2, (n : Dfull) = ghat (Par2.blockP n) * b * r := by
  set x := twoCoreEquiv (mkK n)
  have h1 : mkK n = alphaK x.1 * betaK x.2 := (psiK_twoCoreEquiv (mkK n)).symm
  have hmem : betaK x.2 ∈ Par2.Bh.map mkK := by
    rw [Par2.Bh, MonoidHom.map_closure, Set.image_pair]
    exact betaK_mem x.2
  obtain ⟨b, hb, hbe⟩ := hmem
  have hq : x.1 = Par2.blockP n := rfl
  have h2 : mkK (inclCN (ghatC (Par2.blockP n)) * b) = mkK n := by
    rw [map_mul, ← alphaK_apply, hbe, h1, hq]
  rw [mkK, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
  refine ⟨b, hb, ((inclCN (ghatC (Par2.blockP n)) * b)⁻¹ * n : Ntwo),
    Subgroup.mem_subgroupOf.1 h2, ?_⟩
  change (n : Dfull) = ghat (Par2.blockP n) * b * ((ghat (Par2.blockP n) * b)⁻¹ * n)
  group

theorem hhat_mem_Ehat : hhat ∈ Ehat := ⟨hbar, kappa_rho_mem_Ebar (DQ_mem_centralizer e0Cls), rfl⟩

theorem tauhat_mem_Xgrp :
    tauhat ∈ Xgrp := Subgroup.subset_closure (Set.mem_insert _ _)

theorem Bh_le_Xgrp
    {b : Ntwo} (hb : b ∈ Par2.Bh) : (b : Dfull) ∈ Xgrp := by
  have hle : Par2.Bh ≤ Xgrp.comap Ntwo.subtype := by
    rw [Par2.Bh, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Ehat_le_Xgrp hhat_mem_Ehat
    · exact tauhat_mem_Xgrp
  exact hle hb

theorem mem_Xgrp_iff_ghat
    (n : Ntwo) : (n : Dfull) ∈ Xgrp ↔ ghat (Par2.blockP n) ∈ Xgrp := by
  obtain ⟨b, hb, r, hr, e⟩ := exists_ghat_decomp n
  have hbX := Bh_le_Xgrp hb
  have hrX := R2_le_Xgrp hr
  rw [e]
  constructor
  · intro h
    have := Xgrp.mul_mem (Xgrp.mul_mem h (Xgrp.inv_mem hrX)) (Xgrp.inv_mem hbX)
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this
  · intro h
    exact Xgrp.mul_mem (Xgrp.mul_mem h hbX) hrX

theorem mk_gO_eq_iff (a b : C) :
    (QuotientGroup.mk (gO a) : OLq) = QuotientGroup.mk (gO b) ↔ a = b ∨ a = ΩC + b := by
  have h := mk_gO_mul_PO_eq_iff a b 1 1
  rw [PO_one, mul_one, mul_one] at h
  rw [h]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem ΩC_two : (ΩC : Fin 24 → ZMod 2) 2 = 1 := rfl

theorem coe_permC_apply (q : AutPerm) (a : C) (i : Fin 24) :
    (permC q a : Fin 24 → ZMod 2) i = (a : Fin 24 → ZMod 2) ((q : Equiv.Perm (Fin 24))⁻¹ i) := rfl

theorem ghat_mem_Xgrp_iff
    (q : Ppair) (h2 : ((q : AutPerm) : Equiv.Perm (Fin 24)) 2 = 2) :
    ghat q ∈ Xgrp ↔ permC q dC = dC := by
  have hJ : ghat q ∈ Jhat := Ctwo_le_Jhat (ghat_mem_Ctwo q)
  have hH : ghat q ∈ Xgrp ↔ ghat q ∈ H1 := by
    rw [← Xgrp_inf_centralizer_xhat, Subgroup.mem_inf, centralizer_xhat]
    exact ⟨fun h => ⟨h, hJ⟩, fun h => h.1⟩
  rw [hH, mem_H1_iff]
  have key : jhatToKv0 ⟨ghat q, hJ⟩ ∈ Cr ↔
      ((QuotientGroup.mk (PO (q : AutPerm)) : OLq))⁻¹ * QuotientGroup.mk (gO dC) *
        QuotientGroup.mk (PO (q : AutPerm)) = QuotientGroup.mk (gO dC) := by
    have hr : (rK : OLq) = QuotientGroup.mk (gO dC) := alpha12_eq
    rw [Cr, Subgroup.mem_centralizer_singleton_iff, ← Subtype.coe_inj, Subgroup.coe_mul,
      Subgroup.coe_mul, coe_jhatToKv0, jhatToKv_ghat, hr]
    constructor
    · intro e
      rw [e, inv_mul_cancel_right]
    · intro e
      calc ((QuotientGroup.mk (PO (q : AutPerm)) : OLq))⁻¹ * QuotientGroup.mk (gO dC) =
          ((QuotientGroup.mk (PO (q : AutPerm)) : OLq))⁻¹ * QuotientGroup.mk (gO dC) *
            QuotientGroup.mk (PO (q : AutPerm)) * (QuotientGroup.mk (PO (q : AutPerm)))⁻¹ := by
            group
        _ = _ := by rw [e]
  have e2 : ((QuotientGroup.mk (PO (q : AutPerm)) : OLq))⁻¹ * QuotientGroup.mk (gO dC) *
      QuotientGroup.mk (PO (q : AutPerm)) = QuotientGroup.mk (gO (permC q dC)) := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      PO_inv_mul_gO_mul_PO]
  constructor
  · rintro ⟨_, hk⟩
    have hk' := key.1 hk
    rw [e2, mk_gO_eq_iff] at hk'
    rcases hk' with hk | hk
    · exact hk
    · exfalso
      have h := congrArg (fun a : C => (a : Fin 24 → ZMod 2) 2) hk
      rw [coe_permC_apply, show ((q : AutPerm) : Equiv.Perm (Fin 24))⁻¹ 2 = 2 by
        rw [Equiv.Perm.inv_eq_iff_eq, h2]] at h
      change (dC : Fin 24 → ZMod 2) 2 = (ΩC : Fin 24 → ZMod 2) 2 + (dC : Fin 24 → ZMod 2) 2 at h
      rw [dC_apply, ΩC_two] at h
      exact absurd h (by decide)
  · intro hp
    refine ⟨hJ, ?_⟩
    rw [key, e2, hp]

theorem ite_one_zero_eq_iff {p q : Prop} [Decidable p] [Decidable q] :
    ((if p then (1 : ZMod 2) else 0) = if q then 1 else 0) ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem permC_dC_eq_iff (q : AutPerm) : permC q dC = dC ↔
    ∀ i : Fin 24, (((q : Equiv.Perm (Fin 24)) i : ℕ) < 8 ↔ (i : ℕ) < 8) := by
  rw [← Subtype.coe_inj, funext_iff]
  constructor
  · intro h i
    have h1 := h ((q : Equiv.Perm (Fin 24)) i)
    rw [coe_permC_apply, dC_apply, dC_apply, ite_one_zero_eq_iff,
      show (q : Equiv.Perm (Fin 24))⁻¹ ((q : Equiv.Perm (Fin 24)) i) = i from
        Equiv.Perm.inv_eq_iff_eq.2 rfl] at h1
    exact h1.symm
  · intro h i
    rw [coe_permC_apply, dC_apply, dC_apply, ite_one_zero_eq_iff]
    have h1 := h ((q : Equiv.Perm (Fin 24))⁻¹ i)
    rw [show (q : Equiv.Perm (Fin 24)) ((q : Equiv.Perm (Fin 24))⁻¹ i) = i from
      Equiv.Perm.eq_inv_iff_eq.1 rfl] at h1
    exact h1.symm

theorem lt_eight_iff_native (q : Ppair) (h2 : ((q : AutPerm) : Equiv.Perm (Fin 24)) 2 = 2) :
    (∀ i : Fin 24, ((((q : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) < 8 ↔ (i : ℕ) < 8)) ↔
      ∀ i : NativeCoord, ((((q : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) < 8 ↔ (i : ℕ) < 8) := by
  refine ⟨fun h i => h i, fun h i => ?_⟩
  by_cases hi : 3 ≤ (i : ℕ)
  · exact h ⟨i, hi⟩
  · have hq : (((q : AutPerm) : Equiv.Perm (Fin 24)) i : ℕ) < 3 := by
      have h01 := (mem_Ppair_iff (q : AutPerm)).1 q.2
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by
        rcases i with ⟨i, hi24⟩
        simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
        simp only at hi
        omega
      rcases hi' with rfl | rfl | rfl <;> rcases h01 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;>
        simp [e0, e1, h2]
    constructor <;> intro _ <;> omega

theorem image_perm_eq_iff {α : Type*} (σ : Equiv.Perm α) (T : Set α) :
    σ '' T = T ↔ ∀ i, σ i ∈ T ↔ i ∈ T := by
  constructor
  · intro h i
    have h1 := σ.injective.mem_set_image (s := T) (a := i)
    rwa [h] at h1
  · intro h
    ext y
    rw [Equiv.image_eq_preimage_symm, Set.mem_preimage, ← h, Equiv.apply_symm_apply]

theorem psi_smul_ellLine_iff
    (p : P₂) : psi p • ellLine = ellLine ↔
    ∀ i : NativeCoord, ((restP p i : ℕ) < 8 ↔ (i : ℕ) < 8) := by
  have e : psi p • ellLine = j '' (restP p '' {i : NativeCoord | (i : ℕ) < 8}) := by
    rw [← image_j_lt_eight, ← Set.image_smul, Set.image_image, Set.image_image]
    exact Set.image_congr fun i _ => psi_smul_j p i
  rw [e, ← image_j_lt_eight, j_bijective.1.image_injective.eq_iff, image_perm_eq_iff]
  rfl

theorem mem_Pc_three_iff
    (h : Pc 1) : (h : Dfull) ∈ Pc 3 ↔ (piTwo h).2 • ellLine = ellLine := by
  have h2 : (((Par2.blockP (Par2.inclH h) : Ppair) : AutPerm) : Equiv.Perm (Fin 24)) 2 = 2 :=
    congrArg Subtype.val (Par2.blockP_inclH_rest2 h)
  rw [piTwo_snd, psi_smul_ellLine_iff, Pc_three, Subgroup.mem_inf]
  have e : (h : Dfull) ∈ Xgrp ↔ ((Par2.inclH h : Ntwo) : Dfull) ∈ Xgrp := Iff.rfl
  rw [e, mem_Xgrp_iff_ghat, ghat_mem_Xgrp_iff _ h2, permC_dC_eq_iff, lt_eight_iff_native _ h2]
  simp only [coe_restP_psiH]
  exact ⟨fun hh => hh.1, fun hh => ⟨hh, Pc_le_centralizer 1 h.2⟩⟩

theorem Pc_three_subgroupOf_Pc_one :
    (Pc 3).subgroupOf (Pc 1) =
    ((⊤ : Subgroup (Equiv.Perm Vsharp)).prod (MulAction.stabilizer SigmaL3 ellLine)).comap
      piTwo := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_Pc_three_iff, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff]
  exact ⟨fun h1 => ⟨Subgroup.mem_top _, h1⟩, fun h1 => h1.2⟩

end CFSG.Monster.B.TwoA.Amalgam
