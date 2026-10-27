
module

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetCBase

public import CFSG.Monster.B.TwoA.Sp8.GenActionGen
public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbit
public import CFSG.Monster.B.TwoA.Sp8.QuadInv
public import Certificates.Data.CFSGNative.MonsterB.Orth8BFS
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.Lifts
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionConj
public meta import CFSG.Monster.B.TwoA.Sp8.QuadData
public meta import CFSG.Monster.B.TwoA.Sp8.QuadInv
public meta import CFSG.Monster.B.TwoA.Sp8.ElemAb
public meta import Certificates.Data.CFSGNative.MonsterB.Orth8BFS
public import CFSG.Monster.B.TwoA.Sp8.QuadCosetCInputs
public import Certificates.Certificate3078
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.Lifts
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.TwoA.Sp8.T9
public import CFSG.Monster.B.TwoA.Sp8.QuadForm
public import CFSG.Monster.B.TwoA.Sp8.QuadInvInputs
public import CFSG.Monster.B.Rep4371.SmallFaithful
public import CFSG.Monster.B.Gen.Max2Assembly
public import CFSG.Monster.B.Gen.PacketGeneration
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import Certificates.Certificate3055Base
public import Certificates.Certificate3078Base

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371

theorem cImg_checks : ∀ k < 44,
    (h1ConjN k (false, 0, 127) = Model.Pauli.mul (false, 0, 127) (foldP (cImg k)) ∨
      h1ConjN k (false, 0, 127) = Model.Pauli.mul (false, 0, 127)
        (foldP (cImg k + Pi.single 7 1))) ∧
    cImg k 7 = 0 :=
  Certificates.certificate3078.1

theorem PhiD_eq_Psi_of
    {v : Fin 8 → ZMod 2} (h7 : v 7 = 0) : PhiD v =
    Psi v := by
  rw [PhiD_eq_Psi, Function.update_eq_self_iff.2 h7.symm]

theorem h1LiftD_conj_cQ
    (k : Fin 44) : h1LiftD k * cQ *
    (h1LiftD k)⁻¹
    = cQ * Psi (cImg k) := by
  obtain ⟨hc, h7⟩ := cImg_checks k k.2
  have key : ∃ u : Fin 8 → ZMod 2, conjQ (h1Lift k) cP = cP * PhiQ u ∧ PhiD u = Psi (cImg k) := by
    rcases hc with h | h
    · refine ⟨cImg k, ?_, PhiD_eq_Psi_of h7⟩
      rw [cP, conjQ_h1Lift, h, pauliQ_mul]
      rfl
    · refine ⟨cImg k + Pi.single 7 1, ?_, ?_⟩
      · rw [cP, conjQ_h1Lift, h, pauliQ_mul]
        rfl
      · rw [PhiD_add_seven, PhiD_eq_Psi_of h7]
  obtain ⟨u, hu, hD⟩ := key
  have hC : h1LiftC k * cC * (h1LiftC k)⁻¹ = PhiC u * cC := by
    apply Subtype.ext
    show thetaEquiv (h1Lift k) * rhoEquiv cP * (thetaEquiv (h1Lift k))⁻¹ =
      rhoEquiv (PhiQ u) * rhoEquiv cP
    rw [Short.thetaEquiv_conj_rhoEquiv, hu, rhoEquiv_mul]
  calc h1LiftD k * cQ * (h1LiftD k)⁻¹ = iotaD (kappa (PhiC u * cC)) := by
        rw [h1LiftD, cQ_eq, conj_iotaD_kappa, hC]
    _ = PhiD u * cQ := by rw [map_mul, map_mul, cQ_eq]; rfl
    _ = cQ * PhiD u := (cQ_comm_PhiD u).symm
    _ = cQ * Psi (cImg k) := by rw [hD]

theorem h1LiftD_conj_aT_genM
    (k : Fin 44) (j : Fin 8) :
    h1LiftD k * aT j * (h1LiftD k)⁻¹ = Psi (genM k j) := by
  rw [h1LiftD_conj_aT, coe_aEquiv, toAdd_ofAdd]
  rfl

theorem affN_spec : ∀ k < 45, ∀ n < 256,
    bvec 8 (affN k n) = affM k (bvec 8 n) ∧ affN k n < 256 :=
  Certificates.certificate3078.2.1

theorem qPoly_bvec :
    ∀ n < 256, qPoly (bvec 8 n) = if qN n then 1 else 0 :=
  Certificates.certificate3078.2.2.1

theorem qN_affN : ∀ k < 45, ∀ n < 256, qN (affN k n) = qN n :=
  Certificates.certificate3078.2.2.2.1

theorem qPoly_affM {k : ℕ}
    (hk : k < 45) (v : Fin 8 → ZMod 2) : qPoly
    (affM k v) = qPoly v := by
  obtain ⟨n, hn, rfl⟩ := exists_bvec8 v
  obtain ⟨h1, h2⟩ := affN_spec k hk n hn
  rw [← h1, qPoly_bvec _ h2, qPoly_bvec n hn, qN_affN k hk n hn]

theorem genM_qPoly (k : Fin 44)
    (v : Fin 8 → ZMod 2) :
    qPoly (cImg k + ∑ j, v j • genM k j) = qPoly v := by
  have h := qPoly_affM (k := k) (by omega) v
  rwa [affM, ite_eq_left k.2] at h

theorem qPres_h1LiftD
    (k : Fin 44) : QPres (h1LiftD k) :=
  qPres_of_rows (h1LiftD_conj_aT_genM k) (h1LiftD_conj_cQ k) (genM_qPoly k)

theorem Xgrp_le_qPresGrp :
    Xgrp ≤ qPresGrp := by
  rw [Xgrp_eq_closure, Subgroup.closure_le]
  rintro x (rfl | ⟨k, rfl⟩)
  · exact qPres_tauhat
  · exact qPres_h1LiftD k

theorem QPres.conj_mem_A8
    {x : Dfull}
    (hx : QPres x) {a : Dfull} (ha : a ∈ A8) :
    x * a * x⁻¹ ∈ A8 := by
  rw [← range_PsiHom] at ha ⊢
  obtain ⟨v, rfl⟩ := ha
  obtain ⟨w, hw⟩ := hx.1 v.toAdd
  exact ⟨Multiplicative.ofAdd w, hw.symm⟩

theorem QPres.conj_mem_coset
    {x : Dfull} (hx : QPres x) {y : Dfull} (hy : cQ * y ∈ A8) :
    cQ * (x * y * x⁻¹) ∈ A8 := by
  rw [← range_PsiHom] at hy ⊢
  obtain ⟨v, hv⟩ := hy
  have hy' : y = cQ * Psi v.toAdd := by
    rw [← PsiHom_apply, hv, ← mul_assoc, cQ_mul_self, one_mul]
  obtain ⟨w, hw, -⟩ := hx.2 v.toAdd
  refine ⟨Multiplicative.ofAdd w, ?_⟩
  rw [hy', hw, ← mul_assoc, cQ_mul_self, one_mul]
  rfl

theorem QPres.conj_mem_T9
    {x : Dfull} (hx : QPres x) {t : Dfull} (ht : t ∈ T9) :
    x * t * x⁻¹ ∈ T9 := by
  rw [mem_T9_iff] at ht ⊢
  rcases ht with h | h
  · exact Or.inl (hx.conj_mem_A8 h)
  · exact Or.inr (hx.conj_mem_coset h)

theorem Xgrp_le_normalizer_T9 :
    Xgrp ≤ Subgroup.normalizer
    (T9 : Set Dfull) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => (Xgrp_le_qPresGrp hx).conj_mem_T9 ht, fun ht => ?_⟩
  have h := (Xgrp_le_qPresGrp (Xgrp.inv_mem hx)).conj_mem_T9 ht
  rwa [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at h

theorem qPoly_conj
    {x : Dfull} (hx : x ∈ Xgrp) {v w : Fin 8 → ZMod 2}
    (h : x * (cQ * Psi v) * x⁻¹ = cQ * Psi w) : qPoly w = qPoly v := by
  obtain ⟨w', hw', hq⟩ := (Xgrp_le_qPresGrp hx).2 v
  have hww : Psi w = Psi w' := mul_left_cancel (h.symm.trans hw')
  have e : w = w' := by
    have := PsiHom_injective (a₁ := Multiplicative.ofAdd w) (a₂ := Multiplicative.ofAdd w') hww
    exact congrArg Multiplicative.toAdd this
  rw [e, hq]

theorem conj_affM
    {k : ℕ} (_hk : k < 45) :
    ∃ g ∈ Xgrp, ∀ w : Fin 8 → ZMod 2, g * (cQ * Psi w) * g⁻¹ = cQ * Psi (affM k w) := by
  by_cases h44 : k < 44
  · refine ⟨h1LiftD ⟨k, h44⟩, ?_, fun w => ?_⟩
    · rw [Xgrp_eq_closure]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨⟨k, h44⟩, rfl⟩)
    · rw [affM, ite_eq_left h44]
      exact conj_cPsi_of_rows (h1LiftD_conj_aT_genM ⟨k, h44⟩) (h1LiftD_conj_cQ ⟨k, h44⟩) w
  · refine ⟨tauhat, ?_, fun w => ?_⟩
    · rw [Xgrp_eq_closure]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [affM, ite_eq_right h44, ← zero_add (∑ j, w j • triM j)]
      exact conj_cPsi_of_rows tauhat_conj_aT_triM tauhat_conj_cQ w

theorem affTab_get :
    ∀ k < 45, ∀ n < 256, (affTab[k]!)[n]! = affN k n :=
  Certificates.certificate3078.2.2.2.2.1

theorem zeroTab_get : ∀ n < 256, zeroTab[n]! = !qN n :=
  Certificates.certificate3078.2.2.2.2.2.1

theorem affTab_size : affTab.size = 45 :=
  Certificates.certificate3078.2.2.2.2.2.2.1

theorem pairCheck_eq_true :
    CFSG.Monster.B.Sp8.Native.pairCheck affTab zeroTab 1 = true :=
  Certificates.certificate3078.2.2.2.2.2.2.2

@[expose] def Reach
    (p : ℕ) : Prop :=
  ∃ x ∈ Xgrp, x * cQ * x⁻¹ = cQ * Psi (bvec 8 (p / 256)) ∧
    x * (cQ * xhat) * x⁻¹ = cQ * Psi (bvec 8 (p % 256))

theorem Psi_bvec_one :
    Psi (bvec 8 1) = xhat := by
  rw [bvec8_one, Psi_single]
  rfl

theorem reach_root :
    Reach 1 := by
  refine ⟨1, Xgrp.one_mem, ?_, ?_⟩
  · rw [show (1 : ℕ) / 256 = 0 from rfl, show bvec 8 0 = 0 from by decide, Psi_zero']
    group
  · rw [show (1 : ℕ) % 256 = 1 from rfl, Psi_bvec_one]
    group

theorem reach_step
    {k q : ℕ} (hk : k < 45)
    (hq : q < 65536)
    (h : Reach q) :
    Reach (CFSG.Monster.B.Sp8.Native.pairImg affTab k q) := by
  obtain ⟨x, hx, h1, h2⟩ := h
  obtain ⟨g, hg, hgw⟩ := conj_affM hk
  have ha := affN_spec k hk (q / 256) (by omega)
  have hb := affN_spec k hk (q % 256) (by omega)
  have e : CFSG.Monster.B.Sp8.Native.pairImg affTab k q =
      256 * affN k (q / 256) + affN k (q % 256) := by
    rw [CFSG.Monster.B.Sp8.Native.pairImg, affTab_get k hk _ (by omega),
      affTab_get k hk _ (by omega)]
  have hdiv : CFSG.Monster.B.Sp8.Native.pairImg affTab k q / 256 = affN k (q / 256) := by
    rw [e]
    omega
  have hmod : CFSG.Monster.B.Sp8.Native.pairImg affTab k q % 256 = affN k (q % 256) := by
    rw [e]
    omega
  refine ⟨g * x, Xgrp.mul_mem hg hx, ?_, ?_⟩
  · rw [show g * x * cQ * (g * x)⁻¹ = g * (x * cQ * x⁻¹) * g⁻¹ by group, h1, hgw, hdiv, ha.1]
  · rw [show g * x * (cQ * xhat) * (g * x)⁻¹ = g * (x * (cQ * xhat) * x⁻¹) * g⁻¹ by group, h2,
      hgw, hmod, hb.1]

theorem reach_pair :
    ∀ (d p : ℕ), p < 65536 →
    (CFSG.Monster.B.Sp8.Native.pairBFS affTab 1).2[p]! = d → qN (p / 256) = false →
    qN (p % 256) = false → p / 256 ≠ p % 256 → Reach p := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro p hp hd hza hzb hab
    by_cases h1 : p = 1
    · subst h1
      exact reach_root
    · have hc := pairCheck_eq_true
      simp only [CFSG.Monster.B.Sp8.Native.pairCheck, Bool.and_eq_true, beq_iff_eq,
        List.all_eq_true, List.mem_range] at hc
      have hcp := hc.2 p hp
      rw [zeroTab_get _ (by omega), zeroTab_get _ (by omega), hza, hzb] at hcp
      rw [ite_eq_left (by simp [hab, h1])] at hcp
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
        affTab_size, and_assoc] at hcp
      obtain ⟨hk, hdep, hq, hzqa, hzqb, hqab⟩ := hcp
      have hqlt : (CFSG.Monster.B.Sp8.Native.pairBFS affTab 1).1[p]! % 65536 < 65536 :=
        Nat.mod_lt _ (by norm_num)
      rw [zeroTab_get _ (by omega)] at hzqa hzqb
      have hzqa' :
          qN ((CFSG.Monster.B.Sp8.Native.pairBFS affTab 1).1[p]! % 65536 / 256) = false := by
        simpa using hzqa
      have hzqb' :
          qN ((CFSG.Monster.B.Sp8.Native.pairBFS affTab 1).1[p]! % 65536 % 256) = false := by
        simpa using hzqb
      have hr := ih _ (hd ▸ hdep) _ hqlt rfl hzqa' hzqb' hqab
      rw [← hq]
      exact reach_step hk hqlt hr

theorem qN_of_qPoly {n : ℕ} (hn : n < 256) (h : qPoly (bvec 8 n) = 0)
    : qN n = false := by
  rw [qPoly_bvec n hn] at h
  cases hq : qN n
  · rfl
  · rw [hq, ite_eq_left rfl] at h
    exact absurd h one_ne_zero

theorem reach_of_vec
    {v w : Fin 8 → ZMod 2} (hv : qPoly v = 0)
    (hw : qPoly w = 0) (hvw : v ≠ w) :
    ∃ x ∈ Xgrp, x * cQ * x⁻¹ = cQ * Psi v ∧ x * (cQ * xhat) * x⁻¹ = cQ * Psi w := by
  obtain ⟨a, ha, rfl⟩ := exists_bvec8 v
  obtain ⟨b, hb, rfl⟩ := exists_bvec8 w
  have hp : 256 * a + b < 65536 := by omega
  have hdiv : (256 * a + b) / 256 = a := by omega
  have hmod : (256 * a + b) % 256 = b := by omega
  obtain ⟨x, hx, h1, h2⟩ := reach_pair _ (256 * a + b) hp rfl
    (by rw [hdiv]; exact qN_of_qPoly ha hv) (by rw [hmod]; exact qN_of_qPoly hb hw)
    (by rw [hdiv, hmod]; exact fun h => hvw (h ▸ rfl))
  rw [hdiv] at h1
  rw [hmod] at h2
  exact ⟨x, hx, h1, h2⟩

theorem mem_orbit_of_qPoly
    {v : Fin 8 → ZMod 2} (hv : qPoly v = 0) :
    ∃ x ∈ Xgrp, x * cQ * x⁻¹ = cQ * Psi v := by
  by_cases h0 : v = 0
  · subst h0
    exact ⟨1, Xgrp.one_mem, by rw [Psi_zero', mul_one, one_mul, inv_one, mul_one]⟩
  · obtain ⟨x, hx, h1, -⟩ := reach_of_vec hv qPoly_zero' h0
    exact ⟨x, hx, h1⟩

theorem orbit_cQ :
    {y : Dfull | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y} =
    (fun v => cQ * Psi v) '' {v : Fin 8 → ZMod 2 | qPoly v = 0} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hq⟩ := (Xgrp_le_qPresGrp hx).2 0
    refine ⟨w, ?_, ?_⟩
    · show qPoly w = 0
      rw [hq]
      decide
    · show cQ * Psi w = x * cQ * x⁻¹
      rw [← hw, Psi_zero', mul_one]
  · rintro ⟨v, hv, rfl⟩
    exact mem_orbit_of_qPoly hv

theorem cPsi_injective :
    Function.Injective fun v : Fin 8 → ZMod 2 => cQ * Psi v := by
  intro v w h
  have hP : Psi v = Psi w := mul_left_cancel h
  exact congrArg Multiplicative.toAdd
    (PsiHom_injective (a₁ := Multiplicative.ofAdd v) (a₂ := Multiplicative.ofAdd w) hP)

theorem ncard_orbit_cQ :
    {y : Dfull | ∃ x ∈ Xgrp, x * cQ * x⁻¹ = y}.ncard = 120 := by
  rw [orbit_cQ, Set.ncard_image_of_injective _ cPsi_injective, ← card_qPoly_zero,
    ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

end CFSG.Monster.B.TwoA.Sp8
