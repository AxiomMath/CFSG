module

public import CFSG.Sporadic.Co1Patterson.AmalgamNative
public import CFSG.Sporadic.Co1Patterson.AmalgamRigidInputs
public import CFSG.Sporadic.Co1Patterson.TwistNativeCore
public import Certificates.Certificate21158
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.NotConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Monster.GMS CFSG.Open
  CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1Patterson.TwistNative
open CFSG.EvenSmallLie.OmegaEight (ind bNat)
open CFSG.Blueprint (NativeSporadic.Co1)

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)


theorem qae_check : qaeOK = true := Certificates.certificate21158.1

theorem edge_elem_check : edgeElemOK = true := Certificates.certificate21158.2.1

theorem stab_check : stabOK = true := Certificates.certificate21158.2.2.1

theorem perp_check : perpOK = true := Certificates.certificate21158.2.2.2

theorem edgeRigidCheck_parts : qaeOK = true ∧ edgeElemOK = true ∧ stabOK = true ∧
    perpOK = true :=
  ⟨qae_check, edge_elem_check, stab_check, perp_check⟩

theorem edgeElemOK_parts :
    (1 ≤ y0Idx ∧ y0Idx ≤ 190) ∧
    Native.mul (Native.mul (gEl (gensKe.getD 4 0)) pRows) (gElInv (gensKe.getD 4 0)) =
      Native.mul qRows pRows ∧
    Native.mul (Native.mul (gEl y0Idx) qRows) (gElInv y0Idx) = qRows ∧
    Native.mul (Native.mul (gEl y0Idx) pRows) (gElInv y0Idx) = Native.mul qRows pRows ∧
    qRows = Native.mul (yprodRow 217) iotaARows ∧ pRows = yprodRow 9 ∧
    conjOK (repRows 1) eCols = true ∧
    (∀ c ∈ uBasis, colsApply eCols c = c) ∧
    (∀ c ∈ uBasis, Native.mul (yprodRow c) (repRows 1) = Native.mul (repRows 1) (yprodRow c)) ∧
    colsApply eCols 1 = 8 ∧ colsApply eCols 16 = 192 := by
  have h := edgeRigidCheck_parts.2.1
  unfold edgeElemOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨⟨h1, h2⟩, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem nrep_iff_mrep (R : Native.Rows) (h : centralizer ({aNC} : Set NativeSporadic.Co1)) :
    NRep R (h : NativeSporadic.Co1) ↔ MRep R (centEmb h) := by
  rw [NRep, MRep, matHom_eq_nativeEmb, centEmb_apply]
  exact eq_comm

theorem nrep_yprodH (c : ℕ) : NRep (yprodRow c) (yprodH c : NativeSporadic.Co1) := by
  rw [nrep_iff_mrep, centEmb_yprodH]
  exact rep_yprodG c

theorem coe_z : ((typeSystemC.z : centralizer ({aNC} : Set NativeSporadic.Co1)) :
    NativeSporadic.Co1) = aNC := rfl

theorem coe_q_eq : ((wT 2 : Vt) : NativeSporadic.Co1) =
    ((yprodH 217 * typeSystemC.z : centralizer ({aNC} : Set NativeSporadic.Co1)) :
      NativeSporadic.Co1) := by
  have h := nrep_wT 2
  have e : wRows (triW.getD (2 : Fin 3) 0) = qRows := rfl
  rw [e, edgeElemOK_parts.2.2.2.2.1] at h
  refine NRep.unique h ?_
  rw [Subgroup.coe_mul, coe_z]
  exact (nrep_yprodH 217).mul nrep_aNC

theorem coe_p_eq : ((wT 0 : Vt) : NativeSporadic.Co1) =
    ((yprodH 9 : centralizer ({aNC} : Set NativeSporadic.Co1)) : NativeSporadic.Co1) := by
  have h := nrep_wT 0
  have e : wRows (triW.getD (0 : Fin 3) 0) = pRows := rfl
  rw [e, edgeElemOK_parts.2.2.2.2.2.1] at h
  exact NRep.unique h (nrep_yprodH 9)

@[expose] noncomputable def eC : centralizer ({aNC} : Set NativeSporadic.Co1) :=
  ⟨(vE : NativeSporadic.Co1), vE_mem_cent_aNC⟩

theorem coe_eC : ((eC : centralizer ({aNC} : Set NativeSporadic.Co1)) : NativeSporadic.Co1) =
    (vE : NativeSporadic.Co1) := rfl

theorem eC_conj : ∀ k < 8, eC * yH k * eC⁻¹ = yprodH (eCols.getD k 0) ∨
    eC * yH k * eC⁻¹ = yprodH (eCols.getD k 0) * typeSystemC.z := by
  intro k hk
  have hz : centEmb typeSystemC.z = aG := centEmb_zM
  have hrep : MRep (repRows 1) (centEmb eC) :=
    (nrep_iff_mrep _ _).1 (nrep_repV (show 1 < 10 by norm_num))
  rcases conjOK_spec hrep edgeElemOK_parts.2.2.2.2.2.2.1 k hk with h1 | h1
  · left
    apply centEmb_injective
    rw [map_mul, map_mul, map_inv, centEmb_yH, centEmb_yprodH, h1]
  · right
    apply centEmb_injective
    rw [map_mul, map_mul, map_inv, centEmb_yH, map_mul, centEmb_yprodH, hz, h1]

theorem phi_eC_bv (v : ℕ) :
    ((typeSystemC.φ eC : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv v) =
      bv (colsApply eCols v) :=
  phi_bv_of_conj eC eCols eC_conj v

theorem yprodH_comm_eC {c : ℕ} (hc : c ∈ uBasis) : yprodH c * eC = eC * yprodH c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_eC]
  exact NRep.unique ((nrep_yprodH c).mul (nrep_repV (show 1 < 10 by norm_num)))
    (by rw [edgeElemOK_parts.2.2.2.2.2.2.2.2.1 c hc]
        exact (nrep_repV (show 1 < 10 by norm_num)).mul (nrep_yprodH c))

theorem linearMap_ext_uBasis {F G : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (h1 : F (bv 1) = G (bv 1)) (h16 : F (bv 16) = G (bv 16))
    (hU : ∀ c ∈ uBasis, F (bv c) = G (bv c)) : F = G := by
  have hu : ∀ c, c ∈ uBasis → F (bv c) = G (bv c) := hU
  have hx : ∀ a b, F (bv a) = G (bv a) → F (bv b) = G (bv b) →
      F (bv (a ^^^ b)) = G (bv (a ^^^ b)) := fun a b ha hb => by
    rw [bv_xor, map_add, map_add, ha, hb]
  refine linearMap_ext_bv fun k hk => ?_
  interval_cases k
  · exact h1
  · exact hu 2 (by decide)
  · exact hx 5 1 (hu 5 (by decide)) h1
  · exact hx 9 1 (hu 9 (by decide)) h1
  · exact h16
  · exact hu 32 (by decide)
  · exact hu 64 (by decide)
  · exact hx 144 16 (hu 144 (by decide)) h16

theorem eq_one_or_phi_eC {f : L₀}
    (hf : ∀ c ∈ uBasis, (f : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv c) = bv c) :
    f = 1 ∨ f = typeSystemC.φ eC := by
  set F := (f : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) with hFdef
  have hpol : ∀ u v a b, F (bv u) = bv a → F (bv v) = bv b → bNat a b = bNat u v := by
    intro u v a b ha hb
    apply ind_injective
    rw [← polar_q₀_bv, ← polar_q₀_bv, ← ha, ← hb, hFdef, polar_L₀]
  have hq : ∀ u a, F (bv u) = bv a →
      CFSG.EvenSmallLie.OmegaEight.qNat a = CFSG.EvenSmallLie.OmegaEight.qNat u := by
    intro u a ha
    apply ind_injective
    rw [← q₀_bv, ← q₀_bv, ← ha, hFdef, q₀_L₀]
  have hy₁ : F (bv 1) = bv (enc (F (bv 1))) := (bv_enc _).symm
  have hy₂ : F (bv 16) = bv (enc (F (bv 16))) := (bv_enc _).symm
  have hcond : stabCond (enc (F (bv 1))) (enc (F (bv 16))) = true := by
    unfold stabCond
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    exact ⟨⟨⟨fun c hc => ⟨hpol 1 c _ c hy₁ (hf c hc), hpol 16 c _ c hy₂ (hf c hc)⟩,
      hq 1 _ hy₁⟩, hq 16 _ hy₂⟩, hpol 1 16 _ _ hy₁ hy₂⟩
  have hstab := edgeRigidCheck_parts.2.2.1
  unfold stabOK at hstab
  simp only [List.all_eq_true, List.mem_range] at hstab
  have h := hstab (enc (F (bv 1))) (enc_lt _) (enc (F (bv 16))) (enc_lt _)
  rw [hcond] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hF : (F : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) = LinearMap.id :=
      linearMap_ext_uBasis (by rw [LinearEquiv.coe_coe, hy₁, h1]; rfl)
        (by rw [LinearEquiv.coe_coe, hy₂, h2]; rfl) (fun c hc => by
          rw [LinearEquiv.coe_coe, hf c hc]; rfl)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun hF x
  · right
    have hF : (F : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) =
        (((typeSystemC.φ eC : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :
          (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) := by
      obtain ⟨-, -, -, -, -, -, -, hfix, -, h8, h192⟩ := edgeElemOK_parts
      refine linearMap_ext_uBasis ?_ ?_ fun c hc => ?_
      · rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, hy₁, h1, phi_eC_bv, h8]
      · rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, hy₂, h2, phi_eC_bv, h192]
      · rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, hf c hc, phi_eC_bv, hfix c hc]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun hF x

theorem eq_or_eq_mul_z_of_vec {u v : centralizer ({aNC} : Set NativeSporadic.Co1)}
    (hu : typeSystemC.φ u = 1) (hv : typeSystemC.φ v = 1)
    (h : typeSystemC.vec u = typeSystemC.vec v) : u = v ∨ u = v * typeSystemC.z := by
  have hw : typeSystemC.φ (v⁻¹ * u) = 1 := by rw [map_mul, map_inv, hu, hv, inv_one, one_mul]
  have h0 : typeSystemC.vec (v⁻¹ * u) = 0 := by
    rw [typeSystemC.vec_mul _ _ (by rw [map_inv, hv, inv_one]) hu, typeSystemC.vec_inv hv, h]
    exact vec_add_self _
  rcases (typeSystemC.vec_eq_zero _ hw).1 h0 with h1 | h1
  · exact Or.inl (inv_mul_eq_one.1 h1).symm
  · right
    rw [← h1, mul_inv_cancel_left]

@[expose] noncomputable def T₃ : Subgroup NativeSporadic.Co1 :=
  centralizer ({aNC} : Set NativeSporadic.Co1) ⊓
    centralizer ({(vE : NativeSporadic.Co1)} : Set NativeSporadic.Co1) ⊓
    centralizer ({((wT 0 : Vt) : NativeSporadic.Co1)} : Set NativeSporadic.Co1)

theorem conj_mul_of_comm {G : Type*} [Group G] {u v x : G} (h : u * x = x * u) :
    v * u * x * (v * u)⁻¹ = v * x * v⁻¹ := by
  calc v * u * x * (v * u)⁻¹ = v * (u * x) * u⁻¹ * v⁻¹ := by group
    _ = v * (x * u) * u⁻¹ * v⁻¹ := by rw [h]
    _ = v * x * v⁻¹ := by group

theorem conj_T₃_of_vec {s : centralizer ({aNC} : Set NativeSporadic.Co1)}
    (hs : typeSystemC.φ s = 1) {c : ℕ} (hc : c = 0 ∨ c = 9 ∨ c = 208 ∨ c = 217)
    (hv : typeSystemC.vec s = bv c) :
    (∀ x ∈ T₃, (s : NativeSporadic.Co1) * x * (s : NativeSporadic.Co1)⁻¹ = x) ∨
    (∀ x ∈ T₃, (s : NativeSporadic.Co1) * x * (s : NativeSporadic.Co1)⁻¹ =
      ((wT 2 : Vt) : NativeSporadic.Co1) * x * ((wT 2 : Vt) : NativeSporadic.Co1)⁻¹) := by
  have hza : ∀ x ∈ T₃, (typeSystemC.z : NativeSporadic.Co1) * x = x * typeSystemC.z :=
    fun x hx => by rw [coe_z]; exact (mem_centralizer_singleton_iff.1 (mem_inf.1
      (mem_inf.1 hx).1).1).symm
  have hzp : ∀ x ∈ T₃, ((wT 0 : Vt) : NativeSporadic.Co1) * x = x * ((wT 0 : Vt) :
      NativeSporadic.Co1) := fun x hx => (mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2).symm
  have key : ∀ r : centralizer ({aNC} : Set NativeSporadic.Co1), typeSystemC.φ r = 1 →
      typeSystemC.vec r = bv c → ∀ x ∈ T₃,
        (s : NativeSporadic.Co1) * x * (s : NativeSporadic.Co1)⁻¹ =
          (r : NativeSporadic.Co1) * x * (r : NativeSporadic.Co1)⁻¹ := by
    intro r hr hrv x hx
    rcases eq_or_eq_mul_z_of_vec hs hr (hv.trans hrv.symm) with h | h
    · rw [h]
    · rw [h, Subgroup.coe_mul]
      exact conj_mul_of_comm (hza x hx)
  have hpC : typeSystemC.φ (yprodH 9) = 1 := phi_yprodH 9
  have hqC : typeSystemC.φ (yprodH 217 * typeSystemC.z) = 1 := by
    rw [map_mul, phi_yprodH, typeSystemC.φ_z, one_mul]
  have hqv : typeSystemC.vec (yprodH 217 * typeSystemC.z) = bv 217 := vec_yprodH_mul_z 217
  rcases hc with rfl | rfl | rfl | rfl
  · left
    intro x hx
    rw [key 1 (map_one _) (by rw [typeSystemC.vec_one, bv_zero]) x hx]
    simp
  · left
    intro x hx
    rw [key (yprodH 9) hpC (vec_yprodH 9) x hx, ← coe_p_eq, hzp x hx, mul_inv_cancel_right]
  · right
    intro x hx
    have hv208 : typeSystemC.vec ((yprodH 217 * typeSystemC.z) * yprodH 9) = bv 208 := by
      rw [typeSystemC.vec_mul _ _ hqC hpC, hqv, vec_yprodH, ← bv_xor]
      rfl
    rw [key _ (by rw [map_mul, hqC, hpC, one_mul]) hv208 x hx, Subgroup.coe_mul, ← coe_q_eq,
      ← coe_p_eq]
    calc ((wT 2 : Vt) : NativeSporadic.Co1) * (wT 0 : Vt) * x *
          (((wT 2 : Vt) : NativeSporadic.Co1) * (wT 0 : Vt))⁻¹ =
        (wT 2 : Vt) * ((wT 0 : Vt) * x) * ((wT 0 : Vt) : NativeSporadic.Co1)⁻¹ *
          ((wT 2 : Vt) : NativeSporadic.Co1)⁻¹ := by group
      _ = (wT 2 : Vt) * x * ((wT 2 : Vt) : NativeSporadic.Co1)⁻¹ := by
          rw [hzp x hx]; group
  · right
    intro x hx
    rw [key _ hqC hqv x hx, ← coe_q_eq]

theorem perp_cases {v : ℕ} (hv : v < 256) (h : ∀ c ∈ uBasis, bNat v c = false) :
    v = 0 ∨ v = 9 ∨ v = 208 ∨ v = 217 := by
  have hp := edgeRigidCheck_parts.2.2.2
  unfold perpOK at hp
  rw [List.all_eq_true] at hp
  have h1 := hp v (List.mem_range.2 hv)
  have hall : (uBasis.all fun c => !bNat v c) = true :=
    List.all_eq_true.2 fun c hc => by rw [h c hc]; rfl
  rw [hall] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with ((h1 | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem cent_cases {d : NativeSporadic.Co1}
    (hd : d ∈ centralizer ({aNC} : Set NativeSporadic.Co1) ⊓
      centralizer ({(vE : NativeSporadic.Co1)} : Set NativeSporadic.Co1))
    (hcomm : ∀ c ∈ uBasis, d * (yprodH c : NativeSporadic.Co1) =
      (yprodH c : NativeSporadic.Co1) * d) :
    (∀ x ∈ T₃, d * x * d⁻¹ = x) ∨
    (∀ x ∈ T₃, d * x * d⁻¹ =
      ((wT 2 : Vt) : NativeSporadic.Co1) * x * ((wT 2 : Vt) : NativeSporadic.Co1)⁻¹) := by
  set δ : centralizer ({aNC} : Set NativeSporadic.Co1) := ⟨d, (mem_inf.1 hd).1⟩ with hδ
  have hδc : ∀ c ∈ uBasis, δ * yprodH c = yprodH c * δ := fun c hc => Subtype.ext (hcomm c hc)
  have hfix : ∀ c ∈ uBasis,
      ((typeSystemC.φ δ : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv c) = bv c := by
    intro c hc
    have h := typeSystemC.vec_conj δ (yprodH c) (phi_yprodH c)
    rw [show δ * yprodH c * δ⁻¹ = yprodH c by rw [hδc c hc]; group, vec_yprodH] at h
    exact h.symm
  obtain ⟨δ', hδ'φ, hδ'c, hdec⟩ : ∃ δ' : centralizer ({aNC} : Set NativeSporadic.Co1),
      typeSystemC.φ δ' = 1 ∧ (∀ c ∈ uBasis, δ' * yprodH c = yprodH c * δ') ∧
      (d = (δ' : NativeSporadic.Co1) ∨ d = (δ' : NativeSporadic.Co1) * vE) := by
    rcases eq_one_or_phi_eC hfix with h1 | h1
    · exact ⟨δ, h1, hδc, Or.inl rfl⟩
    · refine ⟨δ * eC⁻¹, by rw [map_mul, map_inv, h1, mul_inv_cancel], fun c hc => ?_,
        Or.inr ?_⟩
      · have he := yprodH_comm_eC hc
        have he' : eC⁻¹ * yprodH c = yprodH c * eC⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← he, mul_assoc, mul_inv_cancel, mul_one]
        rw [mul_assoc, he', ← mul_assoc, hδc c hc, mul_assoc]
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_eC, inv_mul_cancel_right]
  have hperp : ∀ c ∈ uBasis, bNat (enc (typeSystemC.vec δ')) c = false := by
    intro c hc
    have h := (typeSystemC.comm_eq_one_iff δ' (yprodH c) hδ'φ (phi_yprodH c)).1
      (by rw [hδ'c c hc]; group)
    rw [vec_yprodH, ← bv_enc (typeSystemC.vec δ')] at h
    have h' : ind (ZMod 2) (bNat (enc (typeSystemC.vec δ')) c) = 0 := by
      rw [← polar_q₀_bv]
      exact h
    exact (ind_eq_zero_iff _).1 h'
  have hc' := perp_cases (enc_lt (typeSystemC.vec δ')) hperp
  have hv : typeSystemC.vec δ' = bv (enc (typeSystemC.vec δ')) := (bv_enc _).symm
  have hcases := conj_T₃_of_vec hδ'φ hc' hv
  have heT : ∀ x ∈ T₃, (vE : NativeSporadic.Co1) * x = x * vE := fun x hx =>
    (mem_centralizer_singleton_iff.1 (mem_inf.1 (mem_inf.1 hx).1).2).symm
  rcases hdec with hdd | hdd
  · rw [hdd]
    exact hcases
  · rw [hdd]
    rcases hcases with h1 | h1
    · left
      intro x hx
      have e1 := conj_mul_of_comm (v := (δ' : NativeSporadic.Co1)) (heT x hx)
      rw [e1, h1 x hx]
    · right
      intro x hx
      have e1 := conj_mul_of_comm (v := (δ' : NativeSporadic.Co1)) (heT x hx)
      rw [e1, h1 x hx]

end CFSG.Sporadic.Co1Patterson
