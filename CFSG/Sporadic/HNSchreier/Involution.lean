module

public import CFSG.Sporadic.HNSchreier.InvolSpec
public import CFSG.Sporadic.HNSchreier.Recognition
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.ONSchreier CFSG.Sporadic.HN.Local Matrix Equiv

abbrev matG (g : GL (Fin hnsData.d) (ZMod 5)) : Matrix (Fin 133) (Fin 133) (ZMod 5) := g.val

theorem matG_mul (g h : GL (Fin hnsData.d) (ZMod 5)) : matG (g * h) = matG g * matG h := rfl

theorem matG_one : matG 1 = 1 := rfl

theorem matG_ext {g h : GL (Fin hnsData.d) (ZMod 5)} (e : matG g = matG h) : g = h := Units.ext e

theorem matJ_eq_matG (g : JH) : matJ g = matG g := rfl

@[expose] def cU :
    GL (Fin hnsData.d) (ZMod 5) := ⟨matCx, matCx, matCx_sq, matCx_sq⟩

theorem matG_cU :
    matG cU = matCx := rfl

theorem cU_mul_self :
    cU * cU = 1 := matG_ext matCx_sq

theorem cU_inv :
    cU⁻¹ = cU := inv_eq_of_mul_eq_one_right cU_mul_self

@[expose] def dJ : JH := hWordJ LocalData.innerWord * (seedWordJ LocalData.outerWord)⁻¹

theorem matCx_eq_dS : matCx = matJ dJ * matS := by
  rw [dJ, matJ_mul]
  rfl

@[expose] def sU :
    GL (Fin hnsData.d) (ZMod 5) := (dJ : GL (Fin hnsData.d) (ZMod 5))⁻¹ * cU

theorem matG_sU : matG sU = matS := by
  rw [sU, matG_mul, matG_cU, matCx_eq_dS, ← mul_assoc]
  show matJ dJ⁻¹ * matJ dJ * matS = matS
  rw [matJ_inv_mul, one_mul]

theorem isUnit_matS :
    IsUnit matS := ⟨sU, matG_sU⟩

abbrev wJ : JH := (aJ * bJ ^ 2) ^ 8

theorem matJ_pow (g : JH) (n : ℕ) : matJ (g ^ n) = matJ g ^ n := map_pow matJHom g n

theorem matJ_wJ : matJ wJ = (matA * (matB * matB)) ^ 8 := by
  rw [matJ_pow, matJ_mul, matJ_pow, mat_aJ, mat_bJ, pow_two]

theorem sU_conj_aJ :
    sU * (aJ : GL (Fin hnsData.d) (ZMod 5)) * sU⁻¹ = aJ := by
  have key : sU * (aJ : GL (Fin hnsData.d) (ZMod 5)) = aJ * sU := by
    apply matG_ext
    rw [matG_mul, matG_mul, matG_sU, ← matJ_eq_matG, mat_aJ]
    exact matS_comm_A
  rw [key, mul_inv_cancel_right]

theorem sU_conj_bJ :
    sU * (bJ : GL (Fin hnsData.d) (ZMod 5)) * sU⁻¹ =
    ((wJ : GL (Fin hnsData.d) (ZMod 5)))⁻¹ * bJ * wJ := by
  have key : (wJ : GL (Fin hnsData.d) (ZMod 5)) * (sU * bJ) = bJ * (wJ * sU) := by
    apply matG_ext
    rw [matG_mul, matG_mul, matG_mul, matG_mul, matG_sU, ← matJ_eq_matG, ← matJ_eq_matG, mat_bJ,
      matJ_wJ]
    exact matS_conj_B
  calc sU * (bJ : GL (Fin hnsData.d) (ZMod 5)) * sU⁻¹
      = ((wJ : GL (Fin hnsData.d) (ZMod 5)))⁻¹ * (wJ * (sU * bJ)) * sU⁻¹ := by group
    _ = ((wJ : GL (Fin hnsData.d) (ZMod 5)))⁻¹ * (bJ * (wJ * sU)) * sU⁻¹ := by rw [key]
    _ = ((wJ : GL (Fin hnsData.d) (ZMod 5)))⁻¹ * bJ * wJ := by group

theorem sU_conj_mem
    (g : JH) : sU * (g : GL (Fin hnsData.d) (ZMod 5)) * sU⁻¹ ∈ JH := by
  have hg : g ∈ Subgroup.closure ({aJ, bJ} : Set JH) := by
    rw [CFSG.Sporadic.F5.closure_ab hnsData]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [sU_conj_aJ]
      exact aJ.2
    · rw [sU_conj_bJ]
      exact mul_mem (mul_mem (inv_mem wJ.2) bJ.2) wJ.2
  | one =>
    rw [Subgroup.coe_one, mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have e : sU * ((x * y : JH) : GL (Fin hnsData.d) (ZMod 5)) * sU⁻¹ =
        (sU * x * sU⁻¹) * (sU * y * sU⁻¹) := by
      rw [Subgroup.coe_mul]
      group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : sU * ((x⁻¹ : JH) : GL (Fin hnsData.d) (ZMod 5)) * sU⁻¹ = (sU * x * sU⁻¹)⁻¹ := by
      rw [Subgroup.coe_inv]
      group
    rw [e]
    exact inv_mem hx

theorem cU_eq :
    cU = (dJ : GL (Fin hnsData.d) (ZMod 5)) * sU := by
  unfold sU
  group

theorem cU_conj_mem
    (g : JH) : cU * (g : GL (Fin hnsData.d) (ZMod 5)) * cU⁻¹ ∈ JH := by
  have e : cU * (g : GL (Fin hnsData.d) (ZMod 5)) * cU⁻¹ =
      (dJ : GL (Fin hnsData.d) (ZMod 5)) * (sU * g * sU⁻¹) *
        ((dJ : GL (Fin hnsData.d) (ZMod 5)))⁻¹ := by
    rw [cU_eq]
    group
  rw [e]
  exact mul_mem (mul_mem dJ.2 (sU_conj_mem g)) (inv_mem dJ.2)

@[expose] def conjC : JH ≃* JH where
  toFun g := ⟨cU * g * cU⁻¹, cU_conj_mem g⟩
  invFun g := ⟨cU * g * cU⁻¹, cU_conj_mem g⟩
  left_inv g := Subtype.ext (by
    show cU * (cU * (g : GL (Fin hnsData.d) (ZMod 5)) * cU⁻¹) * cU⁻¹ = g
    rw [cU_inv, ← mul_assoc, ← mul_assoc, cU_mul_self, one_mul, mul_assoc, cU_mul_self, mul_one])
  right_inv g := Subtype.ext (by
    show cU * (cU * (g : GL (Fin hnsData.d) (ZMod 5)) * cU⁻¹) * cU⁻¹ = g
    rw [cU_inv, ← mul_assoc, ← mul_assoc, cU_mul_self, one_mul, mul_assoc, cU_mul_self, mul_one])
  map_mul' g h := Subtype.ext (by
    show cU * ((g : GL (Fin hnsData.d) (ZMod 5)) * h) * cU⁻¹ =
      cU * (g : GL (Fin hnsData.d) (ZMod 5)) * cU⁻¹ * (cU * h * cU⁻¹)
    group)

theorem conjC_val
    (g : JH) : ((conjC g : JH) : GL (Fin hnsData.d) (ZMod 5)) = cU * g * cU⁻¹ :=
  rfl

theorem matJ_conjC
    (g : JH) : matJ (conjC g) = matCx * matJ g * matCx := by
  rw [matJ_eq_matG, conjC_val, cU_inv, matG_mul, matG_mul, matG_cU]

theorem conjC_conjC
    (g : JH) : conjC (conjC g) = g := conjC.left_inv g

theorem conj_matJ_range :
    {M | ∃ g : JH, M = matCx * matJ g * matCx} = Set.range matJ := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨conjC g, matJ_conjC g⟩
  · rintro ⟨g, rfl⟩
    exact ⟨conjC g, by rw [← matJ_conjC, conjC_conjC]⟩

theorem conjC_mem_HJ
    {h : JH} (hh : h ∈ HJ) : conjC h ∈ HJ := by
  rw [HJ_eq_vStabJ, mem_vStabJ] at hh ⊢
  rw [matJ_conjC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matCx_fix, hh, matCx_fix]

@[expose] def conjCH
    (h : HJ) : HJ := ⟨conjC h, conjC_mem_HJ h.2⟩

theorem matJ_conjCH
    (h : HJ) : matJ (conjCH h : JH) = matCx * matJ h * matCx := matJ_conjC h

theorem tauF_tauF
    (k : Fin 462) : tauF (tauF k) = k := by
  apply labPart_injective
  rw [labPart_tauF, labPart_tauF, ← mul_smul, Equiv.swap_mul_self, one_smul]

theorem conjCH_xVec
    (h : HJ) (k : Fin 462) :
    matJ (conjCH h : JH) *ᵥ xVec k = xVec (tauF (rhoH (hjEquiv h) (tauF k))) := by
  rw [matJ_conjCH, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matCx_xVec, HJ_xVec,
    matCx_xVec]

theorem thetaJ_conjCH
    (h : HJ) :
    (thetaJ (conjCH h) : Perm (Fin 12)) = swap 0 1 * (thetaJ h : Perm (Fin 12)) * swap 0 1 := by
  apply natHom_injective
  refine Equiv.ext fun S => ?_
  obtain ⟨k, rfl⟩ := labPart_bijective.2 S
  rw [natHom_apply, natHom_apply, ← thetaJ_equivariant, mul_smul, mul_smul, ← labPart_tauF,
    ← thetaJ_equivariant, ← labPart_tauF]
  apply congrArg labPart
  apply xVec_injective
  rw [← HJ_xVec, conjCH_xVec]

theorem closure_h1J_h2J :
    Subgroup.closure ({⟨h1J, h1J_mem⟩, ⟨h2J, h2J_mem⟩} : Set HJ) = ⊤ := by
  apply Subgroup.map_injective HJ.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem eq_thetaJ
    (θ : HJ ≃* alternatingGroup (Fin 12))
    (h1 : (θ ⟨h1J, h1J_mem⟩ : Perm (Fin 12)) = natPerm1)
    (h2 : (θ ⟨h2J, h2J_mem⟩ : Perm (Fin 12)) = natPerm2) : θ = thetaJ := by
  have key : ∀ h : HJ, θ h = thetaJ h := by
    intro h
    have hh : h ∈ Subgroup.closure ({⟨h1J, h1J_mem⟩, ⟨h2J, h2J_mem⟩} : Set HJ) := by
      rw [closure_h1J_h2J]
      trivial
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Subtype.ext (h1.trans thetaJ_h1.symm)
      · exact Subtype.ext (h2.trans thetaJ_h2.symm)
    | one => rw [map_one, map_one]
    | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
    | inv x _ hx => rw [map_inv, map_inv, hx]
  exact MulEquiv.ext key

theorem tau_not_mem : swap (0 : Fin 12) 1 ∉ alternatingGroup (Fin 12) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)]
  decide

theorem matCx_not_range
    (g : JH) : matJ g ≠ matCx := by
  intro hg
  have hgH : g ∈ HJ := by
    rw [HJ_eq_vStabJ, mem_vStabJ, hg]
    exact matCx_fix
  have hinv : matJ g⁻¹ = matCx := by
    calc matJ g⁻¹ = (matCx * matCx) * matJ g⁻¹ := by rw [matCx_sq, one_mul]
      _ = matCx * (matJ g * matJ g⁻¹) := by rw [hg, mul_assoc]
      _ = matCx := by rw [matJ_mul_inv, mul_one]
  have hconj : ∀ h : HJ, conjCH h = ⟨g, hgH⟩ * h * (⟨g, hgH⟩ : HJ)⁻¹ := by
    intro h
    apply Subtype.ext
    apply matJ_injective
    rw [matJ_conjCH]
    show matCx * matJ h * matCx = matJ (g * h * g⁻¹)
    rw [matJ_mul, matJ_mul, hg, hinv]
  set π : Perm (Fin 12) := (thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1
  have hcomm : ∀ σ ∈ alternatingGroup (Fin 12), π * σ = σ * π := by
    intro σ hσ
    obtain ⟨h, hh⟩ := thetaJ.surjective ⟨σ, hσ⟩
    have e := thetaJ_conjCH h
    rw [hconj, map_mul, map_mul, map_inv] at e
    have e' : (thetaJ h : Perm (Fin 12)) = σ := congrArg Subtype.val hh
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
    rw [e'] at e
    have hs : swap (0 : Fin 12) 1 * swap 0 1 = 1 := Equiv.swap_mul_self 0 1
    have e2 : swap 0 1 * σ = (thetaJ ⟨g, hgH⟩ : Perm (Fin 12)) * σ *
        (thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1 := by
      rw [e, mul_assoc (swap 0 1 * σ) (swap 0 1) (swap 0 1), hs, mul_one]
    show (thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1 * σ =
      σ * ((thetaJ ⟨g, hgH⟩ : Perm (Fin 12))⁻¹ * swap 0 1)
    rw [mul_assoc, e2]
    group
  have hπ := eq_one_of_commute_alt hcomm
  apply tau_not_mem
  have : swap (0 : Fin 12) 1 = (thetaJ ⟨g, hgH⟩ : Perm (Fin 12)) := by
    have := congrArg (fun x => (thetaJ ⟨g, hgH⟩ : Perm (Fin 12)) * x) hπ
    simp only [π, mul_one] at this
    rw [← this, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [this]
  exact (thetaJ ⟨g, hgH⟩).2

theorem matB_sq : matB ^ 2 = matB * matB := pow_two matB

theorem ctuc_hn_explicit_normalizing_involution :
    IsUnit matS ∧ matS * matA = matA * matS ∧
    matS * matB = ((matA * matB ^ 2) ^ 8)⁻¹ * matB * (matA * matB ^ 2) ^ 8 * matS ∧
    matCx = matCpin ∧ matCx * matCx = 1 ∧ matCx *ᵥ fixedVector = fixedVector ∧
    {M | ∃ g : JH, M = matCx * matJ g * matCx} = Set.range matJ ∧
    (∀ h ∈ HJ, ∃ h' ∈ HJ, matJ h' = matCx * matJ h * matCx) ∧
    (∀ θ : HJ ≃* alternatingGroup (Fin 12), (θ ⟨h1J, h1J_mem⟩ : Perm (Fin 12)) = natPerm1 →
      (θ ⟨h2J, h2J_mem⟩ : Perm (Fin 12)) = natPerm2 → ∀ h h' : HJ,
        matJ h' = matCx * matJ h * matCx →
          (θ h' : Perm (Fin 12)) = swap 0 1 * (θ h : Perm (Fin 12)) * swap 0 1) ∧
    (∀ k : Fin 462, ∃ k' : Fin 462,
      matCx *ᵥ xVec k = xVec k' ∧ labPart k' = swap (0 : Fin 12) 1 • labPart k) ∧
    matCx ≠ 1 ∧ ∀ g : JH, matJ g ≠ matCx := by
  refine ⟨isUnit_matS, matS_comm_A, ?_, matCx_eq_matC, matCx_sq, matCx_fix, conj_matJ_range,
    fun h hh => ⟨conjC h, conjC_mem_HJ hh, matJ_conjC h⟩, ?_,
    fun k => ⟨tauF k, matCx_xVec k, labPart_tauF k⟩, matCx_ne_one, matCx_not_range⟩
  · have hW : ((matA * matB ^ 2) ^ 8)⁻¹ * (matA * matB ^ 2) ^ 8 = 1 := by
      rw [matB_sq, ← matJ_wJ]
      exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1
        ⟨⟨_, _, matJ_mul_inv wJ, matJ_inv_mul wJ⟩, rfl⟩)
    calc matS * matB = ((matA * matB ^ 2) ^ 8)⁻¹ * (matA * matB ^ 2) ^ 8 * (matS * matB) := by
          rw [hW, one_mul]
      _ = ((matA * matB ^ 2) ^ 8)⁻¹ * ((matA * matB ^ 2) ^ 8 * (matS * matB)) := by
          rw [mul_assoc]
      _ = ((matA * matB ^ 2) ^ 8)⁻¹ * matB * (matA * matB ^ 2) ^ 8 * matS := by
          rw [matB_sq, matS_conj_B]
          simp only [mul_assoc]
  · intro θ h1 h2 h h' hh'
    rw [eq_thetaJ θ h1 h2]
    have e : h' = conjCH h := Subtype.ext (matJ_injective (hh'.trans (matJ_conjCH h).symm))
    rw [e]
    exact thetaJ_conjCH h

end CFSG.Sporadic.HNSchreier
