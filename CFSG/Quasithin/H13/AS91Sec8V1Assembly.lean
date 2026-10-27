module

public import CFSG.Quasithin.H13.AS91Sec8V1Map
public import CFSG.Quasithin.H13.AS91Sec8V1Cocycle
public import CFSG.Quasithin.H13.AS91Sec8V2

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.H.Mathieu CFSG.Quasithin.Asc94
open CFSG.ASVolI.ChH (M24g S24)
open scoped Pointwise

theorem autPres_subgroupCongr_trans {G : Type*} [Group G] {H K : Subgroup G} (h : H = K)
    (B : Subgroup G) (β : ↥K ≃* ↥K) :
    autPres H B ((MulEquiv.subgroupCongr h).trans (β.trans (MulEquiv.subgroupCongr h).symm)) ↔
      autPres K B β := by
  subst h
  rfl

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem todd_conj_inv_phiS (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (h : ↥(c.G3 ⊓ c.G1)) (e : ↥c.E) :
    r.todd ⟨(h : G)⁻¹ * (e : G) * (h : G), by
        have h1 := c.conj_mem_E (Subgroup.inclusion inf_le_right (h⁻¹)) e.2
        simpa using h1⟩ =
      (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h))⁻¹ (r.todd e) := by
  have h1 := c.todd_conj_phiS r hU (h⁻¹) e
  rw [_root_.map_inv (c.phiS r hU) h,
    _root_.map_inv (rho11 M24G.sextStab M24G.sextStab_le) (c.phiS r hU h)] at h1
  simpa only [Subgroup.coe_inv, inv_inv] using h1

theorem conj_prod_eq (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (h : ↥(c.G3 ⊓ c.G1)) (w : W11) (e eβ eα : ↥c.E) (A B : W11)
    (he : r.todd e = w) (heβ : r.todd eβ = B) (heα : r.todd eα = A) :
    (e : G) * (h : G) * (eβ : G) * (eα : G) * (e : G)⁻¹ =
      (h : G) * (r.todd.symm (M24G.coboundary M24G.sextStab M24G.sextStab_le w
        (c.phiS r hU h) * A * B) : G) := by
  have hheh : (h : G)⁻¹ * (e : G) * (h : G) ∈ c.E := by
    have h1 := c.conj_mem_E
      (⟨(h : G), (Subgroup.mem_inf.mp h.2).2⟩ : ↥c.G1)⁻¹ e.2
    simpa only [Subgroup.coe_inv, inv_inv] using h1
  let X : ↥c.E := ⟨(h : G)⁻¹ * (e : G) * (h : G) * (eβ : G) * (eα : G) * (e : G)⁻¹, by
    exact mul_mem (mul_mem (mul_mem hheh eβ.2) eα.2) (Subgroup.inv_mem c.E e.2)⟩
  have htoddX : r.todd X =
      (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h))⁻¹ w * B * A * w⁻¹ := by
    have hprod : X = ⟨(h : G)⁻¹ * (e : G) * (h : G), hheh⟩ * eβ * eα *
        ⟨(e : G)⁻¹, Subgroup.inv_mem c.E e.2⟩ := Subtype.ext rfl
    rw [hprod, map_mul, map_mul, map_mul, c.todd_conj_inv_phiS r hU h e, heβ, heα]
    have he_inv : r.todd ⟨(e : G)⁻¹, Subgroup.inv_mem c.E e.2⟩ = w⁻¹ := by
      have h := _root_.map_inv r.todd e
      rw [he] at h
      have h2 : (⟨(e : G)⁻¹, Subgroup.inv_mem c.E e.2⟩ : ↥c.E) = e⁻¹ := rfl
      rw [h2]
      exact h
    rw [he_inv, he]
  have hcomm : ∀ a B A w : W11, a * B * A * w⁻¹ = a * w⁻¹ * A * B := by
    intro a B A w
    simp only [M24G.W11_inv]
    ac_rfl
  have htodd_eq : (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h))⁻¹ w * B * A * w⁻¹ =
      (rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h))⁻¹ w * w⁻¹ * A * B :=
    hcomm _ _ _ _
  have hXeq : X = r.todd.symm ((rho11 M24G.sextStab M24G.sextStab_le (c.phiS r hU h))⁻¹ w *
      w⁻¹ * A * B) := by
    apply r.todd.injective
    rw [htoddX, MulEquiv.apply_symm_apply]
    exact htodd_eq
  have hval : (X : G) = (r.todd.symm (M24G.coboundary M24G.sextStab M24G.sextStab_le w
      (c.phiS r hU h) * A * B) : G) := congrArg (fun x : ↥c.E => (x : G)) hXeq
  calc (e : G) * (h : G) * (eβ : G) * (eα : G) * (e : G)⁻¹
      = (h : G) * (X : G) := by
        rw [show (X : G) =
          (h : G)⁻¹ * (e : G) * (h : G) * (eβ : G) * (eα : G) * (e : G)⁻¹ from rfl]
        group
    _ = (h : G) * (r.todd.symm (M24G.coboundary M24G.sextStab M24G.sextStab_le w
          (c.phiS r hU h) * A * B) : G) := by rw [hval]

theorem autPres_conj_twist (α : ↥c.G3 ≃* ↥c.G3) (a : Bool)
    (hα : ∀ x : ↥c.G3, (x : G) ∈ c.G1 ↔ ((α x : ↥c.G3) : G) ∈ c.G1)
    (ge : ↥c.G3) (hge : (ge : G) ∈ c.G1) :
    autPres c.G3 (c.G3 ⊓ c.G1) ((if a then α else MulEquiv.refl _).trans (MulAut.conj ge)) := by
  let αa : ↥c.G3 ≃* ↥c.G3 := if a then α else MulEquiv.refl _
  let φ : ↥c.G3 ≃* ↥c.G3 := αa.trans (MulAut.conj ge)
  change autPres c.G3 (c.G3 ⊓ c.G1) φ
  intro x
  have hφval : ((φ x : ↥c.G3) : G) = (ge : G) * ((αa x : ↥c.G3) : G) * (ge : G)⁻¹ := by
    rw [show φ x = MulAut.conj ge (αa x) from rfl, MulAut.conj_apply]
    rfl
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  simp only [x.2, (φ x).2, true_and]
  rw [hφval]
  have hconj : (ge : G) * ((αa x : ↥c.G3) : G) * (ge : G)⁻¹ ∈ c.G1 ↔
      ((αa x : ↥c.G3) : G) ∈ c.G1 := by
    constructor
    · intro h
      have h1 : (ge : G)⁻¹ * ((ge : G) * ((αa x : ↥c.G3) : G) * (ge : G)⁻¹) * (ge : G) ∈ c.G1 :=
        mul_mem (mul_mem (Subgroup.inv_mem c.G1 hge) h) hge
      simpa [mul_assoc] using h1
    · intro h
      exact mul_mem (mul_mem hge h) (Subgroup.inv_mem c.G1 hge)
  rw [hconj]
  by_cases ha : a
  · have hαa : αa = α := by simp [αa, ha]
    rw [hαa]
    exact hα x
  · have hαa : αa = MulEquiv.refl _ := by simp [αa, ha]
    rw [hαa]
    rfl

theorem autPres_twist_G1 (β : ↥c.G1 ≃* ↥c.G1) (b : Bool)
    (hβ : ∀ x : ↥c.G1, (x : G) ∈ c.G3 ↔ ((β x : ↥c.G1) : G) ∈ c.G3) :
    autPres c.G1 (c.G3 ⊓ c.G1) (if b then β else MulEquiv.refl _) := by
  let ψ₀ : ↥c.G1 ≃* ↥c.G1 := if b then β else MulEquiv.refl _
  change autPres c.G1 (c.G3 ⊓ c.G1) ψ₀
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  simp only [x.2, (ψ₀ x).2, true_and, and_true]
  by_cases hb : b
  · have hψ₀ : ψ₀ = β := by simp [ψ₀, hb]
    rw [hψ₀]
    exact hβ x
  · have hψ₀ : ψ₀ = MulEquiv.refl _ := by simp [ψ₀, hb]
    rw [hψ₀]
    rfl

theorem stabTwist_apply_val (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0)
    (β : ↥c.G1 ≃* ↥c.G1) (bB : Bool)
    (hβformula : ∀ h : ↥(c.G3 ⊓ c.G1),
      ((β (Subgroup.inclusion inf_le_right h) : ↥c.G1) : G) =
        (h : G) * (r.todd.symm (M24G.dBeta M24G.sextStab (c.phiS r hU h)) : G))
    (bs : ↥(MulAction.stabilizer G c.x0)) (h : ↥(c.G3 ⊓ c.G1))
    (hhval : (h : G) = (bs : G)) :
    (((((MulEquiv.subgroupCongr c.stab_x0).trans
        (((if bB then β else MulEquiv.refl _)).trans
          (MulEquiv.subgroupCongr c.stab_x0).symm)) bs :
      ↥(MulAction.stabilizer G c.x0)) : G)) =
      (h : G) * (r.todd.symm
        (if bB then M24G.dBeta M24G.sextStab (c.phiS r hU h) else 1) : G) := by
  have hb1 : ((MulEquiv.subgroupCongr c.stab_x0) bs : ↥c.G1) =
      Subgroup.inclusion inf_le_right h := by
    apply Subtype.ext
    rw [MulEquiv.subgroupCongr_apply]
    exact hhval.symm
  have h1 : (((((MulEquiv.subgroupCongr c.stab_x0).trans
        (((if bB then β else MulEquiv.refl _)).trans
          (MulEquiv.subgroupCongr c.stab_x0).symm)) bs :
      ↥(MulAction.stabilizer G c.x0)) : G)) =
      ((((if bB then β else MulEquiv.refl _) (Subgroup.inclusion inf_le_right h) : ↥c.G1)) : G) := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hb1]
    exact MulEquiv.subgroupCongr_symm_apply c.stab_x0 _
  rw [h1]
  by_cases hB : bB
  · rw [if_pos hB, hβformula h, if_pos hB]
  · rw [if_neg hB]
    have he : (r.todd.symm (if bB then M24G.dBeta M24G.sextStab (c.phiS r hU h) else 1) : G) = 1 := by
      rw [if_neg hB]
      simp
    rw [he, mul_one]
    rfl

theorem hypV_v1_of_parts {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)
    (r : ResM24T c) (hU : r.U₀ = M24G.sextFin 0) (hCoc : M24G.SextStabCocycle)
    (hA : ∀ θ : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1), c.IsInnerCocycle r hU θ)
    (hα : c.HasAlphaTwist r hU) (hβ : c.HasBetaTwist r hU) :
    ∀ θ : ↥(c.G3 ⊓ MulAction.stabilizer G c.x0) ≃* ↥(c.G3 ⊓ MulAction.stabilizer G c.x0),
      ∃ (φ : ↥c.G3 ≃* ↥c.G3)
        (ψ : ↥(MulAction.stabilizer G c.x0) ≃* ↥(MulAction.stabilizer G c.x0)),
        autPres c.G3 (c.G3 ⊓ MulAction.stabilizer G c.x0) φ ∧
        autPres (MulAction.stabilizer G c.x0) (c.G3 ⊓ MulAction.stabilizer G c.x0) ψ ∧
        ∀ b : ↥(c.G3 ⊓ MulAction.stabilizer G c.x0),
          ((θ b : ↥(c.G3 ⊓ MulAction.stabilizer G c.x0)) : G) = totFun φ (totFun ψ (b : G)) := by
  classical
  have hBI : (c.G3 ⊓ MulAction.stabilizer G c.x0) = (c.G3 ⊓ c.G1) := by rw [c.stab_x0]
  let eI : ↥(c.G3 ⊓ MulAction.stabilizer G c.x0) ≃* ↥(c.G3 ⊓ c.G1) :=
    MulEquiv.subgroupCongr hBI
  intro θ
  let θ' : ↥(c.G3 ⊓ c.G1) ≃* ↥(c.G3 ⊓ c.G1) := eI.symm.trans (θ.trans eI)
  obtain ⟨g, D, hgI, hD, hθ'⟩ := hA θ'
  obtain ⟨χ, α, hχ, hαpres, hαformula⟩ := hα
  obtain ⟨w, bA, bB, hDformula⟩ := hCoc D hD χ hχ
  obtain ⟨β, hβpres, hβformula⟩ := hβ
  have hgG3 : (g : G) ∈ c.G3 := (Subgroup.mem_inf.mp hgI).1
  have hgG1 : (g : G) ∈ c.G1 := (Subgroup.mem_inf.mp hgI).2
  let e : ↥c.E := r.todd.symm w
  have htodd_e : r.todd e = w := MulEquiv.apply_symm_apply r.todd w
  have heG3 : (e : G) ∈ c.G3 := c.E_le_G3 e.2
  have heG1 : (e : G) ∈ c.G1 := c.E_le_G1 e.2
  let ge : ↥c.G3 := ⟨(g : G) * (e : G), mul_mem hgG3 heG3⟩
  have hgeG1 : (ge : G) ∈ c.G1 := mul_mem hgG1 heG1
  let αa : ↥c.G3 ≃* ↥c.G3 := if bA then α else MulEquiv.refl _
  let φ : ↥c.G3 ≃* ↥c.G3 := αa.trans (MulAut.conj ge)
  let ψ₀ : ↥c.G1 ≃* ↥c.G1 := if bB then β else MulEquiv.refl _
  let eS : ↥(MulAction.stabilizer G c.x0) ≃* ↥c.G1 := MulEquiv.subgroupCongr c.stab_x0
  let ψ : ↥(MulAction.stabilizer G c.x0) ≃* ↥(MulAction.stabilizer G c.x0) :=
    eS.trans (ψ₀.trans eS.symm)
  have hφpres : autPres c.G3 (c.G3 ⊓ MulAction.stabilizer G c.x0) φ := by
    rw [autPres_congr hBI φ]
    exact c.autPres_conj_twist α bA hαpres ge hgeG1
  have hψpres : autPres (MulAction.stabilizer G c.x0) (c.G3 ⊓ MulAction.stabilizer G c.x0) ψ := by
    rw [autPres_congr hBI ψ]
    exact (autPres_subgroupCongr_trans c.stab_x0 (c.G3 ⊓ c.G1) ψ₀).mpr
      (c.autPres_twist_G1 β bB hβpres)
  refine ⟨φ, ψ, hφpres, hψpres, ?_⟩
  intro b
  let bs : ↥(MulAction.stabilizer G c.x0) := ⟨(b : G), (Subgroup.mem_inf.mp b.2).2⟩
  let h : ↥(c.G3 ⊓ c.G1) := eI b
  have hhval : (h : G) = (b : G) := MulEquiv.subgroupCongr_apply hBI b
  have hθapply : θ' h = eI (θ b) := by
    have h' : eI.symm h = b := by
      rw [show h = eI b from rfl, MulEquiv.symm_apply_apply]
    show eI (θ (eI.symm h)) = eI (θ b)
    rw [h']
  have hθb : ((θ b : ↥(c.G3 ⊓ MulAction.stabilizer G c.x0)) : G) =
      (g : G) * ((h : G) * (r.todd.symm (D (c.phiS r hU h)) : G)) * (g : G)⁻¹ := by
    have h1 := hθ' h
    rw [hθapply, MulEquiv.subgroupCongr_apply] at h1
    exact h1
  let s : ↥M24G.sextStab := c.phiS r hU h
  let A : W11 := if bA then (if χ s = 1 then 1 else M24G.sextClass (M24G.sextFin 0)) else 1
  let B : W11 := if bB then M24G.dBeta M24G.sextStab s else 1
  let eβ : ↥c.E := r.todd.symm B
  let eα : ↥c.E := r.todd.symm A
  have heβ : r.todd eβ = B := MulEquiv.apply_symm_apply r.todd B
  have heα : r.todd eα = A := MulEquiv.apply_symm_apply r.todd A
  have hDs : D s = M24G.coboundary M24G.sextStab M24G.sextStab_le w s * A * B :=
    hDformula s
  let eD : ↥c.E := r.todd.symm (M24G.coboundary M24G.sextStab M24G.sextStab_le w s * A * B)
  have hθb' : ((θ b : ↥(c.G3 ⊓ MulAction.stabilizer G c.x0)) : G) =
      (g : G) * ((h : G) * (eD : G)) * (g : G)⁻¹ := by
    rw [hθb, hDs]
  have hkey : (e : G) * (h : G) * (eβ : G) * (eα : G) * (e : G)⁻¹ =
      (h : G) * (eD : G) :=
    c.conj_prod_eq r hU h w e eβ eα A B htodd_e heβ heα
  have hψval : ((ψ bs : ↥(MulAction.stabilizer G c.x0)) : G) = (h : G) * (eβ : G) :=
    stabTwist_apply_val c r hU β bB hβformula bs h hhval
  have hψG3 : ((ψ bs : ↥(MulAction.stabilizer G c.x0)) : G) ∈ c.G3 := by
    have hmem : ((ψ bs : ↥(MulAction.stabilizer G c.x0)) : G) ∈
        (c.G3 ⊓ MulAction.stabilizer G c.x0) := (hψpres bs).mp b.2
    exact (Subgroup.mem_inf.mp hmem).1
  have htotψ : totFun ψ (b : G) = ((ψ bs : ↥(MulAction.stabilizer G c.x0)) : G) := by
    rw [totFun_of_mem ψ (show (b : G) ∈ MulAction.stabilizer G c.x0 from (Subgroup.mem_inf.mp b.2).2)]
  let k : ↥c.G3 := ⟨((ψ bs : ↥(MulAction.stabilizer G c.x0)) : G), hψG3⟩
  have htotφ : totFun φ (totFun ψ (b : G)) = ((φ k : ↥c.G3) : G) := by
    rw [htotψ]
    exact totFun_of_mem φ hψG3
  let eβI : ↥(c.G3 ⊓ c.G1) := ⟨(eβ : G),
    Subgroup.mem_inf.mpr ⟨c.E_le_G3 eβ.2, c.E_le_G1 eβ.2⟩⟩
  let hI : ↥(c.G3 ⊓ c.G1) := h * eβI
  have hk_eq : k = Subgroup.inclusion inf_le_left hI := by
    apply Subtype.ext
    show ((ψ bs : ↥(MulAction.stabilizer G c.x0)) : G) = (h : G) * (eβ : G)
    exact hψval
  have hphiS : c.phiS r hU hI = s := by
    show c.phiS r hU (h * eβI) = c.phiS r hU h
    rw [map_mul, (c.phiS_eq_one_iff r hU eβI).mpr eβ.2]
    simp
  have hαk : ((αa k : ↥c.G3) : G) = (h : G) * (eβ : G) * (eα : G) := by
    rw [hk_eq]
    by_cases hA : bA
    · have hαa : αa = α := by simp [αa, hA]
      rw [hαa]
      have h := hαformula hI
      rw [hphiS] at h
      rw [h]
      rw [show (eα : G) = (r.todd.symm (if χ s = 1 then 1 else
          M24G.sextClass (M24G.sextFin 0)) : G) from by
        show (r.todd.symm A : G) = _
        rw [show A = (if χ s = 1 then 1 else M24G.sextClass (M24G.sextFin 0)) from by
          simp [A, hA]]]
      rfl
    · have hαa : αa = MulEquiv.refl _ := by simp [αa, hA]
      rw [hαa]
      have heα1 : (eα : G) = 1 := by
        show (r.todd.symm A : G) = 1
        rw [show A = 1 from by simp [A, hA]]
        simp
      rw [heα1, mul_one]
      rfl
  have hφk : ((φ k : ↥c.G3) : G) = (ge : G) * ((αa k : ↥c.G3) : G) * (ge : G)⁻¹ := by
    rw [show φ k = MulAut.conj ge (αa k) from rfl, MulAut.conj_apply]
    rfl
  have hkeyB : (g : G) * (e : G) * ((h : G) * (eβ : G) * (eα : G)) * ((g : G) * (e : G))⁻¹ =
      (g : G) * ((h : G) * (eD : G)) * (g : G)⁻¹ := by
    have h1 : (e : G) * ((h : G) * (eβ : G) * (eα : G)) * (e : G)⁻¹ = (h : G) * (eD : G) := by
      simpa only [mul_assoc] using hkey
    calc (g : G) * (e : G) * ((h : G) * (eβ : G) * (eα : G)) * ((g : G) * (e : G))⁻¹
        = (g : G) * ((e : G) * ((h : G) * (eβ : G) * (eα : G)) * (e : G)⁻¹) *
            (g : G)⁻¹ := by group
      _ = (g : G) * ((h : G) * (eD : G)) * (g : G)⁻¹ := by rw [h1]
  have hφk' : ((φ k : ↥c.G3) : G) = (g : G) * ((h : G) * (eD : G)) * (g : G)⁻¹ := by
    rw [hφk, hαk]
    exact hkeyB
  calc ((θ b : ↥(c.G3 ⊓ MulAction.stabilizer G c.x0)) : G)
      = (g : G) * ((h : G) * (eD : G)) * (g : G)⁻¹ := hθb'
    _ = ((φ k : ↥c.G3) : G) := hφk'.symm
    _ = totFun φ (totFun ψ (b : G)) := htotφ.symm

end Loc49

end CFSG.Quasithin.H13.AS91
