module

public import CFSG.GroupTheory.F4ModuleFromOperator
public import CFSG.RankThree.GF2n.Parrott.WAction

public section

noncomputable section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.Fischer
open scoped commutatorElement
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GroupTheory.F4ModuleFromOperator
open CFSG.GroupTheory.HeisenbergF4

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)
variable (h : Tim79a.ParrottHyp z)

instance instAddCommGroupWsubModule :
    AddCommGroup ↥(WsubModule (z := z) (D := D) h) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  infer_instance

instance instModuleZMod2WsubModule :
    Module (ZMod 2) ↥(WsubModule (z := z) (D := D) h) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  infer_instance

@[expose] def sigma1O3H : ↥(O3H D) :=
  ⟨sigma1Nine (z := z) D, sigma1Nine_mem_O3H (z := z) D⟩

abbrev Wc :
    WsubModule (z := z) (D := D) h →ₗ[ZMod 2] WsubModule (z := z) (D := D) h :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  Wact (z := z) (D := D) h (sigma1O3H (z := z) (D := D))

@[simp] theorem Wc_coe_apply (v : WsubModule (z := z) (D := D) h) :
    ((Wc (z := z) (D := D) h v : WsubModule (z := z) (D := D) h) :
        Additive (QuotientV.V z)) =
      conjVLinearMap h (sigma1Nine (z := z) D) v :=
  rfl

theorem Wc_sq_add_Wc_add_one :
    Wc (z := z) (D := D) h * Wc (z := z) (D := D) h +
        Wc (z := z) (D := D) h + 1 = 0 := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  simpa only [Wc, sigma1O3H, rhoO3H_apply] using rhoO3H_omega (z := z) (D := D) h

abbrev Wf4Module :
    Module F4 (WsubModule (z := z) (D := D) h) :=
  Operator.f4Module (W := WsubModule (z := z) (D := D) h)
    (Wc (z := z) (D := D) h) (Wc_sq_add_Wc_add_one (z := z) (D := D) h)

instance instModuleF4WsubModule :
    Module F4 (WsubModule (z := z) (D := D) h) :=
  Wf4Module (z := z) (D := D) h

omit
  hN in
theorem conjVLinearMap_comm_of_commute {x y : ↥(H z)} (hcomm : Commute x y) :
    conjVLinearMap h x * conjVLinearMap h y =
      conjVLinearMap h y * conjVLinearMap h x := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  ext v
  simp only [Module.End.mul_apply, conjVLinearMap_apply, toMul_ofMul]
  set w : QuotientV.V z := Additive.toMul v
  calc conjV h x (conjV h y w)
      = (conjV h x * conjV h y) w := by rw [MulAut.mul_apply]
    _ = (conjV h (x * y)) w := by rw [map_mul]
    _ = (conjV h (y * x)) w := by rw [hcomm.eq]
    _ = (conjV h y * conjV h x) w := by rw [map_mul]
    _ = conjV h y (conjV h x w) := by rw [MulAut.mul_apply]

theorem conjVLinearMap_mem_WsubModule_of_commute (x : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) x) :
    ∀ v ∈ WsubModule (z := z) (D := D) h,
      conjVLinearMap h x v ∈ WsubModule (z := z) (D := D) h := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  intro v hv
  have hcommV : conjV h x * conjV h (sigma1Nine (z := z) D) =
      conjV h (sigma1Nine (z := z) D) * conjV h x := (hcomm.symm.map (conjV h)).eq
  rw [mem_WsubModule_iff, conjVLinearMap_apply]
  simpa using conjV_mem_Wsub_of_commute (z := z) (D := D) h hcommV
    (Additive.toMul v) (by rwa [mem_WsubModule_iff] at hv)

@[expose] def Wsigma2Map (σ₂ : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    WsubModule (z := z) (D := D) h →ₗ[ZMod 2] WsubModule (z := z) (D := D) h :=
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  (conjVLinearMap h σ₂).restrict
    (conjVLinearMap_mem_WsubModule_of_commute (z := z) (D := D) h σ₂ hcomm)

@[simp] theorem Wsigma2Map_coe_apply (σ₂ : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (v : WsubModule (z := z) (D := D) h) :
    ((Wsigma2Map (z := z) (D := D) h σ₂ hcomm v :
        WsubModule (z := z) (D := D) h) : Additive (QuotientV.V z)) =
      conjVLinearMap h σ₂ v :=
  rfl

theorem Wsigma2Map_comp_Wc (σ₂ : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    (Wsigma2Map (z := z) (D := D) h σ₂ hcomm).comp (Wc (z := z) (D := D) h) =
      (Wc (z := z) (D := D) h).comp
        (Wsigma2Map (z := z) (D := D) h σ₂ hcomm) := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simpa [Wsigma2Map, Wc, sigma1O3H, Wact_apply, LinearMap.restrict_apply,
    LinearMap.comp_apply, Module.End.mul_apply] using LinearMap.congr_fun
    (conjVLinearMap_comm_of_commute (z := z) (h := h) hcomm.symm)
    (v : Additive (QuotientV.V z))

@[expose] def Wsigma2 (σ₂ : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂) :
    WsubModule (z := z) (D := D) h →ₗ[F4] WsubModule (z := z) (D := D) h :=
  letI : Module F4 (WsubModule (z := z) (D := D) h) := Wf4Module (z := z) (D := D) h
  Operator.f4LinearMap (Wc (z := z) (D := D) h)
    (Wc_sq_add_Wc_add_one (z := z) (D := D) h)
    (Wsigma2Map (z := z) (D := D) h σ₂ hcomm)
    (Wsigma2Map_comp_Wc (z := z) (D := D) h σ₂ hcomm)

@[simp] theorem Wsigma2_coe_apply (σ₂ : ↥(H z))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (v : WsubModule (z := z) (D := D) h) :
    ((Wsigma2 (z := z) (D := D) h σ₂ hcomm v :
        WsubModule (z := z) (D := D) h) : Additive (QuotientV.V z)) =
      (Wsigma2Map (z := z) (D := D) h σ₂ hcomm) v :=
  rfl

theorem fixW_eq_bot_of_centralizerJ_eq (σ₂ : ↥(H z))
    (hσ2ord : orderOf σ₂ = 3)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    fixW (z := z) (D := D) h σ₂ = ⊥ := by
  letI : CommGroup (QuotientV.V z) := commGroupV h
  letI : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hle : Fsub (z := z) (sigma1Nine (z := z) D) ≤ autFixedSubgroup (conjV h σ₂) := by
    intro v hv
    rw [mem_autFixedSubgroup]
    exact conjV_trivial_on_Fsub_of_le (z := z) h (le_of_eq hEq) v hv
  have hcardCJ : Nat.card (centralizerJ σ₂) = 16 := by
    rw [← hEq]
    exact card_centralizerJ_sigma1Nine (z := z) h D
  have hcardCJZ : Nat.card ↥(centralizerJ σ₂ ⊓ Subgroup.center (J z)) = 4 := by
    rw [← hEq]
    exact card_centralizerJ_inf_center_sigma1Nine (z := z) (D := D) h
  have hcop : Nat.Coprime (orderOf σ₂) (Nat.card (J z)) := by
    rw [hσ2ord, card_J h]
    norm_num
  have hformula := card_centralizerJ_eq_card_inf_mul_card_autFixed
    (z := z) (h := h) (x := σ₂) hcop
  rw [hcardCJ, hcardCJZ] at hformula
  have hcardFix : Nat.card ↥(autFixedSubgroup (conjV h σ₂)) = 4 := by
    omega
  have hEqFix : Fsub (z := z) (sigma1Nine (z := z) D) =
      autFixedSubgroup (conjV h σ₂) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardFix, card_Fsub_sigma1Nine (z := z) (D := D) h]
  have hfixSub : fixSubmodule (z := z) h σ₂ =
      FsubModule (z := z) (D := D) h := by
    ext v
    rw [mem_fixSubmodule_iff (z := z) h σ₂ v,
      mem_FsubModule_iff (z := z) (D := D) h v, ← hEqFix]
  have hFW : FsubModule (z := z) (D := D) h ⊓
      WsubModule (z := z) (D := D) h = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    rw [Submodule.mem_bot]
    apply Additive.toMul.injective
    have hmemF : Additive.toMul v ∈ Fsub (z := z) (sigma1Nine (z := z) D) :=
      (mem_FsubModule_iff (z := z) (D := D) h v).mp hv.1
    have hmemW : Additive.toMul v ∈ Wsub h (sigma1Nine (z := z) D) :=
      (mem_WsubModule_iff (z := z) (D := D) h v).mp hv.2
    have hmem := Subgroup.mem_inf.mpr ⟨hmemF, hmemW⟩
    rw [inf_Fsub_Wsub_sigma1Nine (z := z) (D := D) h] at hmem
    simpa using Subgroup.mem_bot.mp hmem
  change fixSubmodule (z := z) h σ₂ ⊓
    WsubModule (z := z) (D := D) h = ⊥
  rw [hfixSub, hFW]

end CFSG.RankThree.GF2n.Parrott
