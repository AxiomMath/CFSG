module

public import CFSG.Monster.B.TwoA.Unitary.SemilinearBase

public import CFSG.Monster.B.TwoA.Unitary.Stab891
public import CFSG.Monster.B.TwoA.Unitary.Order
public import CFSG.Monster.B.TwoA.Unitary.Witt
public meta import CFSG.Monster.B.TwoA.Unitary.BData
public import Certificates.Certificate3062
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import Certificates.Certificate3175Base
public import CFSG.Monster.B.TwoA.Unitary.Planes

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
open CFSG.ClassicalGroups.UnitaryFlag Matrix

@[expose] def Gp :
    Subgroup SigmaU6 := Subgroup.closure (Set.range slElt)

@[expose] def slEltG (k : Fin 17) :
    Gp := ⟨slElt k, Subgroup.subset_closure ⟨k, rfl⟩⟩

theorem closure_slEltG :
    Subgroup.closure (Set.range slEltG) = ⊤ := by
  apply Subgroup.map_injective (f := Gp.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rfl

theorem wAct_n6vec_mem
    (u : Usig) (j : Fin 891) : ∃ j', n6vec j' = wAct v0 u (n6vec j)
    := by
  obtain ⟨h, hh, e⟩ := exists_wAct_wFr j
  obtain ⟨j', hj'⟩ := (mem_range_n6vec_iff _).1
    ⟨h * u, Usig.mul_mem hh u.2, by rw [wAct_mul, Module.End.mul_apply, e]⟩
  exact ⟨j', hj'⟩

@[expose] def genU
    (k : Fin 17) : Usig := ⟨genK k, genK_mem_Usig k⟩

theorem closure_genU :
    Subgroup.closure (Set.range genU) = ⊤ := by
  apply Subgroup.map_injective (f := Usig.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact H6K_eq_Usig

theorem Lp_injective :
    Function.Injective Lp := plane_injective.comp
    b6Iso_bijective.1

theorem n6perm_injective
    (k : Fin 17) : Function.Injective
    (n6perm k)
    := by
  intro i j h
  apply n6vec_injective
  have hi := wAct_genK_n6vec k i
  have hj := wAct_genK_n6vec k j
  rw [h, ← hj] at hi
  have := congrArg (wAct v0 (genK k)⁻¹) hi
  rwa [wAct_inv_apply, wAct_inv_apply] at this

theorem sigmaAct_Lp_slElt (k : Fin 17) (j : Fin 891) :
    sigmaAct (Lp j) (slElt k) = Lp (n6perm k j) :=
  sigmaAct_slElt_plane k j

theorem Permutes.inv {x : SigmaU6}
    (hx : Permutes x) : Permutes x⁻¹
    := by
  classical
  let f : Fin 891 → Fin 891 := fun j => Classical.choose (hx j)
  have hf : ∀ j, sigmaAct (Lp j) x = Lp (f j) := fun j => Classical.choose_spec (hx j)
  have hinj : Function.Injective f := by
    intro i j h
    apply Lp_injective
    rw [← sigmaAct_inv_cancel (Lp i) x, ← sigmaAct_inv_cancel (Lp j) x, hf, hf, h]
  intro j
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hinj) j
  refine ⟨i, ?_⟩
  rw [← hi, ← hf, sigmaAct_inv_cancel]

theorem permutes_of_mem_Gp
    {x : SigmaU6} (hx : x ∈ Gp) : Permutes x
    := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact fun j => ⟨n6perm k j, sigmaAct_Lp_slElt k j⟩
  | one => exact fun j => ⟨j, sigmaAct_one _⟩
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

@[expose] def natIdx
    (u : Usig) (j : Fin 891) : Fin 891 := Classical.choose
    (wAct_n6vec_mem u j)

theorem n6vec_natIdx
    (u : Usig) (j : Fin 891) : n6vec (natIdx u j) = wAct v0 u
    (n6vec j) :=
  Classical.choose_spec (wAct_n6vec_mem u j)

theorem natIdx_genU
    (k : Fin 17) (j : Fin 891) : natIdx (genU k) j = n6perm k j :=
  n6vec_injective ((n6vec_natIdx _ j).trans (wAct_genK_n6vec k j))

theorem natIdx_one
    (j : Fin 891) : natIdx 1 j = j :=
  n6vec_injective (by rw [n6vec_natIdx]; exact congrArg (fun f => f (n6vec j)) wAct_one)

theorem natIdx_mul
    (u u' : Usig) (j : Fin 891) : natIdx (u * u') j = natIdx u'
    (natIdx u j) :=
  n6vec_injective (by
    rw [n6vec_natIdx, n6vec_natIdx, n6vec_natIdx, Subgroup.coe_mul, wAct_mul,
      Module.End.mul_apply])

@[expose, instance_reducible] def natAction :
    MulAction Usig (Fin 891) where
  smul u j := natIdx u⁻¹ j
  one_smul j := by
    change natIdx 1⁻¹ j = j
    rw [inv_one, natIdx_one]
  mul_smul u u' j := by
    change natIdx (u * u')⁻¹ j = natIdx u⁻¹ (natIdx u'⁻¹ j)
    rw [_root_.mul_inv_rev, natIdx_mul]

@[expose] def rhoN :
    Usig →* Equiv.Perm (Fin 891) := @MulAction.toPermHom Usig
    (Fin 891) _ natAction

theorem rhoN_injective :
    Function.Injective rhoN := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hfix : ∀ j, wAct v0 (u⁻¹ : Usig) (n6vec j) = n6vec j := by
    intro j
    rw [← n6vec_natIdx]
    exact congrArg n6vec (congrArg (fun p : Equiv.Perm (Fin 891) => p j) hu)
  have h1 := eq_one_of_fix_n6vec hfix
  have h2 : (u⁻¹ : Usig) = 1 := Subtype.ext h1
  rw [← inv_inv u, h2, inv_one]

theorem rhoN_apply
    (u : Usig) (j : Fin 891) : rhoN u j = natIdx u⁻¹ j := rfl

@[expose] def uIdx (x : Gp)
    (j : Fin 891) : Fin 891 :=
  Classical.choose (permutes_of_mem_Gp x.2 j)

theorem Lp_uIdx (x : Gp) (j : Fin 891)
    : Lp (uIdx x j) = sigmaAct
    (Lp j) x :=
  (Classical.choose_spec (permutes_of_mem_Gp x.2 j)).symm

theorem uIdx_mul (x y : Gp)
    (j : Fin 891) : uIdx (x * y) j = uIdx y
    (uIdx x j) :=
  Lp_injective (by rw [Lp_uIdx, Lp_uIdx, Lp_uIdx, Subgroup.coe_mul, sigmaAct_mul])

theorem uIdx_one (j : Fin 891) :
    uIdx 1 j = j :=
  Lp_injective (by rw [Lp_uIdx]; exact sigmaAct_one _)

@[expose, instance_reducible] def uAction :
    MulAction Gp (Fin 891)
    where
  smul x j := uIdx x⁻¹ j
  one_smul j := by
    change uIdx 1⁻¹ j = j
    rw [inv_one, uIdx_one]
  mul_smul x y j := by
    change uIdx (x * y)⁻¹ j = uIdx x⁻¹ (uIdx y⁻¹ j)
    rw [_root_.mul_inv_rev, uIdx_mul]

@[expose] def rhoU :
    Gp →* Equiv.Perm (Fin 891) :=
    @MulAction.toPermHom Gp (Fin 891) _ uAction

theorem rhoU_apply (x : Gp)
    (j : Fin 891) : rhoU x j = uIdx x⁻¹ j :=
    rfl

theorem rhoU_injective :
    Function.Injective rhoU := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hfix : ∀ j, sigmaAct (plane j) ((x⁻¹ : Gp) : SigmaU6) = plane j := by
    intro j
    obtain ⟨i, rfl⟩ := b6Iso_bijective.2 j
    change sigmaAct (Lp i) _ = Lp i
    rw [← Lp_uIdx]
    exact congrArg Lp (congrArg (fun p : Equiv.Perm (Fin 891) => p i) hx)
  have h1 := eq_one_of_sigmaAct_plane _ hfix
  have h2 : (x⁻¹ : Gp) = 1 := Subtype.ext h1
  rw [← inv_inv x, h2, inv_one]

theorem uIdx_slEltG (k : Fin 17)
    (j : Fin 891) : uIdx (slEltG k) j =
    n6perm k j :=
  Lp_injective (by rw [Lp_uIdx]; exact sigmaAct_Lp_slElt k j)

theorem rhoN_genU_eq
    (k : Fin 17) : rhoN (genU k) =
    rhoU (slEltG k)
    := by
  have hN : ∀ j, rhoN (genU k) (n6perm k j) = j := by
    intro j
    rw [← natIdx_genU, rhoN_apply, ← natIdx_mul, mul_inv_cancel, natIdx_one]
  have hU : ∀ j, rhoU (slEltG k) (n6perm k j) = j := by
    intro j
    rw [rhoU_apply, ← uIdx_slEltG, ← uIdx_mul, mul_inv_cancel, uIdx_one]
  have hsurj : Function.Surjective (n6perm k) :=
    Finite.injective_iff_surjective.1 (n6perm_injective k)
  ext j
  obtain ⟨i, rfl⟩ := hsurj j
  rw [hN, hU]

theorem range_rhoN_eq :
    rhoN.range = rhoU.range := by
  rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, ← closure_genU, ← closure_slEltG,
    MonoidHom.map_closure, MonoidHom.map_closure, ← Set.range_comp, ← Set.range_comp]
  congr 2
  funext k
  exact rhoN_genU_eq k

@[expose] noncomputable def phi0 :
    Usig ≃* Gp :=
  (MonoidHom.ofInjective rhoN_injective).trans ((MulEquiv.subgroupCongr range_rhoN_eq).trans
    (MonoidHom.ofInjective rhoU_injective).symm)

theorem rhoU_phi0
    (u : Usig) : rhoU (phi0 u) = rhoN
    u := by
  have h := MulEquiv.apply_symm_apply (MonoidHom.ofInjective rhoU_injective)
    ((MulEquiv.subgroupCongr range_rhoN_eq) ((MonoidHom.ofInjective rhoN_injective) u))
  exact congrArg Subtype.val h

theorem phi0_genU
    (k : Fin 17) : phi0 (genU k) =
    slEltG k :=
  rhoU_injective (by rw [rhoU_phi0, rhoN_genU_eq])

instance finite_Usig :
    Finite Usig :=
    Nat.finite_of_card_ne_zero
    (by rw [natCard_Usig]; norm_num)

theorem Gp_eq_top :
    Gp = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [← Nat.card_congr phi0.toEquiv, natCard_Usig, natCard_SigmaU6]

@[expose] noncomputable def phiU :
    Usig ≃* SigmaU6 :=
  phi0.trans ((MulEquiv.subgroupCongr Gp_eq_top).trans Subgroup.topEquiv)

theorem coe_phiU
    (u : Usig) : phiU u =
    (phi0 u : SigmaU6) := rfl

theorem phiU_genU
    (k : Fin 17) : phiU (genU k) =
    slElt k := by
  rw [coe_phiU, phi0_genU]
  rfl

theorem uIdx_phi0
    (u : Usig) (j : Fin 891) : uIdx
    (phi0 u) j = natIdx
    u j := by
  have h := congrArg (fun p : Equiv.Perm (Fin 891) => p j) (rhoU_phi0 u⁻¹)
  rw [rhoU_apply, rhoN_apply, map_inv, inv_inv, inv_inv] at h
  exact h

theorem plane_natIdx
    (u : Usig) (j : Fin 891) :
    plane (b6Iso (natIdx u j)) = sigmaAct (plane (b6Iso j)) (phiU u) := by
  change Lp (natIdx u j) = sigmaAct (Lp j) (phi0 u)
  rw [← uIdx_phi0, Lp_uIdx]

theorem exists_plane_of_isMaxIso
    {P : Submodule F4 V6}
    (hP : IsMaxIso P) : ∃ j, plane j = P := by
  obtain ⟨g, hg⟩ := exists_SUh_plane0 hP
  obtain ⟨j₀, hj₀⟩ := b6Iso_bijective.2 0
  have hx : ((⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd 0⟩ : SigmaU6) : SigmaU6) ∈ Gp := by
    rw [Gp_eq_top]
    trivial
  obtain ⟨j', hj'⟩ := permutes_of_mem_Gp hx j₀
  refine ⟨b6Iso j', ?_⟩
  change Lp j' = P
  rw [← hj', Lp, hj₀, sigmaAct_mk, subBarPow_zero, hg]

theorem isMaxIso_sigmaAct
    {P : Submodule F4 V6}
    (hP : IsMaxIso P)
    (x : SigmaU6) :
    IsMaxIso (sigmaAct P x) := by
  obtain ⟨j, rfl⟩ := exists_plane_of_isMaxIso hP
  obtain ⟨i, rfl⟩ := b6Iso_bijective.2 j
  have hx : x ∈ Gp := by rw [Gp_eq_top]; trivial
  obtain ⟨i', hi'⟩ := permutes_of_mem_Gp hx i
  change IsMaxIso (sigmaAct (Lp i) x)
  rw [hi']
  exact isMaxIso_plane _

theorem thetaEquiv_inl (g : SUh) :
    thetaEquiv ⟨(g : SUh ⧸ Zh), 1⟩ = ⟨(psiSU g : unitaryPSU hF4 6), 1⟩ := by
  change theta ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd 0⟩ = _
  rw [theta_mk, ite_eq_left rfl, mul_one]
  rfl

theorem thetaEquiv_frob :
    thetaEquiv ⟨1, Multiplicative.ofAdd 1⟩ =
      ⟨(PiSU : unitaryPSU hF4 6), Multiplicative.ofAdd 1⟩ := by
  change theta ⟨1, Multiplicative.ofAdd 1⟩ = _
  rw [theta_mk, ite_eq_right (by decide), map_one, one_mul]
  rfl

theorem native_unitary_six_semilinear_isomorphism :
    (∀ j, IsMaxIso (plane j)) ∧ Function.Injective plane ∧
    (∀ P : Submodule F4 V6, IsMaxIso P → ∃ j, plane j = P) ∧
    (∀ (P : Submodule F4 V6) (x : SigmaU6), IsMaxIso P → IsMaxIso (sigmaAct P x)) ∧
    (∀ x : SigmaU6, (∀ j, sigmaAct (plane j) x = plane j) → x = 1) ∧
    Function.Bijective b6Iso ∧
    (∀ k : Fin 17, (b6Mat k).det = 1 ∧ b6Mat k * hGram * (barM (b6Mat k))ᵀ = hGram) ∧
    (∀ k : Fin 17, b6Frob k = if (k : ℕ) = 5 then 1 else 0) ∧
    (∀ (P : Submodule F4 V6) (k : Fin 17),
      sigmaAct P (slElt k) = subMul (subBarPow (b6Frob k) P) (b6Mat k)) ∧
    (∀ (k : Fin 17) (j : Fin 891),
      plane (b6Iso (n6perm k j)) = sigmaAct (plane (b6Iso j)) (slElt k)) ∧
    (∃ Φ : Usig ≃* SigmaU6,
      (∀ (u : Usig) (j : Fin 891),
        plane (b6Iso (natIdx u j)) = sigmaAct (plane (b6Iso j)) (Φ u)) ∧
      ∀ k : Fin 17, Φ (genU k) = slElt k) ∧
    (∃ Θ : SigmaU6 ≃* PSU62,
      (∀ g : SUh, Θ ⟨(g : SUh ⧸ Zh), 1⟩ = ⟨(psiSU g : unitaryPSU hF4 6), 1⟩) ∧
      Θ ⟨1, Multiplicative.ofAdd 1⟩ = ⟨(PiSU : unitaryPSU hF4 6), Multiplicative.ofAdd 1⟩) ∧
    IsSimpleGroup (unitaryPSU hF4 6) ∧
    Nat.card (unitaryPSU hF4 6) = 9196830720 ∧ Nat.card SigmaU6 = 18393661440 :=
  ⟨isMaxIso_plane, plane_injective, fun _ hP => exists_plane_of_isMaxIso hP,
    fun _ x hP => isMaxIso_sigmaAct hP x, eq_one_of_sigmaAct_plane, b6Iso_bijective,
    fun k => ⟨b6Mat_det k, b6Mat_gram k⟩, b6Frob_eq, sigmaAct_slElt,
    fun k j => (sigmaAct_slElt_plane k j).symm, ⟨phiU, plane_natIdx, phiU_genU⟩,
    ⟨thetaEquiv, thetaEquiv_inl, thetaEquiv_frob⟩, isSimpleGroup_unitaryPSU, natCard_unitaryPSU,
    natCard_SigmaU6⟩

end CFSG.Monster.B.TwoA.Unitary
