module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixI.proposition_2

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFAppendixI Representation
open scoped IsMulCommutative

universe uL uN

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
public theorem claim3_appendixI_scalar_adapter_KP
    {r p : Nat} [Fact r.Prime]
    {L : Type uL} {N : Type uN}
    [Group L] [Finite L] [Group N] [Finite N] [Nontrivial N]
    [IsElementaryAbelian r N] [MulDistribMulAction L N]
    (K P : Subgroup L) [K.Normal] [IsCyclic K]
    [FaithfulSMul K N]
    [Representation.IsIrreducible
      (AppendixIRepresentationOfT
        (p := r) (E := N) (⊤ : Subgroup K))]
    (act : P →* MulAut K)
    (hact_coe : ∀ (a : P) (k : K),
      (((act a) k : K) : L) = (a : L) * (k : L) * (a : L)⁻¹)
    (hdim : Module.finrank (ZMod r) (Additive N) = p) :
    let T : Subgroup K := ⊤
    let Fr := AppendixIFpT (p := r) (E := N) T
    ∃ scalarR : K →* Frˣ,
      Nat.card Fr = r ^ p ∧
        Function.Injective scalarR ∧
          Subring.closure (Set.range fun k : K => (scalarR k : Fr)) = ⊤ ∧
            ∀ (a : P) (k : K) (x : Additive N),
              (Theory.Representation.ofElementaryAbelianAction
                  (A := L) (G := N) (p := r)) (a : L)
                    ((scalarR k : Fr).1 x) =
                (scalarR ((act a) k) : Fr).1
                  ((Theory.Representation.ofElementaryAbelianAction
                    (A := L) (G := N) (p := r)) (a : L) x) := by
  classical
  let T : Subgroup K := ⊤
  let rhoT := AppendixIRepresentationOfT (p := r) (E := N) T
  letI : FiniteDimensional (ZMod r) (Additive N) := Module.Finite.of_finite
  letI : Field (AppendixIEndT (p := r) (E := N) T) := endField_field rhoT
  letI : Finite (AppendixIEndT (p := r) (E := N) T) := endField_finite rhoT
  letI : Module (AppendixIEndT (p := r) (E := N) T) (Additive N) :=
    endFieldModule rhoT
  let Fr := AppendixIFpT (p := r) (E := N) T
  letI : Field Fr := (Finite.isField_of_domain Fr).toField
  letI : Module Fr (Additive N) :=
    Module.compHom (Additive N) Fr.val.toRingHom
  have hcardN : Nat.card N = r ^ p := by
    have hcard := Module.natCard_eq_pow_finrank
      (K := ZMod r) (V := Additive N)
    calc
      Nat.card N = Nat.card (Additive N) :=
        (Nat.card_congr Additive.toMul).symm
      _ = r ^ p := by simpa [hdim] using hcard
  have hFrCard : Nat.card Fr = r ^ p := by
    obtain ⟨fieldInst, hfield⟩ :=
      peterfalvi_appendixI_proposition_2_a
        (p := r) (n := p) (U := K) (E := N) T hcardN
    letI : Field Fr := fieldInst
    obtain ⟨moduleInst, hFrCard, _hFrFinrank, _hFrSmul⟩ := hfield
    letI : Module Fr (Additive N) := moduleInst
    exact hFrCard
  let tauF : T →* Fr :=
    { toFun := fun t =>
        ⟨AppendixITActionEnd (p := r) (E := N) T t,
          Algebra.subset_adjoin (Set.mem_range_self t)⟩
      map_one' := by
        ext x
        simp [AppendixITActionEnd_apply]
      map_mul' := by
        intro a b
        ext x
        simp [AppendixITActionEnd_apply, mul_smul] }
  let scalarTop : T →* Frˣ :=
    MonoidHom.toHomUnits (G := T) (M := Fr) tauF
  let toTop : K →* T := (Subgroup.topEquiv : T ≃* K).symm.toMonoidHom
  let scalarR : K →* Frˣ := scalarTop.comp toTop
  have hK_smul (k : K) (x : N) : k • x = (k : L) • x := rfl
  have hscalar_apply (k : K) (x : Additive N) :
      (scalarR k : Fr) • x =
        (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)) (k : L) x := by
    change (scalarR k : Fr).1 x = _
    simp [scalarR, scalarTop, toTop, tauF, T, AppendixITActionEnd_apply]
    rfl
  have hscalar_injective : Function.Injective scalarR := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := N)
    intro x
    have h := congrArg
      (fun u : Frˣ => (u : Fr) • (Additive.ofMul x : Additive N)) hab
    change
      (scalarR a : Fr) • (Additive.ofMul x : Additive N) =
        (scalarR b : Fr) • (Additive.ofMul x : Additive N) at h
    rw [hscalar_apply, hscalar_apply] at h
    apply Additive.ofMul.injective
    simpa only [Theory.Representation.ofElementaryAbelianAction_apply_ofMul,
      hK_smul] using h
  have hscalar_end (k : K) :
      (scalarR k : Fr).1 =
        AppendixITActionEnd (p := r) (E := N) T (toTop k) := by
    ext x
    have h : (scalarR k : Fr).1 x =
        (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)) (k : L) x :=
      hscalar_apply k x
    simpa [AppendixITActionEnd_apply, toTop, T, hK_smul] using h
  let scalarSet : Set Fr := Set.range fun k : K => (scalarR k : Fr)
  have hscalarSet_closure : Subring.closure scalarSet = ⊤ := by
    apply top_unique
    intro z _hz
    have hz := z.property
    refine Algebra.adjoin_induction
      (p := fun y hy => (⟨y, hy⟩ : Fr) ∈ Subring.closure scalarSet)
      ?_ ?_ ?_ ?_ hz
    · intro y hy
      rcases hy with ⟨t, rfl⟩
      apply Subring.subset_closure
      refine ⟨(t : T), ?_⟩
      apply Subtype.ext
      exact (hscalar_end (t : T)).symm
    · intro c
      have hc : ((c.cast : Int) : Fr) ∈ Subring.closure scalarSet :=
        intCast_mem (Subring.closure scalarSet) c.cast
      have heq :
          (⟨(algebraMap (ZMod r) (AppendixIEndT (p := r) (E := N) T)) c,
            Subalgebra.algebraMap_mem Fr c⟩ : Fr) = ((c.cast : Int) : Fr) := by
        apply Subtype.ext
        calc
          (algebraMap (ZMod r) (AppendixIEndT (p := r) (E := N) T)) c =
              (algebraMap (ZMod r) (AppendixIEndT (p := r) (E := N) T))
                ((c.cast : Int) : ZMod r) :=
            congrArg
              (algebraMap (ZMod r) (AppendixIEndT (p := r) (E := N) T))
              (ZMod.intCast_zmod_cast c).symm
          _ = ((c.cast : Int) : AppendixIEndT (p := r) (E := N) T) :=
            map_intCast
              (algebraMap (ZMod r) (AppendixIEndT (p := r) (E := N) T)) c.cast
          _ = (((c.cast : Int) : Fr) : AppendixIEndT (p := r) (E := N) T) := rfl
      rw [heq]
      exact hc
    · intro x y hx hy hxmem hymem
      exact (Subring.closure scalarSet).add_mem hxmem hymem
    · intro x y hx hy hxmem hymem
      exact (Subring.closure scalarSet).mul_mem hxmem hymem
  have hcompat (a : P) (k : K) (x : Additive N) :
      (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)) (a : L) ((scalarR k : Fr).1 x) =
        (scalarR ((act a) k) : Fr).1
          ((Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L) x) := by
    let rho : Representation (ZMod r) L (Additive N) :=
      Theory.Representation.ofElementaryAbelianAction (A := L) (G := N) (p := r)
    change
      rho (a : L) ((scalarR k : Fr) • x) =
        (scalarR ((act a) k) : Fr) • rho (a : L) x
    calc
      rho (a : L) ((scalarR k : Fr) • x) =
          rho (a : L) (rho (k : L) x) := by rw [hscalar_apply]
      _ = (rho (a : L) * rho (k : L)) x := rfl
      _ = rho ((a : L) * (k : L)) x := by rw [map_mul]
      _ = rho ((((act a) k : K) : L) * (a : L)) x := by
        congr 2
        rw [hact_coe]
        group
      _ = (rho (((act a) k : K) : L) * rho (a : L)) x := by rw [map_mul]
      _ = rho (((act a) k : K) : L) (rho (a : L) x) := rfl
      _ = (scalarR ((act a) k) : Fr) • rho (a : L) x := by
        rw [hscalar_apply]
  exact ⟨scalarR, hFrCard, hscalar_injective, hscalarSet_closure, hcompat⟩

private theorem claim3_P_action_injective_of_conjugation
    {L N : Type*} [Group L] [Group N] [MulDistribMulAction L N]
    (K P : Subgroup L) [FaithfulSMul K N]
    (act : P →* MulAut K) (hact : Function.Injective act)
    (hact_coe : ∀ (a : P) (k : K),
      (((act a) k : K) : L) = (a : L) * (k : L) * (a : L)⁻¹) :
    Function.Injective (MulDistribMulAction.toMulAut P N) := by
  intro a b hab
  apply hact
  apply MulEquiv.ext
  intro k
  apply FaithfulSMul.eq_of_smul_eq_smul (α := N)
  intro x
  have hab_apply (y : N) : a • y = b • y := by
    exact congrArg (fun e : MulAut N => e y) hab
  have hab_inv :
      (MulDistribMulAction.toMulAut P N) a⁻¹ =
        (MulDistribMulAction.toMulAut P N) b⁻¹ := by
    rw [map_inv, map_inv, hab]
  have hab_inv_apply (y : N) : a⁻¹ • y = b⁻¹ • y := by
    exact congrArg (fun e : MulAut N => e y) hab_inv
  change (((act a) k : K) : L) • x = (((act b) k : K) : L) • x
  calc
    (((act a) k : K) : L) • x =
        (a : L) • ((k : L) • ((a : L)⁻¹ • x)) := by
      rw [hact_coe]
      simp [mul_smul]
    _ = (b : L) • ((k : L) • ((b : L)⁻¹ • x)) := by
      change a • ((k : K) • (a⁻¹ • x)) = b • ((k : K) • (b⁻¹ • x))
      rw [hab_inv_apply, hab_apply]
    _ = (((act b) k : K) : L) • x := by
      rw [hact_coe]
      simp [mul_smul]

private theorem claim3_smul_left_injective
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (y : V) (hy : y ≠ 0) :
    Function.Injective (fun z : F => z • y) := by
  intro a b hab
  apply sub_eq_zero.mp
  by_contra hne
  have hzero : (a - b) • y = 0 := by
    calc
      (a - b) • y = a • y - b • y := sub_smul a b y
      _ = 0 := sub_eq_zero.mpr hab
  apply hy
  calc
    y = (1 : F) • y := by simp
    _ = ((a - b)⁻¹ * (a - b)) • y := by rw [inv_mul_cancel₀ hne]
    _ = (a - b)⁻¹ • ((a - b) • y) := mul_smul _ _ _
    _ = 0 := by rw [hzero, smul_zero]

private theorem claim3_appendixI_semilinear_unique
    {G F U : Type*} [Group G] [Field F] [Group U]
    (Q0 : Subgroup G) (q0_add : Q0 ≃* Multiplicative F)
    (u_add : U →* (Q0 ≃* Q0)) (s : Q0) (hs : (s : G) ≠ 1)
    (u : U) (σ τ : F ≃+* F)
    (hσ : ∀ lambda : F, ∀ x : Q0,
      u_add u (q0_add.symm
        (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
      q0_add.symm
        (Multiplicative.ofAdd
          (σ lambda * Multiplicative.toAdd (q0_add (u_add u x)))))
    (hτ : ∀ lambda : F, ∀ x : Q0,
      u_add u (q0_add.symm
        (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
      q0_add.symm
        (Multiplicative.ofAdd
          (τ lambda * Multiplicative.toAdd (q0_add (u_add u x))))) :
    σ = τ := by
  ext lambda
  have hs_ne : s ≠ 1 := by
    intro hsone
    exact hs (congrArg Subtype.val hsone)
  have hus_ne : u_add u s ≠ 1 := by
    intro husone
    apply hs_ne
    apply (u_add u).injective
    simpa using husone
  have hus_coord_ne : Multiplicative.toAdd (q0_add (u_add u s)) ≠ 0 := by
    intro huszero
    apply hus_ne
    apply q0_add.injective
    simpa using (toAdd_eq_zero.mp huszero)
  have hcoord := congrArg Multiplicative.toAdd
    (congrArg q0_add ((hσ lambda s).symm.trans (hτ lambda s)))
  have hprod :
      σ lambda * Multiplicative.toAdd (q0_add (u_add u s)) =
        τ lambda * Multiplicative.toAdd (q0_add (u_add u s)) := by
    simpa using hcoord
  exact mul_right_cancel₀ hus_coord_ne hprod

private theorem claim3_appendixI_sigmaHom_of_per_element
    {G F U : Type*} [Group G] [Field F] [Group U]
    (Q0 : Subgroup G) (q0_add : Q0 ≃* Multiplicative F)
    (u_add : U →* (Q0 ≃* Q0))
    (s : Q0) (hs : (s : G) ≠ 1)
    (hper : ∀ u : U, ∃ σ : F ≃+* F, ∀ lambda : F, ∀ x : Q0,
      u_add u (q0_add.symm
        (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
      q0_add.symm
        (Multiplicative.ofAdd
          (σ lambda * Multiplicative.toAdd (q0_add (u_add u x))))) :
    ∃ σHom : U →* (F ≃+* F),
      ∀ (u : U) (lambda : F) (x : Q0),
        u_add u (q0_add.symm
          (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
        q0_add.symm
          (Multiplicative.ofAdd
            (σHom u lambda * Multiplicative.toAdd (q0_add (u_add u x)))) := by
  classical
  let σ : U → (F ≃+* F) := fun u => Classical.choose (hper u)
  have hσ (u : U) : ∀ lambda : F, ∀ x : Q0,
      u_add u (q0_add.symm
        (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
      q0_add.symm
        (Multiplicative.ofAdd
          (σ u lambda * Multiplicative.toAdd (q0_add (u_add u x)))) :=
    Classical.choose_spec (hper u)
  have hσ_one : σ 1 = 1 := by
    apply claim3_appendixI_semilinear_unique Q0 q0_add u_add s hs 1
    · exact hσ 1
    · intro lambda x
      simp
  have hσ_mul (u v : U) : σ (u * v) = σ u * σ v := by
    apply claim3_appendixI_semilinear_unique Q0 q0_add u_add s hs (u * v)
    · exact hσ (u * v)
    · intro lambda x
      calc
        u_add (u * v) (q0_add.symm
            (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
            u_add u (u_add v (q0_add.symm
              (Multiplicative.ofAdd
                (lambda * Multiplicative.toAdd (q0_add x))))) := by
              rw [map_mul]
              rfl
        _ = u_add u (q0_add.symm
            (Multiplicative.ofAdd
              (σ v lambda * Multiplicative.toAdd (q0_add (u_add v x))))) := by
              rw [hσ v lambda x]
        _ = q0_add.symm
            (Multiplicative.ofAdd
              (σ u (σ v lambda) *
                Multiplicative.toAdd (q0_add (u_add u (u_add v x))))) :=
              hσ u (σ v lambda) (u_add v x)
        _ = q0_add.symm
            (Multiplicative.ofAdd
              ((σ u * σ v) lambda *
                Multiplicative.toAdd (q0_add (u_add (u * v) x)))) := by
              have huv : u_add (u * v) x = u_add u (u_add v x) := by
                rw [map_mul]
                rfl
              rw [huv]
              rfl
  let σHom : U →* (F ≃+* F) :=
    { toFun := σ
      map_one' := hσ_one
      map_mul' := hσ_mul }
  exact ⟨σHom, hσ⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
public theorem claim3_appendixI_sigma_adapter_KP
    {r : Nat} [Fact r.Prime]
    {L N Fr : Type*}
    [Group L] [Group N] [Finite N] [Nontrivial N]
    [IsElementaryAbelian r N] [MulDistribMulAction L N]
    [Field Fr] [Finite Fr] [Module Fr (Additive N)]
    (K P : Subgroup L) [FaithfulSMul K N]
    (act : P →* MulAut K) (hact : Function.Injective act)
    (hact_coe : ∀ (a : P) (k : K),
      (((act a) k : K) : L) = (a : L) * (k : L) * (a : L)⁻¹)
    (scalarR : K →* Frˣ)
    (hcard : Nat.card Fr = Nat.card (Additive N))
    (hscalarSet_closure :
      Subring.closure (Set.range fun k : K => (scalarR k : Fr)) = ⊤)
    (hscalar_conj : ∀ (a : P) (k : K) (x : Additive N),
      (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)) (a : L) ((scalarR k : Fr) • x) =
        (scalarR ((act a) k) : Fr) •
          (Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L) x) :
    ∃ sigmaR : P →* (Fr ≃+* Fr),
      ∀ (a : P) (k : K),
        scalarR ((act a) k) =
          Units.map (sigmaR a).toMonoidWithZeroHom (scalarR k) := by
  classical
  have hP_smul (a : P) (x : N) : a • x = (a : L) • x := rfl
  obtain ⟨s, hs⟩ : ∃ s : N, s ≠ 1 := exists_ne 1
  let sAdd : Additive N := Additive.ofMul s
  have hsAdd : sAdd ≠ 0 := by simpa [sAdd] using hs
  let toN : Fr →+ Additive N :=
    { toFun := fun z => z • sAdd
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }
  have htoN_injective : Function.Injective toN := by
    intro a b hab
    apply claim3_smul_left_injective sAdd hsAdd
    exact hab
  letI : Fintype Fr := Fintype.ofFinite Fr
  letI : Fintype (Additive N) := Fintype.ofFinite (Additive N)
  have htoN_card : Fintype.card Fr = Fintype.card (Additive N) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have htoN_bijective : Function.Bijective toN :=
    (Fintype.bijective_iff_injective_and_card toN).2
      ⟨htoN_injective, htoN_card⟩
  let coord : Fr ≃+ Additive N :=
    AddEquiv.ofBijective toN htoN_bijective
  let coordR : N ≃* Multiplicative Fr :=
    { toFun := fun x =>
        Multiplicative.ofAdd (coord.symm (Additive.ofMul x))
      invFun := fun a =>
        Additive.toMul (coord (Multiplicative.toAdd a))
      left_inv := fun x => by simp
      right_inv := fun a => by simp
      map_mul' := fun x y => by
        change coord.symm (Additive.ofMul (x * y)) =
          coord.symm (Additive.ofMul x) + coord.symm (Additive.ofMul y)
        exact coord.symm.map_add _ _ }
  let Q0 : Subgroup N := ⊤
  let topEquiv : Q0 ≃* N := Subgroup.topEquiv
  let q0_add : Q0 ≃* Multiplicative Fr := topEquiv.trans coordR
  have hq0_scalar (lambda : Fr) (x : Q0) :
      q0_add.symm
          (Multiplicative.ofAdd
            (lambda * Multiplicative.toAdd (q0_add x))) =
        ⟨Additive.toMul
          (lambda • Additive.ofMul ((x : Q0) : N)), Subgroup.mem_top _⟩ := by
    apply Subtype.ext
    change Additive.toMul
        (coord (lambda * coord.symm (Additive.ofMul ((x : Q0) : N)))) =
      Additive.toMul (lambda • Additive.ofMul ((x : Q0) : N))
    apply Additive.toMul.injective
    change toN (lambda * coord.symm (Additive.ofMul ((x : Q0) : N))) =
      lambda • Additive.ofMul ((x : Q0) : N)
    have hcoord_apply :
        toN (coord.symm (Additive.ofMul ((x : Q0) : N))) =
          Additive.ofMul ((x : Q0) : N) := by
      change coord (coord.symm (Additive.ofMul ((x : Q0) : N))) =
        Additive.ofMul ((x : Q0) : N)
      exact coord.apply_symm_apply _
    calc
      toN (lambda * coord.symm (Additive.ofMul ((x : Q0) : N))) =
          lambda • toN (coord.symm (Additive.ofMul ((x : Q0) : N))) := by
            change (lambda * coord.symm (Additive.ofMul ((x : Q0) : N))) • sAdd =
              lambda • (coord.symm (Additive.ofMul ((x : Q0) : N)) • sAdd)
            rw [mul_smul]
      _ = lambda • Additive.ofMul ((x : Q0) : N) := by rw [hcoord_apply]
  let u_add : P →* (Q0 ≃* Q0) :=
    { toFun := fun a =>
        topEquiv.trans ((MulDistribMulAction.toMulAut P N) a) |>.trans
          topEquiv.symm
      map_one' := by
        ext x
        simp [topEquiv]
      map_mul' := by
        intro a b
        ext x
        simp [topEquiv, mul_smul] }
  have hu_add_apply (a : P) (x : Q0) :
      ((u_add a x : Q0) : N) = a • ((x : Q0) : N) := by
    rfl
  have hPaction :
      Function.Injective (MulDistribMulAction.toMulAut P N) :=
    claim3_P_action_injective_of_conjugation K P act hact hact_coe
  let scalarSet : Set Fr := Set.range fun k : K => (scalarR k : Fr)
  have hconjT : ∀ (a : P) (lambda : Fr),
      lambda ∈ scalarSet → ∃ c : Fr, ∀ x : Q0,
        u_add a (q0_add.symm
            (Multiplicative.ofAdd
              (lambda * Multiplicative.toAdd (q0_add x)))) =
          q0_add.symm
            (Multiplicative.ofAdd
              (c * Multiplicative.toAdd (q0_add (u_add a x)))) := by
    intro a lambda hlambda
    rcases hlambda with ⟨k, rfl⟩
    refine ⟨(scalarR ((act a) k) : Fr), ?_⟩
    intro x
    rw [hq0_scalar, hq0_scalar]
    apply Subtype.ext
    rw [hu_add_apply]
    apply Additive.ofMul.injective
    simpa [hu_add_apply, hP_smul,
      Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using
      hscalar_conj a k (Additive.ofMul ((x : Q0) : N))
  let sQ0 : Q0 := ⟨s, Subgroup.mem_top s⟩
  have hsQ0 : (sQ0 : N) ≠ 1 := by simpa [sQ0] using hs
  have hper := peterfalvi_appendixI_proposition_2_b_per_element
    Q0 q0_add u_add sQ0 hsQ0 scalarSet hscalarSet_closure hconjT
  rcases claim3_appendixI_sigmaHom_of_per_element
      Q0 q0_add u_add sQ0 hsQ0 hper with
    ⟨sigmaR, hsemilinear⟩
  have hsemilinear_action (a : P) (lambda : Fr) (x : Additive N) :
      (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)) (a : L) (lambda • x) =
        sigmaR a lambda •
          (Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L) x := by
    let xQ0 : Q0 :=
      ⟨Additive.toMul x, Subgroup.mem_top (Additive.toMul x)⟩
    have h := hsemilinear a lambda xQ0
    rw [hq0_scalar, hq0_scalar] at h
    have hN := congrArg (fun y : Q0 => Additive.ofMul ((y : Q0) : N)) h
    simpa [xQ0, hu_add_apply, hP_smul,
      Theory.Representation.ofElementaryAbelianAction_apply] using hN
  refine ⟨sigmaR, ?_⟩
  intro a k
  have hsImage :
      (Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)) (a : L) sAdd ≠ 0 := by
    intro hzero
    apply hsAdd
    apply (Representation.apply_bijective
      (Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)) (a : L)).1
    simpa using hzero
  have hcoeff :
      sigmaR a (scalarR k : Fr) = (scalarR ((act a) k) : Fr) := by
    apply claim3_smul_left_injective _ hsImage
    calc
      sigmaR a (scalarR k : Fr) •
          (Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L) sAdd =
        (Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L)
          ((scalarR k : Fr) • sAdd) :=
            (hsemilinear_action a (scalarR k : Fr) sAdd).symm
      _ = (scalarR ((act a) k) : Fr) •
          (Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L) sAdd :=
        hscalar_conj a k sAdd
  apply Units.ext
  simpa using hcoeff.symm


end PFchapter2
end CFSG.BenderSuzuki
