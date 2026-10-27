module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestPCore
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvLin
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvQV
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvariant
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestLeviInv
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestCenter
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LieType.Chevalley.ExactNormalFormE

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

open scoped commutatorElement

private abbrev e6au_rhoPerm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

private abbrev e6au_rho (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  permLattice e6au_rhoPerm v

private theorem e6au_cartan_perm (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan (e6au_rhoPerm i) (e6au_rhoPerm j) = Tag.E6.cartan i j :=
  TwistTag.cartan_perm TwistTag.E6 i j

private theorem e6au_cartan_perm_symm (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan (e6au_rhoPerm.symm i) (e6au_rhoPerm.symm j) = Tag.E6.cartan i j :=
  cartan_perm_symm e6au_cartan_perm i j

private theorem e6au_iform_perm {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ : ∀ i j, Tag.E6.cartan (π i) (π j) = Tag.E6.cartan i j) (x y : Fin Tag.E6.rank → ℤ) :
    iform (permLattice π x) (permLattice π y) = iform x y := by
  simp only [iform, permLattice, Function.comp_apply, Tag.symmetrizedCartan, Tag.symmetrizer,
    Matrix.one_mul]
  rw [← Equiv.sum_comp π.symm (fun i => ∑ j, x i * Tag.E6.cartan i j * y j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π (fun j => x (π.symm i) * Tag.E6.cartan i j * y (π.symm j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply,
    show Tag.E6.cartan i (π j) = Tag.E6.cartan (π.symm i) j from by
      simpa using hπ (π.symm i) j]

private theorem e6au_permLattice_symm_apply {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (v : Fin τ.rank → ℤ) : permLattice π.symm (permLattice π v) = v := by
  ext i; simp [permLattice]

private theorem e6au_rho_lamE : permLattice e6au_rhoPerm lamE = lamE := by
  decide +kernel

private theorem e6au_rho_symm_lamE : permLattice e6au_rhoPerm.symm lamE = lamE := by
  decide +kernel

private theorem e6au_rho_qRoots : e6au_rho '' qRoots = qRoots := by
  ext β
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨hγ.1.permLattice e6au_cartan_perm, ?_⟩
    have h := e6au_iform_perm e6au_cartan_perm γ lamE
    rw [e6au_rho_lamE] at h
    rw [h]; exact hγ.2
  · intro hβ
    refine ⟨permLattice e6au_rhoPerm.symm β, ?_, e6au_permLattice_symm_apply _ _⟩
    refine ⟨hβ.1.permLattice e6au_cartan_perm_symm, ?_⟩
    have h := e6au_iform_perm e6au_cartan_perm_symm β lamE
    rw [e6au_rho_symm_lamE] at h
    rw [h]; exact hβ.2

private theorem e6au_rho_zRoots : e6au_rho '' zRoots = zRoots := by
  ext β
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨hγ.1.permLattice e6au_cartan_perm, ?_⟩
    have h := e6au_iform_perm e6au_cartan_perm γ lamE
    rw [e6au_rho_lamE] at h
    rw [h]; exact hγ.2
  · intro hβ
    refine ⟨permLattice e6au_rhoPerm.symm β, ?_, e6au_permLattice_symm_apply _ _⟩
    refine ⟨hβ.1.permLattice e6au_cartan_perm_symm, ?_⟩
    have h := e6au_iform_perm e6au_cartan_perm_symm β lamE
    rw [e6au_rho_symm_lamE] at h
    rw [h]; exact hβ.2

private theorem e6au_rho_mu1_subset :
    ∀ γ ∈ mu1List, e6au_rho γ ∈ mu2List := by
  decide +kernel

private theorem e6au_rho_symm_mu2_subset :
    ∀ γ ∈ mu2List, permLattice e6au_rhoPerm.symm γ ∈ mu1List := by
  decide +kernel

private theorem e6au_rho_mu1 : e6au_rho '' {β | β ∈ mu1List} = {β | β ∈ mu2List} := by
  ext β
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact e6au_rho_mu1_subset γ hγ
  · intro hβ
    refine ⟨permLattice e6au_rhoPerm.symm β, e6au_rho_symm_mu2_subset β hβ,
      e6au_permLattice_symm_apply _ _⟩

private theorem e6au_map_subgroupOf_conj {G : Type*} [Group G] {A H : Subgroup G} (hH : H ≤ A)
    (α : MulAut A) (g : G) (hα : ∀ a : A, ((α a : A) : G) = g * (a : G) * g⁻¹) :
    (H.subgroupOf A).map α.toMonoidHom =
      (H.map (MulAut.conj g).toMonoidHom).subgroupOf A := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ⟨(a : G), ha, by simpa [MulAut.conj_apply] using (hα a).symm⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨y, hH hy⟩, hy, ?_⟩
    apply Subtype.ext
    show ((α ⟨y, hH hy⟩ : A) : G) = (x : G)
    rw [hα]
    simpa [MulAut.conj_apply] using hyx

private noncomputable def e6au_gamma :
    MulAut EC :=
  exactNormalAut .E6 F2 1 (RingEquiv.refl F2) 1

private theorem e6au_gamma_apply
    (h : EC) :
    ((e6au_gamma h : EC) : ModGL .E6 F2) =
      exactQ .E6 F2 1 * (h : ModGL .E6 F2) * (exactQ .E6 F2 1)⁻¹ := by
  rw [e6au_gamma, coe_exactNormalAut, rootDiagUnit_one, one_mul, inv_one, mul_one,
    show Units.map (entrywiseHom (RingEquiv.refl F2).toRingHom) (h : ModGL .E6 F2) =
      (h : ModGL .E6 F2) from Units.ext (entrywise_id _)]

private theorem e6au_gamma_rootSpan
    (S : Set (Fin Tag.E6.rank → ℤ))
    (hS : ∀ α ∈ S, IsRoot .E6 α) :
    (rootSpan .E6 F2 S).map (MulAut.conj (exactQ .E6 F2 1)).toMonoidHom =
      rootSpan .E6 F2 (e6au_rho '' S) := by
  have htw : (MulAut.conj (exactQ .E6 F2 1)).toMonoidHom =
      twistHom TwistTag.E6 F2 (RingHom.id F2) := by
    rw [show exactQ .E6 F2 1 = (diagramMap TwistTag.E6 F2 : ModGL Tag.E6 F2) from by
      rw [exactQ, pow_one]]
    exact conj_diagramMap_eq_twistHom TwistTag.E6 F2
  rw [htw]
  exact map_twistHom_rootSpan (t := TwistTag.E6) (K := F2) (σ := RingHom.id F2)
    (S := S) Function.surjective_id hS

private theorem e6au_qRoots_isRoot : ∀ α ∈ qRoots, IsRoot .E6 α := fun _ hα => hα.1

private theorem e6au_zRoots_isRoot : ∀ α ∈ zRoots, IsRoot .E6 α := fun _ hα => hα.1

private theorem e6au_mu1_mem_rootFinset
    : ∀ α ∈ mu1List, α ∈ rootFinset .E6 := by
  decide +kernel

private theorem e6au_mu1_isRoot :
    ∀ α ∈ mu1List, IsRoot .E6 α :=
  fun α hα => mem_rootFinset.1 (e6au_mu1_mem_rootFinset α hα)

private theorem e6au_mu2_mem_rootFinset
    : ∀ α ∈ mu2List, α ∈ rootFinset .E6 := by
  decide +kernel

private theorem e6au_mu2_isRoot :
    ∀ α ∈ mu2List, IsRoot .E6 α :=
  fun α hα => mem_rootFinset.1 (e6au_mu2_mem_rootFinset α hα)

private theorem e6au_gamma_qE :
    qE.map e6au_gamma.toMonoidHom = qE := by
  have h := e6au_map_subgroupOf_conj (A := adjointGroup .E6 F2)
      (H := rootSpan .E6 F2 qRoots) (E6Pilot.rootSpan_le_adjointGroup_E6 qRoots) e6au_gamma
      (exactQ .E6 F2 1) (fun a => e6au_gamma_apply a)
  rw [e6au_gamma_rootSpan qRoots e6au_qRoots_isRoot, e6au_rho_qRoots] at h
  simpa only [qE] using h

private theorem e6au_gamma_z0E :
    z0E.map e6au_gamma.toMonoidHom = z0E := by
  have h := e6au_map_subgroupOf_conj (A := adjointGroup .E6 F2)
      (H := rootSpan .E6 F2 zRoots) (E6Pilot.rootSpan_le_adjointGroup_E6 zRoots) e6au_gamma
      (exactQ .E6 F2 1) (fun a => e6au_gamma_apply a)
  rw [e6au_gamma_rootSpan zRoots e6au_zRoots_isRoot, e6au_rho_zRoots] at h
  simpa only [z0E] using h

private theorem e6au_gamma_uMu1 :
    uMu1.map e6au_gamma.toMonoidHom = uMu2 := by
  have h := e6au_map_subgroupOf_conj (A := adjointGroup .E6 F2)
      (H := rootSpan .E6 F2 {β | β ∈ mu1List})
      (E6Pilot.rootSpan_le_adjointGroup_E6 _) e6au_gamma
      (exactQ .E6 F2 1) (fun a => e6au_gamma_apply a)
  rw [e6au_gamma_rootSpan {β | β ∈ mu1List} e6au_mu1_isRoot, e6au_rho_mu1] at h
  simpa only [uMu1, uMu2] using h

private noncomputable abbrev e6au_W1 :
    Subgroup EC :=
  z0E ⊔ uMu1

private noncomputable abbrev e6au_W2 :
    Subgroup EC :=
  z0E ⊔ uMu2

private theorem e6au_mu1_level :
    ∀ α ∈ mu1List, 0 < iform α lamE := by
  decide +kernel

private theorem e6au_mu2_level :
    ∀ α ∈ mu2List, 0 < iform α lamE := by
  decide +kernel

private theorem e6au_uMu1_le_qE :
    uMu1 ≤ qE := by
  intro x hx
  simp only [uMu1, qE, Subgroup.mem_subgroupOf] at hx ⊢
  exact rootSpan_mono
    (fun β hβ => (show β ∈ qRoots from ⟨e6au_mu1_isRoot β hβ, e6au_mu1_level β hβ⟩)) hx

private theorem e6au_uMu2_le_qE :
    uMu2 ≤ qE := by
  intro x hx
  simp only [uMu2, qE, Subgroup.mem_subgroupOf] at hx ⊢
  exact rootSpan_mono
    (fun β hβ => (show β ∈ qRoots from ⟨e6au_mu2_isRoot β hβ, e6au_mu2_level β hβ⟩)) hx

private theorem e6au_W1_le_qE :
    e6au_W1 ≤ qE :=
  sup_le z0E_le_qE e6au_uMu1_le_qE

private theorem e6au_W2_le_qE :
    e6au_W2 ≤ qE :=
  sup_le z0E_le_qE e6au_uMu2_le_qE

private theorem e6au_invU1_inf_invU2 : invU1 ⊓ invU2 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  funext i
  by_cases hi : (i : ℕ) < 8
  · exact (Submodule.mem_inf.mp hv).2 i hi
  · exact (Submodule.mem_inf.mp hv).1 i (by omega)

private theorem e6au_W1_inf_W2 :
    e6au_W1 ⊓ e6au_W2 = z0E := by
  obtain ⟨c, hc⟩ := exists_qcoord
  refine le_antisymm ?_ (le_inf le_sup_left le_sup_left)
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hxq : x ∈ qE := e6au_W1_le_qE hx1
  have h1 : Multiplicative.toAdd (c ⟨x, hxq⟩) ∈ invU1 :=
    (qcoord_mem_U1_iff hc ⟨x, hxq⟩).2 hx1
  have h2 : Multiplicative.toAdd (c ⟨x, hxq⟩) ∈ invU2 :=
    (qcoord_mem_U2_iff hc ⟨x, hxq⟩).2 hx2
  have hzero : Multiplicative.toAdd (c ⟨x, hxq⟩) = 0 := by
    have hmem : Multiplicative.toAdd (c ⟨x, hxq⟩) ∈ (⊥ : Submodule (ZMod 2) e6TwoRestQV) := by
      rw [← e6au_invU1_inf_invU2]
      exact Submodule.mem_inf.mpr ⟨h1, h2⟩
    simpa using hmem
  have hone : c ⟨x, hxq⟩ = 1 := by
    have h := congrArg Multiplicative.ofAdd hzero
    rwa [ofAdd_toAdd, ofAdd_zero] at h
  have hker : ⟨x, hxq⟩ ∈ c.ker := MonoidHom.mem_ker.mpr hone
  rw [hc.2.1, Subgroup.mem_subgroupOf] at hker
  exact hker

private theorem e6au_gamma_W1 :
    e6au_W1.map e6au_gamma.toMonoidHom = e6au_W2 := by
  rw [e6au_W1, e6au_W2, Subgroup.map_sup, e6au_gamma_z0E, e6au_gamma_uMu1]

private theorem e6au_commutator_qE_le_z0E :
    ⁅qE, qE⁆ ≤ z0E := by
  obtain ⟨c, hc⟩ := exists_qcoord
  have hker : ⁅(⊤ : Subgroup ↥qE), ⊤⁆ ≤ c.ker := Abelianization.commutator_subset_ker c
  rw [hc.2.1] at hker
  have hmap := Subgroup.map_mono (f := qE.subtype) hker
  rw [Subgroup.subgroupOf_map_subtype] at hmap
  have htop : (⊤ : Subgroup ↥qE).map qE.subtype = qE := by
    ext x
    simp [Subgroup.mem_map]
  have hEq : ((⁅(⊤ : Subgroup ↥qE), ⊤⁆ : Subgroup ↥qE)).map qE.subtype = ⁅qE, qE⁆ := by
    rw [Subgroup.map_commutator, htop]
  rw [hEq] at hmap
  exact hmap.trans inf_le_left

private theorem e6au_map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj g)⁻¹ x, ?_, ?_⟩
    · have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ H := by
        have heq : g * (g⁻¹ * x * g) * g⁻¹ = x := by
          calc g * (g⁻¹ * x * g) * g⁻¹
              = g * (g⁻¹ * (x * g)) * g⁻¹ := by rw [mul_assoc (g⁻¹) x g]
            _ = (x * g) * g⁻¹ := by rw [mul_inv_cancel_left]
            _ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]
        rwa [heq]
      have h3 := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr h2
      simpa [MulAut.conj_apply] using h3
    · change (MulAut.conj g) ((MulAut.conj g)⁻¹ x) = x
      exact MulEquiv.apply_symm_apply _ _

private theorem e6au_y_qE
    (y : MulAut EC) (hyR : rE.map y.toMonoidHom = rE) :
    qE.map y.toMonoidHom = qE := by
  have hNR : (Subgroup.normalizer (rE : Set EC)).map y.toMonoidHom =
      Subgroup.normalizer (rE : Set EC) := by
    rw [← GGRootNorm.normalizer_map_mulEquiv y rE, hyR]
  rw [← pCoreOf_normalizer_rE,
    ← GGRootNorm.pCoreOf_map_mulEquiv y (Subgroup.normalizer (rE : Set EC)), hNR]

private theorem e6au_zmod_two (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private def e6au_zeroE : Fin (exactE .E6) := ⟨0, by decide +kernel⟩

private def e6au_oneE : Fin (exactE .E6) := ⟨1, by decide +kernel⟩

private theorem e6au_eps_cases (ε : Fin (exactE .E6)) : ε = e6au_zeroE ∨ ε = e6au_oneE := by
  revert ε
  decide +kernel

private theorem e6au_exactQ_zero

    : exactQ .E6 F2 0 = 1 := rfl

private theorem e6au_F2_two (x : F2) : x = 0 ∨ x = 1 := by
  rcases e6au_zmod_two (GaloisField.equivZmodP (p := 2) x) with h | h
  · left
    apply (GaloisField.equivZmodP (p := 2)).injective
    rw [h, map_zero]
  · right
    apply (GaloisField.equivZmodP (p := 2)).injective
    rw [h, map_one]

private theorem e6au_F2_units_subsingleton : Subsingleton F2ˣ :=
  ⟨fun u v => Units.ext (by
    have hu : (u : F2) = 1 := by
      rcases e6au_F2_two (u : F2) with h | h
      · exact absurd h (Units.ne_zero u)
      · exact h
    have hv : (v : F2) = 1 := by
      rcases e6au_F2_two (v : F2) with h | h
      · exact absurd h (Units.ne_zero v)
      · exact h
    rw [hu, hv])⟩

private theorem e6au_z0_comm
    {z q : EC} (hz : z ∈ z0E) (hq : q ∈ qE) : z * q = q * z :=
  (Subgroup.mem_centralizer_iff.mp (z0E_central hz) q hq).symm

private theorem e6au_z0E_map_le
    (y : MulAut EC) (hyQ : qE.map y.toMonoidHom = qE) :
    z0E.map y.toMonoidHom ≤ z0E := by
  rintro _ ⟨z, hz, rfl⟩
  rw [← center_qE] at hz ⊢
  obtain ⟨zc, hzc, rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨y (zc : EC), ?_⟩, ?_, rfl⟩
  · exact le_of_eq hyQ (Subgroup.mem_map_of_mem y.toMonoidHom zc.2)
  · rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have hm : y⁻¹ (m : EC) ∈ qE :=
      le_of_eq (map_inv_toMonoidHom_of_map_eq hyQ)
        (Subgroup.mem_map_of_mem y⁻¹.toMonoidHom m.2)
    have hzc' := Subgroup.mem_center_iff.mp hzc ⟨y⁻¹ (m : EC), hm⟩
    have h := congrArg (fun t : ↥qE => (y (t : EC) : EC)) hzc'
    simpa using h

private theorem e6au_y_z0E
    (y : MulAut EC) (hyQ : qE.map y.toMonoidHom = qE) :
    z0E.map y.toMonoidHom = z0E := by
  refine le_antisymm (e6au_z0E_map_le y hyQ) ?_
  have h1 := e6au_z0E_map_le y⁻¹ (map_inv_toMonoidHom_of_map_eq hyQ)
  have h2 := Subgroup.map_mono (f := y.toMonoidHom) h1
  have hsymm : (z0E.map y⁻¹.toMonoidHom).map y.toMonoidHom = z0E := by
    rw [Subgroup.map_map]
    have hcomp : y.toMonoidHom.comp y⁻¹.toMonoidHom = MonoidHom.id EC := by
      ext x
      simp
    rw [hcomp]
    exact Subgroup.map_id z0E
  rwa [hsymm] at h2

private noncomputable def e6au_H
    (y : MulAut EC) : Subgroup EC :=
  Subgroup.closure ((z0E : Set EC) ∪ {x | ∃ u ∈ e6au_W1, x = u * y u})

private theorem e6au_z0E_le_H
    (y : MulAut EC) : z0E ≤ e6au_H y := fun _ hx =>
  Subgroup.subset_closure (Set.mem_union_left _ hx)

private theorem e6au_H_le_qE

    (y : MulAut EC) (hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2) :
    e6au_H y ≤ qE := by
  rw [e6au_H, Subgroup.closure_le]
  rintro g (hgZ0 | ⟨u, hu, rfl⟩)
  · exact z0E_le_qE hgZ0
  · exact qE.mul_mem (e6au_W1_le_qE hu)
      (e6au_W2_le_qE (by rw [← hyW1]; exact ⟨u, hu, rfl⟩))

private theorem e6au_T_mul
    (y : MulAut EC) (hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2)
    {u v : EC} (hu : u ∈ e6au_W1) (hv : v ∈ e6au_W1) :
    (u * y u) * (v * y v) * ((u * v) * y (u * v))⁻¹ ∈ z0E := by
  have huQ : u ∈ qE := e6au_W1_le_qE hu
  have hvQ : v ∈ qE := e6au_W1_le_qE hv
  have hyuQ : y u ∈ qE :=
    e6au_W2_le_qE (by rw [← hyW1]; exact ⟨u, hu, rfl⟩)
  have hcomm : ⁅y u, v⁆ ∈ z0E :=
    e6au_commutator_qE_le_z0E (Subgroup.commutator_mem_commutator hyuQ hvQ)
  have heq : (u * y u) * (v * y v) * ((u * v) * y (u * v))⁻¹ = u * ⁅y u, v⁆ * u⁻¹ := by
    rw [map_mul]
    simp only [commutatorElement_def]
    group
  rw [heq]
  have hc : u * ⁅y u, v⁆ = ⁅y u, v⁆ * u :=
    Subgroup.mem_centralizer_iff.mp (z0E_central hcomm) u huQ
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact hcomm

private theorem e6au_T_inv
    (y : MulAut EC) (hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2)
    {u : EC} (hu : u ∈ e6au_W1) :
    (u * y u)⁻¹ * (u⁻¹ * y u⁻¹)⁻¹ ∈ z0E := by
  have huQ : u ∈ qE := e6au_W1_le_qE hu
  have hyuQ : y u ∈ qE :=
    e6au_W2_le_qE (by rw [← hyW1]; exact ⟨u, hu, rfl⟩)
  have hcomm : ⁅(y u)⁻¹, u⁻¹⁆ ∈ z0E :=
    e6au_commutator_qE_le_z0E
      (Subgroup.commutator_mem_commutator (qE.inv_mem hyuQ) (qE.inv_mem huQ))
  have heq : (u * y u)⁻¹ * (u⁻¹ * y u⁻¹)⁻¹ = ⁅(y u)⁻¹, u⁻¹⁆ := by
    rw [map_inv]
    simp only [commutatorElement_def]
    group
  rw [heq]
  exact hcomm

private theorem e6au_map_conj_z0E
    {g : EC}
    (hg : g ∈ Subgroup.normalizer (qE : Set EC)) :
    z0E.map (MulAut.conj g).toMonoidHom = z0E :=
  e6au_y_z0E (MulAut.conj g) (e6au_map_conj_eq_of_mem_normalizer hg)

private theorem e6au_mul_mem_z0E
    {a b A B C : EC} (ha : a ∈ z0E) (hb : b ∈ z0E)
    (hA : A ∈ qE) (hB : B ∈ qE) (hABC : A * B * C⁻¹ ∈ z0E) :
    (a * A) * (b * B) * C⁻¹ ∈ z0E := by
  have heq : (a * A) * (b * B) * C⁻¹ = a * b * (A * B * C⁻¹) := by
    calc (a * A) * (b * B) * C⁻¹
        = a * A * b * B * C⁻¹ := by simp only [mul_assoc]
      _ = a * (A * b) * B * C⁻¹ := by simp only [mul_assoc]
      _ = a * (b * A) * B * C⁻¹ := by rw [← e6au_z0_comm hb hA]
      _ = a * b * A * B * C⁻¹ := by simp only [mul_assoc]
      _ = a * b * (A * B * C⁻¹) := by simp only [mul_assoc]
  rw [heq]
  exact z0E.mul_mem (z0E.mul_mem ha hb) hABC

private theorem e6au_inv_mem_z0E
    {a A B : EC} (ha : a ∈ z0E) (hA : A ∈ qE)
    (hAB : A⁻¹ * B⁻¹ ∈ z0E) : (a * A)⁻¹ * B⁻¹ ∈ z0E := by
  have ha' : a⁻¹ ∈ z0E := z0E.inv_mem ha
  have hAinvQ : A⁻¹ ∈ qE := qE.inv_mem hA
  have heq : (a * A)⁻¹ * B⁻¹ = a⁻¹ * (A⁻¹ * B⁻¹) := by
    rw [mul_inv_rev, ← e6au_z0_comm ha' hAinvQ]
    simp only [mul_assoc]
  rw [heq]
  exact z0E.mul_mem ha' hAB

private theorem e6au_mem_H_form
    (y : MulAut EC)
    (hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2) :
    ∀ h ∈ e6au_H y, ∃ u ∈ e6au_W1, h * (u * y u)⁻¹ ∈ z0E := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hxZ0 | ⟨u, hu, rfl⟩
    · exact ⟨1, e6au_W1.one_mem, by simpa using hxZ0⟩
    · exact ⟨u, hu, by simp⟩
  | one => exact ⟨1, e6au_W1.one_mem, by simp⟩
  | mul x z hx hz ihx ihz =>
    obtain ⟨u, hu, hxu⟩ := ihx
    obtain ⟨v, hv, hzv⟩ := ihz
    refine ⟨u * v, e6au_W1.mul_mem hu hv, ?_⟩
    have hA : u * y u ∈ qE := qE.mul_mem (e6au_W1_le_qE hu)
      (e6au_W2_le_qE (by rw [← hyW1]; exact ⟨u, hu, rfl⟩))
    have hB : v * y v ∈ qE := qE.mul_mem (e6au_W1_le_qE hv)
      (e6au_W2_le_qE (by rw [← hyW1]; exact ⟨v, hv, rfl⟩))
    have hC : (u * v) * y (u * v) ∈ qE :=
      qE.mul_mem (qE.mul_mem (e6au_W1_le_qE hu) (e6au_W1_le_qE hv))
      (e6au_W2_le_qE (by rw [← hyW1]; exact ⟨u * v, e6au_W1.mul_mem hu hv, rfl⟩))
    have hABC : (u * y u) * (v * y v) * ((u * v) * y (u * v))⁻¹ ∈ z0E :=
      e6au_T_mul y hyW1 hu hv
    have hxc : x = (x * (u * y u)⁻¹) * (u * y u) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hzc : z = (z * (v * y v)⁻¹) * (v * y v) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [hxc, hzc]
    exact e6au_mul_mem_z0E hxu hzv hA hB hABC
  | inv x hx ihx =>
    obtain ⟨u, hu, hxu⟩ := ihx
    refine ⟨u⁻¹, e6au_W1.inv_mem hu, ?_⟩
    have hA : u * y u ∈ qE := qE.mul_mem (e6au_W1_le_qE hu)
      (e6au_W2_le_qE (by rw [← hyW1]; exact ⟨u, hu, rfl⟩))
    have hAB : (u * y u)⁻¹ * (u⁻¹ * y u⁻¹)⁻¹ ∈ z0E := e6au_T_inv y hyW1 hu
    have hxc : x = (x * (u * y u)⁻¹) * (u * y u) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [hxc]
    exact e6au_inv_mem_z0E hxu hA hAB

private theorem e6au_H_map_conj_le
    (y : MulAut EC)
    (hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2)
    (hymod : ∀ n ∈ Subgroup.normalizer (rE : Set EC),
      y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (rE : Set EC)))
    {n : EC} (hn : n ∈ Subgroup.normalizer (rE : Set EC)) :
    (e6au_H y).map (MulAut.conj n).toMonoidHom ≤ e6au_H y := by
  rw [e6au_H, MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨x, hx, rfl⟩
  rcases hx with hxZ0 | ⟨u, hu, rfl⟩
  · exact e6au_z0E_le_H y (by
      have hz := e6au_map_conj_z0E (normalizer_rE_le_normalizer_qE hn)
      exact hz ▸ (⟨x, hxZ0, rfl⟩ : (MulAut.conj n) x ∈ z0E.map (MulAut.conj n).toMonoidHom))
  · have hnQ : n ∈ Subgroup.normalizer (qE : Set EC) := normalizer_rE_le_normalizer_qE hn
    set u' : EC := n * u * n⁻¹ with hu'_def
    set a : EC := n * y u * n⁻¹ with ha_def
    have hu'W1 : u' ∈ e6au_W1 := by
      change u' ∈ z0E ⊔ uMu1
      have h := e6au_map_conj_eq_of_mem_normalizer
        (normalizer_qE_le_normalizer_z0E_sup_uMu1 hnQ)
      rw [← h]
      exact ⟨u, hu, rfl⟩
    have haQ : a ∈ qE := by
      have hyuW2 : y u ∈ e6au_W2 := by
        rw [← hyW1]
        exact ⟨u, hu, rfl⟩
      have h := e6au_map_conj_eq_of_mem_normalizer
        (normalizer_qE_le_normalizer_z0E_sup_uMu2 hnQ)
      have : a ∈ e6au_W2.map (MulAut.conj n).toMonoidHom := ⟨y u, hyuW2, rfl⟩
      rw [h] at this
      exact e6au_W2_le_qE this
    have hqQ : y n * n⁻¹ ∈ qE := by
      have := hymod n hn
      rwa [pCoreOf_normalizer_rE] at this
    have hyu' : y u' = (y n * n⁻¹) * a * (y n * n⁻¹)⁻¹ := by
      rw [hu'_def, ha_def, map_mul, map_mul, map_inv]
      group
    have hdiff : a * (y u')⁻¹ ∈ z0E := by
      rw [hyu']
      have h2 : ⁅a, y n * n⁻¹⁆ ∈ z0E :=
        e6au_commutator_qE_le_z0E (Subgroup.commutator_mem_commutator haQ hqQ)
      have heq : a * ((y n * n⁻¹) * a * (y n * n⁻¹)⁻¹)⁻¹ = ⁅a, y n * n⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [heq]
      exact h2
    have hgen : u' * y u' ∈ e6au_H y :=
      Subgroup.subset_closure (Set.mem_union_right _ ⟨u', hu'W1, rfl⟩)
    have hz : u' * a * (u' * y u')⁻¹ ∈ z0E := by
      have hc : (a * (y u')⁻¹) * u' = u' * (a * (y u')⁻¹) :=
        e6au_z0_comm hdiff (e6au_W1_le_qE hu'W1)
      have heq : u' * a * (u' * y u')⁻¹ = u' * (a * (y u')⁻¹) * u'⁻¹ := by
        group
      rw [heq, ← hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hdiff
    have hta : u' * a = (u' * a * (u' * y u')⁻¹) * (u' * y u') := by
      rw [mul_assoc (u' * a), inv_mul_cancel, mul_one]
    show (MulAut.conj n) (u * y u) ∈ e6au_H y
    rw [show (MulAut.conj n) (u * y u) = u' * a from by
      rw [hu'_def, ha_def, MulAut.conj_apply]
      group]
    rw [hta]
    exact (e6au_H y).mul_mem (e6au_z0E_le_H y hz) hgen

private theorem e6au_NR_le_NH
    (y : MulAut EC)
    (hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2)
    (hymod : ∀ n ∈ Subgroup.normalizer (rE : Set EC),
      y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (rE : Set EC))) :
    Subgroup.normalizer (rE : Set EC) ≤
      Subgroup.normalizer ((e6au_H y : Subgroup EC) : Set EC) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact e6au_H_map_conj_le y hyW1 hymod hn ⟨x, hx, rfl⟩
  · intro hx
    have h := e6au_H_map_conj_le y hyW1 hymod (Subgroup.inv_mem _ hn)
    refine h ⟨n * x * n⁻¹, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem e6au_H_inf_W1
    (y : MulAut EC)
    (hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2) (hyZ0 : z0E.map y.toMonoidHom = z0E) :
    e6au_H y ⊓ e6au_W1 = z0E := by
  refine le_antisymm ?_ (le_inf (e6au_z0E_le_H y) le_sup_left)
  intro h hh
  obtain ⟨hhH, hhW1⟩ := Subgroup.mem_inf.mp hh
  obtain ⟨u, hu, hzu⟩ := e6au_mem_H_form y hyW1 h hhH
  have hzuW1 : h * (u * y u)⁻¹ ∈ e6au_W1 :=
    show h * (u * y u)⁻¹ ∈ z0E ⊔ uMu1 from Subgroup.mem_sup_left hzu
  have huW1 : u * y u ∈ e6au_W1 := by
    have heq : u * y u = (h * (u * y u)⁻¹)⁻¹ * h := by group
    rw [heq]
    exact e6au_W1.mul_mem (e6au_W1.inv_mem hzuW1) hhW1
  have hyuW1 : y u ∈ e6au_W1 := by
    have heq : y u = u⁻¹ * (u * y u) := by group
    rw [heq]
    exact e6au_W1.mul_mem (e6au_W1.inv_mem hu) huW1
  have hyuW2 : y u ∈ e6au_W2 := by
    rw [← hyW1]
    exact ⟨u, hu, rfl⟩
  have hyuZ0 : y u ∈ z0E := by
    have hmem : y u ∈ e6au_W1 ⊓ e6au_W2 := ⟨hyuW1, hyuW2⟩
    rwa [e6au_W1_inf_W2] at hmem
  have huZ0 : u ∈ z0E := by
    have hmem : u ∈ z0E.map y⁻¹.toMonoidHom := ⟨y u, hyuZ0, by simp⟩
    rwa [map_inv_toMonoidHom_of_map_eq hyZ0] at hmem
  have huyuZ0 : u * y u ∈ z0E := z0E.mul_mem huZ0 hyuZ0
  have heq : h = (h * (u * y u)⁻¹) * (u * y u) := by group
  rw [heq]
  exact z0E.mul_mem hzu huyuZ0

theorem rE_item3 :
    GGRootNormInner rE := by
  intro y hy2 hyR hymod
  obtain ⟨g, a, σ, ε, hform⟩ :=
    (ordinary_E_exact_automorphism_normal_form (τ := .E6) (Or.inl rfl) F2).2.2 y
  haveI : Subsingleton F2ˣ := e6au_F2_units_subsingleton
  have ha : a = 1 := Subsingleton.elim a 1
  have hσ : σ = RingEquiv.refl F2 := by
    refine RingEquiv.ext fun c => ?_
    rcases e6au_F2_two c with rfl | rfl <;> simp
  subst ha
  subst hσ
  have hentry : ∀ x : ModGL .E6 F2,
      Units.map (entrywiseHom (RingEquiv.refl F2).toRingHom) x = x := by
    intro x
    refine Units.ext ?_
    rw [Units.coe_map,
      show (RingEquiv.refl F2).toRingHom = RingHom.id F2 from rfl]
    exact entrywise_id _
  simp only [rootDiagUnit_one, hentry] at hform
  rcases e6au_eps_cases ε with hε0 | hε1
  · rw [hε0] at hform
    refine ⟨g, ?_⟩
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have hQ : exactQ .E6 F2 e6au_zeroE = 1 := e6au_exactQ_zero
    rw [hform h, hQ, inv_one, mul_one,
      MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    simp
  · rw [hε1] at hform
    exfalso
    have hform1 : ∀ h : EC, (y h : ModGL .E6 F2) = (g : ModGL .E6 F2) * 1 *
        exactQ .E6 F2 1 * (h : ModGL .E6 F2) * (exactQ .E6 F2 1)⁻¹ * 1⁻¹ *
        (g : ModGL .E6 F2)⁻¹ := hform
    have hy : y = MulAut.conj g * e6au_gamma := by
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hform1 h, MulAut.mul_apply, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e6au_gamma_apply]
      group
    have hyQ : qE.map y.toMonoidHom = qE := e6au_y_qE y hyR
    have hyZ0 : z0E.map y.toMonoidHom = z0E := e6au_y_z0E y hyQ
    have hgQ : qE.map (MulAut.conj g).toMonoidHom = qE := by
      have h1 : MulAut.conj g = y * e6au_gamma⁻¹ := by
        rw [hy]
        group
      rw [h1, map_toMonoidHom_mul_mulAut,
        map_inv_toMonoidHom_of_map_eq e6au_gamma_qE, hyQ]
    have hgNQ : g ∈ Subgroup.normalizer (qE : Set EC) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← hgQ]
        exact ⟨x, hx, rfl⟩
      · intro hx
        rw [← map_inv_toMonoidHom_of_map_eq hgQ]
        refine ⟨(MulAut.conj g) x, hx, ?_⟩
        show ((MulAut.conj g)⁻¹) ((MulAut.conj g) x) = x
        exact MulEquiv.symm_apply_apply _ _
    have hyW1 : e6au_W1.map y.toMonoidHom = e6au_W2 := by
      rw [hy, map_toMonoidHom_mul_mulAut, e6au_gamma_W1]
      exact e6au_map_conj_eq_of_mem_normalizer
        (normalizer_qE_le_normalizer_z0E_sup_uMu2 hgNQ)
    have hHinf : e6au_H y ⊓ e6au_W1 = z0E := e6au_H_inf_W1 y hyW1 hyZ0
    have hNH : Subgroup.normalizer (rE : Set EC) ≤
        Subgroup.normalizer ((e6au_H y : Subgroup EC) : Set EC) :=
      e6au_NR_le_NH y hyW1 hymod
    have hclass := invariant_between_z0E_qE (e6au_H y) (e6au_z0E_le_H y)
      (e6au_H_le_qE y hyW1) hNH
    obtain ⟨c, hc⟩ := exists_qcoord
    let v : EC := xr (l1Root 0)
    have hvq : v ∈ qE := xr_l1Root_mem_qE 0
    have hvW1 : v ∈ e6au_W1 :=
      show v ∈ z0E ⊔ uMu1 from Subgroup.mem_sup_right (xr_l1Root_mem_uMu1 0 (by decide))
    have hvZ0 : v ∉ z0E := by
      intro hv
      have hker : ⟨v, hvq⟩ ∈ c.ker := by
        rw [hc.2.1, Subgroup.mem_subgroupOf]
        exact hv
      rw [MonoidHom.mem_ker, hc.2.2 0] at hker
      have h := congrArg Multiplicative.toAdd hker
      rw [toAdd_ofAdd] at h
      have h0 := congrFun h 0
      simp at h0
    have hyvW2 : y v ∈ e6au_W2 := by
      rw [← hyW1]
      exact ⟨v, hvW1, rfl⟩
    have hyvq : y v ∈ qE := e6au_W2_le_qE hyvW2
    have hyvZ0 : y v ∉ z0E := by
      intro h
      exact hvZ0 (by
        have hmem : v ∈ z0E.map y⁻¹.toMonoidHom := ⟨y v, h, by simp⟩
        rwa [map_inv_toMonoidHom_of_map_eq hyZ0] at hmem)
    have hmq : v * y v ∈ qE := qE.mul_mem hvq hyvq
    have hcv : c ⟨v, hvq⟩ = Multiplicative.ofAdd (Pi.single (0 : Fin 16) 1) := hc.2.2 0
    have hcyvU2 : Multiplicative.toAdd (c ⟨y v, hyvq⟩) ∈ invU2 :=
      (qcoord_mem_U2_iff hc ⟨y v, hyvq⟩).2 hyvW2
    have hcyvne : Multiplicative.toAdd (c ⟨y v, hyvq⟩) ≠ 0 := by
      intro hw
      apply hyvZ0
      have hone : c ⟨y v, hyvq⟩ = 1 := by
        have := congrArg Multiplicative.ofAdd hw
        rwa [ofAdd_toAdd, ofAdd_zero] at this
      have hker : ⟨y v, hyvq⟩ ∈ c.ker := MonoidHom.mem_ker.mpr hone
      rw [hc.2.1, Subgroup.mem_subgroupOf] at hker
      exact hker
    have hcm : Multiplicative.toAdd (c ⟨v * y v, hmq⟩) =
        Pi.single (0 : Fin 16) 1 + Multiplicative.toAdd (c ⟨y v, hyvq⟩) := by
      have hsplit : (⟨v * y v, hmq⟩ : ↥qE) = ⟨v, hvq⟩ * ⟨y v, hyvq⟩ :=
        Subtype.ext rfl
      have h1 : c ⟨v * y v, hmq⟩ = Multiplicative.ofAdd
          (Pi.single (0 : Fin 16) 1 + Multiplicative.toAdd (c ⟨y v, hyvq⟩)) := by
        rw [hsplit, map_mul, hcv, ← ofAdd_toAdd (c ⟨y v, hyvq⟩)]
        exact ofAdd_add _ _
      rw [h1, toAdd_ofAdd]
    have hmZ0 : v * y v ∉ z0E := by
      intro hm
      have hker : ⟨v * y v, hmq⟩ ∈ c.ker := by
        rw [hc.2.1, Subgroup.mem_subgroupOf]
        exact hm
      rw [MonoidHom.mem_ker] at hker
      have h := congrArg Multiplicative.toAdd hker
      rw [hcm] at h
      have h0 : (1 : ZMod 2) = 0 := by
        have h1 := congrFun h 0
        simpa [Pi.single_apply, hcyvU2 0 (by decide : (0 : Fin 16) < 8)] using h1
      exact one_ne_zero h0
    have hmW1 : v * y v ∉ e6au_W1 := by
      intro hm
      have hmem : Multiplicative.toAdd (c ⟨v * y v, hmq⟩) ∈ invU1 :=
        (qcoord_mem_U1_iff hc ⟨v * y v, hmq⟩).2 hm
      obtain ⟨j, hj⟩ : ∃ j : Fin 16, Multiplicative.toAdd (c ⟨y v, hyvq⟩) j ≠ 0 := by
        by_contra h
        push Not at h
        exact hcyvne (funext h)
      have hj8 : 8 ≤ (j : ℕ) := by
        by_contra hlt
        exact hj (hcyvU2 j (by omega))
      have h0 : Multiplicative.toAdd (c ⟨y v, hyvq⟩) j = 0 := by
        have h1 := hmem j hj8
        rw [hcm] at h1
        simpa [Pi.single_apply, if_neg (by omega : ¬ (j = (0 : Fin 16)))] using h1
      exact hj h0
    have hmW2 : v * y v ∉ e6au_W2 := by
      intro hm
      have hmem : Multiplicative.toAdd (c ⟨v * y v, hmq⟩) ∈ invU2 :=
        (qcoord_mem_U2_iff hc ⟨v * y v, hmq⟩).2 hm
      have h0 : (1 : ZMod 2) = 0 := by
        have h1 := hmem 0 (by decide : (0 : Fin 16) < 8)
        rw [hcm] at h1
        simpa [Pi.single_apply, hcyvU2 0 (by decide : (0 : Fin 16) < 8)] using h1
      exact one_ne_zero h0
    have hmH : v * y v ∈ e6au_H y :=
      Subgroup.subset_closure (Set.mem_union_right _ ⟨v, hvW1, rfl⟩)
    rcases hclass with hH | hH | hH | hH
    · exact hmZ0 (hH ▸ hmH)
    · have hW1z : e6au_W1 ≤ z0E := by
        rw [← hHinf, hH]
        exact le_inf e6au_W1_le_qE le_rfl
      exact hvZ0 (hW1z hvW1)
    · rw [hH] at hmH
      exact hmW1 hmH
    · rw [hH] at hmH
      exact hmW2 hmH

end CFSG.StandardType.GGSixE6Two

