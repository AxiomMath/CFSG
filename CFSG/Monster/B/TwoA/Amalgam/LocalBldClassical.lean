module

public import CFSG.Monster.B.TwoA.Amalgam.LocalBldPlane4
public import CFSG.Monster.B.TwoA.Amalgam.LocalBldPlane2

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.Monster.B.TwoA.Amalgam

open Module CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Classical.ThreePlane CFSG.Monster.B.Geometry CFSG.LieType.Chevalley

open scoped IsMulCommutative

attribute [local instance] subspaceAction

@[expose] def lineSub (S : planeLines) : Submodule F4 (Fin 3 → F4) :=
  LinearMap.ker (Classical.choose S.2)

theorem submodule_eq_span_rep (x : PlanePoint) : x.submodule = F4 ∙ x.rep := by
  conv_lhs => rw [← x.mk_rep]
  exact Projectivization.submodule_mk _ _

theorem mem_iff_le_lineSub (S : planeLines) (x : PlanePoint) :
    x ∈ (S : Set PlanePoint) ↔ x.submodule ≤ lineSub S := by
  obtain ⟨-, hS⟩ := Classical.choose_spec S.2
  rw [lineSub, submodule_eq_span_rep, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
  conv_lhs => rw [hS]
  rfl

theorem finrank_lineSub (S : planeLines) : finrank F4 (lineSub S) = 2 := by
  have h := (Classical.choose S.2).finrank_ker_add_one_of_ne_zero (Classical.choose_spec S.2).1
  rw [Module.finrank_fin_fun] at h
  rw [lineSub]
  omega

theorem lineSub_injective : Function.Injective lineSub := by
  intro S S' h
  apply Subtype.ext
  ext x
  rw [mem_iff_le_lineSub, mem_iff_le_lineSub, h]

theorem exists_form_ker_eq {L : Submodule F4 (Fin 3 → F4)} (hL : finrank F4 L = 2) :
    ∃ f : Module.Dual F4 (Fin 3 → F4), f ≠ 0 ∧ LinearMap.ker f = L := by
  have hlt : L < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have h3 := congrArg (fun U : Submodule F4 (Fin 3 → F4) => finrank F4 U) h
    simp only [finrank_top, Module.finrank_fin_fun, hL] at h3
    omega
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  refine ⟨f, hf, ?_⟩
  have hle : L ≤ LinearMap.ker f := by
    intro v hv
    rw [LinearMap.mem_ker]
    have : f v ∈ L.map f := ⟨v, hv, rfl⟩
    rw [hmap] at this
    exact this
  have h2 := f.finrank_ker_add_one_of_ne_zero hf
  rw [Module.finrank_fin_fun] at h2
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem exists_lineSub_eq {L : Submodule F4 (Fin 3 → F4)} (hL : finrank F4 L = 2) :
    ∃ S : planeLines, lineSub S = L := by
  obtain ⟨f, hf, hker⟩ := exists_form_ker_eq hL
  let S : planeLines := ⟨{x | f x.rep = 0}, f, hf, rfl⟩
  refine ⟨S, ?_⟩
  ext v
  by_cases hv : v = 0
  · rw [hv]
    exact ⟨fun _ => L.zero_mem, fun _ => (lineSub S).zero_mem⟩
  · have h := mem_iff_le_lineSub S (Projectivization.mk F4 v hv)
    rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem] at h
    rw [← h, ← hker, LinearMap.mem_ker]
    change f (Projectivization.mk F4 v hv).rep = 0 ↔ f v = 0
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep F4 v hv
    rw [← hc, Units.smul_def, map_smul, smul_eq_mul, mul_eq_zero, or_iff_right c.ne_zero]

@[expose] def toPlaneFlag4 (u : IncFlag plane4Inc) : PlaneFlag F4 :=
  ⟨u.1.1.submodule, lineSub u.1.2, u.1.1.finrank_submodule, finrank_lineSub _,
    (mem_iff_le_lineSub _ _).mp u.2⟩

@[expose] def ofPlaneFlag4 (F : PlaneFlag F4) : IncFlag plane4Inc :=
  ⟨(Projectivization.mk'' F.pt F.finrank_pt, (exists_lineSub_eq F.finrank_line).choose), by
    change Projectivization.mk'' F.pt F.finrank_pt ∈
      ((exists_lineSub_eq F.finrank_line).choose : Set PlanePoint)
    rw [mem_iff_le_lineSub, Projectivization.submodule_mk'',
      (exists_lineSub_eq F.finrank_line).choose_spec]
    exact F.pt_le_line⟩

@[expose] def plane4FlagEquiv : IncFlag plane4Inc ≃ PlaneFlag F4 where
  toFun := toPlaneFlag4
  invFun := ofPlaneFlag4
  left_inv u := by
    obtain ⟨⟨x, S⟩, hx⟩ := u
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Projectivization.mk''_submodule x
    · exact lineSub_injective (exists_lineSub_eq (finrank_lineSub S)).choose_spec
  right_inv F := PlaneFlag.ext (Projectivization.submodule_mk'' _ _)
    (exists_lineSub_eq F.finrank_line).choose_spec

theorem plane4FlagEquiv_pt (u v : IncFlag plane4Inc) :
    (plane4FlagEquiv u).pt = (plane4FlagEquiv v).pt ↔ u.1.1 = v.1.1 :=
  Projectivization.submodule_injective.eq_iff

theorem plane4FlagEquiv_line (u v : IncFlag plane4Inc) :
    (plane4FlagEquiv u).line = (plane4FlagEquiv v).line ↔ u.1.2 = v.1.2 :=
  lineSub_injective.eq_iff

@[expose] def toPlaneFlag2
    (u : IncFlag plane2Inc) : PlaneFlag (ZMod 2) :=
  ⟨u.1.1.1.map (Par3.bE : Additive E3 →ₗ[ZMod 2] (Fin 3 → ZMod 2)),
    u.1.2.1.map (Par3.bE : Additive E3 →ₗ[ZMod 2] (Fin 3 → ZMod 2)),
    by rw [LinearEquiv.finrank_map_eq]; exact u.1.1.2,
    by rw [LinearEquiv.finrank_map_eq]; exact u.1.2.2, Submodule.map_mono u.2⟩

@[expose] def ofPlaneFlag2
    (F : PlaneFlag (ZMod 2)) : IncFlag plane2Inc :=
  ⟨(⟨F.pt.map (Par3.bE.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Additive E3), by
      rw [LinearEquiv.finrank_map_eq]; exact F.finrank_pt⟩,
    ⟨F.line.map (Par3.bE.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Additive E3), by
      rw [LinearEquiv.finrank_map_eq]; exact F.finrank_line⟩), Submodule.map_mono F.pt_le_line⟩

theorem map_bE_symm
    {U : Submodule (ZMod 2) (Additive E3)} :
    (U.map (Par3.bE : Additive E3 →ₗ[ZMod 2] (Fin 3 → ZMod 2))).map
      (Par3.bE.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Additive E3) = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [LinearEquiv.symm_apply_apply]
  · intro hv
    exact ⟨Par3.bE v, ⟨v, hv, rfl⟩, LinearEquiv.symm_apply_apply _ _⟩

theorem map_bE_symm'
    {U : Submodule (ZMod 2) (Fin 3 → ZMod 2)} :
    (U.map (Par3.bE.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Additive E3)).map
      (Par3.bE : Additive E3 →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = U := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [LinearEquiv.apply_symm_apply]
  · intro hv
    exact ⟨Par3.bE.symm v, ⟨v, hv, rfl⟩, LinearEquiv.apply_symm_apply _ _⟩

@[expose] def plane2FlagEquiv :
    IncFlag plane2Inc ≃ PlaneFlag (ZMod 2) where
  toFun := toPlaneFlag2
  invFun := ofPlaneFlag2
  left_inv _ := Subtype.ext (Prod.ext (Subtype.ext map_bE_symm) (Subtype.ext map_bE_symm))
  right_inv _ := PlaneFlag.ext map_bE_symm' map_bE_symm'

theorem map_bE_inj
    {U U' : Submodule (ZMod 2) (Additive E3)} :
    U.map (Par3.bE : Additive E3 →ₗ[ZMod 2] (Fin 3 → ZMod 2)) =
        U'.map (Par3.bE : Additive E3 →ₗ[ZMod 2] (Fin 3 → ZMod 2)) ↔ U = U' :=
  (Submodule.map_injective_of_injective Par3.bE.injective).eq_iff

theorem plane2FlagEquiv_pt
    (u v : IncFlag plane2Inc) :
    (plane2FlagEquiv u).pt = (plane2FlagEquiv v).pt ↔ u.1.1 = v.1.1 :=
  map_bE_inj.trans Subtype.ext_iff.symm

theorem plane2FlagEquiv_line
    (u v : IncFlag plane2Inc) :
    (plane2FlagEquiv u).line = (plane2FlagEquiv v).line ↔ u.1.2 = v.1.2 :=
  map_bE_inj.trans Subtype.ext_iff.symm

@[expose] def fiveEquiv :
    Five ≃ Fin 5 :=
  (Finite.equivFin Five).trans (finCongr natCard_orbit_subgeom)

theorem incProduct_adj_iff_planeProduct {Pt Ln : Type*} {inc : Pt → Ln → Prop} {Z Z' : Type*}
    {k : Type*} [Field k] {a b z : Fin 4} (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (E : IncFlag inc ≃ PlaneFlag k) (eZ : Z ≃ Z')
    (hpt : ∀ u v, (E u).pt = (E v).pt ↔ u.1.1 = v.1.1)
    (hline : ∀ u v, (E u).line = (E v).line ↔ u.1.2 = v.1.2) (j : Fin 4) (p q : IncFlag inc × Z) :
    (planeProduct k Z' a b z).adj j (E.prodCongr eZ p) (E.prodCongr eZ q) ↔
      (incProduct inc Z a b z).adj j p q := by
  by_cases hja : j = a
  · subst hja
    rw [planeProduct_adj_a, incProduct_adj_a]
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hline, eZ.injective.eq_iff]
  by_cases hjb : j = b
  · subst hjb
    rw [planeProduct_adj_b hab, incProduct_adj_b hab]
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hpt, eZ.injective.eq_iff]
  by_cases hjz : j = z
  · subst hjz
    rw [planeProduct_adj_z haz hbz, incProduct_adj_z haz hbz]
    simp only [Equiv.prodCongr_apply, Prod.map_fst, E.injective.eq_iff]
  · have h1 : (planeProduct k Z' a b z).adj j = Eq := by
      simp [planeProduct, ChamberSystem.ofThree, hja, hjb, hjz]
    have h2 : (incProduct inc Z a b z).adj j = Eq := by
      simp [incProduct, ChamberSystem.ofThree, hja, hjb, hjz]
    rw [h1, h2]
    exact (E.prodCongr eZ).injective.eq_iff

theorem residue_iso_planeProduct
    {Pt Ln : Type*} {inc : Pt → Ln → Prop} {Z Z' : Type*}
    {k : Type*} [Field k] {a b z i : Fin 4} (hab : a ≠ b) (haz : a ≠ z) (hbz : b ≠ z)
    (E : IncFlag inc ≃ PlaneFlag k) (eZ : Z ≃ Z')
    (hpt : ∀ u v, (E u).pt = (E v).pt ↔ u.1.1 = v.1.1)
    (hline : ∀ u v, (E u).line = (E v).line ↔ u.1.2 = v.1.2) {x : Chamber}
    {ψ : IncFlag inc × Z → Chamber}
    (hψ : Set.BijOn ψ Set.univ (cosetCS.residue {j | j ≠ i} x))
    (hadj : ∀ p q, ∀ j ∈ {j : Fin 4 | j ≠ i}, (cosetCS.adj j (ψ p) (ψ q) ↔
      (incProduct inc Z a b z).adj j p q)) :
    ∃ ψ' : PlaneFlag k × Z' → Chamber,
      Set.BijOn ψ' Set.univ (cosetCS.residue {j | j ≠ i} x) ∧
      ∀ p q (j : Fin 4), j ≠ i →
        (cosetCS.adj j (ψ' p) (ψ' q) ↔ (planeProduct k Z' a b z).adj j p q) := by
  refine ⟨ψ ∘ (E.prodCongr eZ).symm, hψ.comp (Set.bijOn_univ.mpr (E.prodCongr eZ).symm.bijective),
    fun p q j hj => ?_⟩
  rw [Function.comp_apply, Function.comp_apply, hadj _ _ j hj,
    ← incProduct_adj_iff_planeProduct hab haz hbz E eZ hpt hline, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

theorem plane4_residue_classical
    (x : Chamber) :
    ∃ ψ : PlaneFlag C2E6Overlap.K × Fin 3 → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (1 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 1 →
        (chamberCS.adj j (ψ a) (ψ b) ↔
          (planeProduct C2E6Overlap.K (Fin 3) (2 : Fin 4) 3 0).adj j a b) := by
  obtain ⟨ψ, hψ, hadj⟩ := exists_residue_iso plane4_residue.1
    (fun a b j hj => plane4_residue.2.2.1 a b j hj) x
  exact residue_iso_planeProduct (by decide) (by decide) (by decide) plane4FlagEquiv vsharpEquiv
    plane4FlagEquiv_pt plane4FlagEquiv_line hψ hadj

theorem plane2_residue_classical
    (x : Chamber) :
    ∃ ψ : PlaneFlag (ZMod 2) × Fin 5 → Chamber,
      Set.BijOn ψ Set.univ (chamberCS.residue {j | j ≠ (2 : Fin 4)} x) ∧
      ∀ a b (j : Fin 4), j ≠ 2 →
        (chamberCS.adj j (ψ a) (ψ b) ↔
          (planeProduct (ZMod 2) (Fin 5) (0 : Fin 4) 1 3).adj j a b) := by
  obtain ⟨ψ, hψ, hadj⟩ := exists_residue_iso plane2_residue.1
    (fun a b j hj => plane2_residue.2.2.1 a b j hj) x
  exact residue_iso_planeProduct (by decide) (by decide) (by decide) plane2FlagEquiv fiveEquiv
    plane2FlagEquiv_pt plane2FlagEquiv_line hψ hadj

end CFSG.Monster.B.TwoA.Amalgam
