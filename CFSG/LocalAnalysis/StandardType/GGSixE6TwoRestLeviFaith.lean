module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestLevi
public import CFSG.LieType.Chevalley.C2E6D4Faithful
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYGroupAction
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6StandardBetaStar
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LieType.Chevalley.C2E6StandardLeviFactors

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.Steinberg.Adjoint

open scoped commutatorElement

private noncomputable def e6lf_stdLevi :
    Subgroup EC :=
  (parabolicLevi .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2)

private theorem e6lf_fin_roots1 : ∀ k : Fin 72,
    iform (C2E6Std.e6Root k) E6Pilot.yLamAS = 2 →
      ∃ j : Fin 8, C2E6Std.rootD j = C2E6Std.e6Root k := by
  decide +kernel

private theorem e6lf_fin_roots2 : ∀ j : Fin 8,
    iform (C2E6Std.rootD j) E6Pilot.yLamAS = 2 := by
  decide

private theorem e6lf_stdZRoots_eq_range_rootD :
    stdZRoots = Set.range C2E6Std.rootD := by
  ext γ
  constructor
  · intro hγ
    obtain ⟨k, rfl⟩ := C2E6Std.exists_e6Root_eq hγ.1
    obtain ⟨j, hj⟩ := e6lf_fin_roots1 k hγ.2
    exact ⟨j, hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨C2E6Std.isRoot_rootD j, e6lf_fin_roots2 j⟩

private noncomputable def e6lf_f2EquivZMod : ZMod 2 ≃+* F2 :=
  RingEquiv.ofBijective (algebraMap (ZMod 2) F2 : ZMod 2 →+* F2) (by
    haveI : Fintype F2 := Fintype.ofFinite F2
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨RingHom.injective (algebraMap (ZMod 2) F2), ?_⟩
    have h1 : Fintype.card F2 = 2 := by
      rw [← Nat.card_eq_fintype_card, show F2 = GaloisField 2 1 from rfl,
        GaloisField.card 2 1 (by norm_num), pow_one]
    have h2 : Fintype.card (ZMod 2) = 2 := ZMod.card 2
    rw [h1, h2])

private theorem e6lf_faithful_of_fixes_M
    {g : ModGL Tag.E6 F2}
    (hg : g ∈ subsystemGroup Tag.E6 F2 C2E6Std.setD)
    (hfix : ∀ j : Fin 8,
      (g : Module.End F2 (RootModule Tag.E6 F2)) (rootVec Tag.E6 F2 (C2E6Std.rootD j)) =
        rootVec Tag.E6 F2 (C2E6Std.rootD j)) : g = 1 := by
  let f : F2 →+* C2E6Overlap.K :=
    (algebraMap (ZMod 2) C2E6Overlap.K).comp e6lf_f2EquivZMod.symm.toRingHom
  let h : ModGL Tag.E6 C2E6Overlap.K := baseChangeGL f g
  have hh : h ∈ C2E6Std.groupD := by
    have hle : (subsystemGroup Tag.E6 F2 C2E6Std.setD).map (baseChangeGL f) ≤
        subsystemGroup Tag.E6 C2E6Overlap.K C2E6Std.setD := by
      change (Subgroup.closure {x | ∃ i ∈ C2E6Std.setD, ∃ c : F2,
          x = xUnit Tag.E6 F2 i c ∨ x = yUnit Tag.E6 F2 i c}).map (baseChangeGL f) ≤
        Subgroup.closure {x | ∃ i ∈ C2E6Std.setD, ∃ c : C2E6Overlap.K,
          x = xUnit Tag.E6 C2E6Overlap.K i c ∨ x = yUnit Tag.E6 C2E6Overlap.K i c}
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, ⟨i, hi, c, rfl | rfl⟩, rfl⟩
      · rw [baseChangeGL_xUnit (τ := Tag.E6) f i c]
        exact Subgroup.subset_closure ⟨i, hi, f c, Or.inl rfl⟩
      · rw [baseChangeGL_yUnit (τ := Tag.E6) f i c]
        exact Subgroup.subset_closure ⟨i, hi, f c, Or.inr rfl⟩
    exact hle ⟨g, hg, rfl⟩
  have hpsi : C2E6Std.psiD ⟨h, hh⟩ = 1 := by
    rw [C2E6Std.psiD_eq_one_iff]
    intro v hv
    have hfixD : ∀ j : Fin 8,
        (h : Module.End C2E6Overlap.K (RootModule Tag.E6 C2E6Overlap.K)) (C2E6Std.vecD j) =
          C2E6Std.vecD j := by
      intro j
      rw [C2E6Std.vecD, C2E6Std.rootVec_eq_single (C2E6Std.isRoot_rootD j),
        baseChangeGL_apply_single f g (Sum.inr ⟨C2E6Std.rootD j, C2E6Std.isRoot_rootD j⟩)]
      rw [show (Finsupp.single (Sum.inr ⟨C2E6Std.rootD j, C2E6Std.isRoot_rootD j⟩) (1 : F2) :
            RootModule Tag.E6 F2) = rootVec Tag.E6 F2 (C2E6Std.rootD j) from
          (C2E6Std.rootVec_eq_single (C2E6Std.isRoot_rootD j)).symm]
      rw [hfix j]
      rw [C2E6Std.rootVec_eq_single (C2E6Std.isRoot_rootD j)]
      rw [Finsupp.mapRange_single]
      simp
    have hspan : ∀ x ∈ C2E6Std.moduleD,
        (h : Module.End C2E6Overlap.K (RootModule Tag.E6 C2E6Overlap.K)) x = x := by
      intro x hx
      rw [C2E6Std.moduleD_eq_span] at hx
      refine Submodule.span_induction (p := fun x _ =>
        (h : Module.End C2E6Overlap.K (RootModule Tag.E6 C2E6Overlap.K)) x = x)
        ?_ ?_ ?_ ?_ hx
      · rintro y ⟨j, rfl⟩
        exact hfixD j
      · simp
      · intro y z hy hz ihy ihz
        rw [map_add, ihy, ihz]
      · intro c y hy ihy
        rw [map_smul, ihy]
    exact hspan v hv
  have h1 : (⟨h, hh⟩ : C2E6Std.groupD) = 1 :=
    C2E6Std.psiD_injective (by rw [hpsi, map_one])
  have h3 : baseChangeGL f g = 1 := Subtype.ext_iff.mp h1
  exact baseChangeGL_injective f (by rw [h3, map_one])

private theorem e6lf_fixes_single
    {g : ModGL Tag.E6 F2}
    (hg : g ∈ subsystemGroup Tag.E6 F2 C2E6Std.setD)
    (hcen : ∀ j : Fin 8, g * pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1 * g⁻¹ =
      pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1) (j : Fin 8) :
    (g : Module.End F2 (RootModule Tag.E6 F2)) (rootVec Tag.E6 F2 (C2E6Std.rootD j)) =
      rootVec Tag.E6 F2 (C2E6Std.rootD j) := by
  have h1 := d4Psi_conj_rootD_product (F := F2) ⟨g, hg⟩
    (Pi.single (C2E6Std.natD j) (1 : F2))
  rw [d4RootWord_single j 1] at h1
  rw [hcen j] at h1
  have hpsi : d4Psi F2 ⟨g, hg⟩ (Pi.single (C2E6Std.natD j) (1 : F2)) =
      Pi.single (C2E6Std.natD j) (1 : F2) :=
    d4RootWord_injective (h1.symm.trans (d4RootWord_single j 1).symm)
  have hphi := d4Psi_phi (K := F2) ⟨g, hg⟩ (d4Vec_mem (K := F2) j)
  rw [d4Phi_vec] at hphi
  rw [hpsi] at hphi
  have hEq : (⟨((g : ModGL Tag.E6 F2) : Module.End F2 (RootModule Tag.E6 F2))
        (d4Vec F2 j), mem_d4Module_of_mem_subsystemGroup hg (d4Vec F2 j) (d4Vec_mem j)⟩ : d4Module F2) =
      ⟨d4Vec F2 j, d4Vec_mem j⟩ :=
    (d4Phi F2).injective (hphi.symm.trans (d4Phi_vec j).symm)
  exact congrArg Subtype.val hEq

private theorem e6lf_torusGroup_F2 :
    torusGroup Tag.E6 F2 = ⊥ := by
  haveI : Fintype F2 := Fintype.ofFinite F2
  rw [torusGroup, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨⟨i, t⟩, rfl⟩
  have hcard : Nat.card F2 = 2 := by
    rw [show F2 = GaloisField 2 1 from rfl, GaloisField.card 2 1 (by norm_num), pow_one]
  have ht : t = 1 := Units.ext (by
    have h := FiniteField.pow_card_sub_one_eq_one (t : F2) t.ne_zero
    rwa [← Nat.card_eq_fintype_card, hcard, show 2 - 1 = 1 from rfl, pow_one] at h)
  subst ht
  show torusElt Tag.E6 F2 i 1 ∈ ({1} : Set (ModGL Tag.E6 F2))
  rw [torusElt_one]
  exact Set.mem_singleton 1

private theorem e6lf_nodes16_subset_setD : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 →
    j ∈ ({1, 2, 3, 4} : Set (Fin 6)) := by
  decide +kernel

private theorem e6lf_parabolicLevi_le_subsystem :
    parabolicLevi Tag.E6 F2 E6Pilot.nodes16 ≤ subsystemGroup Tag.E6 F2 C2E6Std.setD := by
  change torusGroup Tag.E6 F2 ⊔ Subgroup.closure {g | ∃ j ∈ E6Pilot.nodes16, ∃ c : F2,
      g = xUnit Tag.E6 F2 j c ∨ g = yUnit Tag.E6 F2 j c} ≤
    subsystemGroup Tag.E6 F2 C2E6Std.setD
  refine sup_le ?_ ?_
  · rw [e6lf_torusGroup_F2]; exact bot_le
  · rw [Subgroup.closure_le]
    rintro g ⟨j, hj, c, rfl | rfl⟩
    · exact xUnit_mem_subsystemGroup (e6lf_nodes16_subset_setD j hj.1 hj.2) c
    · exact yUnit_mem_subsystemGroup (e6lf_nodes16_subset_setD j hj.1 hj.2) c

private theorem e6lf_stdLevi_inf_centralizer_z0Std :
    e6lf_stdLevi ⊓ Subgroup.centralizer (z0Std : Set EC) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgle, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_bot]
  have hgs : (g : ModGL Tag.E6 F2) ∈ subsystemGroup Tag.E6 F2 C2E6Std.setD := by
    exact e6lf_parabolicLevi_le_subsystem (Subgroup.mem_subgroupOf.1 hgle)
  have hcen : ∀ j : Fin 8, (g : ModGL Tag.E6 F2) * pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1 *
      (g : ModGL Tag.E6 F2)⁻¹ = pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1 := by
    intro j
    have hmem : pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1 ∈ rootSpan Tag.E6 F2 stdZRoots := by
      rw [e6lf_stdZRoots_eq_range_rootD]
      exact pinnedX_mem_rootSpan (S := Set.range C2E6Std.rootD) ⟨j, rfl⟩ 1
    let y : z0Std := ⟨⟨pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1,
        pinnedX_mem_adjointGroup _ _⟩, Subgroup.mem_subgroupOf.2 hmem⟩
    have hcomm := (Subgroup.mem_centralizer_iff.1 hgc) y y.2
    have hval : pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1 * (g : ModGL Tag.E6 F2) =
        (g : ModGL Tag.E6 F2) * pinnedX Tag.E6 F2 (C2E6Std.rootD j) 1 := by
      have := congrArg Subtype.val hcomm
      simpa [y] using this
    rw [← hval]
    group
  have hfix : ∀ j : Fin 8,
      ((g : ModGL Tag.E6 F2) : Module.End F2 (RootModule Tag.E6 F2))
          (rootVec Tag.E6 F2 (C2E6Std.rootD j)) = rootVec Tag.E6 F2 (C2E6Std.rootD j) :=
    fun j => e6lf_fixes_single hgs hcen j
  have hg1 : (g : ModGL Tag.E6 F2) = 1 := e6lf_faithful_of_fixes_M hgs hfix
  exact Subtype.ext hg1

private theorem e6lf_centralizer_conj
    (H : Subgroup EC) :
    Subgroup.centralizer (H.map (MulAut.conj nQ).toMonoidHom : Set EC) =
      (Subgroup.centralizer (H : Set EC)).map (MulAut.conj nQ).toMonoidHom := by
  apply le_antisymm
  · intro y hy
    refine Subgroup.mem_map.2 ⟨(MulAut.conj nQ).symm y, ?_,
      (MulAut.conj nQ).apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have h1 := hy ((MulAut.conj nQ) x) (Subgroup.mem_map_of_mem _ hx)
    exact (MulAut.conj nQ).injective (by
      rw [map_mul, MulEquiv.apply_symm_apply, map_mul, MulEquiv.apply_symm_apply]
      exact h1)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← map_mul, ← map_mul, hx a ha]

theorem lamLevi_inf_centralizer_z0E :
    lamLevi ⊓ Subgroup.centralizer (z0E : Set EC) = ⊥ := by
  have hstd := e6lf_stdLevi_inf_centralizer_z0Std
  have hmain : e6lf_stdLevi.map (MulAut.conj nQ).toMonoidHom ⊓
      Subgroup.centralizer (z0Std.map (MulAut.conj nQ).toMonoidHom : Set EC) = ⊥ := by
    rw [e6lf_centralizer_conj, ← Subgroup.map_inf _ _ _ (MulAut.conj nQ).injective, hstd,
      Subgroup.map_bot]
  rw [show lamLevi = e6lf_stdLevi.map (MulAut.conj nQ).toMonoidHom from rfl,
    z0E_eq_map_z0Std]
  exact hmain

end CFSG.StandardType.GGSixE6Two
