module

public import CFSG.Monster.B.TwoA.Amalgam.Flag3Quot
public import CFSG.Monster.B.TwoA.Amalgam.Flag3Lin

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 MulAction

open scoped IsMulCommutative

attribute [local instance] k3SetAction subspaceAction parAction

theorem exists_phiP3_eq
    (A : Additive E3 ≃ₗ[ZMod 2] Additive E3) (π : Equiv.Perm Five) :
    ∃ g : Pc 2, (phiP3 g).1 = A ∧ (phiP3 g).2 = π := by
  obtain ⟨g, hg⟩ := phiP3_surjective (A, π)
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

instance finiteDimensional_additive_E3 :
    FiniteDimensional (ZMod 2) (Additive E3) :=
  Module.Finite.of_finite

theorem finrank_additive_E3 :
    Module.finrank (ZMod 2) (Additive E3) = 3 :=
  finrank_additive_of_card natCard_E3_pow

theorem exists_smul_eq_sub
    {j : ℕ} (S T : SubspaceDim (ZMod 2) (Additive E3) j) :
    ∃ g : Pc 2, (phiP3 g).1 • S = T := by
  obtain ⟨A, hA⟩ := exists_linearEquiv_map_eq (S.2.trans T.2.symm)
  obtain ⟨g, hg, -⟩ := exists_phiP3_eq A 1
  exact ⟨g, (congrArg (· • S) hg).trans (Subtype.ext ((subspace_smul_coe A S).trans hA))⟩

theorem exists_smul_eq_five
    (C' C'' : Five) : ∃ g : Pc 2, (phiP3 g).2 C' = C'' := by
  obtain ⟨g, -, hg⟩ := exists_phiP3_eq 1 (Equiv.swap C' C'')
  exact ⟨g, (congrArg (fun τ : Equiv.Perm Five => τ C') hg).trans (Equiv.swap_apply_left C' C'')⟩

theorem exists_gl_flag
    (p p' : SubspaceDim (ZMod 2) (Additive E3) 1)
    (l l' : SubspaceDim (ZMod 2) (Additive E3) 2) (hpl : p.1 ≤ l.1) (hpl' : p'.1 ≤ l'.1) :
    ∃ A : Additive E3 ≃ₗ[ZMod 2] Additive E3, A • p = p' ∧ A • l = l' := by
  have h1 : Module.finrank (ZMod 2) p.1 = Module.finrank (ZMod 2) p'.1 := p.2.trans p'.2.symm
  have h2 : Module.finrank (ZMod 2) l.1 = Module.finrank (ZMod 2) l'.1 := l.2.trans l'.2.symm
  have hex := exists_linearEquiv_map_eq_map_eq hpl hpl' h1 h2
  obtain ⟨A, hA⟩ := hex
  exact ⟨A, Subtype.ext ((subspace_smul_coe A p).trans hA.1),
    Subtype.ext ((subspace_smul_coe A l).trans hA.2)⟩

theorem p3_flag_transitive
    (p p' : SubspaceDim (ZMod 2) (Additive E3) 1)
    (l l' : SubspaceDim (ZMod 2) (Additive E3) 2) (C' C'' : Five) (hpl : p.1 ≤ l.1)
    (hpl' : p'.1 ≤ l'.1) :
    ∃ g : Pc 2, (phiP3 g).1 • p = p' ∧ (phiP3 g).1 • l = l' ∧ (phiP3 g).2 C' = C'' :=
  (exists_gl_flag p p' l l' hpl hpl').elim fun A hA =>
    (exists_phiP3_eq A (Equiv.swap C' C'')).elim fun g hg =>
      ⟨g, (congrArg (· • p) hg.1).trans hA.1, (congrArg (· • l) hg.1).trans hA.2,
        (congrArg (fun τ : Equiv.Perm Five => τ C') hg.2).trans (Equiv.swap_apply_left C' C'')⟩

theorem mk_eq_mk_iff_pt
    (x g : Pc 2) :
    (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g ↔ (phiP3 x).1 • ptE1 = (phiP3 g).1 • ptE1 :=
  mk_eq_mk_iff_of_hom ((MonoidHom.fst _ _).comp phiP3) ptE1 (fun g => mem_Pc0_iff g) x g

theorem mk_eq_mk_iff_ln
    (x g : Pc 2) :
    (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g ↔ (phiP3 x).1 • lnE2 = (phiP3 g).1 • lnE2 :=
  mk_eq_mk_iff_of_hom ((MonoidHom.fst _ _).comp phiP3) lnE2 (fun g => mem_Pc1_iff g) x g

theorem mk_eq_mk_iff_five
    (x g : Pc 2) :
    (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = g ↔ (phiP3 x).2 fiveC = (phiP3 g).2 fiveC :=
  mk_eq_mk_iff_of_hom ((MonoidHom.snd _ _).comp phiP3) fiveC (fun g => mem_Pc3_iff g) x g

theorem exists_pt_equiv :
    ∃ f : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2) ≃ SubspaceDim (ZMod 2) (Additive E3) 1,
      (∀ g : Pc 2, f g = (phiP3 g).1 • ptE1) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).1 • f a :=
  exists_quotient_equiv_of_hom ((MonoidHom.fst _ _).comp phiP3) ptE1
    (fun x => exists_smul_eq_sub ptE1 x) (fun g => mem_Pc0_iff g)

theorem exists_ln_equiv :
    ∃ f : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2) ≃ SubspaceDim (ZMod 2) (Additive E3) 2,
      (∀ g : Pc 2, f g = (phiP3 g).1 • lnE2) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).1 • f a :=
  exists_quotient_equiv_of_hom ((MonoidHom.fst _ _).comp phiP3) lnE2
    (fun x => exists_smul_eq_sub lnE2 x) (fun g => mem_Pc1_iff g)

theorem exists_five_equiv :
    ∃ f : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2) ≃ Five,
      (∀ g : Pc 2, f g = (phiP3 g).2 fiveC) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).2 (f a) :=
  exists_quotient_equiv_of_hom ((MonoidHom.snd _ _).comp phiP3) fiveC
    (fun x => exists_smul_eq_five fiveC x) (fun g => mem_Pc3_iff g)

theorem pt_ln_incident_iff
    (g h : Pc 2) :
    (∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g ∧
      (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = h) ↔
      ((phiP3 g).1 • ptE1).1 ≤ ((phiP3 h).1 • lnE2).1 := by
  constructor
  · rintro ⟨x, hx0, hx1⟩
    have hle : ((phiP3 x).1 • ptE1).1 ≤ ((phiP3 x).1 • lnE2).1 :=
      (subspace_smul_coe (phiP3 x).1 ptE1).trans_le
        ((Submodule.map_mono ptE1_le_lnE2).trans_eq (subspace_smul_coe (phiP3 x).1 lnE2).symm)
    calc ((phiP3 g).1 • ptE1).1 = ((phiP3 x).1 • ptE1).1 :=
          (congrArg Subtype.val ((mk_eq_mk_iff_pt x g).1 hx0)).symm
      _ ≤ ((phiP3 x).1 • lnE2).1 := hle
      _ = ((phiP3 h).1 • lnE2).1 := congrArg Subtype.val ((mk_eq_mk_iff_ln x h).1 hx1)
  · intro hle
    obtain ⟨g', hg1, hg2, -⟩ := p3_flag_transitive ptE1 ((phiP3 g).1 • ptE1) lnE2
      ((phiP3 h).1 • lnE2) fiveC fiveC ptE1_le_lnE2 hle
    exact ⟨g', (mk_eq_mk_iff_pt g' g).2 hg1, (mk_eq_mk_iff_ln g' h).2 hg2⟩

theorem pt_five_incident
    (g h : Pc 2) :
    ∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g ∧
      (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = h := by
  obtain ⟨x, hx1, hx2⟩ := exists_phiP3_eq (phiP3 g).1 (phiP3 h).2
  exact ⟨x, (mk_eq_mk_iff_pt x g).2 (congrArg (· • ptE1) hx1),
    (mk_eq_mk_iff_five x h).2 (congrArg (fun τ : Equiv.Perm Five => τ fiveC) hx2)⟩

theorem ln_five_incident
    (g h : Pc 2) :
    ∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g ∧
      (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = h := by
  obtain ⟨x, hx1, hx2⟩ := exists_phiP3_eq (phiP3 g).1 (phiP3 h).2
  exact ⟨x, (mk_eq_mk_iff_ln x g).2 (congrArg (· • lnE2) hx1),
    (mk_eq_mk_iff_five x h).2 (congrArg (fun τ : Equiv.Perm Five => τ fiveC) hx2)⟩

theorem p3_chamber_transitive
    (g₀ g₁ g₃ : Pc 2)
    (h01 : ∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g₀ ∧
      (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g₁) :
    ∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g₀ ∧
      (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g₁ ∧ (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = g₃ := by
  obtain ⟨x, hx1, hx2, hx3⟩ := p3_flag_transitive ptE1 ((phiP3 g₀).1 • ptE1) lnE2
    ((phiP3 g₁).1 • lnE2) fiveC ((phiP3 g₃).2 fiveC) ptE1_le_lnE2 ((pt_ln_incident_iff g₀ g₁).1 h01)
  exact ⟨x, (mk_eq_mk_iff_pt x g₀).2 hx1, (mk_eq_mk_iff_ln x g₁).2 hx2,
    (mk_eq_mk_iff_five x g₃).2 hx3⟩

theorem conj_mem_Nc_two
    {x : Dfull} (hx : x ∈ Nc 2) (g : Pc 2) :
    (g : Dfull)⁻¹ * x * g ∈ Nc 2 := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨g⁻¹ * n * g⁻¹⁻¹, (CFSG.pCore_normal (p := 2) (G := Pc 2)).conj_mem n hn g⁻¹, by simp⟩

theorem phiP3_fst_smul_eq
    (y : Pc 2) (h0 : ∀ g : Pc 2, ((g⁻¹ * y * g : Pc 2) : Dfull) ∈ Pc 0)
    (g : Pc 2) : (phiP3 y).1 • ((phiP3 g).1 • ptE1) = (phiP3 g).1 • ptE1 := by
  have h := (mem_Pc0_iff (g⁻¹ * y * g)).1 (h0 g)
  have key : (phiP3 (g⁻¹ * y * g)).1 = ((phiP3 g).1)⁻¹ * (phiP3 y).1 * (phiP3 g).1 := by
    simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv]
  have h' : ((phiP3 g).1)⁻¹ • (phiP3 y).1 • (phiP3 g).1 • ptE1 = ptE1 :=
    ((mul_smul (((phiP3 g).1)⁻¹ * (phiP3 y).1) (phiP3 g).1 ptE1).trans
      (mul_smul ((phiP3 g).1)⁻¹ (phiP3 y).1 ((phiP3 g).1 • ptE1))).symm.trans
        ((congrArg (· • ptE1) key).symm.trans h)
  exact inv_smul_eq_iff.1 h'

theorem phiP3_snd_apply_eq
    (y : Pc 2) (h3 : ∀ g : Pc 2, ((g⁻¹ * y * g : Pc 2) : Dfull) ∈ Pc 3)
    (g : Pc 2) : (phiP3 y).2 ((phiP3 g).2 fiveC) = (phiP3 g).2 fiveC := by
  have h := (mem_Pc3_iff (g⁻¹ * y * g)).1 (h3 g)
  have key : (phiP3 (g⁻¹ * y * g)).2 = ((phiP3 g).2)⁻¹ * (phiP3 y).2 * (phiP3 g).2 := by
    simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]
  have h' : ((phiP3 g).2)⁻¹ ((phiP3 y).2 ((phiP3 g).2 fiveC)) = fiveC :=
    ((Equiv.Perm.mul_apply (((phiP3 g).2)⁻¹ * (phiP3 y).2) (phiP3 g).2 fiveC).trans
      (Equiv.Perm.mul_apply ((phiP3 g).2)⁻¹ (phiP3 y).2 ((phiP3 g).2 fiveC))).symm.trans
        ((congrArg (fun τ : Equiv.Perm Five => τ fiveC) key).symm.trans h)
  exact Equiv.Perm.inv_eq_iff_eq.1 h'

theorem mem_Nc_two_of_forall
    (y : Pc 2)
    (h0 : ∀ g : Pc 2, ((g⁻¹ * y * g : Pc 2) : Dfull) ∈ Pc 0)
    (h3 : ∀ g : Pc 2, ((g⁻¹ * y * g : Pc 2) : Dfull) ∈ Pc 3) : (y : Dfull) ∈ Nc 2 := by
  have h1 : (phiP3 y).1 = 1 := by
    refine eq_one_of_forall_map_eq _ fun S hS => ?_
    obtain ⟨g, hg⟩ := exists_smul_eq_sub ptE1 ⟨S, hS⟩
    calc S.map ((phiP3 y).1 : Additive E3 →ₗ[ZMod 2] Additive E3)
        = ((phiP3 y).1 • (⟨S, hS⟩ : SubspaceDim (ZMod 2) (Additive E3) 1)).1 :=
          (subspace_smul_coe (phiP3 y).1 ⟨S, hS⟩).symm
      _ = ((phiP3 y).1 • ((phiP3 g).1 • ptE1)).1 :=
          congrArg (fun T : SubspaceDim (ZMod 2) (Additive E3) 1 => ((phiP3 y).1 • T).1) hg.symm
      _ = ((phiP3 g).1 • ptE1).1 := congrArg Subtype.val (phiP3_fst_smul_eq y h0 g)
      _ = S := congrArg Subtype.val hg
  have h2 : (phiP3 y).2 = 1 := by
    refine Equiv.ext fun C' => ?_
    obtain ⟨g, hg⟩ := exists_smul_eq_five fiveC C'
    calc (phiP3 y).2 C' = (phiP3 y).2 ((phiP3 g).2 fiveC) := congrArg (phiP3 y).2 hg.symm
      _ = (phiP3 g).2 fiveC := phiP3_snd_apply_eq y h3 g
      _ = C' := hg
      _ = (1 : Equiv.Perm Five) C' := (Equiv.Perm.one_apply C').symm
  have hker : y ∈ CFSG.pCore 2 (Pc 2) := ker_phiP3 ▸ MonoidHom.mem_ker.2 (Prod.ext h1 h2)
  exact ⟨y, hker, rfl⟩

theorem iInf_conjSub_eq :
    (⨅ (j : Fin 4) (_ : j ≠ 2) (g : Pc 2), conjSub (g : Dfull) (Pc 2 ⊓ Pc j)) = Nc 2 := by
  apply le_antisymm
  · intro x hx
    have hx' : ∀ j : Fin 4, j ≠ 2 → ∀ g : Pc 2, (g : Dfull)⁻¹ * x * g ∈ Pc 2 ⊓ Pc j :=
      fun j hj g => mem_conjSub.1
        (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx j) hj) g)
    have hxP : x ∈ Pc 2 := by simpa using (hx' 0 (by decide) 1).1
    exact mem_Nc_two_of_forall ⟨x, hxP⟩ (fun g => (hx' 0 (by decide) g).2)
      (fun g => (hx' 3 (by decide) g).2)
  · refine le_iInf fun j => le_iInf fun _ => le_iInf fun g => fun x hx => ?_
    have hn := conj_mem_Nc_two hx g
    exact mem_conjSub.2 ⟨Nc_le_Pc 2 2 hn, Nc_le_Pc 2 j hn⟩

theorem natCard_points_E3 :
    Nat.card (SubspaceDim (ZMod 2) (Additive E3) 1) = 7 := by
  rw [card_subspaces (by rw [finrank_additive_E3]; norm_num), ZMod.card, finrank_additive_E3]
  decide

theorem natCard_lines_E3 :
    Nat.card (SubspaceDim (ZMod 2) (Additive E3) 2) = 7 := by
  rw [card_subspaces (by rw [finrank_additive_E3]; norm_num), ZMod.card, finrank_additive_E3]
  decide

theorem index_Pc0_subgroupOf :
    ((Pc 0).subgroupOf (Pc 2)).index = 7 := by
  obtain ⟨f, -, -⟩ := exists_pt_equiv
  exact (Nat.card_congr f).trans natCard_points_E3

theorem index_Pc1_subgroupOf :
    ((Pc 1).subgroupOf (Pc 2)).index = 7 := by
  obtain ⟨f, -, -⟩ := exists_ln_equiv
  exact (Nat.card_congr f).trans natCard_lines_E3

theorem index_Pc3_subgroupOf :
    ((Pc 3).subgroupOf (Pc 2)).index = 5 := by
  obtain ⟨f, -, -⟩ := exists_five_equiv
  exact (Nat.card_congr f).trans natCard_orbit_subgeom

theorem short_third_centralizer_product_flag :
    Module.finrank (ZMod 2) (Additive E3) = 3 ∧
    (orbit K3 subgeom : Set (Set ParGeom)) =
      {C' | (∃ s : Shat, C' = subgeomConj s) ∧ stdObj 3 (by norm_num) (by norm_num) ∈ C'} ∧
    Nat.card Five = 5 ∧ (fiveC : Set ParGeom) = subgeom ∧
    (∀ s : Shat, (s • ·) '' subgeom = subgeom ↔ (s : Dfull) ∈ Xgrp) ∧
    (∀ k : K3, k • subgeom = subgeom ↔ (k : Dfull) ∈ Xgrp) ∧
    (∀ (g : Pc 2) (e : E3), ((Additive.toMul ((phiP3 g).1 (Additive.ofMul e)) : E3) : Dfull) =
      (g : Dfull) * e * (g : Dfull)⁻¹) ∧
    (∀ (g : Pc 2) (C' : Five), (((phiP3 g).2 C' : Five) : Set ParGeom) =
      (k3S (Subgroup.inclusion Pc2_le_K3 g) • ·) '' (C' : Set ParGeom)) ∧
    Function.Surjective phiP3 ∧ phiP3.ker = (Nc 2).subgroupOf (Pc 2) ∧
    phiP3.ker = CFSG.pCore 2 (Pc 2) ∧
    (∃ e : Pc 2 ⧸ CFSG.pCore 2 (Pc 2) ≃* (Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five,
      (∀ g : Pc 2, e g = phiP3 g) ∧
        ∀ H : Subgroup ((Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five),
          (H.comap e.toMonoidHom).comap (QuotientGroup.mk' (CFSG.pCore 2 (Pc 2))) =
            H.comap phiP3) ∧
    Nonempty ((Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five ≃*
      GL (Fin 3) (ZMod 2) × Equiv.Perm (Fin 5)) ∧
    Echain 1 = Subgroup.zpowers xhat ∧ Echain 2 = Vhat ∧
    ptE1.1 = subOf E3 (Echain 1) ∧ lnE2.1 = subOf E3 (Echain 2) ∧ ptE1.1 ≤ lnE2.1 ∧
    (Pc 0).subgroupOf (Pc 2) =
      ((stabilizer (Additive E3 ≃ₗ[ZMod 2] Additive E3) ptE1).prod ⊤).comap phiP3 ∧
    (Pc 1).subgroupOf (Pc 2) =
      ((stabilizer (Additive E3 ≃ₗ[ZMod 2] Additive E3) lnE2).prod ⊤).comap phiP3 ∧
    (Pc 3).subgroupOf (Pc 2) =
      ((⊤ : Subgroup (Additive E3 ≃ₗ[ZMod 2] Additive E3)).prod
        (stabilizer (Equiv.Perm Five) fiveC)).comap phiP3 ∧
    (∃ f : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2) ≃ SubspaceDim (ZMod 2) (Additive E3) 1,
      (∀ g : Pc 2, f g = (phiP3 g).1 • ptE1) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).1 • f a) ∧
    (∃ f : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2) ≃ SubspaceDim (ZMod 2) (Additive E3) 2,
      (∀ g : Pc 2, f g = (phiP3 g).1 • lnE2) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).1 • f a) ∧
    (∃ f : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2) ≃ Five,
      (∀ g : Pc 2, f g = (phiP3 g).2 fiveC) ∧
        ∀ (g : Pc 2) (a : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)), f (g • a) = (phiP3 g).2 (f a)) ∧
    Nat.card (SubspaceDim (ZMod 2) (Additive E3) 1) = 7 ∧
    Nat.card (SubspaceDim (ZMod 2) (Additive E3) 2) = 7 ∧
    ((Pc 0).subgroupOf (Pc 2)).index = 7 ∧ ((Pc 1).subgroupOf (Pc 2)).index = 7 ∧
    ((Pc 3).subgroupOf (Pc 2)).index = 5 ∧
    (∀ g h : Pc 2, (∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g ∧
      (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = h) ↔
        ((phiP3 g).1 • ptE1).1 ≤ ((phiP3 h).1 • lnE2).1) ∧
    (∀ g h : Pc 2, ∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g ∧
      (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = h) ∧
    (∀ g h : Pc 2, ∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g ∧
      (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = h) ∧
    (∀ (p p' : SubspaceDim (ZMod 2) (Additive E3) 1) (l l' : SubspaceDim (ZMod 2) (Additive E3) 2)
      (C' C'' : Five), p.1 ≤ l.1 → p'.1 ≤ l'.1 →
        ∃ g : Pc 2, (phiP3 g).1 • p = p' ∧ (phiP3 g).1 • l = l' ∧ (phiP3 g).2 C' = C'') ∧
    (∀ g₀ g₁ g₃ : Pc 2, (∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g₀ ∧
      (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g₁) →
        ∃ x : Pc 2, (x : Pc 2 ⧸ (Pc 0).subgroupOf (Pc 2)) = g₀ ∧
          (x : Pc 2 ⧸ (Pc 1).subgroupOf (Pc 2)) = g₁ ∧
            (x : Pc 2 ⧸ (Pc 3).subgroupOf (Pc 2)) = g₃) ∧
    (⨅ (j : Fin 4) (_ : j ≠ 2) (g : Pc 2), conjSub (g : Dfull) (Pc 2 ⊓ Pc j)) = Nc 2 :=
  ⟨finrank_additive_E3, fiveConj_eq_orbit.symm, natCard_orbit_subgeom, fiveC_coe, stab_S_iff,
    k3_smul_subgeom_eq_iff, phiP3_fst_apply, phiP3_snd_apply, phiP3_surjective, ker_phiP3_eq,
    ker_phiP3, ⟨p3QuotProd, p3QuotProd_mk, comap_mk_comap_p3QuotProd⟩, nonempty_prod_equiv, rfl,
    rfl, rfl, rfl, ptE1_le_lnE2, Pc0_subgroupOf, Pc1_subgroupOf, Pc3_subgroupOf, exists_pt_equiv,
    exists_ln_equiv, exists_five_equiv, natCard_points_E3, natCard_lines_E3, index_Pc0_subgroupOf,
    index_Pc1_subgroupOf, index_Pc3_subgroupOf, pt_ln_incident_iff, pt_five_incident,
    ln_five_incident, p3_flag_transitive, p3_chamber_transitive, iInf_conjSub_eq⟩

end CFSG.Monster.B.TwoA.Amalgam
