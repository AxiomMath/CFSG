module

public import CFSG.Monster.B.TwoA.Amalgam.Kernels
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 MulAction

open scoped IsMulCommutative

attribute [local instance] k3SetAction subspaceAction parAction

abbrev Five : Type := orbit K3 subgeom

@[expose] def fiveC :
    Five := ⟨subgeom, mem_orbit_self subgeom⟩

theorem fiveC_coe :
    (fiveC : Set ParGeom) = subgeom := rfl

@[expose] def rho5 :
    K3 →* Equiv.Perm Five := toPermHom K3 Five

theorem coe_rho5
    (k : K3) (C' : Five) :
    ((rho5 k C' : Five) : Set ParGeom) = k • (C' : Set ParGeom) := by
  rw [rho5, toPermHom_apply, toPerm_apply, orbit.coe_smul]

theorem rho5_surjective :
    Function.Surjective rho5 := surjective_toPermHom_fiveConj

theorem ker_sigma3_le_ker_rho5 :
    sigma3.ker ≤ rho5.ker := fun n hn => by
  rw [MonoidHom.mem_ker]
  refine Equiv.ext fun ω => ?_
  exact fixes_of_normal_of_coprime Nat.prime_five natCard_orbit_subgeom sigma3.ker
    (by rw [natCard_ker_sigma3]; norm_num) ⟨n, hn⟩ ω

theorem natCard_perm_Five :
    Nat.card (Equiv.Perm Five) = 120 := by
  rw [Nat.card_perm, natCard_orbit_subgeom]
  rfl

theorem natCard_perm_fin_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem ker_rho5 :
    rho5.ker = sigma3.ker := by
  refine (Subgroup.eq_of_le_of_card_ge ker_sigma3_le_ker_rho5 ?_).symm
  have h1 := Subgroup.card_mul_index rho5.ker
  have h2 := Subgroup.card_mul_index sigma3.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 rho5_surjective, Subgroup.card_top,
    natCard_perm_Five] at h1
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 sigma3_surjective, Subgroup.card_top,
    natCard_perm_fin_five] at h2
  omega

@[expose] def psiK3 :
    K3 →* (Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five :=
  (linConj E3).prod rho5

theorem psiK3_apply
    (k : K3) : psiK3 k = (linConj E3 k, rho5 k) := by
  rw [psiK3, MonoidHom.prod_apply]

@[expose] def glE3Equiv :
    (Additive E3 ≃ₗ[ZMod 2] Additive E3) ≃* GL (Fin 3) (ZMod 2) :=
  (mulAutEquivLinear E3).symm.trans (mulAutEquivGL natCard_E3_pow)

theorem glE3Equiv_linConj
    (k : K3) : glE3Equiv (linConj E3 k) = actE3 k := by
  change mulAutEquivGL natCard_E3_pow ((mulAutEquivLinear E3).symm
    (mulAutEquivLinear E3 (conjE E3 k))) = mulAutEquivGL natCard_E3_pow (conjE E3 k)
  rw [MulEquiv.symm_apply_apply]

theorem linConj_eq_one_iff
    (k : K3) : linConj E3 k = 1 ↔ actE3 k = 1 := by
  rw [← glE3Equiv_linConj, MulEquiv.map_eq_one_iff]

theorem ker_psiK3 :
    psiK3.ker = R3.subgroupOf K3 := by
  obtain ⟨e, he⟩ := exists_k3QuotProd
  ext k
  rw [MonoidHom.mem_ker, psiK3_apply, Prod.mk_eq_one, linConj_eq_one_iff,
    ← MonoidHom.mem_ker (f := rho5), ker_rho5, MonoidHom.mem_ker,
    ← QuotientGroup.eq_one_iff (N := R3.subgroupOf K3), ← e.map_eq_one_iff, he, Prod.mk_eq_one]

theorem psiK3_surjective :
    Function.Surjective psiK3 := by
  obtain ⟨e, he⟩ := exists_k3QuotProd
  intro y
  obtain ⟨k₁, hk₁⟩ := rho5_surjective y.2
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm (glE3Equiv y.1, sigma3 k₁))
  have h := he k
  rw [hk, MulEquiv.apply_symm_apply, Prod.mk.injEq] at h
  have hσ : k₁⁻¹ * k ∈ sigma3.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← h.2, inv_mul_cancel]
  rw [← ker_rho5, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hσ
  refine ⟨k, ?_⟩
  have e1 : linConj E3 k = y.1 := glE3Equiv.injective ((glE3Equiv_linConj k).trans h.1.symm)
  have e2 : rho5 k = y.2 := hσ.symm.trans hk₁
  exact (psiK3_apply k).trans (Prod.ext e1 e2)

theorem Pc2_le_K3 : Pc 2 ≤ K3 := by
  rw [Pc_two]
  exact inf_le_left

theorem mem_centralizer_of_Pc2
    (g : Pc 2) : (g : Dfull) ∈ Subgroup.centralizer {cQ} :=
  Pc_le_centralizer 2 g.2

@[expose] def phiP3 :
    Pc 2 →* (Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five :=
  psiK3.comp (Subgroup.inclusion Pc2_le_K3)

theorem phiP3_apply
    (g : Pc 2) : phiP3 g = psiK3 (Subgroup.inclusion Pc2_le_K3 g) := by
  rw [phiP3, MonoidHom.comp_apply]

theorem phiP3_fst
    (g : Pc 2) : (phiP3 g).1 = linConj E3 (Subgroup.inclusion Pc2_le_K3 g) := by
  rw [phiP3_apply, psiK3_apply]

theorem phiP3_snd
    (g : Pc 2) : (phiP3 g).2 = rho5 (Subgroup.inclusion Pc2_le_K3 g) := by
  rw [phiP3_apply, psiK3_apply]

theorem phiP3_fst_apply
    (g : Pc 2) (e : E3) :
    ((Additive.toMul ((phiP3 g).1 (Additive.ofMul e)) : E3) : Dfull) =
      (g : Dfull) * e * (g : Dfull)⁻¹ := by
  rw [phiP3_fst, linConj_apply, Subgroup.coe_inclusion]

theorem phiP3_snd_apply
    (g : Pc 2) (C' : Five) :
    (((phiP3 g).2 C' : Five) : Set ParGeom) =
      (k3S (Subgroup.inclusion Pc2_le_K3 g) • ·) '' (C' : Set ParGeom) := by
  rw [phiP3_snd, coe_rho5, k3_smul_set]

theorem exists_Pc2_of_K3
    (k : K3) :
    ∃ (p : Pc 2) (r : K3), (r : Dfull) ∈ R3 ∧ Subgroup.inclusion Pc2_le_K3 p = r * k := by
  obtain ⟨r, hr, hrc⟩ := Par3.cE3_R3_transitive (Par3.conj_cQ_mem_cE3 k.2) Par3.cQ_mem_cE3
  have hm : r * (k : Dfull) ∈ Pc 2 := by
    rw [Pc_two]
    refine ⟨K3.mul_mem (Par3.R3_le_K3 hr) k.2, (Par3.stabilizer_iff _).1 ?_⟩
    calc r * (k : Dfull) * cQ * (r * k)⁻¹ = r * ((k : Dfull) * cQ * (k : Dfull)⁻¹) * r⁻¹ := by
          group
      _ = cQ := hrc
  exact ⟨⟨_, hm⟩, ⟨r, Par3.R3_le_K3 hr⟩, hr, Subtype.ext rfl⟩

theorem phiP3_surjective :
    Function.Surjective phiP3 := by
  intro y
  obtain ⟨k, rfl⟩ := psiK3_surjective y
  obtain ⟨p, r, hr, hp⟩ := exists_Pc2_of_K3 k
  have hrK : r ∈ psiK3.ker := by
    rw [ker_psiK3]
    exact Subgroup.mem_subgroupOf.2 hr
  refine ⟨p, ?_⟩
  calc phiP3 p = psiK3 (Subgroup.inclusion Pc2_le_K3 p) := phiP3_apply p
    _ = psiK3 r * psiK3 k := (congrArg psiK3 hp).trans (map_mul psiK3 r k)
    _ = psiK3 k := (congrArg (· * psiK3 k) (MonoidHom.mem_ker.1 hrK)).trans (one_mul _)

theorem mem_ker_phiP3_iff
    (g : Pc 2) : g ∈ phiP3.ker ↔ (g : Dfull) ∈ R3 := by
  rw [MonoidHom.mem_ker, phiP3_apply, ← MonoidHom.mem_ker, ker_psiK3, Subgroup.mem_subgroupOf,
    Subgroup.coe_inclusion]

theorem Nc_two_subgroupOf :
    (Nc 2).subgroupOf (Pc 2) = CFSG.pCore 2 (Pc 2) :=
  Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _

theorem ker_phiP3_eq :
    phiP3.ker = (Nc 2).subgroupOf (Pc 2) := by
  ext g
  rw [mem_ker_phiP3_iff, Subgroup.mem_subgroupOf, Nc_two, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h, mem_centralizer_of_Pc2 g⟩, fun h => h.1⟩

theorem ker_phiP3 :
    phiP3.ker = CFSG.pCore 2 (Pc 2) := ker_phiP3_eq.trans Nc_two_subgroupOf

@[expose] def p3QuotProd :
    Pc 2 ⧸ CFSG.pCore 2 (Pc 2) ≃* (Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five :=
  (QuotientGroup.quotientMulEquivOfEq ker_phiP3.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective phiP3 phiP3_surjective)

theorem p3QuotProd_mk
    (g : Pc 2) : p3QuotProd (g : Pc 2 ⧸ CFSG.pCore 2 (Pc 2)) = phiP3 g := rfl

theorem comap_mk_comap_p3QuotProd
    (H : Subgroup ((Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five)) :
    (H.comap p3QuotProd.toMonoidHom).comap (QuotientGroup.mk' (CFSG.pCore 2 (Pc 2))) =
      H.comap phiP3 := by
  have h : p3QuotProd.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 (Pc 2))) = phiP3 :=
    MonoidHom.ext fun g => p3QuotProd_mk g
  rw [Subgroup.comap_comap, h]

theorem nonempty_prod_equiv :
    Nonempty ((Additive E3 ≃ₗ[ZMod 2] Additive E3) × Equiv.Perm Five ≃*
      GL (Fin 3) (ZMod 2) × Equiv.Perm (Fin 5)) :=
  ⟨glE3Equiv.prodCongr (Equiv.permCongrHom (Finite.equivFinOfCardEq natCard_orbit_subgeom))⟩

theorem zpowers_xhat_le_E3 : Subgroup.zpowers xhat ≤ E3 := Subgroup.zpowers_le.2 xhat_mem_E3

@[expose] def ptE1 : SubspaceDim (ZMod 2) (Additive E3) 1 :=
  ⟨subOf E3 (Subgroup.zpowers xhat), finrank_subOf E3 zpowers_xhat_le_E3 natCard_zpowers_xhat⟩

@[expose] def lnE2 : SubspaceDim (ZMod 2) (Additive E3) 2 :=
  ⟨subOf E3 Vhat, finrank_subOf E3 Vhat_le_E3 natCard_Vhat_pow⟩

theorem ptE1_coe : ptE1.1 = subOf E3 (Subgroup.zpowers xhat) := rfl

theorem lnE2_coe : lnE2.1 = subOf E3 Vhat := rfl

theorem ptE1_le_lnE2 : ptE1.1 ≤ lnE2.1 := fun _ hx =>
  (mem_subOf E3).2 (Subgroup.zpowers_le.2 xhat_mem_Vhat ((mem_subOf E3).1 hx))

theorem subspace_smul_coe {j : ℕ} (A : Additive E3 ≃ₗ[ZMod 2] Additive E3)
    (S : SubspaceDim (ZMod 2) (Additive E3) j) :
    (A • S).1 = S.1.map (A : Additive E3 →ₗ[ZMod 2] Additive E3) := rfl

theorem mem_Pc0_iff
    (g : Pc 2) : (g : Dfull) ∈ Pc 0 ↔ (phiP3 g).1 • ptE1 = ptE1 := by
  rw [← Subtype.coe_inj, subspace_smul_coe, phiP3_fst, ptE1_coe,
    map_linConj_eq_iff E3 zpowers_xhat_le_E3, Subgroup.coe_inclusion, normalizer_zpowers_xhat,
    Pc_zero, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_centralizer_of_Pc2 g⟩⟩

theorem mem_Pc1_iff
    (g : Pc 2) : (g : Dfull) ∈ Pc 1 ↔ (phiP3 g).1 • lnE2 = lnE2 := by
  rw [← Subtype.coe_inj, subspace_smul_coe, phiP3_fst, lnE2_coe,
    map_linConj_eq_iff E3 Vhat_le_E3, Subgroup.coe_inclusion, Pc_one, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_centralizer_of_Pc2 g⟩⟩

theorem mem_Pc3_iff
    (g : Pc 2) : (g : Dfull) ∈ Pc 3 ↔ (phiP3 g).2 fiveC = fiveC := by
  rw [← Subtype.coe_inj, phiP3_snd, coe_rho5, fiveC_coe, k3_smul_subgeom_eq_iff,
    Subgroup.coe_inclusion, Pc_three, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, mem_centralizer_of_Pc2 g⟩⟩

theorem Pc0_subgroupOf :
    (Pc 0).subgroupOf (Pc 2) =
    ((stabilizer (Additive E3 ≃ₗ[ZMod 2] Additive E3) ptE1).prod ⊤).comap phiP3 := by
  ext g
  refine Subgroup.mem_subgroupOf.trans ((mem_Pc0_iff g).trans ?_)
  refine Iff.trans ?_ (Subgroup.mem_comap.trans Subgroup.mem_prod).symm
  exact ⟨fun h => ⟨mem_stabilizer_iff.2 h, Subgroup.mem_top _⟩, fun h => mem_stabilizer_iff.1 h.1⟩

theorem Pc1_subgroupOf :
    (Pc 1).subgroupOf (Pc 2) =
    ((stabilizer (Additive E3 ≃ₗ[ZMod 2] Additive E3) lnE2).prod ⊤).comap phiP3 := by
  ext g
  refine Subgroup.mem_subgroupOf.trans ((mem_Pc1_iff g).trans ?_)
  refine Iff.trans ?_ (Subgroup.mem_comap.trans Subgroup.mem_prod).symm
  exact ⟨fun h => ⟨mem_stabilizer_iff.2 h, Subgroup.mem_top _⟩, fun h => mem_stabilizer_iff.1 h.1⟩

theorem Pc3_subgroupOf :
    (Pc 3).subgroupOf (Pc 2) =
    ((⊤ : Subgroup (Additive E3 ≃ₗ[ZMod 2] Additive E3)).prod
      (stabilizer (Equiv.Perm Five) fiveC)).comap phiP3 := by
  ext g
  refine Subgroup.mem_subgroupOf.trans ((mem_Pc3_iff g).trans ?_)
  refine Iff.trans ?_ (Subgroup.mem_comap.trans Subgroup.mem_prod).symm
  exact ⟨fun h => ⟨Subgroup.mem_top _, mem_stabilizer_iff.2 h⟩,
    fun h => mem_stabilizer_iff.1 h.2⟩

end CFSG.Monster.B.TwoA.Amalgam
