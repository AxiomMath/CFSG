module

public import CFSG.Monster.B.CTIB.VisibleOctad
public import CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixedCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionQuotientLocal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.Griess CFSG.Monster.B.TwoA.Census CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed
open scoped IsMulCommutative

theorem center_rhoQvis_eq : Subgroup.center rhoQvis = zRho :=
  CFSG.Monster.Existence.center_rhoQvis.trans (congrArg Subgroup.zpowers (Subtype.ext
    (Subtype.ext (CFSG.Monster.Existence.rhoQvisEquivQ_symm_zQ.trans
      (xmat_eq_xB.trans (coe_coe_rhoN_zQ).symm)))))

theorem conj_mem_centerQ_iff (g : Gvis) (q : rhoQvis) :
    g * (q : Gvis) * g⁻¹ * (q : Gvis)⁻¹ ∈ (Subgroup.center rhoQvis).map rhoQvis.subtype ↔
      (QuotientGroup.mk (MulAut.conjNormal g q) : VisMod) = QuotientGroup.mk q := by
  have e : rhoQvis.subtype (MulAut.conjNormal g q / q) = g * (q : Gvis) * g⁻¹ * (q : Gvis)⁻¹ := by
    simp only [div_eq_mul_inv, map_mul, map_inv, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  refine (Iff.of_eq (congrArg (· ∈ (Subgroup.center rhoQvis).map rhoQvis.subtype) e)).symm.trans
    ((Subgroup.mem_map_iff_mem rhoQvis.subtype_injective).trans ?_)
  exact (Iff.of_eq (congrArg (MulAut.conjNormal g q / q ∈ ·) center_rhoQvis_eq)).trans
    QuotientGroup.eq_iff_div_mem.symm

theorem mem_rhoQvis_of_forall (g : Gvis)
    (h : ∀ q ∈ rhoQvis, g * q * g⁻¹ * q⁻¹ ∈ (Subgroup.center rhoQvis).map rhoQvis.subtype) :
    g ∈ rhoQvis := by
  rw [← ker_conjVis, MonoidHom.mem_ker, conjVis_eq_one_iff]
  exact fun q => (conj_mem_centerQ_iff g q).1 (h q q.2)

theorem octad_fix
    (q : Gvis) (hq : q ∈ rhoQvis)
    (h : cosetRep 1 * q * (cosetRep 1)⁻¹ * q⁻¹ ∈ (Subgroup.center rhoQvis).map rhoQvis.subtype) :
    q ∈ rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} := by
  have hk := (conj_mem_centerQ_iff (cosetRep 1) ⟨q, hq⟩).1 h
  have ht := rhoN_surjective ⟨q, hq⟩
  obtain ⟨t, ht⟩ := ht
  rw [← ht] at hk
  have hc := commute_of_octA_fix t ((repVis_apply _ _).trans (congrArg Additive.ofMul hk))
  have hq' : (rhoN t : Gvis) = q := congrArg Subtype.val ht
  rw [hq'] at hc
  exact ⟨hq, Subgroup.mem_centralizer_singleton_iff.2 hc⟩

instance finite_Gvis_of_Gmat : Finite Gvis :=
  Finite.of_injective (fun g : Gvis => (⟨g, Hmat_le_Gmat g.2⟩ : Gmat)) fun _ _ h =>
    Subtype.ext (congrArg (fun y : Gmat => (y : SpaceB ≃ₗ[ℚ] SpaceB)) h)

theorem orderOf_cosetRep_one_Gvis :
    orderOf (cosetRep 1) = 2 :=
  (Subgroup.orderOf_coe (cosetRep 1)).symm.trans orderOf_cosetRep_one

theorem ordProj_visQuot :
    ordProj[2] (Nat.card (Gvis ⧸ rhoQvis)) = 2 ^ 21 := by
  rw [CFSG.Monster.Existence.natCard_visQuot_eq,
    show (4157776806543360000 : ℕ) = 2 ^ 21 * 1982582476875 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem octad_extraspecial_fixed :
    IsPGroup 2 ↥(Subgroup.centralizer {cosetRep 1} ⊓ Subgroup.centralizer
        ((rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) : Set Gvis)) ∧
      CFSG.IsCharacteristicP 2 (Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) ∧
      (∀ K : Subgroup (Subgroup.centralizer {cosetRep 1} : Subgroup Gvis),
        ¬ CFSG.IsComponent K) ∧
      ordProj[2] (Nat.card (Subgroup.centralizer {cosetRep 1} : Subgroup Gvis)) ≤
        Nat.card (rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) *
          ordProj[2] (Nat.card (Gvis ⧸ rhoQvis)) :=
  extraspecial_full_fixed_space_centralizer_normal_two_subgroup inferInstance
    CFSG.Monster.Existence.isExtraspecialPGroup_rhoQvis rfl mem_rhoQvis_of_forall
    orderOf_cosetRep_one_Gvis rfl rfl fun q hq h => le_sup_left (a := rhoQvis ⊓
      Subgroup.centralizer {cosetRep 1}) (octad_fix q hq h)

theorem ordProj_octC_le :
    ordProj[2] (Nat.card (Subgroup.centralizer {cosetRep 1} : Subgroup Gvis)) ≤ 2 ^ 38 := by
  have h := octad_extraspecial_fixed.2.2.2
  rw [natCard_octU, ordProj_visQuot] at h
  exact h.trans (by norm_num)

@[expose] noncomputable def hGmat :
    Gmat := ⟨cosetRep 1, Hmat_le_Gmat (cosetRep 1).2⟩

theorem xmat_comm_cosetRep_one :
    xmat * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = cosetRep 1 * xmat :=
  (mul_inv_eq_iff_eq_mul.1 (Gvis_conj_xmat (cosetRep 1).2)).symm

theorem xGmat_mem_centralizer_hGmat :
    CFSG.Monster.Existence.xGmat ∈ Subgroup.centralizer ({hGmat} : Set Gmat) :=
  Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext xmat_comm_cosetRep_one)

theorem comm_xmat_of_mem_Gvis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gvis) : g * xmat = xmat * g :=
  mul_inv_eq_iff_eq_mul.1 (Gvis_conj_xmat hg)

theorem mem_centralizer_pair_iff {G : Type*} [Group G] {a b g : G} :
    g ∈ Subgroup.centralizer ({a, b} : Set G) ↔ a * g = g * a ∧ b * g = g * b := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨h a (Set.mem_insert _ _), h b (Set.mem_insert_of_mem _ rfl)⟩
  · rintro ⟨ha, hb⟩ y hy
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.1 hy]
      exact hb

@[expose] noncomputable def centPairEquiv :
    Subgroup.centralizer ({hGmat, CFSG.Monster.Existence.xGmat} : Set Gmat) ≃
      (Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) where
  toFun g := ⟨⟨g, Existence.Census.mem_Gvis_of_comm_xmat (g : Gmat).2
      (congrArg Subtype.val (mem_centralizer_pair_iff.1 g.2).2).symm⟩,
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
      (congrArg Subtype.val (mem_centralizer_pair_iff.1 g.2).1).symm)⟩
  invFun c := ⟨⟨c, Hmat_le_Gmat (c : Gvis).2⟩, mem_centralizer_pair_iff.2
    ⟨Subtype.ext (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2)).symm,
      Subtype.ext (comm_xmat_of_mem_Gvis (c : Gvis).2).symm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] noncomputable def octUGmat :
    Subgroup Gmat :=
  (Qmat ⊓ Subgroup.centralizer {(cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)}).subgroupOf Gmat

theorem mem_octUGmat_iff (g : Gmat) :
    g ∈ octUGmat ↔ (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Qmat ∧
      (g : SpaceB ≃ₗ[ℚ] SpaceB) * cosetRep 1 = cosetRep 1 * g :=
  Subgroup.mem_subgroupOf.trans (and_congr_right fun _ => Subgroup.mem_centralizer_singleton_iff)

theorem isPGroup_Qmat : IsPGroup 2 Qmat :=
  CFSG.Monster.Existence.isExtraspecialPGroup_rhoQvis.1.of_equiv
    (Subgroup.subgroupOfEquivOfLe Qmat_le_Hmat)

theorem octUGmat_le :
    octUGmat ≤ Subgroup.centralizer ({hGmat, CFSG.Monster.Existence.xGmat} :
    Set Gmat) := fun g hg =>
  mem_centralizer_pair_iff.2 ⟨Subtype.ext ((mem_octUGmat_iff g).1 hg).2.symm,
    Subtype.ext (comm_xmat_of_mem_Gvis (Qmat_le_Hmat ((mem_octUGmat_iff g).1 hg).1)).symm⟩

theorem conj_comm_of_comm {G : Type*} [Group G] {a b h : G} (ha : a * h = h * a)
    (hb : b * h = h * b) : a * b * a⁻¹ * h = h * (a * b * a⁻¹) := by
  have ha' : a⁻¹ * h = h * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]
  calc a * b * a⁻¹ * h = a * b * (h * a⁻¹) := by rw [mul_assoc, ha']
    _ = a * (b * h) * a⁻¹ := by group
    _ = a * (h * b) * a⁻¹ := by rw [hb]
    _ = (a * h) * b * a⁻¹ := by group
    _ = h * (a * b * a⁻¹) := by rw [ha]; group

theorem octUGmat_normal :
    (octUGmat.subgroupOf (Subgroup.centralizer
    ({hGmat, CFSG.Monster.Existence.xGmat} : Set Gmat))).Normal := by
  refine ⟨fun n hn c => Subgroup.mem_subgroupOf.2 ((mem_octUGmat_iff _).2 ?_)⟩
  have hn' := (mem_octUGmat_iff _).1 (Subgroup.mem_subgroupOf.1 hn)
  have hc := mem_centralizer_pair_iff.1 c.2
  have hcV : ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis :=
    Existence.Census.mem_Gvis_of_comm_xmat (c : Gmat).2 (congrArg Subtype.val hc.2).symm
  have hnV : ((n : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := Qmat_le_Hmat hn'.1
  have hch : ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * cosetRep 1 = cosetRep 1 * (c : Gmat) :=
    (congrArg Subtype.val hc.1).symm
  have hQ : ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (n : Gmat) *
      ((c : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ ∈ Qmat :=
    Subgroup.mem_subgroupOf.1 ((normal_rhoQ_subgroupOf).conj_mem ⟨_, hnV⟩
      (Subgroup.mem_subgroupOf.2 hn'.1) ⟨_, hcV⟩)
  exact ⟨hQ, conj_comm_of_comm hch hn'.2⟩

theorem isPGroup_octUGmat :
    IsPGroup 2 octUGmat :=
  isPGroup_of_forall_mem isPGroup_Qmat fun g hg => ((mem_octUGmat_iff g).1 hg).1

theorem hGmat_not_mem_octUGmat :
    hGmat ∉ octUGmat := fun h =>
  cosetRep_one_not_mem_Qmat ((mem_octUGmat_iff _).1 h).1

theorem isPGroup_centPair_inf :
    IsPGroup 2 ↥(Subgroup.centralizer
    ({hGmat, CFSG.Monster.Existence.xGmat} : Set Gmat) ⊓
      Subgroup.centralizer (octUGmat : Set Gmat)) := by
  refine isPGroup_of_forall_mem (octad_extraspecial_fixed.1.map Gvis.subtype)
    fun g hg => ?_
  have hc := mem_centralizer_pair_iff.1 hg.1
  have hgV : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis :=
    Existence.Census.mem_Gvis_of_comm_xmat g.2 (congrArg Subtype.val hc.2).symm
  have hgC : (⟨g, hgV⟩ : Gvis) ∈ (Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (congrArg Subtype.val hc.1).symm)
  have hgU : (⟨g, hgV⟩ : Gvis) ∈ Subgroup.centralizer
      ((rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) : Set Gvis) := by
    refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
    have hu' : (⟨u, Hmat_le_Gmat u.2⟩ : Gmat) ∈ octUGmat := (mem_octUGmat_iff _).2
      ⟨hu.1, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hu.2)⟩
    have h1 := congrArg (fun y : Gmat => (y : SpaceB ≃ₗ[ℚ] SpaceB))
      ((Subgroup.mem_centralizer_iff.1 hg.2) _ hu')
    exact Subtype.ext h1
  exact ⟨⟨g, hgV⟩, ⟨hgC, hgU⟩, rfl⟩

abbrev octadD :
    Type := Subgroup.centralizer ({hGmat} : Set Gmat) ⧸ selfZpowers hGmat

@[expose] noncomputable def octadT :
    octadD :=
  QuotientGroup.mk ⟨CFSG.Monster.Existence.xGmat, xGmat_mem_centralizer_hGmat⟩

theorem hGmat_ne_xGmat :
    hGmat ≠ CFSG.Monster.Existence.xGmat := fun h => by
  have e : (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = xmat := congrArg Subtype.val h
  exact cosetRep_one_not_mem_Qmat (e ▸ xmat_mem_Qmat)

theorem orderOf_hGmat :
    orderOf hGmat = 2 :=
  (Subgroup.orderOf_coe hGmat).symm.trans orderOf_cosetRep_one

theorem orderOf_xGmat' : orderOf CFSG.Monster.Existence.xGmat = 2 :=
  (Subgroup.orderOf_coe CFSG.Monster.Existence.xGmat).symm.trans orderOf_xmat

theorem octad_involution_quotient :
    CFSG.IsCharacteristicP 2 (Subgroup.centralizer {octadT} : Subgroup octadD) ∧
      (∀ K : Subgroup (Subgroup.centralizer {octadT} : Subgroup octadD), ¬ CFSG.IsComponent K) ∧
      ordProj[2] (Nat.card (Subgroup.centralizer {octadT} : Subgroup octadD)) ≤
        ordProj[2] (Nat.card (Subgroup.centralizer
          ({hGmat, CFSG.Monster.Existence.xGmat} : Set Gmat))) :=
  central_involution_quotient_local_normal_two_subgroup orderOf_hGmat orderOf_xGmat'
    hGmat_ne_xGmat xGmat_mem_centralizer_hGmat octUGmat_le octUGmat_normal isPGroup_octUGmat
    hGmat_not_mem_octUGmat isPGroup_centPair_inf

theorem ordProj_centPair_le :
    ordProj[2] (Nat.card (Subgroup.centralizer
    ({hGmat, CFSG.Monster.Existence.xGmat} : Set Gmat))) ≤ 2 ^ 38 :=
  (congrArg (fun n => ordProj[2] n) (Nat.card_congr centPairEquiv)).trans_le ordProj_octC_le

theorem visible_octad_centralizer_normal_two_subgroup_and_bound :
    ((rhoQvis ⊓ Subgroup.centralizer {cosetRep 1}).subgroupOf
        (Subgroup.centralizer {cosetRep 1})).Normal ∧
      Nat.card (rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) = 2 ^ 17 ∧
      cosetRep 1 ∉ (rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) ∧
      IsPGroup 2 ↥(Subgroup.centralizer {cosetRep 1} ⊓ Subgroup.centralizer
        ((rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) : Set Gvis)) ∧
      ordProj[2] (Nat.card (Subgroup.centralizer {cosetRep 1} : Subgroup Gvis)) ≤ 2 ^ 38 ∧
      CFSG.IsCharacteristicP 2 (Subgroup.centralizer {octadT} : Subgroup octadD) ∧
      (∀ K : Subgroup (Subgroup.centralizer {octadT} : Subgroup octadD), ¬ CFSG.IsComponent K) ∧
      ordProj[2] (Nat.card (Subgroup.centralizer {octadT} : Subgroup octadD)) ≤ 2 ^ 38 := by
  have hq := octad_involution_quotient
  refine ⟨?_, natCard_octU, fun h => cosetRep_one_not_mem_Qmat (Subgroup.mem_subgroupOf.1 h.1),
    octad_extraspecial_fixed.1, ordProj_octC_le, hq.1, hq.2.1, hq.2.2.trans ordProj_centPair_le⟩
  rw [Subgroup.inf_subgroupOf_right]
  infer_instance

end CFSG.Monster.B.CTIB
