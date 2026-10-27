module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.lemma_14_4_3

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

/-!
# Hall Lemma 14.4.4

Source interface for the generation of `H` by `H₀` and the diagonal defects.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u

set_option maxRecDepth 2000 in
/-- Source-faithful content of Hall Lemma 14.4.4.  The transfer is formed from
`G₀ = u_p(G)` to `H`, and `dstar u` is a representative in `H` of the actual
diagonal defect in `H / H₀`.  Only representatives indexed by `u ∈ P` are
needed to generate `H` together with `H₀`. -/
@[expose] public noncomputable def hallDiagonalDefectGeneration
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (N₁ H₁ G₀ H P H₀ : Subgroup G)
    (hN₁ : N₁ = Subgroup.normalizer ((P₁ : Subgroup G) : Set G))
    (hN₁_le_H₁ : N₁ ≤ H₁)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hH₀ : H₀ = hallTransferModulus p H H₁) : Prop := by
  have hH_le_G₀ : H ≤ G₀ := by
    rw [hH]
    exact inf_le_left
  have hH_le_H₁ : H ≤ H₁ := by
    rw [hH]
    exact inf_le_right
  have hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁ :=
    Subgroup.le_normalizer.trans (hN₁ ▸ hN₁_le_H₁)
  have hP_le_H : P ≤ H := by
    rw [hP, hH]
    exact inf_le_inf le_rfl hP₁_le_H₁
  have hH₀_le_H : H₀ ≤ H := by
    rw [hH₀]
    exact hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH
  have hH₀_normal : (H₀.subgroupOf H).Normal := by
    subst H₀
    exact hallTransferModulus_subgroupOf_normal p H H₁ hH_le_H₁
      (hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH)
  letI : (H₀.subgroupOf H).Normal := hH₀_normal
  have hcomm : commutator H ≤ H₀.subgroupOf H := by
    intro x hx
    have hxmap : H.subtype x ∈ (commutator H).map H.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hxmap
    have hC : ⁅H, H₁⁆ ≤ H₀ := by
      rw [hH₀]
      exact le_sup_right.trans le_sup_left
    exact hC ((Subgroup.commutator_mono le_rfl hH_le_H₁) hxmap)
  letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcomm
  letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
  let HG₀ : Subgroup G₀ := H.subgroupOf G₀
  let eH : HG₀ ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G₀
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let φ : HG₀ →* H ⧸ H₀.subgroupOf H := π.comp eH.toMonoidHom
  exact ∃ dstar : H → H,
    (∀ u : H, π (dstar u) =
      hallDiagonalDefect (G := G₀) (H := HG₀) φ (eH.symm u)) ∧
      H ≤ H₀ ⊔ Subgroup.closure
        {x : G | ∃ u : H, (u : G) ∈ P ∧ x = (dstar u : G)}

private theorem hall_hom_eq_one_of_domain_eq_pResidual
    {G A : Type*} [Group G] [Finite G] [Group A]
    (p : ℕ) [Fact p.Prime] (G₀ : Subgroup G)
    (hG₀ : G₀ = hallPResidual p G) (f : G₀ →* A)
    (hA : IsPGroup p A) : f = 1 := by
  subst G₀
  ext x
  change f x = 1
  exact Subgroup.closure_induction (p := fun g hg => f ⟨g, hg⟩ = 1)
    (fun g hg => by
      let a : hallPResidual p G := ⟨g, Subgroup.subset_closure hg⟩
      change f a = 1
      rw [← orderOf_eq_one_iff]
      have hdiv : orderOf (f a) ∣ orderOf (a : G) := by
        simpa only [Subgroup.orderOf_coe] using orderOf_map_dvd f a
      have hcop : p.Coprime (orderOf (f a)) :=
        Nat.Coprime.of_dvd_right hdiv hg
      have hself : (orderOf (f a)).Coprime (orderOf (f a)) :=
        hA.orderOf_coprime hcop (f a)
      exact Nat.eq_one_of_dvd_coprimes hself dvd_rfl dvd_rfl)
    (by change f 1 = 1; exact map_one f)
    (fun x y hx hy hx1 hy1 => by
      change f (⟨x, hx⟩ * ⟨y, hy⟩) = 1
      simp [hx1, hy1])
    (fun x hx hx1 => by
      change f (⟨x, hx⟩⁻¹) = 1
      simp [hx1])
    x.property
private theorem hall_lemma_14_4_4_defect_term_eq_sylow_defect
    {G A : Type u} [Group G] [Finite G]
    {H : Subgroup G} [H.FiniteIndex] [CommGroup A]
    (p : ℕ) [Fact p.Prime] (S : Sylow p H) (φ : H →* A)
    {u y : H} (hu : u ∈ (S : Subgroup H))
    (hy : ∃ n : ℕ,
      (y : G) = (u : G) ^ n ∨
        IsConj ((u : G) ^ n) ((y : G)⁻¹)) :
    ∃ v : H, v ∈ (S : Subgroup H) ∧
      hallDiagonalDefect (H := H) φ y =
        hallDiagonalDefect (H := H) φ v := by
  classical
  rcases hy with ⟨n, hyn | hyn⟩
  · have hyu : y = u ^ n := by
      apply Subtype.ext
      simpa using hyn
    subst y
    exact ⟨u ^ n, S.pow_mem hu n, rfl⟩
  · let unS : S := ⟨u ^ n, S.pow_mem hu n⟩
    obtain ⟨k, hk⟩ := S.isPGroup' unS
    have hpow_unG : ((u : G) ^ n) ^ p ^ k = 1 := by
      have hcoe := congrArg (fun z : S => (((z : H) : G))) hk
      simpa [unS] using hcoe
    have hpow_inv_yG : ((y : G)⁻¹) ^ p ^ k = 1 := by
      exact isConj_one_right.mp (hpow_unG ▸ hyn.pow (p ^ k))
    have hpow_yH : y ^ p ^ k = 1 := by
      apply Subtype.ext
      change (y : G) ^ p ^ k = 1
      have h := congrArg Inv.inv hpow_inv_yG
      simpa only [inv_pow, inv_inv, inv_one] using h
    have hord_dvd : orderOf y ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one hpow_yH
    obtain ⟨j, _hj_le, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hord_dvd
    have hyPgroup : IsPGroup p (Subgroup.zpowers y) := by
      apply IsPGroup.of_card (n := j)
      rw [Nat.card_zpowers, hj]
    obtain ⟨T, hyT⟩ := IsPGroup.exists_le_sylow (G := H) (p := p) hyPgroup
    obtain ⟨g, hgTS⟩ := MulAction.exists_smul_eq H T S
    let v : H := (MulAut.conj g) y
    have hvS : v ∈ (S : Subgroup H) := by
      rw [← hgTS, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g)
        (T : Subgroup H) (hyT (Subgroup.mem_zpowers y))
    have hyv : IsConj (y : G) (v : G) := by
      rw [isConj_iff]
      exact ⟨(g : G), by rfl⟩
    have hdiag :
        hallDiagonalContribution (H := H) φ (y : G) =
          hallDiagonalContribution (H := H) φ (v : G) :=
      (hall_lemma_14_4_2_diagonal_contribution_conjugacy φ).1
        (y : G) (v : G) hyv
    have hφ : φ v = φ y := by
      simp [v, mul_assoc, mul_comm, mul_left_comm]
    refine ⟨v, hvS, ?_⟩
    simp only [hallDiagonalDefect]
    rw [hφ, hdiag]

private theorem hall_lemma_14_4_4_sylow_le_defect_closure
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (H₁ G₀ H P H₀ : Subgroup G)
    (hG₀ : G₀ = hallPResidual p G)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hH₀ : H₀ = hallTransferModulus p H H₁)
    (hH_le_G₀ : H ≤ G₀) (hP_le_H : P ≤ H) (hH₀_le_H : H₀ ≤ H)
    [hH₀_normal : (H₀.subgroupOf H).Normal]
    (hcomm : commutator H ≤ H₀.subgroupOf H) :
    letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcomm
    letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
    ∀ dstar : H → H,
      (∀ u : H,
        QuotientGroup.mk' (H₀.subgroupOf H) (dstar u) =
          hallDiagonalDefect (G := G₀) (H := H.subgroupOf G₀)
            ((QuotientGroup.mk' (H₀.subgroupOf H)).comp
              (Subgroup.subgroupOfEquivOfLe hH_le_G₀).toMonoidHom)
            ((Subgroup.subgroupOfEquivOfLe hH_le_G₀).symm u)) →
      P ≤ H₀ ⊔ Subgroup.closure
        {x : G | ∃ u : H, (u : G) ∈ P ∧ x = (dstar u : G)} := by
  letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcomm
  letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
  intro dstar hdstar
  let HG₀ : Subgroup G₀ := H.subgroupOf G₀
  let eH : HG₀ ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G₀
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let φ : HG₀ →* H ⧸ H₀.subgroupOf H := π.comp eH.toMonoidHom
  have hres_le_H₀ : hallPResidual p H ≤ H₀.subgroupOf H := by
    intro x hx
    change (x : G) ∈ H₀
    rw [hH₀]
    exact (le_sup_right : (hallPResidual p H).map H.subtype ≤
      hallPPowerSubgroup p H ⊔ ⁅H, H₁⁆ ⊔ (hallPResidual p H).map H.subtype)
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hquot_p : IsPGroup p (H ⧸ H₀.subgroupOf H) :=
    hallPResidual_le_quotient_isPGroup p (H₀.subgroupOf H) hres_le_H₀
  have htransfer_one : MonoidHom.transfer φ = 1 :=
    hall_hom_eq_one_of_domain_eq_pResidual p G₀ hG₀ (MonoidHom.transfer φ) hquot_p
  obtain ⟨P₀, hP₀_map⟩ := hall_residual_inf_sylow p P₁ G₀ hG₀
  have hP₀_map_P : ((P₀ : Subgroup G₀).map G₀.subtype : Subgroup G) = P :=
    hP₀_map.trans hP.symm
  have hP₀_le_HG₀ : (P₀ : Subgroup G₀) ≤ HG₀ := by
    intro x hx
    change (x : G) ∈ H
    apply hP_le_H
    rw [← hP₀_map_P]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  let S₀ : Sylow p HG₀ := P₀.subtype hP₀_le_HG₀
  let K : Subgroup G := H₀ ⊔ Subgroup.closure
    {x : G | ∃ u : H, (u : G) ∈ P ∧ x = (dstar u : G)}
  have hK_le_H : K ≤ H := by
    refine sup_le hH₀_le_H ?_
    rw [Subgroup.closure_le]
    rintro x ⟨u, _hu, rfl⟩
    exact (dstar u).property
  have hpower_mem_K : ∀ u : G, u ∈ P → u ^ HG₀.index ∈ K := by
    intro u hu
    let uH : H := ⟨u, hP_le_H hu⟩
    let u₀ : HG₀ := eH.symm uH
    have huS : u₀ ∈ (S₀ : Subgroup HG₀) := by
      change (u₀ : G₀) ∈ (P₀ : Subgroup G₀)
      have hu_map : u ∈ ((P₀ : Subgroup G₀).map G₀.subtype : Subgroup G) := by
        rw [hP₀_map_P]
        exact hu
      rcases Subgroup.mem_map.mp hu_map with ⟨x, hx, hxu⟩
      have hxu₀ : x = (u₀ : G₀) := by
        exact Subtype.ext hxu
      rwa [← hxu₀]
    obtain ⟨defectTerms, hdefectTerms⟩ :=
      hall_lemma_14_4_3_transfer_diagonal_defect_formula φ
    have hformula := (hdefectTerms u₀).1
    let KH : Subgroup H := K.subgroupOf H
    let L : Subgroup (H ⧸ H₀.subgroupOf H) := KH.map π
    have hdefect_mem_L : ∀ y : HG₀, y ∈ defectTerms u₀ →
        hallDiagonalDefect (H := HG₀) φ y ∈ L := by
      intro y hy
      obtain ⟨v, hvS, hydef⟩ :=
        hall_lemma_14_4_4_defect_term_eq_sylow_defect p S₀ φ huS
          ((hdefectTerms u₀).2 y hy)
      have hvP : ((eH v : H) : G) ∈ P := by
        rw [← hP₀_map_P]
        refine Subgroup.mem_map.mpr ⟨(v : G₀), ?_, ?_⟩
        · exact hvS
        · rfl
      have hdK : ((dstar (eH v) : H) : G) ∈ K := by
        exact (le_sup_right : Subgroup.closure
          {x : G | ∃ w : H, (w : G) ∈ P ∧ x = (dstar w : G)} ≤ K)
          (Subgroup.subset_closure ⟨eH v, hvP, rfl⟩)
      have hdKH : dstar (eH v) ∈ KH := by
        change ((dstar (eH v) : H) : G) ∈ K
        exact hdK
      have hπdL : π (dstar (eH v)) ∈ L :=
        Subgroup.mem_map.mpr ⟨dstar (eH v), hdKH, rfl⟩
      have hdstarv : π (dstar (eH v)) =
          hallDiagonalDefect (H := HG₀) φ v := by
        simpa [π, φ, eH, MulEquiv.coe_toMonoidHom] using hdstar (eH v)
      rw [hydef, ← hdstarv]
      exact hπdL
    have hprod_mem_L : ∀ M : Multiset HG₀,
        (∀ y : HG₀, y ∈ M → hallDiagonalDefect (H := HG₀) φ y ∈ L) →
        (M.map (fun y => hallDiagonalDefect (H := HG₀) φ y)).prod ∈ L := by
      intro M hM
      induction M using Multiset.induction_on with
      | empty => simp
      | cons y M ih =>
          rw [Multiset.map_cons, Multiset.prod_cons]
          exact L.mul_mem (hM y (by simp))
            (ih (fun z hz => hM z (by simp [hz])))
    have hdefect_prod_mem :
        ((defectTerms u₀).map
          (fun y => hallDiagonalDefect (H := HG₀) φ y)).prod ∈ L :=
      hprod_mem_L (defectTerms u₀) hdefect_mem_L
    have htransfer_u : MonoidHom.transfer φ (u₀ : G₀) = 1 := by
      have hu := DFunLike.congr_fun htransfer_one (u₀ : G₀)
      simpa using hu
    have hφpow : φ u₀ ^ HG₀.index =
        ((defectTerms u₀).map
          (fun y => hallDiagonalDefect (H := HG₀) φ y)).prod⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hformula]
      exact htransfer_u
    have hφpow_mem : φ u₀ ^ HG₀.index ∈ L := by
      rw [hφpow]
      exact L.inv_mem hdefect_prod_mem
    have hπpow_mem : π (uH ^ HG₀.index) ∈ L := by
      rw [map_pow]
      simpa [φ, u₀] using hφpow_mem
    rcases Subgroup.mem_map.mp hπpow_mem with ⟨k, hkKH, hkπ⟩
    have hkK : ((k : H) : G) ∈ K := by
      exact hkKH
    have hdiv : uH ^ HG₀.index / k ∈ H₀.subgroupOf H :=
      QuotientGroup.eq_iff_div_mem.mp hkπ.symm
    have hdivK : ((uH ^ HG₀.index / k : H) : G) ∈ K :=
      (le_sup_left : H₀ ≤ K) hdiv
    have hmulK := K.mul_mem hdivK hkK
    simpa [uH] using hmulK
  have hindex_coprime : p.Coprime HG₀.index := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hp
    exact P₀.not_dvd_index (hp.trans (Subgroup.index_dvd_of_le hP₀_le_HG₀))
  intro u hu
  have hu_map : u ∈ ((P₀ : Subgroup G₀).map G₀.subtype : Subgroup G) := by
    rw [hP₀_map_P]
    exact hu
  rcases Subgroup.mem_map.mp hu_map with ⟨x, hx, hxu⟩
  let xP : P₀ := ⟨x, hx⟩
  let root : P₀ := (P₀.isPGroup'.powEquiv hindex_coprime).symm xP
  have hroot_pow : root ^ HG₀.index = xP := by
    rw [← IsPGroup.powEquiv_apply P₀.isPGroup' hindex_coprime root]
    exact Equiv.apply_symm_apply (P₀.isPGroup'.powEquiv hindex_coprime) xP
  let r : G := (((root : P₀) : G₀) : G)
  have hrP : r ∈ P := by
    rw [← hP₀_map_P]
    exact Subgroup.mem_map.mpr ⟨(root : G₀), root.property, rfl⟩
  have hrK := hpower_mem_K r hrP
  have hru : r ^ HG₀.index = u := by
    have hroot_ambient := congrArg (fun z : P₀ => (((z : P₀) : G₀) : G)) hroot_pow
    have hroot_ambient' : r ^ HG₀.index = ((x : G₀) : G) := by
      simpa [r, xP] using hroot_ambient
    exact hroot_ambient'.trans hxu
  rwa [hru] at hrK
private theorem hall_lemma_14_4_4_generation_core
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (H₁ G₀ H P H₀ : Subgroup G)
    (hG₀ : G₀ = hallPResidual p G)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hH₀ : H₀ = hallTransferModulus p H H₁)
    (hH_le_G₀ : H ≤ G₀) (hP_le_H : P ≤ H) (hH₀_le_H : H₀ ≤ H)
    [hH₀_normal : (H₀.subgroupOf H).Normal]
    (hcomm : commutator H ≤ H₀.subgroupOf H) :
    letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcomm
    letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
    ∀ dstar : H → H,
      (∀ u : H,
        QuotientGroup.mk' (H₀.subgroupOf H) (dstar u) =
          hallDiagonalDefect (G := G₀) (H := H.subgroupOf G₀)
            ((QuotientGroup.mk' (H₀.subgroupOf H)).comp
              (Subgroup.subgroupOfEquivOfLe hH_le_G₀).toMonoidHom)
            ((Subgroup.subgroupOfEquivOfLe hH_le_G₀).symm u)) →
      H ≤ H₀ ⊔ Subgroup.closure
        {x : G | ∃ u : H, (u : G) ∈ P ∧ x = (dstar u : G)} := by
  letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcomm
  letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
  intro dstar hdstar
  let HG₀ : Subgroup G₀ := H.subgroupOf G₀
  let eH : HG₀ ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G₀
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let φ : HG₀ →* H ⧸ H₀.subgroupOf H := π.comp eH.toMonoidHom
  let K : Subgroup G := H₀ ⊔ Subgroup.closure
    {x : G | ∃ u : H, (u : G) ∈ P ∧ x = (dstar u : G)}
  have hK_le_H : K ≤ H := by
    refine sup_le hH₀_le_H ?_
    rw [Subgroup.closure_le]
    rintro x ⟨u, _hu, rfl⟩
    exact (dstar u).property
  have hH₀_le_K : H₀ ≤ K := le_sup_left
  have hP_le_K : P ≤ K := by
    exact hall_lemma_14_4_4_sylow_le_defect_closure p P₁ H₁ G₀ H P H₀
      hG₀ hP hH₀ hH_le_G₀ hP_le_H hH₀_le_H hcomm dstar hdstar
  obtain ⟨P₀, hP₀_map⟩ := hall_residual_inf_sylow p P₁ G₀ hG₀
  have hP₀_map_P : ((P₀ : Subgroup G₀).map G₀.subtype : Subgroup G) = P :=
    hP₀_map.trans hP.symm
  have hP₀_le_HG₀ : (P₀ : Subgroup G₀) ≤ HG₀ := by
    intro x hx
    change (x : G) ∈ H
    apply hP_le_H
    rw [← hP₀_map_P]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  let S₀ : Sylow p HG₀ := P₀.subtype hP₀_le_HG₀
  have hres_le_H₀ : hallPResidual p H ≤ H₀.subgroupOf H := by
    intro x hx
    change (x : G) ∈ H₀
    rw [hH₀]
    exact (le_sup_right : (hallPResidual p H).map H.subtype ≤
      hallPPowerSubgroup p H ⊔ ⁅H, H₁⁆ ⊔ (hallPResidual p H).map H.subtype)
      (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hquot_p : IsPGroup p (H ⧸ H₀.subgroupOf H) :=
    hallPResidual_le_quotient_isPGroup p (H₀.subgroupOf H) hres_le_H₀
  have hφ_surj : Function.Surjective φ := by
    exact (QuotientGroup.mk'_surjective (H₀.subgroupOf H)).comp eH.surjective
  let SQ : Sylow p (H ⧸ H₀.subgroupOf H) := S₀.mapSurjective hφ_surj
  have hSQ_top : (SQ : Subgroup (H ⧸ H₀.subgroupOf H)) = ⊤ := by
    apply le_antisymm le_top
    exact (SQ.is_maximal' (hquot_p.to_subgroup ⊤) le_top).le
  intro h hh
  let hH : H := ⟨h, hh⟩
  have hπ_mem : π hH ∈ (S₀ : Subgroup HG₀).map φ := by
    change π hH ∈ (SQ : Subgroup (H ⧸ H₀.subgroupOf H))
    rw [hSQ_top]
    exact Subgroup.mem_top _
  rcases Subgroup.mem_map.mp hπ_mem with ⟨s, hs, hsπ⟩
  have hsP : ((eH s : H) : G) ∈ P := by
    rw [← hP₀_map_P]
    refine Subgroup.mem_map.mpr ⟨(s : G₀), ?_, ?_⟩
    · exact hs
    · rfl
  have hsK : ((eH s : H) : G) ∈ K := hP_le_K hsP
  have hquot_eq : π hH = π (eH s) := by
    simpa [φ] using hsπ.symm
  have hdiv : hH / eH s ∈ H₀.subgroupOf H :=
    QuotientGroup.eq_iff_div_mem.mp hquot_eq
  have hdivK : ((hH / eH s : H) : G) ∈ K := hH₀_le_K hdiv
  have hmulK := K.mul_mem hdivK hsK
  change h ∈ K
  simpa [hH] using hmulK
set_option maxRecDepth 2000 in
/-- Hall Lemma 14.4.4: `H` is generated by `H₀` and representatives of the
actual diagonal defects `d*(u)` for `u ∈ P`. -/
public theorem hall_lemma_14_4_4_generated_by_diagonal_defects
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (N₁ H₁ G₀ H P H₀ : Subgroup G)
    (hN₁ : N₁ = Subgroup.normalizer ((P₁ : Subgroup G) : Set G))
    (hN₁_le_H₁ : N₁ ≤ H₁)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hH₀ : H₀ = hallTransferModulus p H H₁) :
    hallDiagonalDefectGeneration p P₁ N₁ H₁ G₀ H P H₀
      hN₁ hN₁_le_H₁ hG₀ hH hP hH₀ := by
  simp only [hallDiagonalDefectGeneration]
  have hH_le_G₀ : H ≤ G₀ := by
    rw [hH]
    exact inf_le_left
  have hH_le_H₁ : H ≤ H₁ := by
    rw [hH]
    exact inf_le_right
  have hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁ :=
    Subgroup.le_normalizer.trans (hN₁ ▸ hN₁_le_H₁)
  have hP_le_H : P ≤ H := by
    rw [hP, hH]
    exact inf_le_inf le_rfl hP₁_le_H₁
  have hH₀_le_H : H₀ ≤ H := by
    rw [hH₀]
    exact hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH
  have hH₀_normal : (H₀.subgroupOf H).Normal := by
    subst H₀
    exact hallTransferModulus_subgroupOf_normal p H H₁ hH_le_H₁
      (hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH)
  letI : (H₀.subgroupOf H).Normal := hH₀_normal
  have hcomm : commutator H ≤ H₀.subgroupOf H := by
    intro x hx
    have hxmap : H.subtype x ∈ (commutator H).map H.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hxmap
    have hC : ⁅H, H₁⁆ ≤ H₀ := by
      rw [hH₀]
      exact le_sup_right.trans le_sup_left
    exact hC ((Subgroup.commutator_mono le_rfl hH_le_H₁) hxmap)
  letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcomm
  letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
  let HG₀ : Subgroup G₀ := H.subgroupOf G₀
  let eH : HG₀ ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G₀
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let φ : HG₀ →* H ⧸ H₀.subgroupOf H := π.comp eH.toMonoidHom
  let dstar : H → H := fun u =>
    (hallDiagonalDefect (G := G₀) (H := HG₀) φ (eH.symm u)).out
  have hdstar : ∀ u : H,
      π (dstar u) = hallDiagonalDefect (G := G₀) (H := HG₀) φ (eH.symm u) := by
    intro u
    simp [π, dstar]
  refine ⟨dstar, hdstar, ?_⟩
  exact hall_lemma_14_4_4_generation_core p P₁ H₁ G₀ H P H₀
    hG₀ hP hH₀ hH_le_G₀ hP_le_H hH₀_le_H hcomm dstar hdstar

end External
end CFSG.BenderSuzuki








