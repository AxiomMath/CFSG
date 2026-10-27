module

public import CFSG.RankThree.GF2n.Parrott.QuotientV
public import CFSG.GroupTheory.FixedPointQuotientCard

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem J_subgroupOf_eq_pCore (z : G) :
    (J z).subgroupOf (H z) = pCore 2 (H z) := by
  show (J z).comap (H z).subtype = pCore 2 (H z)
  rw [J, inSubgroup]
  exact Subgroup.comap_map_eq_self_of_injective (H z).subtype_injective _

instance J_subgroupOf_normal (z : G) :
    ((J z).subgroupOf (H z)).Normal := by
  rw [J_subgroupOf_eq_pCore]
  infer_instance

@[expose] noncomputable def conjJ (z : G) : H z →* MulAut ((J z).subgroupOf (H z)) :=
  MulAut.conjNormal

@[expose] noncomputable def conjJ' (z : G) : H z →* MulAut (J z) :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z)))).toMonoidHom.comp
    (conjJ z)

theorem conjJ'_apply_coe (g : H z) (x : J z) :
    ((conjJ' z g x : J z) : G) = (g : G) * (x : G) * (g : G)⁻¹ := by
  simp [conjJ', conjJ, MulAut.congr, MulEquiv.trans_apply,
    MulAut.conjNormal_apply, Subgroup.subgroupOfEquivOfLe]

@[expose] noncomputable def centerQuotientAutHom (J : Type*) [Group J] :
    MulAut J →* MulAut (J ⧸ Subgroup.center J) where
  toFun := quotientAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) x
    rw [quotientAut_mk]
    simp
  map_mul' := by
    intro α β
    apply MulEquiv.ext
    intro x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) x
    rw [quotientAut_mk]
    change QuotientGroup.mk' (Subgroup.center J) ((α * β) j) =
      quotientAut α (quotientAut β (QuotientGroup.mk' (Subgroup.center J) j))
    rw [quotientAut_mk, quotientAut_mk]
    simp

private lemma quotientMulEquivOfEq_mk' {X : Type*} [Group X] {M N : Subgroup X}
    [M.Normal] [N.Normal] (h : M = N) (x : X) :
    (QuotientGroup.quotientMulEquivOfEq h) (QuotientGroup.mk' M x) =
      QuotientGroup.mk' N x := by
  change (QuotientGroup.quotientMulEquivOfEq h) (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x

private lemma quotientMulEquivOfEq_symm_mk' {X : Type*} [Group X] {M N : Subgroup X}
    [M.Normal] [N.Normal] (h : M = N) (x : X) :
    (QuotientGroup.quotientMulEquivOfEq h).symm (QuotientGroup.mk' N x) =
      QuotientGroup.mk' M x := by
  change (QuotientGroup.quotientMulEquivOfEq h).symm (QuotientGroup.mk x) =
    QuotientGroup.mk x
  conv_lhs => rw [← QuotientGroup.quotientMulEquivOfEq_mk h x]
  exact (QuotientGroup.quotientMulEquivOfEq h).symm_apply_apply (QuotientGroup.mk x)

@[expose] noncomputable def conjV (_h : Tim79a.ParrottHyp z) : H z →* MulAut (QuotientV.V z) :=
  (MulAut.congr (QuotientGroup.quotientMulEquivOfEq
    (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm)).toMonoidHom.comp
    ((centerQuotientAutHom (J z)).comp (conjJ' z))

theorem conjV_mk (h : Tim79a.ParrottHyp z) (g : H z) (x : J z) :
    conjV h g (QuotientV.pi z x) = QuotientV.pi z (conjJ' z g x) := by
  rw [conjV, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change (MulAut.congr (QuotientGroup.quotientMulEquivOfEq
      (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm)
    ((centerQuotientAutHom (J z)) ((conjJ' z) g))) (QuotientV.pi z x) = _
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply]
  change QuotientGroup.quotientMulEquivOfEq
      (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm
      (quotientAut ((conjJ' z) g)
        ((QuotientGroup.quotientMulEquivOfEq
          (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm).symm
          (QuotientGroup.mk' ((centerIn (J z)).subgroupOf (J z)) x))) =
    QuotientGroup.mk' ((centerIn (J z)).subgroupOf (J z)) (((conjJ' z) g) x)
  rw [quotientMulEquivOfEq_symm_mk']
  change QuotientGroup.quotientMulEquivOfEq
      (QuotientV.centerIn_subgroupOf_eq_center (z := z)).symm
      (quotientAut ((conjJ' z) g)
        (QuotientGroup.mk' (Subgroup.center (J z)) x)) =
    QuotientGroup.mk' ((centerIn (J z)).subgroupOf (J z)) (((conjJ' z) g) x)
  rw [quotientAut_mk, quotientMulEquivOfEq_mk']

theorem commutator_mem_centerIn (h : Tim79a.ParrottHyp z) (a b : J z) :
    ⁅(a : G), (b : G)⁆ ∈ centerIn (J z) := by
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  have hmem : ⁅(a : G), (b : G)⁆ ∈ ⁅J z, J z⁆ :=
    Subgroup.commutator_mem_commutator a.2 b.2
  rw [hJcomm] at hmem
  exact (Subgroup.zpowers_le_of_mem (H := centerIn (J z))
    ⟨z_mem_J h, z_centralizes_J h⟩) hmem

theorem conjJ'_mul_inv_mem_centerIn (h : Tim79a.ParrottHyp z) {g : H z}
    (hg : (g : G) ∈ J z) (x : J z) :
    ((conjJ' z g x : J z) : G) * (x : G)⁻¹ ∈ centerIn (J z) := by
  have hcomm := commutator_mem_centerIn h (⟨(g : G), hg⟩ : J z) x
  simpa [conjJ'_apply_coe, commutatorElement_def] using hcomm

theorem conjV_apply_pi_eq (h : Tim79a.ParrottHyp z) {g : H z}
    (hg : (g : G) ∈ J z) (x : J z) :
    conjV h g (QuotientV.pi z x) = QuotientV.pi z x := by
  rw [conjV_mk]
  change (QuotientGroup.mk (conjJ' z g x) :
      J z ⧸ (centerIn (J z)).subgroupOf (J z)) = QuotientGroup.mk x
  rw [QuotientGroup.eq_iff_div_mem]
  rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
  exact conjJ'_mul_inv_mem_centerIn h hg x

theorem J_le_ker_conjV (h : Tim79a.ParrottHyp z) :
    (J z).subgroupOf (H z) ≤ (conjV h).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  exact conjV_apply_pi_eq h (Subgroup.mem_subgroupOf.mp hg) x

@[expose] noncomputable def actionA (h : Tim79a.ParrottHyp z) :
    (↥(H z) ⧸ (J z).subgroupOf (H z)) →* MulAut (QuotientV.V z) :=
  QuotientGroup.lift _ (conjV h) (J_le_ker_conjV h)

@[simp] theorem actionA_mk (h : Tim79a.ParrottHyp z) (g : H z) :
    actionA h (QuotientGroup.mk' ((J z).subgroupOf (H z)) g) = conjV h g :=
  QuotientGroup.lift_mk' _ _ g

end CFSG.RankThree.GF2n.Parrott
