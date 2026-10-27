module

public import CFSG.Quasithin.Background.S1567Cx
public import CFSG.Quasithin.Background.S1567ASymm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

section Q

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

omit [Finite G] in
theorem subgroupOf_pCoreOf_eq (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.Open.pCore 2 ↥L := by
  unfold pCoreOf Subgroup.subgroupOf
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem commJ_data (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) :
    thompsonJ (TE153 T E) ≤ TE153 T E ∧
    TE153 T E ≤ Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) ∧
    Y153 Mc M ≤ Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) ∧
    (∀ P : Subgroup G, thompsonJ (TE153 T E) ≤ P → P ≤ TE153 T E →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (thompsonJ (TE153 T E) : Set G)) ∧
    Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) ≤ M ∧
    thompsonJ (TE153 T E) = thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  obtain ⟨hNJM, hYTJ⟩ := C1Pack153.normalizer_thompsonJ_TE_le_M h113 k.c k.L k.r66
  have hRTE : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ TE153 T E := C1Pack153.R_le_TE k.L
  have hJ : thompsonJ (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf ((thompsonJ_le_self _).trans inf_le_left)
      (C1Pack153.thompsonJ_TE_le_centralizer k.c k.L k.r66)
  refine ⟨thompsonJ_le_self _, B6.le_normalizer_thompsonJ _, le_sup_left.trans hYTJ,
    fun P hJP hPTE => ?_, hNJM, thompsonJ_eq_of_le hJ hRTE⟩
  exact (normalizer_le_normalizer_thompsonJ P).trans
    (le_of_eq (by rw [← thompsonJ_eq_of_le hJP hPTE]))

theorem XE_comm_153 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    XE153 E = ⁅XE153 E, thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G))⁆ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := commJ_data h113 k
  rw [← h6]
  exact XE_eq_commutator_of k hidx h1 h2 h3 h4 h5

theorem not_CE_le_normalizer_SE (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    ¬ Subgroup.centralizer (E : Set G) ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hN
  obtain ⟨h1, h2', h3, h4, h5, h6⟩ := commJ_data h113 k
  have hnot := not_commutator_le_pCore_XE k hidx h1 h2' h3 h4 h5
  apply hnot
  have hJSE : thompsonJ (TE153 T E) ≤ T ⊓ Subgroup.centralizer (E : Set G) := by
    refine le_inf (h1.trans inf_le_left) ?_
    have hJR : thompsonJ (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      le_inf ((thompsonJ_le_self _).trans inf_le_left)
        (C1Pack153.thompsonJ_TE_le_centralizer k.c k.L k.r66)
    exact fun x hx => Subgroup.centralizer_le k.L.le_V (hJR hx).2
  have hSXE : T ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (XE153 E : Set G) :=
    SE_le_normalizer_XE E
  have hXSE : XE153 E ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
    (oTwoUpper_le _).trans hN
  have hc1 : ⁅XE153 E, T ⊓ Subgroup.centralizer (E : Set G)⁆ ≤ XE153 E :=
    commutator_le_of_le_normalizer hSXE
  have hc2 : ⁅XE153 E, T ⊓ Subgroup.centralizer (E : Set G)⁆ ≤ T ⊓ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer hXSE
  have hmono : ⁅XE153 E, thompsonJ (TE153 T E)⁆ ≤ ⁅XE153 E, T ⊓ Subgroup.centralizer (E : Set G)⁆ :=
    Subgroup.commutator_mono le_rfl hJSE
  refine hmono.trans ((le_inf hc1 hc2).trans ?_)
  rw [inf_comm]
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (isSylowTwoOf_SE k).2.1.to_inf_left
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXSE hx, Subgroup.le_normalizer hx⟩

theorem nonempty_quot_CE (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    Nonempty (OTwoQuot (Subgroup.centralizer (E : Set G)) ≃* Equiv.Perm (Fin 3)) :=
  nonempty_quotient_pCore_of_relIndex_eq_three' (isSylowTwoOf_SE k) (relIndex_SE_CE k hidx)
    (not_CE_le_normalizer_SE h113 k hidx)

theorem nonempty_quot_GE_CE (k : Ctx67 G T Mc M V₁ V₂ E t) :
    Nonempty (↥(Subgroup.normalizer (E : Set G)) ⧸
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)) ≃*
        Equiv.Perm (Fin 3)) := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hHGE : YE153 Mc M E ⊔ TE153 T E ≤ Subgroup.normalizer (E : Set G) :=
    (YE_TE_le_ME k.c).trans inf_le_right
  have hnormal : ((Subgroup.centralizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr (normalizer_le_normalizer_CE E)
  let f : ↥(YE153 Mc M E ⊔ TE153 T E) →*
      ↥(Subgroup.normalizer (E : Set G)) ⧸
        (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hHGE)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hz : (z : G) ∈ ((YE153 Mc M E ⊔ TE153 T E : Subgroup G) : Set G) *
        (Subgroup.centralizer (E : Set G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (hHGE.trans (normalizer_le_normalizer_CE E)), ← k.r66.GE_eq]
      exact z.2
    obtain ⟨h, hh, c, hc, hhc⟩ := Set.mem_mul.mp hz
    refine ⟨⟨h, hh⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hHGE ⟨h, hh⟩) : _ ⧸ _) = QuotientGroup.mk z
    rw [QuotientGroup.eq]
    show (h⁻¹ * (z : G)) ∈ Subgroup.centralizer (E : Set G)
    have : h⁻¹ * (z : G) = c := by rw [← hhc]; group
    rw [this]; exact hc
  have hker : f.ker = CFSG.Open.pCore 2 ↥(YE153 Mc M E ⊔ TE153 T E) := by
    rw [← subgroupOf_pCoreOf_eq, k.r66.pCore_YETE]
    ext x
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  obtain ⟨e⟩ := k.r66.quot_S3
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans e)⟩

theorem quot_S3S3_153 (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    Nonempty (OTwoQuot (Subgroup.normalizer (E : Set G)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hnormal : ((Subgroup.centralizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr (normalizer_le_normalizer_CE E)
  obtain ⟨e⟩ := nonempty_quot_CE h113 k hidx
  let ψ : ↥(Subgroup.centralizer (E : Set G)) ≃*
      ↥((Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G))) :=
    (Subgroup.subgroupOfEquivOfLe hCN).symm
  have hC : Nonempty (↥((Subgroup.centralizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G))) ⧸
      CFSG.Open.pCore 2 ↥((Subgroup.centralizer (E : Set G)).subgroupOf
        (Subgroup.normalizer (E : Set G))) ≃* Equiv.Perm (Fin 3)) := by
    refine gold_isoS3_of_surjective_kernel ψ.toMonoidHom ψ.surjective ?_ e
    rw [(MonoidHom.ker_eq_bot_iff _).mpr ψ.injective]
    exact IsPGroup.of_bot
  exact oTwoQuot_equiv_S3S3 _ (nonempty_quot_GE_CE k) hC

end Q

end S1567

end CFSG.Quasithin
