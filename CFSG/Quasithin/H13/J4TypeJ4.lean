module

public import CFSG.Quasithin.H13.J4TypeW
public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.H13.J4Centralizer

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem center_CmodZ
    : Subgroup.center (CQ ⧸ ZC) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : m22EquivC.symm x ∈ Subgroup.center M22 := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    apply m22EquivC.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx _
  rw [center_M22, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  have := congrArg m22EquivC h1
  rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem center_CQ_eq
    : (Subgroup.center CQ).map CQ.subtype = Zq := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    have hmk : (QuotientGroup.mk c : CQ ⧸ ZC) ∈ Subgroup.center (CQ ⧸ ZC) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H d =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hc d]
    rw [center_CmodZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_ZC_iff] at hmk
    exact hmk
  · intro z hz
    exact ⟨⟨z, Zq_le_CQ hz⟩, ZC_le_center (mem_ZC_iff.2 hz), rfl⟩

theorem inverts_Zq
    {g : QW} (hg : g ∉ CQ) {x : QW} (hx : x ∈ Zq) : g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow, not_mem_CQ_iff.1 hg, inv_zpow]

@[expose] def psiQ
    : CQ →* M22 := m22EquivC.symm.toMonoidHom.comp (QuotientGroup.mk' ZC)

theorem psiQ_surjective
    : Function.Surjective psiQ :=
  m22EquivC.symm.surjective.comp (QuotientGroup.mk'_surjective ZC)

theorem ker_psiQ
    : psiQ.ker = ZC := by
  ext c
  rw [MonoidHom.mem_ker]
  show m22EquivC.symm (QuotientGroup.mk c) = 1 ↔ c ∈ ZC
  rw [← QuotientGroup.eq_one_iff, ← map_one m22EquivC.symm]
  exact m22EquivC.symm.injective.eq_iff

theorem qToAut_psiQ
    (g : QW) (d : CQ) (h : g * d * g⁻¹ ∈ CQ) :
    qToAut g (psiQ d) = psiQ ⟨g * d * g⁻¹, h⟩ := by
  show m22EquivC.symm (conjHom g (m22EquivC (m22EquivC.symm (QuotientGroup.mk d)))) =
    m22EquivC.symm (QuotientGroup.mk ⟨g * d * g⁻¹, h⟩)
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem isAutTripleM22_QW
    : IsAutTripleM22 QW :=
  ⟨Zq, Zq_normal, card_Zq, index_CQ, ⟨commutator_CQ⟩, center_CQ_eq,
    fun _ hg _ hx => inverts_Zq hg hx, psiQ, qToAut, psiQ_surjective, ker_psiQ, qToAut_psiQ,
    qToAut_surjective, ker_qToAut, map_qToAut_CQ⟩

@[expose] def corePEquiv
    : CFSG.pCore 2 W ≃* P :=
  (MulEquiv.subgroupCongr pCore_W).trans (Subgroup.subgroupOfEquivOfLe P_le_W)

theorem coe_corePEquiv
    (q : CFSG.pCore 2 W) :
    (corePEquiv q : GL (Fin 112) (ZMod 2)) = ((q : W) : GL (Fin 112) (ZMod 2)) := by
  simp [corePEquiv]

theorem center_pCore_W
    :
    (Subgroup.center (CFSG.pCore 2 W)).map (CFSG.pCore 2 W).subtype =
      Subgroup.zpowers (⟨t, t_mem_W⟩ : W) := by
  have hZ := secondLocal_extraspecial.1
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    have h1 : corePEquiv q ∈ Subgroup.center P := by
      rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hq
      rw [Subgroup.mem_center_iff]
      intro g
      apply corePEquiv.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
      exact hq _
    have h2 : ((corePEquiv q : P) : GL (Fin 112) (ZMod 2)) ∈ Subgroup.zpowers t := by
      rw [← hZ]
      have := Subgroup.mem_map_of_mem P.subtype h1
      rwa [Subgroup.coe_subtype] at this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
    refine Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_zpow, Subgroup.coe_subtype, ← coe_corePEquiv, ← hk]
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have ht : (⟨t, t_mem_W⟩ : W) ∈ CFSG.pCore 2 W := by
      rw [pCore_W]
      exact t_mem_P
    refine ⟨⟨_, ht⟩ ^ k, ?_, by rw [map_zpow, Subgroup.coe_subtype]⟩
    refine Subgroup.zpow_mem _ ?_ k
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    have hg : ((g : W) : GL (Fin 112) (ZMod 2)) ∈ W := (g : W).2
    exact (Subgroup.mem_centralizer_iff.1 (W_le_centralizer hg) t (Set.mem_singleton t)).symm

theorem isTypeJ4Core_W
    : IsTypeJ4Core W ⟨t, t_mem_W⟩ := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_P
  refine ⟨generalizedFitting_W.symm, isExtraspecialPGroup_of_mulEquiv' (X := P)
    (Y := CFSG.pCore 2 W) corePEquiv.symm isExtraspecialPGroup_P,
    by rw [Nat.card_congr corePEquiv.toEquiv, card_P], center_pCore_W, ⟨corePEquiv.trans φ⟩⟩

@[expose] def wCentEquiv
    : W ≃* Subgroup.centralizer ({tJ} : Set J) :=
  (Subgroup.subgroupOfEquivOfLe W_le_J).symm.trans (MulEquiv.subgroupCongr centralizer_tJ_eq.symm)

theorem coe_wCentEquiv
    (w : W) :
    ((wCentEquiv w : J) : GL (Fin 112) (ZMod 2)) = (w : GL (Fin 112) (ZMod 2)) := by
  simp [wCentEquiv]

theorem wCentEquiv_t
    : wCentEquiv ⟨t, t_mem_W⟩ = selfC tJ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_wCentEquiv]
  rfl

theorem finite_W
    : Finite W := Nat.finite_of_card_ne_zero (by rw [card_W]; norm_num)

theorem finite_J'
    : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)

theorem isTypeJ4Core_C
    : IsTypeJ4Core (Subgroup.centralizer ({tJ} : Set J)) (selfC tJ) := by
  have := finite_W
  exact IsTypeJ4Core.of_mulEquiv (X := W) (Y := Subgroup.centralizer ({tJ} : Set J))
    isTypeJ4Core_W wCentEquiv wCentEquiv_t

theorem isAutTripleM22_C
    : IsAutTripleM22 (Subgroup.centralizer ({tJ} : Set J) ⧸
    CFSG.pCore 2 (Subgroup.centralizer ({tJ} : Set J))) := by
  have h1 := IsAutTripleM22.of_mulEquiv (X := QW) (Y := W ⧸ CFSG.pCore 2 W) isAutTripleM22_QW
    (QuotientGroup.quotientMulEquivOfEq pCore_W.symm)
  exact IsAutTripleM22.of_mulEquiv (X := W ⧸ CFSG.pCore 2 W)
    (Y := Subgroup.centralizer ({tJ} : Set J) ⧸ CFSG.pCore 2 (Subgroup.centralizer ({tJ} : Set J)))
    h1 (pCoreQuotEquiv (X := W) (Y := Subgroup.centralizer ({tJ} : Set J)) wCentEquiv)

theorem card_C
    : Nat.card (Subgroup.centralizer ({tJ} : Set J)) = 21799895040 := by
  rw [← Nat.card_congr wCentEquiv.toEquiv, card_W]

theorem exists_sylow_le_C
    :
    ∃ S : Sylow 2 J, (S : Subgroup J) ≤ Subgroup.centralizer ({tJ} : Set J) := by
  have := finite_J'
  have hF : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (Subgroup.centralizer ({tJ} : Set J))))
  have hfC : (21799895040 : ℕ).factorization 2 = 21 := by
    rw [show (21799895040 : ℕ) = 2 ^ 21 * 10395 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide), add_zero]
  have hcard : Nat.card ((T : Subgroup _).map (Subgroup.centralizer ({tJ} : Set J)).subtype) =
      2 ^ (Nat.card J).factorization 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Sylow.card_eq_multiplicity,
      card_C, hfC, CFSG.Sporadic.J4Schreier.factorization_card_J]
  refine ⟨Sylow.ofCard _ hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem hWeak_mem_J : hWeak ∈ J := by
  unfold hWeak
  have hg : gWeak ∈ J := wordProd_mem J baseGL_mem _
  exact J.mul_mem (J.pow_mem (J.mul_mem t_mem_J (J.mul_mem (J.mul_mem (J.inv_mem hg)
    (W_le_J (P_le_W (hypElt_mem_P 0)))) hg)) _) (J.inv_mem hg)

theorem not_weaklyClosed_tJ
    :
    ∃ g : J, g⁻¹ * tJ * g ∈ (CFSG.pCore 2 (Subgroup.centralizer ({tJ} : Set J))).map
      (Subgroup.centralizer ({tJ} : Set J)).subtype ∧ g⁻¹ * tJ * g ≠ tJ := by
  obtain ⟨h1, h2⟩ := weakChecks_spec
  have ha0 : hypElt 0 ∈ W := P_le_W (hypElt_mem_P 0)
  refine ⟨⟨hWeak, hWeak_mem_J⟩, ?_, ?_⟩
  · have hq : (⟨hypElt 0, ha0⟩ : W) ∈ CFSG.pCore 2 W := by
      rw [pCore_W]
      exact hypElt_mem_P 0
    obtain ⟨y, hy⟩ : ∃ y, wCentEquiv ⟨_, ha0⟩ = y := ⟨_, rfl⟩
    refine ⟨y, ?_, ?_⟩
    · exact @mem_pCore_of_mulEquiv W (Subgroup.centralizer ({tJ} : Set J)) W.toGroup
        (Subgroup.centralizer ({tJ} : Set J)).toGroup _ hq wCentEquiv _ hy
    · apply Subtype.ext
      rw [Subgroup.coe_subtype, ← hy, coe_wCentEquiv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact h1.symm
  · intro e
    apply h2
    have := congrArg Subtype.val e
    rw [← h1]
    exact this

theorem isTypeJ4Centralizer_tJ
    : IsTypeJ4Centralizer J tJ :=
  ⟨card_C, exists_sylow_le_C, isTypeJ4Core_C, isAutTripleM22_C, not_weaklyClosed_tJ⟩

end CFSG.Quasithin.H13.J4
