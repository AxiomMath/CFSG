module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS12
public import CFSG.Quasithin.Vol2.Ch10SecEBlockA5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem exists_alpha {L : Subgroup G} (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5)) :
    ∃ α : ↥L →* alternatingGroup (Fin 5), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

variable [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem card_fsuUL_case2 (h2 : Ch10.Case10_1_1Two T L I) : Nat.card ↥(fsuUL T L I) = 16 := by
  obtain ⟨-, hcU, hA⟩ := h2
  rw [SecE.card_of_alternatingNatural_five hA, Nat.card_congr (L246.coreEquiv 5).toEquiv]
  exact card_delta5

theorem not_le_centralizer_of_three (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {q : G} (hqL : q ∈ L) (hq3 : orderOf q = 3) :
    ¬ fsuUL T L I ≤ Subgroup.centralizer ({q} : Set G) := by
  intro h
  obtain ⟨α, hαs, hαk⟩ := exists_alpha h2.1.some
  have hLp := perfect_of_mem_cComp (SecE.mem_cComp_L0T hyp)
  have hLV : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := SecC.le_normalizer_fsuUL T L I
  have hbotN : ∀ g : G, g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g =>
    (Subgroup.normalizer_eq_top_iff (H := (⊥ : Subgroup G)).mpr inferInstance) ▸
      Subgroup.mem_top g
  have hqt : q ∈ trivOn (fsuUL T L I) ⊥ := by
    refine ⟨hLV hqL, hbotN q, fun y hy => ?_⟩
    have hyq := Subgroup.mem_centralizer_singleton_iff.mp (h hy)
    rw [Subgroup.mem_bot, ← hyq]
    group
  have hLN : L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g _ => hbotN g
  have hLt := le_of_normal_of_not_le hLp hαs hαk (le_normalizer_trivOn hLV hLN) hqt hqL
    (alpha_ne_one_of_three hαk hqL hq3)
  have hbot : fsuUL T L I ≤ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) := by
    refine le_inf le_rfl fun v hv => Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have h1 := Subgroup.mem_bot.mp ((hLt hl).2.2 v hv)
    calc l * v = l * v * l⁻¹ * v⁻¹ * (v * l) := by group
      _ = v * l := by rw [h1, one_mul]
  rw [SecF.fsuUL_inf_centralizer_eq_bot h2] at hbot
  have h1 : Nat.card ↥(fsuUL T L I) = 1 := by
    rw [le_bot_iff.mp hbot]
    exact Subgroup.card_bot
  rw [card_fsuUL_case2 h2] at h1
  omega

theorem blockU_eq_fsuUL_of_relIndex (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {q : G} (hqL : q ∈ L) (hq3 : orderOf q = 3)
    (hc16 : (Subgroup.centralizer ({q} : Set G)).relIndex (T ⊓ L) ≤ 16) :
    blockU L = fsuUL T L I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3' : q ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q
  obtain ⟨α, hαs, hαk⟩ := exists_alpha h2.1.some
  have hLc := SecE.mem_cComp_L0T hyp
  have hLp := perfect_of_mem_cComp hLc
  have hT : IsSylowTwoOf T (fsuL0 T L ⊔ T) :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  have hS : IsSylowTwoOf (T ⊓ L) L := A312.isSylowTwoOf_inf_of_subnormal
    (subnormal_of_mem_cComp hLc) hT
  have hOT : pCoreOf 2 L ≤ T ⊓ L :=
    le_inf ((A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hLc)).trans
      (pCoreOf_two_le_of_isSylowTwoOf hT)) (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hCO := inf_centralizer_le_pCoreOf hαk hS.2.1 inf_le_right hqL hq3
  have hN1 : T ⊓ L ⊓ Subgroup.centralizer ({q} : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 L : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hx.1.2
  have hmul1 := relIndex_centralizer_eq_mul hOT hN1
  rw [sup_eq_left.mpr hCO, relIndex_pCoreOf_eq_four hαs hαk hS hOT] at hmul1
  have hVO : fsuUL T L I ≤ pCoreOf 2 L := SecE.fsuUL_le_pCoreOf_L hyp
  have hLV : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := SecC.le_normalizer_fsuUL T L I
  have hN2 : pCoreOf 2 L ⊓ Subgroup.centralizer ({q} : Set G) ≤
      Subgroup.normalizer (fsuUL T L I : Set G) := fun x hx =>
    hLV (CFSG.LieType.BorelTits.pCoreOf_le 2 L hx.1)
  have hmul2 := relIndex_centralizer_eq_mul hVO hN2
  obtain ⟨he, hcU, hA⟩ := h2
  have hV16 := card_fsuUL_case2 ⟨he, hcU, hA⟩
  have hαq := alpha_ne_one_of_three hαk hqL hq3
  have hnot := not_le_centralizer_of_three hyp ⟨he, hcU, hA⟩ hqL hq3
  have h4V := four_le_relIndex_of_card hV16 hq3' (hLV hqL) hnot
  have hm0 : (fsuUL T L I ⊔ pCoreOf 2 L ⊓ Subgroup.centralizer ({q} : Set G)).relIndex
      (pCoreOf 2 L) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm1 : (fsuUL T L I ⊔ pCoreOf 2 L ⊓ Subgroup.centralizer ({q} : Set G)).relIndex
      (pCoreOf 2 L) = 1 := by
    rw [hmul2] at hmul1
    have h1 := Nat.mul_le_mul_right
      ((fsuUL T L I ⊔ pCoreOf 2 L ⊓ Subgroup.centralizer ({q} : Set G)).relIndex
        (pCoreOf 2 L)) h4V
    rw [hmul1] at hc16
    generalize (Subgroup.centralizer ({q} : Set G)).relIndex (fsuUL T L I) *
      (fsuUL T L I ⊔ pCoreOf 2 L ⊓ Subgroup.centralizer ({q} : Set G)).relIndex
        (pCoreOf 2 L) = k at h1 hc16
    omega
  have hle := Subgroup.relIndex_eq_one.mp hm1
  have hqt : q ∈ trivOn (pCoreOf 2 L) (fsuUL T L I) := by
    refine ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hqL, hLV hqL, fun y hy => ?_⟩
    have hy' : y ∈ ((fsuUL T L I ⊔ pCoreOf 2 L ⊓ Subgroup.centralizer ({q} : Set G) :
        Subgroup G) : Set G) := hle hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN2] at hy'
    obtain ⟨v, hv, c, hc, rfl⟩ := Set.mem_mul.mp hy'
    have hcq : c * q⁻¹ = q⁻¹ * c :=
      ((Commute.inv_right (Subgroup.mem_centralizer_singleton_iff.mp hc.2 : Commute c q))).eq
    have e1 : q * (v * c) * q⁻¹ * (v * c)⁻¹ = q * v * (c * q⁻¹) * c⁻¹ * v⁻¹ := by group
    rw [e1, hcq]
    have e2 : q * v * (q⁻¹ * c) * c⁻¹ * v⁻¹ = q * v * q⁻¹ * v⁻¹ := by group
    rw [e2]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hLV hqL) v).mp hv)
      (Subgroup.inv_mem _ hv)
  have hLt := le_of_normal_of_not_le hLp hαs hαk
    (le_normalizer_trivOn (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hLV) hqt hqL hαq
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.mpr fun y hy l hl => ?_
    have h1 := (hLt hl).2.2 y hy
    have e : ⁅y, l⁆ = (l * y * l⁻¹ * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  · calc fsuUL T L I = ⁅fsuUL T L I, L⁆ := (SecC.commutator_fsuUL_eq hyp).symm
      _ ≤ blockU L := Subgroup.commutator_mono hVO le_rfl

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
