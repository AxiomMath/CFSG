module

public import CFSG.Quasithin.Vol2.Ch10SecQ4C1
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K T : Subgroup G}

omit [Finite G] in
theorem map_center_eq_inf (K : Subgroup G) :
    (Subgroup.center ↥K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set G) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.mp hk ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxK, hxc⟩
    refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxc y y.2

omit [Finite G] in
theorem card_center_eq (K : Subgroup G) :
    Nat.card (Subgroup.center ↥K) = Nat.card ↥(K ⊓ Subgroup.centralizer (K : Set G)) := by
  rw [← map_center_eq_inf, Subgroup.card_map_of_injective K.subtype_injective]

omit [Finite G] in
theorem inf_centralizer_le_blockQ (hK : IsShort2 K) :
    K ⊓ Subgroup.centralizer (K : Set G) ≤ blockQ K := by
  rintro x ⟨hxK, hxc⟩
  refine hK.2.1 ⟨hxK, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hxc q (CFSG.LieType.BorelTits.pCoreOf_le 2 K hq)

theorem blockZ_eq_bot_of_c113 (h113 : ASInputs.AS_C_1_13) (hT : IsSylowTwoOf T (K ⊔ T))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hK : IsShort2 K) (h5 : IsAltType K 5) :
    blockZ K = ⊥ := by
  obtain ⟨hO, hUC, -⟩ := (h113 G K T hT hTK hK).2.1 5 (Or.inr rfl) h5
  have hUT : blockU K ≤ T := by
    have h1 : blockU K ≤ pCoreOf 2 (K ⊔ T) := hO ▸ le_sup_left
    exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT)
  rw [eq_bot_iff, ← hUC]
  rintro x ⟨hxU, hxc⟩
  exact ⟨hxU, hUT hxU, hxc⟩

omit [Finite G] in
theorem mk_mem_center_of_mem_blockQ [hN : ((blockU K).subgroupOf K).Normal]
    {q : ↥K} (hq : (q : G) ∈ blockQ K) :
    (QuotientGroup.mk q : ↥K ⧸ (blockU K).subgroupOf K) ∈ Subgroup.center _ := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hmem : ⁅(q : G)⁻¹, (k : G)⁻¹⁆ ∈ blockU K :=
    Subgroup.commutator_mem_commutator ((blockQ K).inv_mem hq) (K.inv_mem k.2)
  rw [commutatorElement_def, inv_inv, inv_inv] at hmem
  simpa [mul_assoc] using hmem

theorem card_center_sl2_five :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv,
    show max (Fintype.card (Fin 2)) 1 = 2 by simp]
  exact (IsPrimitiveRoot.neg_one 5 (by norm_num)).card_rootsOfUnity

omit [Finite G] in
theorem blockQ_le_blockU_of_center [((blockU K).subgroupOf K).Normal]
    (hc : Subgroup.center (↥K ⧸ (blockU K).subgroupOf K) = ⊥) : blockQ K ≤ blockU K := by
  intro x hx
  have hxK : x ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hx
  have h := mk_mem_center_of_mem_blockQ (q := ⟨x, hxK⟩) hx
  rw [hc, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  exact h

theorem blockQ_eq_sup_of_c113 (h113 : ASInputs.AS_C_1_13) (hT : IsSylowTwoOf T (K ⊔ T))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hK : IsShort2 K) (h5 : IsAltType K 5) :
    blockQ K = blockU K ⊔ (K ⊓ Subgroup.centralizer (K : Set G)) ∧
      (K ⊓ Subgroup.centralizer (K : Set G) = ⊥ ∨ Nat.card (Subgroup.center ↥K) = 2) := by
  have hZ := blockZ_eq_bot_of_c113 h113 hT hTK hK h5
  obtain ⟨-, -, -, -, h5', -⟩ := (h113 G K T hT hTK hK).2.1 5 (Or.inr rfl) h5
  obtain ⟨hN, hcase⟩ := h5' rfl
  have hZc := inf_centralizer_le_blockQ hK
  have hZU : ∀ x ∈ K ⊓ Subgroup.centralizer (K : Set G), x ∈ blockU K → x = 1 := by
    intro x hx hxU
    have : x ∈ blockZ K := ⟨hxU, hx.2⟩
    rwa [hZ, Subgroup.mem_bot] at this
  have hle : blockU K ⊔ (K ⊓ Subgroup.centralizer (K : Set G)) ≤ blockQ K :=
    sup_le (hK.2.2.1.1.trans inf_le_left) hZc
  rcases hcase with he | ⟨he, hcard⟩
  ·
    obtain ⟨e⟩ := he
    have hc : Subgroup.center (↥K ⧸ (blockU K).subgroupOf K) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      apply e.injective
      rw [map_one]
      refine alt5_center _ fun h => ?_
      have := (Subgroup.mem_center_iff.mp hy (e.symm h)).symm
      simpa using congrArg e this
    have hQU := blockQ_le_blockU_of_center hc
    refine ⟨le_antisymm (hQU.trans le_sup_left) hle, Or.inl ?_⟩
    rw [eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (hZU x hx (hQU (hZc hx)))
  ·
    obtain ⟨e⟩ := he
    refine ⟨le_antisymm ?_ hle, Or.inr hcard⟩
    obtain ⟨z, hz1⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥K))).mp hcard
    obtain ⟨⟨z, hzc⟩, hz⟩ := z, hz1.1
    have hz0 : z ≠ 1 := fun h => hz (Subtype.ext h)
    have hzZ : (z : G) ∈ K ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← map_center_eq_inf]
      exact ⟨z, hzc, rfl⟩
    have hzU : (z : G) ∉ blockU K := fun h => hz0 (Subtype.ext (hZU _ hzZ h))
    have hcK : Nat.card (Subgroup.center (↥K ⧸ (blockU K).subgroupOf K)) = 2 := by
      rw [← card_center_sl2_five, ← Subgroup.map_center_eq e,
        Subgroup.card_map_of_injective e.injective]
    have hzm := mk_mem_center_of_mem_blockQ (q := z) (hZc hzZ)
    have hzm1 : (⟨_, hzm⟩ : ↥(Subgroup.center (↥K ⧸ (blockU K).subgroupOf K))) ≠ 1 := by
      intro h
      apply hzU
      have := congrArg Subtype.val h
      rw [OneMemClass.coe_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
      exact this
    obtain ⟨w, hw, hwu⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center
      (↥K ⧸ (blockU K).subgroupOf K)))).mp hcK
    intro x hx
    have hxK : x ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hx
    have hxm := mk_mem_center_of_mem_blockQ (q := ⟨x, hxK⟩) hx
    by_cases hx1 : (⟨_, hxm⟩ : ↥(Subgroup.center (↥K ⧸ (blockU K).subgroupOf K))) = 1
    · have := congrArg Subtype.val hx1
      rw [OneMemClass.coe_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
      exact Subgroup.mem_sup_left this
    · have heq := (hwu _ hx1).trans (hwu _ hzm1).symm
      have := congrArg Subtype.val heq
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
      have hmem : (z : G) * ((z : G)⁻¹ * x) ∈ blockU K ⊔ (K ⊓ Subgroup.centralizer (K : Set G)) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right hzZ) (by
          have h' : ((⟨x, hxK⟩ : ↥K)⁻¹ * z : ↥K) = _ := rfl
          refine Subgroup.mem_sup_left ?_
          have := (blockU K).inv_mem this
          simpa using this)
      simpa using hmem

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
