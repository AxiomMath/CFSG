module

public import CFSG.Quasithin.Vol2.Ch4Sec4Lem444
public import CFSG.Quasithin.Background.BlueprintB2Reduced

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G]

theorem conjClosure_eq_self {L T : Subgroup G} (h : T ≤ Subgroup.normalizer (L : Set G)) :
    conjClosure L T = L :=
  le_antisymm (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (h ht) l).1 hl)
    (le_conjClosure L T)

theorem conjugate_eq_self_of_normalizes {L : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) : CFSG.conjugate L t = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (inv_mem ht)

theorem three_subgroups_le {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set K := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hmap : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf K, B.subgroupOf K⁆, C.subgroupOf K⁆).map K.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ K → B ≤ K → C ≤ K →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔
        ⁅⁅(A.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)),
          (B.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆,
          (C.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

variable [Finite G] {T M L B Tp VB V : Subgroup G}

omit [Finite G] in
theorem mul_bot_eq_bot_mul (B : Subgroup G) :
    (B : Set G) * ((⊥ : Subgroup G) : Set G) = ((⊥ : Subgroup G) : Set G) * (B : Set G) := by
  rw [Subgroup.coe_bot, Set.mul_singleton, Set.singleton_mul]
  simp

theorem Hyp4_4_1TwoOrbit.toBot (h : Hyp4_4_1TwoOrbit G T M L B Tp)
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) : Hyp4_4_1TwoOrbit G T M L B ⊥ :=
  { h.toHyp4_4_1Core with
    Tp_le := bot_le
    mul_comm_Tp := mul_bot_eq_bot_mul B
    orbit_Tp := fun t ht => ⟨1, Subgroup.one_mem _, by
      rw [conjugate_eq_self_of_normalizes (hLn (h.T_le ht)),
        conjugate_eq_self_of_mem L.one_mem]⟩ }

theorem Hyp4_4_1Orbit.toBot (h : Hyp4_4_1Orbit G T M L B Tp VB)
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) : Hyp4_4_1Orbit G T M L B ⊥ VB :=
  { h.toHyp4_4_1TwoOrbit.toBot hLn, h.toHyp4_4_1Three with }

omit [Finite G] in
theorem le_omegaOneCenter_of_isPrimeReduced {X V : Subgroup G} (hVX : V ≤ X)
    (hV : IsPrimeReduced 2 (V.subgroupOf X)) :
    V ≤ quasithinOmegaOneCenter (pCoreOf 2 X) ∧
      pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := by
  have hle := isPrimeReduced_le_centerTorsion_pCore hV
  have key : ∀ v ∈ V, v ∈ pCoreOf 2 X ∧ (∀ y ∈ pCoreOf 2 X, y * v = v * y) ∧ v ^ 2 = 1 := by
    intro v hv
    have h1 : (⟨v, hVX hv⟩ : ↥X) ∈ BlueprintB2.centerTorsion 2 (CFSG.pCore 2 ↥X) :=
      hle (Subgroup.mem_subgroupOf.2 hv)
    rw [BlueprintB2.mem_centerTorsion_iff] at h1
    obtain ⟨hvP, hvC, hv2⟩ := h1
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨⟨v, hVX hv⟩, ?_, rfl⟩
      exact hvP
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : y ∈ CFSG.pCore 2 ↥X := by exact hy
      exact congrArg Subtype.val (hvC y hy')
    · exact congrArg Subtype.val hv2
  refine ⟨fun v hv => ?_, fun y hy => ?_⟩
  · obtain ⟨hvP, hvC, hv2⟩ := key v hv
    exact Subgroup.subset_closure ⟨⟨hvP, Subgroup.mem_centralizer_iff.2 hvC⟩, hv2⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((key v hv).2.1 y hy).symm

theorem remark_4_4_2 (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) (hTM : T ≤ M) (hL : quasithinIsMaximalLocal T L)
    (hLf : quasithinIsFaithfulLocal T L) (hLM : L ≤ M)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) (hVLT : V ≤ L ⊔ T)
    (hV : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) (hVL : V = ⁅V, L⁆) (hV1 : V ≠ ⊥)
    (hBM : B ≤ M) (hBV : B ≤ Subgroup.centralizer (V : Set G)) (hB1 : B ≠ ⊥)
    (hBc : IsMulCommutative ↥B) (hBo : Odd (Nat.card B)) :
    Hyp4_4_1Orbit G T M L B ⊥ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTM.trans hLn
  have hL0 : conjClosure L T = L := conjClosure_eq_self hTL
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBM.trans hLn
  have hVnormal : (V.subgroupOf (L ⊔ T)).Normal := hV.1
  have hVn : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := by
    have h := le_normalizer_map_subtype_of_normal (L ⊔ T) (V.subgroupOf (L ⊔ T))
    rwa [Subgroup.map_subgroupOf_eq_of_le hVLT] at h
  obtain ⟨hVZ, hRV⟩ := le_omegaOneCenter_of_isPrimeReduced hVLT hV
  have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 L)
    exact sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L))
  have hQV : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := hQL.trans hRV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hVn
  have hLB : ⁅L, B⁆ ≤ L ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hBL) ?_
    rw [Subgroup.commutator_le]
    intro l hl b hb
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : l⁻¹ * v * l ∈ V := (Subgroup.mem_normalizer_iff''.1 (hLV hl) v).1 hv
    have hbv : (l⁻¹ * v * l) * b = b * (l⁻¹ * v * l) :=
      Subgroup.mem_centralizer_iff.1 (hBV hb) _ hv'
    have hbv' : v * b⁻¹ = b⁻¹ * v :=
      Subgroup.mem_centralizer_iff.1 (hBV (B.inv_mem hb)) v hv
    rw [commutatorElement_def]
    calc v * (l * b * l⁻¹ * b⁻¹) = l * ((l⁻¹ * v * l) * b) * l⁻¹ * b⁻¹ := by group
      _ = l * (b * (l⁻¹ * v * l)) * l⁻¹ * b⁻¹ := by rw [hbv]
      _ = l * b * l⁻¹ * (v * b⁻¹) := by group
      _ = l * b * l⁻¹ * (b⁻¹ * v) := by rw [hbv']
      _ = l * b * l⁻¹ * b⁻¹ * v := by group
  have hCLnorm : L ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (V : Set G) :
      Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · rintro ⟨hcL, hcV⟩
      refine ⟨L.mul_mem (L.mul_mem hl hcL) (L.inv_mem hl), ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
      have hv' : l⁻¹ * v * l ∈ V := (Subgroup.mem_normalizer_iff''.1 (hLV hl) v).1 hv
      have h1 := (Subgroup.mem_centralizer_iff.1 hcV) _ hv'
      calc v * (l * c * l⁻¹) = l * ((l⁻¹ * v * l) * c) * l⁻¹ := by group
        _ = l * (c * (l⁻¹ * v * l)) * l⁻¹ := by rw [h1]
        _ = l * c * l⁻¹ * v := by group
    · rintro ⟨hcL, hcV⟩
      have hcL' : c ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem hl) hcL) hl
        simpa [mul_assoc] using this
      refine ⟨hcL', ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
      have hv' : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) v).1 hv
      have h1 := (Subgroup.mem_centralizer_iff.1 hcV) _ hv'
      have h2 : l⁻¹ * (l * v * l⁻¹ * (l * c * l⁻¹)) * l =
          l⁻¹ * (l * c * l⁻¹ * (l * v * l⁻¹)) * l := by rw [h1]
      simpa [mul_assoc] using h2
  have hCQ : ⁅L ⊓ Subgroup.centralizer (V : Set G), L⁆ ≤ pCoreOf 2 L := by
    set C := L ⊓ Subgroup.centralizer (V : Set G) with hC
    have hCnormal : (C.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hCLnorm
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hCbar : ((C.subgroupOf L).map π).Normal := hCnormal.map π hπs
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
        ((C.subgroupOf L).map π) with hcen | htop
    · rw [Subgroup.commutator_le]
      intro c hc l hl
      have hcl : π ⁅(⟨c, hc.1⟩ : ↥L), ⟨l, hl⟩⁆ = 1 := by
        rw [map_commutatorElement]
        have hcz : π ⟨c, hc.1⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
          hcen ⟨⟨c, hc.1⟩, hc, rfl⟩
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.1 hcz _).symm
      have hmem := (QuotientGroup.eq_one_iff _).1 hcl
      refine ⟨⁅(⟨c, hc.1⟩ : ↥L), ⟨l, hl⟩⁆, ?_, rfl⟩
      exact hmem
    ·
      exfalso
      apply hV1
      rw [hVL, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
      intro l hl
      have hl' : π ⟨l, hl⟩ ∈ (C.subgroupOf L).map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨c, hc, hce⟩ := hl'
      have hq' : c⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        change (π c)⁻¹ * π ⟨l, hl⟩ = 1
        rw [hce, inv_mul_cancel]
      have hqG : ((c⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := by
        refine ⟨c⁻¹ * ⟨l, hl⟩, ?_, rfl⟩
        exact hq'
      have hcV : (c : G) ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_subgroupOf.1 hc).2
      have hlc : l = (c : G) * ((c⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
      rw [hlc]
      exact Subgroup.mul_mem _ hcV (hQV hqG)
  have hQn : L ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 L
  have hBQ : B ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    hBL.trans (normalizer_le_normalizer_pCoreOf 2 L)
  have h1 : ⁅⁅L, B⁆, L⁆ ≤ pCoreOf 2 L := (Subgroup.commutator_mono hLB le_rfl).trans hCQ
  have h2 : ⁅⁅B, L⁆, L⁆ ≤ pCoreOf 2 L := by rw [Subgroup.commutator_comm B L]; exact h1
  have h3 : ⁅⁅L, L⁆, B⁆ ≤ pCoreOf 2 L := three_subgroups_le hQn hBQ hQn h1 h2
  have hLperf : ⁅L, L⁆ = L := hL.1.2.1.2.1
  rw [hLperf] at h3
  refine
    { simple := hs
      nonabelian := hnab
      qtke := hK
      sylow := hT
      maxTwoLocal := hM
      T_le := hTM
      maximal := hL
      faithful := hLf
      L_le := hLM
      quasisimple := hq
      B_le := hBM
      B_ne_bot := hB1
      B_comm := hBc
      B_odd := hBo
      commutator_le := by rw [hL0]; exact h3
      Tp_le := bot_le
      mul_comm_Tp := mul_bot_eq_bot_mul B
      orbit_Tp := fun t ht => ⟨1, Subgroup.one_mem _, by
        rw [conjugate_eq_self_of_normalizes (hTL ht), conjugate_eq_self_of_mem L.one_mem]⟩
      VB_le := by rw [hL0]; exact hVZ
      VB_normalized := by rw [hL0]; exact hVn
      VB_eq := by rw [hL0]; exact hVL
      VB_ne_bot := hV1
      VB_centralizes :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).2 (Subgroup.le_centralizer_iff.1 hBV) }

end CFSG.Quasithin.H13
