module

public import CFSG.CGT.PushingUpLit.BlocksCommuteQuasi
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem blockQ_eq_oTwoIn (K : Subgroup G) : blockQ K = CGT.PushingUpLit.oTwoIn K := by
  rw [blockQ, pCoreOf, CGT.PushingUpLit.oTwoIn_eq_map]

theorem blockU_eq_lit (K : Subgroup G) : blockU K = CGT.PushingUpLit.blockU K := by
  rw [QuasithinUnique.blockU, CGT.PushingUpLit.blockU, blockQ_eq_oTwoIn]

theorem blockZ_eq_lit (K : Subgroup G) : blockZ K = CGT.PushingUpLit.blockZ K := by
  rw [QuasithinUnique.blockZ, CGT.PushingUpLit.blockZ, blockU_eq_lit]

variable [Finite G]

theorem isShortGroup_of_isShort2 {K : Subgroup G} (hK : IsShort2 K) :
    RankThree.PartOne.IsShortGroup ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hres, hchar, ⟨hUQ, -⟩, htype, hlt, hirr⟩ := hK
  have hQ : blockQ K = (CFSG.pCore 2 ↥K).map K.subtype := by
    rw [blockQ_eq_oTwoIn, CGT.PushingUpLit.oTwoIn_eq_map]
  have hU : (RankThree.PartOne.shortU ↥K).map K.subtype = blockU K := by
    rw [blockU_eq_lit, CGT.PushingUpLit.map_shortU_subtype]
  have hC : (RankThree.PartOne.shortC ↥K).map K.subtype = blockZ K := by
    rw [blockZ_eq_lit, CGT.PushingUpLit.map_shortC_subtype]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥K 2).mp fun c hc => ?_
    have hc' : (c : G) ∈ K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
      refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro r hr
      have hr' : r ∈ (CFSG.pCore 2 ↥K).map K.subtype := by rw [← hQ]; exact hr
      obtain ⟨r0, hr0, rfl⟩ := hr'
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc r0 hr0)
    have h1 : (c : G) ∈ (CFSG.pCore 2 ↥K).map K.subtype := by rw [← hQ]; exact hchar hc'
    obtain ⟨c0, hc0, hcc⟩ := h1
    rwa [← Subtype.ext hcc]
  · refine CGT.PushingUpLit.oResidualTwo_eq_top_iff.2 fun N hN hpow => ?_
    exact hres N ((CGT.PushingUpLit.isPGroup_two_quotient_iff N).2 hpow)
  · rcases htype with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact Nat.prime_three)
  · refine CGT.PushingUpLit.shortU_le_center_iff.2 fun u hu => ?_
    have hu' : (u : G) ∈ blockU K := by rw [← hU]; exact Subgroup.mem_map_of_mem _ hu
    have hu2 := hUQ hu'
    have hmem : (u : G) ∈ (CFSG.pCore 2 ↥K).map K.subtype := by rw [← hQ]; exact hu2.1
    obtain ⟨u0, hu0, hu0e⟩ := hmem
    refine ⟨by rwa [← Subtype.ext hu0e], fun r hr => Subtype.ext ?_⟩
    have hr' : (r : G) ∈ blockQ K := by rw [hQ]; exact Subgroup.mem_map_of_mem _ hr
    exact (Subgroup.mem_centralizer_iff.mp hu2.2 r hr').symm
  · rw [← Subgroup.map_lt_map_iff_of_injective K.subtype_injective, hU, hC]
    exact hlt
  · intro N hN hNU hCN
    have hNU' : N.map K.subtype ≤ blockU K := by rw [← hU]; exact Subgroup.map_mono hNU
    have hCN' : blockZ K ≤ N.map K.subtype := by rw [← hC]; exact Subgroup.map_mono hCN
    have hKN : K ≤ Subgroup.normalizer (N.map K.subtype : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨k, hk⟩ * n * ⟨k, hk⟩⁻¹, hN.conj_mem n hn _, rfl⟩
      · rintro ⟨n, hn, hne⟩
        have hx : x ∈ K := by
          have h1 : k * x * k⁻¹ ∈ K := hne ▸ n.2
          simpa [mul_assoc] using K.mul_mem (K.mul_mem (K.inv_mem hk) h1) hk
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have h2 := hN.conj_mem n hn ⟨k, hk⟩⁻¹
        have e : (⟨k, hk⟩⁻¹ * n * (⟨k, hk⟩⁻¹)⁻¹ : ↥K) = ⟨x, hx⟩ := by
          have hn' : (n : G) = k * x * k⁻¹ := hne
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hn']
          group
        rwa [e] at h2
    rcases hirr _ hCN' hNU' hKN with h | h
    · left
      apply Subgroup.map_injective K.subtype_injective
      rw [h, hC]
    · right
      apply Subgroup.map_injective K.subtype_injective
      rw [h, hU]

theorem commutator_eq_bot_of_mem_cComp {H K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ cComp H)
    (h₂ : K₂ ∈ cComp H) (hs₁ : IsShort2 K₁) (hs₂ : IsShort2 K₂)
    (hq : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) (hne : K₁ ≠ K₂) : ⁅K₁, K₂⁆ = ⊥ := by
  have hK₁H := le_of_mem_cComp h₁
  have hK₂H := le_of_mem_cComp h₂
  have hblock : ∀ {K : Subgroup G}, K ∈ cComp H → IsShort2 K →
      CGT.PushingUpLit.IsBlockOf (K.subgroupOf H) := by
    intro K hK hs
    refine ⟨A3.subnormal_top_iff.mp ((isSubnormal_subgroupOf_top_iff (le_of_mem_cComp hK)).mpr
      (subnormal_of_mem_cComp hK)), ?_⟩
    exact CGT.PushingUpLit.isShortGroup_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp hK)).symm (isShortGroup_of_isShort2 hs)
  have hq' : CFSG.IsQuasisimple (↥(K₁.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K₁.subgroupOf H)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CGT.PushingUpLit.quotTopEquiv (Subgroup.subgroupOfEquivOfLe hK₁H).symm) hq
  have hne' : K₁.subgroupOf H ≠ K₂.subgroupOf H := by
    intro h
    have h2 := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr hK₁H, inf_eq_left.mpr hK₂H] at h2
    exact hne h2
  have h := CGT.PushingUpLit.commutator_eq_bot_of_qs (hblock h₁ hs₁) hq' (hblock h₂ hs₂) hne'
  have h' := congrArg (Subgroup.map H.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK₁H,
    Subgroup.map_subgroupOf_eq_of_le hK₂H, Subgroup.map_bot] at h'

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
