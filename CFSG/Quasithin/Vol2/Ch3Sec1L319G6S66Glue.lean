module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Theta
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Parity
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66O2Blocks
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Simple
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Nat

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.Ch3z

theorem exists_block_eq_theta {G : Type} [Group G] [Finite G] {H T M₂ U A L N L' N' : Subgroup G}
    (hB1 : B69One) (h : Ch3z.Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hstep' : IsChiefStep H U L' N') (hnc' : ¬ IsCentralStep H L' N')
    (hJ : centralizerMod L' H N' = centralizerMod L H N)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @Ch3z.BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    {H' : Subgroup (MulAut ↥(chiefMod L N))} (hH' : H' ∈ 𝓗)
    (hNat : @Ch3z.NatBlockData ↥(chiefMod L N) (chiefCG (h.hE hstep)) H'
        (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (h.hE hstep)) H') 2)
    {𝓗' : Finset (Subgroup (MulAut ↥(chiefMod L' N')))}
    (hctx' : @Ch3z.BlkCtx ↥(chiefMod L' N') (chiefCG (h.hE hstep')) (chiefAut H L' N')
        (chiefImg (Setting.hHL hstep') (Setting.hHN hstep') T)
        (chiefImg (Setting.hHL hstep') (Setting.hHN hstep') M₂) 𝓗')
    {y : G} (hyH : y ∈ H) (hyH' : chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩ ∈ H') :
    ∃ K₀ ∈ 𝓗', (@Ch3z.NatBlockData ↥(chiefMod L' N') (chiefCG (h.hE hstep')) K₀
        (@CFSG.Quasithin.commV ↥(chiefMod L' N') (chiefCG (h.hE hstep')) K₀) 2) ∧
      chiefPsi (Setting.hHL hstep') (Setting.hHN hstep') ⟨y, hyH⟩ ∈ K₀ := by
  classical
  haveI : Finite ↥(chiefMod L N) := inferInstance
  let _ : CommGroup ↥(chiefMod L N) := chiefCG (h.hE hstep)
  let _ : CommGroup ↥(chiefMod L' N') := chiefCG (h.hE hstep')
  obtain ⟨θ, hθ⟩ := chiefAut_mulEquiv_of_centralizerMod_eq (Setting.hHL hstep) (Setting.hHN hstep)
    (Setting.hHL hstep') (Setting.hHN hstep') (h.hNL hstep) (h.hNL hstep') hJ.symm
  have hperf : ∀ K ∈ 𝓗, Group.IsPerfect ↥K :=
    blocks_perfect_of_trans hctx hH' (Ch3z.NatBlockData.isPerfect le_rfl hNat)
  have hnat' := allBlocks_natural_of_step hB1 h hstep hnc hstep' hnc' hJ hctx hH' hNat hctx'
  have hperf' : ∀ K ∈ 𝓗', Group.IsPerfect ↥K := by
    intro K hK
    obtain ⟨e, he, hN⟩ := hnat' K hK
    exact Ch3z.NatBlockData.isPerfect he hN
  have hO2 : O2 ↥(chiefAut H L N) = (⨆ K ∈ 𝓗, K).subgroupOf (chiefAut H L N) :=
    O2_eq_iSup_of_blocks hctx hperf
  have hO2' : O2 ↥(chiefAut H L' N') = (⨆ K ∈ 𝓗', K).subgroupOf (chiefAut H L' N') :=
    O2_eq_iSup_of_blocks hctx' hperf'
  have hmap : (O2 ↥(chiefAut H L N)).map θ.toMonoidHom = O2 ↥(chiefAut H L' N') :=
    O2_map_mulEquiv θ
  rw [hO2, hO2'] at hmap
  have hH'A : H' ≤ ⨆ K ∈ 𝓗, K := le_iSup₂ (f := fun K (_ : K ∈ 𝓗) => K) H' hH'
  have hA'X' : (⨆ K ∈ 𝓗', K) ≤ chiefAut H L' N' := iSup₂_le fun K hK => hctx'.mem_le hK
  have hcomm0 : ∀ K ∈ 𝓗, K ≠ H' → ∀ a ∈ K, ∀ s ∈ H', a * s * a⁻¹ = s := by
    intro K hK hKH a ha s hs
    rw [hctx.comm_of_ne hK hH' hKH ha hs, mul_inv_cancel_right]
  have hnormH' : ∀ g ∈ ⨆ K ∈ 𝓗, K, ∀ s ∈ H', g * s * g⁻¹ ∈ H' := by
    have hle : (⨆ K ∈ 𝓗, K) ≤ Subgroup.normalizer (H' : Set _) := by
      refine iSup₂_le fun K hK => ?_
      by_cases hKH : K = H'
      · subst hKH
        exact Subgroup.le_normalizer
      · intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hs
          rw [hcomm0 K hK hKH a ha s hs]
          exact hs
        · intro hs
          have h2 := hcomm0 K hK hKH a⁻¹ (K.inv_mem ha) _ hs
          have e : a⁻¹ * (a * s * a⁻¹) * a⁻¹⁻¹ = s := by group
          rw [e] at h2
          rw [h2]
          exact hs
    intro g hg s hs
    exact (Subgroup.mem_normalizer_iff.mp (hle hg) s).mp hs
  obtain ⟨S, hS⟩ : ∃ S, S = ((H'.subgroupOf (chiefAut H L N)).map θ.toMonoidHom).map
      (chiefAut H L' N').subtype := ⟨_, rfl⟩
  have hSA : S ≤ ⨆ K ∈ 𝓗', K := by
    intro s hs
    rw [hS] at hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    have hxO : x ∈ (⨆ K ∈ 𝓗, K).subgroupOf (chiefAut H L N) :=
      Subgroup.mem_subgroupOf.mpr (hH'A (Subgroup.mem_subgroupOf.mp hx))
    have h1 : θ x ∈ (⨆ K ∈ 𝓗', K).subgroupOf (chiefAut H L' N') := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hxO
    exact Subgroup.mem_subgroupOf.mp h1
  have hSn : ∀ g ∈ ⨆ K ∈ 𝓗', K, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have hgM : (⟨g, hA'X' hg⟩ : ↥(chiefAut H L' N')) ∈
        ((⨆ K ∈ 𝓗, K).subgroupOf (chiefAut H L N)).map θ.toMonoidHom := by
      rw [hmap]
      exact Subgroup.mem_subgroupOf.mpr hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgM
    have hxg' : ((θ x : ↥(chiefAut H L' N')) : MulAut ↥(chiefMod L' N')) = g :=
      congrArg Subtype.val hxg
    rw [hS] at hs ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp ht
    have hmem : x * s₀ * x⁻¹ ∈ H'.subgroupOf (chiefAut H L N) := by
      rw [Subgroup.mem_subgroupOf]
      have h3 := hnormH' _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hs₀)
      simpa using h3
    subst hxg'
    refine Subgroup.mem_map.mpr ⟨θ (x * s₀ * x⁻¹), Subgroup.mem_map_of_mem _ hmem, ?_⟩
    simp
  haveI : IsSimpleGroup ↥H' := natBlock_isSimpleGroup le_rfl hNat
  have eS : ↥H' ≃* ↥S := by
    rw [hS]
    exact (Subgroup.subgroupOfEquivOfLe (hctx.mem_le hH')).symm.trans
      ((Subgroup.equivMapOfInjective (H'.subgroupOf (chiefAut H L N)) θ.toMonoidHom θ.injective).trans
        (Subgroup.equivMapOfInjective _ (chiefAut H L' N').subtype
          (Subgroup.subtype_injective _)))
  have hSs : IsSimpleGroup ↥S := eS.symm.isSimpleGroup
  have hSna : ¬ IsMulCommutative ↥S := fun hc =>
    natBlock_not_isMulCommutative le_rfl hNat (Function.Surjective.isMulCommutative eS.symm.surjective hc)
  have hKs : ∀ K ∈ 𝓗', IsSimpleGroup ↥K := by
    intro K hK
    obtain ⟨e, he, hN⟩ := hnat' K hK
    exact natBlock_isSimpleGroup he hN
  have hcomm2 : ∀ K ∈ 𝓗', ∀ K' ∈ 𝓗', K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a :=
    fun K hK K' hK' hne a ha b hb => hctx'.comm_of_ne hK hK' hne ha hb
  have hS𝓗' : S ∈ 𝓗' := mem_of_simple_normal_blocks 𝓗' hcomm2 hKs S hSA hSn hSs hSna
  obtain ⟨e₀, he₀, hN₀⟩ := hnat' S hS𝓗'
  have h60 : Nat.card ↥H' = 60 := (natBlock_card hNat).trans (by norm_num)
  have hcardS : Nat.card ↥S = 60 := (Nat.card_congr eS.toEquiv).symm.trans h60
  have he₀2 : e₀ = 2 := natBlock_eq_two_of_card hN₀ hcardS
  subst he₀2
  have hmemψ : chiefPsi (Setting.hHL hstep') (Setting.hHN hstep') ⟨y, hyH⟩ ∈ S := by
    rw [hS]
    have hg : chiefHom (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩ ∈
        H'.subgroupOf (chiefAut H L N) :=
      Subgroup.mem_subgroupOf.mpr hyH'
    have hθg : ((θ (chiefHom (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩) :
        ↥(chiefAut H L' N')) : MulAut ↥(chiefMod L' N')) =
        chiefPsi (Setting.hHL hstep') (Setting.hHN hstep') ⟨y, hyH⟩ :=
      congrArg Subtype.val (hθ ⟨y, hyH⟩)
    exact Subgroup.mem_map.mpr ⟨θ (chiefHom (Setting.hHL hstep) (Setting.hHN hstep) ⟨y, hyH⟩),
      Subgroup.mem_map_of_mem _ hg, hθg⟩
  exact ⟨S, hS𝓗', hN₀, hmemψ⟩

end CFSG.Quasithin.H13.L319.S66

end
