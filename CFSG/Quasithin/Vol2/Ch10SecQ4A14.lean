module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A13
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Direct
public import CFSG.Quasithin.Vol2.Ch10SecQ4A11
public import CFSG.Quasithin.Vol2.Ch10SecQ4A3
public import CFSG.Quasithin.Vol2.Ch10SecQ4A9
public import CFSG.Quasithin.Vol2.Ch10SecQ4Obl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

@[expose] def NoDelta5Statement : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y → CFSG.SectionRank.IsSQTKCat Y →
    CFSG.pCore 2 Y = ⊥ → A5.G3.NoDelta5In Y

namespace C10E4

variable {G : Type} [Group G] [Finite G] {K J X T : Subgroup G}

omit [Finite G] in
theorem isSylowTwoOf_sup (hT : IsSylowTwoOf T X) (hKX : K ≤ X) : IsSylowTwoOf T (K ⊔ T) := by
  refine ⟨le_sup_right, hT.2.1, fun hdvd => hT.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex T (K ⊔ T) X le_sup_right (sup_le hKX hT.1)
  have h2 : 2 ∣ T.relIndex X := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem false_of_blockU_inf_eq_bot (h36' : A36ForSQTK) (hF1 : FactA314NoSL25Block)
    (hΔ : NoDelta5Statement) (h113 : ASInputs.AS_C_1_13)
    (hXs : CFSG.SectionRank.IsSQTKCat ↥X) (hT : IsSylowTwoOf T X) (hJ : J ∈ cComp X)
    (hKJ : K < J) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hQK : pCoreOf 2 J ≤ Subgroup.normalizer (K : Set G)) (hK : IsShort2 K) (h5 : IsAltType K 5)
    (hUQ : blockU K ⊓ pCoreOf 2 J = ⊥) : False := by
  have hJX := le_of_mem_cComp hJ
  have hTs := isSylowTwoOf_sup hT (hKJ.le.trans hJX)
  have hZ := blockZ_eq_bot_of_c113 h113 hTs hTK hK h5
  obtain ⟨hQeq, hcases⟩ := blockQ_eq_sup_of_c113 h113 hTs hTK hK h5
  have hYc := sqtkHypCat_quot hJX hXs
  set f := fK hKJ.le with hf
  have hkQ : ∀ x : ↥K, f x = 1 → (x : G) ∈ blockQ K := fK_ker_le hKJ.le
  have hkU : ∀ x : ↥K, f x = 1 → (x : G) ∈ blockU K → (x : G) = 1 := by
    intro x hx hxU
    have : (x : G) ∈ blockU K ⊓ pCoreOf 2 J := ⟨hxU, (fK_eq_one_iff hKJ.le x).mp hx⟩
    rwa [hUQ, Subgroup.mem_bot] at this
  have hQK' : blockQ K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hUK : blockU K ≤ K := hK.2.2.1.1.trans (inf_le_left.trans hQK')
  have hZK : K ⊓ Subgroup.centralizer (K : Set G) ≤ K := inf_le_left
  by_cases hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)
  · have hB1 := isShort2_range f hkQ hkU hK h5
    have hB2 := isAltType_range f hkQ hkU hK h5
    have hBZ := blockZ_range_eq_bot f hkQ hkU hZ
    have hS := isSylowTwoOf_quot hT hJ
    have hSN := quotSylow_le_normalizer hKJ.le hTK
    by_cases hZQ : K ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 J
    ·
      have hQB : blockQ f.range = blockU f.range := by
        rw [blockQ_range f hkQ, hQeq, imgL_sup f hUK hZK, blockU_range f hkQ]
        have h0 : imgL f (K ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          obtain ⟨x, hx, rfl⟩ := (mem_imgL f).mp hy
          exact (Subgroup.mem_bot).mpr ((fK_eq_one_iff hKJ.le x).mpr (hZQ hx))
        rw [h0, sup_bot_eq]
      have hD := A5.G3.isDelta5Group_of_block hB2 hBZ hQB
      have hBq : CFSG.IsQuasisimple (↥f.range ⧸ CFSG.pCore 2 ↥f.range) :=
        (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr (quotEquivRange f hkQ)).mp
          (quot_isQuasisimple hK h5)
      have hnorm : (f.range.subgroupOf (f.range ⊔
          ((T ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J)))).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
          (sup_le Subgroup.le_normalizer hSN)
      have hBf : f.range ∈ lFamily (((T ⊓ J).subgroupOf J).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) :=
        C1GN.mem_cComp_of_short hB1 hBq (A3.subnormal_of_normal le_sup_left hnorm)
      exact hΔ _ hq (Vol2Native.SQTKHypCat.isSQTKCat hYc) hYc.o2 _ hS _ hBf
        (range_fK_ne_top hJ hKJ hQK (perfect_of_isAltType_five hK h5)
          (ne_bot_of_isAltType_five h5)) hSN hD
    ·
      obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.mp hZQ
      have hcard : Nat.card (Subgroup.center ↥K) = 2 := by
        rcases hcases with h | h
        · exfalso
          rw [h] at hzZ
          obtain rfl := Subgroup.mem_bot.mp hzZ
          exact hzQ (Subgroup.one_mem _)
        · exact h
      have hinj : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have hxZ := inf_pCoreOf_le_center hKJ.le hUQ ⟨x.2, (fK_eq_one_iff hKJ.le x).mp hx⟩
        have hc2 : Nat.card ↥(K ⊓ Subgroup.centralizer (K : Set G)) = 2 :=
          (card_center_eq K) ▸ hcard
        obtain ⟨w, -, hwu⟩ :=
          (Nat.card_eq_two_iff' (1 : ↥(K ⊓ Subgroup.centralizer (K : Set G)))).mp hc2
        by_contra hx1
        have hxw : (⟨x, hxZ⟩ : ↥(K ⊓ Subgroup.centralizer (K : Set G))) = w :=
          hwu _ fun h => hx1 (Subtype.ext (by simpa using congrArg Subtype.val h))
        have hzw : (⟨z, hzZ⟩ : ↥(K ⊓ Subgroup.centralizer (K : Set G))) = w := by
          refine hwu _ fun h => hzQ ?_
          have h' : z = 1 := congrArg Subtype.val h
          rw [h']
          exact Subgroup.one_mem _
        have hxz : (x : G) = z := congrArg Subtype.val (hxw.trans hzw.symm)
        exact hzQ (hxz ▸ (fK_eq_one_iff hKJ.le x).mp hx)
      let e : ↥K ≃* ↥f.range := MonoidHom.ofInjective hinj
      have hBc : Nat.card (Subgroup.center ↥f.range) = 2 := by
        rw [← Subgroup.map_center_eq e,
          Subgroup.card_map_of_injective (f := (e : ↥K →* ↥f.range)) e.injective]
        exact hcard
      have hQB : blockQ f.range =
          blockU f.range ⊔ (Subgroup.center ↥f.range).map f.range.subtype := by
        rw [blockQ_range f hkQ, hQeq, imgL_sup f hUK hZK, blockU_range f hkQ,
          imgL_center_of_injective f hinj]
      exact hF1 _ hYc hq _ _ hS hSN hB1 hB2 hBZ hBc hQB
  ·
    obtain ⟨u₁, hu₁, u₂, hu₂, h1, h2, h12⟩ := exists_two_blockU h5 hZ
    have hsq : ∀ u (hu : u ∈ blockU K), f ⟨u, hUK hu⟩ ^ 2 = 1 := by
      intro u hu
      rw [← map_pow]
      have : (⟨u, hUK hu⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa using hK.2.2.1.2 u hu)
      rw [this, map_one]
    refine false_of_four (h36' _ (sqtkHyp_of_cat hYc)) (top_mem_cComp_quot hJ) hq
      (hsq u₁ hu₁) (hsq u₂ hu₂) (fun h => h1 (hkU _ h hu₁)) (fun h => h2 (hkU _ h hu₂))
      (fun h => h12 (congrArg Subtype.val (eq_of_mem_blockU f hkU hu₁ hu₂ h))) ?_
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hK.2.2.1.1 hu₂).2 u₁ (hK.2.2.1.1 hu₁).1)

end C10E4

end CFSG.Quasithin.Vol2.Ch10.SecF
