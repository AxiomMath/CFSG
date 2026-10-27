module

public import CFSG.Quasithin.Background.C58Blocks
public import CFSG.Quasithin.Vol2.Ch3xC58NSGood

public section

namespace CFSG.Quasithin.H13.Ch4.C53

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.C58 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_blockConfig_of_isSylowTwoOf {T H R M₀ N : Subgroup G} (hTsylH : IsSylowTwoOf T H)
    (hchar : CharTwo H) (hN : IsUniqueMaxOver H T N)
    (hTn : ¬ H ≤ normalizer (T : Set G)) (hsolv : Group.IsSolvable H)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2)
    (hR1 : R ≠ ⊥) (hRT : R ≤ T) (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R))
    (hTM₀ : T ≤ M₀) (hM₀R : M₀ ≤ normalizer (R : Set G)) (hNC : NoCommonNormal R H M₀) :
    ∃ K₁ : Subgroup G, BlockConfig H T R K₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hTsylH.2.1
  have hTH : T ≤ H := hTsylH.1
  have hminH : MinParabolic H T N := ⟨hTsylH, hTn, hN⟩
  have hTR : T ≤ normalizer (R : Set G) := hTM₀.trans hM₀R
  have hncH : NoCharNormal R H := fun C hCR hC1 hCchar hHC =>
    hNC C hCR hC1 hHC (hM₀R.trans (normalizer_le_normalizer_of_characteristic hCR hCchar))
  obtain ⟨P, H₀, hPKR, hRP, -, -, hminP, -, -, hSsyl, hH₀KS, hSH₀, hH₀N, hminH₀, -,
    hshort, halt, hJ⟩ := exists_pushUp_data hminH hchar hsolv hSQT hR1 hRT hRsyl hTR hncH
  have hsubH := isSubnormal_block hminH hsolv hRT hRsyl hPKR hRP hminP hSsyl hH₀KS hSH₀
  set L := oTwoUpper H₀ with hL
  have hA : IsA4Block L (blockU L) := IsA4Block.of_alt3 hshort halt
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hPH : P ≤ H := hPKR.trans (sup_le hKH (hRT.trans hTH))
  have hH₀H : H₀ ≤ H := (hH₀KS.trans (sup_le (oTwoUpper_le P)
    ((C1GN.baum_le R).trans hRP))).trans hPH
  have hLH : L ≤ H := (oTwoUpper_le H₀).trans hH₀H
  have hB : IsBlock2 H L := ⟨hshort, hLH, hsubH⟩
  have h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := card_quotient_pCore_of_isAltType halt
  have hcommute : ∀ g ∈ H, ∀ g' ∈ H, conjSubgroup L g ≠ conjSubgroup L g' →
      ⁅conjSubgroup L g, conjSubgroup L g'⁆ = ⊥ := fun g hg g' hg' hne =>
    C1Pack.commutator_eq_bot_of_card_three hchar (isBlock2_conjSubgroup hB hg)
      ((card_quotient_pCore_conjSubgroup L g).trans h3) (isBlock2_conjSubgroup hB hg')
      ((card_quotient_pCore_conjSubgroup L g').trans h3) hne
  have hcomm1 : ∀ g ∈ H, conjSubgroup L g ≠ L → ∀ a ∈ L, ∀ b ∈ conjSubgroup L g,
      a * b = b * a := by
    intro g hg hne a ha b hb
    have h1 := hcommute 1 (one_mem H) g hg (by rw [conjSubgroup_one]; exact hne.symm)
    rw [conjSubgroup_one, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    exact ((mem_centralizer_iff.mp (h1 ha)) b hb).symm
  have hLN : ¬ L ≤ N := by
    intro hle
    apply hH₀N
    have hS : baum R ⊔ twoResidual H₀ = H₀ := sup_twoResidual_eq hminH₀.isSylow
    rw [F6.twoResidual_eq_oTwoUpper] at hS
    rw [← hS]
    exact sup_le (((C1GN.baum_le R).trans hRT).trans hminH.le) hle
  set X := ⨆ (g : G) (_ : g ∈ T), conjSubgroup L g with hX
  have hLX : L ≤ X := le_iSup₂_of_le (1 : G) (one_mem T) (by rw [conjSubgroup_one])
  have hXH : X ≤ H := iSup₂_le fun g hg => (isBlock2_conjSubgroup hB (hTH hg)).2.1
  have hTX : T ≤ normalizer (X : Set G) := le_normalizer_iSup_conj L T
  have hXT : X ⊔ T = H := by
    by_contra hne
    have hlt : X ⊔ T < H := lt_of_le_of_ne (sup_le hXH hTH) hne
    exact hLN ((hLX.trans le_sup_left).trans (hminH.le_of_lt le_sup_right hlt))
  have hgen : oTwoUpper H ≤ X := oTwoUpper_le_of_le_sup hXT.ge hT2 hTX
  have hindex : (T ⊓ normalizer (L : Set G)).relIndex T ≤ 2 := by
    by_contra hlt
    push Not at hlt
    set N' : Subgroup T := (T ⊓ normalizer (L : Set G)).subgroupOf T with hN'
    have hcard : 2 < Nat.card (↥T ⧸ N') := hlt
    have : Fintype (↥T ⧸ N') := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hcard
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard
    set ta : T := Quotient.out a
    set tb : T := Quotient.out b
    set tc : T := Quotient.out c
    have hta : (ta : ↥T ⧸ N') = a := Quotient.out_eq a
    have htb : (tb : ↥T ⧸ N') = b := Quotient.out_eq b
    have htc : (tc : ↥T ⧸ N') = c := Quotient.out_eq c
    have hdist : ∀ x y : T, (x : ↥T ⧸ N') ≠ (y : ↥T ⧸ N') →
        conjSubgroup L ((x : G))⁻¹ ≠ conjSubgroup L ((y : G))⁻¹ := by
      intro x y hxy heq
      apply hxy
      rw [QuotientGroup.eq]
      have h1 := congrArg (fun A => conjSubgroup A (y : G)) heq
      simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
      have h2 : ((x⁻¹ * y : T) : G) ∈ normalizer (L : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.mp (by simpa using h1)
      exact mem_subgroupOf.mpr ⟨(x⁻¹ * y).2, h2⟩
    have hab' := hdist ta tb (by rw [hta, htb]; exact hab)
    have hac' := hdist ta tc (by rw [hta, htc]; exact hac)
    have hbc' := hdist tb tc (by rw [htb, htc]; exact hbc)
    have hmemH : ∀ x : T, ((x : G))⁻¹ ∈ H := fun x => inv_mem (hTH x.2)
    set S₃ : Finset (Subgroup G) := {conjSubgroup L ((ta : G))⁻¹, conjSubgroup L ((tb : G))⁻¹,
      conjSubgroup L ((tc : G))⁻¹} with hS₃
    have hS₃card : S₃.card = 3 := Finset.card_eq_three.2 ⟨_, _, _, hab', hac', hbc', rfl⟩
    have hconj : ∀ K ∈ S₃, ∃ x : T, K = conjSubgroup L ((x : G))⁻¹ := by
      intro K hK
      simp only [hS₃, Finset.mem_insert, Finset.mem_singleton] at hK
      rcases hK with rfl | rfl | rfl
      exacts [⟨ta, rfl⟩, ⟨tb, rfl⟩, ⟨tc, rfl⟩]
    obtain ⟨E, hEle, hE, hEcard⟩ := C1GN.exists_elemAbelian_three_pow (fun K : Subgroup G => K)
      S₃
      (fun K hK => by
        obtain ⟨x, rfl⟩ := hconj K hK
        exact (isBlock2_conjSubgroup hB (hmemH x)).1.2.1)
      (fun K hK => by
        obtain ⟨x, rfl⟩ := hconj K hK
        rw [card_conjSubgroup, hA.card_L]
        norm_num)
      (fun K hK K' hK' hne => by
        obtain ⟨x, rfl⟩ := hconj K hK
        obtain ⟨y, rfl⟩ := hconj K' hK'
        exact hcommute _ (hmemH x) _ (hmemH y) hne)
    have hEH : E ≤ H := hEle.trans (iSup₂_le fun K hK => by
      obtain ⟨x, rfl⟩ := hconj K hK
      exact (isBlock2_conjSubgroup hB (hmemH x)).2.1)
    rw [hS₃card] at hEcard
    have h3r := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEH hE hEcard
    have := hSQT 3 Nat.prime_three (by norm_num)
    omega
  have hQU : blockQ L = blockU L :=
    le_antisymm (IsA4Block.le_U_of_isPGroup hA (C1.blockQ_le L)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)) (C1.blockU_le_blockQ hshort)
  have hQH : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ L, k * q * k⁻¹ * q⁻¹ ∈ blockU L := by
    intro q hq k hk
    have hqN : q ∈ normalizer (L : Set G) :=
      (normal_subgroupOf_iff_le_normalizer le_sup_left).mp
        (C1Pack.isBlock2_normal_sup_pCore hB).2 (mem_sup_right hq)
    have h1 : k * q * k⁻¹ * q⁻¹ ∈ L := by
      have : q * k⁻¹ * q⁻¹ ∈ L := (mem_normalizer_iff.mp hqN k⁻¹).mp (inv_mem hk)
      have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
      rw [e]; exact mul_mem hk this
    have h2 : k * q * k⁻¹ * q⁻¹ ∈ pCoreOf 2 H := by
      have : k * q * k⁻¹ ∈ pCoreOf 2 H :=
        (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hk)) q).mp
          hq
      exact mul_mem this (inv_mem hq)
    rw [← hQU, C1Pack.blockQ_eq_inf_pCoreOf hB]
    exact ⟨h1, h2⟩
  set U := ⨆ (g : G) (_ : g ∈ T), conjSubgroup (blockU L) g with hU
  have hUconj : ∀ g : G, conjSubgroup (blockU L) g ≤ conjSubgroup L g := fun g =>
    conjSubgroup_mono hA.le g
  have hXU : X ≤ normalizer (U : Set G) := by
    refine iSup₂_le fun g' hg' => ?_
    intro x hx
    refine mem_normalizer_iSup fun g => mem_normalizer_iSup fun hg => ?_
    by_cases heq : conjSubgroup L g' = conjSubgroup L g
    · rw [heq] at hx
      have h1 := conjSubgroup_mono (IsA4Block.le_normalizer_U hA) g
      rw [C5.conjSubgroup_normalizer] at h1
      exact h1 hx
    · have h1 := hcommute g' (hTH hg') g (hTH hg) heq
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
      refine Subgroup.centralizer_le_normalizer _ ?_
      exact Subgroup.centralizer_le (hUconj g) (h1 hx)
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hXT]; exact sup_le hXU (le_normalizer_iSup_conj (blockU L) T)
  have hCH : T ⊓ centralizer (U : Set G) ≤ pCoreOf 2 H := by
    set Y := H ⊓ centralizer (U : Set G) with hY
    have hYn : H ≤ normalizer (Y : Set G) := fun h hh =>
      mem_normalizer_inf (Subgroup.le_normalizer hh) (mem_normalizer_centralizer (hHU hh))
    rcases hminH.le_kerIn_or_twoResidual_le inf_le_left hYn with hYJ | hKY
    · have hJS := hminH.isSylowTwoOf_pCoreOf_kerIn
      refine le_of_isPGroup_of_normal hJS ?_ ((inf_le_inf_right _ hTH).trans hYJ)
        (hT2.to_le inf_le_left)
      exact hminH.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    · exfalso
      have hLK : L ≤ twoResidual H := by
        rw [F6.twoResidual_eq_oTwoUpper]; exact oTwoUpper_mono hH₀H
      have hUU : blockU L ≤ U := le_iSup₂_of_le (1 : G) (one_mem T) (by rw [conjSubgroup_one])
      obtain ⟨c, hcL, -, -, hcfp, -⟩ := hA.exists_c
      have hcC : c ∈ centralizer (U : Set G) := ((hLK.trans hKY) hcL).2
      obtain ⟨u, huU, hu1⟩ : ∃ u ∈ blockU L, u ≠ 1 := by
        by_contra h
        push Not at h
        have hbot : blockU L = ⊥ := eq_bot_iff.mpr fun u hu => mem_bot.mpr (h u hu)
        have h4 := hA.card_U
        rw [hbot, Subgroup.card_bot] at h4
        norm_num at h4
      apply hcfp u huU hu1
      have h1 : u * c = c * u := (mem_centralizer_iff.mp hcC) u (hUU huU)
      calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [h1]
        _ = u := by group
  refine ⟨L, ⟨hshort, halt, hLH, hJ, ?_, ?_, ?_, hindex, hgen, hQH, hCH⟩⟩
  ·
    have h1 : pCoreOf 2 L ≤ pCoreOf 2 H₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (oTwoUpper_le H₀))
        ((le_normalizer_oTwoUpper H₀).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact (C1.blockU_le_blockQ hshort).trans (h1.trans
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hminH₀.isSylow).trans (C1GN.baum_le R)))
  · intro g hg
    by_cases heq : conjSubgroup L g = L
    · exact Or.inl heq
    · exact Or.inr (hcomm1 g (hTH hg) heq)
  · intro g hg hne
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    refine hA.center_L x hx.1 fun l hl => ?_
    exact (hcomm1 g (hTH hg) hne l hl x hx.2).symm


theorem blockConfig_exists_good_elt {H T R K₁ M₀ : Subgroup G} (hcfg : BlockConfig H T R K₁)
    (hNC : NoCommonNormal R H M₀) (hT : IsSylowTwoOf T M₀) (hM₀R : M₀ ≤ normalizer (R : Set G))
    (hRT : R ≤ T) (hTH : T ≤ H) (hH : H ≤ oTwoUpper H ⊔ T) :
    ¬ T ≤ normalizer (K₁ : Set G) ∧ ∃ x ∈ M₀,
      x ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) ∧
      ¬ conjSubgroup (blockU K₁) x ≤ centralizer (blockU K₁ : Set G) := by
  have hT2 : IsPGroup 2 T := hT.2.1
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  obtain ⟨hUS, hSK, hSnt⟩ := hcfg.baum_facts hR2 hRT
  have hS2 : IsPGroup 2 (baum R) := hR2.to_le inf_le_left
  have hM₀S : M₀ ≤ normalizer ((baum R : Subgroup G) : Set G) :=
    hM₀R.trans (normalizer_le_normalizer_baum R)
  obtain ⟨y, hyM₀, hyU⟩ := hcfg.exists_conj_not_le_centralizer hNC hT.1 hM₀R hRT hTH hH hT2
  obtain ⟨W, hP⟩ := pairData_of_block hcfg.isA4 hcfg.short hS2 hUS hSK hSnt (hM₀S hyM₀) hyU
  exact C58NS.exists_good_elt_of_hor hT hM₀S hcfg.index rfl rfl hP.hQ hUS hyM₀
    hP.mem_normalizer_sqSub hP.hx1 (fun m hm => hP.mem_or_mem (hM₀S hm.1) hm.2)
    (fun g hg => hP.conj_D_le (hM₀S hg.1) hg.2)

end CFSG.Quasithin.H13.Ch4.C53
