module

public import CFSG.Quasithin.Vol2.Ch3xC58NSInputs
public import CFSG.Quasithin.Background.C58Blocks
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.Quasithin.Background.C118NoOuter
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.Quasithin.Vol2.Ch3xC58NSGamma

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.C58 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_alt3 {K : Subgroup G} (h : IsAltType K 3) : Group.IsSolvable ↥K := by
  obtain ⟨α, -, hker, -⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  have : Group.IsSolvable ↥(alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥K).subtype α
    (by rw [hker, Subgroup.range_subtype])

theorem exists_blockConfigNS (h126 : TheoremC126) (hMPB : MinParabolicBlockSubnormal)
    {T H R M₀ N : Subgroup G} (hTsylH : IsSylowTwoOf T H) (hchar : CharTwo H)
    (hSQ : IsSQTKTC H) (hN : IsUniqueMaxOver H T N) (hTn : ¬ H ≤ normalizer (T : Set G))
    (hnsolv : ¬ Group.IsSolvable H) (hR1 : R ≠ ⊥) (hRT : R ≤ T)
    (hRsyl : IsSylowTwoOf R (oTwoUpper H ⊔ R)) (hTM₀ : T ≤ M₀)
    (hM₀R : M₀ ≤ normalizer (R : Set G)) (hNC : NoCommonNormal R H M₀) :
    ∃ K₁ : Subgroup G, BlockConfigNS H T R K₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hTsylH.2.1
  have hTH : T ≤ H := hTsylH.1
  have hminH : MinParabolic H T N := ⟨hTsylH, hTn, hN⟩
  have hTR : T ≤ normalizer (R : Set G) := hTM₀.trans hM₀R
  have hncH : NoCharNormal R H := fun C hCR hC1 hCchar hHC =>
    hNC C hCR hC1 hHC (hM₀R.trans (normalizer_le_normalizer_of_characteristic hCR hCchar))
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]; exact sup_twoResidual_eq hTsylH
  obtain ⟨P, hPKR, hRP, hPN, hRsylP, hRnP, hPmax, -, -, hncP⟩ :=
    minimal_parabolic_subgroup_over_normal_Sylow_part (p := 2) hTsylH hminH.maximal.1 hminH.le
      (fun Y hTY hYH => hminH.le_of_lt hTY hYH) hKH (le_normalizer_oTwoUpper H) hKT
      (hasNoTwoQuotient_oddOrderSubgroup H) hR1 hRT hTR hRsyl hncH
  have hminP : MinParabolic P R (P ⊓ N) := minParabolic_of_select hRsylP hRnP hPmax
  have hPH : P ≤ H := hPKR.trans (sup_le hKH (hRT.trans hTH))
  have hKRn : H ≤ normalizer ((oTwoUpper H ⊔ R : Subgroup G) : Set G) := by
    calc H = oTwoUpper H ⊔ T := hKT.symm
      _ ≤ _ := sup_le (le_sup_left.trans Subgroup.le_normalizer)
        (fun t ht => C1.mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTR ht))
  have hcharKR : CharTwo (oTwoUpper H ⊔ R) :=
    A4.charTwo_of_normal (sup_le hKH (hRT.trans hTH)) hKRn hchar
  have hcharP : CharTwo P := C1GN.charTwo_of_le hcharKR hRsyl hRP.le hPKR
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  obtain ⟨h1ne, h1Z, h1char, h2ne, h2B, h2char, -⟩ := hC.pair R hR2 hR1
  rcases h126 G C₁ C₂ hC P R (C1GN.IsSQTKTC.mono hPH hSQ) hminP.isSylow hcharP
      (minParabolic_iff.mp hminP).1 with h1 | h2 | ⟨r, K, hr, hK, -, hres, hperm, htrans⟩
  · exfalso
    refine hncP (C₁ R) (h1Z.trans (C1GN.omegaOneCenterOf_le_self R)) h1ne h1char ?_
    have hPC : P ≤ centralizer (C₁ R : Set G) :=
      Subgroup.le_centralizer_iff.mpr (h1.trans inf_le_right)
    exact hPC.trans (Subgroup.centralizer_le_normalizer _)
  · exfalso
    exact hncP (C₂ R) (h2B.trans (C1GN.baum_le R)) h2ne
      (C1GN.characteristic_subgroupOf_trans (C1GN.baum_le R) h2B (C1GN.characteristic_baum R)
        h2char) h2
  set i₀ : Fin r := ⟨0, hr⟩ with hi₀
  set L := K i₀ with hL
  have hblkP : IsChi0Block P L := (hK i₀).1
  have hJ : ⁅L, thompsonJ R⁆ = L := (hK i₀).2
  have hPeq : P = R ⊔ conjClosure L R := by
    rw [hL, C1GN.conjClosure_eq_iSup K hperm htrans i₀, ← hres]
    exact (sup_twoResidual_eq hminP.isSylow).symm
  have hB : IsBlock2 H L :=
    hMPB G H T N R P L hminH hchar hSQ hnsolv hRT hTR hRsyl hPKR hRP.le hPN hminP hncH hblkP hJ
      hPeq
  have hshort : IsShort2 L := hB.1
  have hLH : L ≤ H := hB.2.1
  have hLchi : IsChiBlock H L := C1GN.isChiBlock_of_isChi0Block hB hblkP
  have h3 : 3 ∣ Nat.card L := C1GN.three_dvd_card_of_isChiBlock hLchi
  have hcommute : ∀ g ∈ H, ∀ g' ∈ H, conjSubgroup L g ≠ conjSubgroup L g' →
      ⁅conjSubgroup L g, conjSubgroup L g'⁆ = ⊥ := fun g hg g' hg' hne =>
    distinctBlocksCommuteStatement (G := G) H _ _ hchar (isBlock2_conjSubgroup hB hg)
      (isBlock2_conjSubgroup hB hg') hne
  have hcomm1 : ∀ g ∈ H, conjSubgroup L g ≠ L → ∀ a ∈ L, ∀ b ∈ conjSubgroup L g,
      a * b = b * a := by
    intro g hg hne a ha b hb
    have h1 := hcommute 1 (one_mem H) g hg (by rw [conjSubgroup_one]; exact hne.symm)
    rw [conjSubgroup_one, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    exact ((mem_centralizer_iff.mp (h1 ha)) b hb).symm
  have hLN : ¬ L ≤ N := by
    intro hle
    apply hPN
    rw [hPeq]
    refine sup_le (hRT.trans hminH.le) (conjClosure_le fun r hr x hx => ?_)
    have h1 : r * x * r⁻¹ ∈ N :=
      (mem_normalizer_iff.mp (Subgroup.le_normalizer (hminH.le (hRT hr))) x).mp (hle hx)
    exact h1
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
        rw [card_conjSubgroup]
        exact h3)
      (fun K hK K' hK' hne => by
        obtain ⟨x, rfl⟩ := hconj K hK
        obtain ⟨y, rfl⟩ := hconj K' hK'
        exact hcommute _ (hmemH x) _ (hmemH y) hne)
    have hEH : E ≤ H := hEle.trans (iSup₂_le fun K hK => by
      obtain ⟨x, rfl⟩ := hconj K hK
      exact (isBlock2_conjSubgroup hB (hmemH x)).2.1)
    rw [hS₃card] at hEcard
    have h3r := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEH hE hEcard
    have := C1Pack.pRank_le_two_of_isSQTKTC hSQ 3 Nat.prime_three (by norm_num)
    omega
  have htyp : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5 := by
    rcases hblkP.2 with h | h3' | h5
    · exact Or.inl h
    · exfalso
      apply hnsolv
      have hLs : Group.IsSolvable ↥L := isSolvable_of_alt3 h3'
      have hXs : Group.IsSolvable ↥X := by
        by_cases hTL : T ≤ normalizer (L : Set G)
        · have hXL : X ≤ L := iSup₂_le fun g hg => by
            rw [conjSubgroup_eq_iff_mem_normalizer.mpr (hTL hg)]
          exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXL)
        · obtain ⟨t, htT, htL⟩ := IsConcreteLE.not_le_iff_exists.mp hTL
          have hidx2 : (T ⊓ normalizer (L : Set G)).relIndex T = 2 := by
            have h1 : (T ⊓ normalizer (L : Set G)).relIndex T ≠ 1 := fun h =>
              htL (((Subgroup.relIndex_eq_one.mp h).trans inf_le_right) htT)
            have h0 : (T ⊓ normalizer (L : Set G)).relIndex T ≠ 0 :=
              Subgroup.index_ne_zero_of_finite (H := (T ⊓ normalizer (L : Set G)).subgroupOf T)
            omega
          have hidxT : ((T ⊓ normalizer (L : Set G)).subgroupOf T).index = 2 := hidx2
          have hLt : conjSubgroup L t ≠ L := fun h =>
            htL (conjSubgroup_eq_iff_mem_normalizer.mp h)
          have hcommt := hcomm1 t (hTH htT) hLt
          have hXLt : X ≤ L ⊔ conjSubgroup L t := by
            refine iSup₂_le fun g hg => ?_
            by_cases hgL : g ∈ normalizer (L : Set G)
            · rw [conjSubgroup_eq_iff_mem_normalizer.mpr hgL]; exact le_sup_left
            · have hgt : g * t⁻¹ ∈ normalizer (L : Set G) := by
                have := (Subgroup.mul_mem_iff_of_index_two hidxT (a := ⟨g, hg⟩)
                  (b := ⟨t⁻¹, inv_mem htT⟩)).mpr
                simp only [mem_subgroupOf, coe_mul, mem_inf] at this
                refine (this (iff_of_false (fun h => hgL h.2)
                  (fun h => htL (by simpa using inv_mem h.2)))).2
              have e : g = (g * t⁻¹) * t := by group
              rw [e, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hgt]
              exact le_sup_right
          have hLtN : conjSubgroup L t ≤ normalizer (L : Set G) :=
            le_normalizer_of_commute fun a ha b hb => (hcommt b hb a ha).symm
          have hLts : Group.IsSolvable ↥(conjSubgroup L t) := by
            have e : conjSubgroup L t = L.map (MulAut.conj t⁻¹).toMonoidHom := by
              ext y
              simp only [mem_conjSubgroup_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
                inv_inv]
            rw [e]
            exact Group.isSolvable_of_isSolvable_injective
              (f := ((L.equivMapOfInjective _ (MulAut.conj t⁻¹).injective).symm.toMonoidHom))
              (MulEquiv.injective _)
          have hsup := CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hLtN hLs hLts
          exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXLt)
      have hTs : Group.IsSolvable ↥T := by
        have := hT2.isNilpotent
        infer_instance
      have hXTs := CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hTX hXs hTs
      rw [hXT] at hXTs
      exact hXTs
    · exact Or.inr h5
  have hQH : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ L, k * q * k⁻¹ * q⁻¹ ∈ blockU L := by
    intro q hq k hk
    have hqN : q ∈ normalizer (L : Set G) :=
      (normal_subgroupOf_iff_le_normalizer le_sup_left).mp
        (C1Pack.isBlock2_normal_sup_pCore hB).2 (mem_sup_right hq)
    have hy : ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ blockQ L := by
      intro l hl
      rw [C1Pack.blockQ_eq_inf_pCoreOf hB]
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem ((mem_normalizer_iff.mp hqN l).mp hl) (inv_mem hl), ?_⟩
      have : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 H :=
        (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hl))
          q⁻¹).mp (inv_mem hq)
      have e : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
      rw [e]; exact mul_mem hq this
    have h1 := C1.commutator_mem_blockU_of_mem_blockQ hshort hy k hk
    have e : k * q * k⁻¹ * q⁻¹ = (q * k * q⁻¹ * k⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem h1
  set U := ⨆ (g : G) (_ : g ∈ T), conjSubgroup (blockU L) g with hU
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hshort).trans (C1.blockQ_le L)
  have hUconj : ∀ g : G, conjSubgroup (blockU L) g ≤ conjSubgroup L g := fun g =>
    conjSubgroup_mono hUL g
  have hXU : X ≤ normalizer (U : Set G) := by
    refine iSup₂_le fun g' hg' => ?_
    intro x hx
    refine mem_normalizer_iSup fun g => mem_normalizer_iSup fun hg => ?_
    by_cases heq : conjSubgroup L g' = conjSubgroup L g
    · rw [heq] at hx
      have h1 := conjSubgroup_mono (C1.le_normalizer_blockU L) g
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
        rw [F6.twoResidual_eq_oTwoUpper, C1Pack.isShort2_eq_oTwoUpper hshort]
        exact oTwoUpper_mono hLH
      have hUU : blockU L ≤ U := le_iSup₂_of_le (1 : G) (one_mem T) (by rw [conjSubgroup_one])
      have hLC : L ≤ centralizer (blockU L : Set G) :=
        ((hLK.trans hKY).trans inf_le_right).trans (Subgroup.centralizer_le hUU)
      apply (lt_iff_le_not_ge.mp hshort.2.2.2.2.1).2
      calc blockU L = ⁅blockU L, L⁆ := (C1.commutator_blockU hshort).symm
        _ ≤ blockZ L := by
          rw [Subgroup.commutator_le]
          intro u hu k hk
          have hku : u * k = k * u := (mem_centralizer_iff.mp (hLC hk)) u hu
          have e : ⁅u, k⁆ = 1 := by
            rw [commutatorElement_def, hku]; group
          rw [e]; exact one_mem _
  refine ⟨L, ⟨hshort, htyp, hLH, hJ, ?_, ?_, ?_, hindex, hgen, hQH, hCH⟩⟩
  ·
    have hBP : IsBlock2 P L := hblkP.1
    have h1 : blockQ L ≤ pCoreOf 2 P := by
      rw [C1Pack.blockQ_eq_inf_pCoreOf hBP]; exact inf_le_right
    exact (C1.blockU_le_blockQ hshort).trans
      (h1.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hminP.isSylow))
  · exact RankOneRecog.isSylowTwoOf_inf_of_subnormal hTsylH hLH hB.2.2
  · intro g hg
    by_cases heq : conjSubgroup L g = L
    · exact Or.inl heq
    · exact Or.inr (hcomm1 g (hTH hg) heq)

end CFSG.Quasithin.C58NS
