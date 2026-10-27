module

public import CFSG.Quasithin.H13.L32NLem14331m
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_le_of_mem_cComp {I G₁ G₂ X : Subgroup G}
    (htriple : F6.IsGoldschmidtTripleIn I G₁ G₂) (hXI : X ≤ I)
    (eX : Nonempty (↥X ⧸ CFSG.Open.pCore 2 ↥X ≃* Equiv.Perm (Fin 3)))
    {K₀ : Subgroup ↥I} (hK₀ : K₀ ∈ cComp (⊤ : Subgroup ↥I))
    (hK₀O : K₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) =
      oTwoUpper (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))) :
    oTwoUpper X ≤ K₀.map I.subtype := by
  obtain ⟨eX⟩ := eX
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxX, hxo⟩
  have hx3 := L14331.pow_three_of_odd_sub eX hxX hxo
  have hxI := hXI hxX
  have hx3' : (⟨x, hxI⟩ : ↥I) ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using hx3)
  have hπ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) ⟨x, hxI⟩ ∈
      K₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) := by
    rw [hK₀O]
    refine mem_oTwoUpper_of_odd (Subgroup.mem_top _)
      (Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ?_))
    rw [← map_pow, show (⟨x, hxI⟩ : ↥I) ^ 3 = 1 by simpa using hx3', map_one]
  exact ⟨⟨x, hxI⟩, A5.mem_of_pow_three_of_mem_map htriple.isSolvable_pPrimeCore hK₀ hx3' hπ, rfl⟩

theorem simple_quot_of_faithful {T L : Subgroup G} (h1434 : Lemma1434One)
    (hyp : Hyp14_3_1One G T L) {I : Subgroup G} {K₀ : Subgroup ↥I}
    (hf : quasithinIsFaithfulLocal T (K₀.map I.subtype)) :
    IsSimpleGroup (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) ∧
      (Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) = 60 ∨
        Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) = 168) := by
  set K₀G := K₀.map I.subtype with hK₀G
  set ι : ↥K₀ ≃* ↥K₀G := K₀.equivMapOfInjective _ I.subtype_injective with hι
  have hιp : (CFSG.Open.pCore 2 ↥K₀).map ι.toMonoidHom = CFSG.Open.pCore 2 ↥K₀G :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ι
  set q : ↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀ ≃* ↥K₀G ⧸ CFSG.Open.pCore 2 ↥K₀G :=
    QuotientGroup.congr _ _ ι hιp with hq
  set r : ↥K₀G ⧸ CFSG.pCore 2 ↥K₀G ≃* ↥K₀G ⧸ CFSG.Open.pCore 2 ↥K₀G :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 _)
    with hr
  rcases h1434 G T L hyp K₀G hf with h5 | h3
  · obtain ⟨e5⟩ := h5
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have e' := (q.trans r.symm).trans e5
    refine ⟨(MulEquiv.isSimpleGroup_congr e').mpr this, Or.inl ?_⟩
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    try rfl
  · obtain ⟨eL⟩ := nonempty_equiv_SL32_of_lieModel h3
    have e' := (q.trans r.symm).trans eL
    refine ⟨(MulEquiv.isSimpleGroup_congr (q.trans r.symm)).mpr
      (L14331.isSimpleGroup_of_lieModel_psl32 h3), Or.inr ?_⟩
    rw [Nat.card_congr e'.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three]

theorem three_mul_card_eq_of_quasisimple {T L : Subgroup G} (h1434 : Lemma1434One)
    (hyp : Hyp14_3_1One G T L) (hQ : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    {I G₁ G₂ : Subgroup G} (htriple : F6.IsGoldschmidtTripleIn I G₁ G₂) (hTG : G₁ ⊓ G₂ = T)
    (hI2 : pCoreOf 2 I ≠ ⊥)
    (hZ : ∀ K : Subgroup G, K ≤ I → I ≤ Subgroup.normalizer (K : Set G) →
      ⁅quasithinOmegaOneCenter T, K⁆ = ⊥ → IsPGroup 2 ↥K)
    (hq : CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))))
    (h60 : ∀ b : ℕ,
      Nat.card ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I))) ≠ 60 * 2 ^ b)
    (hAm : IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) :
    3 * Nat.card ↥I = 21 * Nat.card ↥G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) with hπ
  set Y := CFSG.pPrimeCore 3 ↥I with hY
  set g1 := (G₁.subgroupOf I).map π with hg1
  set g2 := (G₂.subgroupOf I).map π with hg2
  have hO2n : (oTwoUpper (⊤ : Subgroup (↥I ⧸ Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_oTwoUpper ⊤))
  have hKbc : oTwoUpper (⊤ : Subgroup (↥I ⧸ Y)) ∈ cComp (⊤ : Subgroup (↥I ⧸ Y)) :=
    mem_cComp_top_of_isComponent ⟨hq, hO2n.isSubnormal⟩
  obtain ⟨K₀, hK₀, hK₀O⟩ := (cComp_quotient_bijOn Y htriple.isSolvable_pPrimeCore).2.2 hKbc
  have hK₀n : K₀.Normal :=
    L14331.normal_of_mem_cComp htriple.isSolvable_pPrimeCore hK₀ (hK₀O ▸ hO2n)
  set K₀G := K₀.map I.subtype with hK₀G
  have hG₁I : G₁ ≤ I := htriple.1 ▸ le_sup_left
  have hG₂I : G₂ ≤ I := htriple.1 ▸ le_sup_right
  have hTG₁ : T ≤ G₁ := hTG ▸ inf_le_left
  have hTG₂ : T ≤ G₂ := hTG ▸ inf_le_right
  have hTI : T ≤ I := hTG₁.trans hG₁I
  have hG10 := oTwoUpper_le_of_mem_cComp htriple hG₁I htriple.2.1 hK₀ hK₀O
  have hG20 := oTwoUpper_le_of_mem_cComp htriple hG₂I htriple.2.2.1 hK₀ hK₀O
  have hIN : I ≤ Subgroup.normalizer (K₀G : Set G) := by
    intro t htI
    refine L14328.mem_normalizer_of_maps fun w hw => ?_
    obtain ⟨w', hw', rfl⟩ := hw
    exact ⟨⟨t, htI⟩ * w' * ⟨t, htI⟩⁻¹, hK₀n.conj_mem w' hw' _, rfl⟩
  have hZK : ⁅quasithinOmegaOneCenter T, K₀G⁆ ≠ ⊥ := by
    intro hb
    have hp := hZ K₀G (Subgroup.map_subtype_le K₀) hIN hb
    have hp' : IsPGroup 2 ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ Y))) := by
      rw [← hK₀O]
      exact (hp.of_equiv (K₀.equivMapOfInjective _ I.subtype_injective).symm).map π
    have : Group.IsNilpotent ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ Y))) := hp'.isNilpotent
    have : Nontrivial ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ Y))) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ Y))) := hq.1
    exact Group.IsPerfect.not_isNilpotent _ ‹_›
  have hsylI : IsSylowTwoOf T I := isSylowTwoOf_of_quasithinIsSylowTwo hT hTI
  have hL₀c := map_subtype_mem_cComp hK₀
  have hloc := isLocal_of_mem_cComp_of_sylow hsylI hI2 hL₀c
  have hf := Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter hQ hT hloc hZK
  obtain ⟨hs, hcard⟩ := simple_quot_of_faithful h1434 hyp hf
  have h3dvd : 3 ∣ Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) := by
    rcases hcard with h | h <;> rw [h] <;> norm_num
  have hT2 : IsPGroup 2 ↥T := hT.1
  have hTN : T ≤ Subgroup.normalizer (K₀G : Set G) := hTI.trans hIN
  have hIle : I ≤ K₀G ⊔ T := by
    have hG1' : G₁ = oTwoUpper G₁ ⊔ T :=
      eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_quasithinIsSylowTwo hT hTG₁)
    have hG2' : G₂ = oTwoUpper G₂ ⊔ T :=
      eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_quasithinIsSylowTwo hT hTG₂)
    rw [← htriple.1]
    refine sup_le ?_ ?_
    · rw [hG1']
      exact sup_le_sup_right hG10 T
    · rw [hG2']
      exact sup_le_sup_right hG20 T
  have hle := L14331.subgroupOf_le_pCore_of_simple CFSG.pPrimeCore_coprime_card K₀ hs h3dvd
  have hY2 : IsPGroup 2 ↥Y := by
    have hodd : ∀ y' ∈ Y, Odd (orderOf y') → y' = 1 := by
      intro y' hy' hyo
      have hyo' : Odd (orderOf (y' : G)) := by rwa [Subgroup.orderOf_coe]
      obtain ⟨y'', hy'', hy''e⟩ :=
        L14331.mem_of_odd_of_mem_sup hT2 hTN (hIle y'.2) hyo' (pow_orderOf_eq_one _)
      have hyy : y'' = y' := Subtype.ext hy''e
      subst hyy
      have hmem : (⟨y'', hy''⟩ : ↥K₀) ∈ Y.subgroupOf K₀ := hy'
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K₀) 2 ⟨_, hle hmem⟩
      have hn' : y'' ^ 2 ^ n = 1 := by
        have := congrArg (fun x => ((x : ↥K₀) : ↥I)) (congrArg Subtype.val hn)
        simpa using this
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hyo)) (orderOf_dvd_of_pow_eq_one hn')
        dvd_rfl)
    intro y'
    obtain ⟨n, hn⟩ := L14331.exists_two_pow_of_odd hodd y'.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hYO : Y ≤ CFSG.Open.pCore 2 ↥I := CFSG.LieType.BorelTits.le_pCore 2 inferInstance hY2
  have hYG₁ : Y ≤ G₁.subgroupOf I := by
    intro y hy
    have := hYO hy
    rw [← F6.inf_pPrimeCore_eq_pCore_left htriple.subgroupOf] at this
    exact this.1
  obtain ⟨b', hb'⟩ := L14331.card_map_of_simple CFSG.pPrimeCore_coprime_card K₀ hs h3dvd
  rw [hK₀O] at hb'
  have hcard168 : Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) = 168 := by
    rcases hcard with h | h
    · exact absurd (by rw [hb', h]) (h60 b')
    · exact h
  have hO : Nat.card ↥(oTwoUpper (⊤ : Subgroup (↥I ⧸ Y))) = 21 * 2 ^ (b' + 3) := by
    rw [hb', hcard168, pow_add]
    ring
  obtain ⟨S, hS⟩ := hAm.sylow
  have hS2 : IsPGroup 2 ↥(g1 ⊓ g2) := hS ▸ S.isPGroup'
  have hSi : ¬ 2 ∣ (g1 ⊓ g2).index := hS ▸ S.not_dvd_index
  have hsyl : IsSylowTwoOf (g1 ⊓ g2) ⊤ :=
    ⟨le_top, hS2, by rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right]⟩
  have hDsup : oTwoUpper (⊤ : Subgroup (↥I ⧸ Y)) ⊔ (g1 ⊓ g2) = ⊤ :=
    (eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl).symm
  have hD := L14331.card_eq_odd_mul hO2n hS2 hSi hDsup (by decide : Odd 21) hO
  have hG1 : Nat.card ↥g1 = 3 * Nat.card ↥(g1 ⊓ g2) := by
    have h1 := hAm.toIsGoldschmidtTriple.relIndex_inf_left
    have h2 := Subgroup.relIndex_mul_card (g1 ⊓ g2) g1
    rw [h1, inf_of_le_left inf_le_left] at h2
    exact h2.symm
  have hIc : Nat.card ↥I = Nat.card (↥I ⧸ Y) * Nat.card ↥Y :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Y
  have hG1c : Nat.card ↥G₁ = Nat.card ↥g1 * Nat.card ↥Y := by
    rw [hg1, F6.card_map_mk, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hG₁I).toEquiv,
      ← Subgroup.relIndex_mul_card Y (G₁.subgroupOf I), inf_of_le_left hYG₁]
  rw [hG1c, hIc, hD, hG1]
  ring

end CFSG.Quasithin.H13.L32A
