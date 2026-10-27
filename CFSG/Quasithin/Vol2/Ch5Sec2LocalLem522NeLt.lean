module

public import CFSG.Quasithin.Vol2.Ch6Conj
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Two
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeSteps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Transport

variable {G : Type} [Group G] [Finite G]

theorem Hyp5_1_8.conj_of_mem {T M L H : Subgroup G} {n : ℕ} (h : Hyp5_1_8 G T M L H n)
    {m : G} (hmM : m ∈ M) :
    Hyp5_1_8 G (T.map (MulAut.conj m).toMonoidHom) M L (H.map (MulAut.conj m).toMonoidHom) n := by
  set φ : G ≃* G := MulAut.conj m with hφ
  have hM : M.map φ.toMonoidHom = M :=
    map_conj_eq_of_mem_normalizer_ch6 (Subgroup.le_normalizer hmM)
  have hL : L.map φ.toMonoidHom = L := map_conj_eq_of_mem_normalizer_ch6 (h.normal hmM)
  have hloc := quasithinIsLocal_map φ h.maximal.1
  rw [hL] at hloc
  refine
    { simple := h.simple
      nonabelian := h.nonabelian
      qtke := h.qtke
      sylow := ⟨h.sylow.1.map φ.toMonoidHom, ?_⟩
      maxTwoLocal := h.maxTwoLocal
      T_le := ?_
      maximal := ?_
      faithful := ⟨hloc, h.faithful.2⟩
      L_le := h.L_le
      normal := h.normal
      two_le := h.two_le
      lie := h.lie
      hStar := ?_
      lieQuot := ?_ }
  · rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    exact h.sylow.2
  · rw [← hM]
    exact Subgroup.map_mono h.T_le
  · have := quasithinIsMaximalLocal_map φ h.maximal
    rwa [hL] at this
  · have := isHStar_map φ h.hStar
    rwa [hM] at this
  · obtain ⟨K, hK, hKq⟩ := h.lieQuot
    exact ⟨K.map φ.toMonoidHom, cComp_map_mulEquiv φ hK, hKq.map_mulEquiv φ⟩

omit [Finite G] in
theorem IsCh5Module.conj_of_mem {T L V : Subgroup G} (hV : IsCh5Module T L V) {m : G}
    (hmL : m ∈ Subgroup.normalizer (L : Set G)) :
    IsCh5Module (T.map (MulAut.conj m).toMonoidHom) L (V.map (MulAut.conj m).toMonoidHom) := by
  set φ : G ≃* G := MulAut.conj m with hφ
  have hL : L.map φ.toMonoidHom = L := map_conj_eq_of_mem_normalizer_ch6 hmL
  have hLT : (L ⊔ T).map φ.toMonoidHom = L ⊔ T.map φ.toMonoidHom := by
    rw [Subgroup.map_sup, hL]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLT]
    exact Subgroup.map_mono hV.1
  · let ψ : ↥(L ⊔ T) ≃* ↥(L ⊔ T.map φ.toMonoidHom) :=
      (φ.subgroupMap (L ⊔ T)).trans (MulEquiv.subgroupCongr hLT)
    have hred := isPrimeReduced_map ψ hV.2.1
    have hmap : (V.subgroupOf (L ⊔ T)).map ψ.toMonoidHom =
        (V.map φ.toMonoidHom).subgroupOf (L ⊔ T.map φ.toMonoidHom) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hyLT : y ∈ L ⊔ T := by
          have hx2 : (x : G) ∈ (L ⊔ T).map φ.toMonoidHom := by rw [hLT]; exact x.2
          obtain ⟨z, hz, hzx⟩ := hx2
          have : z = y := φ.injective (hzx.trans hyx.symm)
          rw [← this]
          exact hz
        exact ⟨⟨y, hyLT⟩, hy, Subtype.ext hyx⟩
    rw [← hmap]
    exact hred
  · intro h0
    apply hV.2.2
    have hc : (⁅V, L⁆).map φ.toMonoidHom = ⁅V.map φ.toMonoidHom, L⁆ := by
      rw [Subgroup.map_commutator, hL]
    rw [← hc] at h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h0

end Transport

namespace Hyp5_2_2p

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}

theorem false_of_lieModel_PSL2 (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
    (h38 : Vol2Native.A38ForSQTKCat) (hL₂K : L₂ < oTwoUpper H) {f : ℕ} (hf : 2 ≤ f)
    (hK4 : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, hK1eq, -⟩
  · obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hK₁ hKeq hL₂K
    have hsup : oTwoUpper H = L₂ ⊔ K₂ := tc.sup
    set K := oTwoUpper H with hKdef
    have hL₂Kle : L₂ ≤ K := hL₂K.le
    have hK₂K : K₂ ≤ K := by rw [hsup]; exact le_sup_right
    have hKN : K ≤ Subgroup.normalizer (L₂ : Set G) := by
      rw [hsup]
      exact sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hK₁ tc.cK₂)
    have hKperf : ⁅K, K⁆ = K := by
      apply le_antisymm
      · rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
      · calc K = L₂ ⊔ K₂ := hsup
          _ = ⁅L₂, L₂⁆ ⊔ ⁅K₂, K₂⁆ := by rw [hK₁.2.1, tc.cK₂.2.1]
          _ ≤ ⁅K, K⁆ := sup_le (Subgroup.commutator_mono hL₂Kle hL₂Kle)
              (Subgroup.commutator_mono hK₂K hK₂K)
    have hsimple : IsSimpleGroup (O2Q K) := isSimpleGroup_of_lieModel_PSL2 hK4
    have hn : (modO2Image K L₂).Normal :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hL₂Kle).mpr hKN).map _
        (QuotientGroup.mk'_surjective _)
    rcases hsimple.eq_bot_or_eq_top_of_normal (modO2Image K L₂) with h0 | h0
    ·
      have hle : L₂.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
        intro x hx
        have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈ modO2Image K L₂ := ⟨x, hx, rfl⟩
        rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
        exact hx'
      have h2 : IsPGroup 2 ↥(L₂.subgroupOf K) := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).to_le hle
      have h2' : IsPGroup 2 ↥L₂ := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hL₂Kle)
      exact hK₁.1 (Vol2Native.eq_bot_of_perfect_of_isPGroup L₂ h2' hK₁.2.1)
    ·
      have hle := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top hL₂Kle h0
      have hOK : pCoreOf 2 K ≤ Subgroup.normalizer (L₂ : Set G) := (pCoreOf_le 2 K).trans hKN
      exact hL₂K.ne (le_antisymm hL₂Kle
        (le_of_perfect_of_le_sup hKperf hle (pCoreOf_isPGroup 2 K) hOK))
  · apply hnb
    rw [hK1eq]
    exact ⟨f, hf, Or.inl hK4⟩

theorem false_of_lieModel_two (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
    (h38 : Vol2Native.A38ForSQTKCat) (hL₂K : L₂ < oTwoUpper H)
    (hK4 : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2) : False :=
  hyp.false_of_lieModel_PSL2 h38 hL₂K le_rfl hK4

end Hyp5_2_2p

theorem stmt5_2_2_ne_lt_of (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (h515 : Stmt5_1_5) (h5113 : Stmt5_1_13C) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) : Stmt5_2_2_ne_lt := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO hOX hHX hT₀ hL₂K hDp T₁ hT₁ hlt hT₁syl hT₁M hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  set K := oTwoUpper H with hKdef
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTY : IsSylowTwoOf T (T ⊔ T₁) := h.isSylowTwoOf le_sup_left
  have hT₁Y : IsSylowTwoOf T₁ (T ⊔ T₁) := isSylowTwoOf_of_isSylowTwo hT₁syl le_sup_right
  obtain ⟨y, hyY, hy⟩ := A4.exists_conj_of_isSylowTwoOf hTY hT₁Y
  have hT₁eq : T.map (MulAut.conj y).toMonoidHom = T₁ := by
    ext x
    rw [hy x, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have e : y⁻¹ * ((MulAut.conj y).toMonoidHom t) * y = t := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact ht
    · intro hx
      exact ⟨y⁻¹ * x * y, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hTKN : T ≤ Subgroup.normalizer (K : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hT₁KN : T₁ ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK]
    exact le_normalizer_conjClosure L₂ T₁
  have hyM : y ∈ M := (sup_le h.T_le hT₁M) hyY
  have hyK : K.map (MulAut.conj y).toMonoidHom = K :=
    map_conj_eq_of_mem_normalizer_ch6 ((sup_le hTKN hT₁KN) hyY)
  set H₀ := H.map (MulAut.conj y).toMonoidHom with hH₀def
  have hyp₁ : Hyp5_1_8 G T₁ M L H₀ n := hT₁eq ▸ hyp.toHyp5_1_8.conj_of_mem hyM
  have hKH₀ : oTwoUpper H₀ = K := by rw [hH₀def, oTwoUpper_map, ← hKdef, hyK]
  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts h510 h331 hR
  have hTLT₀ : T ⊓ L ≤ T₀ := by
    intro x hx
    have hxS : x ∈ S ⊓ L := by
      rw [hSL]
      exact hx
    exact ⟨hx.1, hyp.S_le hxS.1⟩
  have hTL₁ : T₁ ⊓ L = T ⊓ L := by
    have hle : T ⊓ L ≤ T₁ ⊓ L := le_inf (hTLT₀.trans hlt.le) inf_le_right
    have hyL : y ∈ Subgroup.normalizer (L : Set G) := h.normal hyM
    have hcard : Nat.card ↥(T₁ ⊓ L) = Nat.card ↥(T ⊓ L) := by
      have e : (T ⊓ L).map (MulAut.conj y).toMonoidHom = T₁ ⊓ L := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj y).injective, hT₁eq,
          map_conj_eq_of_mem_normalizer_ch6 hyL]
      rw [← e, Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hD₁ : Lin2.IsHallTwoPrimeOf D (borelL T₁ L) := by
    show Lin2.IsHallTwoPrimeOf D (L ⊓ Subgroup.normalizer ((T₁ ⊓ L : Subgroup G) : Set G))
    rw [hTL₁]
    exact hyp.notation59.2.1
  obtain ⟨-, -, h5152⟩ := h515 G T₁ M L H₀ D n hyp₁.toHyp5_0_1 hyp₁.hStar hD₁
  obtain ⟨-, B₁, hB₁, hB₁D⟩ := h5152 hyp₁.lieQuot
  have hN₁ : IsNotation5_1_9 T₁ M L H₀ B₁ D := ⟨inf_comm M H₀ ▸ hB₁, hD₁, hB₁D⟩
  have hV₁ : IsCh5Module T₁ L (V.map (MulAut.conj y).toMonoidHom) :=
    hT₁eq ▸ hyp.ch5Module.conj_of_mem (h.normal hyM)
  obtain ⟨K₁, hK₁, hKeq, -⟩ := hyp.choice
  set K₁' := K₁.map (MulAut.conj y).toMonoidHom with hK₁'def
  have hK₁' : quasithinIsCComponent K₁' H₀ := quasithinIsCComponent_map (MulAut.conj y) hK₁
  have hKeq' : oTwoUpper H₀ = conjClosure K₁' T₁ := by
    rw [hH₀def, oTwoUpper_map, hKeq, map_conjClosure_eq, hT₁eq]
  have hT₁X : T₁ ≤ X₀ := hT₁.1
  have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans (le_sup_left.trans le_sup_left)
  have hKX : K ≤ X₀ := by
    rw [hK]
    exact conjClosure_le fun t ht z hz =>
      X₀.mul_mem (X₀.mul_mem (hT₁X ht) (hL₂X hz)) (X₀.inv_mem (hT₁X ht))
  have hH₀X : H₀ ≤ X₀ := by
    have e : H₀ = K ⊔ T₁ := by
      rw [hH₀def, eq_oTwoUpper_sup_of_isSylowTwoOf' hTH, Subgroup.map_sup, ← hKdef, hyK, hT₁eq]
    rw [e]
    exact sup_le hKX hT₁X
  have hX : InH H₀ X₀ := ⟨hH₀X, hOX⟩
  have hK₁'H₀ : K₁' ≤ H₀ := A3.subnormal_le hK₁'.2.2.1
  have hT₁H₀ : T₁ ≤ H₀ := hyp₁.hStar.1.1
  have hK₁'loc : K₁' ∈ lFamily T₁ := cComp_mem_of_le hK₁' le_sup_left (sup_le hK₁'H₀ hT₁H₀)
  obtain ⟨Kh₁, ⟨hKh₁, hK₁Kh₁⟩, huniq⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc h37 h39 hOX hT₁
      (hK₁'H₀.trans hH₀X) hK₁'loc
  have hhat : IsHatComp X₀ K₁' Kh₁ := ⟨hKh₁, hK₁Kh₁, fun Y hY hK₁Y => huniq Y ⟨hY, hK₁Y⟩⟩
  rcases h5113 G T₁ M L (V.map (MulAut.conj y).toMonoidHom) H₀ B₁ D K₁' X₀ Kh₁ n hyp₁ hN₁ hV₁
      hK₁' hKeq' hX hhat with h1 | h2 | h3
  · apply hyp.Dp_not_le
    have hDpX : Dp ≤ X₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
    have := (le_inf hyp.Dp_le hDpX).trans h1
    rwa [hKH₀] at this
  · have h4 : LieModel (O2Q K) .PSL 2 2 2 := by
      rw [← hKH₀]
      exact h2.1
    exact hyp.false_of_lieModel_two h38 hL₂K h4
  · have h8 : LieModel (O2Q K) .PSL 2 2 3 := by
      rw [← hKH₀]
      exact h3.1
    exact hyp.false_of_lieModel_PSL2 h38 hL₂K (by norm_num) h8

end CFSG.Quasithin.H13
