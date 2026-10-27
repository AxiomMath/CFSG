module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeConj

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_ne_c2_conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    quasithinIsCComponent L₂ H → oTwoUpper H = conjClosure L₂ T →
    ∀ T₁ : Subgroup G, quasithinIsSylowTwo T₁ → T ⊓ Subgroup.normalizer (L₂ : Set G) < T₁ →
      T₁ ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L₂ : Set G) : Subgroup G) : Set G) →
    ∀ Kh₁ : Subgroup G,
      pCoreOf 2 (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L₂ : Set G) : Subgroup G) :
        Set G) ⊔ H) ≠ ⊥ →
      IsHatComp (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L₂ : Set G) : Subgroup G) :
        Set G) ⊔ H) L₂ Kh₁ →
      LieModel (O2Q L₂) .PSL 2 2 2 →
      (IsSporadic .J1 (O2Q Kh₁) ∨ ∃ q : ℕ, q.Prime ∧ q ^ 2 % 5 = 1 ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧
        IsPSL 2 q 1 (O2Q Kh₁)) →
      ∃ z ∈ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (L₂ : Set G) : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (L₂ : Set G),
        T.map (MulAut.conj z).toMonoidHom = T₁

section General

variable {G : Type} [Group G] [Finite G]

theorem false_of_isSimpleGroup_O2Q_of_lt {K L₂ : Subgroup G} (hlt : L₂ < K)
    (hKN : K ≤ Subgroup.normalizer (L₂ : Set G)) (hKperf : ⁅K, K⁆ = K) (hL₂perf : ⁅L₂, L₂⁆ = L₂)
    (hL₂ : L₂ ≠ ⊥) (hsimple : IsSimpleGroup (O2Q K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (modO2Image K L₂).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hlt.le).mpr hKN).map _
      (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (modO2Image K L₂) with h0 | h0
  · have hle : L₂.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
      intro x hx
      have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈ modO2Image K L₂ := ⟨x, hx, rfl⟩
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hx'
    have h2 : IsPGroup 2 ↥(L₂.subgroupOf K) := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).to_le hle
    have h2' : IsPGroup 2 ↥L₂ := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hlt.le)
    exact hL₂ (Vol2Native.eq_bot_of_perfect_of_isPGroup L₂ h2' hL₂perf)
  · have hle := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top hlt.le h0
    have hOK : pCoreOf 2 K ≤ Subgroup.normalizer (L₂ : Set G) := (pCoreOf_le 2 K).trans hKN
    exact hlt.ne (le_antisymm hlt.le
      (le_of_perfect_of_le_sup hKperf hle (pCoreOf_isPGroup 2 K) hOK))

omit [Finite G] in
theorem le_normalizer_of_cComp_eq_or {K X Y P : Subgroup G} (hX : X ∈ cComp K)
    (hc : ∀ C ∈ cComp K, C = X ∨ C = Y) (hP : P ≤ Subgroup.normalizer (K : Set G))
    (hodd : ¬ 2 ∣ Nat.card P) : P ≤ Subgroup.normalizer (X : Set G) := by
  by_contra hne
  have hlt : P ⊓ Subgroup.normalizer (X : Set G) < P :=
    lt_of_le_of_ne inf_le_left fun heq => hne (by rw [← heq]; exact inf_le_right)
  have h2 := relIndex_eq_two_of_orbit hlt (Y := Y) fun s hs => by
    have := quasithinIsCComponent_map (MulAut.conj s) hX
    rw [map_conj_eq_of_mem_normalizer_ch6 (hP hs)] at this
    exact hc _ this
  apply hodd
  have h3 := Subgroup.relIndex_mul_card (P ⊓ Subgroup.normalizer (X : Set G)) P
  rw [h2] at h3
  exact ⟨_, h3.symm⟩

end General

theorem stmt5_2_2_ne_conj_c2_of (h510 : Stmt5_1_10) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) (h432 : Stmt4_3_2) (h515 : Stmt5_1_5) (h5113 : Stmt5_1_13C)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hz : Stmt5_2_2_ne_c2_conj) : Stmt5_2_2_ne_conj_c2 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp _ hOX _ hT₀ hL₂K hDp T₁ hT₁ hlt hT₁syl _ hT₁N hL₂C
    hKeq Kh₁ hOX' hhat hL4 hJ
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set S := sec52S M H with hSdef
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set X₀ := Dp ⊔ (L₂ ⊔ S) ⊔ T₀ ⊔ B with hX₀def
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨z, ⟨hzT₀, hzL₂⟩, hzT⟩ := hz G T M L V H B D L₂ Dp n p hyp hT₀ hL₂K hL₂C hKeq T₁
    hT₁syl hlt hT₁N Kh₁ hOX' hhat hL4 hJ
  obtain ⟨-, -, -, -, hSL, -⟩ := hyp.S_facts h510 h331 hR
  have hTL : T ⊓ L ≤ T₀ := by
    intro x hx
    have hxS : x ∈ S ⊓ L := by
      rw [hSL]
      exact hx
    exact ⟨hx.1, hyp.S_le hxS.1⟩
  have hT₀L : T₀ ⊓ L = T ⊓ L :=
    le_antisymm (inf_le_inf_right L inf_le_left) (le_inf hTL inf_le_right)
  have hsylL : IsSylowTwoOf (T₀ ⊓ L) L := by
    rw [hT₀L]
    exact A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left
      h.sup_le_normalizer
  obtain ⟨-, hN⟩ := h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
    h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩
  have hzM : z ∈ M := hN T₀ inf_le_left hsylL hzT₀
  set H₀ := H.map (MulAut.conj z).toMonoidHom with hH₀def
  have hyp₁ : Hyp5_1_8 G T₁ M L H₀ n := hzT ▸ hyp.toHyp5_1_8.conj_of_mem hzM
  have hL₂z : L₂.map (MulAut.conj z).toMonoidHom = L₂ := map_conj_eq_of_mem_normalizer_ch6 hzL₂
  have hKz : (oTwoUpper H).map (MulAut.conj z).toMonoidHom = conjClosure L₂ T₁ := by
    rw [hKeq, map_conjClosure_eq, hL₂z, hzT]
  have hKH₀ : oTwoUpper H₀ = conjClosure L₂ T₁ := by rw [hH₀def, oTwoUpper_map, hKz]
  have hTL₁ : T₁ ⊓ L = T ⊓ L := by
    have hle : T ⊓ L ≤ T₁ ⊓ L := le_inf (hTL.trans hlt.le) inf_le_right
    have hzL : z ∈ Subgroup.normalizer (L : Set G) := h.normal hzM
    have hcard : Nat.card ↥(T₁ ⊓ L) = Nat.card ↥(T ⊓ L) := by
      have e : (T ⊓ L).map (MulAut.conj z).toMonoidHom = T₁ ⊓ L := by
        rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj z).injective, hzT,
          map_conj_eq_of_mem_normalizer_ch6 hzL]
      rw [← e, Subgroup.card_map_of_injective (MulAut.conj z).injective]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hD₁ : Lin2.IsHallTwoPrimeOf D (borelL T₁ L) := by
    show Lin2.IsHallTwoPrimeOf D (L ⊓ Subgroup.normalizer ((T₁ ⊓ L : Subgroup G) : Set G))
    rw [hTL₁]
    exact hyp.notation59.2.1
  obtain ⟨-, -, h5152⟩ := h515 G T₁ M L H₀ D n hyp₁.toHyp5_0_1 hyp₁.hStar hD₁
  obtain ⟨-, B₁, hB₁, hB₁D⟩ := h5152 hyp₁.lieQuot
  have hN₁ : IsNotation5_1_9 T₁ M L H₀ B₁ D := ⟨inf_comm M H₀ ▸ hB₁, hD₁, hB₁D⟩
  have hV₁ : IsCh5Module T₁ L (V.map (MulAut.conj z).toMonoidHom) :=
    hzT ▸ hyp.ch5Module.conj_of_mem (h.normal hzM)
  have hL₂H₀ : quasithinIsCComponent L₂ H₀ := by
    have := quasithinIsCComponent_map (MulAut.conj z) hL₂C
    rwa [hL₂z] at this
  have hT₁X : T₁ ≤ X₀ := hT₁.1
  have hL₂X : L₂ ≤ X₀ := (le_sup_left.trans le_sup_right).trans (le_sup_left.trans le_sup_left)
  have hK₀X : conjClosure L₂ T₁ ≤ X₀ :=
    conjClosure_le fun t ht w hw =>
      X₀.mul_mem (X₀.mul_mem (hT₁X ht) (hL₂X hw)) (X₀.inv_mem (hT₁X ht))
  have hH₀X : H₀ ≤ X₀ := by
    have e : H₀ = conjClosure L₂ T₁ ⊔ T₁ := by
      rw [hH₀def, eq_oTwoUpper_sup_of_isSylowTwoOf' hTH, Subgroup.map_sup, hKz, hzT]
    rw [e]
    exact sup_le hK₀X hT₁X
  have hX : InH H₀ X₀ := ⟨hH₀X, hOX⟩
  have hL₂H₀le : L₂ ≤ H₀ := A3.subnormal_le hL₂H₀.2.2.1
  have hT₁H₀ : T₁ ≤ H₀ := hyp₁.hStar.1.1
  have hL₂loc : L₂ ∈ lFamily T₁ := cComp_mem_of_le hL₂H₀ le_sup_left (sup_le hL₂H₀le hT₁H₀)
  obtain ⟨Lh, ⟨hLh, hL₂Lh⟩, huniq⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc h37 h39 hOX hT₁ (hL₂H₀le.trans hH₀X) hL₂loc
  have hhat₀ : IsHatComp X₀ L₂ Lh := ⟨hLh, hL₂Lh, fun Y hY hL₂Y => huniq Y ⟨hY, hL₂Y⟩⟩
  obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hHO hTH hL₂C hKeq hL₂K
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (L₂ : Set G) := by
    rw [tc.sup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hL₂C tc.cK₂)
  have hK₀N : oTwoUpper H₀ ≤ Subgroup.normalizer (L₂ : Set G) := by
    rw [hH₀def, oTwoUpper_map]
    rintro _ ⟨k, hk, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzL₂ (hKN hk)) (Subgroup.inv_mem _ hzL₂)
  have hlt₀ : L₂ < oTwoUpper H₀ := by
    have := (Subgroup.map_lt_map_iff_of_injective (f := (MulAut.conj z).toMonoidHom)
      (MulAut.conj z).injective).mpr hL₂K
    rw [hL₂z] at this
    rw [hH₀def, oTwoUpper_map]
    exact this
  rcases h5113 G T₁ M L (V.map (MulAut.conj z).toMonoidHom) H₀ B₁ D L₂ X₀ Lh n hyp₁ hN₁ hV₁
      hL₂H₀ hKH₀ hX hhat₀ with h1 | h2
  ·
    apply hDp
    have hDpX : Dp ≤ X₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
    have hDpK : Dp ≤ Subgroup.normalizer (oTwoUpper H₀ : Set G) :=
      (le_inf hyp.Dp_le hDpX).trans h1
    have hL₂c : L₂ ∈ cComp (oTwoUpper H₀) := cComp_mem_of_le hL₂H₀ hlt₀.le (oTwoUpper_le H₀)
    refine le_normalizer_of_cComp_eq_or hL₂c (Y := K₂.map (MulAut.conj z).toMonoidHom)
      (fun C hC => ?_) hDpK ?_
    · have hC' := quasithinIsCComponent_map (MulAut.conj z⁻¹) hC
      have eK : (oTwoUpper H₀).map (MulAut.conj z⁻¹).toMonoidHom = oTwoUpper H := by
        rw [hH₀def, oTwoUpper_map, Subgroup.map_map]
        ext w
        simp [MulAut.conj_apply, mul_assoc]
      rw [eK] at hC'
      have eC : (C.map (MulAut.conj z⁻¹).toMonoidHom).map (MulAut.conj z).toMonoidHom = C := by
        rw [Subgroup.map_map]
        ext w
        simp [MulAut.conj_apply, mul_assoc]
      rcases tc.cK _ hC' with h3 | h3
      · left
        rw [← eC, h3, hL₂z]
      · right
        rw [← eC, h3]
    · rw [hyp.card_Dp]
      rcases hyp.p_cases with rfl | rfl <;> norm_num
  ·
    have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
      have hK₂K : K₂ ≤ oTwoUpper H := by
        rw [tc.sup]
        exact le_sup_right
      apply le_antisymm
      · rw [Subgroup.commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        exact (oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem hx hy)
          ((oTwoUpper H).inv_mem hx)) ((oTwoUpper H).inv_mem hy)
      · calc oTwoUpper H = L₂ ⊔ K₂ := tc.sup
          _ = ⁅L₂, L₂⁆ ⊔ ⁅K₂, K₂⁆ := by rw [hL₂C.2.1, tc.cK₂.2.1]
          _ ≤ ⁅oTwoUpper H, oTwoUpper H⁆ := sup_le (Subgroup.commutator_mono hL₂K.le hL₂K.le)
              (Subgroup.commutator_mono hK₂K hK₂K)
    have hK₀perf : ⁅oTwoUpper H₀, oTwoUpper H₀⁆ = oTwoUpper H₀ := by
      rw [hH₀def, oTwoUpper_map, ← Subgroup.map_commutator, hKperf]
    exact false_of_isSimpleGroup_O2Q_of_lt hlt₀ hK₀N hK₀perf hL₂C.2.1 hL₂C.1
      (h2.elim (fun h => isSimpleGroup_of_lieModel_PSL2 h.1)
        fun h => isSimpleGroup_of_lieModel_PSL2 h.1)

end CFSG.Quasithin.H13
