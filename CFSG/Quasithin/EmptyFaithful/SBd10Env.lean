module

public import CFSG.Quasithin.EmptyFaithful.SBd10Row
public import CFSG.Quasithin.Vol2.Ch1List
public import CFSG.Quasithin.EmptyFaithful.S153D35
public import CFSG.Quasithin.EmptyFaithful.SBd10Lie

public section

namespace CFSG.Quasithin.SBd10

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem pCore_two_eq_bot_of_card_u34 {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hc : Nat.card X = 62400) : CFSG.pCore 2 X = ⊥ := by
  have : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 X := by
      have := (CFSG.pCore_isPGroup (p := 2) (G := X))
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hc] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 62400)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem u34Row_modO2Image {G : Type} [Group G] [Finite G] {H L : Subgroup G} (hLH : L ≤ H)
    (hs : IsSimpleGroup ↥L) (hc : Nat.card ↥L = 62400) : U34Row (modO2Image H L) := by
  have hnp : ¬ ∃ k : ℕ, Nat.card ↥L = 2 ^ k := by
    rintro ⟨k, hk⟩
    rw [hc] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 62400)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hLO : L ⊓ pCoreOf 2 H = ⊥ := by
    have hnorm : ((L ⊓ pCoreOf 2 H).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
      intro g hg
      have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hg)
      have h1 : g ∈ Subgroup.normalizer ((L ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hgO⟩
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, Subgroup.le_normalizer hg⟩
    rcases hs.eq_bot_or_eq_top_of_normal ((L ⊓ pCoreOf 2 H).subgroupOf L) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxL : x ∈ L := hx.1
      have : (⟨x, hxL⟩ : ↥L) ∈ (L ⊓ pCoreOf 2 H).subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hLle : L ≤ pCoreOf 2 H := fun x hx => by
        have : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ pCoreOf 2 H).subgroupOf L := by rw [h]; trivial
        exact this.2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((pCoreOf_isPGroup 2 H).to_le hLle)
      exact hnp ⟨k, hk⟩
  let f : ↥(L.subgroupOf H) →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (L.subgroupOf H).subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : ((x : ↥H) : G) ∈ pCoreOf 2 H := (S153D.mem_pCore_iff (x : ↥H)).mp h1
    have h3 : ((x : ↥H) : G) ∈ L ⊓ pCoreOf 2 H := ⟨x.2, h2⟩
    rw [hLO, Subgroup.mem_bot] at h3
    exact Subtype.ext (Subtype.ext h3)
  have hrange : f.range = modO2Image H L := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  let e : ↥L ≃* ↥(modO2Image H L) :=
    ((Subgroup.subgroupOfEquivOfLe hLH).symm.trans (MonoidHom.ofInjective hf)).trans
      (MulEquiv.subgroupCongr hrange)
  have hs' : IsSimpleGroup ↥(modO2Image H L) := e.symm.isSimpleGroup
  have hc' : Nat.card ↥(modO2Image H L) = 62400 := by rw [← Nat.card_congr e.toEquiv, hc]
  refine ⟨hs', hc', ?_⟩
  have hpc := pCore_two_eq_bot_of_card_u34 hs' hc'
  rw [← Nat.card_congr
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hpc.symm)).toEquiv, hc']


variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem normalizer_V₁_le_normalizer_L
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hL0 : L = conjClosure L (Sgp153 T V₁))
    (hLs : IsSimpleGroup ↥L) (hU : IsPSU 3 2 2 ↥L) (hYY : Yp = Y153 Mc M)
    (hC : ∀ v ∈ V₁, ∀ x ∈ L, v * x = x * v) :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hcardL : Nat.card ↥L = 62400 := card_u34 hU
  set S := Sgp153 T V₁ with hSdef
  set I₁ : Subgroup G := Subgroup.normalizer (V₁ : Set G) with hI₁
  have hLC : L ≤ Subgroup.centralizer (V₁ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hC v hv x hx
  have hLI₁ : L ≤ I₁ := fun x hx => Subgroup.centralizer_le_normalizer _ (hLC hx)
  have hYI₁ : Yp ≤ I₁ := by
    obtain ⟨hY₁, -⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
    rw [hYY]
    exact hY₁
  have hSI₁ : S ≤ I₁ := inf_le_right
  have hpC : pCoreOf 2 I₁ ≠ ⊥ := by
    have hV₁2 : IsPGroup 2 ↥V₁ := IsPGroup.of_card (n := 2) (by rw [hh.decomp.card₁]; norm_num)
    have hle : V₁ ≤ pCoreOf 2 I₁ :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV₁2
    intro hb
    rw [hb, le_bot_iff] at hle
    have := hh.decomp.card₁
    rw [hle, Subgroup.card_bot] at this
    omega
  have hH : IsHPlus Yp S M I₁ :=
    ⟨⟨sup_le hYI₁ hSI₁, hpC⟩, fun hle => c.c33.not_le (hLI₁.trans hle)⟩
  have hS₁ : IsSylowTwoOf S I₁ := hh.lemma_15_3_11_one h11 h113 hH
  have hLloc : quasithinIsLocal S L :=
    isLocal_of_mem_cComp_of_sylow c.facts.sylow c.inH.1.2 c.c33.mem
  have hB : L ∈ lFamily S := mem_lFamily_of_isLocal hLloc
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := by
    have := le_normalizer_conjClosure L S
    rwa [← hL0] at this
  have hqk := hq.qtke
  obtain ⟨L', hL', hLL'⟩ :=
    lemma_1_2_4_exists hqk hq.simple hq.nonabelian h37 h39 hpC hS₁ hLI₁ hB
  have hnorm : (L'.subgroupOf I₁).Normal :=
    lemma_1_2_4_normal hqk hq.simple hq.nonabelian h37 h38 hpC hS₁ hB hLL' hL' hSL
  have hlist := lemma_1_2_4_list hqk hq.simple hq.nonabelian h312 hpC hS₁ hLI₁ hB hL' hLL'
  have hD : U34Row (modO2Image I₁ L) := u34Row_modO2Image hLI₁ hLs hcardL
  have hmono : modO2Image I₁ L ≤ modO2Image I₁ L' := Subgroup.map_mono (fun x hx => hLL' hx)
  have heq : modO2Image I₁ L = modO2Image I₁ L' := by
    rcases hlist with h | h | h
    · exact h
    · exact (row_u34 hD hmono (Or.inl h)).elim
    · exact (row_u34 hD hmono (Or.inr h)).elim
  have hOS : pCoreOf 2 I₁ ≤ S := pCoreOf_two_le_of_sylowIn hS₁.1 hS₁.2.1 hS₁.2.2
  have hL'I₁ : L' ≤ I₁ := le_of_mem_cComp hL'
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    have hxI : x ∈ I₁ := hL'I₁ hx
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥I₁) ⟨x, hxI⟩ ∈ modO2Image I₁ L := by
      rw [heq]
      exact ⟨⟨x, hxI⟩, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    have hv : (((y⁻¹ * ⟨x, hxI⟩ : ↥I₁)) : G) ∈ pCoreOf 2 I₁ :=
      (S153D.mem_pCore_iff (y⁻¹ * ⟨x, hxI⟩ : ↥I₁)).mp hyx
    have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hxe : x = (y : G) * (((y⁻¹ * ⟨x, hxI⟩ : ↥I₁)) : G) := by
      simp
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hyL) (hSL (hOS hv))
  have hLn : (L.subgroupOf L').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLL').mpr hL'N
  have hsub : IsSubnormal L I₁ :=
    A3.subnormal_trans (A3.subnormal_of_normal hLL' hLn) (A3.subnormal_of_normal hL'I₁ hnorm)
  have hLL'eq : L = L' := by
    by_contra hne
    exact not_subnormal_of_mem_cComp hL' (lt_of_le_of_ne hLL' hne)
      (ne_bot_of_mem_cComp c.c33.mem) (perfect_of_mem_cComp c.c33.mem) hsub
  rw [hLL'eq]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hL'I₁).mp hnorm

end CFSG.Quasithin.SBd10
