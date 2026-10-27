module

public import CFSG.Quasithin.EmptyFaithful.T1515A
public import CFSG.Quasithin.Background.A3Structure312Embed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_sup1516 {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.centralizer (A : Set G)) (hB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_
    · intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (Subgroup.mem_centralizer_iff.mp hA h hh).symm
    · intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (Subgroup.mem_centralizer_iff.mp hB h hh).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.mp (hle hh) x (Set.mem_singleton x)).symm

omit [Finite G] in
theorem oPrimeResidualOf_le1516 (p : ℕ) (X : Subgroup G) : oPrimeResidualOf p X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

omit [Finite G] in
theorem oPrimeResidualOf_mono1516 (p : ℕ) {X Y : Subgroup G} (h : X ≤ Y) :
    oPrimeResidualOf p X ≤ oPrimeResidualOf p Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem lemma_15_1_19 (h : Lemma15119Input) {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) : Lemma15119Concl T Mc M Z₁ V₂ :=
  h G T Mc M Z₁ Z₂ V₁ V₂ hC h17 h18

theorem Setting1516.pCore_g1_ne_bot {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ :=
  fun h => hS.z1_ne (le_bot_iff.mp (h ▸ le_pCoreOf_of_le_normalizer 2 (hS.z1_le_g1 hq hM)
    (Subgroup.centralizer_le_normalizer _)
    (isPGroup_of_isElemAbelian (hS.z1_isElemAbelian hq hM))))

theorem lemma_15_1_20_sylow {T Mc Z₁ L : Subgroup G}
    (h4 : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁)) (hL : IsL1520 T Mc Z₁ L) :
    IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := by
  have hsub : IsSubnormal L (L ⊔ s1516 T Z₁) :=
    subnormal_of_mem_cComp (cComp_of_isLocal hL.mem.2)
  have hS : IsSylowTwoOf (s1516 T Z₁) (L ⊔ s1516 T Z₁) :=
    A4.isSylowTwoOf_mono h4 le_sup_right (sup_le hL.mem.1 (s1516_le_g1 T Z₁))
  exact A312.isSylowTwoOf_inf_of_subnormal hsub hS

theorem lemma_15_1_20_one {T Mc M Z₁ L : Subgroup G}
    (h156 : ∀ M V : Subgroup G, InM T M → IsTwoReducedIn M V →
      perfectCore M ≤ Subgroup.centralizer (V : Set G))
    (hM : IsMf T Mc M) (h15 : Lemma1515Concl T Mc M) (hL : IsL1520 T Mc Z₁ L) : ¬ L ≤ M := by
  intro hLM
  apply hL.not_le
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp (cComp_of_isLocal hL.mem.2)
  have hLinf : L ≤ perfectCore M := le_perfectCore_of_perfect hLM hperf
  have hLC : L ≤ Subgroup.centralizer (V154 T Mc M : Set G) :=
    hLinf.trans (h156 M _ hM.1.1 h15.reduced)
  exact fun x hx => ⟨hL.mem.1 hx, h15.centralizer_le (hLC hx)⟩

theorem lemma_15_1_20 (h : Lemma15120Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h156 : ∀ M V : Subgroup G, InM T M → IsTwoReducedIn M V →
      perfectCore M ≤ Subgroup.centralizer (V : Set G))
    (h15 : Lemma1515Concl T Mc M) (h17 : Lemma15117Concl T M Z₁) (h18 : Lemma15118Concl T Mc M Z₁)
    (h19 : Lemma15119Concl T Mc M Z₁ V₂) (hL : IsL1520 T Mc Z₁ L) :
    Lemma15120Concl T Mc M Z₁ L := by
  obtain ⟨h2, h3⟩ := h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL
  exact ⟨lemma_15_1_20_sylow h18.four hL, lemma_15_1_20_one h156 hC.mf h15 hL, h2, h3⟩

theorem lemma_15_1_21 (h : Lemma15121Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) (h19 : Lemma15119Concl T Mc M Z₁ V₂) :
    Lemma15121Concl Mc Z₁ L :=
  h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19

theorem lemma_15_1_22 (h : Lemma15122Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) (h19 : Lemma15119Concl T Mc M Z₁ V₂)
    (hL : IsL1519 Mc Z₁ L) (h20 : Lemma15120Concl T Mc M Z₁ L) (h21 : Lemma15121Concl Mc Z₁ L) :
    Lemma15122Concl T Mc M Z₁ L :=
  h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 h21

theorem lemma_15_1_23 (h : Lemma15123Input) (h110 : StageLemma15110)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h17 : Lemma15117Concl T M Z₁) (h18 : Lemma15118Concl T Mc M Z₁)
    (h19 : Lemma15119Concl T Mc M Z₁ V₂) (hL : IsL1519 Mc Z₁ L)
    (h22 : Lemma15122Concl T Mc M Z₁ L) : Lemma15123Concl T Mc M := by
  intro p hp h6
  have hp3 : p = 3 := h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 p hp h6
  subst hp3
  exact ⟨rfl, h110 G T Mc M hC.qtfe hC.mf hC.ce h6⟩

theorem Ce15Small_of_lemma_15_1_23 {T Mc M : Subgroup G} (hce : Ce15 T Mc M)
    (h23 : Lemma15123Concl T Mc M) : Ce15Small T Mc M := by
  rcases hce with h | ⟨p, hp, h⟩ | h
  · exact Or.inl h
  · rw [(h23 p hp h).1] at h
    exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem lemma_15_1_24_three {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (h15 : Lemma1515Concl T Mc M)
    (hsmall : Ce15Small T Mc M) :
    ∀ Y₀ : Subgroup G, oTwoUpper Y₀ = Y₀ → Y₀ ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) →
      ¬ Y₀ ≤ mZ1516 Mc Z₁ →
        ⁅V₂, Y₀⁆ = V₂ ∧ (Y₀ ⊓ Subgroup.centralizer (V₂ : Set G)).relIndex Y₀ = 3 := by
  intro Y₀ _ hY₀Y hY₀MZ
  set V := V154 T Mc M with hVdef
  set Y := oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) with hY
  obtain ⟨⟨hcard, -, hcomm, -⟩, hV1⟩ := hS.y_facts hsmall
  have hYM : Y ≤ M ⊓ g1_1516 Z₁ := oPrimeResidualOf_le1516 3 _
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) :=
    hYM.trans (inf_le_left.trans (le_normalizer_V154 T Mc M))
  have hY₀N : Y₀ ≤ Subgroup.normalizer (V : Set G) := hY₀Y.trans hYN
  have hnc : ¬ Y₀ ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    exact hY₀MZ fun y hy => ⟨(hYM (hY₀Y hy)).2, h15.centralizer_le (hle hy)⟩
  have hbot : autOn Y₀ V ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hY₀N hnc
  have hle : autOn Y₀ V ≤ autOn Y V := autOn_le_autOn V hY₀Y
  have heq : autOn Y₀ V = autOn Y V := by
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard] at hdvd
    have hne1 : Nat.card (autOn Y₀ V) ≠ 1 := fun h => hbot (Subgroup.card_eq_one.mp h)
    have h3 : Nat.card (autOn Y₀ V) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h3])
  refine ⟨?_, ?_⟩
  · refine le_antisymm ((Subgroup.commutator_mono le_rfl hY₀Y).trans hcomm.le) ?_
    calc V₂ = ⁅V₂, Y⁆ := hcomm.symm
      _ ≤ ⁅V₂, Y₀⁆ := by
        rw [Subgroup.commutator_le]
        intro v hv y hy
        have hvV : v ∈ V := hS.v2_le hv
        have hyN : y ∈ Subgroup.normalizer (V : Set G) := hYN hy
        have hmem : conjAct V ⟨y, hyN⟩ ∈ autOn Y₀ V := by
          rw [heq]
          exact mem_autOn_iff_exists.mpr ⟨y, hyN, hy, rfl⟩
        obtain ⟨y₀, hy₀N, hy₀, hact⟩ := mem_autOn_iff_exists.mp hmem
        have h1 := congrArg (fun φ : MulAut V => ((φ ⟨v, hvV⟩ : V) : G)) hact
        have h2 : y₀ * v * y₀⁻¹ = y * v * y⁻¹ := h1
        have h3 : ⁅v, y⁆ = ⁅v, y₀⁆ := by
          simp only [commutatorElement_def]
          have : y * v⁻¹ * y⁻¹ = y₀ * v⁻¹ * y₀⁻¹ := by
            have := congrArg (fun a : G => a⁻¹) h2
            simpa [mul_assoc] using this.symm
          calc v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
            _ = v * (y₀ * v⁻¹ * y₀⁻¹) := by rw [this]
            _ = v * y₀ * v⁻¹ * y₀⁻¹ := by group
        rw [h3]
        exact Subgroup.commutator_mem_commutator hv hy₀
  · obtain ⟨W, hWV, hYW⟩ : ∃ W : Subgroup G, W ⊔ V₂ = V ∧
        Y ≤ Subgroup.centralizer (W : Set G) := by
      by_cases h7 : Ce15Seven T Mc M
      · exact ⟨Z₁, (hS.decomp_seven h7).1, fun y hy => (hYM hy).2⟩
      · obtain ⟨-, -, hsup, -⟩ := hS.decomp_other h7
        exact ⟨V₁, hsup, le_centralizer_of_commutator_eq_bot (hV1 h7)⟩
    have hCeq : Y₀ ⊓ Subgroup.centralizer (V₂ : Set G) = Y₀ ⊓ Subgroup.centralizer (V : Set G) := by
      refine le_antisymm (fun y hy => ⟨hy.1, ?_⟩)
        (inf_le_inf_left _ (Subgroup.centralizer_le hS.v2_le))
      rw [← hWV]
      exact mem_centralizer_sup1516 (hYW (hY₀Y hy.1)) hy.2
    rw [hCeq, ← card_autOn_eq_relIndex hY₀N, heq, hcard]

theorem lemma_15_1_24_four {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (hsmall : Ce15Small T Mc M)
    (h : Ce15Four T Mc M ∨ Ce15Six T Mc M 3) :
    V₁ ≤ s1516 T Z₁ ⊓ Subgroup.centralizer (oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) : Set G) := by
  have h7 := not_seven_of_four_or_six h
  obtain ⟨hV1V, hZ1V1, -, -⟩ := hS.decomp_other h7
  have hVab := hS.V_isElemAbelian hq hM
  intro v hv
  have hYC := le_centralizer_of_commutator_eq_bot ((hS.y_facts hsmall).2 h7)
  refine ⟨⟨hS.V_le_T hq hM (hV1V hv), Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  · have := hVab.1
    have hcomm := mul_comm' (⟨z, hS.z1_le_V hz⟩ : V154 T Mc M) ⟨v, hV1V hv⟩
    exact congrArg (fun a : V154 T Mc M => (a : G)) hcomm
  · exact (Subgroup.mem_centralizer_iff.mp (hYC hy) v hv).symm

theorem lemma_15_1_24 (h : Lemma15124Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) (h19 : Lemma15119Concl T Mc M Z₁ V₂)
    (hL : IsL1519 Mc Z₁ L) (h22 : Lemma15122Concl T Mc M Z₁ L) (h23 : Lemma15123Concl T Mc M)
    (h15 : Lemma1515Concl T Mc M) : Lemma15124Concl T Mc M Z₁ V₁ V₂ L := by
  have hsmall := Ce15Small_of_lemma_15_1_23 hC.setting.ce15 h23
  obtain ⟨h1, h2⟩ := h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 hsmall
  have h7 := not_seven_of_four_or_six h1
  exact ⟨h1, (hC.setting.decomp_other h7).2.1, h2, lemma_15_1_24_three hC.setting h15 hsmall,
    (hC.setting.y_facts hsmall).1.2.2.1, lemma_15_1_24_four hC.qtfe hC.mf hC.setting hsmall h1⟩

theorem lemma_15_1_25_four {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (h : Ce15Four T Mc M ∨ Ce15Six T Mc M 3) :
    (Subgroup.centralizer (V₁ : Set G) ⊓ s1516 T Z₁).relIndex (s1516 T Z₁) = 2 :=
  hS.index_v1 (ce15Small_of_four_or_six h) (not_seven_of_four_or_six h)

theorem lemma_15_1_25_six {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂) (h : Ce15Four T Mc M ∨ Ce15Six T Mc M 3) :
    (s1516 T Z₁).relIndex T = 2 :=
  hS.index_two (ce15Small_of_four_or_six h) (not_seven_of_four_or_six h)

theorem lemma_15_1_25 (h : Lemma15125Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) (h19 : Lemma15119Concl T Mc M Z₁ V₂)
    (hL : IsL1519 Mc Z₁ L) (h22 : Lemma15122Concl T Mc M Z₁ L)
    (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) : Lemma15125Concl T Z₁ V₁ L := by
  obtain ⟨h1, h2, h3, h5⟩ := h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24
  exact ⟨h1, h2, h3, lemma_15_1_25_four hC.setting h24.one, h5,
    lemma_15_1_25_six hC.setting h24.one⟩

omit [Finite G] in
theorem v1_le_centralizer_of_centS {T M Z₁ V₁ L : Subgroup G}
    (h4 : V₁ ≤ s1516 T Z₁ ⊓ Subgroup.centralizer (oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) : Set G))
    (hLG : L ≤ g1_1516 Z₁) (hc : CentS15122 T M Z₁ L) :
    V₁ ≤ Subgroup.centralizer (L : Set G) := by
  intro v hv
  have hmono : oPrimeResidualOf 3 (M ⊓ L) ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) :=
    oPrimeResidualOf_mono1516 3 (inf_le_inf_left M hLG)
  have hv' : v ∈ s1516 T Z₁ ⊓ Subgroup.centralizer (oPrimeResidualOf 3 (M ⊓ L) : Set G) :=
    ⟨(h4 hv).1, Subgroup.centralizer_le hmono (h4 hv).2⟩
  have : v ∈ s1516 T Z₁ ⊓ Subgroup.centralizer (L : Set G) := by
    rw [← hc]
    exact hv'
  exact this.2

theorem lemma_15_1_26 {T Mc M Z₁ V₁ V₂ L : Subgroup G} (hL : IsL1519 Mc Z₁ L)
    (h22 : Lemma15122Concl T Mc M Z₁ L) (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L)
    (h25 : Lemma15125Concl T Z₁ V₁ L) : Lemma15126Concl L := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hL.comp
  have key : CentS15122 T M Z₁ L → False := fun hc =>
    h25.three (v1_le_centralizer_of_centS h24.four hLG hc)
  rcases h22 with h | h | h | h | h | h | h
  · exact absurd h.1 h25.five
  · exact (key h.2.2.2.2.2).elim
  · exact ⟨h.1, h.2.1⟩
  · exact (key h.2.2.2.2.2).elim
  · exact (key h.2.2).elim
  · exact absurd h.1 h25.two
  · exact (key h.2.2.2.2.2.2.2).elim

theorem lemma_15_1_27 (h : Lemma15127Input) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h17 : Lemma15117Concl T M Z₁)
    (h18 : Lemma15118Concl T Mc M Z₁) (h19 : Lemma15119Concl T Mc M Z₁ V₂)
    (hL : IsL1519 Mc Z₁ L) (h22 : Lemma15122Concl T Mc M Z₁ L)
    (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) (h25 : Lemma15125Concl T Z₁ V₁ L)
    (h26 : Lemma15126Concl L) : Lemma15127Concl Z₂ L :=
  h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26

end CFSG.Quasithin
