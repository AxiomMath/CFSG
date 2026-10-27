module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrderSixAD
public import CFSG.LocalAnalysis.StandardType.GGSecFivePZLabel
public import CFSG.LocalAnalysis.StandardType.GGPsiInnerDiagOfMarking
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal Module

variable {G : Type} [Group G] [Finite G]

theorem pow_rank_le_card_inf_of_cartan_pairing {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hstep : ∀ ψ ∈ A, ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) * (b : G)⁻¹ ∈ X)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hpair : ∀ {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V),
      ∃ (e : M.Group ≃* ↥A) (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
        (hα : ∀ i, α i (h i) = 2),
        (∀ i, ggLin (p := p) ιV ((e (M.simple i) : ↥A) : MulAut ↥Bs) = reflection (hα i)) ∧
        ∀ i j, α i (h j) = (C i j : ZMod p)) :
    p ^ (C.map (Int.castRingHom (ZMod p))).rank ≤ Nat.card ↥(Bs ⊓ X) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨V, hVadd, hVmod, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have : Finite V := Finite.of_equiv _ ιV.toEquiv
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨e, h, α, hα, hrefl, hP⟩ := hpair ιV
  have hle : Submodule.span (ZMod p) (Set.range h) ≤ ggLinImage (p := p) ιV X := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact (mem_ggLinImage ιV X (h i)).mpr
      (coroot_mem_of_reflection hp2 ιV (hstep _ (e (M.simple i)).2) (hα i) (hrefl i))
  have hfr : (C.map (Int.castRingHom (ZMod p))).rank ≤
      Module.finrank (ZMod p) (ggLinImage (p := p) ιV X) :=
    (cartan_rank_le_finrank_span h α hP).trans (Submodule.finrank_mono hle)
  rw [← card_ggLinImage (p := p) ιV X, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p),
    ZMod.card]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hfr

theorem GGSecFiveRouteCfg.inf_centralizer_ggG0_eq_bot {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    Bs ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
  have hfix : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ ⟨b, hbB⟩ = ⟨b, hbB⟩ := by
    intro φ hφ
    have hle : ggG0 p B x L D J ≤ Subgroup.centralizer ({b} : Set G) := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hbC g hg)
    have hJ : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (ggG0 p B x L D J) Bs :=
      sup_le (ggAutomizer_mono Bs (le_ggG0_left p B x L D J))
        (iSup₂_le fun K hK => ggAutomizer_mono Bs
          (le_ggG0_of_ggNbr (hcfg.2.2.2.1.2 K hK).choose_spec))
    exact ggAutomizer_apply_eq_of_le_centralizer (x := ⟨b, hbB⟩) hle (hJ hφ)
  have h1 := hcfg.eq_one_of_forall_join_fix hTBF hWI ⟨b, hbB⟩ hfix
  rw [Subgroup.mem_bot]
  simpa using congrArg Subtype.val h1

section Cells

@[expose] def GGSecFivePZData (G0 Bs L : Subgroup G) (x : G) (m : ℕ) : Prop :=
  GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = m - 1 ∧ lab.n = 1) 3 Bs L ∧
    (Nat.card Bs = 3 ^ m ∧ Nat.card ↥(Bs ⊓ L) = 3 ^ (m - 1)) ∧
    (Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) ∧ Disjoint (Subgroup.zpowers x) (Bs ⊓ L)) ∧
    (Bs ≤ Subgroup.normalizer (G0 : Set G) ∧ Bs ⊓ Subgroup.centralizer (G0 : Set G) = ⊥)

@[expose] def GGSecFivePZKnownGroupInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G) (m : ℕ),
    5 ≤ m → 3 ∣ m + 1 → GGConfig 3 B Bs x L D J → GGNoTransvection 3 Bs →
      GGSecFivePZData (ggG0 3 B x L D J) Bs L x m →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ →
            GGInnerDiagOn Bs (ggG0 3 B x L D J)

@[expose] def GGSecFivePZTwA5Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region 3 B Bs x L D J → ¬ GGSecFivePhanARow 3 B Bs x L D J →
      ¬ GGSecFiveQTwoCell 3 B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGSecFiveJoinOrderSixAt 3 L Bs 𝒦 M e →
        ∀ σ : Fin 5 ≃ ι, M = (CoxeterMatrix.A 5).reindex σ → Nat.card Bs = 3 ^ 5 →
        GGInnerDiagOnLabel GGLabQTwo 3 Bs L → x ∉ L →
        ¬ GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L

theorem ggSecFivePZData_of_not_mem
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hW : GGTBTorWRows)
    (hLift : GGTBTorLiftRows) (hU6 : GGSecFivePZTwA5Input)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hReg : ¬ GGSecFiveTier1Region 3 B Bs x L D J)
    (hrow : ¬ GGSecFivePhanARow 3 B Bs x L D J) (hQ : ¬ GGSecFiveQTwoCell 3 B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hsix : GGSecFiveJoinOrderSixAt 3 L Bs 𝒦 M e) {m : ℕ} {σ : Fin m ≃ ι} (hm : 5 ≤ m)
    (hM : M = (CoxeterMatrix.A m).reindex σ) (h3 : 3 ∣ m + 1)
    (hbig : 3 ^ (m - 1) < Nat.card Bs) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hxL : x ∉ L) : GGSecFivePZData (ggG0 3 B x L D J) Bs L x m := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hR.1
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hconf.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have hNT : GGNoTransvection 3 Bs := hR.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := fun S hSL hSp => hS.2.2.2.2 S hSL hSp
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hWJ : GGWeylOfType 3 (CoxeterMatrix.A m) (ggAutomizerJoin L Bs 𝒦) := by
    have h : GGWeylOfType 3 M (ggAutomizerJoin L Bs 𝒦) := ⟨e, hsix.1.2⟩
    rw [hM] at h
    exact h.of_reindex
  have hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ b = b) → b = 1 :=
    fun b hb => hcfg.eq_one_of_forall_join_fix hTBF hWI b hb
  have hcardJ : Nat.card (ggAutomizerJoin L Bs 𝒦) = (m + 1).factorial := by
    obtain ⟨f, -⟩ := hWJ
    rw [← Nat.card_congr f.toEquiv, l05nK3a_card_coxeterA]
  have hcard : Nat.card Bs = 3 ^ m := by
    have hle : Nat.card Bs ≤ 3 ^ m := by
      simpa using hcfg.card_le_pow_of_weylOfType hTBF hWI le_rfl hWJ
    have hpg : IsPGroup 3 ↥Bs := fun g => ⟨1, Subtype.ext (by simpa using hBs.2 g g.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    rw [hk] at hle hbig ⊢
    have h1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hbig
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    congr 1
    omega
  have hALJ : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  have hdvdL : Nat.card (ggAutomizer L Bs) ∣ (m + 1).factorial := by
    rw [← hcardJ]
    exact Subgroup.card_dvd_of_le hALJ
  have hne : Nat.card (ggAutomizer L Bs) ≠ (m + 1).factorial := by
    intro hc
    have hEq : ggAutomizer L Bs = ggAutomizerJoin L Bs 𝒦 :=
      Subgroup.eq_of_le_of_card_ge hALJ (by rw [hcardJ, hc])
    have hb : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      intro φ hφ
      rw [← hEq] at hφ
      exact ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxB⟩) hLx hφ
    exact hx1 (by simpa using congrArg Subtype.val (hfix _ hb))
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    have hij' : σ.symm i ≠ σ.symm j := fun h => hij (σ.symm.injective h)
    rw [hM, CoxeterMatrix.reindex_apply]
    simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij']
    split_ifs <;> omega
  have hns : ¬ GGSplitLie 3 L :=
    ggSecFive_not_split_of_not_tier1 hcfg hReg hsix.1 (Or.inl (Or.inl ⟨m, σ, by omega, hM⟩))
  obtain ⟨lab₀, hΛ₀, hhas₀, R₀, _, I₀, F₀, θ₀, hP₀⟩ := largeEvenMarking_exists_hasLabel hq
  have hn₀ : lab₀.n = 1 := by
    have h1 : 1 ≤ lab₀.n := hΛ₀.1
    have h2 : lab₀.n < 2 := hP₀.1
    omega
  have hlab : GGInnerDiagOnLabel (fun p lab => lab.n = 1 ∧ (ggRowP_ESU p lab ∨ ggRowP_EOmM p lab ∨
      ggRowP_ETwE6 p lab ∨ (p = 3 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨
        ggRowP_NF4 p lab)))) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel ?_
      (ggL_baseLabel_of_nonSplit hcfg hsix.1 hle3 hns)
    intro lab hΛ hhas hrow'
    have htag : lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
      obtain ⟨t, r, n⟩ := lab
      simp only [ggRowP_ESU, ggRowP_EOmM, ggRowP_ETwE6, ggRowP_EOmP, ggRowP_EE7, ggRowP_EE8,
        ggRowP_NF4] at hrow'
      dsimp only at hrow' ⊢
      rcases hrow' with ⟨⟨rfl, -⟩ | ⟨rfl, rfl⟩, -⟩ | ⟨rfl, h5, -, -⟩ | ⟨rfl, -⟩ |
        ⟨-, -, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
      all_goals refine ⟨by decide, fun h => ?_⟩
      all_goals first | exact absurd h (by decide) | omega
    have hiso : GGLabelIso lab lab₀ := ggLabelRigidInput_holds lab lab₀ _ hΛ hΛ₀ hhas hhas₀
    have hn : lab.n = 1 := (NSJoin.ggLabelIso_n_eq hiso htag.1 htag.2).trans hn₀
    rcases hrow' with h1 | h2 | h3' | ⟨hn', hp3, h4⟩
    · exact ⟨hn, Or.inl h1⟩
    · exact ⟨hn, Or.inr (Or.inl h2)⟩
    · exact ⟨hn, Or.inr (Or.inr (Or.inl h3'))⟩
    · exact ⟨hn', Or.inr (Or.inr (Or.inr ⟨hp3, h4⟩))⟩
  have hU : GGInnerDiagOnLabel (fun p lab => (lab.tag = .twA ∧ lab.rank = m - 1 ∧ lab.n = 1) ∨
      (lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) ∨
      (∃ (r m' N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M' : CoxeterMatrix (Fin N)),
        GGTBTorRowAt p lab r m' N C M' ∧ (N + 1 < m ∨ ¬ Nat.card M'.Group ∣ (m + 1).factorial ∨
          Nat.card M'.Group = (m + 1).factorial)) ∨
      GGF4ThreeLabel p lab ∨ GGTwE6BadLabel p lab) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono' ?_ hlab
    rintro lab ⟨hn, h1 | h2 | h3' | ⟨-, h4 | h5 | h6 | h7⟩⟩
    · exact PZ.label_cases hn hm (Or.inl h1)
    · exact PZ.label_cases hn hm (Or.inr (Or.inl h2))
    · exact PZ.label_cases hn hm (Or.inr (Or.inr (Or.inl h3')))
    · exact PZ.label_cases hn hm (Or.inr (Or.inr (Or.inr (Or.inl h4))))
    · exact PZ.label_cases hn hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    · exact PZ.label_cases hn hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
    · exact PZ.label_cases hn hm (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7))))))
  have hT : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = m - 1 ∧ lab.n = 1) 3
      Bs L := by
    rcases GGInnerDiagOnLabel.elim_or hU with hT | hrest
    · exact hT
    exfalso
    rcases GGInnerDiagOnLabel.elim_or hrest with h5 | hrest
    ·
      by_cases hm5 : m = 5
      · subst hm5
        exact hU6 G B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hsix σ hM hcard hq hxL h5
      · obtain ⟨hperf, F, _, _, θ, hF4, hBsN, hI⟩ := exists_unitaryDatum_of_innerDiagOnLabel_twA5 h5
        have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
          inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx hcyc
        have h6 := E6QTwo.card_le_three_pow_six_of_twA5 hF4 θ hperf hBs hxB hBL hBsN hI
        rw [hcard] at h6
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h6
        omega
    rcases GGInnerDiagOnLabel.elim_or hrest with hrows | hrest
    ·
      obtain ⟨r, m', N, C, M', hPN, hWL, hleN⟩ := hcfg.exists_weylOfType_of_tbTorRow hW hLift hTBF
        (fun _ _ N _ M' => N + 1 < m ∨ ¬ Nat.card M'.Group ∣ (m + 1).factorial ∨
          Nat.card M'.Group = (m + 1).factorial) hrows
      have hcardL : Nat.card (ggAutomizer L Bs) = Nat.card M'.Group := by
        obtain ⟨f, -⟩ := hWL
        exact (Nat.card_congr f.toEquiv).symm
      rcases hPN with hN | hndvd | heq
      · rw [hcard] at hleN
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hleN
        omega
      · exact hndvd (hcardL ▸ hdvdL)
      · exact hne (hcardL.trans heq)
    rcases GGInnerDiagOnLabel.elim_or hrest with hF4 | hE6b
    ·
      have hM4 : GGF4ThreeMarking Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP) hF4
      have hrank : ∀ hN' : Bs ≤ Subgroup.normalizer (L : Set G),
          3 ^ 4 ≤ Nat.card (ggGamma L hN').range := by
        intro hN'
        have hmul := card_range_ggGamma_mul_of Nat.prime_three hBs hxB hx1 hLx hcyc hN'
        rw [hcard] at hmul
        have h5 : 3 ^ 4 * 3 ≤ Nat.card (ggGamma L hN').range * 3 := by
          rw [hmul]
          calc 3 ^ 4 * 3 = 3 ^ 5 := by norm_num
            _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
        exact Nat.le_of_mul_le_mul_right h5 (by norm_num)
      exact ggRow_absurd_of_framePair hcfg hsix.1 hle3 hALJ
        (ggF4Three_framePair_of_rank hconf hM4 hrank)
    ·
      have hWL : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizer L Bs) := ggTwE6Bad_weylOfType hR hE6b
      have h7 := hcfg.card_le_pow_succ_of_weylOfType_L hTBF hWL
      rw [hcard, Fintype.card_fin] at h7
      have hm7 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h7
      obtain rfl : m = 5 := by omega
      have hcardL : Nat.card (ggAutomizer L Bs) = 51840 := by
        obtain ⟨f, -⟩ := hWL
        exact (Nat.card_congr f.toEquiv).symm.trans card_coxeterE6_group
      rw [hcardL] at hdvdL
      exact absurd hdvdL (by decide)
  have hm3 : ¬ 3 ∣ m := by omega
  have hTrow : GGInnerDiagOnLabel (fun p lab => ∃ (r m' N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M' : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m' N C M' ∧
        (N = m - 1 ∧ GGIntCartan M' C ∧ (∀ i j, M' i j ≠ 6) ∧ IsUnit (C.det : ZMod 3) ∧
          ∃ (par : Fin N → Fin N) (root : Fin N) (depth : Fin N → ℕ),
            (∀ i j, i ≠ j → (C i j ≠ 0 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i)))) ∧
              ∀ i, i ≠ root → depth (par i) < depth i)) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hT
    obtain ⟨⟨ht, hr, hn⟩, hnorm, hinds⟩ := hP
    obtain ⟨t, r, n⟩ := lab
    simp only at ht hr hn
    subst ht hr hn
    obtain ⟨hno6, hpar, hdepth⟩ := ggCartanA_pathTree (k := m - 1) ⟨0, by omega⟩ rfl
    refine ⟨⟨_, _, m - 1, CartanMatrix.A (m - 1), CoxeterMatrix.A (m - 1),
      GGTBTorRowAt.aInd (p := 3) (lab := ⟨.twA, m - 1, 1⟩) (Or.inr rfl) (by dsimp only; omega)
        (by simp [ggTorM]), rfl, ggIntCartan_A (m - 1), hno6, ?_, ggPathPar (m - 1),
      ⟨0, by omega⟩, fun i => i.1, hpar, hdepth⟩, hnorm, hinds⟩
    rw [CartanMatrix.A_det]
    refine isUnit_iff_ne_zero.mpr ?_
    have hcast : ((((m - 1 : ℕ) : ℤ) + 1 : ℤ) : ZMod 3) = ((m : ℕ) : ZMod 3) := by
      rw [show m = (m - 1) + 1 by omega]
      push_cast
      ring_nf
    rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
    exact hm3
  obtain ⟨r, m', N, C, M', ⟨rfl, hC, hno6, hdet, par, root, depth, hpar, hdepth⟩, hWL, -⟩ :=
    hcfg.exists_weylOfType_of_tbTorRow hW hLift hTBF _ hTrow
  have hstepL : ∀ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) * (b : G)⁻¹ ∈ L := by
    intro ψ hψ b
    have h := mul_inv_mem_sup_of_mem_sup_ggAutomizer hNL hNL
      (Subgroup.mem_sup_left (S := ggAutomizer L Bs) (T := ggAutomizer L Bs) hψ) b
    rwa [sup_idem] at h
  have hlow : 3 ^ (m - 1) ≤ Nat.card ↥(Bs ⊓ L) := by
    have h := pow_rank_le_card_inf_of_cartan_pairing (by norm_num) hBs hstepL (C := C)
      fun ιV => SecFiveRootRefl.exists_cartan_pairing_of_weylOfType' (by norm_num) hNT hC hno6 par
        root depth hpar hdepth hWL
        (fun _ hφ => mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizer_mono Bs le_top hφ)) ιV
    rwa [rank_eq_card_of_isUnit_det hdet, Fintype.card_fin] at h
  have hxI : x ∉ Bs ⊓ L := fun h => hxL (Subgroup.mem_inf.mp h).2
  have hpow : ∀ {H : Subgroup G}, H ≤ Bs → ∃ k, k ≤ m ∧ Nat.card H = 3 ^ k := by
    intro H hH
    have hd : Nat.card H ∣ 3 ^ m := hcard ▸ Subgroup.card_dvd_of_le hH
    exact (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hcardI : Nat.card ↥(Bs ⊓ L) = 3 ^ (m - 1) := by
    have hlt : Nat.card ↥(Bs ⊓ L) < Nat.card Bs :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hxI (by rw [h]; exact hxB))
    obtain ⟨k, hk, hk'⟩ := hpow (inf_le_left : Bs ⊓ L ≤ Bs)
    rw [hk', hcard] at hlt
    rw [hk'] at hlow ⊢
    have h1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hlow
    congr 1
    omega
  have hdisj : Disjoint (Subgroup.zpowers x) (Bs ⊓ L) := by
    have hord : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ (Bs ⊓ L)) ∣ 3 := by
      rw [← hord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hEq : Subgroup.zpowers x ⊓ (Bs ⊓ L) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3', Nat.card_zpowers, hord])
      have hx : x ∈ Subgroup.zpowers x ⊓ (Bs ⊓ L) := by
        rw [hEq]
        exact Subgroup.mem_zpowers x
      exact hxI (Subgroup.mem_inf.mp hx).2
  have hsup : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
    have hle : Subgroup.zpowers x ⊔ (Bs ⊓ L) ≤ Bs :=
      sup_le (Subgroup.zpowers_le.mpr hxB) inf_le_left
    have hlt : Bs ⊓ L < Subgroup.zpowers x ⊔ (Bs ⊓ L) :=
      lt_of_le_of_ne le_sup_right fun h =>
        hxI (by rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    have hc := Subgroup.card_lt_of_lt hlt
    obtain ⟨k, hk, hk'⟩ := hpow hle
    rw [hcardI, hk'] at hc
    have h1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hc
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hk', hcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
    refine ⟨Bs ⊓ L, inf_le_right, fun g => ⟨1, Subtype.ext (by simpa using hBs.2 g g.2.1)⟩, ?_⟩
    intro hcyc'
    have hexp : Monoid.exponent ↥(Bs ⊓ L) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hBs.2 g g.2.1)
    have hle3' : Nat.card ↥(Bs ⊓ L) ≤ 3 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Nat.le_of_dvd (by norm_num) hexp
    rw [hcardI] at hle3'
    have : 3 ^ 4 ≤ 3 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨hT, ⟨hcard, hcardI⟩, ⟨hsup, hdisj⟩,
    ⟨bstar_le_normalizer_ggG0 hS hnc hconf.2.2.1 hconf.2.1, hcfg.inf_centralizer_ggG0_eq_bot hTBF hWI⟩⟩

theorem ggSecFivePZTwA5Input_of_frame
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) : GGSecFivePZTwA5Input := by
  intro G _ _ B Bs x L D J 𝒦 hcfg _ _ _ ι M e hsix σ hM _ _ _ h5
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR := hcfg.1
  obtain ⟨-, -, hxB, hLx, -⟩ := hR.1.tableB_facts
  have hx1 : x ≠ 1 := hR.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨y, K, hN, -⟩ := hcfg.exists_nbr_sup_le
  have hH : GGResHyp 3 B Bs x L D J y K :=
    ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hN, hcfg.2.1 y K hN, Or.inr hcfg.2.1⟩
  obtain ⟨lab, hΛ, hhas, R₀, _, I₀, F₀, θ₀, ⟨ht, hr, hn⟩, -⟩ := largeEvenMarking_exists_hasLabel h5
  obtain ⟨-, -, ⟨eL⟩⟩ := ggTwA5Three_frame ggLabelRigidInput_holds hLB hPJ hH
    (Or.inl ⟨rfl, rfl⟩) rfl hΛ hhas ⟨ht, hr, by rw [hn]; norm_num⟩
  have hcardL : Nat.card (ggAutomizer L Bs) = 720 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hcardJ : Nat.card (ggAutomizerJoin L Bs 𝒦) = 720 := by
    have h : GGWeylOfType 3 M (ggAutomizerJoin L Bs 𝒦) := ⟨e, hsix.1.2⟩
    rw [hM] at h
    obtain ⟨f, -⟩ := h.of_reindex
    rw [← Nat.card_congr f.toEquiv, l05nK3a_card_coxeterA]
    decide
  have hEq : ggAutomizer L Bs = ggAutomizerJoin L Bs 𝒦 :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardL, hcardJ])
  have hb : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
    intro φ hφ
    rw [← hEq] at hφ
    exact ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxB⟩) hLx hφ
  exact hx1 (by simpa using congrArg Subtype.val (hcfg.eq_one_of_forall_join_fix hTBF hWI _ hb))

theorem GGInnerDiagOn.psiInnerDiag
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {G₀ Bs : Subgroup X} (hID : GGInnerDiagOn Bs G₀)
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) :
    ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b :=
  ggPsiInnerDiag_of_marking hpres (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hID)
    (GGInnerDiagOn.le_normalizer hID)

theorem ggSecFiveOrderSixModularAInput_of_pz
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hW : GGTBTorWRows)
    (hLift : GGTBTorLiftRows) (hU6 : GGSecFivePZTwA5Input) (hK : GGSecFivePZKnownGroupInput) :
    GGSecFiveOrderSixModularAInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hsix m σ hm hM h3 hbig hp3 hq t n f ψ
    hpres
  subst hp3
  obtain ⟨-, -, hxB, -, -⟩ := hcfg.1.1.tableB_facts
  by_cases hxL : x ∈ L
  · have hx : x ∈ ψ.range := by
      rw [hpres.2.1.1]
      exact le_ggG0_left 3 B x L D J hxL
    exact ⟨x⁻¹, ψ.range.inv_mem hx, fun _ _ => ⟨1, Subgroup.one_mem _, fun z _ => by simp⟩⟩
  · have hPZ := ggSecFivePZData_of_not_mem hTBF hWI hW hLift hU6 hcfg hReg hrow hQ hsix hm hM h3
      hbig hq hxL
    exact (hK G B Bs L D J x m hm h3 hcfg.1.1 hcfg.1.2.2.2.1 hPZ t n f ψ hpres).psiInnerDiag hpres
      x hxB

end Cells

end CFSG.StandardType

end
