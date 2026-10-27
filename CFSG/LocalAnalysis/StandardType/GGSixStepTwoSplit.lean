module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGLemmaThreeFourteenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ X H E : Subgroup G,
    (∀ K L' : Subgroup G, K ≤ X → L' ≤ K → ∀ [(L'.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L'.subgroupOf K) → (∃ a b : K ⧸ L'.subgroupOf K, a * b ≠ b * a) →
        InCatalog (K ⧸ L'.subgroupOf K)) →
    IsElemAbelian p E → Nat.card E = p ^ 2 → GGControlsStrongFusionIn X H E →
      ∀ L₁ : Subgroup G, IsComponentOf L₁ H → ∃ K : Subgroup G, IsComponentOf K X ∧ L₁ ≤ K

section Elementary

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggStepTwo_exists_sylow [Fact p.Prime] (hBsEl : IsElemAbelian p Bs)
    (hNM : Subgroup.normalizer (Bs : Set G) ≤ ggM p B x L D J)
    (h1 : GGSixStepOne p B Bs x L D J) :
    ∃ P : Sylow p G, Bs ≤ (P : Subgroup G) ∧ ∀ E : Subgroup G, E ≤ (P : Subgroup G) →
      IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs := by
  obtain ⟨P, hBsP, huniq⟩ := h1.2.2.2.1
  have hN : Subgroup.normalizer (((P : Subgroup (ggM p B x L D J)).map
      (ggM p B x L D J).subtype : Subgroup G) : Set G) ≤ ggM p B x L D J := by
    intro n hn
    apply hNM
    apply mem_normalizer_of_map_conj_eq
    refine huniq _ ?_ (isElemAbelian_map_hom hBsEl _)
      (Subgroup.card_map_of_injective (MulAut.conj n).injective)
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hn a).mp (hBsP ha)
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_map_of_normalizer_le P hN
  exact ⟨Q, by rw [hQ]; exact hBsP, by rw [hQ]; exact huniq⟩

theorem ggStepTwo_mem_of_conj_mem_bstar (hp : p.Prime) (hBsEl : IsElemAbelian p Bs)
    (hNM : Subgroup.normalizer (Bs : Set G) ≤ ggM p B x L D J)
    (h1 : GGSixStepOne p B Bs x L D J) {b g m : G} (hb : b ∈ Bs)
    (hC : Subgroup.centralizer {b} ≤ ggM p B x L D J) (hm : m ∈ ggM p B x L D J)
    (hy : m⁻¹ * (g⁻¹ * b * g) * m ∈ Bs) : g ∈ ggM p B x L D J := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, -, huniq⟩ := ggStepTwo_exists_sylow hBsEl hNM h1
  exact mem_of_conj_mem_bstar
    (fun _ hb' _ hg' => exists_mem_normalizer_conj_eq hBsEl P huniq hb' hg') hNM hb hC hm hy

omit [Finite G] in
theorem ggStepTwo_centralizer_ne_top [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {b : G} (hb1 : b ≠ 1) : Subgroup.centralizer {b} ≠ ⊤ := by
  intro htop
  apply hb1
  have hz : b ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
  rw [CFSG.RankThree.PartTwo.Sec21.center_eq_bot_of_simple hnonab] at hz
  exact Subgroup.mem_bot.mp hz

omit [Finite G] in
theorem ggStepTwo_kGroup_of_ne_top (hK : KProper InCatalog G) {X : Subgroup G} (hX : X ≠ ⊤) :
    ∀ K L' : Subgroup G, K ≤ X → L' ≤ K → ∀ [(L'.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L'.subgroupOf K) → (∃ a b : K ⧸ L'.subgroupOf K, a * b ≠ b * a) →
        InCatalog (K ⧸ L'.subgroupOf K) := by
  intro K L' hKX hLK _ hs hna
  exact hK K L' (fun h => hX (top_le_iff.mp (h ▸ hKX))) hLK hs hna

end Elementary

section Inputs

@[expose] def GGStepTwoComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
          K ≤ ggM p B x L D J

@[expose] def GGStepTwoBstarFusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ b ∈ Bs, Subgroup.centralizer {b} ≤ ggM p B x L D J → ∀ g : G,
        g⁻¹ * b * g ∈ ggM p B x L D J →
          ∃ m ∈ ggM p B x L D J, m⁻¹ * (g⁻¹ * b * g) * m ∈ Bs

theorem ggStepTwoLemmaSixThirteenInput_of_bstarFusion (h : GGStepTwoBstarFusionInput) :
    GGStepTwoLemmaSixThirteenInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b hb hC g hg
  obtain ⟨m, hm, hy⟩ := h G p B Bs x L D J t n f ψ hctx s1 hlin b hb hC g hg
  obtain ⟨⟨-, hBsEl, -⟩, -, -, -, -, -, -, hNBs⟩ := hctx.2
  exact ggStepTwo_mem_of_conj_mem_bstar hctx.1.2.2.2.2.2.1.1 hBsEl hNBs s1 hb hC hm hy

theorem ggStepTwoSubnormalInput_of_split (h314 : GGLemmaThreeFourteenInput)
    (hK : GGStepTwoComponentInput) : GGStepTwoSubnormalInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair
  have : IsSimpleGroup G := hctx.1.1
  obtain ⟨⟨hBBs, hBsEl, -⟩, ⟨⟨hDB, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hDN : D ≤ Subgroup.centralizer {b} := fun d hd => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hBsEl.1
    exact congrArg Subtype.val (mul_comm' (⟨d, hBBs (hDB hd)⟩ : Bs) ⟨b, hpair.1⟩)
  obtain ⟨K, hKc, hLK⟩ := h314 G p hctx.1.2.2.2.2.2.1.1 hctx.1.2.2.2.2.2.1.2.1
    (Subgroup.centralizer {b}) _ D
    (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1 (ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1))
    hDel hDcard (s1.2.1.inf_in hDN) L₁ hpair.isComponentOf_inf
  have hKM := hK G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hKc hLK
  exact ggIsSubnormal_trans
    (ggIsSubnormal_of_le_of_le hpair.isComponentOf_inf.2.1 hLK (le_inf hKM hKc.1)) hKc.2.1

theorem ggSixStepTwoV2Input_of_split (hfus : GGStepTwoBstarFusionInput)
    (hA : GGStepTwoLinearFusionInput) (h314 : GGLemmaThreeFourteenInput)
    (hK : GGStepTwoComponentInput) (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_inputs (ggStepTwoLemmaSixThirteenInput_of_bstarFusion hfus) hA
    (ggStepTwoSubnormalInput_of_split h314 hK) h615

end Inputs

end CFSG.StandardType
