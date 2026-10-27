module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOne
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Preds

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U]

@[expose] def GGBstarUniqueIn (p : ℕ) (M Bs : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ M → IsPGroup p P → Bs ≤ P →
    (∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → P ≤ Q → Q = P) →
    ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E →
      Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs)

@[expose] def GGSixFusionSetting (p : ℕ) (Bs G₀ : Subgroup G) (Δ : UniversalRootDatum U)
    (t : StatedLieTag) (n f : ℕ) (ψ : U →* G) : Prop :=
  (p.Prime ∧ p ≠ 2) ∧ GGPresentsG0 G₀ Δ t n f ψ ∧ Subgroup.centralizer (G₀ : Set G) = ⊥ ∧
    (Bs ≤ Subgroup.normalizer (G₀ : Set G) ∧ IsElemAbelian p Bs ∧
      ∀ b ∈ Bs, GGPsiInnerDiag Δ ψ b) ∧
    (∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) ∧
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (G₀ : Set G) ∧
    GGBstarUniqueIn p (Subgroup.normalizer (G₀ : Set G)) Bs

@[expose] def GGTwoLocalRankFour (p : ℕ) (M : Subgroup G) : Prop :=
  ∃ E T : Subgroup G, E ≤ M ∧ IsElemAbelian p E ∧ p ^ 4 ≤ Nat.card E ∧ T ≤ M ∧ T ≠ ⊥ ∧
    IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G)

@[expose] def GGCentralizerEmbeds (M : Subgroup G) (y b : G) : Prop :=
  ∃ θ : ↥(M ⊓ Subgroup.centralizer {y}) →* G, Function.Injective θ ∧
    (∀ c, θ c ∈ M ⊓ Subgroup.centralizer {b}) ∧
    ∀ hy : y ∈ M ⊓ Subgroup.centralizer {y}, θ ⟨y, hy⟩ = b

@[expose] def GGTrialityCaseAt (p : ℕ) (G₀ : Subgroup G) (Δ : UniversalRootDatum U)
    (t : StatedLieTag) (n f : ℕ) (ψ : U →* G) (y : G) : Prop :=
  t = .POmegaPlus ∧ n = 4 ∧ p = 3 ∧ 3 ∣ 2 ^ f - 1 ∧ ¬ GGPsiInnerDiag Δ ψ y ∧
    LieModel (↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y})) ⧸
      Subgroup.center ↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y}))) .PSL 3 2 f

theorem ggSixTrialityCase_iff {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G} {y : G} :
    GGSixTrialityCase p B x L D J Δ t n f ψ y ↔
      GGTrialityCaseAt p (ggG0 p B x L D J) Δ t n f ψ y :=
  Iff.rfl

@[expose] def GGHasTripleValue {p : ℕ} (w : ZMod p → ZMod p) : Prop :=
  ∃ j₁ j₂ j₃ : ZMod p, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧ w j₁ = w j₂ ∧ w j₁ = w j₃

@[expose] def GGTorusCoords (p : ℕ) (Bs G₀ : Subgroup G) (f : ℕ) (z : G)
    (v : G → ZMod p → ZMod p) : Prop :=
  (∀ a ∈ Bs, ∀ b ∈ Bs, ∃ c : ZMod p, ∀ j, v (a * b) j = v a j + v b j + c) ∧
    (∀ a ∈ Bs, (∃ c : ZMod p, ∀ j, v a j = c) → a = 1) ∧
    (∀ a ∈ Bs, ∃ c : ZMod p, ∀ j, v (z⁻¹ * a * z) j = v a (j + 1) + c) ∧
    (∀ z' ∈ Subgroup.normalizer (Bs : Set G), z' ∉ Subgroup.centralizer (Bs : Set G) →
      z' ^ p = 1 → ∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * z' * m ∈ Bs →
        Function.Injective (v (m⁻¹ * z' * m))) ∧
    ∀ a ∈ Bs, ∀ m ∈ Subgroup.normalizer (G₀ : Set G),
      (∃ K : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {m * a * m⁻¹}) ∧
        GGTypeAk f K) → GGHasTripleValue (v a)

end Preds

section Inputs

@[expose] def GGSixLSixElevenKGInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) →
    ∀ b ∈ Bs, ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      (∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
      GGCentralizerEmbeds (Subgroup.normalizer (G₀ : Set G)) y b →
        GGSixLinearCase p t n f ∨ GGTrialityCaseAt p G₀ (ggU t n f).D t n f ψ y

@[expose] def GGSixLinearRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ → GGSixLinearCase p t n f →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      (∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
        Nat.card Bs = p ^ (p - 1)

@[expose] def GGSixLinearTorusModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ → GGSixLinearCase p t n f →
    Nat.card Bs = p ^ (p - 1) →
      (∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (Bs : Set G) → IsPGroup p Q →
        IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
          Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G))) ∧
      ∀ z ∈ Subgroup.normalizer (Bs : Set G), z ∉ Subgroup.centralizer (Bs : Set G) → z ^ p = 1 →
        ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs G₀ f z v

@[expose] def GGSixTwoLocalRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixBstarUnique p B Bs x L D J →
      GGTwoLocalRankFour p (ggM p B x L D J)

@[expose] def GGSixLSixElevenV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixBstarUnique p B Bs x L D J →
    (∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) →
      ∀ b ∈ Bs, Subgroup.centralizer {b} ≤ ggM p B x L D J → ∀ g : G,
        g⁻¹ * b * g ∈ ggM p B x L D J → g ∉ ggM p B x L D J →
          GGSixLinearCase p t n f ∨
            GGSixTrialityCase p B x L D J (ggU t n f).D t n f ψ (g⁻¹ * b * g)

end Inputs

section General

variable {G : Type} [Group G] {U : Type} [Group U] {p : ℕ} {Bs G₀ : Subgroup G}
  {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

theorem ne_one_of_centralizer_le {M : Subgroup G} {b g : G}
    (hC : Subgroup.centralizer {b} ≤ M) (hg : g ∉ M) : b ≠ 1 := by
  rintro rfl
  exact hg (hC (Subgroup.mem_centralizer_singleton_iff.mpr (by simp)))

theorem ggCentralizerEmbeds_conj {M : Subgroup G} {b g : G} (hC : Subgroup.centralizer {b} ≤ M) :
    GGCentralizerEmbeds M (g⁻¹ * b * g) b := by
  refine ⟨(MulAut.conj g).toMonoidHom.comp (M ⊓ Subgroup.centralizer {g⁻¹ * b * g}).subtype,
    ?_, fun c => ?_, fun hy => ?_⟩
  · intro c d hcd
    apply Subtype.ext
    simpa using hcd
  · have hc : (c : G) ∈ Subgroup.centralizer {g⁻¹ * b * g} := c.2.2
    have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer {b} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc g * c * g⁻¹ * b = g * (c * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * c) * g⁻¹ := by rw [hc]
        _ = b * (g * c * g⁻¹) := by group
    exact ⟨hC hc', hc'⟩
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      Subgroup.coe_subtype, MulAut.conj_apply]
    group

namespace GGSixFusionSetting

variable (h : GGSixFusionSetting p Bs G₀ Δ t n f ψ)
include h

theorem prime : p.Prime := h.1.1

theorem ne_two : p ≠ 2 := h.1.2

theorem bstar_le : Bs ≤ Subgroup.normalizer (G₀ : Set G) := h.2.2.2.1.1

theorem elem : IsElemAbelian p Bs := h.2.2.2.1.2.1

theorem omega : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := h.2.2.2.2.1

theorem normalizer_le :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (G₀ : Set G) := h.2.2.2.2.2.1

theorem unique : GGBstarUniqueIn p (Subgroup.normalizer (G₀ : Set G)) Bs := h.2.2.2.2.2.2

theorem exists_sylow [Finite G] : ∃ P : Sylow p G, Bs ≤ (P : Subgroup G) ∧
    (P : Subgroup G) ≤ Subgroup.normalizer (G₀ : Set G) ∧
    ∀ E : Subgroup G, E ≤ (P : Subgroup G) → IsElemAbelian p E → Nat.card E = Nat.card Bs →
      E = Bs := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hBsP, huniq⟩ := exists_sylow_of_bstarUnique h.prime h.elem h.bstar_le h.unique
  have hN : Subgroup.normalizer (((P : Subgroup (Subgroup.normalizer (G₀ : Set G))).map
      (Subgroup.normalizer (G₀ : Set G)).subtype : Subgroup G) : Set G) ≤
        Subgroup.normalizer (G₀ : Set G) := by
    intro k hk
    apply h.normalizer_le
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ ?_ (isElemAbelian_map_hom h.elem _)
      (Subgroup.card_map_of_injective (MulAut.conj k).injective))
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hk a).mp (hBsP ha)
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_map_of_normalizer_le P hN
  refine ⟨Q, by rw [hQ]; exact hBsP, by rw [hQ]; exact Subgroup.map_subtype_le _, ?_⟩
  rw [hQ]
  exact huniq

theorem conj_eq [Finite G] {b g : G} (hb : b ∈ Bs) (hg : g⁻¹ * b * g ∈ Bs) :
    ∃ k ∈ Subgroup.normalizer (Bs : Set G), g⁻¹ * b * g = k⁻¹ * b * k := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, -, -, huniq⟩ := h.exists_sylow
  exact exists_mem_normalizer_conj_eq h.elem P huniq hb hg

theorem not_conj_mem [Finite G] {b g : G} (hb : b ∈ Bs)
    (hC : Subgroup.centralizer {b} ≤ Subgroup.normalizer (G₀ : Set G))
    (hg : g ∉ Subgroup.normalizer (G₀ : Set G)) :
    ∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * (g⁻¹ * b * g) * m ∉ Bs := fun _ hm hy =>
  hg (mem_of_conj_mem_bstar (fun _ hb' _ hg' => h.conj_eq hb' hg') h.normalizer_le hb hC hm hy)

theorem orderOf_conj {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) (g : G) :
    orderOf (g⁻¹ * b * g) = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hbp : orderOf b = p := orderOf_eq_prime (h.elem.2 b hb) hb1
  have ho := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) b
  rw [MulAut.conj_apply, inv_inv] at ho
  rw [ho, hbp]

end GGSixFusionSetting

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.fusionSetting (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥)
    (hU : GGSixBstarUnique p B Bs x L D J) :
    GGSixFusionSetting p Bs (ggG0 p B x L D J) Δ t n f ψ :=
  ⟨⟨h.prime, h.ne_two⟩, h.presents, hC,
    ⟨h.bstar_le_normalizer, h.bstar.2.1, h.2.2.2.2.2.2.1.2⟩, h.bstar.2.2.2,
    h.normalizer_bstar_le, hU⟩

theorem GGSixCtxV2.twoLocalRankFour (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) :
    GGTwoLocalRankFour p (ggM p B x L D J) := by
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := h.stdType.2.1
  have hxD : x ∈ D := h.stdSub.1.2.2.2.1
  have hx1 : x ≠ 1 := h.sstar.2.2.1
  refine ⟨B, T, h.bstar.1.trans h.bstar_le_normalizer, h.sstar.1.1, ?_,
    hTx.trans (h9iii x hxD hx1), ?_, hT2, hBT⟩
  · rw [h.sstar.1.2.1]
    exact Nat.pow_le_pow_right h.prime.pos h.beta.2.2.2
  · rintro rfl
    exact hTB (Subgroup.commutator_bot_left B)

end Ctx

end CFSG.StandardType
