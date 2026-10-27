module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section DiagField

variable {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*} [Group G]

@[expose] def GGPsiDiagField (ψ : U →* G) (c : G) : Prop :=
  ∃ g ∈ ψ.range, ∀ γ ∈ Δ.roots, ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ Δ.rootGroup γ,
    (c * g)⁻¹ * ψ z * (c * g) = ψ z'

variable {Δ}

theorem mem_normalizer_of_mem_ggTorus {h : U} (hh : h ∈ ggTorus Δ) {γ : Fin Δ.rank → ℤ}
    (hγ : γ ∈ Δ.roots) : h ∈ Subgroup.normalizer (Δ.rootGroup γ : Set U) :=
  Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ

theorem GGPsiInnerDiag.diagField {ψ : U →* G} {c : G} (h : GGPsiInnerDiag Δ ψ c) :
    GGPsiDiagField Δ ψ c := by
  obtain ⟨g, hg, hall⟩ := h
  refine ⟨g, hg, fun γ hγ z hz => ?_⟩
  obtain ⟨h, hh, hz'⟩ := hall γ hγ
  exact ⟨h * z * h⁻¹, (Subgroup.mem_normalizer_iff.mp
    (mem_normalizer_of_mem_ggTorus hh hγ) z).mp hz, hz' z hz⟩

theorem GGPsiDiagField.mul_right {ψ : U →* G} {c g : G} (h : GGPsiDiagField Δ ψ c)
    (hg : g ∈ ψ.range) : GGPsiDiagField Δ ψ (c * g) := by
  obtain ⟨g₀, hg₀, hall⟩ := h
  refine ⟨g⁻¹ * g₀, ψ.range.mul_mem (ψ.range.inv_mem hg) hg₀, fun γ hγ z hz => ?_⟩
  rw [show c * g * (g⁻¹ * g₀) = c * g₀ by group]
  exact hall γ hγ z hz

theorem GGPsiInnerDiag.mul_right {ψ : U →* G} {c g : G} (h : GGPsiInnerDiag Δ ψ c)
    (hg : g ∈ ψ.range) : GGPsiInnerDiag Δ ψ (c * g) := by
  obtain ⟨g₀, hg₀, hall⟩ := h
  refine ⟨g⁻¹ * g₀, ψ.range.mul_mem (ψ.range.inv_mem hg) hg₀, fun γ hγ => ?_⟩
  rw [show c * g * (g⁻¹ * g₀) = c * g₀ by group]
  exact hall γ hγ

theorem conj_eq_mul_of_mem_normalizer {ψ : U →* G} {c u : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hu : u ∈ ψ.range) :
    ∃ g ∈ ψ.range, u⁻¹ * c * u = c * g := by
  have hu' : c⁻¹ * u⁻¹ * c ∈ ψ.range := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) u⁻¹).mp
      (ψ.range.inv_mem hu)
    simpa using this
  exact ⟨c⁻¹ * u⁻¹ * c * u, ψ.range.mul_mem hu' hu, by group⟩

theorem GGPsiDiagField.conj {ψ : U →* G} {c u : G} (h : GGPsiDiagField Δ ψ c)
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hu : u ∈ ψ.range) :
    GGPsiDiagField Δ ψ (u⁻¹ * c * u) := by
  obtain ⟨g, hg, e⟩ := conj_eq_mul_of_mem_normalizer hc hu
  rw [e]
  exact h.mul_right hg

theorem GGPsiInnerDiag.conj {ψ : U →* G} {c u : G} (h : GGPsiInnerDiag Δ ψ c)
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hu : u ∈ ψ.range) :
    GGPsiInnerDiag Δ ψ (u⁻¹ * c * u) := by
  obtain ⟨g, hg, e⟩ := conj_eq_mul_of_mem_normalizer hc hu
  rw [e]
  exact h.mul_right hg

theorem ggPsiInnerDiag_one (ψ : U →* G) : GGPsiInnerDiag Δ ψ 1 :=
  ⟨1, ψ.range.one_mem, fun _ _ => ⟨1, (ggTorus Δ).one_mem, fun z _ => by simp⟩⟩

end DiagField

@[expose] def GGOutdiagPrimeConfig (p : ℕ) (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = .PSL ∧ p ∣ n ∧ p ∣ 2 ^ f - 1) ∨ (t = .PSU ∧ p ∣ n ∧ p ∣ 2 ^ f + 1) ∨
    (t = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ f - 1) ∨ (t = .twistedE6 ∧ p = 3 ∧ 3 ∣ 2 ^ f + 1)

namespace GGSixFusionSetting

variable {G : Type} [Group G] {U : Type} [Group U] {p : ℕ} {Bs G₀ : Subgroup G}
  {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}
  (h : GGSixFusionSetting p Bs G₀ Δ t n f ψ)
include h

theorem presents : GGPresentsG0 G₀ Δ t n f ψ := h.2.1

theorem centralizer_eq_bot : Subgroup.centralizer (G₀ : Set G) = ⊥ := h.2.2.1

theorem innerDiag : ∀ b ∈ Bs, GGPsiInnerDiag Δ ψ b := h.2.2.2.1.2.2

theorem range_eq : ψ.range = G₀ := h.2.1.2.1.1

theorem card_le_card_bstar [Finite G] {E : Subgroup G} (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨P, hBsP, hPM, -⟩ := h.exists_sylow
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'P : E' ≤ (P : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hmem : MulAut.conj g x ∈ ((g • S : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hES hx)
    rw [hg] at hmem
    exact hmem
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [← hcard]
  exact (h.unique P hPM P.isPGroup' hBsP (fun Q _ hQ hPQ => P.is_maximal' hQ hPQ) E' hE'P
    (isElemAbelian_map_hom hE _)).1

theorem pow_four_le [Finite G] (h4 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G))) :
    p ^ 4 ≤ Nat.card Bs := by
  obtain ⟨E, -, -, hE, hcard, -⟩ := h4
  exact hcard.trans (h.card_le_card_bstar hE)

theorem conj_mem_of_mem_centralizer {y m : G} (hy : y ^ p = 1)
    (hm : m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)) : m⁻¹ * y * m ∈ Bs := by
  refine h.omega _ hm ?_
  have e := map_pow (MulAut.conj m⁻¹) y p
  simp only [MulAut.conj_apply, inv_inv] at e
  rw [← e, hy, mul_one, inv_mul_cancel]

theorem not_conj_mem_centralizer {y : G} (hy : y ^ p = 1)
    (hnc : ∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) {m : G}
    (hm : m ∈ Subgroup.normalizer (G₀ : Set G)) :
    m⁻¹ * y * m ∉ Subgroup.centralizer (Bs : Set G) := fun hc =>
  hnc m hm (h.conj_mem_of_mem_centralizer hy hc)

end GGSixFusionSetting

section Inputs

@[expose] def GGOrdPInnerConjAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ GGOutdiagPrimeConfig p t n f →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiInnerDiag (ggU t n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

@[expose] def GGOrdPFieldConjAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiDiagField (ggU t n f).D ψ y →
      ¬ GGPsiInnerDiag (ggU t n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

@[expose] def GGOrdPOutdiagAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → GGOutdiagPrimeConfig p t n f →
    ∀ b ∈ Bs, ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      (∀ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∉ Bs) →
      GGCentralizerEmbeds (Subgroup.normalizer (G₀ : Set G)) y b → n = p

@[expose] def GGOrdPGraphAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ → Subgroup.centralizer (G₀ : Set G) = ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ y ∈ Subgroup.normalizer (G₀ : Set G), y ^ p = 1 →
      ¬ GGPsiDiagField (ggU t n f).D ψ y → t = .POmegaPlus ∧ n = 4 ∧ p = 3

@[expose] def GGOrdPTrialityInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Bs G₀ : Subgroup G) (f : ℕ)
    (ψ : (ggU .POmegaPlus 4 f).K →* G),
    GGSixFusionSetting 3 Bs G₀ (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ →
    GGTwoLocalRankFour 3 (Subgroup.normalizer (G₀ : Set G)) →
    ∀ b ∈ Bs, ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = 3 →
      ¬ GGPsiDiagField (ggU .POmegaPlus 4 f).D ψ y →
      GGCentralizerEmbeds (Subgroup.normalizer (G₀ : Set G)) y b →
        3 ∣ 2 ^ f - 1 ∧
          LieModel (↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y})) ⧸
            Subgroup.center ↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer {y}))) .PSL 3 2 f

end Inputs

end CFSG.StandardType
