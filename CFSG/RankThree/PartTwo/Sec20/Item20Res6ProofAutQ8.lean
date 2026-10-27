module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAutQ8Tools
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def KFactL3OddParabolicInner : Prop :=
  ∀ (n : ℕ), Odd n → ∀ (Y : Type) [Group Y] [Finite Y],
    Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) →
    ∀ X : Subgroup Y, Sec18.IsMaxParabolicRankTwo X →
    ∀ α : MulAut Y, (∃ a : ℕ, α ^ 2 ^ a = 1) → X.map α.toMonoidHom = X →
      ∃ y : Y, α = MulAut.conj y

namespace Res6

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quotAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ CFSG.pCore 2 Y) where
  toFun σ := QuotientGroup.congr (CFSG.pCore 2 Y) (CFSG.pCore 2 Y) σ (CFSG.pCore_map_iso 2 σ)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

omit [Finite G] in
theorem quotAut_apply_mk {Y : Type*} [Group Y] (σ : MulAut Y) (y : Y) :
    quotAut Y σ (y : Y ⧸ CFSG.pCore 2 Y) = ((σ y : Y) : Y ⧸ CFSG.pCore 2 Y) :=
  rfl

theorem exists_mem_cenK_of_kFact (hK : KFactL3OddParabolicInner) {K P : Subgroup G} {n : ℕ}
    (hn : Odd n) (e : K ⧸ CFSG.pCore 2 K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))
    (hpar : Sec18.IsMaxParabolicRankTwo ((P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))))
    {d : G} (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hdP : d ∈ Subgroup.normalizer (P : Set G)) (hd2 : ∃ a : ℕ, d ^ 2 ^ a = 1) :
    ∃ k ∈ K, k⁻¹ * d ∈ cenK K := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  set X := (P.subgroupOf K).map π with hX
  set φ : Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ CFSG.pCore 2 K) :=
    (quotAut K).comp K.normalizerMonoidHom with hφ
  set α := φ ⟨d, hdK⟩ with hα
  have hαmk : ∀ x : K,
      α (π x) = π ⟨d * x * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdK x).mp x.2⟩ := by
    intro x
    rfl
  have hXle : X.map α.toMonoidHom ≤ X := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨d * x * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdK x).mp x.2⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp hdP _).mp hx
    · exact (hαmk x).symm
  have hXα : X.map α.toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hXle
      (le_of_eq (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).symm)
  obtain ⟨a, ha⟩ := hd2
  have hα2 : α ^ 2 ^ a = 1 := by
    have h1 : (⟨d, hdK⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ a = 1 := by
      apply Subtype.ext
      simpa using ha
    rw [hα, ← map_pow, h1, map_one]
  obtain ⟨y, hy⟩ := hK n hn (K ⧸ CFSG.pCore 2 K) ⟨e⟩ X hpar α ⟨a, hα2⟩ hXα
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) y
  refine ⟨k₀, k₀.2, ?_⟩
  refine ⟨mul_mem (inv_mem (Subgroup.le_normalizer k₀.2)) hdK, fun x hx => ?_⟩
  have h1 : π ⟨d * x * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdK x).mp hx⟩ =
      π (k₀ * ⟨x, hx⟩ * k₀⁻¹) := by
    rw [← hαmk ⟨x, hx⟩, hy, MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq] at h1
  have h2' := (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h1
  have h2 : (k₀ : G) * x⁻¹ * (k₀ : G)⁻¹ * (d * x * d⁻¹) ∈ CFSG.Open.pCoreOf 2 K := by
    convert h2' using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hKO : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have h3 := (Subgroup.mem_normalizer_iff.mp (hKO (K.inv_mem k₀.2)) _).mp h2
  have h4 := (Subgroup.mem_normalizer_iff.mp (hKO hx) _).mp h3
  have e1 : x * ((k₀ : G)⁻¹ * ((k₀ : G) * x⁻¹ * (k₀ : G)⁻¹ * (d * x * d⁻¹)) * (k₀ : G)⁻¹⁻¹) *
      x⁻¹ = (k₀ : G)⁻¹ * d * x * ((k₀ : G)⁻¹ * d)⁻¹ * x⁻¹ := by group
  rwa [e1] at h4

theorem exists_two_subgroup_of_le_autIn {H B : Subgroup G} {Q : Subgroup (MulAut B)}
    (hQ : Q ≤ Sec4.autIn H B) (hQ2 : IsPGroup 2 Q) :
    ∃ D : Subgroup G, IsPGroup 2 D ∧ D ≤ H ∧ D ≤ Subgroup.normalizer (B : Set G) ∧
      Q ≤ Sec4.autIn D B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NB := Subgroup.normalizer (B : Set G) with hNB
  set φ := B.normalizerMonoidHom with hφ
  set W : Subgroup NB := (H ⊓ NB).subgroupOf NB ⊓ Q.comap φ with hW
  have hWQ : ∀ σ ∈ Q, ∃ w ∈ W, φ w = σ := by
    intro σ hσ
    obtain ⟨g, hgN, hgH, rfl⟩ := Sec4.mem_autIn_iff.mp (hQ hσ)
    exact ⟨⟨g, hgN⟩, ⟨Subgroup.mem_subgroupOf.mpr ⟨hgH, hgN⟩, hσ⟩, rfl⟩
  set f : W →* Q := (φ.comp W.subtype).codRestrict Q fun w => w.2.2 with hf
  have hfs : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    obtain ⟨w, hw, rfl⟩ := hWQ σ hσ
    exact ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 W))
  have hPtop : (P : Subgroup W).map f = ⊤ := by
    have hS := P.mapSurjective hfs
    have h1 : ((P.mapSurjective hfs : Sylow 2 Q) : Subgroup Q) = ⊤ := by
      have htop : IsPGroup 2 (⊤ : Subgroup Q) := hQ2.to_subgroup ⊤
      exact ((P.mapSurjective hfs).3 htop le_top).symm
    rwa [Sylow.coe_mapSurjective] at h1
  refine ⟨((P : Subgroup W).map W.subtype).map NB.subtype, ?_, ?_, ?_, ?_⟩
  · exact (P.isPGroup'.map _).map _
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp w.2.1).1
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact (w : NB).2
  · intro σ hσ
    have hmem : (⟨σ, hσ⟩ : Q) ∈ (P : Subgroup W).map f := by rw [hPtop]; exact Subgroup.mem_top _
    obtain ⟨w, hwP, hwσ⟩ := hmem
    refine Sec4.mem_autIn_iff.mpr ⟨((w : NB) : G), (w : NB).2, ⟨_, ⟨w, hwP, rfl⟩, rfl⟩, ?_⟩
    have := congrArg Subtype.val hwσ
    exact this

omit [Finite G] in
theorem exists_pow_eq_mul {K : Subgroup G} {d : G} (hd : d ∈ Subgroup.normalizer (K : Set G))
    {k : G} (hk : k ∈ K) (m : ℕ) : ∃ k' ∈ K, (d * k) ^ m = d ^ m * k' := by
  induction m with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨k', hk', he⟩ := ih
    refine ⟨d⁻¹ * k' * d * k, K.mul_mem ?_ hk, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hd) k').mp hk'
      simpa using this
    · rw [pow_succ, he, pow_succ]
      group

end Res6

end CFSG.RankThree.PartTwo.Sec20
