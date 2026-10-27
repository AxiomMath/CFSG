module

public import CFSG.RankThree.PartOne.SP4C.GACore

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Lin2.Five (tauAut)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts

section Center

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem center_spRev_eq_bot : Subgroup.center ↥(spRev K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : (spRevEquiv K).symm z ∈ Subgroup.center (StatedSp 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply (spRevEquiv K).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz _
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)] at hz'
  have : (spRevEquiv K).symm z = 1 := Subgroup.mem_bot.1 hz'
  rw [Subgroup.mem_bot]
  have h2 := congrArg (spRevEquiv K) this
  rwa [MulEquiv.apply_symm_apply, map_one] at h2

theorem center_Q_eq_bot : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : (spQe K).symm z ∈ Subgroup.center ↥(spRev K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply (spQe K).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz _
  rw [center_spRev_eq_bot] at hz'
  have : (spQe K).symm z = 1 := Subgroup.mem_bot.1 hz'
  rw [Subgroup.mem_bot]
  have h2 := congrArg (spQe K) this
  rwa [MulEquiv.apply_symm_apply, map_one] at h2

theorem ker_eq_center {E : Type*} [Group E] {p : ℕ} {ε : E →* StatedProj (StatedSp 2 K)}
    (hε : IsCentralPQuot p ε) : ε.ker = Subgroup.center E := by
  refine le_antisymm hε.central ?_
  intro z hz
  rw [MonoidHom.mem_ker]
  have : ε z ∈ Subgroup.center (StatedProj (StatedSp 2 K)) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := hε.surjective q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
  rw [center_Q_eq_bot] at this
  exact Subgroup.mem_bot.1 this

theorem exists_induced_aut {E : Type*} [Group E] {p : ℕ} {ε : E →* StatedProj (StatedSp 2 K)}
    (hε : IsCentralPQuot p ε) (c : MulAut E) :
    ∃ α : MulAut (StatedProj (StatedSp 2 K)), ∀ x : E, α (ε x) = ε (c x) := by
  have hmap : (ε.ker).map c.toMonoidHom = ε.ker := by
    rw [ker_eq_center hε]
    exact Subgroup.map_center_eq c
  let e : E ⧸ ε.ker ≃* StatedProj (StatedSp 2 K) :=
    QuotientGroup.quotientKerEquivOfSurjective ε hε.surjective
  let cbar : MulAut (E ⧸ ε.ker) := QuotientGroup.congr ε.ker ε.ker c hmap
  refine ⟨e.symm.trans (cbar.trans e), fun x => ?_⟩
  have h1 : e.symm (ε x) = QuotientGroup.mk x := (MulEquiv.symm_apply_eq e).mpr rfl
  show e (cbar (e.symm (ε x))) = ε (c x)
  rw [h1]
  show e (QuotientGroup.mk (c x)) = ε (c x)
  rfl

end Center

section Frame

variable {G : Type} [Group G] {p : ℕ} {L F : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

structure TFrame (p : ℕ) (L F : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2] where
  hFL : F ≤ L
  ε : ↥L →* StatedProj (StatedSp 2 K)
  hε : IsCentralPQuot p ε
  h₁ : ∀ t ∈ Tsub p K, ∃ x : F, ε (Subgroup.inclusion hFL x) = spQe K t
  h₂ : ∀ x : F, ∃ t ∈ Tsub p K, ε (Subgroup.inclusion hFL x) = spQe K t
  exp : ∀ x ∈ F, x ^ p = 1

omit [Finite K] in
theorem exists_torC_of_mem (t : ↥(spRev K)) (ht : t ∈ Tsub p K) :
    ∃ v : D8Mod p K, t = torC p K v :=
  ⟨(torT p K).symm ⟨t, ht⟩, (congrArg (fun x : ↥(Tsub p K) => (x : ↥(spRev K)))
    ((torT p K).apply_symm_apply ⟨t, ht⟩)).symm⟩

theorem TFrame.conj_mem (T : TFrame p L F K) {u : ↥L}
    (hu : (u : G) ∈ Subgroup.normalizer (F : Set G)) :
    ∀ t ∈ Tsub p K, (spQe K).symm (T.ε u) * t * ((spQe K).symm (T.ε u))⁻¹ ∈ Tsub p K := by
  intro t ht
  obtain ⟨f, hf⟩ := T.h₁ t ht
  have hfmem : (u : G) * (f : G) * (u : G)⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 hu f).1 f.2
  obtain ⟨t', ht', hf'⟩ := T.h₂ ⟨(u : G) * f * (u : G)⁻¹, hfmem⟩
  have hinc : Subgroup.inclusion T.hFL ⟨(u : G) * f * (u : G)⁻¹, hfmem⟩ =
      u * Subgroup.inclusion T.hFL f * u⁻¹ := Subtype.ext rfl
  rw [hinc, map_mul, map_mul, map_inv, hf] at hf'
  have : (spQe K).symm (T.ε u) * t * ((spQe K).symm (T.ε u))⁻¹ = t' := by
    apply (spQe K).injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hf'
  rw [this]
  exact ht'

theorem TFrame.mem_normalizer (T : TFrame p L F K) {m : ↥(spRev K)}
    (hm : m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K))) {u : ↥L}
    (hu : T.ε u = spQe K m) : (u : G) ∈ Subgroup.normalizer (F : Set G) := by
  have key : ∀ (m : ↥(spRev K)), m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) →
      ∀ u : ↥L, T.ε u = spQe K m → ∀ f ∈ F, (u : G) * f * (u : G)⁻¹ ∈ F := by
    intro m hm u hu f hf
    obtain ⟨t, ht, hft⟩ := T.h₂ ⟨f, hf⟩
    have hmt : m * t * m⁻¹ ∈ Tsub p K := (Subgroup.mem_normalizer_iff.1 hm t).1 ht
    obtain ⟨f', hf'⟩ := T.h₁ _ hmt
    have hpow1 : (u * Subgroup.inclusion T.hFL ⟨f, hf⟩ * u⁻¹) ^ p = 1 := by
      rw [conj_pow]
      have : Subgroup.inclusion T.hFL ⟨f, hf⟩ ^ p = 1 := Subtype.ext (T.exp f hf)
      rw [this]
      group
    have hpow2 : (Subgroup.inclusion T.hFL f') ^ p = 1 := Subtype.ext (T.exp f' f'.2)
    have heq : u * Subgroup.inclusion T.hFL ⟨f, hf⟩ * u⁻¹ = Subgroup.inclusion T.hFL f' := by
      apply T.hε.eq_of_map_eq hpow1 hpow2
      rw [map_mul, map_mul, map_inv, hu, hft, hf', map_mul, map_mul, map_inv]
    have := congrArg (fun x : ↥L => (x : G)) heq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at this
    rw [this]
    exact f'.2
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · exact key m hm u hu f
  · intro hf
    have hm' : m⁻¹ ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) :=
      (Subgroup.normalizer _).inv_mem hm
    have hu' : T.ε u⁻¹ = spQe K m⁻¹ := by rw [map_inv, map_inv, hu]
    have := key m⁻¹ hm' u⁻¹ hu' _ hf
    simpa [mul_assoc] using this

end Frame

end CFSG.RankThree.PartOne.SP4C
