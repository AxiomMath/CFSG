module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G Y : Type} [Group G] [Group Y] {L : Subgroup G} (f : ↥L →* Y)

@[expose] def imgL (A : Subgroup G) : Subgroup Y := (A.subgroupOf L).map f

theorem mem_imgL {A : Subgroup G} {y : Y} :
    y ∈ imgL f A ↔ ∃ x : ↥L, (x : G) ∈ A ∧ f x = y := by
  unfold imgL
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem imgL_le_range (A : Subgroup G) : imgL f A ≤ f.range :=
  Subgroup.map_le_range f _

theorem range_le_normalizer_map {N : Subgroup ↥L} (hN : N.Normal) :
    f.range ≤ Subgroup.normalizer (N.map f : Set Y) := by
  rintro _ ⟨l, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨l * n * l⁻¹, hN.conj_mem n hn l, by simp⟩
  · rintro ⟨n, hn, hny⟩
    refine ⟨l⁻¹ * n * l, by simpa using hN.conj_mem n hn l⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hny]
    group

theorem normal_subgroupOf {A : Subgroup G} (hA : L ≤ Subgroup.normalizer (A : Set G)) :
    (A.subgroupOf L).Normal := by
  constructor
  intro n hn l
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using (Subgroup.mem_normalizer_iff.mp (hA l.2) n).mp hn

theorem range_le_normalizer_imgL {A : Subgroup G} (hA : L ≤ Subgroup.normalizer (A : Set G)) :
    f.range ≤ Subgroup.normalizer (imgL f A : Set Y) :=
  range_le_normalizer_map f (normal_subgroupOf hA)

theorem isPGroup_subgroupOf {A : Subgroup G} (hA : IsPGroup 2 A) :
    IsPGroup 2 (A.subgroupOf L) := by
  intro x
  obtain ⟨n, hn⟩ := hA ⟨((x : ↥L) : G), x.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hn
  simpa using this

variable (hkQ : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockQ L)
include hkQ

theorem blockQ_range : blockQ f.range = imgL f (blockQ L) := by
  have hQn : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have hQ2 : IsPGroup 2 (blockQ L) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
    set P₀ : Subgroup ↥L := (blockQ f.range).comap f
    have hP₀ : IsPGroup 2 P₀ := by
      intro x'
      obtain ⟨n, hn⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 f.range
        ⟨f x', x'.2⟩
      have h1 : f ((x' : ↥L) ^ 2 ^ n) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hn
      obtain ⟨m, hm⟩ := hQ2 ⟨_, hkQ _ h1⟩
      refine ⟨n + m, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hm
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
      exact this
    have hP₀n : P₀.Normal := by
      constructor
      intro n hn l
      show f (l * n * l⁻¹) ∈ blockQ f.range
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 f.range
          ⟨l, rfl⟩) _).mp hn
    have hle : P₀.map L.subtype ≤ blockQ L := by
      refine le_pCoreOf_of_normalized
        ((Subgroup.map_le_range _ _).trans (Subgroup.range_subtype L).le)
        ?_ (hP₀.map _)
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨l, hl⟩ * n * ⟨l, hl⟩⁻¹, hP₀n.conj_mem n hn _, by simp⟩
      · rintro ⟨n, hn, hng⟩
        refine ⟨⟨l, hl⟩⁻¹ * n * ⟨l, hl⟩, by simpa using hP₀n.conj_mem n hn ⟨l, hl⟩⁻¹, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hng ⊢
        rw [hng]
        group
    exact (mem_imgL f).mpr ⟨x, hle ⟨x, hy, rfl⟩, rfl⟩
  · refine le_pCoreOf_of_normalized (imgL_le_range f _) (range_le_normalizer_imgL f hQn) ?_
    exact (isPGroup_subgroupOf (L := L) hQ2).map f

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
