module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

section

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

end

end

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1

variable {G Y : Type} [Group G] [Group Y] {L : Subgroup G} (f : ↥L →* Y)

omit [Group Y] in
theorem mem_blockQ_of_mem_pCore {x : ↥L} (hx : x ∈ CFSG.pCore 2 ↥L) : (x : G) ∈ blockQ L := by
  exact ⟨x, hx, rfl⟩

omit [Group Y] in
theorem mem_pCore_of_mem_blockQ {x : ↥L} (hx : (x : G) ∈ blockQ L) : x ∈ CFSG.pCore 2 ↥L := by
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [Subtype.ext hyx] at hy

omit [Group Y] in
theorem commutator_subgroupOf {A : Subgroup G} (hAL : A ≤ L) :
    (⁅A, L⁆).subgroupOf L = ⁅A.subgroupOf L, ⊤⁆ := by
  apply Subgroup.map_injective L.subtype_injective
  have h1 : ⁅A, L⁆ ≤ L := Subgroup.commutator_le.mpr fun a ha l hl =>
    L.mul_mem (L.mul_mem (L.mul_mem (hAL ha) hl) (L.inv_mem (hAL ha))) (L.inv_mem hl)
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left h1, Subgroup.map_commutator,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hAL, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem blockU_range (hkQ : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockQ L) :
    blockU f.range = imgL f (blockU L) := by
  show ⁅blockQ f.range, f.range⁆ = ((⁅blockQ L, L⁆).subgroupOf L).map f
  rw [blockQ_range f hkQ,
    commutator_subgroupOf (A := blockQ L) (CFSG.LieType.BorelTits.pCoreOf_le 2 L),
    Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  rfl

variable [Finite G] (hkQ : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockQ L)
  (hkU : ∀ x : ↥L, f x = 1 → (x : G) ∈ blockU L → (x : G) = 1)
include hkQ hkU

omit hkQ in
theorem mem_centralizer_of_map {x : ↥L} (hxU : (x : G) ∈ blockU L)
    (hc : f x ∈ Subgroup.centralizer (f.range : Set Y)) :
    (x : G) ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hUn : L ≤ Subgroup.normalizer (blockU L : Set G) := le_normalizer_blockU L
  have h1 : f (⟨l, hl⟩ * x * ⟨l, hl⟩⁻¹ * x⁻¹) = 1 := by
    have := Subgroup.mem_centralizer_iff.mp hc (f ⟨l, hl⟩) ⟨_, rfl⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, this]
    group
  have h2 : l * (x : G) * l⁻¹ * (x : G)⁻¹ ∈ blockU L :=
    (blockU L).mul_mem ((Subgroup.mem_normalizer_iff.mp (hUn hl) _).mp hxU)
      ((blockU L).inv_mem hxU)
  have h3 := hkU _ h1 (by simpa using h2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  have := congrArg (· * ((x : G) * l)) h3
  simp only [one_mul] at this
  rw [← this]
  group

theorem blockZ_range : blockZ f.range = imgL f (blockZ L) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hyU, hyc⟩ := Subgroup.mem_inf.mp hy
    rw [blockU_range f hkQ, mem_imgL] at hyU
    obtain ⟨x, hxU, rfl⟩ := hyU
    exact (mem_imgL f).mpr ⟨x, ⟨hxU, mem_centralizer_of_map f hkU hxU hyc⟩, rfl⟩
  · intro y hy
    obtain ⟨x, hxZ, rfl⟩ := (mem_imgL f).mp hy
    obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.mp hxZ
    refine Subgroup.mem_inf.mpr ⟨(blockU_range f hkQ).symm ▸ (mem_imgL f).mpr ⟨x, hxU, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc l l.2)

omit [Group Y] hkQ hkU in
theorem inf_centralizer_blockU_le (hL : IsShort2 L) (h5 : IsAltType L 5) :
    L ⊓ Subgroup.centralizer (blockU L : Set G) ≤ blockQ L := by
  obtain ⟨α, hα, hαk, -⟩ := h5
  have hQL : blockQ L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  set N : Subgroup ↥L := (L ⊓ Subgroup.centralizer (blockU L : Set G)).subgroupOf L
  have hNn : N.Normal := normal_subgroupOf (fun l hl => Subgroup.mem_normalizer_iff.mpr
    fun x => by
      have hUn := le_normalizer_blockU L hl
      constructor
      · rintro ⟨hx, hxc⟩
        refine ⟨L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl), Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro u hu
        have hu' : l⁻¹ * u * l⁻¹⁻¹ ∈ blockU L :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hUn) u).mp hu
        have := Subgroup.mem_centralizer_iff.mp hxc _ hu'
        rw [inv_inv] at this
        calc u * (l * x * l⁻¹) = l * ((l⁻¹ * u * l) * x) * l⁻¹ := by group
          _ = l * (x * (l⁻¹ * u * l)) * l⁻¹ := by rw [this]
          _ = l * x * l⁻¹ * u := by group
      · rintro ⟨hx, hxc⟩
        have hx' : x = l⁻¹ * (l * x * l⁻¹) * l := by group
        refine ⟨by rw [hx']; exact L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl,
          Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro u hu
        have hu' : l * u * l⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp hUn u).mp hu
        have := Subgroup.mem_centralizer_iff.mp hxc _ hu'
        calc u * x = l⁻¹ * ((l * u * l⁻¹) * (l * x * l⁻¹)) * l := by group
          _ = l⁻¹ * ((l * x * l⁻¹) * (l * u * l⁻¹)) * l := by rw [this]
          _ = x * u := by group)
  have hmapn : (N.map α).Normal := hNn.map α hα
  rcases hmapn.eq_bot_or_eq_top with h | h
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥L) ∈ N := hx
    have hαx : α ⟨x, hx.1⟩ = 1 := by
      have : α ⟨x, hx.1⟩ ∈ N.map α := ⟨_, hxN, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    rw [← MonoidHom.mem_ker, hαk] at hαx
    exact mem_blockQ_of_mem_pCore hαx
  · exfalso
    apply (lt_irrefl (blockU L))
    refine lt_of_le_of_lt ?_ hL.2.2.2.2.1
    intro u hu
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    obtain ⟨n, hn, hnl⟩ : α ⟨l, hl⟩ ∈ N.map α := h ▸ Subgroup.mem_top _
    have hq : ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ blockQ L := by
      have : n⁻¹ * ⟨l, hl⟩ ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel]
      rw [hαk] at this
      exact mem_blockQ_of_mem_pCore this
    have hnc : (n : G) * u = u * n := (Subgroup.mem_centralizer_iff.mp hn.2 u hu).symm
    obtain ⟨q, hqd⟩ : ∃ q : G, q = ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) := ⟨_, rfl⟩
    rw [← hqd] at hq
    have hqc : q * u = u * q := Subgroup.mem_centralizer_iff.mp (hL.2.2.1.1 hu).2 _ hq
    have hl' : l = (n : G) * q := by rw [hqd]; simp
    rw [hl', mul_assoc, hqc, ← mul_assoc, hnc, mul_assoc]

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
