module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A6

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
