module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Def

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem isSylowTwoOf_top_iff_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X) :
    IsSylowTwoOf (S.subgroupOf X) ⊤ ↔ IsSylowTwoOf S X := by
  have hidx : ((S.subgroupOf X).subgroupOf (⊤ : Subgroup ↥X)).index = (S.subgroupOf X).index :=
    Subgroup.relIndex_top_right (S.subgroupOf X)
  unfold IsSylowTwoOf
  constructor
  · rintro ⟨-, hP, hd⟩
    rw [hidx] at hd
    exact ⟨hSX, hP.of_equiv (Subgroup.subgroupOfEquivOfLe hSX), hd⟩
  · rintro ⟨-, hP, hd⟩
    rw [hidx]
    exact ⟨le_top, hP.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm, hd⟩

theorem exists_sylow_of_isSylowTwoOf_top_cs5 {G : Type} [Group G] {S : Subgroup G}
    (hS : IsSylowTwoOf S ⊤) : ∃ P : Sylow 2 G, (P : Subgroup G) = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  exact ⟨hS.2.1.toSylow hi, rfl⟩

theorem exists_conj_of_isSylowTwoOf_top_cs5 {G : Type} [Group G] [Finite G] {S₀ S : Subgroup G}
    (h₀ : IsSylowTwoOf S₀ ⊤) (h : IsSylowTwoOf S ⊤) :
    ∃ g : G, S = S₀.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf_top_cs5 h
  obtain ⟨P₀, hP₀⟩ := exists_sylow_of_isSylowTwoOf_top_cs5 h₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  refine ⟨g, ?_⟩
  rw [← hP, ← hg, ← hP₀]
  rfl

theorem mem_normalizer_subgroupOf_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X)
    (g : ↥X) :
    g ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (g : Y) ∈ Subgroup.normalizer (S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg h
    by_cases hX : h ∈ X
    · simpa [Subgroup.mem_subgroupOf, SetLike.mem_coe] using hg ⟨h, hX⟩
    · have hS : h ∉ S := fun hh => hX (hSX hh)
      have hc : (g : Y) * h * (g : Y)⁻¹ ∉ X := by
        intro hc
        apply hX
        have e : (g : Y)⁻¹ * ((g : Y) * h * (g : Y)⁻¹) * (g : Y) = h := by group
        have := X.mul_mem (X.mul_mem (X.inv_mem g.2) hc) g.2
        rwa [e] at this
      have hS' : (g : Y) * h * (g : Y)⁻¹ ∉ S := fun hh => hc (hSX hh)
      exact ⟨fun hh => absurd hh hS, fun hh => absurd hh hS'⟩
  · intro hg h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hg (h : Y)

theorem conjSub_subgroupOf_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (g : ↥X) :
    B6.conjSub g (S.subgroupOf X) = (B6.conjSub (g : Y) S).subgroupOf X := by
  ext x
  simp only [B6.mem_conjSub, Subgroup.mem_subgroupOf, SetLike.mem_coe, Subgroup.coe_mul,
    Subgroup.coe_inv, iff_self]

theorem card_subgroupOf_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X) :
    Nat.card (S.subgroupOf X) = Nat.card S :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv

theorem mem_centerSub_subgroupOf_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X)
    (z : ↥X) : z ∈ centerSub (S.subgroupOf X) ↔ (z : Y) ∈ centerSub S := by
  rw [mem_centerSub_cs5, mem_centerSub_cs5, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun s hs => ?_⟩
    simpa using congrArg Subtype.val (hc ⟨s, hSX hs⟩ (Subgroup.mem_subgroupOf.mpr hs))
  · rintro ⟨hz, hc⟩
    exact ⟨hz, fun s hs => Subtype.ext (hc s (Subgroup.mem_subgroupOf.mp hs))⟩

theorem centerSub_subgroupOf_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X) :
    (centerSub (S.subgroupOf X)).map X.subtype = centerSub S := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_centerSub_subgroupOf_cs5 hSX z).mp hz
  · intro hy
    have hyX : y ∈ X := hSX (centerSub_le_cs5 S hy)
    exact ⟨⟨y, hyX⟩, (mem_centerSub_subgroupOf_cs5 hSX ⟨y, hyX⟩).mpr hy, rfl⟩

theorem card_centerSub_subgroupOf_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X) :
    Nat.card (centerSub (S.subgroupOf X)) = Nat.card (centerSub S) := by
  rw [← centerSub_subgroupOf_cs5 hSX]
  exact (Subgroup.card_map_of_injective X.subtype_injective).symm

theorem relIndex_inf_normalizer_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} (hSX : S ≤ X) :
    (X ⊓ Subgroup.normalizer (S : Set Y)).relIndex X =
      (Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X)).index := by
  have e : (X ⊓ Subgroup.normalizer (S : Set Y)).subgroupOf X =
      Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, ← mem_normalizer_subgroupOf_cs5 hSX x]
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  show ((X ⊓ Subgroup.normalizer (S : Set Y)).subgroupOf X).index = _
  rw [e]

theorem ti_of_subgroup_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ} (hSX : S ≤ X)
    (h : RankOneSyl (⊤ : Subgroup ↥X) (S.subgroupOf X) q) :
    ∀ g ∈ X, g ∉ Subgroup.normalizer (S : Set Y) → S ⊓ B6.conjSub g S = ⊥ := by
  intro g hgX hgN
  have hgN' : (⟨g, hgX⟩ : ↥X) ∉ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    fun hc => hgN ((mem_normalizer_subgroupOf_cs5 hSX ⟨g, hgX⟩).mp hc)
  have key := h.ti (⟨g, hgX⟩ : ↥X) (Subgroup.mem_top _) hgN'
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyS, hyc⟩ := Subgroup.mem_inf.mp hy
  have hmem : (⟨y, hSX hyS⟩ : ↥X) ∈
      S.subgroupOf X ⊓ B6.conjSub (⟨g, hgX⟩ : ↥X) (S.subgroupOf X) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hyS, ?_⟩
    rw [conjSub_subgroupOf_cs5]
    exact Subgroup.mem_subgroupOf.mpr hyc
  rw [key, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  simpa using congrArg Subtype.val hmem

theorem core_of_subgroup_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ} (hSX : S ≤ X)
    (h : RankOneSyl (⊤ : Subgroup ↥X) (S.subgroupOf X) q) :
    ∀ N : Subgroup Y, N ≤ X ⊓ Subgroup.normalizer (S : Set Y) →
      (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N = ⊥ := by
  intro N hN hnorm
  have hNX : N ≤ X := hN.trans inf_le_left
  have hNN : N ≤ Subgroup.normalizer (S : Set Y) := hN.trans inf_le_right
  have hMle : N.subgroupOf X ≤ (⊤ : Subgroup ↥X) ⊓
      Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro m hm
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _,
      (mem_normalizer_subgroupOf_cs5 hSX m).mpr (hNN (Subgroup.mem_subgroupOf.mp hm))⟩
  have hMnorm : ∀ x ∈ (⊤ : Subgroup ↥X), ∀ n ∈ N.subgroupOf X,
      x * n * x⁻¹ ∈ N.subgroupOf X := by
    intro x _ n hn
    have := hnorm (x : Y) x.2 (n : Y) (Subgroup.mem_subgroupOf.mp hn)
    rw [Subgroup.mem_subgroupOf]
    simpa using this
  have hM := h.core (N.subgroupOf X) hMle hMnorm
  rw [eq_bot_iff]
  intro n hn
  have hmem : (⟨n, hNX hn⟩ : ↥X) ∈ N.subgroupOf X := Subgroup.mem_subgroupOf.mpr hn
  rw [hM, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  simpa using congrArg Subtype.val hmem

theorem index_of_subgroup_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ} (hSX : S ≤ X)
    (h : RankOneSyl (⊤ : Subgroup ↥X) (S.subgroupOf X) q) :
    (X ⊓ Subgroup.normalizer (S : Set Y)).relIndex X = Nat.card S + 1 := by
  have e1 := h.index
  rw [inf_eq_right.mpr le_top, Subgroup.relIndex_top_right, card_subgroupOf_cs5 hSX] at e1
  rw [relIndex_inf_normalizer_cs5 hSX]
  exact e1

theorem zexp_of_subgroup_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ} (hSX : S ≤ X)
    (h : RankOneSyl (⊤ : Subgroup ↥X) (S.subgroupOf X) q) :
    ∀ z ∈ centerSub S, z * z = 1 := by
  intro z hz
  have hzX : z ∈ X := hSX (centerSub_le_cs5 S hz)
  have hzc : (⟨z, hzX⟩ : ↥X) ∈ centerSub (S.subgroupOf X) :=
    (mem_centerSub_subgroupOf_cs5 hSX ⟨z, hzX⟩).mpr hz
  have h2 := h.zexp ⟨z, hzX⟩ hzc
  simpa using congrArg Subtype.val h2

theorem ztrans_of_subgroup_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ} (hSX : S ≤ X)
    (h : RankOneSyl (⊤ : Subgroup ↥X) (S.subgroupOf X) q) :
    ∀ z ∈ centerSub S, z ≠ 1 → ∀ z' ∈ centerSub S, z' ≠ 1 →
      ∃ b ∈ X ⊓ Subgroup.normalizer (S : Set Y), b * z * b⁻¹ = z' := by
  intro z hz hz1 z' hz' hz'1
  have hzX : z ∈ X := hSX (centerSub_le_cs5 S hz)
  have hz'X : z' ∈ X := hSX (centerSub_le_cs5 S hz')
  have hzc : (⟨z, hzX⟩ : ↥X) ∈ centerSub (S.subgroupOf X) :=
    (mem_centerSub_subgroupOf_cs5 hSX ⟨z, hzX⟩).mpr hz
  have hz'c : (⟨z', hz'X⟩ : ↥X) ∈ centerSub (S.subgroupOf X) :=
    (mem_centerSub_subgroupOf_cs5 hSX ⟨z', hz'X⟩).mpr hz'
  have hzne : (⟨z, hzX⟩ : ↥X) ≠ 1 := fun e => hz1 (by simpa using congrArg Subtype.val e)
  have hz'ne : (⟨z', hz'X⟩ : ↥X) ≠ 1 := fun e => hz'1 (by simpa using congrArg Subtype.val e)
  obtain ⟨b, hb, hbeq⟩ := h.ztrans ⟨z, hzX⟩ hzc hzne ⟨z', hz'X⟩ hz'c hz'ne
  have hbN : (b : Y) ∈ Subgroup.normalizer (S : Set Y) :=
    (mem_normalizer_subgroupOf_cs5 hSX b).mp (Subgroup.mem_inf.mp hb).2
  refine ⟨(b : Y), Subgroup.mem_inf.mpr ⟨b.2, hbN⟩, ?_⟩
  simpa using congrArg Subtype.val hbeq

theorem omega1_of_subgroup_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ} (hSX : S ≤ X)
    (h : RankOneSyl (⊤ : Subgroup ↥X) (S.subgroupOf X) q) :
    ∀ x ∈ S, x * x = 1 → x ∈ centerSub S := by
  intro x hx hx2
  have hxX : x ∈ X := hSX hx
  have h2 : (⟨x, hxX⟩ : ↥X) * ⟨x, hxX⟩ = 1 := Subtype.ext (by simpa using hx2)
  exact (mem_centerSub_subgroupOf_cs5 hSX ⟨x, hxX⟩).mp
    (h.omega1 ⟨x, hxX⟩ (Subgroup.mem_subgroupOf.mpr hx) h2)

theorem RankOneSyl.of_subgroup_cs5 {Y : Type} [Group Y] {X S : Subgroup Y} {q : ℕ} (hSX : S ≤ X)
    (h : RankOneSyl (⊤ : Subgroup ↥X) (S.subgroupOf X) q) : RankOneSyl X S q :=
  { sylow := (isSylowTwoOf_top_iff_cs5 hSX).mp h.sylow
    ti := ti_of_subgroup_cs5 hSX h
    index := index_of_subgroup_cs5 hSX h
    core := core_of_subgroup_cs5 hSX h
    zcard := (card_centerSub_subgroupOf_cs5 hSX).symm.trans h.zcard
    zexp := zexp_of_subgroup_cs5 hSX h
    ztrans := ztrans_of_subgroup_cs5 hSX h
    omega1 := omega1_of_subgroup_cs5 hSX h
    three_le := h.three_le }

end CFSG.Quasithin.H13
