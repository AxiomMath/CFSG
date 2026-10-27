module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

universe u v

section SubImg

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {N : Subgroup Mb}

@[expose] def subImg (b : ↥N →* G) (X : Subgroup Mb) : Subgroup G := (X.subgroupOf N).map b

theorem mem_subImg {b : ↥N →* G} {X : Subgroup Mb} {g : G} :
    g ∈ subImg b X ↔ ∃ (x : Mb) (hx : x ∈ N), x ∈ X ∧ b ⟨x, hx⟩ = g := by
  unfold subImg
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, y.2, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hxX, rfl⟩

theorem subImg_mono (b : ↥N →* G) {X Y : Subgroup Mb} (h : X ≤ Y) : subImg b X ≤ subImg b Y := by
  intro g hg
  obtain ⟨x, hx, hxX, rfl⟩ := mem_subImg.mp hg
  exact mem_subImg.mpr ⟨x, hx, h hxX, rfl⟩

theorem mem_subImg_of_mem (b : ↥N →* G) {X : Subgroup Mb} {x : Mb} (hx : x ∈ N) (hxX : x ∈ X) :
    b ⟨x, hx⟩ ∈ subImg b X :=
  mem_subImg.mpr ⟨x, hx, hxX, rfl⟩

theorem subImg_self (b : ↥N →* G) : subImg b N = b.range := by
  ext g
  rw [mem_subImg]
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, y.2, rfl⟩

theorem subImg_eq_of_agree {N₂ : Subgroup Mb} {b₁ : ↥N →* G} {b₂ : ↥N₂ →* G}
    (hag : ∀ g (h1 : g ∈ N) (h2 : g ∈ N₂), b₁ ⟨g, h1⟩ = b₂ ⟨g, h2⟩) {X : Subgroup Mb}
    (hX1 : X ≤ N) (hX2 : X ≤ N₂) : subImg b₁ X = subImg b₂ X := by
  ext g
  rw [mem_subImg, mem_subImg]
  constructor
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨x, hX2 hxX, hxX, (hag x hx (hX2 hxX)).symm⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨x, hX1 hxX, hxX, hag x (hX1 hxX) hx⟩

theorem subImg_eq_range {b : ↥N →* G} {X : Subgroup Mb} (hX : X ≤ N) :
    subImg b X = (b.comp (Subgroup.inclusion hX)).range := by
  ext g
  rw [mem_subImg]
  constructor
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hxX⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, hX y.2, y.2, rfl⟩

theorem subImg_pCoreOf {b : ↥N →* G} (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ N) :
    pCoreOf 2 (subImg b X) = subImg b (pCoreOf 2 X) := by
  let e : ↥X ≃* ↥(subImg b X) :=
    (Subgroup.subgroupOfEquivOfLe hX).symm.trans (Subgroup.equivMapOfInjective _ b hb)
  have h1 := LieType.BorelTits.map_pCore_mulEquiv 2 e
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← h1] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact mem_subImg.mpr ⟨x.1, hX x.2, ⟨x, hx, rfl⟩, rfl⟩
  · intro hg
    obtain ⟨x, hxN, ⟨y, hy, rfl⟩, rfl⟩ := mem_subImg.mp hg
    refine ⟨e y, ?_, rfl⟩
    rw [← h1]
    exact ⟨y, hy, rfl⟩


theorem derivedSeriesOf_range {H : Type*} [Group H] (f : H →* G) (n : ℕ) :
    derivedSeriesOf f.range n = (derivedSeries H n).map f := by
  induction n with
  | zero => rw [derivedSeriesOf_zero, derivedSeries_zero, MonoidHom.range_eq_map]
  | succ n ih => rw [derivedSeriesOf_succ, ih, derivedSeries_succ, Subgroup.map_commutator]

theorem subImg_perfectCore {b : ↥N →* G} (hb : Function.Injective b) {X : Subgroup Mb}
    (hX : X ≤ N) : perfectCore (subImg b X) = subImg b (perfectCore X) := by
  set f : ↥X →* G := b.comp (Subgroup.inclusion hX) with hf
  have hfi : Function.Injective f := hb.comp (Subgroup.inclusion_injective hX)
  have hr : subImg b X = f.range := subImg_eq_range hX
  ext g
  constructor
  · intro hg
    have hn : ∀ n, g ∈ (derivedSeries ↥X n).map f := fun n => by
      have := Subgroup.mem_iInf.mp hg n
      rwa [hr, derivedSeriesOf_range] at this
    obtain ⟨d, -, hd⟩ := hn 0
    have hd' : ∀ n, d ∈ derivedSeries ↥X n := fun n => by
      obtain ⟨d', hd', hd''⟩ := hn n
      have : d' = d := hfi (hd''.trans hd.symm)
      rwa [this] at hd'
    refine mem_subImg.mpr ⟨d.1, hX d.2, ?_, hd⟩
    refine Subgroup.mem_iInf.mpr fun n => ?_
    rw [derivedSeriesOf_eq_map_derivedSeries]
    exact ⟨d, hd' n, rfl⟩
  · intro hg
    obtain ⟨x, hxN, hxX, rfl⟩ := mem_subImg.mp hg
    refine Subgroup.mem_iInf.mpr fun n => ?_
    rw [hr, derivedSeriesOf_range]
    have := Subgroup.mem_iInf.mp hxX n
    rw [derivedSeriesOf_eq_map_derivedSeries] at this
    obtain ⟨d, hd, hdx⟩ := this
    refine ⟨d, hd, ?_⟩
    have : (⟨x, hxN⟩ : ↥N) = ⟨d.1, hX d.2⟩ := Subtype.ext hdx.symm
    rw [this]
    rfl

theorem commute_iff_of_injective {b : ↥N →* G} (hb : Function.Injective b) {x y : Mb} (hx : x ∈ N)
    (hy : y ∈ N) : b ⟨y, hy⟩ * b ⟨x, hx⟩ = b ⟨x, hx⟩ * b ⟨y, hy⟩ ↔ y * x = x * y := by
  rw [← map_mul, ← map_mul]
  constructor
  · intro h
    have := hb h
    exact congrArg Subtype.val this
  · intro h
    exact congrArg b (Subtype.ext h)

theorem subImg_centerOf {b : ↥N →* G} (hb : Function.Injective b) {X : Subgroup Mb}
    (hX : X ≤ N) : centerOf (subImg b X) = subImg b (centerOf X) := by
  ext g
  constructor
  · rintro ⟨hgX, hgc⟩
    obtain ⟨x, hxN, hxX, rfl⟩ := mem_subImg.mp hgX
    refine mem_subImg.mpr ⟨x, hxN, ⟨hxX, ?_⟩, rfl⟩
    show x ∈ Subgroup.centralizer (X : Set Mb)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_iff_of_injective hb hxN (hX hy)).mp
      (Subgroup.mem_centralizer_iff.mp hgc _ (mem_subImg_of_mem b (hX hy) hy))
  · intro hg
    obtain ⟨x, hxN, ⟨hxX, hxc⟩, rfl⟩ := mem_subImg.mp hg
    refine ⟨mem_subImg_of_mem b hxN hxX, ?_⟩
    show b ⟨x, hxN⟩ ∈ Subgroup.centralizer (subImg b X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨y, hyN, hyX, rfl⟩ := mem_subImg.mp hh
    exact (commute_iff_of_injective hb hxN hyN).mpr
      (Subgroup.mem_centralizer_iff.mp hxc y hyX)

theorem sq_eq_one_iff_of_injective {b : ↥N →* G} (hb : Function.Injective b) {x : Mb}
    (hx : x ∈ N) : b ⟨x, hx⟩ ^ 2 = 1 ↔ x ^ 2 = 1 := by
  have h : b ⟨x, hx⟩ ^ 2 = b (⟨x, hx⟩ ^ 2) := (map_pow b _ 2).symm
  rw [h, ← map_one b]
  constructor
  · intro h'
    exact congrArg Subtype.val (hb h')
  · intro h'
    exact congrArg b (Subtype.ext h')

end SubImg

end CFSG.Quasithin.H13.F431
