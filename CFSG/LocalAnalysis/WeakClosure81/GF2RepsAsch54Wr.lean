module

import CFSG.Quasithin.Vol2.Ch12Sec6P31SecIn
public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Quasithin.Vol2.Ch11.SecB (E111Reduced)
open CFSG.Quasithin.E2.E22N
open CFSG.Quasithin.E2.E22N.E111R (IsComp)

variable {G : Type} [Group G]

@[expose] noncomputable def autJ (J : Subgroup G) : ↥(normalizer (J : Set G)) →* MulAut ↥J :=
  RonanE111.conjOn le_normalizer normal_in_normalizer

@[expose] noncomputable def autT (T J : Subgroup G) : Subgroup (MulAut ↥J) :=
  (T.subgroupOf (normalizer (J : Set G))).map (autJ J)

@[expose] noncomputable def autQ (T J : Subgroup G) : Subgroup (MulAut ↥J) :=
  ((J ⊔ T ⊓ normalizer (J : Set G)).subgroupOf (normalizer (J : Set G))).map (autJ J)

@[expose] noncomputable def preJ (J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) : Subgroup G :=
  (XQ.comap (autJ J)).map (normalizer (J : Set G)).subtype

@[expose] noncomputable def liftY (T J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    Subgroup G :=
  (J ⊔ T ⊓ normalizer (J : Set G)) ⊓ preJ J XQ

@[expose] noncomputable def liftN (T J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    Subgroup G :=
  liftY T J XQ ⊔ T

@[expose] noncomputable def liftD (T J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    Subgroup G :=
  ⨆ t ∈ T, A1b.conjSub t (preJ J XQ ⊓ J)

theorem autJ_apply (J : Subgroup G) (g : ↥(normalizer (J : Set G))) (m : ↥J) :
    ((autJ J g m : ↥J) : G) = (g : G) * m * (g : G)⁻¹ :=
  RonanE111.conjOn_apply _ _ g m

theorem autJ_eq_one_iff {J : Subgroup G} (g : ↥(normalizer (J : Set G))) :
    autJ J g = 1 ↔ (g : G) ∈ centralizer (J : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := congrArg (fun f : MulAut ↥J => ((f ⟨x, hx⟩ : ↥J) : G)) h
    simp only [autJ_apply, MulAut.one_apply] at h1
    calc x * g = g * x * (g : G)⁻¹ * g := by rw [h1]
      _ = g * x := by group
  · intro h
    refine MulEquiv.ext fun m => Subtype.ext ?_
    rw [autJ_apply, MulAut.one_apply, ← h m m.2, mul_inv_cancel_right]

theorem autJ_eq_iff {J : Subgroup G} {a b : ↥(normalizer (J : Set G))} :
    autJ J a = autJ J b ↔ (a : G)⁻¹ * b ∈ centralizer (J : Set G) := by
  have h := autJ_eq_one_iff (a⁻¹ * b)
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem autJ_of_mem {J : Subgroup G} {x : G} (hx : x ∈ J) :
    autJ J ⟨x, le_normalizer hx⟩ = MulAut.conj (⟨x, hx⟩ : ↥J) := by
  refine MulEquiv.ext fun m => Subtype.ext ?_
  rw [autJ_apply, MulAut.conj_apply]
  rfl

theorem mem_preJ {J : Subgroup G} {XQ : Subgroup (MulAut ↥J)} {x : G} :
    x ∈ preJ J XQ ↔ ∃ h : x ∈ normalizer (J : Set G), autJ J ⟨x, h⟩ ∈ XQ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem preJ_le_normalizer (J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    preJ J XQ ≤ normalizer (J : Set G) :=
  map_subtype_le _

theorem centralizer_le_preJ (J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    centralizer (J : Set G) ≤ preJ J XQ := fun c hc =>
  mem_preJ.mpr ⟨centralizer_le_normalizer _ hc, by
    rw [(autJ_eq_one_iff _).mpr hc]
    exact one_mem _⟩

theorem map_subgroupOf_autJ_eq_innAutOf (J : Subgroup G) :
    (J.subgroupOf (normalizer (J : Set G))).map (autJ J) = innAutOf ↥J := by
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, mem_subgroupOf.mp hg⟩, (autJ_of_mem (mem_subgroupOf.mp hg)).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, le_normalizer x.2⟩, mem_subgroupOf.mpr x.2, autJ_of_mem x.2⟩

theorem innAutOf_le_autQ (T J : Subgroup G) : innAutOf ↥J ≤ autQ T J := by
  rw [← map_subgroupOf_autJ_eq_innAutOf]
  exact map_mono fun x hx => mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))

theorem autT_le_autQ (T J : Subgroup G) : autT T J ≤ autQ T J :=
  map_mono fun x hx => mem_subgroupOf.mpr (mem_sup_right ⟨mem_subgroupOf.mp hx, x.2⟩)

theorem innAutOf_sup_autT (T J : Subgroup G) : innAutOf ↥J ⊔ autT T J = autQ T J := by
  rw [autT, autQ, subgroupOf_sup le_normalizer inf_le_right, inf_subgroupOf_right,
    Subgroup.map_sup, map_subgroupOf_autJ_eq_innAutOf]

private theorem normalizer_le_normalizer_centralizer (J : Subgroup G) :
    normalizer (J : Set G) ≤ normalizer (centralizer (J : Set G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance

private theorem mem_normalizer_inf {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hH hK ⊢
  intro h
  exact ⟨fun hh => ⟨(hH h).mp hh.1, (hK h).mp hh.2⟩, fun hh => ⟨(hH h).mpr hh.1, (hK h).mpr hh.2⟩⟩

private theorem exists_mul_of_le_normalizer {H K : Subgroup G} (hK : K ≤ normalizer (H : Set G))
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left H K hK] at hx
  obtain ⟨h, hh, k, hk, rfl⟩ := hx
  exact ⟨h, hh, k, hk, rfl⟩

private theorem exists_mul_of_le_normalizer' {H K : Subgroup G} (hH : H ≤ normalizer (K : Set G))
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H K hH] at hx
  obtain ⟨h, hh, k, hk, rfl⟩ := hx
  exact ⟨h, hh, k, hk, rfl⟩

private theorem pow_two_pow_mem_of_mem_sup {J S : Subgroup G} (hSN : S ≤ normalizer (J : Set G))
    (hS : IsPGroup 2 S) {a : G} (ha : a ∈ J ⊔ S) : ∃ e : ℕ, a ^ 2 ^ e ∈ J := by
  obtain ⟨j, hj, s, hs, rfl⟩ := exists_mul_of_le_normalizer hSN ha
  obtain ⟨e, he⟩ := hS ⟨s, hs⟩
  have hs1 : s ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have key : ∀ n : ℕ, ∃ j' ∈ J, (j * s) ^ n = j' * s ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, J.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨j', hj', h⟩ := ih
      refine ⟨j' * (s ^ n * j * (s ^ n)⁻¹), J.mul_mem hj'
        ((mem_normalizer_iff.mp (hSN (S.pow_mem hs n)) j).mp hj), ?_⟩
      rw [pow_succ, h, pow_succ]
      group
  obtain ⟨j', hj', h⟩ := key (2 ^ e)
  exact ⟨e, by rw [h, hs1, mul_one]; exact hj'⟩

private theorem isSylowIn_map {K M : Type*} [Group K] [Group M] (f : K →* M) {p : ℕ}
    {P H : Subgroup K} (h : IsSylowIn p P H) : IsSylowIn p (P.map f) (H.map f) := by
  refine ⟨map_mono h.le, h.isPGroup.map f, fun hd => h.not_dvd_relIndex (hd.trans ?_)⟩
  rw [← relIndex_comap]
  exact relIndex_dvd_of_le_left H (le_comap_map f P)

section Reduced

variable {X T J : Subgroup G}

theorem center_eq_bot_of_isComp (hJ : IsComp X J) : center ↥J = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  exact Subtype.ext (RonanE111.center_trivial_of_isComp hJ x x.2
    (mem_centralizer_iff.mpr fun y hy => congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)))

noncomputable def innAutOfEquiv (hJ : IsComp X J) : ↥(innAutOf ↥J) ≃* ↥J :=
  (CFSG.Quasithin.H13.P31Sec.innEquiv (center_eq_bot_of_isComp hJ)).symm

theorem conjSub_eq_or_le_centralizer (hR : E111Reduced G X T) (hJ : IsComp X J) (g : G) :
    A1b.conjSub g J = J ∨ A1b.conjSub g J ≤ centralizer (J : Set G) := by
  rcases (hJ.conj hR.1 g).eq_or_commute hJ with h | h
  · exact Or.inl h
  · exact Or.inr fun x hx => mem_centralizer_iff.mpr fun y hy => (h x hx y hy).symm

theorem conjSub_le_centralizer_of_not_mem (hR : E111Reduced G X T) (hJ : IsComp X J) {g : G}
    (hg : g ∉ normalizer (J : Set G)) : A1b.conjSub g J ≤ centralizer (J : Set G) :=
  (conjSub_eq_or_le_centralizer hR hJ g).resolve_left fun h =>
    hg (E111R.mem_normalizer_of_conjSub_eq h)

theorem le_sup_centralizer (hR : E111Reduced G X T) (hJ : IsComp X J) :
    X ≤ J ⊔ centralizer (J : Set G) := by
  rw [← E111R.iSup_conj_eq hR hJ]
  refine iSup₂_le fun t _ => ?_
  rcases conjSub_eq_or_le_centralizer hR hJ t with h | h
  · rw [h]
    exact le_sup_left
  · exact le_sup_of_le_right h

theorem eq_top_of_le (hR : E111Reduced G X T) (hJ : IsComp X J) {Z : Subgroup G} (hJZ : J ≤ Z)
    (hTZ : T ≤ Z) : Z = ⊤ := by
  have hXZ : X ≤ Z := by
    rw [← E111R.iSup_conj_eq hR hJ]
    refine iSup₂_le fun t ht x hx => ?_
    rw [A1b.mem_conjSub_iff] at hx
    have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (hTZ ht) (hJZ hx)) (inv_mem (hTZ ht))
  rw [eq_top_iff, ← hR.2.2.2.2.2.2]
  exact sup_le hXZ hTZ

theorem range_autJ (hR : E111Reduced G X T) (hJ : IsComp X J) :
    (autJ J).range = autQ T J := by
  refine le_antisymm ?_ (map_le_range _ _)
  rintro _ ⟨g, rfl⟩
  have := hR.1
  have hg : (g : G) ∈ X ⊔ T := by
    rw [hR.2.2.2.2.2.2]
    exact mem_top _
  obtain ⟨x, hx, t, ht, hxt⟩ := mem_sup_of_normal_left.mp hg
  obtain ⟨j, hj, c, hc, rfl⟩ := exists_mul_of_le_normalizer'
    (le_normalizer.trans (normalizer_le_normalizer_centralizer J)) (le_sup_centralizer hR hJ hx)
  have hxN : j * c ∈ normalizer (J : Set G) := hJ.le_normalizer hx
  have htN : t ∈ normalizer (J : Set G) := by
    have : t = (j * c)⁻¹ * g := by rw [← hxt]; group
    rw [this]
    exact mul_mem (inv_mem hxN) g.2
  have hjN : j ∈ normalizer (J : Set G) := le_normalizer hj
  refine ⟨⟨j * t, mul_mem hjN htN⟩, mem_subgroupOf.mpr (mul_mem_sup hj ⟨ht, htN⟩), ?_⟩
  rw [autJ_eq_iff]
  have htC : t⁻¹ ∈ normalizer (centralizer (J : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer J (inv_mem htN)
  have h1 := (mem_normalizer_iff.mp htC c).mp hc
  have h2 : (j * t)⁻¹ * (g : G) = t⁻¹ * c * t⁻¹⁻¹ := by rw [← hxt]; group
  rw [show ((⟨j * t, mul_mem hjN htN⟩ : ↥(normalizer (J : Set G))) : G) = j * t from rfl, h2]
  exact h1

theorem isSylowIn_autT [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J) :
    IsSylowIn 2 (autT T J) (autQ T J) := by
  have h := RonanE111.isSylowIn_compSup hR hJ
  have h' := (E1.isSylowIn_subgroupOf_iff
    (inf_le_right : T ⊓ normalizer (J : Set G) ≤ normalizer (J : Set G))
    (sup_le le_normalizer inf_le_right)).mpr h
  rw [inf_subgroupOf_right] at h'
  exact isSylowIn_map (autJ J) h'

theorem isKGroup_autQ (hK : CFSG.Open.IsKGroup G) (T J : Subgroup G) :
    CFSG.Open.IsKGroup ↥(autQ T J) :=
  ((hK.subgroup (normalizer (J : Set G))).subgroup
    ((J ⊔ T ⊓ normalizer (J : Set G)).subgroupOf (normalizer (J : Set G)))).of_surjective _
    ((autJ J).subgroupMap_surjective _)

theorem isSylowIn_autT_subgroupOf [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J) :
    IsSylowIn 2 ((autT T J).subgroupOf (autQ T J)) ⊤ := by
  have h := (E1.isSylowIn_subgroupOf_iff (autT_le_autQ T J) le_rfl).mpr (isSylowIn_autT hR hJ)
  rwa [subgroupOf_self] at h

section Lift

variable {XQ : Subgroup (MulAut ↥J)}

theorem inf_normalizer_le_preJ (hTX : autT T J ≤ XQ) :
    T ⊓ normalizer (J : Set G) ≤ preJ J XQ := fun _ hs =>
  mem_preJ.mpr ⟨hs.2, hTX (mem_map_of_mem _ (mem_subgroupOf.mpr hs.1))⟩

theorem le_liftD (T J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    preJ J XQ ⊓ J ≤ liftD T J XQ :=
  le_iSup₂_of_le (f := fun t _ => A1b.conjSub t (preJ J XQ ⊓ J)) 1 (one_mem T)
    (le_of_eq (A1b.conjSub_one _).symm)

theorem conjSub_le_sup (hR : E111Reduced G X T) (hJ : IsComp X J) (hTX : autT T J ≤ XQ) {u : G}
    (hu : u ∈ T) :
    A1b.conjSub u (preJ J XQ ⊓ J) ≤ (preJ J XQ ⊓ J) ⊔ centralizer (J : Set G) := by
  by_cases huN : u ∈ normalizer (J : Set G)
  · have huY : u ∈ preJ J XQ := inf_normalizer_le_preJ hTX ⟨hu, huN⟩
    rw [E111R.conjSub_eq_of_mem_normalizer (mem_normalizer_inf (le_normalizer huY) huN)]
    exact le_sup_left
  · exact le_sup_of_le_right ((A1b.conjSub_mono u inf_le_right).trans
      (conjSub_le_centralizer_of_not_mem hR hJ huN))

theorem liftD_le (hR : E111Reduced G X T) (hJ : IsComp X J) (hTX : autT T J ≤ XQ) :
    liftD T J XQ ≤ (preJ J XQ ⊓ J) ⊔ centralizer (J : Set G) :=
  iSup₂_le fun _ hu => conjSub_le_sup hR hJ hTX hu

theorem le_normalizer_liftD (T J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    T ≤ normalizer (liftD T J XQ : Set G) := by
  have key : ∀ g ∈ T, A1b.conjSub g (liftD T J XQ) ≤ liftD T J XQ := fun g hg => by
    rw [liftD, E111R.conjSub_iSup₂]
    refine iSup₂_le fun t ht => ?_
    rw [← A1b.conjSub_mul]
    exact le_iSup₂_of_le (f := fun t _ => A1b.conjSub t (preJ J XQ ⊓ J)) (g * t)
      (T.mul_mem hg ht) le_rfl
  exact fun t ht => E111R.mem_normalizer_of_conjSub_le (key t ht) (key t⁻¹ (inv_mem ht))

theorem liftD_le_liftN (T J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) :
    liftD T J XQ ≤ liftN T J XQ := by
  refine iSup₂_le fun t ht x hx => ?_
  rw [A1b.mem_conjSub_iff] at hx
  have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem (mem_sup_right ht) (mem_sup_left ⟨mem_sup_left hx.2, hx.1⟩))
    (inv_mem (mem_sup_right ht))

theorem liftN_eq_sup (hTX : autT T J ≤ XQ) : liftN T J XQ = liftD T J XQ ⊔ T := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le (liftD_le_liftN T J XQ) le_sup_right)
  intro y hy
  obtain ⟨j, hj, s, hs, rfl⟩ := exists_mul_of_le_normalizer
    (inf_le_right : T ⊓ normalizer (J : Set G) ≤ normalizer (J : Set G)) hy.1
  have hsY : s ∈ preJ J XQ := inf_normalizer_le_preJ hTX hs
  have hjY : j ∈ preJ J XQ := by
    have : j = (j * s) * s⁻¹ := by group
    rw [this]
    exact mul_mem hy.2 (inv_mem hsY)
  exact mul_mem (mem_sup_left (le_liftD T J XQ ⟨hjY, hj⟩)) (mem_sup_right hs.1)

theorem map_liftY (hXQ : XQ ≤ autQ T J) :
    ((liftY T J XQ).subgroupOf (normalizer (J : Set G))).map (autJ J) = XQ := by
  refine le_antisymm ?_ fun σ hσ => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact (mem_preJ.mp (mem_subgroupOf.mp hg).2).2
  · obtain ⟨a, ha, rfl⟩ := hXQ hσ
    exact ⟨a, mem_subgroupOf.mpr ⟨mem_subgroupOf.mp ha, mem_preJ.mpr ⟨a.2, hσ⟩⟩, rfl⟩

theorem map_liftN (hR : E111Reduced G X T) (hJ : IsComp X J) (hTX : autT T J ≤ XQ)
    (hXQ : XQ ≤ autQ T J) :
    ((liftN T J XQ).subgroupOf (normalizer (J : Set G))).map (autJ J) = XQ := by
  refine le_antisymm ?_ ((map_liftY hXQ).symm.le.trans (map_mono fun x hx =>
    mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))))
  rintro _ ⟨g, hg, rfl⟩
  have hg' : (g : G) ∈ liftD T J XQ ⊔ T := liftN_eq_sup hTX ▸ mem_subgroupOf.mp hg
  obtain ⟨d, hd, t, ht, hdt⟩ := exists_mul_of_le_normalizer (le_normalizer_liftD T J XQ) hg'
  obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_le_normalizer'
    (inf_le_right.trans (le_normalizer.trans (normalizer_le_normalizer_centralizer J)))
    (liftD_le hR hJ hTX hd)
  have hyN : y ∈ normalizer (J : Set G) := le_normalizer hy.2
  have hcN : c ∈ normalizer (J : Set G) := centralizer_le_normalizer _ hc
  have htN : t ∈ normalizer (J : Set G) := by
    have : t = (y * c)⁻¹ * g := by rw [← hdt]; group
    rw [this]
    exact mul_mem (inv_mem (mul_mem hyN hcN)) g.2
  have hg'' : g = ⟨y, hyN⟩ * ⟨c, hcN⟩ * ⟨t, htN⟩ := Subtype.ext hdt.symm
  rw [hg'', map_mul, map_mul, (autJ_eq_one_iff ⟨c, hcN⟩).mpr hc, mul_one]
  exact mul_mem (mem_preJ.mp hy.1).2 (hTX (mem_map_of_mem _ (mem_subgroupOf.mpr ht)))

theorem liftN_eq_top_iff (hR : E111Reduced G X T) (hJ : IsComp X J) (hTX : autT T J ≤ XQ)
    (hXQ : XQ ≤ autQ T J) : liftN T J XQ = ⊤ ↔ XQ = autQ T J := by
  constructor
  · intro h
    rw [← map_liftN hR hJ hTX hXQ, h, top_subgroupOf, ← MonoidHom.range_eq_map, range_autJ hR hJ]
  · rintro rfl
    refine eq_top_of_le hR hJ (fun x hx => mem_sup_left ⟨mem_sup_left hx, mem_preJ.mpr
      ⟨le_normalizer hx, innAutOf_le_autQ T J ?_⟩⟩) le_sup_right
    rw [autJ_of_mem hx]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem liftN_lt_top (hR : E111Reduced G X T) (hJ : IsComp X J) (hTX : autT T J ≤ XQ)
    (hXQ : XQ ≤ autQ T J) (hne : XQ ≠ autQ T J) : liftN T J XQ < ⊤ :=
  lt_top_iff_ne_top.mpr fun h => hne ((liftN_eq_top_iff hR hJ hTX hXQ).mp h)

theorem le_liftN (T J : Subgroup G) (XQ : Subgroup (MulAut ↥J)) : T ≤ liftN T J XQ :=
  le_sup_right

theorem isPGroup_ker_autJ_comp (hR : E111Reduced G X T) (hJ : IsComp X J) {K : Subgroup G}
    (hKA : K ≤ J ⊔ T ⊓ normalizer (J : Set G)) (hKN : K ≤ normalizer (J : Set G)) :
    IsPGroup 2 ((autJ J).comp (inclusion hKN)).ker := by
  intro k
  obtain ⟨e, he⟩ := pow_two_pow_mem_of_mem_sup
    (inf_le_right : T ⊓ normalizer (J : Set G) ≤ normalizer (J : Set G))
    (hR.2.2.2.2.2.1.isPGroup.to_le inf_le_left) (hKA (k : ↥K).2)
  refine ⟨e, ?_⟩
  have hkC : ((k : ↥K) : G) ∈ centralizer (J : Set G) :=
    (autJ_eq_one_iff _).mp (MonoidHom.mem_ker.mp k.2)
  have h1 := RonanE111.center_trivial_of_isComp hJ _ he (pow_mem hkC _)
  exact Subtype.ext (Subtype.ext (by simpa using h1))

theorem normal_liftD (hTX : autT T J ≤ XQ) :
    ((liftD T J XQ).subgroupOf (liftN T J XQ)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer (liftD_le_liftN T J XQ), liftN_eq_sup hTX]
  exact sup_le le_normalizer (le_normalizer_liftD T J XQ)

theorem liftD_le_normalizer_conjSub (hR : E111Reduced G X T) (hJ : IsComp X J)
    (hTX : autT T J ≤ XQ) {t : G} (ht : t ∈ T) :
    liftD T J XQ ≤ normalizer (A1b.conjSub t (preJ J XQ ⊓ J) : Set G) := by
  refine iSup₂_le fun t' ht' => ?_
  by_cases h : A1b.conjSub t' J = A1b.conjSub t J
  · have hu : t⁻¹ * t' ∈ normalizer (J : Set G) := E111R.mem_normalizer_of_conjSub_eq (by
      rw [A1b.conjSub_mul, h, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one])
    have huY : t⁻¹ * t' ∈ preJ J XQ :=
      inf_normalizer_le_preJ hTX (mem_inf.mpr ⟨T.mul_mem (T.inv_mem ht) ht', hu⟩)
    have h1 : A1b.conjSub (t⁻¹ * t') (preJ J XQ ⊓ J) = preJ J XQ ⊓ J :=
      E111R.conjSub_eq_of_mem_normalizer (mem_normalizer_inf (le_normalizer huY) hu)
    have h2 : A1b.conjSub t' (preJ J XQ ⊓ J) = A1b.conjSub t (preJ J XQ ⊓ J) := by
      calc A1b.conjSub t' (preJ J XQ ⊓ J)
          = A1b.conjSub t (A1b.conjSub (t⁻¹ * t') (preJ J XQ ⊓ J)) := by
            rw [← A1b.conjSub_mul, mul_inv_cancel_left]
        _ = A1b.conjSub t (preJ J XQ ⊓ J) := by rw [h1]
    rw [h2]
    exact le_normalizer
  · rcases (hJ.conj hR.1 t').eq_or_commute (hJ.conj hR.1 t) with h' | h'
    · exact absurd h' h
    · intro x hx
      refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
      exact (h' x (A1b.conjSub_mono t' inf_le_right hx) y (A1b.conjSub_mono t inf_le_right hy)).symm

theorem isCompositionFactor_of_liftD [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    (hTX : autT T J ≤ XQ) {L : Type} [Group L]
    (h : E1.IsCompositionFactor ↥(liftD T J XQ) L) :
    E1.IsCompositionFactor ↥(preJ J XQ ⊓ J) L := by
  classical
  have : Fintype ↥T := Fintype.ofFinite _
  set B := preJ J XQ ⊓ J with hB
  set D := liftD T J XQ with hD
  set f : ↥T → Subgroup ↥D := fun t => (A1b.conjSub (t : G) B).subgroupOf D with hf
  have hfD : ∀ t : ↥T, A1b.conjSub (t : G) B ≤ D := fun t =>
    le_iSup₂_of_le (f := fun t _ => A1b.conjSub t B) (t : G) t.2 le_rfl
  have hnorm : ∀ N ∈ Finset.univ.image f, N.Normal := by
    intro N hN
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hN
    exact (normal_subgroupOf_iff_le_normalizer (hfD t)).mpr
      (liftD_le_normalizer_conjSub hR hJ hTX t.2)
  have hDeq : D = ⨆ t : ↥T, A1b.conjSub (t : G) B :=
    iSup_subtype' (p := fun t => t ∈ T) (f := fun t _ => A1b.conjSub t B)
  have hmap : ∀ t : ↥T, (f t).map D.subtype = A1b.conjSub (t : G) B := fun t =>
    map_subgroupOf_eq_of_le (hfD t)
  have hsup : (Finset.univ.image f).sup id = ⊤ := by
    rw [Finset.sup_image, Finset.sup_univ_eq_iSup]
    apply map_injective D.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    exact (iSup_congr hmap).trans hDeq.symm
  obtain ⟨N, hN, hcf⟩ := H13.L829N.isCompositionFactor_of_finset_sup _ hnorm hsup h
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hN
  have h1 := (H13.L829N.isCompositionFactor_congr (subgroupOfEquivOfLe (hfD t))).mp hcf
  exact (H13.L829N.isCompositionFactor_congr (equivMapOfInjective B
    (MulAut.conj (t : G)).toMonoidHom (MulAut.conj (t : G)).injective).symm).mp h1

theorem isCompositionFactor_of_liftN [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    (hTX : autT T J ≤ XQ) (hXQ : XQ ≤ autQ T J) {L : Type} [Group L]
    (h : E1.IsCompositionFactor ↥(liftN T J XQ) L) (hnab : ∃ a b : L, a * b ≠ b * a) :
    E1.IsCompositionFactor ↥XQ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := normal_liftD hTX
  have h1 : E1.IsCompositionFactor ↥(liftD T J XQ) L := by
    rcases isCompositionFactor_of_normal ((liftD T J XQ).subgroupOf (liftN T J XQ)) h with
      h' | h'
    · exact (H13.L829N.isCompositionFactor_congr
        (subgroupOfEquivOfLe (liftD_le_liftN T J XQ))).mp h'
    · exfalso
      have hP : IsPGroup 2 (↥(liftN T J XQ) ⧸ (liftD T J XQ).subgroupOf (liftN T J XQ)) := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        have hx : (x : G) ∈ liftD T J XQ ⊔ T := liftN_eq_sup hTX ▸ x.2
        obtain ⟨e, he⟩ := pow_two_pow_mem_of_mem_sup (le_normalizer_liftD T J XQ)
          hR.2.2.2.2.2.1.isPGroup hx
        refine ⟨e, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
        simpa using he
      have := hP.isNilpotent
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
        inferInstance h' a b)
  have h2 := isCompositionFactor_of_liftD hR hJ hTX h1
  have hBY : preJ J XQ ⊓ J ≤ liftY T J XQ := fun x hx => ⟨mem_sup_left hx.2, hx.1⟩
  have hYN : liftY T J XQ ≤ normalizer (J : Set G) := inf_le_right.trans (preJ_le_normalizer J XQ)
  have : ((preJ J XQ ⊓ J).subgroupOf (liftY T J XQ)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBY).mpr fun y hy =>
      mem_normalizer_inf (le_normalizer hy.2) (hYN hy)
  have h3 : E1.IsCompositionFactor ↥(liftY T J XQ) L :=
    kbr_isCompositionFactor_of_normal_subgroup _
      ((H13.L829N.isCompositionFactor_congr (subgroupOfEquivOfLe hBY)).mpr h2)
  have hrange : ((autJ J).comp (inclusion hYN)).range = XQ := by
    rw [MonoidHom.range_comp, inclusion_range, map_liftY hXQ]
  rcases isCompositionFactor_of_normal ((autJ J).comp (inclusion hYN)).ker h3 with h4 | h4
  · exfalso
    have := (isPGroup_ker_autJ_comp (K := liftY T J XQ) hR hJ inf_le_left hYN).isNilpotent
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      inferInstance h4 a b)
  · exact (H13.L829N.isCompositionFactor_congr
      ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange))).mp h4

end Lift

theorem inf_ne_bot_of_isComp [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J) :
    T ⊓ J ≠ ⊥ := by
  have := hJ.simple
  obtain ⟨-, x, hx⟩ :=
    CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hJ.nonabelian
  refine E111R.inf_ne_bot hR hJ ⟨x, x.2, fun h => ?_, ?_⟩
  · have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this

theorem le_of_innAutOf_le [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    {Z : Subgroup G} (hTZ : T ≤ Z)
    (h : innAutOf ↥J ≤ (Z.subgroupOf (normalizer (J : Set G))).map (autJ J)) : J ≤ Z := by
  refine E111R.le_of_diag hJ.simple (inf_ne_bot_of_isComp hR hJ) hTZ fun x hx => ?_
  obtain ⟨k, hk, hkx⟩ := h (show MulAut.conj (⟨x, hx⟩ : ↥J) ∈ innAutOf ↥J from ⟨⟨x, hx⟩, rfl⟩)
  refine ⟨k, mem_subgroupOf.mp hk, ?_⟩
  have : autJ J ⟨x, le_normalizer hx⟩ = autJ J k := by rw [autJ_of_mem hx, hkx]
  exact autJ_eq_iff.mp this

theorem autT_le_map_subtype {W : Subgroup ↥(autQ T J)}
    (hTW : (autT T J).subgroupOf (autQ T J) ≤ W) : autT T J ≤ W.map (autQ T J).subtype :=
  fun σ hσ => ⟨⟨σ, autT_le_autQ T J hσ⟩, hTW (mem_subgroupOf.mpr hσ), rfl⟩

theorem map_subtype_ne_of_lt_top {W : Subgroup ↥(autQ T J)} (hW : W < ⊤) :
    W.map (autQ T J).subtype ≠ autQ T J := by
  intro heq
  apply hW.ne
  rw [eq_top_iff]
  intro w _
  have hw : (w : MulAut ↥J) ∈ W.map (autQ T J).subtype := by
    rw [heq]
    exact w.2
  obtain ⟨w', hw', hww'⟩ := hw
  rwa [show w = w' from Subtype.ext hww'.symm]

theorem liftN_mem_calLT [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    {P : ∀ (L : Type) [Group L], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    {W : Subgroup ↥(autQ T J)} (hW : W ∈ calLT P ⊤ ((autT T J).subgroupOf (autQ T J))) :
    liftN T J (W.map (autQ T J).subtype) ∈ calLT P ⊤ T := by
  obtain ⟨hTW, hWt, hWcf⟩ := hW
  have hTX := autT_le_map_subtype hTW
  have hXQ : W.map (autQ T J).subtype ≤ autQ T J := map_subtype_le W
  refine ⟨le_sup_right, liftN_lt_top hR hJ hTX hXQ (map_subtype_ne_of_lt_top hWt), ?_⟩
  rintro ⟨L, _, hcf, hPL⟩
  have := isCompositionFactor_finite hcf
  exact hWcf ⟨L, inferInstance, (H13.L829N.isCompositionFactor_congr
    (equivMapOfInjective W _ (autQ T J).subtype_injective)).mpr
    (isCompositionFactor_of_liftN hR hJ hTX hXQ hcf (hP L hPL)), hPL⟩

theorem lGen_le_map_lGen [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    {P : ∀ (L : Type) [Group L], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a) :
    lGen P ⊤ ((autT T J).subgroupOf (autQ T J)) ≤
      ((((J ⊔ T ⊓ normalizer (J : Set G)) ⊓ lGen P ⊤ T).subgroupOf
        (normalizer (J : Set G))).map (autJ J)).subgroupOf (autQ T J) := by
  refine iSup₂_le fun W hW w hw => mem_subgroupOf.mpr ?_
  have hTX := autT_le_map_subtype hW.1
  have hXQ : W.map (autQ T J).subtype ≤ autQ T J := map_subtype_le W
  have hK : liftN T J (W.map (autQ T J).subtype) ≤ lGen P ⊤ T :=
    le_iSup₂_of_le (f := fun X _ => X) _ (liftN_mem_calLT hR hJ hP hW) le_rfl
  have h1 : (w : MulAut ↥J) ∈
      ((liftY T J (W.map (autQ T J).subtype)).subgroupOf (normalizer (J : Set G))).map
        (autJ J) := by
    rw [map_liftY hXQ]
    exact mem_map_of_mem _ hw
  obtain ⟨g, hg, hgw⟩ := h1
  exact ⟨g, mem_subgroupOf.mpr ⟨(mem_subgroupOf.mp hg).1,
    hK (mem_sup_left (mem_subgroupOf.mp hg))⟩, hgw⟩

theorem lGen_eq_top_of_autQ [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    {P : ∀ (L : Type) [Group L], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    (h : lGen P ⊤ ((autT T J).subgroupOf (autQ T J)) = ⊤) : lGen P ⊤ T = ⊤ := by
  have hQ : autQ T J ≤ ((lGen P ⊤ T).subgroupOf (normalizer (J : Set G))).map (autJ J) := by
    intro σ hσ
    have h1 := lGen_le_map_lGen hR hJ hP (h ▸ mem_top (⟨σ, hσ⟩ : ↥(autQ T J)))
    have hle : ((J ⊔ T ⊓ normalizer (J : Set G)) ⊓ lGen P ⊤ T).subgroupOf
        (normalizer (J : Set G)) ≤ (lGen P ⊤ T).subgroupOf (normalizer (J : Set G)) :=
      fun x hx => mem_subgroupOf.mpr (mem_subgroupOf.mp hx).2
    exact map_mono hle (mem_subgroupOf.mp h1)
  have hTK : T ≤ lGen P ⊤ T := by
    obtain ⟨W, hW⟩ : (calLT P ⊤ ((autT T J).subgroupOf (autQ T J))).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have hbot : lGen P ⊤ ((autT T J).subgroupOf (autQ T J)) = ⊥ := by simp [lGen, hempty]
      obtain ⟨a, b, hab⟩ := hJ.nonabelian
      apply hab
      have h1 : (⟨MulAut.conj a, innAutOf_le_autQ T J ⟨a, rfl⟩⟩ : ↥(autQ T J)) ∈
          (⊥ : Subgroup ↥(autQ T J)) := by
        rw [← hbot, h]
        exact mem_top _
      have h2 : MulAut.conj a = 1 := congrArg Subtype.val (mem_bot.mp h1)
      have h3 := congrArg (fun f : MulAut ↥J => f b) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc a * b = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [h3]
    exact le_sup_right.trans
      (le_iSup₂_of_le (f := fun X _ => X) _ (liftN_mem_calLT hR hJ hP hW) le_rfl)
  exact eq_top_of_le hR hJ (le_of_innAutOf_le hR hJ hTK ((innAutOf_le_autQ T J).trans hQ)) hTK

theorem autT_subgroupOf_lt_top [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J) :
    (autT T J).subgroupOf (autQ T J) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  rw [subgroupOf_eq_top] at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(innAutOf ↥J) :=
    (isSylowIn_autT hR hJ).isPGroup.to_le ((innAutOf_le_autQ T J).trans h)
  have := (h2.of_equiv (innAutOfEquiv hJ)).isNilpotent
  have := hJ.simple
  obtain ⟨a, b, hab⟩ := hJ.nonabelian
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

theorem inf_le_iSup_conjSub [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J) {P : Subgroup G}
    (hCP : centralizer (J : Set G) ≤ P)
    (hD : (⨆ t ∈ T, A1b.conjSub t (P ⊓ J)) ≤ ⨅ t ∈ T, A1b.conjSub t P) :
    (⨅ t ∈ T, A1b.conjSub t P) ⊓ X ≤ ⨆ t ∈ T, A1b.conjSub t (P ⊓ J) := by
  classical
  have key : ∀ F : Finset G, (∀ t ∈ F, t ∈ T) →
      (⨅ t ∈ T, A1b.conjSub t P) ⊓ (⨆ t ∈ F, A1b.conjSub t J) ≤
        ⨆ t ∈ T, A1b.conjSub t (P ⊓ J) := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; simp
    | insert t₀ F ht₀F ih =>
      intro hF
      have ht₀ : t₀ ∈ T := hF t₀ (Finset.mem_insert_self t₀ F)
      have ih' := ih fun t ht => hF t (Finset.mem_insert_of_mem ht)
      rw [Finset.iSup_insert]
      by_cases hex : ∃ t ∈ F, A1b.conjSub t J = A1b.conjSub t₀ J
      · obtain ⟨t, htF, htK⟩ := hex
        have hle : A1b.conjSub t₀ J ≤ ⨆ t ∈ F, A1b.conjSub t J :=
          htK ▸ le_iSup₂_of_le (f := fun t _ => A1b.conjSub t J) t htF le_rfl
        rwa [sup_of_le_right hle]
      · push Not at hex
        have hXF : (⨆ t ∈ F, A1b.conjSub t J) ≤ centralizer (A1b.conjSub t₀ J : Set G) := by
          refine iSup₂_le fun t htF => ?_
          rcases (hJ.conj hR.1 t).eq_or_commute (hJ.conj hR.1 t₀) with h | h
          · exact absurd h (hex t htF)
          · exact fun x hx => mem_centralizer_iff.mpr fun y hy => (h x hx y hy).symm
        rintro x ⟨hxE, hx⟩
        obtain ⟨k, hk, y, hy, rfl⟩ :=
          exists_mul_of_le_normalizer (hXF.trans (centralizer_le_normalizer _)) hx
        have hyC : t₀⁻¹ * y * t₀ ∈ centralizer (J : Set G) := by
          rw [mem_centralizer_iff]
          intro j hj
          have hc := mem_centralizer_iff.mp (hXF hy) _ (A1b.mem_conjSub_of_mem (g := t₀) hj)
          calc j * (t₀⁻¹ * y * t₀) = t₀⁻¹ * ((t₀ * j * t₀⁻¹) * y) * t₀ := by group
            _ = t₀⁻¹ * (y * (t₀ * j * t₀⁻¹)) * t₀ := by rw [hc]
            _ = (t₀⁻¹ * y * t₀) * j := by group
        have hxP : t₀⁻¹ * (k * y) * t₀ ∈ P :=
          A1b.mem_conjSub_iff.mp (mem_iInf.mp (mem_iInf.mp hxE t₀) ht₀)
        have hkP : t₀⁻¹ * k * t₀ ∈ P := by
          have : t₀⁻¹ * k * t₀ = (t₀⁻¹ * (k * y) * t₀) * (t₀⁻¹ * y * t₀)⁻¹ := by group
          rw [this]
          exact mul_mem hxP (inv_mem (hCP hyC))
        have hkD : k ∈ ⨆ t ∈ T, A1b.conjSub t (P ⊓ J) :=
          le_iSup₂_of_le (f := fun t _ => A1b.conjSub t (P ⊓ J)) t₀ ht₀ le_rfl
            (A1b.mem_conjSub_iff.mpr ⟨hkP, A1b.mem_conjSub_iff.mp hk⟩)
        have hyE : y ∈ ⨅ t ∈ T, A1b.conjSub t P := by
          simpa using mul_mem (inv_mem (hD hkD)) hxE
        exact mul_mem hkD (ih' ⟨hyE, hy⟩)
  have hX : X = ⨆ t ∈ (Set.toFinite (T : Set G)).toFinset, A1b.conjSub t J := by
    rw [← E111R.iSup_conj_eq hR hJ]
    simp only [Set.Finite.mem_toFinset, SetLike.mem_coe]
  intro x hx
  exact key _ (fun t ht => (Set.Finite.mem_toFinset _).mp ht) ⟨hx.1, hX ▸ hx.2⟩

theorem le_liftN_of_isMaxOver [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    {M : Subgroup ↥(autQ T J)} (hM : M < ⊤)
    (hMax : ∀ W : Subgroup ↥(autQ T J), (autT T J).subgroupOf (autQ T J) ≤ W → W < ⊤ → W ≤ M) :
    liftN T J (M.map (autQ T J).subtype) < ⊤ ∧
      ∀ Z : Subgroup G, T ≤ Z → Z < ⊤ → Z ≤ liftN T J (M.map (autQ T J).subtype) := by
  have hTX := autT_le_map_subtype (hMax _ le_rfl (autT_subgroupOf_lt_top hR hJ))
  have hXQ : M.map (autQ T J).subtype ≤ autQ T J := map_subtype_le M
  refine ⟨liftN_lt_top hR hJ hTX hXQ (map_subtype_ne_of_lt_top hM), fun Z hTZ hZt => ?_⟩
  have hZQ : (Z.subgroupOf (normalizer (J : Set G))).map (autJ J) ≤ autQ T J :=
    (map_le_range _ _).trans (range_autJ hR hJ).le
  have hZM : (Z.subgroupOf (normalizer (J : Set G))).map (autJ J) ≤
      M.map (autQ T J).subtype := by
    have hne : (Z.subgroupOf (normalizer (J : Set G))).map (autJ J) ≠ autQ T J := fun heq =>
      hZt.ne (eq_top_of_le hR hJ
        (le_of_innAutOf_le hR hJ hTZ ((innAutOf_le_autQ T J).trans heq.ge)) hTZ)
    have hlt : ((Z.subgroupOf (normalizer (J : Set G))).map (autJ J)).subgroupOf (autQ T J) < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hZQ (subgroupOf_eq_top.mp h))
    have hle := hMax _ (fun σ hσ => mem_subgroupOf.mpr (map_mono (fun x hx =>
      mem_subgroupOf.mpr (hTZ (mem_subgroupOf.mp hx))) (mem_subgroupOf.mp hσ))) hlt
    exact fun σ hσ => ⟨⟨σ, hZQ hσ⟩, hle (mem_subgroupOf.mpr hσ), rfl⟩
  have hE : Z ⊓ X ≤ ⨅ t ∈ T, A1b.conjSub t (preJ J (M.map (autQ T J).subtype)) := by
    intro z hz
    refine mem_iInf.mpr fun t => mem_iInf.mpr fun ht => A1b.mem_conjSub_iff.mpr (mem_preJ.mpr ?_)
    have hzX : t⁻¹ * z * t ∈ X := by simpa using hR.1.conj_mem z hz.2 t⁻¹
    exact ⟨hJ.le_normalizer hzX, hZM ⟨⟨t⁻¹ * z * t, hJ.le_normalizer hzX⟩, mem_subgroupOf.mpr
      (mul_mem (mul_mem (inv_mem (hTZ ht)) hz.1) (hTZ ht)), rfl⟩⟩
  have hDE : liftD T J (M.map (autQ T J).subtype) ≤
      ⨅ t ∈ T, A1b.conjSub t (preJ J (M.map (autQ T J).subtype)) := by
    refine iSup₂_le fun t' ht' => le_iInf₂ fun t ht => ?_
    have h1 : A1b.conjSub (t⁻¹ * t') (preJ J (M.map (autQ T J).subtype) ⊓ J) ≤
        preJ J (M.map (autQ T J).subtype) :=
      (conjSub_le_sup hR hJ hTX (mul_mem (inv_mem ht) ht')).trans
        (sup_le inf_le_left (centralizer_le_preJ J _))
    calc A1b.conjSub t' (preJ J (M.map (autQ T J).subtype) ⊓ J)
        = A1b.conjSub t (A1b.conjSub (t⁻¹ * t') (preJ J (M.map (autQ T J).subtype) ⊓ J)) := by
          rw [← A1b.conjSub_mul, mul_inv_cancel_left]
      _ ≤ A1b.conjSub t (preJ J (M.map (autQ T J).subtype)) := A1b.conjSub_mono t h1
  have hZD : Z ⊓ X ≤ liftD T J (M.map (autQ T J).subtype) := fun z hz =>
    inf_le_iSup_conjSub hR hJ (centralizer_le_preJ J _) hDE ⟨hE hz, hz.2⟩
  intro z hz
  have := hR.1
  have hz' : z ∈ X ⊔ T := by
    rw [hR.2.2.2.2.2.2]
    exact mem_top z
  obtain ⟨x, hx, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hz'
  have hxZ : x ∈ Z := by
    have : x = x * t * t⁻¹ := by group
    rw [this]
    exact mul_mem hz (inv_mem (hTZ ht))
  exact mul_mem (liftD_le_liftN T J _ (hZD ⟨hxZ, hx⟩)) (mem_sup_right ht)

theorem pRank_map_autJ [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} (hK : K ≤ J ⊔ T ⊓ normalizer (J : Set G)) :
    CFSG.Open.pRank p ((K.subgroupOf (normalizer (J : Set G))).map (autJ J)) =
      CFSG.Open.pRank p K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ normalizer (J : Set G) := hK.trans (sup_le le_normalizer inf_le_right)
  have hrange : ((autJ J).comp (inclusion hKN)).range =
      (K.subgroupOf (normalizer (J : Set G))).map (autJ J) := by
    rw [MonoidHom.range_comp, inclusion_range]
  have hker : ¬ p ∣ Nat.card ((autJ J).comp (inclusion hKN)).ker := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_ker_autJ_comp hR hJ hK hKN)
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  rw [← hrange, CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (QuotientGroup.quotientKerEquivRange ((autJ J).comp (inclusion hKN))),
    CFSG.SectionRank.pRank_quotient_eq _ hker]

theorem pRank_le_of_le_map [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} (hK : K ≤ J ⊔ T ⊓ normalizer (J : Set G))
    {W : Subgroup ↥(autQ T J)}
    (hW : W.map (autQ T J).subtype ≤ (K.subgroupOf (normalizer (J : Set G))).map (autJ J)) :
    CFSG.Open.pRank p W ≤ CFSG.Open.pRank p K :=
  calc CFSG.Open.pRank p W ≤ CFSG.Open.pRank p (W.map (autQ T J).subtype) :=
        CFSG.SectionRank.pRank_le_map hp.one_lt _ (autQ T J).subtype_injective _
    _ ≤ CFSG.Open.pRank p ((K.subgroupOf (normalizer (J : Set G))).map (autJ J)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt hW
    _ = CFSG.Open.pRank p K := pRank_map_autJ hR hJ hp hp2 hK

theorem pRank_lGen_le [Finite G] (hR : E111Reduced G X T) (hJ : IsComp X J)
    {P : ∀ (L : Type) [Group L], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (lGen P ⊤ ((autT T J).subgroupOf (autQ T J))) ≤
      CFSG.Open.pRank p (lGen P ⊤ T) :=
  (pRank_le_of_le_map hR hJ hp hp2 inf_le_left
    (map_le_iff_le_comap.mpr (lGen_le_map_lGen hR hJ hP))).trans
    (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right)

end Reduced

end CFSG.LocalAnalysis.WeakClosure81

end
