module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerRaw
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClFrame
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Std
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem corner_single_ne_zero {r : ℕ} (i : Fin r) :
    (Pi.single i (1 : PlaneRaw.F) : PlaneRaw.V r) ≠ 0 := by
  intro h
  have h1 : (1 : PlaneRaw.F) = 0 := by simpa using congrFun h i
  exact one_ne_zero h1

private theorem corner_admissible {r : ℕ} (hr : 4 ≤ r) (i : Fin r) :
    (planeEntry .symplectic r).admissible (PlaneRaw.Code.zero (Finset.univ.erase i)) := by
  refine ⟨hr, ?_⟩
  change 2 ≤ (Finset.univ.erase i).card
  have hc : (Finset.univ.erase i).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [hc]
  omega

private theorem corner_single_mem_cent {r : ℕ} (k : PlaneRaw.PlaneKind) (i : Fin r) :
    (Pi.single i (1 : PlaneRaw.F) : PlaneRaw.V r) ∈
      PlaneRaw.cent k (PlaneRaw.Code.zero (Finset.univ.erase i)) := by
  rw [PlaneRaw.mem_cent_zero]
  intro j hj
  exact Pi.single_eq_of_ne (Finset.mem_erase.mp hj).1 1

private theorem corner_span {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (he : R.coord (Additive.ofMul e) = Pi.single i 1) :
    ggLinImage (p := 3) R.coord (Subgroup.zpowers ((e : ↥L) : ↥L)) =
      Submodule.span PlaneRaw.F ({Pi.single i 1} : Set (PlaneRaw.V r)) := by
  have hmem : (e : ↥L) ∈ Bs.subgroupOf L := e.2
  have h1 := (span_singleton_eq_ggLinImage (p := 3) R.coord hmem).symm
  rw [show (⟨(e : ↥L), hmem⟩ : ↥(Bs.subgroupOf L)) = e from Subtype.ext rfl, he] at h1
  exact h1

private theorem corner_occurs_iff {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1) (X : Subgroup ↥L) :
    IsComponentOf X (⊤ ⊓ Subgroup.centralizer (Subgroup.zpowers (e : ↥L) : Set ↥L)) ↔
      X = R.component (PlaneRaw.Code.zero (Finset.univ.erase i)) := by
  have hmem : (e : ↥L) ∈ Bs.subgroupOf L := e.2
  have hspan := corner_span R he
  have hadm := corner_admissible (r := r) hr i
  have hocc : PlaneRaw.occurs (Submodule.span PlaneRaw.F ({Pi.single i 1} : Set (PlaneRaw.V r)))
      (PlaneRaw.Code.zero (Finset.univ.erase i)) := by
    rw [PlaneRaw.occurs_zero_span_iff]
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [Finset.mem_erase]
      simp [hj]
  constructor
  · intro hX
    obtain ⟨c, hadm', hocc', hXc⟩ :=
      (R.occurs_iff _ (Subgroup.zpowers_le.mpr hmem) X).mp hX
    rw [hspan] at hocc'
    have hc : c = PlaneRaw.Code.zero (Finset.univ.erase i) := by
      refine eq_zero_erase_of_occurs_span_singleton ?_ ?_ ?_ hocc'
      · intro j hj
        exact Pi.single_eq_of_ne hj 1
      · intro h
        exact corner_single_ne_zero i h
      · intro v hv
        rw [hv] at hadm'
        exact lt_of_lt_of_le (by norm_num) hadm'.2.2
    rw [hc] at hXc
    exact hXc
  · rintro rfl
    exact (R.occurs_iff _ (Subgroup.zpowers_le.mpr hmem) _).mpr
      ⟨_, hadm, by rw [hspan]; exact hocc, rfl⟩

theorem inf_centralizer_zpowers_sup_eq {L : Subgroup G} {x z : G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
  have hsub : (Subgroup.zpowers z : Set G) ⊆
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) : Set G) :=
    SetLike.coe_subset_coe.mpr le_sup_right
  refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le hsub)) ?_
  intro g hg
  obtain ⟨hgL, hgz⟩ := Subgroup.mem_inf.mp hg
  refine Subgroup.mem_inf.mpr ⟨hgL, ?_⟩
  have hx : x * g = g * x :=
    Subgroup.mem_centralizer_iff.mp (hLx hgL) x (Set.mem_singleton x)
  have hxg : g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff, Subgroup.zpowers_le,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hx
  rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.mpr hxg
  · rw [Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.mpr hgz

private theorem corner_map_centralizer {L : Subgroup G} (X : Subgroup ↥L) :
    (Subgroup.centralizer (X : Set ↥L)).map L.subtype =
      Subgroup.centralizer (X.map L.subtype : Set G) ⊓ L :=
  CFSG.CGT.PushingUpLit.map_subtype_centralizer X

theorem map_top_inf_centralizer_zpowers {L : Subgroup G} (z : ↥L) :
    ((⊤ : Subgroup ↥L) ⊓ Subgroup.centralizer
        (Subgroup.zpowers z : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G) := by
  rw [Subgroup.map_inf_eq _ _ L.subtype L.subtype_injective, corner_map_centralizer,
    MonoidHom.map_zpowers]
  rw [show (⊤ : Subgroup ↥L).map L.subtype = L from by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]]
  change L ⊓ (Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G) ⊓ L) =
    L ⊓ Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G)
  rw [inf_eq_right.mpr inf_le_right, inf_comm]

theorem subgroupOf_inf_centralizer_zpowers [Finite G] {L : Subgroup G} (z : ↥L) :
    (L ⊓ Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G)).subgroupOf L =
      ⊤ ⊓ Subgroup.centralizer (Subgroup.zpowers z : Set ↥L) := by
  have hZ : (Subgroup.zpowers (z : G)).subgroupOf L = Subgroup.zpowers z := by
    ext w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, Subtype.ext hn⟩, fun ⟨n, hn⟩ => ⟨n, congrArg Subtype.val hn⟩⟩
  rw [CFSG.LocalAnalysis.GLTheoremA.S265.subgroupOf_inf',
    CFSG.LocalAnalysis.GLTheoremA.S265.subgroupOf_centralizer
      (Subgroup.zpowers_le.mpr z.2), hZ, Subgroup.subgroupOf_self]

private theorem corner_component_iff [Finite G] {Bs L : Subgroup G} {x : G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (K : Subgroup G) :
    IsComponentOf K (L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) : Subgroup G) : Set G)) ↔
      K = (R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype := by
  have hCinf := inf_centralizer_zpowers_sup_eq (L := L) (x := x) (z := ((e : ↥L) : G)) hLx
  have hmapEq := map_top_inf_centralizer_zpowers (e : ↥L)
  have hsubEq := subgroupOf_inf_centralizer_zpowers (e : ↥L)
  constructor
  · intro hK
    have hKL : K ≤ L := hK.1.trans inf_le_left
    have hCL : L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) : Subgroup G) : Set G) ≤ L :=
      inf_le_left
    have hKsub : IsComponentOf (K.subgroupOf L)
        ((L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔
          Subgroup.zpowers ((e : ↥L) : G) : Subgroup G) : Set G)).subgroupOf L) := by
      refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff L.subtype_injective).mp ?_
      rw [Subgroup.map_subgroupOf_eq_of_le hKL, Subgroup.map_subgroupOf_eq_of_le hCL]
      exact hK
    rw [hCinf, hsubEq] at hKsub
    have hKc := (corner_occurs_iff R hr he _).mp hKsub
    rw [← Subgroup.map_subgroupOf_eq_of_le hKL, hKc]
  · intro hK
    rw [hK]
    have hcomp : IsComponentOf (R.component (PlaneRaw.Code.zero (Finset.univ.erase i)))
        (⊤ ⊓ Subgroup.centralizer (Subgroup.zpowers (e : ↥L) : Set ↥L)) :=
      (corner_occurs_iff R hr he _).mpr rfl
    have hmap := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      L.subtype_injective).mpr hcomp
    rw [hmapEq, ← hCinf] at hmap
    exact hmap

private theorem corner_layer [Finite G] {Bs L : Subgroup G} {x : G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    LargeEvenLayer (L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) : Subgroup G) : Set G)) =
      (R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype := by
  have hiff := corner_component_iff R hr he hLx
  have hself : IsComponentOf
      ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype)
      (L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) : Subgroup G) : Set G)) :=
    (hiff _).mpr rfl
  change sSup {K | IsComponentOf K (L ⊓ Subgroup.centralizer
    ((Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) : Subgroup G) : Set G))} =
      (R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype
  exact le_antisymm (sSup_le fun K hK => le_of_eq ((hiff K).mp hK)) (le_sSup hself)

private theorem corner_e_ne_one {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (he : R.coord (Additive.ofMul e) = Pi.single i 1) :
    ((e : ↥L) : G) ≠ 1 := by
  intro h1
  have h2 : (e : ↥(Bs.subgroupOf L)) = 1 := Subtype.ext (Subtype.ext h1)
  have h3 : (Pi.single i (1 : PlaneRaw.F) : PlaneRaw.V r) = 0 := by
    have h4 : R.coord (Additive.ofMul (e : ↥(Bs.subgroupOf L))) = 0 := by
      simpa using congrArg (fun z : ↥(Bs.subgroupOf L) => R.coord (Additive.ofMul z)) h2
    rw [he] at h4
    exact h4
  exact corner_single_ne_zero i h3

private theorem corner_self_centralizer_le {B Bs L : Subgroup G} {x : G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    (hxB : x ∈ B) (heB : ((e : ↥L) : G) ∈ B)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) ≤
      B ⊓ Subgroup.centralizer
        ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype : Set G) := by
  have hxJ : x ∈ Subgroup.centralizer
      ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp
      (hLx (Subgroup.map_subtype_le _ hy)) x (Set.mem_singleton x)).symm
  have heCent : ((e : ↥L)) ∈ Subgroup.centralizer
      (R.component (PlaneRaw.Code.zero (Finset.univ.erase i)) : Set ↥L) := by
    have hmem : R.coord (Additive.ofMul e) ∈ ggLinImage (p := 3) R.coord
        (Subgroup.centralizer
          (R.component (PlaneRaw.Code.zero (Finset.univ.erase i)) : Set ↥L)) := by
      rw [R.cent_eq _ (corner_admissible (r := r) hr i), he]
      exact corner_single_mem_cent (r := r) .symplectic i
    exact (ofMul_mem_ggLinImage R.coord _ e).mp hmem
  have heGJ : ((e : ↥L) : G) ∈ Subgroup.centralizer
      ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨j, hj, rfl⟩
    simpa using congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp heCent j hj)
  refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hxB, hxJ⟩))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨heB, heGJ⟩))

private theorem corner_eq_smul_single {r : ℕ} {i : Fin r} {w : PlaneRaw.V r}
    (h : w ∈ PlaneRaw.cent .symplectic (PlaneRaw.Code.zero (Finset.univ.erase i))) :
    w = (w i) • Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · have h0 : w j = 0 :=
      (PlaneRaw.mem_cent_zero .symplectic (Finset.univ.erase i) w).mp h j
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    rw [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
    exact h0

private theorem corner_pow_of_centralizes {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    {a' : ↥(Bs.subgroupOf L)}
    (ha'cent : (a' : ↥L) ∈ Subgroup.centralizer
      (R.component (PlaneRaw.Code.zero (Finset.univ.erase i)) : Set ↥L)) :
    (a' : ↥L) ∈ Subgroup.zpowers (e : ↥L) := by
  have hcoord : R.coord (Additive.ofMul a') ∈
      PlaneRaw.cent .symplectic (PlaneRaw.Code.zero (Finset.univ.erase i)) := by
    have hmem : R.coord (Additive.ofMul a') ∈ ggLinImage (p := 3) R.coord
        (Subgroup.centralizer
          (R.component (PlaneRaw.Code.zero (Finset.univ.erase i)) : Set ↥L)) :=
      (ofMul_mem_ggLinImage R.coord _ a').mpr ha'cent
    rw [R.cent_eq _ (corner_admissible (r := r) hr i)] at hmem
    exact hmem
  set w : PlaneRaw.V r := R.coord (Additive.ofMul a') with hw
  have hsingle : w = (w i) • Pi.single i 1 := corner_eq_smul_single hcoord
  obtain ⟨l, hl⟩ := ZMod.intCast_surjective (w i)
  have hsingle' : w = l • Pi.single i 1 := by
    rw [hsingle, ← hl, ← Int.cast_smul_eq_zsmul (R := ZMod 3)]
  have hpow : R.coord (Additive.ofMul (e ^ l)) = R.coord (Additive.ofMul a') := by
    rw [ofMul_zpow, map_zsmul, he]
    exact hsingle'.symm
  have heqa : e ^ l = a' := Additive.ofMul.injective (R.coord.injective hpow)
  have h2 : Subgroup.subtype (Bs.subgroupOf L) (e ^ l) = (a' : ↥L) :=
    congrArg (Subgroup.subtype (Bs.subgroupOf L)) heqa
  rw [map_zpow] at h2
  exact Subgroup.mem_zpowers_iff.mpr ⟨l, h2⟩

private theorem corner_self_centralizer_ge {B Bs L : Subgroup G} {x : G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    (hBBs : B ≤ Bs)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    B ⊓ Subgroup.centralizer
        ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype : Set G) ≤
      Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) := by
  intro b hb
  obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
  obtain ⟨a, ha, k, hbk⟩ := hsplit b (hBBs hbB)
  obtain ⟨haBs, haL⟩ := Subgroup.mem_inf.mp ha
  have hxJ : x ∈ Subgroup.centralizer
      ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp
      (hLx (Subgroup.map_subtype_le _ hy)) x (Set.mem_singleton x)).symm
  have haC : a ∈ Subgroup.centralizer
      ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype : Set G) := by
    have haeq : a = b * x ^ (-k) := by rw [hbk]; group
    rw [haeq]
    exact Subgroup.mul_mem _ hbC (Subgroup.zpow_mem _ hxJ (-k))
  set a' : ↥(Bs.subgroupOf L) := ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr haBs⟩ with ha'def
  have ha'cent : (a' : ↥L) ∈ Subgroup.centralizer
      (R.component (PlaneRaw.Code.zero (Finset.univ.erase i)) : Set ↥L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h := Subgroup.mem_centralizer_iff.mp haC (j : G)
      (Subgroup.mem_map_of_mem L.subtype hj)
    exact Subtype.ext (by simpa using h)
  have ha'z := corner_pow_of_centralizes R hr he ha'cent
  have haG : a ∈ Subgroup.zpowers ((e : ↥L) : G) := by
    have hm : (Subgroup.zpowers (e : ↥L)).map L.subtype =
        Subgroup.zpowers ((e : ↥L) : G) := MonoidHom.map_zpowers L.subtype (e : ↥L)
    rw [← hm]
    exact Subgroup.mem_map_of_mem L.subtype ha'z
  rw [hbk]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right haG)
    (Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)) k)

private theorem corner_self_centralizer {B Bs L : Subgroup G} {x : G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    (hBBs : B ≤ Bs) (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hxB : x ∈ B)
    (heB : ((e : ↥L) : G) ∈ B) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) =
      B ⊓ Subgroup.centralizer
        ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype : Set G) :=
  le_antisymm (corner_self_centralizer_le R hr he hxB heB hLx)
    (corner_self_centralizer_ge R hr he hBBs hsplit hLx)

private theorem corner_notSmall {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {i : Fin r} (hr : 4 ≤ r)
    (hbig : ∀ S : Finset (Fin r), 3 ≤ S.card →
      7 ∣ Nat.card (R.component (PlaneRaw.Code.zero S))) :
    ¬ LargeEvenSmall
      ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype) := by
  refine IOneOrthEnd.not_largeEvenSmall_of_seven_dvd ?_
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  refine hbig _ ?_
  have hc : (Finset.univ.erase i).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [hc]
  omega

section Finite

variable [Finite G]

private theorem corner_disjoint {x z : G} (hx : Nat.card (Subgroup.zpowers x) = 3)
    (hz : Nat.card (Subgroup.zpowers z) = 3) (hnot : z ∉ Subgroup.zpowers x) :
    Subgroup.zpowers x ⊓ Subgroup.zpowers z = ⊥ := by
  by_contra hne
  have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers z ≤ Subgroup.zpowers x := inf_le_left
  have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers z : Subgroup G) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hx] at h
  have h3 : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers z : Subgroup G) = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact h3
  have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers z = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hx, h3])
  have hle' : Subgroup.zpowers x ≤ Subgroup.zpowers z := heq ▸ inf_le_right
  have heq2 : Subgroup.zpowers x = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle' (by rw [hz, hx])
  exact hnot (heq2 ▸ Subgroup.mem_zpowers z)

theorem isElemAbelian_zpowers_sup_zpowers_of_inf_eq_bot {B Bs L : Subgroup G} {x : G}
    {e : ↥(Bs.subgroupOf L)} (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hx1 : x ≠ 1) (hxB : x ∈ B) (heG_ne : ((e : ↥L) : G) ≠ 1)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥) :
    IsElemAbelian 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G)) ∧
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G)
        : Subgroup G) = 3 ^ 2 := by
  have hxBs : x ∈ Bs := hBBs hxB
  have heG_mem : ((e : ↥L) : G) ∈ Bs := e.2
  have hxord : orderOf x = 3 :=
    @orderOf_eq_prime G _ x 3 ⟨by norm_num⟩ (hBs.2 x hxBs) hx1
  have heord : orderOf ((e : ↥L) : G) = 3 :=
    @orderOf_eq_prime G _ ((e : ↥L) : G) 3 ⟨by norm_num⟩ (hBs.2 _ heG_mem) heG_ne
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hcarde : Nat.card (Subgroup.zpowers ((e : ↥L) : G)) = 3 := by
    rw [Nat.card_zpowers, heord]
  have hDLE : Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) ≤ Bs :=
    sup_le (Subgroup.zpowers_le.mpr hxBs) (Subgroup.zpowers_le.mpr heG_mem)
  have hnot : ((e : ↥L) : G) ∉ Subgroup.zpowers x := by
    intro hmem
    have hb : ((e : ↥L) : G) ∈ Subgroup.zpowers x ⊓ L :=
      Subgroup.mem_inf.mpr ⟨hmem, (e : ↥L).2⟩
    rw [hxL] at hb
    exact heG_ne (Subgroup.mem_bot.mp hb)
  have hdisj := corner_disjoint (z := ((e : ↥L) : G)) hcardx hcarde hnot
  have hcomm : ∀ a ∈ Subgroup.zpowers x,
      ∀ c ∈ Subgroup.zpowers ((e : ↥L) : G), a * c = c * a := by
    intro a ha c hc
    exact congrArg Subtype.val (hBs.1.is_comm.comm
      ⟨a, Subgroup.zpowers_le.mpr hxBs ha⟩ ⟨c, Subgroup.zpowers_le.mpr heG_mem hc⟩)
  have hcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G)
      : Subgroup G) = 3 ^ 2 := by
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers x) (Subgroup.zpowers ((e : ↥L) : G)) hcomm).1
    rw [hdisj, Subgroup.card_bot, mul_one, hcardx, hcarde] at h1
    rw [h1]
    norm_num
  exact ⟨CFSG.Open.IsElemAbelian.mono hBs hDLE, hcard⟩

private theorem corner_stdSubPre {B Bs L : Subgroup G} {x : G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (hr : 4 ≤ r)
    (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs) (hx1 : x ≠ 1) (hxB : x ∈ B)
    (heB : ((e : ↥L) : G) ∈ B) (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    LargeEvenStdSubPre 3 B x L
      (Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G))
      ((R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype) := by
  obtain ⟨helem, hcard⟩ :=
    isElemAbelian_zpowers_sup_zpowers_of_inf_eq_bot hBBs hBs hx1 hxB (corner_e_ne_one R he) hxL
  have hDleB : Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G) ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr heB)
  exact ⟨hDleB, helem, hcard, Subgroup.mem_sup_left (Subgroup.mem_zpowers x),
    (corner_layer R hr he hLx).symm, (corner_component_iff R hr he hLx _).mpr rfl,
    corner_self_centralizer R hr he hBBs hsplit hLx hxB heB⟩

theorem GGConfig.not_largeEvenSmall_of_corner_single {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) {r : ℕ} (hr : 4 ≤ r)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (hbig : ∀ S : Finset (Fin r), 3 ≤ S.card → 7 ∣ Nat.card (R.component (.zero S)))
    {e : ↥(Bs.subgroupOf L)} {i : Fin r} (he : R.coord (Additive.ofMul e) = Pi.single i 1)
    (heB : ((e : ↥L) : G) ∈ B) : ¬ LargeEvenSmall J := by
  have hThm : GGThmIHyp 3 B x L := hC.1
  have hBstar : GGBstar 3 B Bs := hC.2.1
  have hStd : LargeEvenStdSub 3 B x L D J := hC.2.2
  obtain ⟨-, hxB, hx1, hLcomp, -⟩ := hThm.2.2.2.2.2.2.1
  obtain ⟨hBBs, hBs, -, -⟩ := hBstar
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hLcomp.1
  refine hStd.2 ⟨rfl, Subgroup.zpowers x ⊔ Subgroup.zpowers ((e : ↥L) : G),
    (R.component (PlaneRaw.Code.zero (Finset.univ.erase i))).map L.subtype, ?_, ?_⟩
  · exact corner_stdSubPre R hr he hBBs hBs hx1 hxB heB hxL hsplit hLx
  · exact corner_notSmall R hr hbig

end Finite

end CFSG.StandardType

end
