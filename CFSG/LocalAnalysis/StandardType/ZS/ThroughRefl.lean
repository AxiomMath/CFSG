module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
public import CFSG.LocalAnalysis.StandardType.ZS.MovedGroup

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem subtype_restrictHom_apply {X : Subgroup (U ≃ₗ[ZMod p] U)} (e : X)
    (w : HardMathSupport.Kantor79.commutatorSpace X) :
    (HardMathSupport.Kantor79.commutatorSpace X).subtype
      (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) e w) =
      (e : U ≃ₗ[ZMod p] U) (w : U) :=
  restrictHom_apply X (HardMathSupport.Kantor79.commutatorSpace X)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) e w

theorem restrictHom_injective_of_splitSupport {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) :
    Function.Injective (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hker : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : φ x = 1 := (MonoidHom.mem_ker).mp hx
    apply Subtype.ext
    ext u
    have hu : u ∈ V ⊔ C := by rw [hX.1.sup_eq_top]; trivial
    obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    have hv' : (x : U ≃ₗ[ZMod p] U) v = v := by
      have hc' := congrArg (fun e : V ≃ₗ[ZMod p] V => (e ⟨v, hv⟩ : U)) h1
      simpa [φ, restrictHom_apply] using hc'
    have hc' : (x : U ≃ₗ[ZMod p] U) c = c := (mem_centralizerSpace.mp hc) x x.2
    rw [hv', hc']
    simp
  exact (MonoidHom.ker_eq_bot_iff φ).mp hker

theorem irred_movedGroup_of_splitSupport {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) : ∀ W : Submodule (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace X),
    (∀ g ∈ movedGroup X, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  let X' : Submodule (ZMod p) U := W.map V.subtype
  have hXinv : ∀ h ∈ X, ∀ x ∈ X', h x ∈ X' := by
    intro h hh x hx
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨φ ⟨h, hh⟩ w,
      hW (φ ⟨h, hh⟩) (MonoidHom.mem_range.mpr ⟨⟨h, hh⟩, rfl⟩) w hw, ?_⟩
    exact subtype_restrictHom_apply (X := X) ⟨h, hh⟩ w
  have hX'le : X' ≤ V := by
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  rcases hX.2.2 X' bot_le hX'le hXinv with hX' | hX'
  · left
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    have : (w : U) ∈ X' := ⟨w, hw, rfl⟩
    rw [hX'] at this
    simpa using this
  · right
    refine le_antisymm le_top ?_
    intro w _
    have : (w : U) ∈ X' := by rw [hX']; exact w.2
    obtain ⟨w', hw', hEq⟩ := this
    have hw'' : w' = w := Subtype.ext hEq
    rwa [hw''] at hw'

theorem exists_isRefl_pair_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l)
    (hd : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X, IsRefl p x ∧ IsRefl p y ∧
      3 < orderOf (x * y) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hX
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
  have hxne : φ ⟨x, hx⟩ ≠ 1 := by
    intro h
    have h1 : φ ⟨x, hx⟩ = φ (1 : X) := by rw [h, map_one]
    exact IsRefl.ne_one hxr (Subtype.ext_iff.mp (hinj h1))
  have hyne : φ ⟨y, hy⟩ ≠ 1 := by
    intro h
    have h1 : φ ⟨y, hy⟩ = φ (1 : X) := by rw [h, map_one]
    exact IsRefl.ne_one hyr (Subtype.ext_iff.mp (hinj h1))
  have hxR : IsRefl p (φ ⟨x, hx⟩) := by
    rcases isRefl_restrictHom_or_eq_one (X := X) (t := ⟨x, hx⟩) hxr with h | h
    · exact h
    · exact absurd h hxne
  have hyR : IsRefl p (φ ⟨y, hy⟩) := by
    rcases isRefl_restrictHom_or_eq_one (X := X) (t := ⟨y, hy⟩) hyr with h | h
    · exact h
    · exact absurd h hyne
  have horder : orderOf (φ ⟨x, hx⟩ * φ ⟨y, hy⟩) = orderOf (x * y) := by
    rw [← map_mul, orderOf_injective φ hinj]
    exact (orderOf_injective X.subtype X.subtype_injective (⟨x, hx⟩ * ⟨y, hy⟩)).symm
  exact ⟨φ ⟨x, hx⟩, MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩,
    φ ⟨y, hy⟩, MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩, hxR, hyR,
    by rw [horder]; exact hxy⟩

@[expose] def movedPullback (X : Subgroup (U ≃ₗ[ZMod p] U))
    (B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)) : Subgroup (U ≃ₗ[ZMod p] U) :=
  (B.comap (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv))).map X.subtype

theorem movedPullback_le (X : Subgroup (U ≃ₗ[ZMod p] U))
    (B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)) :
    movedPullback X B ≤ X := by
  rintro g ⟨h, _, rfl⟩
  exact h.2

theorem mem_movedPullback {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)} {g : U ≃ₗ[ZMod p] U} :
    g ∈ movedPullback X B ↔ ∃ hg : g ∈ X,
      restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨g, hg⟩ ∈ B := by
  constructor
  · rintro ⟨h, hhB, hhg⟩
    have hg : g ∈ X := hhg ▸ h.2
    refine ⟨hg, ?_⟩
    have he : (⟨g, hg⟩ : X) = h := Subtype.ext hhg.symm
    rw [he]
    exact hhB
  · rintro ⟨hg, hhB⟩
    exact ⟨⟨g, hg⟩, hhB, rfl⟩

theorem movedSpace_eq_map_of_splitSupport {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) (x : X) :
    HardMathSupport.Kantor79.movedSpace (x : U ≃ₗ[ZMod p] U) =
      (HardMathSupport.Kantor79.movedSpace
        (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
          (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x)).map
        (HardMathSupport.Kantor79.commutatorSpace X).subtype := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  change LinearMap.range ((x : U →ₗ[ZMod p] U) - 1) =
    (LinearMap.range (((φ x : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) - 1)).map V.subtype
  apply le_antisymm
  · rintro y ⟨u, rfl⟩
    obtain ⟨v, hv, c, hc, hvc⟩ := Submodule.mem_sup.mp
      (show u ∈ V ⊔ C by rw [hX.1.sup_eq_top]; trivial)
    subst hvc
    have hxc : (x : U ≃ₗ[ZMod p] U) c = c := (mem_centralizerSpace.mp hc) x x.2
    refine Submodule.mem_map.mpr ⟨(φ x) ⟨v, hv⟩ - ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, ?_⟩
    rw [map_sub, subtype_restrictHom_apply x ⟨v, hv⟩]
    simp [hxc]
  · rintro y ⟨w, hw, rfl⟩
    obtain ⟨v, hv⟩ := hw
    rw [← hv]
    exact ⟨(v : U), by
      simp only [LinearMap.sub_apply, map_sub]
      rfl⟩

theorem isRefl_of_isRefl_restrictHom {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) {x : X}
    (h : IsRefl p (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x)) :
    IsRefl p (x : U ≃ₗ[ZMod p] U) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  change IsRefl p (φ x) at h
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hX
  have hxx : x * x = 1 := hinj (by rw [map_mul, h.1, map_one])
  have hfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.movedSpace (x : U ≃ₗ[ZMod p] U)) = 1 := by
    rw [movedSpace_eq_map_of_splitSupport hX x, Submodule.finrank_map_subtype_eq]
    exact h.2
  exact ⟨by simpa using congrArg (Subtype.val) hxx, hfin⟩

theorem isRefl_restrictHom_of_isRefl {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) {x : X} (h : IsRefl p (x : U ≃ₗ[ZMod p] U)) :
    IsRefl p (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x) := by
  let φ := restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
    (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  change IsRefl p (φ x)
  have hxx : x * x = 1 := Subtype.ext (by simpa using h.1)
  have hfin : Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.movedSpace (x : U ≃ₗ[ZMod p] U)) = 1 := h.2
  rw [movedSpace_eq_map_of_splitSupport hX x, Submodule.finrank_map_subtype_eq] at hfin
  exact ⟨by rw [← map_mul φ, hxx, map_one], hfin⟩

theorem commutatorSpace_movedPullback {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l)
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)}
    (hB : B ≤ movedGroup X) :
    HardMathSupport.Kantor79.commutatorSpace (movedPullback X B) =
      (HardMathSupport.Kantor79.commutatorSpace B).map
        (HardMathSupport.Kantor79.commutatorSpace X).subtype := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  change HardMathSupport.Kantor79.commutatorSpace (movedPullback X B) =
    (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype
  apply le_antisymm
  · rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro w ⟨g, hg, u, rfl⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
    have heB : φ e ∈ B := Subgroup.mem_comap.mp he
    obtain ⟨v, hv, c, hc, hvc⟩ := Submodule.mem_sup.mp
      (show u ∈ V ⊔ C by rw [hX.1.sup_eq_top]; trivial)
    subst hvc
    have hxc : (e : U ≃ₗ[ZMod p] U) c = c := (mem_centralizerSpace.mp hc) e e.2
    refine Submodule.mem_map.mpr ⟨(φ e) ⟨v, hv⟩ - ⟨v, hv⟩,
      Submodule.subset_span ⟨φ e, heB, ⟨⟨v, hv⟩, rfl⟩⟩, ?_⟩
    have hxc' : (X.subtype e : U ≃ₗ[ZMod p] U) c = c := hxc
    simp only [map_add, hxc', map_sub]
    abel
  · rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, hb, v, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp (hB hb)
    have heP : (X.subtype e : U ≃ₗ[ZMod p] U) ∈ movedPullback X B :=
      (mem_movedPullback (B := B)).mpr ⟨e.2, he ▸ hb⟩
    have hbe : V.subtype (b v - v) =
        (X.subtype e : U ≃ₗ[ZMod p] U) (v : U) - (v : U) := by
      rw [map_sub, show b v = (φ e) v from by rw [he], subtype_restrictHom_apply]
      rfl
    rw [hbe]
    exact Submodule.subset_span ⟨X.subtype e, heP, (v : U), rfl⟩

theorem reflGen_movedPullback {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l)
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)}
    (hB : B ≤ movedGroup X) (hBr : ReflGen p B) :
    ReflGen p (movedPullback X B) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  let P := movedPullback X B
  let Q : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure {t | t ∈ P ∧ IsRefl p t}
  have hQle : Q ≤ P := by
    change Subgroup.closure {t | t ∈ P ∧ IsRefl p t} ≤ P
    rw [Subgroup.closure_le]
    rintro t ⟨ht, _⟩
    exact ht
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hX
  have hmap_le : (Q.comap X.subtype).map φ ≤ B := by
    rintro b ⟨e, he, rfl⟩
    obtain ⟨hg, hφ⟩ := (mem_movedPullback (B := B)).mp (hQle (Subgroup.mem_comap.mp he))
    have he' : (⟨X.subtype e, hg⟩ : X) = e := Subtype.ext rfl
    rwa [he'] at hφ
  have hB_le_map : B ≤ (Q.comap X.subtype).map φ := by
    rw [hBr, Subgroup.closure_le]
    rintro b ⟨hb, hbr⟩
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp (hB hb)
    have heB : φ e ∈ B := by rwa [he]
    have heP : (X.subtype e : U ≃ₗ[ZMod p] U) ∈ P :=
      (mem_movedPullback (B := B)).mpr ⟨e.2, heB⟩
    have hrefl : IsRefl p (X.subtype e : U ≃ₗ[ZMod p] U) :=
      isRefl_of_isRefl_restrictHom hX (x := e) (by rw [he]; exact hbr)
    exact ⟨e, Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨heP, hrefl⟩), he⟩
  have hPle : P ≤ Q := by
    intro g hg
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
    have heB : φ e ∈ B := Subgroup.mem_comap.mp he
    obtain ⟨q, hq, hqφ⟩ := Subgroup.mem_map.mp (hB_le_map heB)
    have hqe : q = e := hinj hqφ
    have hqQ : X.subtype q ∈ Q := Subgroup.mem_comap.mp hq
    rwa [hqe] at hqQ
  exact le_antisymm hPle hQle

private theorem centralizerSpace_map_le_movedPullback {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)} :
    (centralizerSpace B).map (HardMathSupport.Kantor79.commutatorSpace X).subtype ≤
      centralizerSpace (movedPullback X B) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  intro w hw
  obtain ⟨c, hc, rfl⟩ := hw
  rw [mem_centralizerSpace]
  intro g hg
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hg
  have heB : φ e ∈ B := Subgroup.mem_comap.mp he
  have hc' : (φ e) c = c := (mem_centralizerSpace.mp hc) (φ e) heB
  calc
    (X.subtype e : U ≃ₗ[ZMod p] U) (V.subtype c)
        = V.subtype ((φ e) c) := (subtype_restrictHom_apply (X := X) e c).symm
    _ = V.subtype c := congrArg V.subtype hc'

private theorem centralizerSpace_le_movedPullback {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)} :
    centralizerSpace X ≤ centralizerSpace (movedPullback X B) := by
  intro c hc
  rw [mem_centralizerSpace] at hc ⊢
  intro g hg
  exact hc g (movedPullback_le X B hg)

private theorem commutatorSpace_inf_centralizerSpace_movedPullback
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l k : ℕ}
    (hX : SplitSupport X l)
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)}
    (hB : B ≤ movedGroup X) (hBs : SplitSupport B k) :
    HardMathSupport.Kantor79.commutatorSpace (movedPullback X B) ⊓
      centralizerSpace (movedPullback X B) = ⊥ := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  let P := movedPullback X B
  have hV : HardMathSupport.Kantor79.commutatorSpace P =
      (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype :=
    commutatorSpace_movedPullback hX hB
  refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
  rw [hV] at hw
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hw.1
  have hbC : b ∈ centralizerSpace B := by
    rw [mem_centralizerSpace]
    intro b' hb'
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp (hB hb')
    have heP : (X.subtype e : U ≃ₗ[ZMod p] U) ∈ P :=
      (mem_movedPullback (B := B)).mpr ⟨e.2, he ▸ hb'⟩
    have hfix := (mem_centralizerSpace.mp hw.2) (X.subtype e) heP
    have h1 : V.subtype ((φ e) b) = V.subtype b := by
      rw [subtype_restrictHom_apply (X := X) e b]
      exact hfix
    have h2 : (φ e) b = b := Subtype.ext h1
    rwa [he] at h2
  have hb0 : b = 0 := by
    have hmem : b ∈ HardMathSupport.Kantor79.commutatorSpace B ⊓ centralizerSpace B :=
      ⟨hb, hbC⟩
    rw [hBs.1.inf_eq_bot] at hmem
    simpa using hmem
  rw [hb0, map_zero]

private theorem commutatorSpace_sup_centralizerSpace_movedPullback
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l k : ℕ}
    (hX : SplitSupport X l)
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)}
    (hB : B ≤ movedGroup X) (hBs : SplitSupport B k) :
    HardMathSupport.Kantor79.commutatorSpace (movedPullback X B) ⊔
      centralizerSpace (movedPullback X B) = ⊤ := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let C := centralizerSpace X
  let P := movedPullback X B
  have hV : HardMathSupport.Kantor79.commutatorSpace P =
      (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype :=
    commutatorSpace_movedPullback hX hB
  have hCmap : (centralizerSpace B).map V.subtype ≤ centralizerSpace P :=
    centralizerSpace_map_le_movedPullback
  have hCX : centralizerSpace X ≤ centralizerSpace P :=
    centralizerSpace_le_movedPullback
  rw [eq_top_iff]
  intro u _
  have hu : u ∈ V ⊔ C := by rw [hX.1.sup_eq_top]; trivial
  obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
  have hv' : v ∈ (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype ⊔
      (centralizerSpace B).map V.subtype := by
    rw [← Submodule.map_sup, hBs.1.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
    exact hv
  have hvP : v ∈ HardMathSupport.Kantor79.commutatorSpace P ⊔ centralizerSpace P := by
    refine (sup_le_sup_left hCmap _) ?_
    rw [hV]
    exact hv'
  exact add_mem hvP (Submodule.mem_sup_right (hCX hc))

private theorem irredOnSection_movedPullback
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l k : ℕ}
    (hX : SplitSupport X l)
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)}
    (hB : B ≤ movedGroup X) (hBs : SplitSupport B k) :
    IrredOnSection (movedPullback X B) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (movedPullback X B)) := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let P := movedPullback X B
  have hV := commutatorSpace_movedPullback hX hB
  intro Y _ hYle hYinv; let Y' : Submodule (ZMod p) V := Y.comap V.subtype
  have hY'le : Y' ≤ HardMathSupport.Kantor79.commutatorSpace B := by
    intro v hv
    have hle : (v : U) ∈ (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype := by
      rw [← hV]; exact hYle (show (v : U) ∈ Y from hv)
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hle
    have hwv' : w = v := Subtype.ext hwv
    rwa [hwv'] at hw
  have hY'inv : ∀ b ∈ B, ∀ y ∈ Y', b y ∈ Y' := by
    intro b hb y hy; obtain ⟨e, he⟩ := MonoidHom.mem_range.mp (hB hb)
    have heP : (X.subtype e : U ≃ₗ[ZMod p] U) ∈ P :=
      (mem_movedPullback (B := B)).mpr ⟨e.2, he ▸ hb⟩
    have hmem : (X.subtype e : U ≃ₗ[ZMod p] U) (V.subtype y) ∈ Y :=
      hYinv _ heP _ (Submodule.mem_comap.mp hy)
    have h1 : V.subtype (b y) = (X.subtype e : U ≃ₗ[ZMod p] U) (V.subtype y) := by
      rw [← he]; exact subtype_restrictHom_apply (X := X) e y
    show V.subtype (b y) ∈ Y; rw [h1]; exact hmem
  rcases hBs.2.2 Y' bot_le hY'le hY'inv with hY' | hY'
  · left; refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
    have hyV : y ∈ (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype := by
      rw [← hV]; exact hYle hy
    obtain ⟨v, hv, hv_eq⟩ := Submodule.mem_map.mp hyV
    have hy' : V.subtype v ∈ Y := by rw [hv_eq]; exact hy
    have hvY' : v ∈ Y' := Submodule.mem_comap.mpr hy'
    rw [hY'] at hvY'
    have hv0 : v = 0 := by simpa using hvY'
    rw [← hv_eq, hv0, map_zero]
  · right; refine le_antisymm hYle ?_
    intro y hy; have hyV : y ∈ (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype := by
      rw [← hV]; exact hy
    obtain ⟨v, hv, hv_eq⟩ := Submodule.mem_map.mp hyV
    have hvY' : v ∈ Y' := by rw [hY']; exact hv
    have hmem : V.subtype v ∈ Y := Submodule.mem_comap.mp hvY'
    rwa [hv_eq] at hmem


theorem splitSupport_movedPullback {X : Subgroup (U ≃ₗ[ZMod p] U)} {l k : ℕ}
    (hX : SplitSupport X l)
    {B : Subgroup (HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)}
    (hB : B ≤ movedGroup X) (hBs : SplitSupport B k) :
    SplitSupport (movedPullback X B) k := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let P := movedPullback X B
  have hV : HardMathSupport.Kantor79.commutatorSpace P =
      (HardMathSupport.Kantor79.commutatorSpace B).map V.subtype :=
    commutatorSpace_movedPullback hX hB
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace P) = k := by
    rw [hV, Submodule.finrank_map_subtype_eq, hBs.2.1]
  exact ⟨IsCompl.of_eq
      (commutatorSpace_inf_centralizerSpace_movedPullback hX hB hBs)
      (commutatorSpace_sup_centralizerSpace_movedPullback hX hB hBs),
    hfin, irredOnSection_movedPullback hX hB hBs⟩


theorem exists_splitSupport_pred_of_isRefl [Module.Finite (ZMod p) U] {m : ℕ}
    (hthr : TFThroughRefl p m) {H : Subgroup (U ≃ₗ[ZMod p] U)} (hH : IsRGroup p H)
    (hHs : SplitSupport H m)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {r : U ≃ₗ[ZMod p] U} (hr : r ∈ H) (hrr : IsRefl p r) :
    ∃ H₁ : Subgroup (U ≃ₗ[ZMod p] U), H₁ ≤ H ∧ r ∈ H₁ ∧ ReflGen p H₁ ∧
      SplitSupport H₁ (m - 1) := by
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hHs
  have hφr : IsRefl p (φ ⟨r, hr⟩) := by
    rcases isRefl_restrictHom_or_eq_one (X := H) (t := ⟨r, hr⟩) hrr with h | h
    · exact h
    · exfalso
      apply IsRefl.ne_one hrr
      exact Subtype.ext_iff.mp (hinj (h.trans (map_one φ).symm))
  obtain ⟨B, hBJ, hφrB, hBr, hBs⟩ :=
    hthr V (movedGroup H) hHs.2.1 (reflGen_movedGroup hH.1)
      (transvectionFree_movedGroup hHs hH.2)
      (irred_movedGroup_of_splitSupport hHs)
      (exists_isRefl_pair_movedGroup hHs hd) (φ ⟨r, hr⟩)
      (MonoidHom.mem_range.mpr ⟨⟨r, hr⟩, rfl⟩) hφr
  exact ⟨movedPullback H B, movedPullback_le H B,
    (mem_movedPullback (B := B)).mpr ⟨hr, hφrB⟩,
    reflGen_movedPullback hHs hBJ hBr, splitSupport_movedPullback hHs hBJ hBs⟩

end CFSG.StandardType.ZS

end
