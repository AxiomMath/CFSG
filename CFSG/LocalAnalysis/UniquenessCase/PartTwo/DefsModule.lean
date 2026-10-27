module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G]

@[expose] def intSub (V : Subgroup G) (hV : IsElemAbelian 2 V) (U : Subgroup G) :
    Subgroup (IntMod V hV) :=
  U.subgroupOf V

theorem mem_intSub (V : Subgroup G) (hV : IsElemAbelian 2 V) (U : Subgroup G) (x : IntMod V hV) :
    x ∈ intSub V hV U ↔ x.val ∈ U := Iff.rfl

@[expose] def modNull (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Subgroup (IntMod V hV) :=
  intSub V hV V₀

abbrev Vtil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Type :=
  IntMod V hV ⧸ modNull V₀ V hV

@[expose] def mkTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : IntMod V hV →* Vtil V₀ V hV :=
  QuotientGroup.mk' (modNull V₀ V hV)

theorem mem_modNull (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (x : IntMod V hV) :
    x ∈ modNull V₀ V hV ↔ x.val ∈ V₀ := Iff.rfl

theorem mkTil_surjective (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Function.Surjective (mkTil V₀ V hV) := QuotientGroup.mk'_surjective _

theorem mkTil_eq_iff (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (x y : IntMod V hV) :
    mkTil V₀ V hV x = mkTil V₀ V hV y ↔ x.val * (y.val)⁻¹ ∈ V₀ := by
  show (x : Vtil V₀ V hV) = (y : Vtil V₀ V hV) ↔ _
  rw [QuotientGroup.eq_iff_div_mem, mem_modNull, div_eq_mul_inv, IntMod.val_mul, IntMod.val_inv]

@[expose] def stabTil (V₀ V : Subgroup G) : Subgroup G :=
  normalizer (V : Set G) ⊓ normalizer (V₀ : Set G)

theorem stabTil_le_normalizer (V₀ V : Subgroup G) : stabTil V₀ V ≤ normalizer (V : Set G) :=
  inf_le_left

theorem stabTil_le_normalizer₀ (V₀ V : Subgroup G) : stabTil V₀ V ≤ normalizer (V₀ : Set G) :=
  inf_le_right

theorem le_stabTil {M : Subgroup G} {V₀ V : Subgroup G} (hM : M ≤ normalizer (V : Set G))
    (hM₀ : M ≤ normalizer (V₀ : Set G)) : M ≤ stabTil V₀ V :=
  le_inf hM hM₀

@[expose] noncomputable def actStab (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    ↥(stabTil V₀ V) →* MulAut (IntMod V hV) :=
  (convI hV).comp (Subgroup.inclusion (stabTil_le_normalizer V₀ V))

theorem actStab_apply_val (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : stabTil V₀ V)
    (v : IntMod V hV) : (actStab V₀ V hV g v).val = (g : G) * v.val * (g : G)⁻¹ :=
  convI_apply_val hV _ v

theorem map_modNull (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : stabTil V₀ V) :
    (modNull V₀ V hV).map ((actStab V₀ V hV g : MulAut (IntMod V hV)) :
      IntMod V hV →* IntMod V hV) = modNull V₀ V hV := by
  ext x
  rw [Subgroup.mem_map]
  have hg : (g : G) ∈ normalizer (V : Set G) := stabTil_le_normalizer V₀ V g.2
  have hg0 : (g : G) ∈ normalizer (V₀ : Set G) := stabTil_le_normalizer₀ V₀ V g.2
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_modNull] at hy ⊢
    show (actStab V₀ V hV g y).val ∈ V₀
    rw [actStab_apply_val]
    exact (Subgroup.mem_normalizer_iff.1 hg0 _).1 hy
  · intro hx
    rw [mem_modNull] at hx
    have hxinv : (g : G)⁻¹ * x.val * (g : G) ∈ V :=
      (Subgroup.mem_normalizer_iff''.1 hg x.val).1 x.val_mem
    refine ⟨IntMod.mk hV ⟨(g : G)⁻¹ * x.val * (g : G), hxinv⟩, ?_, ?_⟩
    · rw [mem_modNull]
      exact (Subgroup.mem_normalizer_iff''.1 hg0 x.val).1 hx
    · refine IntMod.val_injective ?_
      show (actStab V₀ V hV g (IntMod.mk hV ⟨(g : G)⁻¹ * x.val * (g : G), hxinv⟩)).val = x.val
      rw [actStab_apply_val]
      show (g : G) * ((g : G)⁻¹ * x.val * (g : G)) * (g : G)⁻¹ = x.val
      group

@[expose] noncomputable def actTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    ↥(stabTil V₀ V) →* MulAut (Vtil V₀ V hV) where
  toFun g := QuotientGroup.congr (modNull V₀ V hV) (modNull V₀ V hV) (actStab V₀ V hV g)
    (map_modNull V₀ V hV g)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.congr_mk]
      rw [map_one, MulAut.one_apply]
      rfl
  map_mul' g h := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply]
      simp only [QuotientGroup.congr_mk]
      rw [map_mul, MulAut.mul_apply]

theorem actTil_mk (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : stabTil V₀ V)
    (x : IntMod V hV) :
    actTil V₀ V hV g (mkTil V₀ V hV x) = mkTil V₀ V hV (actStab V₀ V hV g x) :=
  QuotientGroup.congr_mk _ _ _ (map_modNull V₀ V hV g) x

theorem actTil_eq_one_iff (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : stabTil V₀ V) :
    actTil V₀ V hV g = 1 ↔ ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ V₀ := by
  constructor
  · intro h v hv
    have h1 := congrArg (fun φ : MulAut (Vtil V₀ V hV) => φ (mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩))) h
    simp only [MulAut.one_apply] at h1
    rw [actTil_mk, mkTil_eq_iff] at h1
    rw [actStab_apply_val] at h1
    exact h1
  · intro h
    refine MulEquiv.ext fun q => ?_
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    rw [actTil_mk, MulAut.one_apply, mkTil_eq_iff, actStab_apply_val]
    exact h x.val x.val_mem

@[expose] noncomputable def barSub (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (X : Subgroup G) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  (X.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)

noncomputable abbrev Mbar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  barSub V₀ V hV M

theorem mem_barSub (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (X : Subgroup G)
    (φ : MulAut (Vtil V₀ V hV)) :
    φ ∈ barSub V₀ V hV X ↔ ∃ g : stabTil V₀ V, (g : G) ∈ X ∧ actTil V₀ V hV g = φ := by
  unfold barSub
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem actTil_mem_barSub (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {X : Subgroup G} {g : G}
    (hg : g ∈ X) (hgs : g ∈ stabTil V₀ V) : actTil V₀ V hV ⟨g, hgs⟩ ∈ barSub V₀ V hV X :=
  (mem_barSub V₀ V hV X _).2 ⟨⟨g, hgs⟩, hg, rfl⟩

theorem barSub_mono (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {X Y : Subgroup G} (h : X ≤ Y) :
    barSub V₀ V hV X ≤ barSub V₀ V hV Y := by
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV X φ).1 hφ
  exact (mem_barSub V₀ V hV Y _).2 ⟨g, h hg, rfl⟩

theorem barSub_bot (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    barSub V₀ V hV ⊥ = ⊥ := by
  refine le_bot_iff.1 fun φ hφ => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV ⊥ φ).1 hφ
  have : g = 1 := Subtype.ext (Subgroup.mem_bot.1 hg)
  rw [this, map_one]
  exact Subgroup.one_mem _

@[expose] def valHom (V : Subgroup G) (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def preTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil V₀ V hV)) : Subgroup G :=
  (S.comap (mkTil V₀ V hV)).map (valHom V hV)

theorem mem_preTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (S : Subgroup (Vtil V₀ V hV))
    {g : G} :
    g ∈ preTil V₀ V hV S ↔ ∃ x : IntMod V hV, x.val = g ∧ mkTil V₀ V hV x ∈ S := by
  unfold preTil
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩
  · rintro ⟨x, rfl, hx⟩
    exact ⟨x, hx, rfl⟩

theorem mem_preTil_iff_of_mem (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil V₀ V hV)) {g : G} (hg : g ∈ V) :
    g ∈ preTil V₀ V hV S ↔ mkTil V₀ V hV (IntMod.mk hV ⟨g, hg⟩) ∈ S := by
  rw [mem_preTil]
  constructor
  · rintro ⟨x, hx, hxS⟩
    have : x = IntMod.mk hV ⟨g, hg⟩ := IntMod.val_injective hx
    rwa [this] at hxS
  · intro h
    exact ⟨_, rfl, h⟩

theorem preTil_le (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (S : Subgroup (Vtil V₀ V hV)) :
    preTil V₀ V hV S ≤ V := by
  intro g hg
  obtain ⟨x, rfl, -⟩ := (mem_preTil V₀ V hV S).1 hg
  exact x.val_mem

theorem preTil_top (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    preTil V₀ V hV ⊤ = V :=
  le_antisymm (preTil_le V₀ V hV _) fun _ hg => (mem_preTil_iff_of_mem V₀ V hV _ hg).2 trivial

theorem preTil_bot (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    preTil V₀ V hV ⊥ = V ⊓ V₀ := by
  ext g
  rw [mem_preTil, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, rfl, hx⟩
    refine ⟨x.val_mem, ?_⟩
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).1 (Subgroup.mem_bot.1 hx)
  · rintro ⟨hgV, hg0⟩
    exact ⟨IntMod.mk hV ⟨g, hgV⟩, rfl,
      Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2 hg0)⟩

@[expose] def imgTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (U : Subgroup G) :
    Subgroup (Vtil V₀ V hV) :=
  (intSub V hV U).map (mkTil V₀ V hV)

theorem mem_imgTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (U : Subgroup G)
    (q : Vtil V₀ V hV) :
    q ∈ imgTil V₀ V hV U ↔ ∃ x : IntMod V hV, x.val ∈ U ∧ mkTil V₀ V hV x = q := by
  unfold imgTil
  simp only [Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩⟩

theorem imgTil_preTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (S : Subgroup (Vtil V₀ V hV)) :
    imgTil V₀ V hV (preTil V₀ V hV S) = S := by
  ext q
  rw [mem_imgTil]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 hx
    rwa [IntMod.val_injective hy] at hyS
  · intro hq
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    exact ⟨x, (mem_preTil V₀ V hV S).2 ⟨x, rfl, hq⟩, rfl⟩

theorem le_preTil_imgTil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (U : Subgroup G) :
    U ⊓ V ≤ preTil V₀ V hV (imgTil V₀ V hV U) := by
  rintro g ⟨hgU, hgV⟩
  rw [mem_preTil_iff_of_mem V₀ V hV _ hgV, mem_imgTil]
  exact ⟨IntMod.mk hV ⟨g, hgV⟩, hgU, rfl⟩

@[expose] noncomputable def preBarSub (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Xbar : Subgroup (MulAut (Vtil V₀ V hV))) : Subgroup G :=
  M ⊓ (Xbar.comap (actTil V₀ V hV)).map (stabTil V₀ V).subtype

theorem mem_preBarSub (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Xbar : Subgroup (MulAut (Vtil V₀ V hV))) {g : G} :
    g ∈ preBarSub M V₀ V hV Xbar ↔
      g ∈ M ∧ ∃ h : g ∈ stabTil V₀ V, actTil V₀ V hV ⟨g, h⟩ ∈ Xbar := by
  unfold preBarSub
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨hgM, ⟨x, hx, rfl⟩⟩
    exact ⟨hgM, x.2, hx⟩
  · rintro ⟨hgM, h, hx⟩
    exact ⟨hgM, ⟨⟨g, h⟩, hx, rfl⟩⟩

theorem barSub_preBarSub (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (Xbar : Subgroup (MulAut (Vtil V₀ V hV))) :
    barSub V₀ V hV (preBarSub M V₀ V hV Xbar) = Xbar ⊓ Mbar M V₀ V hV := by
  ext φ
  rw [Subgroup.mem_inf, mem_barSub, mem_barSub]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgM, h, hx⟩ := (mem_preBarSub M V₀ V hV Xbar).1 hg
    exact ⟨hx, g, hgM, rfl⟩
  · rintro ⟨hφ, g, hgM, rfl⟩
    exact ⟨g, (mem_preBarSub M V₀ V hV Xbar).2 ⟨hgM, g.2, hφ⟩, rfl⟩

theorem le_preBarSub_barSub {M V₀ V X : Subgroup G} (hV : IsElemAbelian 2 V) (hXM : X ≤ M)
    (hX : X ≤ stabTil V₀ V) : X ≤ preBarSub M V₀ V hV (barSub V₀ V hV X) := by
  intro g hg
  exact (mem_preBarSub M V₀ V hV _).2 ⟨hXM hg, hX hg, actTil_mem_barSub V₀ V hV hg (hX hg)⟩

theorem mem_cTilde_iff {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) {g : G} :
    g ∈ F11.CTilde M V₀ V ↔ g ∈ M ∧ ∃ h : g ∈ stabTil V₀ V, actTil V₀ V hV ⟨g, h⟩ = 1 := by
  unfold F11.CTilde
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h
    obtain ⟨hgM, hgN₀, -⟩ := h 1 V.one_mem
    have hgs : g ∈ stabTil V₀ V := ⟨hM hgM, hgN₀⟩
    refine ⟨hgM, hgs, (actTil_eq_one_iff V₀ V hV ⟨g, hgs⟩).2 fun v hv => ?_⟩
    exact (h v hv).2.2
  · rintro ⟨hgM, hgs, h1⟩ v hv
    exact ⟨hgM, hgs.2, (actTil_eq_one_iff V₀ V hV ⟨g, hgs⟩).1 h1 v hv⟩

theorem cTilde_eq_preBarSub_bot {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) :
    F11.CTilde M V₀ V = preBarSub M V₀ V hV ⊥ := by
  ext g
  rw [mem_cTilde_iff hV hM, mem_preBarSub]
  simp only [Subgroup.mem_bot]

@[expose] noncomputable def mBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : ℕ :=
  E3.mParam (Mbar M V₀ V hV)

@[expose] def calABar (k : ℕ) (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
  E3.aSet k (Mbar M V₀ V hV)

@[expose] noncomputable def aBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : ℕ :=
  E3.aParam (Mbar M V₀ V hV)

section Params

open scoped commutatorElement

variable {W : Type*} [CommGroup W]

@[expose] noncomputable def bParam (X Y : Subgroup (MulAut W)) : ℕ :=
  sSup {k : ℕ | 0 < k ∧ ∃ A ∈ E3.aSet k Y, ⁅X, A⁆ ≠ ⊥}

theorem bddAbove_bSet [Finite W] (X Y : Subgroup (MulAut W)) :
    BddAbove {k : ℕ | 0 < k ∧ ∃ A ∈ E3.aSet k Y, ⁅X, A⁆ ≠ ⊥} := by
  refine (E3.aSet_bddAbove Y).mono ?_
  rintro k ⟨hk, A, hA, -⟩
  exact ⟨hk, A, hA⟩

theorem le_bParam [Finite W] {k : ℕ} {X Y A : Subgroup (MulAut W)} (hk : 0 < k)
    (hA : A ∈ E3.aSet k Y) (hne : ⁅X, A⁆ ≠ ⊥) : k ≤ bParam X Y :=
  le_csSup (bddAbove_bSet X Y) ⟨hk, A, hA, hne⟩

theorem bParam_spec [Finite W] (X Y : Subgroup (MulAut W)) (h : 0 < bParam X Y) :
    ∃ A ∈ E3.aSet (bParam X Y) Y, ⁅X, A⁆ ≠ ⊥ := by
  have hne : {k : ℕ | 0 < k ∧ ∃ A ∈ E3.aSet k Y, ⁅X, A⁆ ≠ ⊥}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [bParam, hemp] at h
  exact (Nat.sSup_mem hne (bddAbove_bSet X Y)).2

theorem bParam_lt_iff [Finite W] {k : ℕ} (hk : 0 < k) (X Y : Subgroup (MulAut W)) :
    bParam X Y < k ↔ ∀ A ∈ E3.aSet k Y, ⁅X, A⁆ = ⊥ := by
  constructor
  · intro h A hA
    by_contra hne
    exact absurd (le_bParam hk hA hne) (not_le.2 h)
  · intro h
    by_contra hge
    have hge' : k ≤ bParam X Y := not_lt.1 hge
    obtain ⟨A, hA, hne⟩ := bParam_spec X Y (lt_of_lt_of_le hk hge')
    exact hne (h A (E3.aSet_anti hge' Y hA))

@[expose] def StableUnder (X : Subgroup (MulAut W)) (U : Subgroup W) : Prop :=
  ∀ x ∈ X, ∀ u ∈ U, x u ∈ U

@[expose] def IsIrrOn (X : Subgroup (MulAut W)) (I N : Subgroup W) : Prop :=
  N < I ∧ StableUnder X I ∧ StableUnder X N ∧
    ∀ J : Subgroup W, StableUnder X J → N ≤ J → J ≤ I → J = N ∨ J = I

@[expose] def irrSet (X : Subgroup (MulAut W)) : Set (Subgroup W) :=
  {I | commSub I X = I ∧ IsIrrOn X I (I ⊓ fixV X)}

end Params

@[expose] noncomputable def bBar (X M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : ℕ :=
  bParam (barSub V₀ V hV X) (Mbar M V₀ V hV)

open scoped commutatorElement in
theorem bBar_lt_iff [Finite G] {X M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {k : ℕ} (hk : 0 < k) :
    bBar X M V₀ V hV < k ↔ ∀ A ∈ calABar k M V₀ V hV, ⁅barSub V₀ V hV X, A⁆ = ⊥ :=
  bParam_lt_iff hk _ _

@[expose] def irrBar (X V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) : Set (Subgroup (Vtil V₀ V hV)) :=
  irrSet (barSub V₀ V hV X)

@[expose] noncomputable def compBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
  {K | IsComponentOf K (Mbar M V₀ V hV)}

@[expose] noncomputable def fstarBar [Finite G] (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  Fstar (Mbar M V₀ V hV)

@[expose] noncomputable def dParam (p : ℕ) : ℕ := orderOf (2 : ZMod p)

theorem pow_dParam (p : ℕ) : (2 : ZMod p) ^ dParam p = 1 := by
  by_cases hp : p = 0
  · subst hp
    simp [dParam]
  · haveI : NeZero p := ⟨hp⟩
    exact pow_orderOf_eq_one _

theorem dParam_pos {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 0 < dParam p := by
  haveI := Fact.mk hp
  have h2' : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  exact orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p - 1, by have := hp.one_lt; omega, ZMod.pow_card_sub_one_eq_one h2'⟩)

@[expose] noncomputable def dMinDeg (L : Type*) [Group L] : ℕ :=
  sInf {n : ℕ | ∃ f : L →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2), f ≠ 1}

@[expose] noncomputable def mSub (U : Subgroup G) : ℕ := rk U

theorem card_eq_two_pow_mSub {U : Subgroup G} [Finite G] (hU : IsPGroup 2 U) :
    Nat.card U = 2 ^ mSub U := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hU
  rw [mSub, rk, hn, padicValNat.prime_pow]

structure PairFacts (M V₀ V : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  elemAbelian₀ : IsElemAbelian 2 V₀
  le : V₀ ≤ V
  le_M : V ≤ M
  le_normalizer : M ≤ normalizer (V : Set G)
  le_normalizer₀ : M ≤ normalizer (V₀ : Set G)
  ne_bot : V ≠ ⊥

theorem hyp123_pairFacts {M T V₀ V : Subgroup G} (h : Hyp123 M T V₀ V) : PairFacts M V₀ V := by
  rcases h with ⟨⟨⟨⟨⟨hne, hVM, hMV, hE⟩, -⟩, -, -⟩, -⟩, rfl⟩ |
    ⟨⟨⟨-, hV₀M, hMV₀, hE₀⟩, ⟨hne, hVM, hMV, hE⟩, hle, -⟩, -, -⟩
  · refine ⟨hE, ⟨inferInstance, fun x hx => ?_⟩, bot_le, hVM, hMV, fun m _ => ?_, hne⟩
    · rw [Subgroup.mem_bot.1 hx]; simp
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      simp
  · exact ⟨hE, hE₀, hle, hVM, hMV, hMV₀, hne⟩

theorem hyp123_inCalV {M T V₀ V : Subgroup G} (h : Hyp123 M T V₀ V) : InCalV M V :=
  have hp := hyp123_pairFacts h
  ⟨hp.ne_bot, hp.le_M, hp.le_normalizer, hp.elemAbelian⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
