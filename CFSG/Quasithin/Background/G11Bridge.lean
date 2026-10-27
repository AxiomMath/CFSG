module

public import CFSG.Quasithin.Background.G11Basic
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

@[expose] def addEquivToLinear {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V'] (e : V ≃+ V') :
    V ≃ₗ[ZMod 2] V' where
  toFun := e
  map_add' := e.map_add
  map_smul' c v := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp
    · simp
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

@[simp] theorem addEquivToLinear_apply {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    (e : V ≃+ V') (v : V) : addEquivToLinear e v = e v := rfl

@[expose] def linEquivMulAut : (V ≃ₗ[ZMod 2] V) ≃* MulAut (Multiplicative V) where
  toFun g := AddEquiv.toMultiplicative g.toAddEquiv
  invFun f := addEquivToLinear (AddEquiv.toMultiplicative.symm f)
  left_inv g := by
    ext v
    rfl
  right_inv f := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

@[simp] theorem linEquivMulAut_apply (g : GLV V) (q : Multiplicative V) :
    linEquivMulAut g q = Multiplicative.ofAdd (g (Multiplicative.toAdd q)) := rfl

theorem toAdd_linEquivMulAut_apply (g : GLV V) (v : V) :
    Multiplicative.toAdd (linEquivMulAut g (Multiplicative.ofAdd v)) = g v := rfl

theorem linEquivMulAut_symm_apply (f : MulAut (Multiplicative V)) (v : V) :
    (linEquivMulAut.symm f) v = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) := rfl

theorem linEquivMulAut_injective : Function.Injective (linEquivMulAut (V := V)) :=
  linEquivMulAut.injective

theorem multiplicative_sq_eq_one (q : Multiplicative V) : q ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

instance linMulAct : MulDistribMulAction (GLV V) (Multiplicative V) where
  smul g q := Multiplicative.ofAdd (g (Multiplicative.toAdd q))
  one_smul q := rfl
  mul_smul g h q := rfl
  smul_mul g p q := by
    show Multiplicative.ofAdd (g (Multiplicative.toAdd p + Multiplicative.toAdd q)) = _
    rw [map_add]
    rfl
  smul_one g := by
    show Multiplicative.ofAdd (g 0) = 1
    rw [map_zero]
    rfl

theorem linMulAct_smul (g : GLV V) (q : Multiplicative V) :
    g • q = Multiplicative.ofAdd (g (Multiplicative.toAdd q)) := rfl

@[simp] theorem linMulAct_smul_ofAdd (g : GLV V) (v : V) :
    g • (Multiplicative.ofAdd v) = Multiplicative.ofAdd (g v) := rfl

@[simp] theorem toAdd_linMulAct_smul (g : GLV V) (q : Multiplicative V) :
    Multiplicative.toAdd (g • q) = g (Multiplicative.toAdd q) := rfl

theorem linEquivMulAut_smul_eq (g : GLV V) (q : Multiplicative V) :
    (linEquivMulAut g) • q = g • q := rfl

@[expose] def subToSubgroup : Submodule (ZMod 2) V ≃o Subgroup (Multiplicative V) where
  toFun U := AddSubgroup.toSubgroup U.toAddSubgroup
  invFun S :=
    { carrier := {v | Multiplicative.ofAdd v ∈ S}
      add_mem' := fun {a b} ha hb => S.mul_mem ha hb
      zero_mem' := S.one_mem
      smul_mem' := fun c v hv => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul]
          exact S.one_mem
        · rw [one_smul]
          exact hv }
  left_inv U := by
    ext v
    rfl
  right_inv S := by
    ext v
    rfl
  map_rel_iff' := by
    intro U U'
    constructor
    · intro h v hv
      exact h hv
    · intro h v hv
      exact h hv

theorem mem_subToSubgroup {U : Submodule (ZMod 2) V} {q : Multiplicative V} :
    q ∈ subToSubgroup U ↔ Multiplicative.toAdd q ∈ U := Iff.rfl

theorem ofAdd_mem_subToSubgroup {U : Submodule (ZMod 2) V} {v : V} :
    Multiplicative.ofAdd v ∈ subToSubgroup U ↔ v ∈ U := Iff.rfl

theorem mem_subToSubgroup_symm {S : Subgroup (Multiplicative V)} {v : V} :
    v ∈ subToSubgroup.symm S ↔ Multiplicative.ofAdd v ∈ S := Iff.rfl

theorem subToSubgroup_injective : Function.Injective (subToSubgroup (V := V)) :=
  subToSubgroup.injective

theorem subToSubgroup_inj {U U' : Submodule (ZMod 2) V} :
    subToSubgroup U = subToSubgroup U' ↔ U = U' := subToSubgroup.injective.eq_iff

theorem subToSubgroup_span (S : Set V) :
    subToSubgroup (Submodule.span (ZMod 2) S) = Subgroup.closure (Multiplicative.ofAdd '' S) := by
  apply le_antisymm
  · refine subToSubgroup.le_symm_apply.1 (Submodule.span_le.2 fun s hs => ?_)
    show Multiplicative.ofAdd s ∈ Subgroup.closure (Multiplicative.ofAdd '' S)
    exact Subgroup.subset_closure ⟨s, hs, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨s, hs, rfl⟩
    show s ∈ Submodule.span (ZMod 2) S
    exact Submodule.subset_span hs

@[expose] def toMulSub (K : Subgroup (GLV V)) : Subgroup (MulAut (Multiplicative V)) :=
  K.map linEquivMulAut.toMonoidHom

theorem mem_toMulSub {K : Subgroup (GLV V)} {f : MulAut (Multiplicative V)} :
    f ∈ toMulSub K ↔ linEquivMulAut.symm f ∈ K := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    simpa using hg
  · intro h
    exact ⟨_, h, by simp⟩

theorem linEquivMulAut_mem_toMulSub {K : Subgroup (GLV V)} {g : GLV V} :
    linEquivMulAut g ∈ toMulSub K ↔ g ∈ K := by
  rw [mem_toMulSub, MulEquiv.symm_apply_apply]

theorem toMulSub_le_iff {K K' : Subgroup (GLV V)} : toMulSub K ≤ toMulSub K' ↔ K ≤ K' :=
  (MulEquiv.mapSubgroup (linEquivMulAut (V := V))).le_iff_le (x := K) (y := K')

theorem toMulSub_injective : Function.Injective (toMulSub (V := V)) := fun _ _ h =>
  le_antisymm (toMulSub_le_iff.1 h.le) (toMulSub_le_iff.1 h.ge)

@[expose] def toMulSubIso : Subgroup (GLV V) ≃o Subgroup (MulAut (Multiplicative V)) :=
  MulEquiv.mapSubgroup linEquivMulAut

theorem toMulSubIso_apply (K : Subgroup (GLV V)) : toMulSubIso K = toMulSub K := rfl

theorem toMulSub_surjective : Function.Surjective (toMulSub (V := V)) :=
  toMulSubIso.surjective

theorem toMulSub_sup (K K' : Subgroup (GLV V)) : toMulSub (K ⊔ K') = toMulSub K ⊔ toMulSub K' :=
  toMulSubIso.map_sup K K'

theorem toMulSub_inf (K K' : Subgroup (GLV V)) : toMulSub (K ⊓ K') = toMulSub K ⊓ toMulSub K' :=
  toMulSubIso.map_inf K K'

theorem toMulSub_iSup {ι : Sort*} (f : ι → Subgroup (GLV V)) :
    toMulSub (⨆ i, f i) = ⨆ i, toMulSub (f i) :=
  toMulSubIso.map_iSup f

theorem toMulSub_eq_bot_iff {K : Subgroup (GLV V)} : toMulSub K = ⊥ ↔ K = ⊥ := by
  have : toMulSub (⊥ : Subgroup (GLV V)) = ⊥ := Subgroup.map_bot _
  rw [← this]
  exact toMulSub_injective.eq_iff

@[expose] def toMulSubEquiv (K : Subgroup (GLV V)) : ↥K ≃* ↥(toMulSub K) :=
  linEquivMulAut.subgroupMap K

@[simp] theorem coe_toMulSubEquiv (K : Subgroup (GLV V)) (k : ↥K) :
    ((toMulSubEquiv K k : ↥(toMulSub K)) : MulAut (Multiplicative V)) =
      linEquivMulAut (k : GLV V) := rfl


end G11

namespace XMod

section Congr

variable {A A' : Type*} [Group A] [Group A'] {Q : Type*} [CommGroup Q]
  [MulDistribMulAction A Q] [MulDistribMulAction A' Q] (e : A ≃* A')
  (he : ∀ (a : A) (q : Q), e a • q = a • q)

include he

theorem isInv_congr_equiv (L : Subgroup Q) : IsInv A' L ↔ IsInv A L := by
  constructor
  · intro h a l hl
    rw [← he a l]
    exact h (e a) l hl
  · intro h a' l hl
    obtain ⟨a, rfl⟩ := e.surjective a'
    rw [he a l]
    exact h a l hl

theorem fixed_congr_equiv (L : Subgroup Q) : fixed A' L = fixed A L := by
  ext q
  constructor
  · rintro ⟨hq, hfix⟩
    exact ⟨hq, fun a => by rw [← he a q]; exact hfix (e a)⟩
  · rintro ⟨hq, hfix⟩
    refine ⟨hq, fun a' => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective a'
    rw [he a q]
    exact hfix a

theorem commOf_congr_equiv (L : Subgroup Q) : commOf A' L = commOf A L := by
  unfold commOf
  congr 1
  ext c
  constructor
  · rintro ⟨a', l, hl, rfl⟩
    obtain ⟨a, rfl⟩ := e.surjective a'
    exact ⟨a, l, hl, by rw [he a l]⟩
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨e a, l, hl, by rw [he a l]⟩

theorem isIrrSec_congr_equiv (C L : Subgroup Q) : IsIrrSec A' C L ↔ IsIrrSec A C L := by
  unfold IsIrrSec
  simp only [isInv_congr_equiv e he]

theorem isIrr_congr_equiv (L : Subgroup Q) : IsIrr A' L ↔ IsIrr A L := by
  unfold IsIrr
  rw [isInv_congr_equiv e he, isIrrSec_congr_equiv e he]

theorem isIrrPlus_congr_equiv (I : Subgroup Q) : IsIrrPlus A' I ↔ IsIrrPlus A I := by
  unfold IsIrrPlus
  rw [isInv_congr_equiv e he, commOf_congr_equiv e he, fixed_congr_equiv e he,
    isIrrSec_congr_equiv e he]

theorem iso_congr_equiv (L L' : Subgroup Q) : Iso A' L L' ↔ Iso A L L' := by
  unfold Iso
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun a l l' h => ?_⟩
    rw [← he a] at h ⊢
    exact hφ (e a) l l' h
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun a' l l' h => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective a'
    rw [he a] at h ⊢
    exact hφ a l l' h

theorem isHomComp_congr_equiv (M L : Subgroup Q) : IsHomComp A' M L ↔ IsHomComp A M L := by
  unfold IsHomComp
  simp only [isIrr_congr_equiv e he, iso_congr_equiv e he]

end Congr

end XMod

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[simp] theorem toMulSubEquiv_smul (K : Subgroup (GLV V)) (k : ↥K) (q : Multiplicative V) :
    (toMulSubEquiv K k) • q = k • q := rfl

section XMod

variable {K : Subgroup (GLV V)} {U C L I J M : Submodule (ZMod 2) V}

theorem smul_mul_inv_eq (g : GLV V) (v : V) :
    (g • Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹ = Multiplicative.ofAdd (g v - v) := by
  apply Multiplicative.toAdd.injective
  simp [sub_eq_add_neg]

theorem invariant_iff_isInv : Invariant K U ↔ XMod.IsInv ↥K (subToSubgroup U) := by
  constructor
  · intro h a l hl
    exact h a a.2 (Multiplicative.toAdd l) hl
  · intro h k hk u hu
    exact h ⟨k, hk⟩ (Multiplicative.ofAdd u) hu

theorem invariant_symm_iff {S : Subgroup (Multiplicative V)} :
    Invariant K (subToSubgroup.symm S) ↔ XMod.IsInv ↥K S := by
  rw [invariant_iff_isInv, OrderIso.apply_symm_apply]

theorem fixed_eq (U : Submodule (ZMod 2) V) :
    XMod.fixed ↥K (subToSubgroup U) = subToSubgroup (fixedSpace K ⊓ U) := by
  ext q
  constructor
  · rintro ⟨hqU, hfix⟩
    exact ⟨fun k hk => congrArg Multiplicative.toAdd (hfix ⟨k, hk⟩), hqU⟩
  · rintro ⟨hf, hqU⟩
    exact ⟨hqU, fun a => congrArg Multiplicative.ofAdd (hf a a.2)⟩

theorem fixed_top_eq :
    XMod.fixed ↥K (⊤ : Subgroup (Multiplicative V)) = subToSubgroup (fixedSpace K) := by
  have := fixed_eq (K := K) ⊤
  rwa [OrderIso.map_top, inf_top_eq] at this

theorem commOf_eq (U : Submodule (ZMod 2) V) :
    XMod.commOf ↥K (subToSubgroup U) = subToSubgroup (commSpace K U) := by
  rw [commSpace, subToSubgroup_span, XMod.commOf]
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    refine ⟨(a : GLV V) (Multiplicative.toAdd l) - Multiplicative.toAdd l,
      ⟨a, a.2, Multiplicative.toAdd l, hl, rfl⟩, ?_⟩
    exact (smul_mul_inv_eq (a : GLV V) (Multiplicative.toAdd l)).symm
  · rintro ⟨_, ⟨k, hk, u, hu, rfl⟩, rfl⟩
    exact ⟨⟨k, hk⟩, Multiplicative.ofAdd u, hu, (smul_mul_inv_eq k u).symm⟩

theorem commOf_top_eq :
    XMod.commOf ↥K (⊤ : Subgroup (Multiplicative V)) = subToSubgroup (commSpace K ⊤) := by
  have := commOf_eq (K := K) ⊤
  rwa [OrderIso.map_top] at this

theorem irrSec_iff : IrrSec K C L ↔ XMod.IsIrrSec ↥K (subToSubgroup C) (subToSubgroup L) := by
  unfold IrrSec XMod.IsIrrSec
  rw [subToSubgroup.lt_iff_lt]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h J' hJ' hCJ' hJ'L
    have h1 := h (subToSubgroup.symm J') (invariant_symm_iff.2 hJ')
      (subToSubgroup.le_symm_apply.2 hCJ') (subToSubgroup.symm_apply_le.2 hJ'L)
    rcases h1 with h1 | h1
    · left
      rw [← subToSubgroup.apply_symm_apply J', h1]
    · right
      rw [← subToSubgroup.apply_symm_apply J', h1]
  · intro h J hJ hCJ hJL
    rcases h (subToSubgroup J) (invariant_iff_isInv.1 hJ) (subToSubgroup.monotone hCJ)
      (subToSubgroup.monotone hJL) with h1 | h1
    · exact Or.inl (subToSubgroup.injective h1)
    · exact Or.inr (subToSubgroup.injective h1)

theorem isIrr_iff : IsIrr K U ↔ XMod.IsIrr ↥K (subToSubgroup U) := by
  unfold IsIrr XMod.IsIrr
  rw [invariant_iff_isInv, irrSec_iff, OrderIso.map_bot]

theorem irrPlus_iff : IrrPlus K I ↔ XMod.IsIrrPlus ↥K (subToSubgroup I) := by
  unfold IrrPlus XMod.IsIrrPlus
  rw [invariant_iff_isInv, irrSec_iff, fixed_eq, commOf_eq, subToSubgroup_inj]

theorem mem_irrPlus_top_iff :
    subToSubgroup I ∈ CFSG.Quasithin.IrrPlus K (⊤ : Subgroup (Multiplicative V)) ↔ IrrPlus K I := by
  rw [irrPlus_iff]
  exact ⟨fun h => h.2, fun h => ⟨le_top, h⟩⟩

theorem hIso_iff : HIso K I J ↔ XMod.Iso ↥K (subToSubgroup I) (subToSubgroup J) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨
      { toFun := fun x => ⟨Multiplicative.ofAdd
          ((φ ⟨Multiplicative.toAdd (x : Multiplicative V), x.2⟩ : J) : V),
          (φ ⟨Multiplicative.toAdd (x : Multiplicative V), x.2⟩).2⟩
        invFun := fun y => ⟨Multiplicative.ofAdd
          ((φ.symm ⟨Multiplicative.toAdd (y : Multiplicative V), y.2⟩ : I) : V),
          (φ.symm ⟨Multiplicative.toAdd (y : Multiplicative V), y.2⟩).2⟩
        left_inv := fun x => by
          apply Subtype.ext
          change Multiplicative.ofAdd (((φ.symm (φ ⟨Multiplicative.toAdd (x : Multiplicative V),
            x.2⟩) : I)) : V) = x
          rw [LinearEquiv.symm_apply_apply]
          rfl
        right_inv := fun y => by
          apply Subtype.ext
          change Multiplicative.ofAdd (((φ (φ.symm ⟨Multiplicative.toAdd (y : Multiplicative V),
            y.2⟩) : J)) : V) = y
          rw [LinearEquiv.apply_symm_apply]
          rfl
        map_mul' := fun x y => by
          apply Subtype.ext
          change Multiplicative.ofAdd ((φ (⟨Multiplicative.toAdd (x : Multiplicative V), x.2⟩ +
            ⟨Multiplicative.toAdd (y : Multiplicative V), y.2⟩) : J) : V) = _
          rw [map_add]
          rfl },
      fun a l l' hl => ?_⟩
    exact hφ a a.2 ⟨Multiplicative.toAdd (l : Multiplicative V), l.2⟩
      ⟨Multiplicative.toAdd (l' : Multiplicative V), l'.2⟩ (congrArg Multiplicative.toAdd hl)
  · rintro ⟨ψ, hψ⟩
    refine ⟨addEquivToLinear
      { toFun := fun i => ⟨Multiplicative.toAdd (ψ ⟨Multiplicative.ofAdd (i : V), i.2⟩ :
          subToSubgroup J).1, (ψ ⟨Multiplicative.ofAdd (i : V), i.2⟩).2⟩
        invFun := fun j => ⟨Multiplicative.toAdd (ψ.symm ⟨Multiplicative.ofAdd (j : V), j.2⟩ :
          subToSubgroup I).1, (ψ.symm ⟨Multiplicative.ofAdd (j : V), j.2⟩).2⟩
        left_inv := fun i => by
          apply Subtype.ext
          change Multiplicative.toAdd ((ψ.symm (ψ ⟨Multiplicative.ofAdd (i : V), i.2⟩) :
            subToSubgroup I).1) = i
          rw [MulEquiv.symm_apply_apply]
          rfl
        right_inv := fun j => by
          apply Subtype.ext
          change Multiplicative.toAdd ((ψ (ψ.symm ⟨Multiplicative.ofAdd (j : V), j.2⟩) :
            subToSubgroup J).1) = j
          rw [MulEquiv.apply_symm_apply]
          rfl
        map_add' := fun i i' => by
          apply Subtype.ext
          change Multiplicative.toAdd ((ψ (⟨Multiplicative.ofAdd (i : V), i.2⟩ *
            ⟨Multiplicative.ofAdd (i' : V), i'.2⟩) : subToSubgroup J).1) = _
          rw [map_mul]
          rfl }, fun k hk i j hij => ?_⟩
    exact congrArg Multiplicative.toAdd (hψ ⟨k, hk⟩ ⟨Multiplicative.ofAdd (i : V), i.2⟩
      ⟨Multiplicative.ofAdd (j : V), j.2⟩ (congrArg Multiplicative.ofAdd hij))

@[expose] def HomComp (K : Subgroup (GLV V)) (M L : Submodule (ZMod 2) V) : Prop :=
  IsIrr K L ∧ L ≤ M ∧ ∀ J : Submodule (ZMod 2) V, J ≤ M → IsIrr K J → HIso K J L → J ≤ L

theorem homComp_iff :
    HomComp K M L ↔ XMod.IsHomComp ↥K (subToSubgroup M) (subToSubgroup L) := by
  unfold HomComp XMod.IsHomComp
  rw [isIrr_iff, subToSubgroup.le_iff_le]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h J' hJ'M hJ'irr hJ'iso
    have h1 := h (subToSubgroup.symm J') (subToSubgroup.symm_apply_le.2 hJ'M)
    rw [isIrr_iff, OrderIso.apply_symm_apply] at h1
    rw [hIso_iff, OrderIso.apply_symm_apply] at h1
    have h2 := h1 hJ'irr hJ'iso
    exact subToSubgroup.symm_apply_le.1 h2
  · intro h J hJM hJirr hJiso
    exact subToSubgroup.le_iff_le.1
      (h (subToSubgroup J) (subToSubgroup.monotone hJM) (isIrr_iff.1 hJirr) (hIso_iff.1 hJiso))

theorem homogeneous_iff :
    Homogeneous K ↔ ∀ I J : Subgroup (Multiplicative V), XMod.IsIrrPlus ↥K I →
      XMod.IsIrrPlus ↥K J → XMod.Iso ↥K I J := by
  constructor
  · intro h I J hI hJ
    obtain ⟨I', rfl⟩ := subToSubgroup.surjective I
    obtain ⟨J', rfl⟩ := subToSubgroup.surjective J
    exact hIso_iff.1 (h I' J' (irrPlus_iff.2 hI) (irrPlus_iff.2 hJ))
  · intro h I J hI hJ
    exact hIso_iff.2 (h _ _ (irrPlus_iff.1 hI) (irrPlus_iff.1 hJ))

end XMod

section ToMulSub

variable {K : Subgroup (GLV V)} {U C L I J M : Submodule (ZMod 2) V}

theorem toMulSubEquiv_compat (K : Subgroup (GLV V)) :
    ∀ (k : ↥K) (q : Multiplicative V), toMulSubEquiv K k • q = k • q := fun _ _ => rfl

theorem invariant_iff_isInv_toMulSub :
    Invariant K U ↔ XMod.IsInv ↥(toMulSub K) (subToSubgroup U) :=
  invariant_iff_isInv.trans
    (XMod.isInv_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _).symm

theorem fixed_eq_toMulSub (U : Submodule (ZMod 2) V) :
    XMod.fixed ↥(toMulSub K) (subToSubgroup U) = subToSubgroup (fixedSpace K ⊓ U) :=
  (XMod.fixed_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _).trans (fixed_eq U)

theorem commOf_eq_toMulSub (U : Submodule (ZMod 2) V) :
    XMod.commOf ↥(toMulSub K) (subToSubgroup U) = subToSubgroup (commSpace K U) :=
  (XMod.commOf_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _).trans (commOf_eq U)

theorem irrSec_iff_toMulSub :
    IrrSec K C L ↔ XMod.IsIrrSec ↥(toMulSub K) (subToSubgroup C) (subToSubgroup L) :=
  irrSec_iff.trans
    (XMod.isIrrSec_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _ _).symm

theorem isIrr_iff_toMulSub : IsIrr K U ↔ XMod.IsIrr ↥(toMulSub K) (subToSubgroup U) :=
  isIrr_iff.trans (XMod.isIrr_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _).symm

theorem irrPlus_iff_toMulSub :
    IrrPlus K I ↔ XMod.IsIrrPlus ↥(toMulSub K) (subToSubgroup I) :=
  irrPlus_iff.trans (XMod.isIrrPlus_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _).symm

theorem hIso_iff_toMulSub :
    HIso K I J ↔ XMod.Iso ↥(toMulSub K) (subToSubgroup I) (subToSubgroup J) :=
  hIso_iff.trans (XMod.iso_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _ _).symm

theorem fixed_top_eq_toMulSub :
    XMod.fixed ↥(toMulSub K) (⊤ : Subgroup (Multiplicative V)) = subToSubgroup (fixedSpace K) := by
  have := fixed_eq_toMulSub (K := K) ⊤
  rwa [OrderIso.map_top, inf_top_eq] at this

theorem commOf_top_eq_toMulSub :
    XMod.commOf ↥(toMulSub K) (⊤ : Subgroup (Multiplicative V)) =
      subToSubgroup (commSpace K ⊤) := by
  have := commOf_eq_toMulSub (K := K) ⊤
  rwa [OrderIso.map_top] at this

theorem homComp_iff_toMulSub :
    HomComp K M L ↔ XMod.IsHomComp ↥(toMulSub K) (subToSubgroup M) (subToSubgroup L) :=
  homComp_iff.trans
    (XMod.isHomComp_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) _ _).symm

theorem homogeneous_iff_toMulSub :
    Homogeneous K ↔ ∀ I J : Subgroup (Multiplicative V), XMod.IsIrrPlus ↥(toMulSub K) I →
      XMod.IsIrrPlus ↥(toMulSub K) J → XMod.Iso ↥(toMulSub K) I J := by
  rw [homogeneous_iff]
  constructor
  · intro h I J hI hJ
    exact (XMod.iso_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) I J).2
      (h I J ((XMod.isIrrPlus_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) I).1 hI)
        ((XMod.isIrrPlus_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) J).1 hJ))
  · intro h I J hI hJ
    exact (XMod.iso_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) I J).1
      (h I J ((XMod.isIrrPlus_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) I).2 hI)
        ((XMod.isIrrPlus_congr_equiv (toMulSubEquiv K) (toMulSubEquiv_compat K) J).2 hJ))

end ToMulSub

section Local

variable {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}

theorem subToSubgroup_conjSub (g : GLV V) (U : Submodule (ZMod 2) V) :
    subToSubgroup (conjSub g U) = g • subToSubgroup U := by
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_subToSubgroup, mem_subToSubgroup,
    mem_conjSub]
  rfl

theorem subToSubgroup_conjSub_toMulSub (g : GLV V) (U : Submodule (ZMod 2) V) :
    subToSubgroup (conjSub g U) = (subToSubgroup U).map (linEquivMulAut g).toMonoidHom := by
  rw [subToSubgroup_conjSub]
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ • q, h, by simp⟩
  · rintro ⟨p, hp, rfl⟩
    simpa using hp

theorem mem_centralizerOn_iff_smul {k : GLV V} :
    k ∈ centralizerOn K U ↔ k ∈ K ∧ ∀ u ∈ subToSubgroup U, k • u = u := by
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun u hu => congrArg Multiplicative.ofAdd (h (Multiplicative.toAdd u) hu)⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun u hu => congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd u) hu)⟩

theorem mem_stabilizerOf_iff_smul {k : GLV V} :
    k ∈ stabilizerOf K U ↔ k ∈ K ∧ k • subToSubgroup U = subToSubgroup U := by
  rw [← subToSubgroup_conjSub]
  exact and_congr_right fun _ => subToSubgroup_inj.symm

theorem mem_toMulSub_centralizerOn_iff {f : MulAut (Multiplicative V)} :
    f ∈ toMulSub (centralizerOn K U) ↔ f ∈ toMulSub K ∧ ∀ u ∈ subToSubgroup U, f u = u := by
  obtain ⟨g, rfl⟩ := linEquivMulAut.surjective f
  rw [linEquivMulAut_mem_toMulSub, linEquivMulAut_mem_toMulSub, mem_centralizerOn_iff_smul]
  exact Iff.rfl

theorem mem_toMulSub_stabilizerOf_iff {f : MulAut (Multiplicative V)} :
    f ∈ toMulSub (stabilizerOf K U) ↔
      f ∈ toMulSub K ∧ (subToSubgroup U).map f.toMonoidHom = subToSubgroup U := by
  obtain ⟨g, rfl⟩ := linEquivMulAut.surjective f
  rw [linEquivMulAut_mem_toMulSub, linEquivMulAut_mem_toMulSub]
  have h1 : g ∈ stabilizerOf K U ↔ g ∈ K ∧ conjSub g U = U := Iff.rfl
  rw [h1]
  refine and_congr_right fun _ => ?_
  rw [← subToSubgroup_inj, subToSubgroup_conjSub_toMulSub]

theorem fixV_toMulSub (K : Subgroup (GLV V)) : fixV (toMulSub K) = subToSubgroup (fixedSpace K) := by
  ext q
  constructor
  · intro h k hk
    exact congrArg Multiplicative.toAdd (h (linEquivMulAut k) (linEquivMulAut_mem_toMulSub.2 hk))
  · intro h f hf
    obtain ⟨g, rfl⟩ := linEquivMulAut.surjective f
    exact congrArg Multiplicative.ofAdd (h g (linEquivMulAut_mem_toMulSub.1 hf))

theorem commV_toMulSub (K : Subgroup (GLV V)) :
    commV (toMulSub K) = subToSubgroup (commSpace K ⊤) := by
  rw [commSpace, subToSubgroup_span, commV]
  congr 1
  ext c
  constructor
  · rintro ⟨f, hf, q, rfl⟩
    obtain ⟨g, rfl⟩ := linEquivMulAut.surjective f
    refine ⟨g (Multiplicative.toAdd q) - Multiplicative.toAdd q,
      ⟨g, linEquivMulAut_mem_toMulSub.1 hf, Multiplicative.toAdd q, Submodule.mem_top, rfl⟩, ?_⟩
    exact (smul_mul_inv_eq g (Multiplicative.toAdd q)).symm
  · rintro ⟨_, ⟨k, hk, u, -, rfl⟩, rfl⟩
    exact ⟨linEquivMulAut k, linEquivMulAut_mem_toMulSub.2 hk, Multiplicative.ofAdd u,
      smul_mul_inv_eq k u⟩

end Local

section Card

theorem natCard_subToSubgroup (U : Submodule (ZMod 2) V) :
    Nat.card (subToSubgroup U) = Nat.card U :=
  Nat.card_congr (Multiplicative.toAdd.subtypeEquiv fun _ => Iff.rfl)

theorem natCard_eq_two_pow_finrank [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod]

theorem natCard_subToSubgroup_eq [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card (subToSubgroup U) = 2 ^ Module.finrank (ZMod 2) U := by
  rw [natCard_subToSubgroup, natCard_eq_two_pow_finrank]

theorem natCard_subToSubgroup_le_iff [Finite V] (U : Submodule (ZMod 2) V) (n : ℕ) :
    Nat.card (subToSubgroup U) ≤ 2 ^ n ↔ Module.finrank (ZMod 2) U ≤ n := by
  rw [natCard_subToSubgroup_eq]
  exact Nat.pow_le_pow_iff_right (by norm_num)

theorem natCard_subToSubgroup_eq_iff [Finite V] (U : Submodule (ZMod 2) V) (n : ℕ) :
    Nat.card (subToSubgroup U) = 2 ^ n ↔ Module.finrank (ZMod 2) U = n := by
  rw [natCard_subToSubgroup_eq]
  exact Nat.pow_right_inj (by norm_num)

theorem commSpace_zpowers_top (a : GLV V) :
    commSpace (Subgroup.zpowers a) ⊤ = LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  set R := LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id) with hR
  have haR : ∀ w : V, a w - w ∈ R := fun w => ⟨w, by simp⟩
  let S : Subgroup (GLV V) :=
    { carrier := {k | ∀ u, k u - u ∈ R}
      mul_mem' := fun {k k'} hk hk' u => by
        have : (k * k') u - u = (k (k' u) - k' u) + (k' u - u) := by
          show k (k' u) - u = _
          abel
        rw [this]
        exact R.add_mem (hk _) (hk' u)
      one_mem' := fun u => by
        simp
      inv_mem' := fun {k} hk u => by
        have h1 : k⁻¹ u - u = -(k (k⁻¹ u) - k⁻¹ u) := by
          have : k (k⁻¹ u) = u := by simp
          rw [this]
          abel
        rw [h1]
        exact R.neg_mem (hk _) }
  have hS : Subgroup.zpowers a ≤ S := by
    rw [Subgroup.zpowers_le]
    exact haR
  apply le_antisymm
  · rw [commSpace_le_iff]
    intro k hk u _
    exact hS hk u
  · rintro _ ⟨w, rfl⟩
    have : (a : V →ₗ[ZMod 2] V) w - w ∈ commSpace (Subgroup.zpowers a) ⊤ :=
      sub_mem_commSpace (Subgroup.mem_zpowers a) Submodule.mem_top
    simpa using this

theorem commV_zpowers_toMulSub (a : GLV V) :
    commV (Subgroup.zpowers (linEquivMulAut a)) =
      subToSubgroup (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) := by
  have h1 : Subgroup.zpowers (linEquivMulAut a) = toMulSub (Subgroup.zpowers a) :=
    (MonoidHom.map_zpowers linEquivMulAut.toMonoidHom a).symm
  rw [h1, commV_toMulSub, commSpace_zpowers_top]

end Card

section HIsoApi

variable {K : Subgroup (GLV V)} {I J M : Submodule (ZMod 2) V}

theorem HIso.refl (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : HIso K I I :=
  ⟨LinearEquiv.refl _ _, fun _ _ _ _ h => h⟩

theorem HIso.trans (h : HIso K I J) (h' : HIso K J M) : HIso K I M := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨ψ, hψ⟩ := h'
  exact ⟨φ.trans ψ, fun k hk i j hij => hψ k hk (φ i) (φ j) (hφ k hk i j hij)⟩

theorem HIso.symm (hI : Invariant K I) (h : HIso K I J) : HIso K J I := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun k hk i j hij => ?_⟩
  set x : I := φ.symm i with hx
  have hy : k (x : V) ∈ I := hI k hk _ x.2
  have h1 := hφ k hk x ⟨k (x : V), hy⟩ rfl
  have h2 : ((φ ⟨k (x : V), hy⟩ : J) : V) = (j : V) := by
    rw [← h1]
    have : ((φ x : J) : V) = (i : V) := by rw [hx, LinearEquiv.apply_symm_apply]
    rw [this]
    exact hij
  have h3 : φ ⟨k (x : V), hy⟩ = j := Subtype.ext h2
  have h4 : (⟨k (x : V), hy⟩ : I) = φ.symm j := by
    rw [← h3, LinearEquiv.symm_apply_apply]
  exact congrArg Subtype.val h4

theorem HIso.finrank_eq (h : HIso K I J) :
    Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) J := by
  obtain ⟨φ, -⟩ := h
  exact φ.finrank_eq

theorem hIso_comm (hI : Invariant K I) (hJ : Invariant K J) : HIso K I J ↔ HIso K J I :=
  ⟨HIso.symm hI, HIso.symm hJ⟩

end HIsoApi

end G11

end CFSG.Quasithin
