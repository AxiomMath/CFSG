module

public import CFSG.LinearAlgebra.QuadraticNormalSubgroupCore
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin
  CFSG.LinearAlgebra CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

abbrev VG (G : Subgroup (LGL 2 V)) : Type := Multiplicative V ⋊[linearAction G] G

variable {G : Subgroup (LGL 2 V)}

instance : Finite (VG G) :=
  Finite.of_injective (fun x : VG G => (x.left, x.right))
    fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

@[expose] def wHat (G : Subgroup (LGL 2 V)) (W : Submodule (ZMod 2) V) : Subgroup (VG G) :=
  (AddSubgroup.toSubgroup W.toAddSubgroup).map SemidirectProduct.inl

@[expose] def vHat (G : Subgroup (LGL 2 V)) : Subgroup (VG G) := wHat G ⊤

@[expose] def aHat (G A : Subgroup (LGL 2 V)) : Subgroup (VG G) :=
  (A.subgroupOf G).map SemidirectProduct.inr

@[expose] def projG (G : Subgroup (LGL 2 V)) : VG G →* LGL 2 V :=
  G.subtype.comp SemidirectProduct.rightHom

@[expose] def UAOf (G : Subgroup (LGL 2 V))
    (VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V) (A : Subgroup (LGL 2 V)) :
    Subgroup (VG G) :=
  wHat G (VA A) ⊔ aHat G A

theorem mem_wHat {W : Submodule (ZMod 2) V} {x : VG G} :
    x ∈ wHat G W ↔ ∃ v ∈ W, x = SemidirectProduct.inl (Multiplicative.ofAdd v) := by
  unfold wHat
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Multiplicative.toAdd y, hy, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

theorem mem_aHat {A : Subgroup (LGL 2 V)} {x : VG G} :
    x ∈ aHat G A ↔ ∃ g : G, (g : LGL 2 V) ∈ A ∧ x = SemidirectProduct.inr g := by
  unfold aHat
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

@[simp] theorem projG_inl (v : V) :
    projG G (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) = 1 := by
  simp [projG]

@[simp] theorem projG_inr (g : G) :
    projG G (SemidirectProduct.inr g : VG G) = (g : LGL 2 V) := by
  simp [projG]

theorem inr_mul_inl_mul_inr_inv (g : G) (v : V) :
    (SemidirectProduct.inr g : VG G) * SemidirectProduct.inl (Multiplicative.ofAdd v) *
        (SemidirectProduct.inr g : VG G)⁻¹ =
      SemidirectProduct.inl (Multiplicative.ofAdd ((g : LGL 2 V) v)) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem exists_eq_inl_mul_inr (x : VG G) :
    ∃ (v : V) (g : G),
      x = SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g := by
  exact ⟨Multiplicative.toAdd x.left, x.right, by
    rw [ofAdd_toAdd]; exact (SemidirectProduct.inl_left_mul_inr_right x).symm⟩

theorem wHat_mono {W W' : Submodule (ZMod 2) V} (h : W ≤ W') : wHat G W ≤ wHat G W' := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_wHat.mp hx
  exact mem_wHat.mpr ⟨v, h hv, rfl⟩

@[simp] theorem wHat_bot : wHat G (⊥ : Submodule (ZMod 2) V) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_wHat.mp hx
  rw [Submodule.mem_bot] at hv
  subst hv
  simp

theorem wHat_eq_bot_iff {W : Submodule (ZMod 2) V} : wHat G W = ⊥ ↔ W = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hx : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) ∈ wHat G W :=
      mem_wHat.mpr ⟨v, hv, rfl⟩
    rw [h, Subgroup.mem_bot] at hx
    have := SemidirectProduct.inl_injective (hx.trans (map_one SemidirectProduct.inl).symm)
    simpa using this
  · rintro rfl
    exact wHat_bot

theorem wHat_le_vHat (W : Submodule (ZMod 2) V) : wHat G W ≤ vHat G :=
  wHat_mono le_top

theorem normal_vHat : (vHat G).Normal := by
  have h : vHat G = (SemidirectProduct.rightHom : VG G →* G).ker := by
    ext x
    rw [MonoidHom.mem_ker, SemidirectProduct.rightHom_eq_right]
    constructor
    · intro hx
      obtain ⟨v, -, rfl⟩ := mem_wHat.mp hx
      simp
    · intro hx
      refine mem_wHat.mpr ⟨Multiplicative.toAdd x.left, Submodule.mem_top, ?_⟩
      rw [ofAdd_toAdd]
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
      rw [hx, map_one, mul_one]
  rw [h]
  exact MonoidHom.normal_ker _

theorem isElemAbelian_wHat (W : Submodule (ZMod 2) V) : IsElemAbelian 2 (wHat G W) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨v, hv, hav⟩ := mem_wHat.mp a.2
    obtain ⟨w, hw, hbw⟩ := mem_wHat.mp b.2
    apply Subtype.ext
    change (a : VG G) * b = b * a
    rw [hav, hbw, ← map_mul SemidirectProduct.inl, ← map_mul SemidirectProduct.inl,
      mul_comm (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)]
  · obtain ⟨v, hv, rfl⟩ := mem_wHat.mp hx
    rw [pow_two, ← map_mul, ← ofAdd_add, ZModModule.add_self]
    simp

theorem wHat_le_pCoreOf (W : Submodule (ZMod 2) V) :
    wHat G W ≤ pCoreOf 2 (⊤ : Subgroup (VG G)) := by
  refine le_trans (wHat_le_vHat W) ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 le_top (normal_vHat.subgroupOf _)
    (isElemAbelian_wHat ⊤).isPGroup

theorem aHat_eq_bot_iff {A : Subgroup (LGL 2 V)} (hA : A ≤ G) : aHat G A = ⊥ ↔ A = ⊥ := by
  constructor
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (SemidirectProduct.inr (⟨x, hA hx⟩ : G) : VG G) ∈ aHat G A :=
      mem_aHat.mpr ⟨⟨x, hA hx⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    have := SemidirectProduct.inr_injective (hx'.trans (map_one SemidirectProduct.inr).symm)
    exact congrArg Subtype.val this
  · rintro rfl
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hx
    rw [Subgroup.mem_bot] at hg ⊢
    have : g = 1 := Subtype.ext hg
    simp [this]

theorem isElemAbelian_aHat {A : Subgroup (LGL 2 V)} (h : IsElemAbelian 2 A) :
    IsElemAbelian 2 (aHat G A) := by
  unfold aHat
  exact (h.subgroupOf G).map SemidirectProduct.inr

theorem map_projG_wHat (W : Submodule (ZMod 2) V) : (wHat G W).map (projG G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨v, -, rfl⟩ := mem_wHat.mp hy
  simp [projG]

theorem map_projG_aHat {A : Subgroup (LGL 2 V)} (hA : A ≤ G) : (aHat G A).map (projG G) = A := by
  unfold aHat
  rw [Subgroup.map_map]
  have : (projG G).comp SemidirectProduct.inr = G.subtype := by
    ext g; simp [projG]
  rw [this]
  exact Subgroup.map_subgroupOf_eq_of_le hA

theorem map_projG_pCoreOf_le :
    (pCoreOf 2 (⊤ : Subgroup (VG G))).map (projG G) ≤ pCoreOf 2 G := by
  let f : (⊤ : Subgroup (VG G)) →* G :=
    (SemidirectProduct.rightHom : VG G →* G).comp (⊤ : Subgroup (VG G)).subtype
  have hf : Function.Surjective f := fun g =>
    ⟨⟨SemidirectProduct.inr g, trivial⟩, by simp [f]⟩
  have h1 := CFSG.LieType.BorelTits.map_pCore_le 2 f hf
  unfold pCoreOf
  rw [Subgroup.map_map]
  have : (projG G).comp (⊤ : Subgroup (VG G)).subtype = G.subtype.comp f := rfl
  rw [this, ← Subgroup.map_map]
  exact Subgroup.map_mono h1

private theorem aHat_le_normalizer_wHat {W : Submodule (ZMod 2) V} {A : Subgroup (LGL 2 V)}
    (hstab : ∀ a ∈ A, conjSub a W = W) :
    aHat G A ≤ Subgroup.normalizer ((wHat G W : Subgroup (VG G)) : Set (VG G)) := by
  have key : ∀ g : G, (g : LGL 2 V) ∈ A → ∀ v ∈ W, (g : LGL 2 V) v ∈ W := by
    intro g hg v hv
    have : (g : LGL 2 V) v ∈ conjSub (g : LGL 2 V) W := by
      rw [mem_conjSub]; simpa using hv
    rwa [hstab _ hg] at this
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨v, hv, rfl⟩ := mem_wHat.mp hy
    rw [inr_mul_inl_mul_inr_inv]
    exact mem_wHat.mpr ⟨(g : LGL 2 V) v, key g hg v hv, rfl⟩
  · intro hy
    obtain ⟨w, hw, hw'⟩ := mem_wHat.mp hy
    have h3 := inr_mul_inl_mul_inr_inv g⁻¹ w
    rw [map_inv SemidirectProduct.inr g, inv_inv] at h3
    have hy2 : y = (SemidirectProduct.inr g : VG G)⁻¹ *
        ((SemidirectProduct.inr g : VG G) * y * (SemidirectProduct.inr g : VG G)⁻¹) *
          SemidirectProduct.inr g := by group
    rw [hy2, hw', h3]
    exact mem_wHat.mpr ⟨_, key g⁻¹ (by simpa using A.inv_mem hg) w hw, rfl⟩

theorem mem_wHat_sup_aHat {W : Submodule (ZMod 2) V} {A : Subgroup (LGL 2 V)}
    (hstab : ∀ a ∈ A, conjSub a W = W) {x : VG G} :
    x ∈ wHat G W ⊔ aHat G A ↔
      ∃ v ∈ W, ∃ g : G, (g : LGL 2 V) ∈ A ∧
        x = SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g := by
  have hle := aHat_le_normalizer_wHat (G := G) hstab
  have := Subgroup.coe_mul_of_right_le_normalizer_left (wHat G W) (aHat G A) hle
  rw [← SetLike.mem_coe, this, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨v, hv, rfl⟩ := mem_wHat.mp ha
    obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hb
    exact ⟨v, hv, g, hg, rfl⟩
  · rintro ⟨v, hv, g, hg, rfl⟩
    exact ⟨_, mem_wHat.mpr ⟨v, hv, rfl⟩, _, mem_aHat.mpr ⟨g, hg, rfl⟩, rfl⟩

theorem map_projG_wHat_sup_aHat {W : Submodule (ZMod 2) V} {A : Subgroup (LGL 2 V)}
    (hA : A ≤ G) : (wHat G W ⊔ aHat G A).map (projG G) = A := by
  rw [Subgroup.map_sup, map_projG_wHat, map_projG_aHat hA, bot_sup_eq]

private theorem inl_mul_inr_mul_inl_inv (u : V) (a : G) :
    (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G) * SemidirectProduct.inr a *
        (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)⁻¹ =
      SemidirectProduct.inl (Multiplicative.ofAdd (u - (a : LGL 2 V) u)) *
        SemidirectProduct.inr a := by
  have h := inr_mul_inl_mul_inr_inv a (-u)
  have h2 : (SemidirectProduct.inr a : VG G) *
      SemidirectProduct.inl (Multiplicative.ofAdd (-u)) =
      SemidirectProduct.inl (Multiplicative.ofAdd ((a : LGL 2 V) (-u))) *
        SemidirectProduct.inr a := by
    rw [← h]; group
  rw [← map_inv SemidirectProduct.inl, mul_assoc, ← ofAdd_neg, h2, ← mul_assoc,
    ← map_mul SemidirectProduct.inl, ← ofAdd_add, map_neg, ← sub_eq_add_neg]

theorem vHat_le_normalizer_wHat_sup_aHat {W : Submodule (ZMod 2) V} {A : Subgroup (LGL 2 V)}
    (hcomm : commSub A ≤ W) :
    vHat G ≤ Subgroup.normalizer ((wHat G W ⊔ aHat G A : Subgroup (VG G)) : Set (VG G)) := by
  have key : ∀ u : V, ∀ y ∈ wHat G W ⊔ aHat G A,
      (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G) * y *
        (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)⁻¹ ∈ wHat G W ⊔ aHat G A := by
    intro u y hy
    have hle : wHat G W ⊔ aHat G A ≤ (wHat G W ⊔ aHat G A).comap
        (MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro y hy
        obtain ⟨w, hw, rfl⟩ := mem_wHat.mp hy
        rw [Subgroup.mem_comap]
        change (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G) *
          SemidirectProduct.inl (Multiplicative.ofAdd w) *
            (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)⁻¹ ∈ _
        have : (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G) *
            SemidirectProduct.inl (Multiplicative.ofAdd w) *
              (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)⁻¹ =
            SemidirectProduct.inl (Multiplicative.ofAdd w) := by
          rw [← map_mul SemidirectProduct.inl, ← map_inv SemidirectProduct.inl,
            ← map_mul SemidirectProduct.inl, mul_comm, inv_mul_cancel_left]
        rw [this]
        exact Subgroup.mem_sup_left (mem_wHat.mpr ⟨w, hw, rfl⟩)
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hy
        rw [Subgroup.mem_comap]
        change (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G) *
          SemidirectProduct.inr g *
            (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)⁻¹ ∈ _
        rw [inl_mul_inr_mul_inl_inv]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_wHat.mpr ⟨_, ?_, rfl⟩))
          (Subgroup.mem_sup_right (mem_aHat.mpr ⟨g, hg, rfl⟩))
        have h1 : (g : LGL 2 V) u - u ∈ commSub A := Submodule.subset_span ⟨g, hg, u, rfl⟩
        have h2 := hcomm (Submodule.neg_mem _ h1)
        simpa using h2
    exact hle hy
  intro x hx
  obtain ⟨u, -, rfl⟩ := mem_wHat.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact key u y hy
  · intro hy
    have h := key (-u) _ hy
    have e : (SemidirectProduct.inl (Multiplicative.ofAdd (-u)) : VG G) *
        ((SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G) * y *
          (SemidirectProduct.inl (Multiplicative.ofAdd u) : VG G)⁻¹) *
        (SemidirectProduct.inl (Multiplicative.ofAdd (-u)) : VG G)⁻¹ = y := by
      rw [ofAdd_neg, map_inv, inv_inv]
      group
    rwa [e] at h

theorem isElemAbelian_wHat_sup_aHat {W : Submodule (ZMod 2) V} {A : Subgroup (LGL 2 V)}
    (hAab : IsElemAbelian 2 A) (hfix : W ≤ fixSub A) :
    IsElemAbelian 2 (wHat G W ⊔ aHat G A) := by
  refine IsElemAbelian.sup_of_commute (isElemAbelian_wHat W) (isElemAbelian_aHat hAab) ?_
  intro a ha b hb
  obtain ⟨v, hv, rfl⟩ := mem_wHat.mp ha
  obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hb
  have h := inr_mul_inl_mul_inr_inv g v
  have hgv : (g : LGL 2 V) v = v := hfix hv g hg
  rw [hgv] at h
  calc (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) * SemidirectProduct.inr g
      = (SemidirectProduct.inr g * SemidirectProduct.inl (Multiplicative.ofAdd v) *
          (SemidirectProduct.inr g)⁻¹) * SemidirectProduct.inr g := by rw [h]
    _ = _ := by group

theorem two_lt_card_wHat_sup_aHat {W : Submodule (ZMod 2) V} {A : Subgroup (LGL 2 V)}
    (hA : A ≤ G) (hW : W ≠ ⊥) (hA1 : A ≠ ⊥) :
    2 < Nat.card (wHat G W ⊔ aHat G A : Subgroup (VG G)) := by
  have hlt : wHat G W < wHat G W ⊔ aHat G A := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have hx : (SemidirectProduct.inr (⟨a, hA haA⟩ : G) : VG G) ∈
        wHat G W ⊔ aHat G A :=
      Subgroup.mem_sup_right (mem_aHat.mpr ⟨⟨a, hA haA⟩, haA, rfl⟩)
    rw [← h] at hx
    obtain ⟨v, -, hv⟩ := mem_wHat.mp hx
    have := congrArg (projG G) hv
    simp [projG_inr, projG_inl] at this
    exact ha1 (Subtype.ext this)
  have h1 : 1 < Nat.card (wHat G W) :=
    (wHat G W).one_lt_card_iff_ne_bot.mpr (fun h => hW (wHat_eq_bot_iff.mp h))
  have h2 : Nat.card (wHat G W) < Nat.card (wHat G W ⊔ aHat G A : Subgroup (VG G)) :=
    Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hlt.le
  rw [hk] at h2 ⊢
  rcases k with _ | _ | k
  · simp at h2
  · simp at h2
  · nlinarith

private theorem map_conj_wHat (W : Submodule (ZMod 2) V) (g : G) :
    (wHat G W).map (MulAut.conj (SemidirectProduct.inr g : VG G)).toMonoidHom =
      wHat G (conjSub (g : LGL 2 V) W) := by
  ext x
  rw [Subgroup.mem_map, mem_wHat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, hv, rfl⟩ := mem_wHat.mp hy
    refine ⟨(g : LGL 2 V) v, apply_mem_conjSub hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact inr_mul_inl_mul_inr_inv g v
  · rintro ⟨u, hu, rfl⟩
    have hu' := mem_conjSub.mp hu
    refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd ((g : LGL 2 V).symm u)),
      mem_wHat.mpr ⟨_, hu', rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [inr_mul_inl_mul_inr_inv]
    simp

private theorem map_conj_aHat (A : Subgroup (LGL 2 V)) (g : G) :
    (aHat G A).map (MulAut.conj (SemidirectProduct.inr g : VG G)).toMonoidHom =
      aHat G (cj (g : LGL 2 V) A) := by
  ext x
  rw [Subgroup.mem_map, mem_aHat]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := mem_aHat.mp hy
    refine ⟨g * h * g⁻¹, ?_, ?_⟩
    · exact ⟨(h : LGL 2 V), hh, by simp [MulAut.conj_apply]⟩
    · simp [MulAut.conj_apply]
  · rintro ⟨h, ⟨a, ha, hah⟩, rfl⟩
    refine ⟨SemidirectProduct.inr (g⁻¹ * h * g), mem_aHat.mpr ⟨g⁻¹ * h * g, ?_, rfl⟩, ?_⟩
    · have : ((g⁻¹ * h * g : G) : LGL 2 V) = a := by
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hah
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hah]
        simp [mul_assoc]
      rw [this]; exact ha
    · simp [MulAut.conj_apply, mul_assoc]

theorem conjSubgroup_wHat_sup_aHat_inr_inv (W : Submodule (ZMod 2) V) (A : Subgroup (LGL 2 V))
    (g : G) :
    conjSubgroup (wHat G W ⊔ aHat G A) (SemidirectProduct.inr g⁻¹ : VG G) =
      wHat G (conjSub (g : LGL 2 V) W) ⊔ aHat G (cj (g : LGL 2 V) A) := by
  have key : conjSubgroup (wHat G W ⊔ aHat G A) (SemidirectProduct.inr g⁻¹ : VG G) =
      (wHat G W ⊔ aHat G A).map (MulAut.conj (SemidirectProduct.inr g : VG G)).toMonoidHom := by
    unfold conjSubgroup
    rw [← map_inv SemidirectProduct.inr g⁻¹, inv_inv]
  rw [key, Subgroup.map_sup, map_conj_wHat, map_conj_aHat]

theorem exists_conjSubgroup_eq_inr {U : Subgroup (VG G)}
    (hU : vHat G ≤ Subgroup.normalizer (U : Set (VG G))) (y : VG G) :
    ∃ r : G, conjSubgroup U y = conjSubgroup U (SemidirectProduct.inr r : VG G) := by
  obtain ⟨v, r, rfl⟩ := exists_eq_inl_mul_inr y
  refine ⟨r, ?_⟩
  have hv : conjSubgroup U (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG G) = U :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hU (mem_wHat.mpr ⟨v, Submodule.mem_top, rfl⟩))
  rw [← conjSubgroup_conjSubgroup, hv]

end CFSG.LocalAnalysis.WeakClosure81
