module

public import CFSG.Quasithin.Background.SimsG4Core
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Case3

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

section Basic

variable (B : LinearMap.BilinForm F V)

theorem sp_apply {g : V ≃ₗ[F] V} (hg : g ∈ spGroup B) (x y : V) : B (g x) (g y) = B x y :=
  hg x y

theorem orth_apply {Y : Submodule F V} {x : V} (hx : x ∈ B.orthogonal Y) {y : V} (hy : y ∈ Y) :
    B y x = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff.mp hx y hy

theorem mem_map_iff (g : V ≃ₗ[F] V) (X : Submodule F V) (x : V) :
    x ∈ X.map (g : V →ₗ[F] V) ↔ g⁻¹ x ∈ X :=
  Submodule.mem_map_equiv X

theorem map_eq_iff (g : V ≃ₗ[F] V) (X Y : Submodule F V) :
    X.map (g : V →ₗ[F] V) = Y ↔ ∀ x, x ∈ X ↔ g x ∈ Y := by
  constructor
  · rintro rfl x
    rw [mem_map_iff, inv_mul_apply]
  · intro h
    ext y
    rw [mem_map_iff, h, mul_inv_apply]

theorem ext_of_sup {V₁ V₂ : Submodule F V} (hc : V₁ ⊔ V₂ = ⊤) {g h : V ≃ₗ[F] V}
    (h₁ : ∀ x ∈ V₁, g x = h x) (h₂ : ∀ x ∈ V₂, g x = h x) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ V₁ ⊔ V₂ := by
    rw [hc]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, h₁ y hy, h₂ z hz]

@[expose] def fixGroup (X : Submodule F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x ∈ X, g x = x}
  mul_mem' {g h} hg hh x hx := by
    change g (h x) = x
    rw [hh x hx, hg x hx]
  one_mem' _ _ := rfl
  inv_mem' {g} hg x hx := by
    change g⁻¹ x = x
    calc g⁻¹ x = g⁻¹ (g x) := by rw [hg x hx]
      _ = x := inv_mul_apply g x

theorem mem_fixGroup {X : Submodule F V} {g : V ≃ₗ[F] V} :
    g ∈ fixGroup X ↔ ∀ x ∈ X, g x = x :=
  Iff.rfl

theorem transvFix_le_fixGroup (G₀ : Subgroup (V ≃ₗ[F] V)) (X : Submodule F V) :
    transvFix G₀ X ≤ fixGroup X :=
  (Subgroup.closure_le _).mpr fun _ hd => hd.2

theorem transvFix_le (G₀ : Subgroup (V ≃ₗ[F] V)) (X : Submodule F V) : transvFix G₀ X ≤ G₀ :=
  (Subgroup.closure_le _).mpr fun _ hd => hd.1.1

theorem mem_orth_of_fix {g : V ≃ₗ[F] V} (hg : g ∈ spGroup B) {Y : Submodule F V}
    (hY : ∀ y ∈ Y, g y = y) {x : V} (hx : x ∈ B.orthogonal Y) : g x ∈ B.orthogonal Y := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  calc B y (g x) = B (g y) (g x) := by rw [hY y hy]
    _ = B y x := sp_apply B hg y x
    _ = 0 := orth_apply B hx hy

theorem le_orth_comm (halt : ∀ x, B x x = 0) {X Y : Submodule F V} :
    X ≤ B.orthogonal Y ↔ Y ≤ B.orthogonal X := by
  constructor <;> intro h y hy <;> rw [LinearMap.BilinForm.mem_orthogonal_iff] <;> intro x hx <;>
    rw [SimsG45.bilin_skew B halt x y, orth_apply B (h hx) hy, neg_zero]

theorem isRefl_of_alt (halt : ∀ x, B x x = 0) : B.IsRefl := fun x y h => by
  rw [SimsG45.bilin_skew B halt y x, h, neg_zero]

theorem nondegenerate_of_alt (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) :
    B.Nondegenerate :=
  ⟨hnd, fun y hy => hnd y fun x => by rw [SimsG45.bilin_skew B halt y x, hy x, neg_zero]⟩

theorem isCompl_orth [FiniteDimensional F V] (halt : ∀ x, B x x = 0) {X : Submodule F V}
    (hX : IsNondegLine B X) : IsCompl X (B.orthogonal X) := by
  rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (isRefl_of_alt B halt),
    Submodule.disjoint_def]
  intro x hx hx'
  refine hX.2 x hx fun w hw => ?_
  rw [SimsG45.bilin_skew B halt x w, orth_apply B hx' hw, neg_zero]

theorem map_orth {g : V ≃ₗ[F] V} (hg : g ∈ spGroup B) (X : Submodule F V) :
    (B.orthogonal X).map (g : V →ₗ[F] V) = B.orthogonal (X.map (g : V →ₗ[F] V)) := by
  ext y
  rw [mem_map_iff, LinearMap.BilinForm.mem_orthogonal_iff,
    LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h n hn
    rw [mem_map_iff] at hn
    have h1 := h _ hn
    rwa [← sp_apply B hg, mul_inv_apply, mul_inv_apply] at h1
  · intro h n hn
    have h1 := h (g n) (by rw [mem_map_iff, inv_mul_apply]; exact hn)
    rwa [← sp_apply B hg n (g⁻¹ y), mul_inv_apply]

theorem commSpace_conj (g d : V ≃ₗ[F] V) :
    commSpace (g * d * g⁻¹) = (commSpace d).map (g : V →ₗ[F] V) := by
  have hkey : ((g * d * g⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) - LinearMap.id
      = ((g : V →ₗ[F] V) ∘ₗ ((d : V →ₗ[F] V) - LinearMap.id)) ∘ₗ
          ((g⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearEquiv.mul_apply, map_sub, mul_inv_apply]
  unfold commSpace
  rw [hkey, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range (g⁻¹ : V ≃ₗ[F] V)),
    LinearMap.range_comp]

end Basic

section Transv

variable {B : LinearMap.BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}

theorem exists_form (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hSp : G₀ ≤ spGroup B) {d : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) :
    ∃ u : V, u ≠ 0 ∧ ∃ c : F, c ≠ 0 ∧ (∀ v, d v = v + (c * B v u) • u) ∧
      commSpace d = F ∙ u :=
  SimsG45.exists_transv_form B halt hnd d (hSp hd.1) hd.2.1

theorem fix_iff (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hSp : G₀ ≤ spGroup B) {d : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) (X : Submodule F V) :
    (∀ x ∈ X, d x = x) ↔ commSpace d ≤ B.orthogonal X := by
  obtain ⟨u, hu, c, hc, hdu, hcs⟩ := exists_form halt hnd hSp hd
  rw [hcs, Submodule.span_singleton_le_iff_mem, LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun x _ => ?_
  simp [hdu, hc, hu]

theorem commute_iff (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hSp : G₀ ≤ spGroup B) {d e : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) (he : e ∈ transvSet G₀) :
    d * e = e * d ↔ commSpace e ≤ B.orthogonal (commSpace d) := by
  obtain ⟨u, hu, c, hc, hdu, hcs⟩ := exists_form halt hnd hSp hd
  obtain ⟨w, -, c', hc', hew, hcs'⟩ := exists_form halt hnd hSp he
  rw [SimsG45.transv_commute_iff B halt hnd hu hc hc' hdu hew, hcs, hcs',
    Submodule.span_singleton_le_iff_mem, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h n hn
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hn
    rw [LinearMap.map_smul₂, h, smul_zero]
  · intro h
    exact h u (Submodule.mem_span_singleton_self u)

theorem isNondegLine_sup (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hSp : G₀ ≤ spGroup B) {d e : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) (he : e ∈ transvSet G₀)
    (hde : d * e ≠ e * d) : IsNondegLine B (commSpace d ⊔ commSpace e) := by
  obtain ⟨u, hu, c, hc, hdu, hcs⟩ := exists_form halt hnd hSp hd
  obtain ⟨w, -, c', hc', hew, hcs'⟩ := exists_form halt hnd hSp he
  have huw : B u w ≠ 0 := fun h =>
    hde ((SimsG45.transv_commute_iff B halt hnd hu hc hc' hdu hew).mpr h)
  rw [hcs, hcs']
  exact SimsG45.nondegLine_sup B halt hu huw

end Transv

section Split

variable {B : LinearMap.BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}

structure IsSplit (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V))
    (V₁ V₂ : Submodule F V) : Prop where
  line₁ : IsNondegLine B V₁
  line₂ : IsNondegLine B V₂
  orth₁ : B.orthogonal V₁ = V₂
  orth₂ : B.orthogonal V₂ = V₁
  compl : IsCompl V₁ V₂
  cover : ∀ d ∈ transvSet G₀, commSpace d ≤ V₁ ∨ commSpace d ≤ V₂
  pair₁ : ∃ a ∈ transvSet G₀, ∃ b ∈ transvSet G₀,
    commSpace a ≤ V₁ ∧ commSpace b ≤ V₁ ∧ a * b ≠ b * a
  pair₂ : ∃ a ∈ transvSet G₀, ∃ b ∈ transvSet G₀,
    commSpace a ≤ V₂ ∧ commSpace b ≤ V₂ ∧ a * b ≠ b * a

theorem IsSplit.symm {V₁ V₂ : Submodule F V} (h : IsSplit B G₀ V₁ V₂) : IsSplit B G₀ V₂ V₁ :=
  ⟨h.line₂, h.line₁, h.orth₂, h.orth₁, h.compl.symm, fun d hd => (h.cover d hd).symm,
    h.pair₂, h.pair₁⟩

theorem exists_isSplit [Finite F] [CharP F 2] (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4)
    (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀) (hD : (transvSet G₀).Nonempty)
    (hnc : ¬ (advGraph G₀).Connected) : ∃ V₁ V₂ : Submodule F V, IsSplit B G₀ V₁ V₂ := by
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨a, ha⟩ := hD
  let R : ↥(transvSet G₀) → Prop := fun d => (advGraph G₀).Reachable ⟨a, ha⟩ d
  have hadj : ∀ x y : ↥(transvSet G₀), (x : V ≃ₗ[F] V) * y ≠ y * x → (advGraph G₀).Adj x y :=
    fun x y hxy => (SimpleGraph.fromRel_adj _ x y).mpr ⟨fun h => hxy (by rw [h]), Or.inl hxy⟩
  have hcross : ∀ x y : ↥(transvSet G₀), R x → ¬ R y → (x : V ≃ₗ[F] V) * y = y * x := by
    intro x y hx hy
    by_contra hxy
    exact hy (hx.trans (hadj x y hxy).reachable)
  obtain ⟨z, hz⟩ : ∃ z, ¬ R z := by
    by_contra h
    push Not at h
    exact hnc ((advGraph G₀).connected_iff_exists_forall_reachable.mpr ⟨⟨a, ha⟩, h⟩)
  obtain ⟨b, hb, hba⟩ := advSet_nonempty hdim G₀ hirr ha
  obtain ⟨e, he, hez⟩ := advSet_nonempty hdim G₀ hirr z.2
  have hRa : R ⟨a, ha⟩ := SimpleGraph.Reachable.refl _
  have hRb : R ⟨b, hb⟩ := (hadj ⟨a, ha⟩ ⟨b, hb⟩ (Ne.symm hba)).reachable
  have hRe : ¬ R ⟨e, he⟩ := fun h => hz (h.trans (hadj ⟨e, he⟩ z hez).reachable)
  have hab : a * b ≠ b * a := Ne.symm hba
  have hze : (z : V ≃ₗ[F] V) * e ≠ e * z := Ne.symm hez
  have hl₁ := isNondegLine_sup halt hnd hSp ha hb hab
  have hl₂ := isNondegLine_sup halt hnd hSp z.2 he hze
  have hout : ∀ d : ↥(transvSet G₀), ¬ R d →
      commSpace (d : V ≃ₗ[F] V) ≤ B.orthogonal (commSpace a ⊔ commSpace b) := by
    intro d hd
    rw [le_orth_comm B halt]
    refine sup_le ?_ ?_
    · exact (commute_iff halt hnd hSp d.2 ha).mp (hcross ⟨a, ha⟩ d hRa hd).symm
    · exact (commute_iff halt hnd hSp d.2 hb).mp (hcross ⟨b, hb⟩ d hRb hd).symm
  have hle : commSpace (z : V ≃ₗ[F] V) ⊔ commSpace e ≤
      B.orthogonal (commSpace a ⊔ commSpace b) :=
    sup_le (hout z hz) (hout ⟨e, he⟩ hRe)
  have hfr : Module.finrank F (B.orthogonal (commSpace a ⊔ commSpace b)) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal (nondegenerate_of_alt B halt hnd), hdim, hl₁.1]
  have horth₁ : B.orthogonal (commSpace a ⊔ commSpace b) =
      commSpace (z : V ≃ₗ[F] V) ⊔ commSpace e :=
    (Submodule.eq_of_le_of_finrank_eq hle (by rw [hl₂.1, hfr])).symm
  have horth₂ : B.orthogonal (commSpace (z : V ≃ₗ[F] V) ⊔ commSpace e) =
      commSpace a ⊔ commSpace b := by
    rw [← horth₁, LinearMap.BilinForm.orthogonal_orthogonal (nondegenerate_of_alt B halt hnd)
      (isRefl_of_alt B halt)]
  refine ⟨_, _, ⟨hl₁, hl₂, horth₁, horth₂, horth₁ ▸ isCompl_orth B halt hl₁, ?_,
    ⟨a, ha, b, hb, le_sup_left, le_sup_right, hab⟩,
    ⟨z, z.2, e, he, le_sup_left, le_sup_right, hze⟩⟩⟩
  intro d hd
  by_cases hRd : R ⟨d, hd⟩
  · left
    rw [← horth₂, le_orth_comm B halt]
    refine sup_le ?_ ?_
    · exact (commute_iff halt hnd hSp hd z.2).mp (hcross ⟨d, hd⟩ z hRd hz)
    · exact (commute_iff halt hnd hSp hd he).mp (hcross ⟨d, hd⟩ ⟨e, he⟩ hRd hRe)
  · right
    rw [← horth₁]
    exact hout ⟨d, hd⟩ hRd

variable {V₁ V₂ : Submodule F V}

theorem IsSplit.fix_of_le (h : IsSplit B G₀ V₁ V₂) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hSp : G₀ ≤ spGroup B) {d : V ≃ₗ[F] V}
    (hd : d ∈ transvSet G₀) (h1 : commSpace d ≤ V₁) : ∀ x ∈ V₂, d x = x :=
  (fix_iff halt hnd hSp hd V₂).mpr (by rw [h.orth₂]; exact h1)

theorem IsSplit.exists_pair (h : IsSplit B G₀ V₁ V₂) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hSp : G₀ ≤ spGroup B) :
    ∃ a ∈ transvSet G₀, ∃ b ∈ transvSet G₀,
      (∀ y ∈ V₂, a y = y) ∧ (∀ y ∈ V₂, b y = y) ∧ a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, ha₁, hb₁, hab⟩ := h.pair₁
  exact ⟨a, ha, b, hb, h.fix_of_le halt hnd hSp ha ha₁, h.fix_of_le halt hnd hSp hb hb₁, hab⟩

theorem IsSplit.transvGen_eq (h : IsSplit B G₀ V₁ V₂) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hSp : G₀ ≤ spGroup B) :
    transvGen G₀ = transvFix G₀ V₂ ⊔ transvFix G₀ V₁ := by
  unfold transvGen transvFix
  rw [← Subgroup.closure_union]
  congr 1
  ext d
  constructor
  · intro hd
    rcases h.cover d hd with h1 | h1
    · exact Or.inl ⟨hd, h.fix_of_le halt hnd hSp hd h1⟩
    · exact Or.inr ⟨hd, h.symm.fix_of_le halt hnd hSp hd h1⟩
  · rintro (⟨hd, -⟩ | ⟨hd, -⟩) <;> exact hd

theorem IsSplit.eq_one (h : IsSplit B G₀ V₁ V₂) {g : V ≃ₗ[F] V} (h₁ : ∀ x ∈ V₁, g x = x)
    (h₂ : ∀ x ∈ V₂, g x = x) : g = 1 :=
  ext_of_sup h.compl.sup_eq_top h₁ h₂

theorem IsSplit.inf_eq_bot (h : IsSplit B G₀ V₁ V₂) :
    transvFix G₀ V₂ ⊓ transvFix G₀ V₁ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx₂, hx₁⟩
  rw [Subgroup.mem_bot]
  exact h.eq_one (transvFix_le_fixGroup G₀ V₁ hx₁) (transvFix_le_fixGroup G₀ V₂ hx₂)

theorem IsSplit.mem_of_transvFix (h : IsSplit B G₀ V₁ V₂) (hSp : G₀ ≤ spGroup B)
    {g : V ≃ₗ[F] V} (hg : g ∈ transvFix G₀ V₂) {x : V} (hx : x ∈ V₁) : g x ∈ V₁ := by
  rw [← h.orth₂] at hx ⊢
  exact mem_orth_of_fix B (hSp (transvFix_le G₀ V₂ hg)) (transvFix_le_fixGroup G₀ V₂ hg) hx

theorem IsSplit.commute (h : IsSplit B G₀ V₁ V₂) (hSp : G₀ ≤ spGroup B) :
    ∀ a ∈ transvFix G₀ V₂, ∀ b ∈ transvFix G₀ V₁, a * b = b * a := by
  intro a ha b hb
  have ha₂ := mem_fixGroup.mp (transvFix_le_fixGroup G₀ V₂ ha)
  have hb₁ := mem_fixGroup.mp (transvFix_le_fixGroup G₀ V₁ hb)
  refine ext_of_sup h.compl.sup_eq_top (fun x hx => ?_) (fun x hx => ?_)
  · change a (b x) = b (a x)
    rw [hb₁ x hx, hb₁ _ (h.mem_of_transvFix hSp ha hx)]
  · change a (b x) = b (a x)
    rw [ha₂ _ (h.symm.mem_of_transvFix hSp hb hx), ha₂ x hx]

theorem IsSplit.map_eq_or (h : IsSplit B G₀ V₁ V₂) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hSp : G₀ ≤ spGroup B) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) : V₁.map (g : V →ₗ[F] V) = V₁ ∨ V₁.map (g : V →ₗ[F] V) = V₂ := by
  obtain ⟨a, ha, b, hb, ha₁, hb₁, hab⟩ := h.pair₁
  haveI : FiniteDimensional F V₁ := Module.finite_of_finrank_pos (by rw [h.line₁.1]; norm_num)
  haveI : FiniteDimensional F V₂ := Module.finite_of_finrank_pos (by rw [h.line₂.1]; norm_num)
  have hV : commSpace a ⊔ commSpace b = V₁ :=
    Submodule.eq_of_le_of_finrank_eq (sup_le ha₁ hb₁)
      (by rw [(isNondegLine_sup halt hnd hSp ha hb hab).1, h.line₁.1])
  have ha' := conj_mem_transvSet hg ha
  have hb' := conj_mem_transvSet hg hb
  have hab' : g * a * g⁻¹ * (g * b * g⁻¹) ≠ g * b * g⁻¹ * (g * a * g⁻¹) := by
    intro h'
    apply hab
    have h'' : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ :=
      calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := h'
        _ = g * (b * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h'')
  have hmap : V₁.map (g : V →ₗ[F] V) = commSpace (g * a * g⁻¹) ⊔ commSpace (g * b * g⁻¹) := by
    rw [← hV, Submodule.map_sup, commSpace_conj, commSpace_conj]
  have hfr : Module.finrank F (V₁.map (g : V →ₗ[F] V)) = 2 := by
    rw [LinearEquiv.finrank_map_eq, h.line₁.1]
  rcases h.cover _ ha' with h1 | h1 <;> rcases h.cover _ hb' with h2 | h2
  · left
    exact Submodule.eq_of_le_of_finrank_eq (by rw [hmap]; exact sup_le h1 h2)
      (by rw [hfr, h.line₁.1])
  · refine absurd ((commute_iff halt hnd hSp ha' hb').mpr (h2.trans ?_)) hab'
    rw [← h.orth₁]
    exact LinearMap.BilinForm.orthogonal_le h1
  · refine absurd ((commute_iff halt hnd hSp ha' hb').mpr (h2.trans ?_)) hab'
    rw [← h.orth₂]
    exact LinearMap.BilinForm.orthogonal_le h1
  · right
    exact Submodule.eq_of_le_of_finrank_eq (by rw [hmap]; exact sup_le h1 h2)
      (by rw [hfr, h.line₂.1])

theorem IsSplit.map_cases (h : IsSplit B G₀ V₁ V₂) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hSp : G₀ ≤ spGroup B) {g : V ≃ₗ[F] V}
    (hg : g ∈ G₀) :
    (V₁.map (g : V →ₗ[F] V) = V₁ ∧ V₂.map (g : V →ₗ[F] V) = V₂) ∨
      (V₁.map (g : V →ₗ[F] V) = V₂ ∧ V₂.map (g : V →ₗ[F] V) = V₁) := by
  rcases h.map_eq_or halt hnd hSp hg with h1 | h1
  · exact Or.inl ⟨h1, by rw [← h.orth₁, map_orth B (hSp hg), h1]⟩
  · exact Or.inr ⟨h1, by rw [← h.orth₁, map_orth B (hSp hg), h1, h.orth₂]⟩

theorem IsSplit.exists_swap (h : IsSplit B G₀ V₁ V₂) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4)
    (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀) :
    ∃ s ∈ G₀, V₁.map (s : V →ₗ[F] V) = V₂ := by
  by_contra hcon
  push Not at hcon
  have hinv : ∀ g ∈ G₀, ∀ w ∈ V₁, g w ∈ V₁ := by
    intro g hg w hw
    rcases h.map_eq_or halt hnd hSp hg with h1 | h1
    · rw [← h1]
      exact Submodule.mem_map_of_mem hw
    · exact absurd h1 (hcon g hg)
  have h2 := h.line₁.1
  rcases hirr V₁ hinv with h0 | h0
  · rw [h0, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  · rw [h0, finrank_top, hdim] at h2
    exact absurd h2 (by norm_num)

end Split

end G46Case3

end CFSG.Quasithin.SimsG4
