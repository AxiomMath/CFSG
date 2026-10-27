module

public import CFSG.Quasithin.Background.SimsG46Split
import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Case3

@[expose] def DicksonInvol (n : ℕ) (F : Type) [Field F] : Prop :=
  ∀ T : Set (Matrix.SpecialLinearGroup (Fin 2) F), (∀ t ∈ T, t * t = 1) →
    (∃ s ∈ T, ∃ t ∈ T, s * t ≠ t * s) →
    ((∃ k : ℕ, k ∣ n ∧ Nonempty (↥(Subgroup.closure T) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∨
      ∃ m : ℕ, (m ∣ 2 ^ n + 1 ∨ m ∣ 2 ^ n - 1) ∧
        Nonempty (↥(Subgroup.closure T) ≃* DihedralGroup m)) ∧
    Subgroup.normalizer (Subgroup.closure T : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =
      Subgroup.closure T

section Line

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V)

@[expose] def spStab (X : Submodule F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | g ∈ spGroup B ∧ ∀ x, x ∈ X ↔ g x ∈ X}
  mul_mem' {g h} hg hh :=
    ⟨(spGroup B).mul_mem hg.1 hh.1, fun x => (hh.2 x).trans (hg.2 (h x))⟩
  one_mem' := ⟨(spGroup B).one_mem, fun _ => Iff.rfl⟩
  inv_mem' {g} hg := ⟨(spGroup B).inv_mem hg.1, fun x => by
    rw [hg.2 (g⁻¹ x), mul_inv_apply]⟩

theorem mem_spStab {X : Submodule F V} {g : V ≃ₗ[F] V} :
    g ∈ spStab B X ↔ g ∈ spGroup B ∧ ∀ x, x ∈ X ↔ g x ∈ X :=
  Iff.rfl

theorem spStab_sp {X : Submodule F V} {g : V ≃ₗ[F] V} (hg : g ∈ spStab B X) : g ∈ spGroup B :=
  hg.1

theorem spStab_mem {X : Submodule F V} {g : V ≃ₗ[F] V} (hg : g ∈ spStab B X) {x : V}
    (hx : x ∈ X) : g x ∈ X :=
  (hg.2 x).mp hx

theorem mem_spStab_of_fix {g : V ≃ₗ[F] V} (hg : g ∈ spGroup B) {Y : Submodule F V}
    (hY : ∀ y ∈ Y, g y = y) : g ∈ spStab B (B.orthogonal Y) := by
  refine ⟨hg, fun x => ⟨mem_orth_of_fix B hg hY, fun hx => ?_⟩⟩
  have hY' : ∀ y ∈ Y, g⁻¹ y = y :=
    mem_fixGroup.mp ((fixGroup Y).inv_mem (mem_fixGroup.mpr hY))
  have h1 := mem_orth_of_fix B ((spGroup B).inv_mem hg) hY' hx
  rwa [inv_mul_apply] at h1

theorem transvFix_le_spStab {G₀ : Subgroup (V ≃ₗ[F] V)} (hSp : G₀ ≤ spGroup B)
    (Y : Submodule F V) : transvFix G₀ Y ≤ spStab B (B.orthogonal Y) :=
  (Subgroup.closure_le _).mpr fun _ hd => mem_spStab_of_fix B (hSp hd.1.1) hd.2

structure IsLineBasis (X : Submodule F V) (e f : V) : Prop where
  mem_e : e ∈ X
  mem_f : f ∈ X
  pair : B e f = 1
  expand : ∀ x ∈ X, x = B x f • e + B e x • f

theorem exists_lineBasis (halt : ∀ x, B x x = 0) {X : Submodule F V} (hX : IsNondegLine B X) :
    ∃ e f : V, IsLineBasis B X e f := by
  haveI : FiniteDimensional F X := Module.finite_of_finrank_pos (by rw [hX.1]; norm_num)
  have hne : X ≠ ⊥ := by
    intro h0
    have h2 := hX.1
    rw [h0, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f', hf', hef'⟩ : ∃ f' ∈ X, B e f' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (hX.2 e he hcon)
  obtain ⟨f, hfdef⟩ : ∃ f : V, f = (B e f')⁻¹ • f' := ⟨_, rfl⟩
  have hef : B e f = 1 := by rw [hfdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hef']
  have hfX : f ∈ X := by
    rw [hfdef]
    exact X.smul_mem _ hf'
  have huw : B e f ≠ 0 := by
    rw [hef]
    exact one_ne_zero
  have hsup : F ∙ e ⊔ F ∙ f = X := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le ?_ ?_) ?_
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr he
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hfX
    · rw [(SimsG45.nondegLine_sup B halt he0 huw).1, hX.1]
  refine ⟨e, f, he, hfX, hef, fun x hx => ?_⟩
  rw [← hsup] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [halt, hef]

@[expose] def lineMat (e f : V) (g : V ≃ₗ[F] V) : Matrix (Fin 2) (Fin 2) F :=
  !![B (g e) f, B (g f) f; B e (g e), B e (g f)]

variable {B}

theorem IsLineBasis.map_expand {X : Submodule F V} {e f : V} (hL : IsLineBasis B X e f)
    (g : V ≃ₗ[F] V) {x : V} (hx : x ∈ X) : g x = B x f • g e + B e x • g f := by
  have h1 := congrArg g (hL.expand x hx)
  rwa [map_add, map_smul, map_smul] at h1

theorem lineMat_one {X : Submodule F V} {e f : V} (hL : IsLineBasis B X e f)
    (halt : ∀ x, B x x = 0) : lineMat B e f 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineMat, hL.pair, halt]

theorem lineMat_mul {X : Submodule F V} {e f : V} (hL : IsLineBasis B X e f)
    (g : V ≃ₗ[F] V) {h : V ≃ₗ[F] V} (he : h e ∈ X) (hf : h f ∈ X) :
    lineMat B e f (g * h) = lineMat B e f g * lineMat B e f h := by
  have k1 := hL.map_expand g he
  have k2 := hL.map_expand g hf
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineMat, Matrix.mul_apply, Fin.sum_univ_two, k1, k2] <;> ring

theorem lineMat_det {X : Submodule F V} {e f : V} (hL : IsLineBasis B X e f)
    (halt : ∀ x, B x x = 0) {g : V ≃ₗ[F] V} (hg : g ∈ spGroup B) (he : g e ∈ X)
    (hf : g f ∈ X) : (lineMat B e f g).det = 1 := by
  have hfe : B f e = -1 := by rw [SimsG45.bilin_skew B halt f e, hL.pair]
  have h1 : B (g e) (g f) = 1 := by rw [sp_apply B hg, hL.pair]
  rw [hL.expand _ he, hL.expand _ hf] at h1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
    hL.pair, hfe] at h1
  rw [lineMat, Matrix.det_fin_two_of]
  linear_combination h1

theorem eqOn_of_lineMat_eq {X : Submodule F V} {e f : V} (hL : IsLineBasis B X e f)
    {g h : V ≃ₗ[F] V} (hge : g e ∈ X) (hgf : g f ∈ X) (hhe : h e ∈ X) (hhf : h f ∈ X)
    (hgh : lineMat B e f g = lineMat B e f h) : ∀ x ∈ X, g x = h x := by
  have h00 : B (g e) f = B (h e) f := by simpa [lineMat] using congrFun (congrFun hgh 0) 0
  have h01 : B (g f) f = B (h f) f := by simpa [lineMat] using congrFun (congrFun hgh 0) 1
  have h10 : B e (g e) = B e (h e) := by simpa [lineMat] using congrFun (congrFun hgh 1) 0
  have h11 : B e (g f) = B e (h f) := by simpa [lineMat] using congrFun (congrFun hgh 1) 1
  have he : g e = h e := by rw [hL.expand _ hge, hL.expand _ hhe, h00, h10]
  have hf : g f = h f := by rw [hL.expand _ hgf, hL.expand _ hhf, h01, h11]
  intro x hx
  rw [hL.map_expand g hx, hL.map_expand h hx, he, hf]

@[expose] def lineHom (halt : ∀ x, B x x = 0) {X : Submodule F V} {e f : V}
    (hL : IsLineBasis B X e f) : ↥(spStab B X) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨lineMat B e f g, lineMat_det hL halt (spStab_sp B g.2)
    (spStab_mem B g.2 hL.mem_e) (spStab_mem B g.2 hL.mem_f)⟩
  map_one' := Subtype.ext (lineMat_one hL halt)
  map_mul' g h := Subtype.ext (lineMat_mul hL g (spStab_mem B h.2 hL.mem_e)
    (spStab_mem B h.2 hL.mem_f))

end Line

section Factor

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
variable {B : LinearMap.BilinForm F V} {G₀ : Subgroup (V ≃ₗ[F] V)}

theorem line_main [CharP F 2] (n : ℕ) (hSL2 : DicksonInvol n F) (halt : ∀ x, B x x = 0)
    (hSp : G₀ ≤ spGroup B) {X Y : Submodule F V} {e f : V} (hL : IsLineBasis B X e f)
    (hYX : B.orthogonal Y = X) (hc : X ⊔ Y = ⊤)
    (hpair : ∃ a ∈ transvSet G₀, ∃ b ∈ transvSet G₀,
      (∀ y ∈ Y, a y = y) ∧ (∀ y ∈ Y, b y = y) ∧ a * b ≠ b * a) :
    G41Factor n (transvFix G₀ Y) ∧
      ∀ g ∈ spStab B X, g ∈ Subgroup.normalizer (transvFix G₀ Y : Set (V ≃ₗ[F] V)) →
        ∃ x ∈ transvFix G₀ Y, ∀ v ∈ X, x v = g v := by
  let S := spStab B X
  let D' : Set ↥S := {s | (s : V ≃ₗ[F] V) ∈ transvSet G₀ ∧ ∀ y ∈ Y, (s : V ≃ₗ[F] V) y = y}
  let K : Subgroup ↥S := Subgroup.closure D'
  have hDS : ∀ d ∈ transvSet G₀, (∀ y ∈ Y, d y = y) → d ∈ S := fun d hd hdY => by
    show d ∈ spStab B X
    rw [← hYX]
    exact mem_spStab_of_fix B (hSp hd.1) hdY
  have hK : K.map S.subtype = transvFix G₀ Y := by
    rw [MonoidHom.map_closure]
    unfold transvFix
    congr 1
    ext d
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hd
      exact ⟨⟨d, hDS d hd.1 hd.2⟩, hd, rfl⟩
  have hmemK : ∀ k : ↥S, k ∈ K ↔ (k : V ≃ₗ[F] V) ∈ transvFix G₀ Y := fun k => by
    rw [← hK]
    exact (Subgroup.mem_map_iff_mem S.subtype_injective).symm
  let ρ := lineHom halt hL
  let T : Set (Matrix.SpecialLinearGroup (Fin 2) F) := ρ '' D'
  have hT : Subgroup.closure T = K.map ρ := (MonoidHom.map_closure ρ D').symm
  have hinj : Function.Injective (ρ.domRestrict K) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkX : ∀ x ∈ X, (k.1 : V ≃ₗ[F] V) x = (1 : V ≃ₗ[F] V) x := by
      refine eqOn_of_lineMat_eq hL (spStab_mem B k.1.2 hL.mem_e) (spStab_mem B k.1.2 hL.mem_f)
        hL.mem_e hL.mem_f ?_
      rw [lineMat_one hL halt]
      exact congrArg Subtype.val hk
    have hkY := mem_fixGroup.mp (transvFix_le_fixGroup G₀ Y ((hmemK k.1).mp k.2))
    exact Subtype.ext (Subtype.ext (ext_of_sup hc hkX hkY))
  have hiso : Nonempty (↥(transvFix G₀ Y) ≃* ↥(Subgroup.closure T)) :=
    ⟨((Subgroup.equivMapOfInjective K S.subtype S.subtype_injective).trans
      (MulEquiv.subgroupCongr hK)).symm.trans ((MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr ((MonoidHom.domRestrict_range K ρ).trans hT.symm)))⟩
  have hT1 : ∀ t ∈ T, t * t = 1 := by
    rintro t ⟨s, hs, rfl⟩
    rw [← map_mul]
    have hss : s * s = 1 := Subtype.ext (transv_mul_self _ hs.1.2)
    rw [hss, map_one]
  obtain ⟨a, ha, b, hb, haY, hbY, hab⟩ := hpair
  have haS : a ∈ S := hDS a ha haY
  have hbS : b ∈ S := hDS b hb hbY
  have haK : (⟨a, haS⟩ : ↥S) ∈ K := Subgroup.subset_closure ⟨ha, haY⟩
  have hbK : (⟨b, hbS⟩ : ↥S) ∈ K := Subgroup.subset_closure ⟨hb, hbY⟩
  have hT2 : ∃ s ∈ T, ∃ t ∈ T, s * t ≠ t * s := by
    refine ⟨ρ ⟨a, haS⟩, ⟨_, ⟨ha, haY⟩, rfl⟩, ρ ⟨b, hbS⟩, ⟨_, ⟨hb, hbY⟩, rfl⟩, fun hst => hab ?_⟩
    rw [← map_mul, ← map_mul] at hst
    have h1 : (⟨_, K.mul_mem haK hbK⟩ : ↥K) = ⟨_, K.mul_mem hbK haK⟩ := hinj hst
    exact congrArg (fun k : ↥K => ((k : ↥S) : V ≃ₗ[F] V)) h1
  obtain ⟨hfac, hnorm⟩ := hSL2 T hT1 hT2
  obtain ⟨φ⟩ := hiso
  refine ⟨?_, fun g hgS hgN => ?_⟩
  · rcases hfac with ⟨k, hk, ⟨ψ⟩⟩ | ⟨m, hm, ⟨ψ⟩⟩
    · exact Or.inl ⟨k, hk, ⟨φ.trans ψ⟩⟩
    · exact Or.inr ⟨m, hm, ⟨φ.trans ψ⟩⟩
  · have hgK : (⟨g, hgS⟩ : ↥S) ∈ Subgroup.normalizer (K : Set ↥S) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [hmemK, hmemK]
      exact Subgroup.mem_normalizer_iff.mp hgN k
    have h1 : ρ ⟨g, hgS⟩ ∈ Subgroup.normalizer ((K.map ρ : Subgroup _) : Set _) :=
      Subgroup.le_normalizer_map ρ ⟨_, hgK, rfl⟩
    rw [← hT, hnorm, hT] at h1
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp h1
    exact ⟨k, (hmemK k).mp hk, eqOn_of_lineMat_eq hL (spStab_mem B k.2 hL.mem_e)
      (spStab_mem B k.2 hL.mem_f) (spStab_mem B hgS hL.mem_e) (spStab_mem B hgS hL.mem_f)
      (congrArg Subtype.val hkg)⟩

theorem conj_mem_transvFix {g : V ≃ₗ[F] V} (hg : g ∈ G₀) {Y Y' : Submodule F V}
    (hY : ∀ y ∈ Y', g⁻¹ y ∈ Y) {x : V ≃ₗ[F] V} (hx : x ∈ transvFix G₀ Y) :
    g * x * g⁻¹ ∈ transvFix G₀ Y' := by
  have hsub : {d | d ∈ transvSet G₀ ∧ ∀ y ∈ Y, d y = y} ⊆
      ((transvFix G₀ Y').comap (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[F] V)) := by
    rintro d ⟨hd, hdY⟩
    refine Subgroup.subset_closure ⟨conj_mem_transvSet hg hd, fun y hy => ?_⟩
    change g (d (g⁻¹ y)) = y
    rw [hdY _ (hY y hy), mul_inv_apply]
  exact ((Subgroup.closure_le _).mpr hsub) hx

theorem mem_normalizer_transvFix {g : V ≃ₗ[F] V} (hg : g ∈ G₀) {Y : Submodule F V}
    (hY : Y.map (g : V →ₗ[F] V) = Y) :
    g ∈ Subgroup.normalizer (transvFix G₀ Y : Set (V ≃ₗ[F] V)) := by
  have hY' := (map_eq_iff g Y Y).mp hY
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_transvFix hg fun y hy => by
      rw [hY' (g⁻¹ y), mul_inv_apply]
      exact hy
  · intro hx
    have h1 := conj_mem_transvFix (G₀.inv_mem hg) (fun y hy => by
      rw [inv_inv]
      exact (hY' y).mp hy) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h1

variable {V₁ V₂ : Submodule F V}

theorem IsSplit.line_facts [CharP F 2] (h : IsSplit B G₀ V₁ V₂) (n : ℕ)
    (hSL2 : DicksonInvol n F) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hSp : G₀ ≤ spGroup B) :
    G41Factor n (transvFix G₀ V₂) ∧ ∀ g ∈ G₀, V₁.map (g : V →ₗ[F] V) = V₁ →
      ∃ x ∈ transvFix G₀ V₂, ∀ v ∈ V₁, x v = g v := by
  obtain ⟨e, f, hL⟩ := exists_lineBasis B halt h.line₁
  obtain ⟨hfac, hN⟩ := line_main n hSL2 halt hSp hL h.orth₂ h.compl.sup_eq_top
    (h.exists_pair halt hnd hSp)
  refine ⟨hfac, fun g hg hg₁ => hN g ⟨hSp hg, (map_eq_iff g V₁ V₁).mp hg₁⟩
    (mem_normalizer_transvFix hg ?_)⟩
  rw [← h.orth₁, map_orth B (hSp hg), hg₁]

theorem IsSplit.stab_decomp [CharP F 2] (h : IsSplit B G₀ V₁ V₂) (n : ℕ)
    (hSL2 : DicksonInvol n F) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hSp : G₀ ≤ spGroup B) {g : V ≃ₗ[F] V} (hg : g ∈ G₀)
    (hg₁ : V₁.map (g : V →ₗ[F] V) = V₁) :
    ∃ x₁ ∈ transvFix G₀ V₂, ∃ x₂ ∈ transvFix G₀ V₁, g = x₁ * x₂ := by
  have hg₂ : V₂.map (g : V →ₗ[F] V) = V₂ := by rw [← h.orth₁, map_orth B (hSp hg), hg₁]
  obtain ⟨x₁, hx₁, hx₁g⟩ := (h.line_facts n hSL2 halt hnd hSp).2 g hg hg₁
  obtain ⟨x₂, hx₂, hx₂g⟩ := (h.symm.line_facts n hSL2 halt hnd hSp).2 g hg hg₂
  have hx₁₂ := mem_fixGroup.mp (transvFix_le_fixGroup G₀ V₂ hx₁)
  have hx₂₁ := mem_fixGroup.mp (transvFix_le_fixGroup G₀ V₁ hx₂)
  refine ⟨x₁, hx₁, x₂, hx₂, ext_of_sup h.compl.sup_eq_top (fun v hv => ?_) (fun v hv => ?_)⟩
  · change g v = x₁ (x₂ v)
    rw [hx₂₁ v hv, hx₁g v hv]
  · change g v = x₁ (x₂ v)
    rw [hx₂g v hv, hx₁₂ _ (((map_eq_iff g V₂ V₂).mp hg₂ v).mp hv)]

theorem IsSplit.mem_transvGen [CharP F 2] (h : IsSplit B G₀ V₁ V₂) (n : ℕ)
    (hSL2 : DicksonInvol n F) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hSp : G₀ ≤ spGroup B) {g : V ≃ₗ[F] V} (hg : g ∈ G₀)
    (hg₁ : V₁.map (g : V →ₗ[F] V) = V₁) : g ∈ transvGen G₀ := by
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h.stab_decomp n hSL2 halt hnd hSp hg hg₁
  rw [h.transvGen_eq halt hnd hSp]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx₁) (Subgroup.mem_sup_right hx₂)

theorem IsSplit.exists_involution [CharP F 2] (h : IsSplit B G₀ V₁ V₂) (n : ℕ)
    (hSL2 : DicksonInvol n F) (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀) :
    ∃ t ∈ G₀, t * t = 1 ∧ V₁.map (t : V →ₗ[F] V) = V₂ ∧
      G₀ = transvGen G₀ ⊔ Subgroup.zpowers t := by
  obtain ⟨s, hs, hs₁⟩ := h.exists_swap halt hnd hdim hSp hirr
  have hs₂ : V₂.map (s : V →ₗ[F] V) = V₁ := by
    rw [← h.orth₁, map_orth B (hSp hs), hs₁, h.orth₂]
  have hs₁' := (map_eq_iff s V₁ V₂).mp hs₁
  have hs₂' := (map_eq_iff s V₂ V₁).mp hs₂
  have hss : V₁.map ((s * s : V ≃ₗ[F] V) : V →ₗ[F] V) = V₁ :=
    (map_eq_iff _ V₁ V₁).mpr fun x => (hs₁' x).trans (hs₂' (s x))
  obtain ⟨x₁, hx₁, x₂, hx₂, hsq⟩ := h.stab_decomp n hSL2 halt hnd hSp (G₀.mul_mem hs hs) hss
  have hc₁ : s * x₁ * s⁻¹ ∈ transvFix G₀ V₁ :=
    conj_mem_transvFix hs (fun y hy => (mem_map_iff s V₂ y).mp (by rw [hs₂]; exact hy)) hx₁
  have hc₂ : s * x₂ * s⁻¹ ∈ transvFix G₀ V₂ :=
    conj_mem_transvFix hs (fun y hy => (mem_map_iff s V₁ y).mp (by rw [hs₁]; exact hy)) hx₂
  have hcomm := h.commute hSp
  have hsc : s * x₂ * s⁻¹ * (s * x₁ * s⁻¹) = x₁ * x₂ := by
    rw [hcomm _ hc₂ _ hc₁]
    calc s * x₁ * s⁻¹ * (s * x₂ * s⁻¹) = s * (x₁ * x₂) * s⁻¹ := by group
      _ = s * (s * s) * s⁻¹ := by rw [hsq]
      _ = s * s := by group
      _ = x₁ * x₂ := hsq
  have e1 : s * x₁ * s⁻¹ = x₂ := by
    have h1 : x₁⁻¹ * (s * x₂ * s⁻¹) = x₂ * (s * x₁ * s⁻¹)⁻¹ := by
      calc x₁⁻¹ * (s * x₂ * s⁻¹)
          = x₁⁻¹ * (s * x₂ * s⁻¹ * (s * x₁ * s⁻¹)) * (s * x₁ * s⁻¹)⁻¹ := by group
        _ = x₁⁻¹ * (x₁ * x₂) * (s * x₁ * s⁻¹)⁻¹ := by rw [hsc]
        _ = x₂ * (s * x₁ * s⁻¹)⁻¹ := by group
    have hmem : x₂ * (s * x₁ * s⁻¹)⁻¹ ∈ transvFix G₀ V₂ ⊓ transvFix G₀ V₁ := by
      refine ⟨?_, (transvFix G₀ V₁).mul_mem hx₂ ((transvFix G₀ V₁).inv_mem hc₁)⟩
      rw [← h1]
      exact (transvFix G₀ V₂).mul_mem ((transvFix G₀ V₂).inv_mem hx₁) hc₂
    rw [h.inf_eq_bot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem.symm
  have hx₁G := transvFix_le G₀ V₂ hx₁
  have htG : s * x₁⁻¹ ∈ G₀ := G₀.mul_mem hs (G₀.inv_mem hx₁G)
  have hx₁S : x₁⁻¹ ∈ spStab B V₁ := by
    refine (spStab B V₁).inv_mem ?_
    rw [← h.orth₂]
    exact transvFix_le_spStab B hSp V₂ hx₁
  have htV : ∀ v, v ∈ V₁ ↔ (s * x₁⁻¹) v ∈ V₂ := fun v =>
    (((mem_spStab B).mp hx₁S).2 v).trans (hs₁' (x₁⁻¹ v))
  refine ⟨s * x₁⁻¹, htG, ?_, (map_eq_iff _ V₁ V₂).mpr htV, le_antisymm (fun g hg => ?_)
    (sup_le (transvGen_le G₀) (Subgroup.zpowers_le.mpr htG))⟩
  · calc s * x₁⁻¹ * (s * x₁⁻¹) = (s * x₁ * s⁻¹)⁻¹ * (s * s) * x₁⁻¹ := by group
      _ = x₂⁻¹ * (x₁ * x₂) * x₁⁻¹ := by rw [e1, hsq]
      _ = x₂⁻¹ * (x₂ * x₁) * x₁⁻¹ := by rw [hcomm x₁ hx₁ x₂ hx₂]
      _ = 1 := by group
  · rcases h.map_cases halt hnd hSp hg with ⟨hg₁, -⟩ | ⟨-, hg₂⟩
    · exact Subgroup.mem_sup_left (h.mem_transvGen n hSL2 halt hnd hSp hg hg₁)
    · have hgt : g * (s * x₁⁻¹) ∈ transvGen G₀ := by
        refine h.mem_transvGen n hSL2 halt hnd hSp (G₀.mul_mem hg htG)
          ((map_eq_iff _ V₁ V₁).mpr fun v => ?_)
        exact (htV v).trans ((map_eq_iff g V₂ V₁).mp hg₂ _)
      have h2 := (transvGen G₀ ⊔ Subgroup.zpowers (s * x₁⁻¹)).mul_mem
        (Subgroup.mem_sup_left hgt)
        (Subgroup.mem_sup_right ((Subgroup.zpowers (s * x₁⁻¹)).inv_mem
          (Subgroup.mem_zpowers (s * x₁⁻¹))))
      rwa [mul_inv_cancel_right] at h2

end Factor

end G46Case3

theorem case3_of_not_connected {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty)
    (hSL2 : ∀ T : Set (Matrix.SpecialLinearGroup (Fin 2) F), (∀ t ∈ T, t * t = 1) →
      (∃ s ∈ T, ∃ t ∈ T, s * t ≠ t * s) →
      ((∃ k : ℕ, k ∣ n ∧ Nonempty (↥(Subgroup.closure T) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∨
        ∃ m : ℕ, (m ∣ 2 ^ n + 1 ∨ m ∣ 2 ^ n - 1) ∧
          Nonempty (↥(Subgroup.closure T) ≃* DihedralGroup m)) ∧
      Subgroup.normalizer (Subgroup.closure T : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =
        Subgroup.closure T)
    (hnc : ¬ (advGraph G₀).Connected) : G41Case3 n B G₀ := by
  obtain ⟨V₁, V₂, h⟩ := G46Case3.exists_isSplit halt hnd hdim hSp hirr hD hnc
  exact ⟨V₁, V₂, h.line₁, h.orth₁.symm, h.compl, fun g hg => h.map_cases halt hnd hSp hg,
    h.exists_involution n hSL2 halt hnd hdim hSp hirr,
    ⟨h.transvGen_eq halt hnd hSp, h.inf_eq_bot, h.commute hSp⟩,
    (h.line_facts n hSL2 halt hnd hSp).1, (h.symm.line_facts n hSL2 halt hnd hSp).1⟩

end CFSG.Quasithin.SimsG4
