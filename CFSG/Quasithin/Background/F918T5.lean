module

public import CFSG.Quasithin.Background.F918T1
public import CFSG.Quasithin.Background.F918T2
public import CFSG.Quasithin.Background.F918T3
public import CFSG.Quasithin.Background.F918T4
public import CFSG.Quasithin.Background.SmithB51LnAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

section Assembly

variable {X : Type} [CommGroup X]

@[expose] def conjAutByInv (Lb : Subgroup (MulAut X)) (t : MulAut X)
    (h1 : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb) (h2 : ∀ l ∈ Lb, t * l * t⁻¹ ∈ Lb) : ↥Lb ≃* ↥Lb where
  toFun l := ⟨t⁻¹ * l * t, h1 l l.2⟩
  invFun l := ⟨t * l * t⁻¹, h2 l l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def restrictAutEquiv (t : MulAut X) (V₁ : Subgroup X) : ↥V₁ ≃* ↥(V₁.map t.toMonoidHom) where
  toFun v := ⟨t v, Subgroup.mem_map_of_mem _ v.2⟩
  invFun w := ⟨t.symm w, Subgroup.mem_map_equiv.mp w.2⟩
  left_inv v := Subtype.ext (t.symm_apply_apply (v : X))
  right_inv w := Subtype.ext (t.apply_symm_apply (w : X))
  map_mul' a b := Subtype.ext (map_mul t (a : X) (b : X))

@[simp] theorem restrictAutEquiv_symm_apply_coe (t : MulAut X) (V₁ : Subgroup X) (w : ↥(V₁.map t.toMonoidHom)) :
    (((restrictAutEquiv t V₁).symm w : ↥V₁) : X) = t.symm (w : X) := rfl

@[simp] theorem restrictAutEquiv_apply_coe (t : MulAut X) (V₁ : Subgroup X) (v : ↥V₁) :
    (((restrictAutEquiv t V₁) v : ↥(V₁.map t.toMonoidHom)) : X) = t (v : X) := rfl

@[simp] theorem coe_resHomOn_apply {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} (hLV : Lb ≤ stabSub V₁)
    (l : ↥Lb) (v : ↥V₁) : (((resHomOn V₁ hLV l : MulAut ↥V₁) v : ↥V₁) : X) = (l : MulAut X) (v : X) :=
  rfl

theorem theta2_equivariant {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hLV : Lb ≤ stabSub V₁) (h1 : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb) (h2 : ∀ l ∈ Lb, t * l * t⁻¹ ∈ Lb)
    (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v))
    (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
    (hxw : x (w : X) ∈ V₁.map t.toMonoidHom) :
    ((restrictAutEquiv t V₁).symm.trans Θ) ⟨x (w : X), hxw⟩ =
      altMulAct (θ ((conjAutByInv Lb t h1 h2) ⟨x, hx⟩)) (((restrictAutEquiv t V₁).symm.trans Θ) w) := by
  have : (restrictAutEquiv t V₁).symm ⟨x (w : X), hxw⟩ =
      (resHomOn V₁ hLV ((conjAutByInv Lb t h1 h2) ⟨x, hx⟩) : MulAut ↥V₁) ((restrictAutEquiv t V₁).symm w) := by
    apply Subtype.ext
    simp only [restrictAutEquiv_symm_apply_coe, coe_resHomOn_apply, conjAutByInv, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MulAut.mul_apply, MulAut.inv_apply]
    rw [MulEquiv.apply_symm_apply]
  show Θ ((restrictAutEquiv t V₁).symm ⟨x (w : X), hxw⟩) = altMulAct _ (Θ ((restrictAutEquiv t V₁).symm w))
  rw [this, hΘ]

theorem agree_of_autSub_eq {Lb N : Subgroup (MulAut X)} {V₁ : Subgroup X}
    (hGL : autSub (Lb ⊔ N) V₁ = autSub Lb V₁) {n : MulAut X} (hn : n ∈ N) (hnV : n ∈ stabSub V₁) :
    ∃ l ∈ Lb, ∀ v ∈ V₁, n v = l v := by
  have hmem : resHom V₁ ⟨n, hnV⟩ ∈ autSub (Lb ⊔ N) V₁ :=
    mem_autSub.mpr ⟨⟨n, hnV⟩, (le_sup_right : N ≤ Lb ⊔ N) hn, rfl⟩
  rw [hGL] at hmem
  obtain ⟨g, hg, hgn⟩ := mem_autSub.mp hmem
  refine ⟨(g : MulAut X), hg, fun v hv => ?_⟩
  have := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨v, hv⟩ : ↥V₁) : X)) hgn
  exact this.symm

theorem conj_mem_stabSub_of_mem_stabSub_map {t a : MulAut X} {V₁ : Subgroup X}
    (ha : a ∈ stabSub (V₁.map t.toMonoidHom)) : t⁻¹ * a * t ∈ stabSub V₁ := by
  rw [mem_stabSub_iff_map_eq] at ha ⊢
  rw [map_mul_aut', map_mul_aut', ha, ← map_mul_aut', inv_mul_cancel]
  ext v
  simp

theorem agree_V₂_exists {Lb Tb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hGL : autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁ = autSub Lb V₁)
    (hTL : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb) (ht : t ∈ Tb) {a : MulAut X} (haT : a ∈ Tb)
    (haV₂ : a ∈ stabSub (V₁.map t.toMonoidHom)) :
    ∃ l ∈ Lb, ∀ w ∈ V₁.map t.toMonoidHom, a w = l w := by
  have hmem : t⁻¹ * a * t ∈ Tb ⊓ stabSub V₁ :=
    ⟨Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) haT) ht, conj_mem_stabSub_of_mem_stabSub_map haV₂⟩
  obtain ⟨l', hl', hagree⟩ := agree_of_autSub_eq hGL hmem hmem.2
  refine ⟨t * l' * t⁻¹, hTL t ht l' hl', ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have h := hagree v hv
  simp only [MulAut.mul_apply, MulAut.inv_apply] at h ⊢
  show a (t v) = t (l' (t.symm (t v)))
  rw [MulEquiv.symm_apply_apply, ← h]
  simp

theorem twisted_model {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hLV : Lb ≤ stabSub V₁) (h1 : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb) (h2 : ∀ l ∈ Lb, t * l * t⁻¹ ∈ Lb)
    (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5))
    (hθs : Function.Surjective θ)
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v)) :
    ∃ (θ₂ : ↥Lb →* ↥(StatedSL 5 (ZMod 2)))
      (Θ₂ : ↥(V₁.map t.toMonoidHom) ≃* Multiplicative ↥(altMat 5)),
      (∀ l, θ₂ l = θ ((conjAutByInv Lb t h1 h2) l)) ∧ Function.Surjective θ₂ ∧
      (∀ (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
        (hxw : x (w : X) ∈ V₁.map t.toMonoidHom),
        Θ₂ ⟨x (w : X), hxw⟩ = altMulAct (θ₂ ⟨x, hx⟩) (Θ₂ w)) ∧
      (∀ v : ↥V₁, Θ₂ (restrictAutEquiv t V₁ v) = Θ v) :=
  ⟨θ.comp (conjAutByInv Lb t h1 h2).toMonoidHom, (restrictAutEquiv t V₁).symm.trans Θ, fun _ => rfl,
    hθs.comp (conjAutByInv Lb t h1 h2).surjective,
    fun x hx w hxw => theta2_equivariant hLV h1 h2 θ Θ hΘ x hx w hxw,
    fun v => by
      show Θ ((restrictAutEquiv t V₁).symm ((restrictAutEquiv t V₁) v)) = Θ v
      rw [MulEquiv.symm_apply_apply]⟩

theorem mem_map_of_conj {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hLV : Lb ≤ stabSub V₁) (h1 : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb) {x : MulAut X} (hx : x ∈ Lb)
    {w : X} (hw : w ∈ V₁.map t.toMonoidHom) : x w ∈ V₁.map t.toMonoidHom := by
  obtain ⟨v, hv, rfl⟩ := hw
  refine ⟨(t⁻¹ * x * t) v, (hLV (h1 x hx) v).2 hv, ?_⟩
  simp [MulAut.mul_apply, MulAut.inv_apply]

theorem agree_on_V₂ [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hZ : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) (ht : t ∈ Tb) (hLV : Lb ≤ stabSub V₁)
    (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5))
    (hθs : Function.Surjective θ)
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v))
    {a l l'' : MulAut X} (ha : a ∈ Tb) (hl : l ∈ Lb) (hl'' : l'' ∈ Lb)
    (hagree : ∀ v ∈ V₁, a v = l v) (hagree2 : ∀ w ∈ V₁.map t.toMonoidHom, a w = l'' w) :
    ∀ w ∈ V₁.map t.toMonoidHom, a w = l w := by
  have h1 : ∀ x ∈ Lb, t⁻¹ * x * t ∈ Lb := fun x hx => by
    simpa using z35_conj_mem hZ hML (Tb.inv_mem ht) hx
  have h2 : ∀ x ∈ Lb, t * x * t⁻¹ ∈ Lb := fun x hx => z35_conj_mem hZ hML ht hx
  have hcomm := z35_centralizes hZ hML ha hl hagree
  have hLV₂ : ∀ x ∈ Lb, ∀ w ∈ V₁.map t.toMonoidHom, x w ∈ V₁.map t.toMonoidHom :=
    fun x hx w hw => mem_map_of_conj hLV h1 hx hw
  have hyL : l⁻¹ * l'' ∈ Lb := Lb.mul_mem (Lb.inv_mem hl) hl''
  have hy : ∀ u ∈ V₁.map t.toMonoidHom, (l⁻¹ * a) u = (l⁻¹ * l'') u := fun u hu => by
    simp only [MulAut.mul_apply]
    rw [hagree2 u hu]
  have hyc : ∀ x ∈ Lb, ∀ w ∈ V₁.map t.toMonoidHom, (l⁻¹ * l'') (x w) = x ((l⁻¹ * l'') w) := by
    intro x hx w hw
    rw [← hy _ (hLV₂ x hx w hw), ← hy w hw]
    have := congrArg (fun g : MulAut X => g w) (hcomm x hx)
    simpa [MulAut.mul_apply] using this
  obtain ⟨θ₂, Θ₂, hθ₂, hθ₂s, hequiv, -⟩ := twisted_model hLV h1 h2 θ Θ hθs hΘ
  have hcommS : ∀ δ B, altMulAct (θ₂ ⟨l⁻¹ * l'', hyL⟩) (altMulAct δ B) =
      altMulAct δ (altMulAct (θ₂ ⟨l⁻¹ * l'', hyL⟩) B) := by
    intro δ B
    obtain ⟨x, rfl⟩ := hθ₂s δ
    obtain ⟨w, rfl⟩ := Θ₂.surjective B
    have hxw := hLV₂ (x : MulAut X) x.2 (w : X) w.2
    have hyw := hLV₂ (l⁻¹ * l'') hyL (w : X) w.2
    have e1 := hequiv (x : MulAut X) x.2 w hxw
    have e2 := hequiv (l⁻¹ * l'') hyL w hyw
    have hxyw := hLV₂ (l⁻¹ * l'') hyL ((x : MulAut X) (w : X)) hxw
    have hyxw := hLV₂ (x : MulAut X) x.2 ((l⁻¹ * l'') (w : X)) hyw
    have e3 := hequiv (l⁻¹ * l'') hyL ⟨(x : MulAut X) (w : X), hxw⟩ hxyw
    have e4 := hequiv (x : MulAut X) x.2 ⟨(l⁻¹ * l'') (w : X), hyw⟩ hyxw
    have hxy : (⟨(l⁻¹ * l'') ((x : MulAut X) (w : X)), hxyw⟩ : ↥(V₁.map t.toMonoidHom)) =
        ⟨(x : MulAut X) ((l⁻¹ * l'') (w : X)), hyxw⟩ :=
      Subtype.ext (hyc x x.2 w w.2)
    rw [e1] at e3
    rw [e2] at e4
    exact e3.symm.trans ((congrArg Θ₂ hxy).trans e4)
  have hy1 : θ₂ ⟨l⁻¹ * l'', hyL⟩ = 1 := eq_one_of_altMulAct_comm hcommS
  intro w hw
  have hyw := hLV₂ (l⁻¹ * l'') hyL w hw
  have e2 := hequiv (l⁻¹ * l'') hyL ⟨w, hw⟩ hyw
  rw [hy1, altMulAct_one] at e2
  have hw1 : (⟨(l⁻¹ * l'') w, hyw⟩ : ↥(V₁.map t.toMonoidHom)) = ⟨w, hw⟩ := Θ₂.injective e2
  have hw2 : (l⁻¹ * l'') w = w := congrArg Subtype.val hw1
  rw [hagree2 w hw]
  have : l'' w = l w := by
    have h3 : l (l⁻¹ (l'' w)) = l w := by
      simpa [MulAut.mul_apply] using congrArg l hw2
    simpa using h3
  exact this

theorem model_theta_eq_one_iff {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} (hLV : Lb ≤ stabSub V₁)
    (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v))
    (l : ↥Lb) : θ l = 1 ↔ resHomOn V₁ hLV l = 1 := by
  constructor
  · intro h
    ext v
    have := hΘ l v
    rw [h, altMulAct_one] at this
    have h2 := Θ.injective this
    exact congrArg (fun u : ↥V₁ => (u : X)) h2
  · intro h
    apply altMulAct_faithful
    intro B
    obtain ⟨v, rfl⟩ := Θ.surjective B
    rw [← hΘ, h]
    rfl

theorem ker_theta_le [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X}
    (hZ : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) (hLV : Lb ≤ stabSub V₁)
    (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v))
    (θ₂ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (hθ₂s : Function.Surjective θ₂) (l : ↥Lb)
    (hl : θ l = 1) : θ₂ l = 1 := by
  have hl1 := (model_theta_eq_one_iff hLV θ Θ hΘ l).1 hl
  have hcen : ∀ x ∈ Lb, (l : MulAut X) * x = x * (l : MulAut X) :=
    z35_central_of_trivial hZ hML l.2 (fun v hv => by
      have := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨v, hv⟩ : ↥V₁) : X)) hl1
      simpa using this)
  apply center_statedSL5
  intro δ
  obtain ⟨x, rfl⟩ := hθ₂s δ
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcen x x.2)

@[expose] def altMulEquiv (p : ↥(StatedSL 5 (ZMod 2))) :
    Multiplicative ↥(altMat 5) ≃* Multiplicative ↥(altMat 5) where
  toFun := altMulAct p
  invFun := altMulAct p⁻¹
  left_inv B := by rw [← altMulAct_mul, inv_mul_cancel, altMulAct_one]
  right_inv B := by rw [← altMulAct_mul, mul_inv_cancel, altMulAct_one]
  map_mul' := altMulAct_mul_distrib p

theorem inner_case_false [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hZ : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) (ht : t ∈ Tb) (htV : t ∉ stabSub V₁)
    (hLV : Lb ≤ stabSub V₁)
    (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v))
    (θ₂ : ↥Lb →* ↥(StatedSL 5 (ZMod 2)))
    (Θ₂ : ↥(V₁.map t.toMonoidHom) ≃* Multiplicative ↥(altMat 5))
    (hequiv : ∀ (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
        (hxw : x (w : X) ∈ V₁.map t.toMonoidHom),
        Θ₂ ⟨x (w : X), hxw⟩ = altMulAct (θ₂ ⟨x, hx⟩) (Θ₂ w))
    (hΘ₂t : ∀ v : ↥V₁, Θ₂ (restrictAutEquiv t V₁ v) = Θ v)
    (α : ↥(StatedSL 5 (ZMod 2)) ≃* ↥(StatedSL 5 (ZMod 2))) (hα : ∀ l, α (θ l) = θ₂ l)
    (P : GL (Fin 5) (ZMod 2))
    (hP : ∀ g, mat (α g) = (P : Matrix (Fin 5) (Fin 5) (ZMod 2)) * mat g *
      ((P⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) : False := by
  classical
  set p : ↥(StatedSL 5 (ZMod 2)) := CFSG.Quasithin.B5.Ln.ofGL P with hp
  set G : ↥V₁ ≃* ↥V₁ := Θ.trans ((altMulEquiv p).trans Θ.symm) with hG
  have hΘG : ∀ v, Θ (G v) = altMulAct p (Θ v) := fun v => by
    simp [hG, altMulEquiv]
  have hmap1 : V₁.map (1 : MulAut X).toMonoidHom = V₁ := by
    ext v
    simp
  have key : ∀ (x : MulAut X) (hx : x ∈ Lb) (v v' : ↥V₁), x (v : X) = (v' : X) →
      t ((G v' : ↥V₁) : X) = x (t ((G v : ↥V₁) : X)) := by
    intro x hx v v' hxv
    have hv' : v' = (resHomOn V₁ hLV ⟨x, hx⟩ : MulAut ↥V₁) v := Subtype.ext hxv.symm
    have hxw : x ((restrictAutEquiv t V₁ (G v) : ↥(V₁.map t.toMonoidHom)) : X) ∈ V₁.map t.toMonoidHom :=
      mem_map_of_conj hLV (fun l hl => by
        simpa using z35_conj_mem hZ hML (Tb.inv_mem ht) hl) hx
        (restrictAutEquiv t V₁ (G v)).2
    have e1 := hequiv x hx (restrictAutEquiv t V₁ (G v)) hxw
    rw [hΘ₂t] at e1
    have e2 : Θ₂ (restrictAutEquiv t V₁ (G v')) = Θ₂ ⟨x ((restrictAutEquiv t V₁ (G v) : ↥(V₁.map t.toMonoidHom)) : X), hxw⟩ := by
      rw [e1, hΘ₂t, hΘG, hv', hΘ, hΘG, ← hα, ← altMulAct_inner α P hP (θ ⟨x, hx⟩) (Θ v)]
    exact congrArg (fun w : ↥(V₁.map t.toMonoidHom) => (w : X)) (Θ₂.injective e2)
  have hiso : XMod.Iso ↥Mb (V₁.map (1 : MulAut X).toMonoidHom) (V₁.map t.toMonoidHom) := by
    refine ⟨(MulEquiv.subgroupCongr hmap1).trans (G.trans (restrictAutEquiv t V₁)), ?_⟩
    intro a l l' hal
    have hx : (a : MulAut X) ∈ Lb := hML ▸ a.2
    have hal' : (a : MulAut X) (l : X) = (l' : X) := hal
    have hmem1 : ∀ m : ↥(V₁.map (1 : MulAut X).toMonoidHom), (m : X) ∈ V₁ := fun m => by
      obtain ⟨y, hy, hym⟩ := Subgroup.mem_map.mp m.2
      have : (y : X) = (m : X) := hym
      rwa [← this]
    have hlV : (l : X) ∈ V₁ := hmem1 l
    have hl'V : (l' : X) ∈ V₁ := hmem1 l'
    have hk := key (a : MulAut X) hx ⟨(l : X), hlV⟩ ⟨(l' : X), hl'V⟩ hal'
    exact hk.symm
  have heq := hZ.homog 1 Tb.one_mem t ht hiso
  rw [hmap1] at heq
  exact htV (mem_stabSub_iff_map_eq.mpr heq.symm)

theorem le_stabSub_map_of_conj {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    (hLV : Lb ≤ stabSub V₁) (h1 : ∀ l ∈ Lb, t⁻¹ * l * t ∈ Lb) :
    Lb ≤ stabSub (V₁.map t.toMonoidHom) := by
  intro x hx u
  constructor
  · intro hu
    have := mem_map_of_conj hLV h1 (Lb.inv_mem hx) hu
    simpa using this
  · exact fun hu => mem_map_of_conj hLV h1 hx hu

@[expose] def agreeSub (Lb A : Subgroup (MulAut X)) (V₁ : Subgroup X) (hLV : Lb ≤ stabSub V₁) :
    Subgroup ↥Lb where
  carrier := {l | ∃ a ∈ A, ∀ v ∈ V₁, a v = (l : MulAut X) v}
  one_mem' := ⟨1, A.one_mem, fun v _ => rfl⟩
  mul_mem' := by
    rintro l₁ l₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, fun v hv => ?_⟩
    have h2V : (l₂ : MulAut X) v ∈ V₁ := (hLV l₂.2 v).2 hv
    show a₁ (a₂ v) = (l₁ : MulAut X) ((l₂ : MulAut X) v)
    rw [h₂ v hv]
    exact h₁ _ h2V
  inv_mem' := by
    rintro l ⟨a, ha, h⟩
    refine ⟨a⁻¹, A.inv_mem ha, fun v hv => ?_⟩
    have hlv : (l : MulAut X)⁻¹ v ∈ V₁ := (hLV (Lb.inv_mem l.2) v).2 hv
    have h3 := h _ hlv
    have h4 : a ((l : MulAut X)⁻¹ v) = v := by
      rw [h3]
      simp
    show a⁻¹ v = (l : MulAut X)⁻¹ v
    calc a⁻¹ v = a⁻¹ (a ((l : MulAut X)⁻¹ v)) := by rw [h4]
      _ = (l : MulAut X)⁻¹ v := by simp

theorem card_map_le_of_ker_le {G H₁ H₂ : Type*} [Group G] [Group H₁] [Group H₂] [Finite H₂]
    (Q : Subgroup G) (f : G →* H₁) (g : G →* H₂) (h : g.ker ≤ f.ker) :
    Nat.card (Q.map f) ≤ Nat.card (Q.map g) := by
  have h1 := Subgroup.relIndex_ker Q f
  have h2 := Subgroup.relIndex_ker Q g
  have h3 := Subgroup.relIndex_dvd_of_le_left Q h
  rw [h1, h2] at h3
  exact Nat.le_of_dvd Nat.card_pos h3

omit [CommGroup X] in
theorem fixV_bot_eq_top_aut {V : Type*} [CommGroup V] : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
  ext v
  simp [mem_fixV, Subgroup.mem_bot]

theorem graph_case_false [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} {t : MulAut X}
    {A : Subgroup (MulAut X)} (hU : D35InspExtSq)
    (hZ : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) (ht : t ∈ Tb) (hLV : Lb ≤ stabSub V₁)
    (hGL : autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁ = autSub Lb V₁)
    (hAN : A ≤ Tb ⊓ stabSub V₁) (hAV₂ : A ≤ stabSub (V₁.map t.toMonoidHom))
    (hcard : Nat.card ↥V₁ = 2 ^ 10)
    (hoff₁ : IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub A V₁))
    (hoff₂ : IsFFStarOffender
      (autSub (Lb ⊔ (Tb ⊓ stabSub (V₁.map t.toMonoidHom))) (V₁.map t.toMonoidHom))
      (autSub A (V₁.map t.toMonoidHom)))
    (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5))
    (hθs : Function.Surjective θ)
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v))
    (θ₂ : ↥Lb →* ↥(StatedSL 5 (ZMod 2)))
    (Θ₂ : ↥(V₁.map t.toMonoidHom) ≃* Multiplicative ↥(altMat 5))
    (hequiv : ∀ (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
        (hxw : x (w : X) ∈ V₁.map t.toMonoidHom),
        Θ₂ ⟨x (w : X), hxw⟩ = altMulAct (θ₂ ⟨x, hx⟩) (Θ₂ w))
    (α : ↥(StatedSL 5 (ZMod 2)) ≃* ↥(StatedSL 5 (ZMod 2))) (hα : ∀ l, α (θ l) = θ₂ l)
    (P : GL (Fin 5) (ZMod 2))
    (hP : ∀ g, mat (α g) = (P : Matrix (Fin 5) (Fin 5) (ZMod 2)) * dmat g *
      ((P⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) : False := by
  classical
  have h1 : ∀ x ∈ Lb, t⁻¹ * x * t ∈ Lb := fun x hx => by
    simpa using z35_conj_mem hZ hML (Tb.inv_mem ht) hx
  have hTL : ∀ s ∈ Tb, ∀ l ∈ Lb, s * l * s⁻¹ ∈ Lb := fun s hs l hl => z35_conj_mem hZ hML hs hl
  have hLV₂ : Lb ≤ stabSub (V₁.map t.toMonoidHom) := le_stabSub_map_of_conj hLV h1
  have hboth : ∀ a ∈ A, ∃ l : ↥Lb, (∀ v ∈ V₁, a v = (l : MulAut X) v) ∧
      (∀ w ∈ V₁.map t.toMonoidHom, a w = (l : MulAut X) w) := by
    intro a ha
    obtain ⟨l, hl, hag⟩ := agree_of_autSub_eq hGL (hAN ha) (hAN ha).2
    obtain ⟨l'', hl'', hag2⟩ := agree_V₂_exists hGL hTL ht (hAN ha).1 (hAV₂ ha)
    exact ⟨⟨l, hl⟩, hag, agree_on_V₂ hZ hML ht hLV θ Θ hθs hΘ (hAN ha).1 hl hl'' hag hag2⟩
  set Pa : Subgroup ↥Lb := agreeSub Lb A V₁ hLV with hPa
  have hθeq1 : ∀ l : ↥Lb, θ l = 1 ↔ resHomOn V₁ hLV l = 1 := model_theta_eq_one_iff hLV θ Θ hΘ
  have hker1 : θ.ker = (resHomOn V₁ hLV).ker := by
    ext l
    simp only [MonoidHom.mem_ker]
    exact hθeq1 l
  have hθeq : ∀ l l' : ↥Lb, resHomOn V₁ hLV l = resHomOn V₁ hLV l' → θ l = θ l' := by
    intro l l' h
    have h0 : θ (l'⁻¹ * l) = 1 := by
      rw [hθeq1, map_mul, map_inv, h]
      simp
    rw [map_mul, map_inv] at h0
    exact (inv_mul_eq_one.mp h0).symm
  have hAbar : autSub A V₁ = Pa.map (resHomOn V₁ hLV) := by
    ext φ
    constructor
    · intro hφ
      obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
      obtain ⟨l, hl, hag⟩ := agree_of_autSub_eq hGL (hAN hg) (hAN hg).2
      refine ⟨⟨l, hl⟩, ⟨g, hg, hag⟩, ?_⟩
      ext v
      exact (hag v v.2).symm
    · rintro ⟨l, ⟨a, ha, hag⟩, rfl⟩
      refine mem_autSub.mpr ⟨⟨a, (hAN ha).2⟩, ha, ?_⟩
      ext v
      exact hag v v.2
  have hAbar2 : autSub A (V₁.map t.toMonoidHom) ≤ Pa.map (resHomOn (V₁.map t.toMonoidHom) hLV₂) := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨l, hl1, hl2⟩ := hboth (g : MulAut X) hg
    refine ⟨l, ⟨g, hg, hl1⟩, ?_⟩
    ext w
    exact (hl2 w w.2).symm
  set E : Subgroup ↥(StatedSL 5 (ZMod 2)) := Pa.map θ with hE
  have hker2 : θ.ker ≤ (resHomOn (V₁.map t.toMonoidHom) hLV₂).ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have hl2 : θ₂ l = 1 := by rw [← hα, hl, map_one]
    ext w
    have := hequiv (l : MulAut X) l.2 w ((hLV₂ l.2 (w : X)).2 w.2)
    rw [hl2, altMulAct_one] at this
    have h2 := Θ₂.injective this
    exact congrArg (fun u : ↥(V₁.map t.toMonoidHom) => (u : X)) h2
  have hc1 : Nat.card ↥(autSub A V₁) ≤ Nat.card ↥E := by
    rw [hAbar]
    exact card_map_le_of_ker_le Pa (resHomOn V₁ hLV) θ hker1.le
  have hc2 : Nat.card ↥(autSub A (V₁.map t.toMonoidHom)) ≤ Nat.card ↥E :=
    (Subgroup.card_le_of_le hAbar2).trans (card_map_le_of_ker_le Pa (resHomOn (V₁.map t.toMonoidHom) hLV₂) θ hker2)
  have hf1 : Nat.card ↥(fixV (autSub A V₁)) ≤
      Nat.card {B : Multiplicative ↥(altMat 5) // ∀ γ ∈ E, altMulAct γ B = B} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨Θ (v : ↥V₁), ?_⟩) ?_
    · rintro γ ⟨l, ⟨a, ha, hag⟩, rfl⟩
      have hv : ∀ φ ∈ autSub A V₁, φ (v : ↥V₁) = (v : ↥V₁) := v.2
      have h0 := hv (resHom V₁ ⟨a, (hAN ha).2⟩) (mem_autSub.mpr ⟨⟨a, (hAN ha).2⟩, ha, rfl⟩)
      rw [← hΘ l (v : ↥V₁)]
      congr 1
      apply Subtype.ext
      rw [coe_resHomOn_apply, ← hag ((v : ↥V₁) : X) (v : ↥V₁).2]
      exact congrArg (fun u : ↥V₁ => (u : X)) h0
    · intro v v' h
      exact Subtype.ext (Θ.injective (congrArg Subtype.val h))
  have hf2 : Nat.card ↥(fixV (autSub A (V₁.map t.toMonoidHom))) ≤
      Nat.card {B : Multiplicative ↥(altMat 5) // ∀ γ ∈ E, altMulAct (α γ) B = B} := by
    refine Nat.card_le_card_of_injective (fun w => ⟨Θ₂ (w : ↥(V₁.map t.toMonoidHom)), ?_⟩) ?_
    · rintro γ ⟨l, ⟨a, ha, hag⟩, rfl⟩
      obtain ⟨l', hl1, hl2⟩ := hboth a ha
      have hll' : θ l = θ l' := by
        apply hθeq
        ext v
        rw [coe_resHomOn_apply, coe_resHomOn_apply, ← hag (v : X) v.2, ← hl1 (v : X) v.2]
      have hv : ∀ φ ∈ autSub A (V₁.map t.toMonoidHom),
          φ (w : ↥(V₁.map t.toMonoidHom)) = (w : ↥(V₁.map t.toMonoidHom)) := w.2
      have h0 := hv (resHom (V₁.map t.toMonoidHom) ⟨a, hAV₂ ha⟩)
        (mem_autSub.mpr ⟨⟨a, hAV₂ ha⟩, ha, rfl⟩)
      have h00 : a (((w : ↥(V₁.map t.toMonoidHom)) : X)) = ((w : ↥(V₁.map t.toMonoidHom)) : X) :=
        congrArg (fun u : ↥(V₁.map t.toMonoidHom) => (u : X)) h0
      have hwl := hequiv (l' : MulAut X) l'.2 (w : ↥(V₁.map t.toMonoidHom))
        ((hLV₂ l'.2 ((w : ↥(V₁.map t.toMonoidHom)) : X)).2 (w : ↥(V₁.map t.toMonoidHom)).2)
      rw [hll', hα l']
      show altMulAct (θ₂ l') (Θ₂ (w : ↥(V₁.map t.toMonoidHom))) = Θ₂ (w : ↥(V₁.map t.toMonoidHom))
      rw [← hwl]
      congr 1
      apply Subtype.ext
      show (l' : MulAut X) ((w : ↥(V₁.map t.toMonoidHom)) : X) = ((w : ↥(V₁.map t.toMonoidHom)) : X)
      rw [← hl2 _ (w : ↥(V₁.map t.toMonoidHom)).2]
      exact h00
    · intro v v' h
      exact Subtype.ext (Θ₂.injective (congrArg Subtype.val h))
  have hb1 : 2 ^ 10 ≤ Nat.card ↥(autSub A V₁) * Nat.card ↥(fixV (autSub A V₁)) := by
    have h0 := hoff₁.2.2.2 ⊥ bot_le
    rwa [Subgroup.card_bot, fixV_bot_eq_top_aut, Subgroup.card_top, one_mul, hcard] at h0
  have hb2 : 2 ^ 10 ≤ Nat.card ↥(autSub A (V₁.map t.toMonoidHom)) *
      Nat.card ↥(fixV (autSub A (V₁.map t.toMonoidHom))) := by
    have h0 := hoff₂.2.2.2 ⊥ bot_le
    rw [Subgroup.card_bot, fixV_bot_eq_top_aut, Subgroup.card_top, one_mul] at h0
    have hV2 : Nat.card ↥(V₁.map t.toMonoidHom) = 2 ^ 10 := by
      rw [← hcard]
      exact (Nat.card_congr (restrictAutEquiv t V₁).toEquiv).symm
    rwa [hV2] at h0
  have hE0 : E ≠ ⊥ := by
    obtain ⟨ā, hā⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hoff₁.2.1
    have hmem : (ā : MulAut ↥V₁) ∈ Pa.map (resHomOn V₁ hLV) := hAbar ▸ ā.2
    obtain ⟨l, hl, hlā⟩ := hmem
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    refine ⟨⟨θ l, Subgroup.mem_map_of_mem _ hl⟩, fun h1 => hā ?_⟩
    have h2 : θ l = 1 := congrArg Subtype.val h1
    apply Subtype.ext
    rw [← hlā]
    exact (hθeq1 l).1 h2
  have hEab : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := by
    rintro _ ⟨l₁, hl₁, rfl⟩ _ ⟨l₂, hl₂, rfl⟩
    have hm₁ : resHomOn V₁ hLV l₁ ∈ autSub A V₁ := hAbar ▸ Subgroup.mem_map_of_mem _ hl₁
    have hm₂ : resHomOn V₁ hLV l₂ ∈ autSub A V₁ := hAbar ▸ Subgroup.mem_map_of_mem _ hl₂
    have hc := hoff₁.2.2.1.1 _ hm₁ _ hm₂
    rw [← map_mul, ← map_mul]
    apply hθeq
    rw [map_mul, map_mul]
    exact hc
  have hE2 : ∀ g ∈ E, g * g = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    have hm : resHomOn V₁ hLV l ∈ autSub A V₁ := hAbar ▸ Subgroup.mem_map_of_mem _ hl
    have hc := hoff₁.2.2.1.2 _ hm
    rw [← map_mul, ← map_one θ]
    apply hθeq
    rw [map_mul, map_one]
    simpa [pow_two] using hc
  exact final_graph hU α P hP E hE0 hEab hE2 (hb1.trans (Nat.mul_le_mul hc1 hf1))
    (hb2.trans (Nat.mul_le_mul hc2 hf2))

end Assembly

theorem d35InspUniq11_of_extSq (hU : D35InspExtSq) : D35InspUniq11 := by
  classical
  intro X _ _ Mb Tb Lb V₁ A t hZ hML ht htV hAN hAV₂ hcase hoff₁ hoff₂
  obtain ⟨A₀, hGJ, hJL, hcard, -, π, hπ, -⟩ := hcase
  have hGL : autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁ = autSub Lb V₁ := hGJ.trans hJL
  have hLV : Lb ≤ stabSub V₁ := z35_le_stabSub hZ hML
  obtain ⟨θ, Θ, hθs, hΘ⟩ :=
    exists_modelData extSq5_equiv_alt (fun _ h => altMulAct_faithful h) hLV π hπ
  have h1 : ∀ x ∈ Lb, t⁻¹ * x * t ∈ Lb := fun x hx => by
    simpa using z35_conj_mem hZ hML (Tb.inv_mem ht) hx
  have h2 : ∀ x ∈ Lb, t * x * t⁻¹ ∈ Lb := fun x hx => z35_conj_mem hZ hML ht hx
  obtain ⟨θ₂, Θ₂, -, hθ₂s, hequiv, hΘ₂t⟩ := twisted_model hLV h1 h2 θ Θ hθs hΘ
  have hker : ∀ l, θ l = 1 → θ₂ l = 1 := fun l hl => ker_theta_le hZ hML hLV θ Θ hΘ θ₂ hθ₂s l hl
  obtain ⟨α, hα⟩ := exists_aut_of_ker_le θ θ₂ hθs hθ₂s hker
  obtain ⟨P, hP | hP⟩ := CFSG.Quasithin.B5.Ln.aut_cases (n := 5) (by norm_num) α
  · exact inner_case_false hZ hML ht htV hLV θ Θ hΘ θ₂ Θ₂ hequiv hΘ₂t α hα P hP
  · exact graph_case_false hU hZ hML ht hLV hGL hAN hAV₂ hcard hoff₁ hoff₂ θ Θ hθs hΘ θ₂ Θ₂
      hequiv α hα P hP

theorem d35InspUniq_of_inputs (h8 : D35InspUniq8) (hU : D35InspExtSq) : D35InspUniq :=
  d35InspUniq_of_cases h8 (d35InspUniq11_of_extSq hU)

end CFSG.Quasithin
