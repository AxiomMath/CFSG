module

public import CFSG.Quasithin.Background.F918T5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix

theorem false_of_intertwiner {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)}
    {V₁ : Subgroup X} {t : MulAut X} (hZ : Z35 Mb Tb Lb V₁) (hML : Mb = Lb) (ht : t ∈ Tb)
    (htV : t ∉ stabSub V₁) (hLV : Lb ≤ stabSub V₁)
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (θ : ↥Lb →* ↥Γ) (Θ : ↥V₁ ≃* Multiplicative (Fin 3 → K))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V₁),
      Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = natAct Γ (θ l) (Θ v))
    (θ₂ : ↥Lb →* ↥Γ) (Θ₂ : ↥(V₁.map t.toMonoidHom) ≃* Multiplicative (Fin 3 → K))
    (hequiv : ∀ (x : MulAut X) (hx : x ∈ Lb) (w : ↥(V₁.map t.toMonoidHom))
        (hxw : x (w : X) ∈ V₁.map t.toMonoidHom),
        Θ₂ ⟨x (w : X), hxw⟩ = natAct Γ (θ₂ ⟨x, hx⟩) (Θ₂ w))
    (hΘ₂t : ∀ v : ↥V₁, Θ₂ (restrictAutEquiv t V₁ v) = Θ v)
    (Φ : (Fin 3 → K) ≃+ (Fin 3 → K))
    (hΦ : ∀ (l : ↥Lb) (w : Fin 3 → K),
      Φ ((((θ l : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) =
        ((((θ₂ l : ↥Γ) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Φ w)) : False := by
  classical
  let ΦM : Multiplicative (Fin 3 → K) ≃* Multiplicative (Fin 3 → K) :=
    { toFun := fun x => Multiplicative.ofAdd (Φ (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (Φ.symm (Multiplicative.toAdd x))
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => by simp }
  set G : ↥V₁ ≃* ↥V₁ := Θ.trans (ΦM.trans Θ.symm) with hG
  have hΘG : ∀ v, Θ (G v) = Multiplicative.ofAdd (Φ (Multiplicative.toAdd (Θ v))) := fun v => by
    simp [hG, ΦM]
  have hmap1 : V₁.map (1 : MulAut X).toMonoidHom = V₁ := by
    ext v
    simp
  have key : ∀ (x : MulAut X) (hx : x ∈ Lb) (v v' : ↥V₁), x (v : X) = (v' : X) →
      t ((G v' : ↥V₁) : X) = x (t ((G v : ↥V₁) : X)) := by
    intro x hx v v' hxv
    have hv' : v' = (resHomOn V₁ hLV ⟨x, hx⟩ : MulAut ↥V₁) v := Subtype.ext hxv.symm
    have hxw : x ((restrictAutEquiv t V₁ (G v) : ↥(V₁.map t.toMonoidHom)) : X) ∈
        V₁.map t.toMonoidHom :=
      mem_map_of_conj hLV (fun l hl => by
        simpa using z35_conj_mem hZ hML (Tb.inv_mem ht) hl) hx
        (restrictAutEquiv t V₁ (G v)).2
    have e1 := hequiv x hx (restrictAutEquiv t V₁ (G v)) hxw
    rw [hΘ₂t] at e1
    have e2 : Θ₂ (restrictAutEquiv t V₁ (G v')) =
        Θ₂ ⟨x ((restrictAutEquiv t V₁ (G v) : ↥(V₁.map t.toMonoidHom)) : X), hxw⟩ := by
      rw [e1, hΘ₂t, hΘG, hv', hΘ, hΘG]
      have h3 := hΦ ⟨x, hx⟩ (Multiplicative.toAdd (Θ v))
      simp only [natAct, toAdd_ofAdd]
      rw [h3]
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

end CFSG.Quasithin
