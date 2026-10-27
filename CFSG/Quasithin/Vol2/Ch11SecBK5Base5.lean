module

public import CFSG.Quasithin.Vol2.KGNatSemi
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {W : Type*} [CommGroup W] {LM : LinModel D K M} {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : D.Gam →* ↥H} {f : W → M}

@[expose] def normZH (H : Subgroup (MulAut W)) (Z : Subgroup W) : Subgroup (MulAut W) where
  carrier := {τ | (∀ z, z ∈ Z ↔ τ z ∈ Z) ∧ ∀ h, h ∈ H ↔ τ * h * τ⁻¹ ∈ H}
  one_mem' := ⟨fun _ => Iff.rfl, fun h => by rw [one_mul, inv_one, mul_one]⟩
  mul_mem' {a b} ha hb := ⟨fun z => by rw [MulAut.mul_apply, hb.1 z, ha.1 (b z)],
    fun h => by
      rw [hb.2 h, ha.2 (b * h * b⁻¹)]
      group⟩
  inv_mem' {a} ha := ⟨fun z => by
      rw [ha.1 (a⁻¹ z), MulAut.apply_inv_self],
    fun h => by
      rw [ha.2 (a⁻¹ * h * a⁻¹⁻¹)]
      group⟩

omit [Field K] [AddCommGroup M] [Module K M] in
theorem maps_Z_of {τ : MulAut W} (hτ : τ ∈ normZH H Z) : ∀ z ∈ Z, τ z ∈ Z :=
  fun z hz => (hτ.1 z).mp hz

theorem autMap_mul' (hf : IsCoord LM H Z π f) {s t : MulAut W} (hs : s ∈ normZH H Z)
    (ht : t ∈ normZH H Z) (x : M) :
    hf.autMap (s * t) (maps_Z_of ((normZH H Z).mul_mem hs ht)) x =
      hf.autMap s (maps_Z_of hs) (hf.autMap t (maps_Z_of ht) x) := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [hf.autMap_apply, hf.autMap_apply, hf.autMap_apply, MulAut.mul_apply]

theorem autMap_one' (hf : IsCoord LM H Z π f) (x : M) :
    hf.autMap 1 (maps_Z_of (normZH H Z).one_mem) x = x := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [hf.autMap_apply, MulAut.one_apply]

theorem autMap_congr (hf : IsCoord LM H Z π f) {s t : MulAut W} (hst : s = t)
    (hs : ∀ z ∈ Z, s z ∈ Z) (ht : ∀ z ∈ Z, t z ∈ Z) (x : M) :
    hf.autMap s hs x = hf.autMap t ht x := by
  subst hst
  rfl

@[expose] noncomputable def psiZ (hf : IsCoord LM H Z π f) :
    ↥(normZH H Z) →* MulAut (Multiplicative M) where
  toFun τ :=
    { toFun := fun x => Multiplicative.ofAdd (hf.autMap τ (maps_Z_of τ.2)
        (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (hf.autMap (τ⁻¹ : ↥(normZH H Z))
        (maps_Z_of (τ⁻¹).2) (Multiplicative.toAdd x))
      left_inv := fun x => by
        simp only [toAdd_ofAdd]
        rw [← autMap_mul' hf (τ⁻¹).2 τ.2, autMap_congr hf (s := _ * _) (t := 1) (by
          rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]) _
          (maps_Z_of (normZH H Z).one_mem), autMap_one']
        rfl
      right_inv := fun x => by
        simp only [toAdd_ofAdd]
        rw [← autMap_mul' hf τ.2 (τ⁻¹).2, autMap_congr hf (s := _ * _) (t := 1) (by
          rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]) _
          (maps_Z_of (normZH H Z).one_mem), autMap_one']
        rfl
      map_mul' := fun x y => by
        simp only [toAdd_mul, map_add, ofAdd_add] }
  map_one' := MulEquiv.ext fun x => by
    show Multiplicative.ofAdd (hf.autMap ((1 : ↥(normZH H Z)) : MulAut W)
      (maps_Z_of (1 : ↥(normZH H Z)).2) (Multiplicative.toAdd x)) = x
    rw [autMap_congr hf (t := 1) (Subgroup.coe_one _) _ (maps_Z_of (normZH H Z).one_mem),
      autMap_one']
    rfl
  map_mul' s t := MulEquiv.ext fun x => by
    show Multiplicative.ofAdd (hf.autMap ((s * t : ↥(normZH H Z)) : MulAut W)
      (maps_Z_of (s * t).2) (Multiplicative.toAdd x)) =
      Multiplicative.ofAdd (hf.autMap (s : MulAut W) (maps_Z_of s.2)
        (Multiplicative.toAdd (Multiplicative.ofAdd
        (hf.autMap (t : MulAut W) (maps_Z_of t.2) (Multiplicative.toAdd x)))))
    rw [toAdd_ofAdd, autMap_congr hf (t := (s : MulAut W) * t) (Subgroup.coe_mul _ s t) _
      (maps_Z_of ((normZH H Z).mul_mem s.2 t.2)), autMap_mul' hf s.2 t.2]

theorem psiZ_apply (hf : IsCoord LM H Z π f) (τ : ↥(normZH H Z)) (w : W) :
    psiZ hf τ (Multiplicative.ofAdd (f w)) = Multiplicative.ofAdd (f ((τ : MulAut W) w)) := by
  change Multiplicative.ofAdd (hf.autMap (τ : MulAut W) (maps_Z_of τ.2)
    (Multiplicative.toAdd (Multiplicative.ofAdd (f w)))) = _
  rw [toAdd_ofAdd, hf.autMap_apply]

theorem psiZ_eq_one_iff (hf : IsCoord LM H Z π f) (τ : ↥(normZH H Z)) :
    psiZ hf τ = 1 ↔ ∀ w, f ((τ : MulAut W) w) = f w := by
  constructor
  · intro h w
    have := congrArg (fun φ : MulAut (Multiplicative M) => φ (Multiplicative.ofAdd (f w))) h
    simp only [psiZ_apply, MulAut.one_apply] at this
    exact congrArg Multiplicative.toAdd this
  · intro h
    refine MulEquiv.ext fun x => ?_
    obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd x)
    rw [← ofAdd_toAdd x, ← hw, psiZ_apply, h, MulAut.one_apply]

theorem psiZ_injective (hf : IsCoord LM H Z π f)
    (hfaith : ∀ γ, (∀ x, LM.lin γ x = x) → π γ = 1) (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (hgen : commV H = ⊤) : Function.Injective (psiZ hf) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  have hfix := (psiZ_eq_one_iff hf τ).mp hτ
  have hfix' : ∀ w, f ((τ : MulAut W)⁻¹ w) = f w := fun w => by
    have := hfix ((τ : MulAut W)⁻¹ w)
    rw [MulAut.apply_inv_self] at this
    exact this.symm
  have hcent : ∀ h ∈ H, (τ : MulAut W) * h * (τ : MulAut W)⁻¹ = h := by
    intro h hh
    obtain ⟨γ, hγ⟩ := hf.onto ⟨h, hh⟩
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, (τ.2.2 h).mp hh⟩
    have hγ1 : ((π γ : ↥H) : MulAut W) = h := congrArg Subtype.val hγ
    have hγ2 : ((π γ' : ↥H) : MulAut W) = (τ : MulAut W) * h * (τ : MulAut W)⁻¹ :=
      congrArg Subtype.val hγ'
    have h1 : ∀ w, f (((π γ' : ↥H) : MulAut W) w) = f (((π γ : ↥H) : MulAut W) w) := by
      intro w
      calc f (((π γ' : ↥H) : MulAut W) w)
          = f ((τ : MulAut W) (h ((τ : MulAut W)⁻¹ w))) := by rw [hγ2]; rfl
        _ = f (h ((τ : MulAut W)⁻¹ w)) := hfix _
        _ = f (((π γ : ↥H) : MulAut W) ((τ : MulAut W)⁻¹ w)) := by rw [hγ1]
        _ = LM.lin γ (f ((τ : MulAut W)⁻¹ w)) := hf.act γ _
        _ = LM.lin γ (f w) := by rw [hfix']
        _ = f (((π γ : ↥H) : MulAut W) w) := (hf.act γ w).symm
    have h2 : π (γ⁻¹ * γ') = 1 := by
      refine hfaith _ fun x => ?_
      obtain ⟨w, rfl⟩ := hf.surj x
      calc LM.lin (γ⁻¹ * γ') (f w) = f (((π (γ⁻¹ * γ') : ↥H) : MulAut W) w) :=
            (hf.act _ w).symm
        _ = f (((π γ⁻¹ : ↥H) : MulAut W) (((π γ' : ↥H) : MulAut W) w)) := by
            rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
        _ = LM.lin γ⁻¹ (f (((π γ' : ↥H) : MulAut W) w)) := hf.act _ _
        _ = LM.lin γ⁻¹ (f (((π γ : ↥H) : MulAut W) w)) := by rw [h1]
        _ = f (((π γ⁻¹ : ↥H) : MulAut W) (((π γ : ↥H) : MulAut W) w)) := (hf.act _ _).symm
        _ = f (((π (γ⁻¹ * γ) : ↥H) : MulAut W) w) := by
            rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
        _ = f w := by rw [inv_mul_cancel, map_one]; rfl
    have h3 : π γ' = π γ := by
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
    rw [← hγ2, h3, hγ1]
  have hδ : ∀ w, (τ : MulAut W) w * w⁻¹ ∈ Z := fun w => by
    rw [← hf.ker, hf.map_mul_inv, hfix, sub_self]
  have hker : commV H ≤ (commHom (τ : MulAut W)).ker := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨h, hh, w, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
    have e : (τ : MulAut W) (h w) = h ((τ : MulAut W) w) := by
      have := congrArg (fun φ : MulAut W => φ ((τ : MulAut W) w)) (hcent h hh)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
      exact this
    have e2 : commHom (τ : MulAut W) (h w) = commHom (τ : MulAut W) w := by
      rw [commHom_apply, commHom_apply, e, ← map_inv h w, ← map_mul h, hHZ h hh _ (hδ w)]
    rw [e2, mul_inv_cancel]
  rw [hgen, top_le_iff] at hker
  apply Subtype.ext
  refine MulEquiv.ext fun w => ?_
  have h5 : w ∈ (commHom (τ : MulAut W)).ker := by rw [hker]; trivial
  rw [MonoidHom.mem_ker, commHom_apply, mul_inv_eq_one] at h5
  exact h5

theorem psiZ_pi (hf : IsCoord LM H Z π f) (γ : D.Gam) (hγ : ((π γ : ↥H) : MulAut W) ∈ normZH H Z)
    (x : M) : psiZ hf ⟨_, hγ⟩ (Multiplicative.ofAdd x) = Multiplicative.ofAdd (LM.lin γ x) := by
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [psiZ_apply, hf.act]

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
