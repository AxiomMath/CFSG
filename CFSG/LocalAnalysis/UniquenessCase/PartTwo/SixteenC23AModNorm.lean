module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC

variable {V : Type} [CommGroup V]

private theorem c23a_exists_sl3_of_bijective (φ : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2))
    (hφ : Function.Bijective φ) : ∃ Φ : SL3F2, ∀ x, Φ • x = φ x := by
  let φl : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c x => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl <;> simp }
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := LinearMap.toMatrix' φl
  have hM : ∀ x, M.mulVec x = φ x := fun x => LinearMap.toMatrix'_mulVec φl x
  have hinj : Function.Injective M.mulVec := by
    intro x y h
    exact hφ.1 (by rw [← hM x, ← hM y]; exact h)
  have hunit : IsUnit M := (Matrix.mulVec_injective_iff_isUnit).1 hinj
  have hdet : M.det = 1 := by
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M).1 hunit
    rw [← hu, Subsingleton.elim u 1, Units.val_one]
  refine ⟨(⟨M, hdet⟩ : SL3F2), fun x => ?_⟩
  change (M • x : Fin 3 → ZMod 2) = φ x
  rw [Matrix.smul_eq_mulVec]
  exact hM x

private theorem c23a_sl3_eq_of_smul {A B : SL3F2}
    (h : ∀ x : Fin 3 → ZMod 2, A • x = B • x) : A = B := by
  apply Subtype.ext
  ext i j
  have hb := congrArg (fun v : Fin 3 → ZMod 2 => v i) (h (Pi.single j 1))
  simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    Matrix.mulVec_single_one] using hb

theorem c23a_normalizer_act [Finite V] {L : Subgroup (MulAut V)} {E Z : Subgroup V}
    (h : C23ABlock L E Z) {g : MulAut V} (hgL : g ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (hgE : ∀ e ∈ E, g e ∈ E) : ∃ l ∈ L, ∀ e ∈ E, g e = l e := by
  obtain ⟨D⟩ := h.nat
  have hZE : Z ≤ E := by rw [h.fix]; exact inf_le_left
  have hZF : Z ≤ fixV L := by rw [h.fix]; exact inf_le_right
  have hLE : ∀ l ∈ L, ∀ e ∈ E, l e ∈ E := by
    intro l hl e he
    obtain ⟨γ, hγ⟩ := D.surj ⟨l, hl⟩
    have hcoe : ((D.ρ γ : ↥L) : MulAut V) = l := congrArg Subtype.val hγ
    rw [← hcoe]
    exact D.inv γ e he
  have hgEeq : Subgroup.map g.toMonoidHom E = E :=
    Subgroup.eq_of_le_of_card_ge
      (by rintro v ⟨e, he, rfl⟩; exact hgE e he)
      (by rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective])
  have hgZ : ∀ z ∈ Z, g z ∈ Z := by
    intro z hz
    have hzE : z ∈ E := hZE hz
    rw [h.fix]
    refine ⟨hgE z hzE, mem_fixV.2 ?_⟩
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L :=
      (Subgroup.mem_set_normalizer_iff''.mp hgL l).mp hl
    have hzl : (g⁻¹ * l * g) z = z :=
      (mem_fixV.1 (hZF hz)) (g⁻¹ * l * g) hl'
    calc l (g z) = (g * (g⁻¹ * l * g) * g⁻¹) (g z) := by
          congr 1
          group
      _ = g ((g⁻¹ * l * g) (g⁻¹ (g z))) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = g ((g⁻¹ * l * g) z) := by rw [MulAut.inv_apply_self]
      _ = g z := by rw [hzl]
  have hgZeq : Subgroup.map g.toMonoidHom Z = Z :=
    Subgroup.eq_of_le_of_card_ge
      (by rintro v ⟨z, hz, rfl⟩; exact hgZ z hz)
      (by rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective])
  have hgEinv : ∀ e ∈ E, g⁻¹ e ∈ E := by
    intro e he
    have hmem : e ∈ Subgroup.map g.toMonoidHom E := by rw [hgEeq]; exact he
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 hmem
    have hae' : g a = e := hae
    have h : g⁻¹ e = a := by rw [← hae', MulAut.inv_apply_self]
    rw [h]
    exact ha
  have hgZinv : ∀ z ∈ Z, g⁻¹ z ∈ Z := by
    intro z hz
    have hmem : z ∈ Subgroup.map g.toMonoidHom Z := by rw [hgZeq]; exact hz
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.1 hmem
    have haz' : g a = z := haz
    have h : g⁻¹ z = a := by rw [← haz', MulAut.inv_apply_self]
    rw [h]
    exact ha
  let gE : ↥E ≃* ↥E :=
    { toFun := fun u => ⟨g (u : V), hgE (u : V) u.2⟩
      invFun := fun u => ⟨g⁻¹ (u : V), hgEinv (u : V) u.2⟩
      left_inv := fun u => Subtype.ext (by
        show g⁻¹ (g (u : V)) = (u : V)
        rw [MulAut.inv_apply_self])
      right_inv := fun u => Subtype.ext (by
        show g (g⁻¹ (u : V)) = (u : V)
        rw [MulAut.apply_inv_self])
      map_mul' := fun u v => Subtype.ext (map_mul g (u : V) (v : V)) }
  let Θ : ↥E →* Multiplicative (Fin 3 → ZMod 2) := D.θ.comp gE.toMonoidHom
  have hker : D.θ.ker ≤ Θ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact (D.θ_ker (gE u)).2 (hgZ (u : V) ((D.θ_ker u).1 hu))
  let φmono : Multiplicative (Fin 3 → ZMod 2) →* Multiplicative (Fin 3 → ZMod 2) :=
    D.θ.liftOfSurjective D.θ_surj ⟨Θ, hker⟩
  have hφθ : ∀ u : ↥E, φmono (D.θ u) = Θ u := by
    intro u
    exact MonoidHom.liftOfRightInverse_comp_apply D.θ (Function.surjInv D.θ_surj)
      (Function.rightInverse_surjInv D.θ_surj) ⟨Θ, hker⟩ u
  let φ : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun x => (φmono (Multiplicative.ofAdd x)).toAdd
      map_zero' := by
        show (φmono (Multiplicative.ofAdd 0)).toAdd = 0
        rw [ofAdd_zero, MonoidHom.map_one, toAdd_one]
      map_add' := fun x y => by
        show (φmono (Multiplicative.ofAdd (x + y))).toAdd =
          (φmono (Multiplicative.ofAdd x)).toAdd + (φmono (Multiplicative.ofAdd y)).toAdd
        rw [ofAdd_add, MonoidHom.map_mul, toAdd_mul] }
  have hφθ_add : ∀ u : ↥E, φ (D.θ u).toAdd = (Θ u).toAdd := by
    intro u
    show (φmono (Multiplicative.ofAdd ((D.θ u).toAdd))).toAdd = (Θ u).toAdd
    rw [ofAdd_toAdd, hφθ u]
  have hφα : ∀ u : ↥E, (D.θ (gE u)).toAdd = φ (D.θ u).toAdd := by
    intro u
    show (Θ u).toAdd = φ (D.θ u).toAdd
    exact (hφθ_add u).symm
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨u, hu⟩ := D.θ_surj (Multiplicative.ofAdd y)
    obtain ⟨u₀, hu₀⟩ := gE.surjective u
    refine ⟨(D.θ u₀).toAdd, ?_⟩
    rw [← hφα u₀, hu₀, hu, toAdd_ofAdd]
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨u, hu⟩ := D.θ_surj (Multiplicative.ofAdd x)
    have h1 : D.θ (gE u) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      show (D.θ (gE u)).toAdd = 0
      rw [hφα u, show (D.θ u).toAdd = x from by rw [hu, toAdd_ofAdd], hx]
    have h2 : g (u : V) ∈ Z := (D.θ_ker (gE u)).1 h1
    have h3 : (u : V) ∈ Z := by
      have h4 := hgZinv (g (u : V)) h2
      rwa [MulAut.inv_apply_self] at h4
    have h5 : D.θ u = 1 := (D.θ_ker u).2 h3
    have h6 : Multiplicative.ofAdd x = 1 := by rw [← hu]; exact h5
    have h7 := congrArg Multiplicative.toAdd h6
    simpa using h7
  have hφbij : Function.Bijective φ := ⟨hφinj, hφsurj⟩
  obtain ⟨Φ, hΦ⟩ := c23a_exists_sl3_of_bijective φ hφbij
  have hΦinv : ∀ x, φ x = Φ • x := fun x => (hΦ x).symm
  have hgp : ∀ u : ↥E,
      (D.θ ⟨g (u : V), hgE (u : V) u.2⟩).toAdd = Φ • (D.θ u).toAdd := by
    intro u
    exact (hφα u).trans (hΦinv _)
  let P : MulAut V := (D.ρ Φ : ↥L)
  let c : MulAut V := P⁻¹ * g
  have hP : P ∈ L := (D.ρ Φ).2
  have hPinv_eq : P⁻¹ = ((D.ρ Φ⁻¹ : ↥L) : MulAut V) := by
    show ((D.ρ Φ : ↥L) : MulAut V)⁻¹ = _
    rw [← Subgroup.coe_inv, ← MonoidHom.map_inv D.ρ Φ]
  have hcE : ∀ v ∈ E, c v ∈ E := by
    intro v hv
    have h1 : c v = ((D.ρ Φ⁻¹ : ↥L) : MulAut V) (g v) := by
      show (P⁻¹ * g) v = _
      rw [MulAut.mul_apply, hPinv_eq]
    rw [h1]
    exact D.inv Φ⁻¹ (g v) (hgE v hv)
  have hcEinv : ∀ v ∈ E, c⁻¹ v ∈ E := by
    intro v hv
    have hPv : P v ∈ E := D.inv Φ v hv
    have hgPv : g⁻¹ (P v) ∈ E := hgEinv (P v) hPv
    have hc : c⁻¹ v = g⁻¹ (P v) := by
      show (P⁻¹ * g)⁻¹ v = _
      rw [mul_inv_rev, inv_inv, MulAut.mul_apply]
    rw [hc]
    exact hgPv
  have hc_theta : ∀ u : ↥E, D.θ ⟨c (u : V), hcE (u : V) u.2⟩ = D.θ u := by
    intro u
    have hcu : c (u : V) = ((D.ρ Φ⁻¹ : ↥L) : MulAut V) (g (u : V)) := by
      show (P⁻¹ * g) (u : V) = _
      rw [MulAut.mul_apply, hPinv_eq]
    calc D.θ ⟨c (u : V), hcE (u : V) u.2⟩
        = D.θ ⟨((D.ρ Φ⁻¹ : ↥L) : MulAut V) (g (u : V)),
            D.inv Φ⁻¹ (g (u : V)) (hgE (u : V) u.2)⟩ :=
          congrArg D.θ (Subtype.ext hcu)
      _ = Multiplicative.ofAdd (Φ⁻¹ • (D.θ ⟨g (u : V), hgE (u : V) u.2⟩).toAdd) :=
          D.equiv Φ⁻¹ ⟨g (u : V), hgE (u : V) u.2⟩
      _ = Multiplicative.ofAdd (Φ⁻¹ • (Φ • (D.θ u).toAdd)) := by rw [hgp u]
      _ = Multiplicative.ofAdd ((D.θ u).toAdd) := by rw [inv_smul_smul]
      _ = D.θ u := ofAdd_toAdd _
  have hcN : c ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
    have hPinvN : P⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
      Subgroup.le_normalizer (H := L) (L.inv_mem hP)
    exact (Subgroup.normalizer (L : Set (MulAut V))).mul_mem hPinvN hgL
  have hcent : ∀ l ∈ L, c * l = l * c := by
    intro l hl
    obtain ⟨γ, hγ⟩ := D.surj ⟨l, hl⟩
    have hlγ : ((D.ρ γ : ↥L) : MulAut V) = l := congrArg Subtype.val hγ
    let l' : MulAut V := c * l * c⁻¹
    have hl'mem : l' ∈ L := (Subgroup.mem_set_normalizer_iff.mp hcN l).mp hl
    obtain ⟨γ', hγ'⟩ := D.surj ⟨l', hl'mem⟩
    have hl'γ : ((D.ρ γ' : ↥L) : MulAut V) = l' := congrArg Subtype.val hγ'
    have hl'u : ∀ v : V, l' v = c (l (c⁻¹ v)) := by
      intro v
      show (c * l * c⁻¹) v = c (l (c⁻¹ v))
      rw [MulAut.mul_apply, MulAut.mul_apply]
    have hact_l : ∀ w : ↥E,
        (D.θ ⟨l (w : V), hLE l hl (w : V) w.2⟩).toAdd = γ • (D.θ w).toAdd := by
      intro w
      have heq := D.equiv γ w
      have hsub : (⟨l (w : V), hLE l hl (w : V) w.2⟩ : ↥E) =
          ⟨((D.ρ γ : ↥L) : MulAut V) (w : V), D.inv γ (w : V) w.2⟩ := by
        apply Subtype.ext
        show l (w : V) = ((D.ρ γ : ↥L) : MulAut V) (w : V)
        rw [hlγ]
      rw [hsub, heq, toAdd_ofAdd]
    have hact_l' : ∀ w : ↥E,
        (D.θ ⟨l' (w : V), hLE l' hl'mem (w : V) w.2⟩).toAdd = γ' • (D.θ w).toAdd := by
      intro w
      have heq := D.equiv γ' w
      have hsub : (⟨l' (w : V), hLE l' hl'mem (w : V) w.2⟩ : ↥E) =
          ⟨((D.ρ γ' : ↥L) : MulAut V) (w : V), D.inv γ' (w : V) w.2⟩ := by
        apply Subtype.ext
        show l' (w : V) = ((D.ρ γ' : ↥L) : MulAut V) (w : V)
        rw [hl'γ]
      rw [hsub, heq, toAdd_ofAdd]
    have hsmul : ∀ x : Fin 3 → ZMod 2, γ' • x = γ • x := by
      intro x
      obtain ⟨u, hu⟩ := D.θ_surj (Multiplicative.ofAdd x)
      have hx : (D.θ u).toAdd = x := by rw [hu, toAdd_ofAdd]
      have hLL : (D.θ ⟨l' (u : V), hLE l' hl'mem (u : V) u.2⟩).toAdd =
          (D.θ ⟨l (u : V), hLE l hl (u : V) u.2⟩).toAdd := by
        have h1 : (D.θ ⟨l' (u : V), hLE l' hl'mem (u : V) u.2⟩).toAdd =
            (D.θ ⟨c (l (c⁻¹ (u : V))), hcE (l (c⁻¹ (u : V)))
              (hLE l hl (c⁻¹ (u : V)) (hcEinv (u : V) u.2))⟩).toAdd :=
          congrArg Multiplicative.toAdd (congrArg D.θ (Subtype.ext (hl'u (u : V))))
        have h2 : (D.θ ⟨c (l (c⁻¹ (u : V))), hcE (l (c⁻¹ (u : V)))
              (hLE l hl (c⁻¹ (u : V)) (hcEinv (u : V) u.2))⟩).toAdd =
            (D.θ ⟨l (c⁻¹ (u : V)),
              hLE l hl (c⁻¹ (u : V)) (hcEinv (u : V) u.2)⟩).toAdd :=
          congrArg Multiplicative.toAdd (hc_theta ⟨l (c⁻¹ (u : V)),
            hLE l hl (c⁻¹ (u : V)) (hcEinv (u : V) u.2)⟩)
        have hct' : (D.θ ⟨c⁻¹ (u : V), hcEinv (u : V) u.2⟩).toAdd = (D.θ u).toAdd := by
          have h := hc_theta ⟨c⁻¹ (u : V), hcEinv (u : V) u.2⟩
          have h2' : (⟨c (c⁻¹ (u : V)),
              hcE (c⁻¹ (u : V)) (hcEinv (u : V) u.2)⟩ : ↥E) = u := by
            apply Subtype.ext
            show c (c⁻¹ (u : V)) = (u : V)
            rw [MulAut.apply_inv_self]
          rw [h2'] at h
          exact (congrArg Multiplicative.toAdd h).symm
        have h3 : (D.θ ⟨l (c⁻¹ (u : V)),
              hLE l hl (c⁻¹ (u : V)) (hcEinv (u : V) u.2)⟩).toAdd =
            (D.θ ⟨l (u : V), hLE l hl (u : V) u.2⟩).toAdd := by
          rw [hact_l ⟨c⁻¹ (u : V), hcEinv (u : V) u.2⟩, hact_l u, hct']
        exact h1.trans (h2.trans h3)
      have hL' := hact_l' u
      rw [hx] at hL'
      have hL := hact_l u
      rw [hx] at hL
      rw [← hL', ← hL]
      exact hLL
    have hγγ : γ' = γ := c23a_sl3_eq_of_smul hsmul
    have hl'l : l' = l := by
      calc l' = ((D.ρ γ' : ↥L) : MulAut V) := hl'γ.symm
        _ = ((D.ρ γ : ↥L) : MulAut V) := by rw [hγγ]
        _ = l := hlγ
    calc c * l = (c * l * c⁻¹) * c := by group
      _ = l' * c := rfl
      _ = l * c := by rw [hl'l]
  have hc_fix : ∀ e ∈ E, c e = e := by
    let Fix : Subgroup V :=
      { carrier := {v : V | c v = v}
        one_mem' := by show c 1 = 1; rw [map_one]
        mul_mem' := fun {a b} ha hb => by
          show c (a * b) = a * b
          have ha' : c a = a := ha
          have hb' : c b = b := hb
          rw [map_mul, ha', hb']
        inv_mem' := fun {a} ha => by
          show c a⁻¹ = a⁻¹
          have ha' : c a = a := ha
          rw [map_inv, ha'] }
    have hFix_sub : commSub E L ≤ Fix := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, e, he, rfl⟩
      show c (x e * e⁻¹) = x e * e⁻¹
      have hxc : c * x = x * c := hcent x hx
      have h1 : c (x e) = x (c e) := by
        have := congrArg (fun z : MulAut V => z e) hxc
        simpa [MulAut.mul_apply] using this
      have hzE : c e * e⁻¹ ∈ E := E.mul_mem (hcE e he) (E.inv_mem he)
      have hzZ : c e * e⁻¹ ∈ Z := by
        refine (D.θ_ker ⟨c e * e⁻¹, hzE⟩).1 ?_
        have h2 : (⟨c e * e⁻¹, hzE⟩ : ↥E) = ⟨c e, hcE e he⟩ * (⟨e, he⟩ : ↥E)⁻¹ :=
          Subtype.ext rfl
        rw [h2, map_mul, map_inv, hc_theta ⟨e, he⟩]
        exact mul_inv_cancel _
      have hzfix : x (c e * e⁻¹) = c e * e⁻¹ := (mem_fixV.1 (hZF hzZ)) x hx
      have key : x (c e) * (c e)⁻¹ = x e * e⁻¹ := by
        have hce : c e = (c e * e⁻¹) * e := by group
        have hxce : x (c e) = (c e * e⁻¹) * x e := by
          conv_lhs => rw [hce]
          rw [map_mul, hzfix]
        have hcinv : (c e)⁻¹ = e⁻¹ * (c e * e⁻¹)⁻¹ := by
          conv_lhs => rw [hce, mul_inv_rev]
        rw [hxce, hcinv]
        rw [mul_assoc, ← mul_assoc (x e) e⁻¹ ((c e * e⁻¹)⁻¹),
          mul_comm (x e * e⁻¹) ((c e * e⁻¹)⁻¹), ← mul_assoc, mul_inv_cancel, one_mul]
      calc c (x e * e⁻¹) = c (x e) * c (e⁻¹) := map_mul c _ _
        _ = c (x e) * (c e)⁻¹ := by rw [map_inv]
        _ = x (c e) * (c e)⁻¹ := by rw [h1]
        _ = x e * e⁻¹ := key
    have hEfix : E ≤ Fix := by
      rw [← h.perf]
      exact hFix_sub
    intro e he
    exact hEfix he
  refine ⟨P, hP, fun e he => ?_⟩
  have hgc : g = P * c := by
    show g = P * (P⁻¹ * g)
    group
  rw [hgc, MulAut.mul_apply, hc_fix e he]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

