module

public import CFSG.Quasithin.Background.F918D0
public import CFSG.Quasithin.SteinbergCBI16Alt5
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.I16 CFSG.Quasithin.SteinbergCB.G2Two
  Equiv Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace D5Dual

open DnCoords

@[expose] def gram5 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]

@[expose] def omega5 (u y : Fin 4 → ZMod 2) : ZMod 2 := (gram5 *ᵥ u) ⬝ᵥ y

private theorem gram5_mul_self (u : Fin 4 → ZMod 2) : gram5 *ᵥ (gram5 *ᵥ u) = u := by
  revert u
  decide +kernel

private theorem omega5_gens (i : Fin 2) (x y : Fin 4 → ZMod 2) :
    omega5 (coords5.actA (gens5 i) x) (coords5.actA (gens5 i) y) = omega5 x y := by
  obtain ⟨a, ha, rfl⟩ := toV_surj x
  obtain ⟨b, hb, rfl⟩ := toV_surj y
  rw [act5 i a ha, act5 i b hb]
  revert i a b
  decide +kernel

theorem omega5_actA (γ : ↥(alternatingGroup (Fin 5))) (x y : Fin 4 → ZMod 2) :
    omega5 (coords5.actA γ x) (coords5.actA γ y) = omega5 x y := by
  let S : Subgroup ↥(alternatingGroup (Fin 5)) :=
    { carrier := {γ | ∀ x y, omega5 (coords5.actA γ x) (coords5.actA γ y) = omega5 x y}
      one_mem' := fun x y => by simp only [map_one]; rfl
      mul_mem' := fun {a b} ha hb x y => by
        have h1 : ∀ z, coords5.actA (a * b) z = coords5.actA a (coords5.actA b z) := fun z => by
          rw [map_mul]
          rfl
        simp only [h1]
        rw [ha, hb]
      inv_mem' := fun {a} ha x y => by
        have h1 : ∀ z, coords5.actA a (coords5.actA a⁻¹ z) = z := fun z => by
          have : coords5.actA a * coords5.actA a⁻¹ = 1 := by
            rw [← map_mul, mul_inv_cancel, map_one]
          exact congrArg (fun f : AddMonoid.End (Fin 4 → ZMod 2) => f z) this
        have := ha (coords5.actA a⁻¹ x) (coords5.actA a⁻¹ y)
        rw [h1, h1] at this
        exact this.symm }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← closure_gens5]
    exact (Subgroup.closure_le S).mpr (Set.range_subset_iff.mpr fun i x y => omega5_gens i x y)
  have hγ : γ ∈ S := by rw [hS]; trivial
  exact hγ x y

@[expose] def dotDual (u : Fin 4 → ZMod 2) : Module.Dual (ZMod 2) (Fin 4 → ZMod 2) where
  toFun x := u ⬝ᵥ x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

private theorem dotDual_apply (u x : Fin 4 → ZMod 2) : dotDual u x = u ⬝ᵥ x := rfl

@[expose] def dualVec (l : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) : Fin 4 → ZMod 2 :=
  fun i => l (Pi.single i 1)

private theorem dotDual_dualVec (l : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) :
    dotDual (dualVec l) = l := by
  apply LinearMap.ext
  intro x
  rw [dotDual_apply]
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ l x]
  have hs : ∀ i : Fin 4, (fun j : Fin 4 => if i = j then (1 : ZMod 2) else 0) =
      Pi.single i 1 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [hs, dotProduct, dualVec, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem dualVec_dotDual (u : Fin 4 → ZMod 2) : dualVec (dotDual u) = u := by
  funext i
  simp [dualVec, dotDual_apply, dotProduct_single]

@[expose] def dualEquiv : Module.Dual (ZMod 2) (Fin 4 → ZMod 2) ≃+ (Fin 4 → ZMod 2) where
  toFun l := gram5 *ᵥ dualVec l
  invFun u := dotDual (gram5 *ᵥ u)
  left_inv l := by
    simp only [gram5_mul_self]
    exact dotDual_dualVec l
  right_inv u := by
    simp only [dualVec_dotDual]
    exact gram5_mul_self u
  map_add' a b := by
    simp only [← mulVec_add]
    rfl

private theorem dualEquiv_symm_apply (u x : Fin 4 → ZMod 2) :
    dualEquiv.symm u x = omega5 u x := rfl

@[expose] noncomputable def repD5 :
    Representation (ZMod 2) ↥(alternatingGroup (Fin 5)) (Fin 4 → ZMod 2) where
  toFun γ := AddMonoidHom.toZModLinearMap 2 (coords5.actA γ)
  map_one' := LinearMap.ext fun x => by
    show coords5.actA 1 x = x
    rw [map_one]
    rfl
  map_mul' γ δ := LinearMap.ext fun x => by
    show coords5.actA (γ * δ) x = coords5.actA γ (coords5.actA δ x)
    rw [map_mul]
    rfl

private theorem repD5_apply (γ : ↥(alternatingGroup (Fin 5))) (x : Fin 4 → ZMod 2) :
    repD5 γ x = coords5.actA γ x := rfl

private theorem dualEquiv_equivariant (γ : ↥(alternatingGroup (Fin 5)))
    (l : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) :
    dualEquiv ((Representation.dual repD5) γ l) = coords5.actA γ (dualEquiv l) := by
  apply dualEquiv.symm.injective
  rw [AddEquiv.symm_apply_apply]
  apply LinearMap.ext
  intro x
  have hl : l = dualEquiv.symm (dualEquiv l) := (dualEquiv.symm_apply_apply l).symm
  set u := dualEquiv l with hu
  rw [dualEquiv_symm_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, repD5_apply, hl, dualEquiv_symm_apply]
  have h1 : coords5.actA γ (coords5.actA γ⁻¹ x) = x := by
    have : coords5.actA γ * coords5.actA γ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : AddMonoid.End (Fin 4 → ZMod 2) => f x) this
  conv_rhs => rw [← h1]
  exact (omega5_actA γ u (coords5.actA γ⁻¹ x)).symm

theorem finrank_H1_dual_repD5 :
    Module.finrank (ZMod 2) (H1 (Representation.dual repD5)) = 0 :=
  finrank_H1_alternatingNatural_five
    (coords5.alternatingNatural_of_intertwiner (θ := MulEquiv.refl _) (e := dualEquiv)
      fun γ l => dualEquiv_equivariant γ l)

end D5Dual

open D5Dual in
theorem card_fixV_le_one_of_altD5 {W : Type} [CommGroup W] [Finite W]
    (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) (V : Subgroup W)
    (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hcomm : XMod.commOf ↥L V = V)
    (hnat : AlternatingNatural L V (V ⊓ fixV L) 5) : Nat.card ↥(V ⊓ fixV L) ≤ 1 := by
  obtain ⟨π, hπs, hZV, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hnat
  let β' : ↥V →* Multiplicative (Fin 4 → ZMod 2) := coords5.secEquiv.toMonoidHom.comp β
  have hβ's : Function.Surjective β' := coords5.secEquiv.surjective.comp hβs
  have hβ'k : ∀ v : ↥V, β' v = 1 ↔ (v : W) ∈ V ⊓ fixV L := by
    intro v
    rw [← hβk v]
    exact (coords5.secEquiv.map_eq_one_iff (x := β v))
  have hβ'e : ∀ (γ : ↥(alternatingGroup (Fin 5))) (v : ↥V)
      (hv : (π γ : MulAut W) (v : W) ∈ V),
      β' ⟨(π γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (repD5 γ (Multiplicative.toAdd (β' v))) := by
    intro γ v hv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β v)
    have hm' : (FFModel.altDn 5).act γ m.1 ∈ (FFModel.altDn 5).sec := hsec γ m m.2
    have h1 := hβe γ v m hv hm' hm.symm
    have h2 : β' ⟨(π γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd
          (coords5.proj (DnCoords.secVec ⟨(FFModel.altDn 5).act γ m.1, hm'⟩)) := by
      show coords5.secEquiv (β ⟨(π γ : MulAut W) (v : W), hv⟩) = _
      rw [h1]
      rfl
    have h3 : β' v = Multiplicative.ofAdd (coords5.proj (DnCoords.secVec m)) := by
      show coords5.secEquiv (β v) = _
      rw [← hm]
      rfl
    rw [h2, h3]
    show _ = Multiplicative.ofAdd (coords5.actA γ (coords5.proj (DnCoords.secVec m)))
    congr 1
    exact (coords5.act_proj (γ : Equiv.Perm (Fin 5)) (DnCoords.sum_secVec m)).symm
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(alternatingGroup (Fin 5))) hexp L V
    (V ⊓ fixV L) hZV (fun z hz x hx => hz.2 x hx) hinv hcomm π hπs repD5 β' hβ's hβ'k hβ'e
  rw [finrank_H1_dual_repD5] at hcard
  simpa using hcard

end CFSG.Quasithin
