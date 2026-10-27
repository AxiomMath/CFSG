module

public import CFSG.Quasithin.Background.F918D0
public import CFSG.Quasithin.SteinbergCBI16Alt6
public import CFSG.Quasithin.EmptyFaithful.F918C10

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.I16 CFSG.Quasithin.SteinbergCB.G2Two
  Equiv Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace D6Dual

open DnCoords

@[expose] def gram6 : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]

@[expose] def omega6 (u y : Fin 4 → ZMod 2) : ZMod 2 := (gram6 *ᵥ u) ⬝ᵥ y

private theorem gram6_mul_self (u : Fin 4 → ZMod 2) : gram6 *ᵥ (gram6 *ᵥ u) = u := by
  revert u
  decide +kernel

private theorem omega6_gens (i : Fin 2) (x y : Fin 4 → ZMod 2) :
    omega6 (coords6.actA (gens6 i) x) (coords6.actA (gens6 i) y) = omega6 x y := by
  obtain ⟨a, ha, rfl⟩ := toV_surj x
  obtain ⟨b, hb, rfl⟩ := toV_surj y
  rw [act6 i a ha, act6 i b hb]
  revert i a b
  decide +kernel

theorem omega6_actA (γ : ↥(alternatingGroup (Fin 6))) (x y : Fin 4 → ZMod 2) :
    omega6 (coords6.actA γ x) (coords6.actA γ y) = omega6 x y := by
  let S : Subgroup ↥(alternatingGroup (Fin 6)) :=
    { carrier := {γ | ∀ x y, omega6 (coords6.actA γ x) (coords6.actA γ y) = omega6 x y}
      one_mem' := fun x y => by simp only [map_one]; rfl
      mul_mem' := fun {a b} ha hb x y => by
        have h1 : ∀ z, coords6.actA (a * b) z = coords6.actA a (coords6.actA b z) := fun z => by
          rw [map_mul]
          rfl
        simp only [h1]
        rw [ha, hb]
      inv_mem' := fun {a} ha x y => by
        have h1 : ∀ z, coords6.actA a (coords6.actA a⁻¹ z) = z := fun z => by
          have : coords6.actA a * coords6.actA a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
          exact congrArg (fun f : AddMonoid.End (Fin 4 → ZMod 2) => f z) this
        have := ha (coords6.actA a⁻¹ x) (coords6.actA a⁻¹ y)
        rw [h1, h1] at this
        exact this.symm }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← closure_gens6]
    exact (Subgroup.closure_le S).mpr (Set.range_subset_iff.mpr fun i x y => omega6_gens i x y)
  have hγ : γ ∈ S := by rw [hS]; trivial
  exact hγ x y

@[expose] def dotDual (u : Fin 4 → ZMod 2) : Module.Dual (ZMod 2) (Fin 4 → ZMod 2) where
  toFun x := u ⬝ᵥ x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

private theorem dotDual_apply (u x : Fin 4 → ZMod 2) : dotDual u x = u ⬝ᵥ x := rfl

@[expose] def dualVec (l : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) : Fin 4 → ZMod 2 :=
  fun i => l (Pi.single i 1)

private theorem dotDual_dualVec (l : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) : dotDual (dualVec l) = l := by
  apply LinearMap.ext
  intro x
  rw [dotDual_apply]
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ l x]
  have hs : ∀ i : Fin 4, (fun j : Fin 4 => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [hs, dotProduct, dualVec, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem dualVec_dotDual (u : Fin 4 → ZMod 2) : dualVec (dotDual u) = u := by
  funext i
  simp [dualVec, dotDual_apply, dotProduct_single]

@[expose] def dualEquiv : Module.Dual (ZMod 2) (Fin 4 → ZMod 2) ≃+ (Fin 4 → ZMod 2) where
  toFun l := gram6 *ᵥ dualVec l
  invFun u := dotDual (gram6 *ᵥ u)
  left_inv l := by
    simp only [gram6_mul_self]
    exact dotDual_dualVec l
  right_inv u := by
    simp only [dualVec_dotDual]
    exact gram6_mul_self u
  map_add' a b := by
    simp only [← mulVec_add]
    rfl

private theorem dualEquiv_symm_apply (u x : Fin 4 → ZMod 2) : dualEquiv.symm u x = omega6 u x := rfl

@[expose] noncomputable def repD6 :
    Representation (ZMod 2) ↥(alternatingGroup (Fin 6)) (Fin 4 → ZMod 2) where
  toFun γ := AddMonoidHom.toZModLinearMap 2 (coords6.actA γ)
  map_one' := LinearMap.ext fun x => by
    show coords6.actA 1 x = x
    rw [map_one]
    rfl
  map_mul' γ δ := LinearMap.ext fun x => by
    show coords6.actA (γ * δ) x = coords6.actA γ (coords6.actA δ x)
    rw [map_mul]
    rfl

private theorem repD6_apply (γ : ↥(alternatingGroup (Fin 6))) (x : Fin 4 → ZMod 2) :
    repD6 γ x = coords6.actA γ x := rfl

private theorem dualEquiv_equivariant (γ : ↥(alternatingGroup (Fin 6)))
    (l : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) :
    dualEquiv ((Representation.dual repD6) γ l) = coords6.actA γ (dualEquiv l) := by
  apply dualEquiv.symm.injective
  rw [AddEquiv.symm_apply_apply]
  apply LinearMap.ext
  intro x
  have hl : l = dualEquiv.symm (dualEquiv l) := (dualEquiv.symm_apply_apply l).symm
  set u := dualEquiv l with hu
  rw [dualEquiv_symm_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, repD6_apply, hl, dualEquiv_symm_apply]
  have h1 : coords6.actA γ (coords6.actA γ⁻¹ x) = x := by
    have : coords6.actA γ * coords6.actA γ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun f : AddMonoid.End (Fin 4 → ZMod 2) => f x) this
  conv_rhs => rw [← h1]
  exact (omega6_actA γ u (coords6.actA γ⁻¹ x)).symm

theorem finrank_H1_dual_repD6 :
    Module.finrank (ZMod 2) (H1 (Representation.dual repD6)) = 1 := by
  have : Finite (Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) := Finite.of_equiv _ dualEquiv.symm.toEquiv
  have hcard := card_H1_eq_of_card (Representation.dual repD6) (θ := MulEquiv.refl _)
    (β := dualEquiv) (μ := coords6.actA) (fun γ l => dualEquiv_equivariant γ l) (k := 2) card_Z1A_6
  exact finrank_H1_of_card _ (by rw [hcard]; norm_num)

end D6Dual

open D6Dual in
theorem asI161A6_of : AsI161A6 := by
  intro W _ _ hexp L V hinv hcomm hnat
  obtain ⟨π, hπs, hZV, -, -, hZinv, hsec, hkerD, β, hβs, hβk, hβe⟩ := hnat
  let β' : ↥V →* Multiplicative (Fin 4 → ZMod 2) := coords6.secEquiv.toMonoidHom.comp β
  have hβ's : Function.Surjective β' := coords6.secEquiv.surjective.comp hβs
  have hβ'k : ∀ v : ↥V, β' v = 1 ↔ (v : W) ∈ V ⊓ fixV L := by
    intro v
    rw [← hβk v]
    exact (coords6.secEquiv.map_eq_one_iff (x := β v))
  have hβ'e : ∀ (γ : ↥(alternatingGroup (Fin 6))) (v : ↥V) (hv : (π γ : MulAut W) (v : W) ∈ V),
      β' ⟨(π γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (repD6 γ (Multiplicative.toAdd (β' v))) := by
    intro γ v hv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β v)
    have hm' : (FFModel.altDn 6).act γ m.1 ∈ (FFModel.altDn 6).sec := hsec γ m m.2
    have h1 := hβe γ v m hv hm' hm.symm
    have h2 : β' ⟨(π γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (coords6.proj (DnCoords.secVec ⟨(FFModel.altDn 6).act γ m.1, hm'⟩)) := by
      show coords6.secEquiv (β ⟨(π γ : MulAut W) (v : W), hv⟩) = _
      rw [h1]
      rfl
    have h3 : β' v = Multiplicative.ofAdd (coords6.proj (DnCoords.secVec m)) := by
      show coords6.secEquiv (β v) = _
      rw [← hm]
      rfl
    rw [h2, h3]
    show _ = Multiplicative.ofAdd (coords6.actA γ (coords6.proj (DnCoords.secVec m)))
    congr 1
    exact (coords6.act_proj (γ : Equiv.Perm (Fin 6)) (DnCoords.sum_secVec m)).symm
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(alternatingGroup (Fin 6))) hexp L V (V ⊓ fixV L) hZV
    (fun z hz x hx => hz.2 x hx) hinv hcomm π hπs repD6 β' hβ's hβ'k hβ'e
  rw [finrank_H1_dual_repD6] at hcard
  simpa using hcard

end CFSG.Quasithin
