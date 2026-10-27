module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MTriples
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16c2m_exists_pair {W : Type} [CommGroup W] {J : Subgroup W} {ζ : MulAut W}
    (hsup : J ⊔ J.map ζ.toMonoidHom = ⊤) (w : W) :
    ∃ u v : ↥J, w = (u : W) * ζ (v : W) := by
  have hw : w ∈ J ⊔ J.map ζ.toMonoidHom := by
    rw [hsup]
    exact Subgroup.mem_top w
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hc
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

theorem s16c2m_pair_unique {W : Type} [CommGroup W] {J : Subgroup W} {ζ : MulAut W}
    (hd : Disjoint J (J.map ζ.toMonoidHom)) {u v u' v' : ↥J}
    (h : (u : W) * ζ (v : W) = (u' : W) * ζ (v' : W)) : u = u' ∧ v = v' := by
  have key : (u : W) * (u' : W)⁻¹ = ζ ((v' : W) * (v : W)⁻¹) := by
    rw [map_mul, map_inv]
    calc (u : W) * (u' : W)⁻¹ = ((u : W) * ζ (v : W)) * ((u' : W)⁻¹ * (ζ (v : W))⁻¹) := by
          rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
      _ = ((u' : W) * ζ (v' : W)) * ((u' : W)⁻¹ * (ζ (v : W))⁻¹) := by rw [h]
      _ = ζ (v' : W) * (ζ (v : W))⁻¹ := by
          rw [mul_mul_mul_comm, mul_inv_cancel, one_mul]
  have h1 : (u : W) * (u' : W)⁻¹ ∈ J ⊓ J.map ζ.toMonoidHom :=
    ⟨J.mul_mem u.2 (J.inv_mem u'.2),
      ⟨(v' : W) * (v : W)⁻¹, J.mul_mem v'.2 (J.inv_mem v.2), key.symm⟩⟩
  rw [disjoint_iff.1 hd, Subgroup.mem_bot, mul_inv_eq_one] at h1
  have hu : u = u' := Subtype.ext h1
  subst hu
  have h2 : ζ (v : W) = ζ (v' : W) := mul_left_cancel h
  exact ⟨rfl, Subtype.ext (ζ.injective h2)⟩

theorem s16c2m_pair_model {W : Type} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {J : Subgroup W} {ζ : MulAut W} (hd : Disjoint J (J.map ζ.toMonoidHom))
    (hsup : J ⊔ J.map ζ.toMonoidHom = ⊤) :
    ∃ ψ : W ≃* ↥(s16c2m_Triples ↥J), ∀ (u v : ↥J) (j : Fin 3),
      (ψ ((u : W) * ζ (v : W))).1 j = (if j = 0 then 1 else u) * (if j = 1 then 1 else v) := by
  let Φ : ↥J × ↥J →* W :=
    { toFun := fun p => (p.1 : W) * ζ (p.2 : W)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  have hinj : Function.Injective Φ := by
    intro p q h
    obtain ⟨h1, h2⟩ := s16c2m_pair_unique hd h
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective Φ := by
    intro w
    obtain ⟨u, v, rfl⟩ := s16c2m_exists_pair hsup w
    exact ⟨(u, v), rfl⟩
  let e : ↥J × ↥J ≃* W := MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hu2 : ∀ u : ↥J, u * u = 1 := fun u => Subtype.ext (by simpa [sq] using hW u)
  have hinv : ∀ u : ↥J, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (hu2 u)
  refine ⟨((s16c2m_tripleEquiv ↥J).trans (MulEquiv.prodComm.trans e)).symm, ?_⟩
  intro u v j
  have hev : e (u, v) = (u : W) * ζ (v : W) := rfl
  have h1 : ((s16c2m_tripleEquiv ↥J).trans (MulEquiv.prodComm.trans e)).symm
      ((u : W) * ζ (v : W)) = (s16c2m_tripleEquiv ↥J).symm (v, u) := by
    rw [← hev]
    simp
  rw [h1]
  fin_cases j
  · simp [s16c2m_tripleEquiv]
  · simp [s16c2m_tripleEquiv]
  · simp [s16c2m_tripleEquiv, mul_inv_rev, hinv]
    exact mul_comm v u

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
