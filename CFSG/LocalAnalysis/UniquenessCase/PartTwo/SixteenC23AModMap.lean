module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC

variable {V : Type} [CommGroup V]

theorem c23a_fixV_map (L : Subgroup (MulAut V)) (φ : MulAut V) :
    fixV (L.map (MulAut.conj φ).toMonoidHom) = (fixV L).map φ.toMonoidHom :=
  fixV_map_conj_eq L φ

theorem c23a_commSub_map (E : Subgroup V) (L : Subgroup (MulAut V)) (φ : MulAut V) :
    commSub (E.map φ.toMonoidHom) (L.map (MulAut.conj φ).toMonoidHom) =
      (commSub E L).map φ.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, w', ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨c₀, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj φ).toMonoidHom x, ⟨x, hx, rfl⟩, φ w, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]

theorem c23a_block_map {L : Subgroup (MulAut V)} {E Z : Subgroup V} (h : C23ABlock L E Z)
    (φ : MulAut V) :
    C23ABlock (L.map (MulAut.conj φ).toMonoidHom) (E.map φ.toMonoidHom)
      (Z.map φ.toMonoidHom) := by
  have hperf : commSub (E.map φ.toMonoidHom) (L.map (MulAut.conj φ).toMonoidHom) =
      E.map φ.toMonoidHom := by
    rw [c23a_commSub_map, h.perf]
  have hfix : (Z.map φ.toMonoidHom) =
      E.map φ.toMonoidHom ⊓ fixV (L.map (MulAut.conj φ).toMonoidHom) := by
    rw [h.fix, Subgroup.map_inf E (fixV L) φ.toMonoidHom φ.injective,
      ← c23a_fixV_map L φ]
  refine ⟨?_, hperf, hfix⟩
  obtain ⟨N⟩ := h.nat
  let ρ' : SL3F2 →* ↥(L.map (MulAut.conj φ).toMonoidHom) :=
    { toFun := fun g => ⟨MulAut.conj φ (N.ρ g),
        Subgroup.mem_map.mpr ⟨N.ρ g, (N.ρ g).2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g k => by
        apply Subtype.ext
        show MulAut.conj φ ((N.ρ (g * k) : ↥L) : MulAut V) =
          MulAut.conj φ ((N.ρ g : ↥L) : MulAut V) *
            MulAut.conj φ ((N.ρ k : ↥L) : MulAut V)
        rw [map_mul N.ρ g k, Subgroup.coe_mul, map_mul] }
  let θ' : ↥(E.map φ.toMonoidHom) →* Multiplicative (Fin 3 → ZMod 2) :=
    { toFun := fun u => N.θ ⟨φ.symm (u : V),
        (Subgroup.mem_map_equiv (f := φ) (K := E)).mp u.2⟩
      map_one' := by
        change N.θ ⟨φ.symm (1 : V), _⟩ = 1
        rw [show (⟨φ.symm (1 : V), _⟩ : ↥E) = 1 from Subtype.ext (map_one φ.symm)]
        simp
      map_mul' := fun u w => by
        change N.θ ⟨φ.symm ((u * w : ↥(E.map φ.toMonoidHom)) : V), _⟩ =
          N.θ ⟨φ.symm (u : V), _⟩ * N.θ ⟨φ.symm (w : V), _⟩
        rw [show (⟨φ.symm ((u * w : ↥(E.map φ.toMonoidHom)) : V), _⟩ : ↥E) =
            ⟨φ.symm (u : V), _⟩ * ⟨φ.symm (w : V), _⟩ from
          Subtype.ext (by
            show (MulEquiv.symm φ) ((u : V) * (w : V)) =
              (MulEquiv.symm φ) (u : V) * (MulEquiv.symm φ) (w : V)
            exact map_mul φ.symm _ _)]
        rw [map_mul] }
  have hρ : ∀ g : SL3F2, (ρ' g : MulAut V) = φ * (N.ρ g : MulAut V) * φ⁻¹ := by
    intro g
    show MulAut.conj φ (N.ρ g : MulAut V) = φ * (N.ρ g : MulAut V) * φ⁻¹
    rfl
  refine ⟨{ ρ := ρ'
            surj := ?_
            inj := ?_
            θ := θ'
            θ_surj := ?_
            θ_ker := ?_
            inv := ?_
            equiv := ?_ }⟩
  · intro x
    obtain ⟨l, hl_mem, hl⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨g, hg⟩ := N.surj ⟨l, hl_mem⟩
    refine ⟨g, Subtype.ext ?_⟩
    show MulAut.conj φ (N.ρ g : MulAut V) = (x : MulAut V)
    rw [hg]
    simpa using hl
  · intro g k h
    exact N.inj (Subtype.ext ((MulAut.conj φ).injective (congrArg Subtype.val h)))
  · intro y
    obtain ⟨u₀, hu₀⟩ := N.θ_surj y
    refine ⟨⟨φ u₀, Subgroup.mem_map.mpr ⟨u₀, u₀.2, rfl⟩⟩, ?_⟩
    show N.θ ⟨φ.symm (φ (u₀ : V)), _⟩ = y
    rw [show (⟨φ.symm (φ (u₀ : V)), _⟩ : ↥E) = u₀ from
      Subtype.ext (φ.symm_apply_apply (u₀ : V))]
    exact hu₀
  · intro u
    change N.θ ⟨φ.symm (u : V), _⟩ = 1 ↔ (u : V) ∈ Z.map φ.toMonoidHom
    rw [N.θ_ker]
    exact (Subgroup.mem_map_equiv (f := φ) (K := Z)).symm
  · intro g u hu
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hu
    have hφe : φ.toMonoidHom e = φ e := rfl
    rw [hρ g, hφe]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    exact Subgroup.mem_map.mpr ⟨(N.ρ g : MulAut V) e, N.inv g e he, rfl⟩
  · intro g u
    have hmem : ((ρ' g : MulAut V)) (u : V) ∈ E.map φ.toMonoidHom := by
      have h1 : ((ρ' g : MulAut V)) (u : V) =
          φ ((N.ρ g : MulAut V) (φ.symm (u : V))) := by
        rw [hρ g]
        simp [MulAut.mul_apply, MulAut.inv_apply_self]
      rw [h1]
      exact Subgroup.mem_map.mpr ⟨(N.ρ g : MulAut V) (φ.symm (u : V)),
        N.inv g (φ.symm (u : V))
          ((Subgroup.mem_map_equiv (f := φ) (K := E)).mp u.2), rfl⟩
    have hval : φ.symm (((ρ' g : MulAut V)) (u : V)) =
        (N.ρ g : MulAut V) (φ.symm (u : V)) := by
      rw [hρ g]
      simp [MulAut.mul_apply, MulAut.inv_apply_self]
    have harg : (⟨φ.symm (((ρ' g : MulAut V)) (u : V)),
        (Subgroup.mem_map_equiv (f := φ) (K := E)).mp hmem⟩ : ↥E) =
        ⟨(N.ρ g : MulAut V) (φ.symm (u : V)),
          N.inv g (φ.symm (u : V))
            ((Subgroup.mem_map_equiv (f := φ) (K := E)).mp u.2)⟩ :=
      Subtype.ext hval
    show θ' ⟨((ρ' g : MulAut V)) (u : V), hmem⟩ =
      Multiplicative.ofAdd (g • Multiplicative.toAdd (θ' u))
    rw [show θ' ⟨((ρ' g : MulAut V)) (u : V), hmem⟩ =
        N.θ ⟨φ.symm (((ρ' g : MulAut V)) (u : V)),
          (Subgroup.mem_map_equiv (f := φ) (K := E)).mp hmem⟩ from rfl]
    rw [harg]
    rw [show θ' u = N.θ ⟨φ.symm (u : V),
        (Subgroup.mem_map_equiv (f := φ) (K := E)).mp u.2⟩ from rfl]
    exact N.equiv g ⟨φ.symm (u : V),
      (Subgroup.mem_map_equiv (f := φ) (K := E)).mp u.2⟩

theorem c23a_apply_mem_commSub_top {L L' : Subgroup (MulAut V)} {φ : MulAut V}
    (h : L.map (MulAut.conj φ).toMonoidHom = L') {e : V} (he : e ∈ commSub ⊤ L) :
    φ e ∈ commSub ⊤ L' := by
  have h1 := c23a_commSub_map ⊤ L φ
  rw [Subgroup.map_top_of_surjective _ φ.surjective, h] at h1
  rw [h1]
  exact ⟨e, he, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
