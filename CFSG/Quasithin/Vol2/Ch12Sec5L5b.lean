module

public import CFSG.Quasithin.Vol2.Ch12Sec5L5a
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125St S125W Matrix

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)

namespace S125L5b

@[expose] def y1 : Fin 10 → ZMod 2 := Pi.single 2 1 + Pi.single 4 1

@[expose] def P13 : SL5 :=
  ⟨(Equiv.swap (1 : Fin 5) 3).permMatrix (ZMod 2), S125Aut.det_permMatrix _⟩

theorem wedge_P13 : JonesParshall.wedgeMat ((Equiv.swap (1 : Fin 5) 3).permMatrix (ZMod 2)) *ᵥ
    (Pi.single 0 1 + Pi.single 7 1) = y1 := by
  decide

theorem decodeV_one : Orbit.decodeV 1 = Pi.single 0 1 := by decide

theorem decodeV_129 : Orbit.decodeV 129 = Pi.single 0 1 + Pi.single 7 1 := by decide

theorem wedgeRep_mul (a b : SL5) (x : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep (a * b) x = JonesParshall.wedgeRep a (JonesParshall.wedgeRep b x) := by
  rw [map_mul, Module.End.mul_apply]

theorem wedgeRep_inv_apply (a : SL5) (x : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep a⁻¹ (JonesParshall.wedgeRep a x) = x := by
  rw [← wedgeRep_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_orbit {x : Fin 10 → ZMod 2} (hx : x ≠ 0) :
    ∃ g : SL5, JonesParshall.wedgeRep g (Pi.single 0 1) = x ∨
      JonesParshall.wedgeRep g y1 = x := by
  obtain ⟨g, hg⟩ := Orbit.exists_wedgeRep_base hx
  cases h : Orbit.clsV x
  · rw [h, Orbit.l52BaseC, ite_eq_right (by decide), decodeV_129] at hg
    refine ⟨g * P13⁻¹, Or.inr ?_⟩
    have hP : JonesParshall.wedgeRep P13 (Pi.single 0 1 + Pi.single 7 1) = y1 := by
      rw [S125ZV.wedgeRep_apply]
      exact wedge_P13
    rw [wedgeRep_mul, ← hP, wedgeRep_inv_apply, hg]
  · rw [h, Orbit.l52BaseC, ite_eq_left rfl, decodeV_one] at hg
    exact ⟨g, Or.inl hg⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem exists_l (F : Frame125 T L V) (g : SL5) :
    ∃ (l : G) (hlV : l ∈ Subgroup.normalizer (V : Set G)), l ∈ L ∧
      conjAct V ⟨l, hlV⟩ = ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) :=
  mem_autOn_iff_exists.mp (F.γ.symm g).2

omit [Finite G] in
theorem part2 (F : Frame125 T L V) :
    ∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ ∈ F.V1) ∨ ∃ l ∈ L, l * v * l⁻¹ = F.v1' := by
  intro v hv hv1
  set w : ↥V := ⟨v, hv⟩
  have hx : Multiplicative.toAdd (F.e w) ≠ 0 := by
    intro h
    apply hv1
    have : F.e w = 1 := Multiplicative.toAdd.injective (h.trans toAdd_one.symm)
    have := congrArg Subtype.val ((map_eq_one_iff F.e F.e.injective).1 this)
    exact this
  obtain ⟨g, hg | hg⟩ := exists_orbit hx
  · obtain ⟨l, hlV, hlL, hlh⟩ := exists_l F g
    left
    refine ⟨l⁻¹, L.inv_mem hlL, ?_⟩
    set v₀ : ↥V := F.e.symm (Multiplicative.ofAdd (Pi.single 0 1))
    have h1 : ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) v₀ = w := by
      apply F.e.injective
      rw [F.wedge, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, hg,
        ofAdd_toAdd]
    rw [← hlh] at h1
    have h2 : l * (v₀ : G) * l⁻¹ = v := congrArg Subtype.val h1
    have h3 : l⁻¹ * v * l⁻¹⁻¹ = v₀ := by
      rw [← h2]
      group
    rw [h3]
    refine (mem_sub_iff F {0} v₀).2 fun k hk => ?_
    rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact Pi.single_eq_of_ne (by simpa using hk) _
  · obtain ⟨l, hlV, hlL, hlh⟩ := exists_l F g
    right
    refine ⟨l⁻¹, L.inv_mem hlL, ?_⟩
    have h1 : ((F.γ.symm g : ↥(autOn L V)) : MulAut ↥V) F.w1' = w := by
      apply F.e.injective
      rw [F.wedge, MulEquiv.apply_symm_apply, Frame125.w1', MulEquiv.apply_symm_apply,
        toAdd_ofAdd]
      change Multiplicative.ofAdd (JonesParshall.wedgeRep g y1) = _
      rw [hg, ofAdd_toAdd]
    rw [← hlh] at h1
    have h2 : l * (F.w1' : G) * l⁻¹ = v := congrArg Subtype.val h1
    rw [Frame125.v1', ← h2]
    group

end S125L5b

end CFSG.Quasithin.H13
