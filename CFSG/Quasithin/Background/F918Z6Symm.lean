module

public import CFSG.Quasithin.Background.F918Z6Def
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Conj

variable {V : Type} [CommGroup V]

noncomputable def conjEquivOfEq {D X : Subgroup (MulAut V)} {s : MulAut V}
    (h : X = D.map (MulAut.conj s).toMonoidHom) : ↥D ≃* ↥X :=
  (Subgroup.equivMapOfInjective D (MulAut.conj s).toMonoidHom (MulAut.conj s).injective).trans
    (MulEquiv.subgroupCongr h.symm)

theorem sqtkGroup_of_mulEquiv_z6 {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : SQTKGroup A) : SQTKGroup B := by
  refine ⟨fun p hp hp2 => ?_, h.2.of_mulEquiv e.symm⟩
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 2 := h.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 2
  omega

theorem map_conj_map_conj_z6 (D : Subgroup (MulAut V)) (g s : MulAut V) :
    (D.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      D.map (MulAut.conj (g * s)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

end Conj

section Symm

variable {V : Type} [CommGroup V] [Finite V]

theorem Z37.symm {D X G T' : Subgroup (MulAut V)} {s : MulAut V} (h : Z37 D X G T' s) :
    Z37 X D G T' s := by
  have e : ↥D ≃* ↥X := conjEquivOfEq h.swapDX
  have : IsSimpleGroup ↥D := h.simple
  refine
    { exp := h.exp
      nontrivial := h.nontrivial
      simple := MulEquiv.isSimpleGroup e.symm
      nonab := ?_
      typeD := a38Types_congr e h.typeD
      sqtkD := sqtkGroup_of_mulEquiv_z6 e h.sqtkD
      comm := fun g hg x hx => (h.comm x hx g hg).symm
      swapDX := h.swapXD
      swapXD := h.swapDX
      s_mem := h.s_mem
      DX_le := by rw [sup_comm X D]; exact h.DX_le
      G_eq := by rw [sup_comm X D]; exact h.G_eq
      DX_norm := by rw [sup_comm X D]; exact h.DX_norm
      T_perm := ?_
      T_sylow := h.T_sylow
      irr := by rw [sup_comm X D]; exact h.irr
      qhat := h.qhat }
  · obtain ⟨a, ha, b, hb, hab⟩ := h.nonab
    refine ⟨((e ⟨a, ha⟩ : ↥X) : MulAut V), (e ⟨a, ha⟩).2, ((e ⟨b, hb⟩ : ↥X) : MulAut V),
      (e ⟨b, hb⟩).2, fun hc => hab ?_⟩
    have h1 : e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ := Subtype.ext hc
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  · intro g hg
    have hgs : g * s ∈ T' := T'.mul_mem hg h.s_mem
    have hx : X.map (MulAut.conj g).toMonoidHom = D.map (MulAut.conj (g * s)).toMonoidHom := by
      rw [h.swapDX, map_conj_map_conj_z6]
    rw [hx]
    rcases h.T_perm (g * s) hgs with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1

end Symm

end CFSG.Quasithin
