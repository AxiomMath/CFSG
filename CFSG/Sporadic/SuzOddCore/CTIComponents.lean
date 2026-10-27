module

public import CFSG.Sporadic.SuzOddCore.CTIFirst
public import CFSG.Sporadic.SuzOddCore.CTISecond
public import CFSG.Sporadic.SuzOddCore.SmallModel

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG CFSG.LocalCores CFSG.Certificates CFSG.Monster.B.Co2

theorem center_map_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hx (e.symm g)
    have := congrArg e this
    simpa using this
  · intro hy
    refine ⟨e.symm y, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
    have := Subgroup.mem_center_iff.1 hy (e g)
    have := congrArg e.symm this
    simpa using this

theorem card_quotient_center_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (G ⧸ Subgroup.center G) = Nat.card (H ⧸ Subgroup.center H) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (center_map_equiv e)).toEquiv

theorem component_quotient_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {B : Subgroup G} (hB : IsComponent B) :
    IsComponent (B.map e.toMonoidHom) ∧
      Nat.card (B ⧸ Subgroup.center B) =
        Nat.card (B.map e.toMonoidHom ⧸ Subgroup.center (B.map e.toMonoidHom)) :=
  ⟨isComponent_map_mulEquiv e hB,
    card_quotient_center_equiv (B.equivMapOfInjective e.toMonoidHom e.injective)⟩

theorem centralizer_map_equiv {S : Type*} [Group S] (f : S ≃* suzM) (a : S) :
    (Subgroup.centralizer ({a} : Set S)).map (suzM.subtype.comp f.toMonoidHom) =
      suzM ⊓ Subgroup.centralizer {((f a : suzM) : Equiv.Perm (Fin 1782))} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(f x).2, ?_⟩
    have := congrArg (fun w => ((f w : suzM) : Equiv.Perm (Fin 1782))) hx
    simpa using this
  · rintro ⟨hyM, hyc⟩
    refine ⟨f.symm ⟨y, hyM⟩, ?_, by simp⟩
    apply f.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    exact hyc

theorem CTI_Suz_involution_local_components_simple_quotient_order
    {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Suz) (a : S) (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 20160 := by
  set f : S ≃* suzM := e.trans suzEquivM
  set a' : Equiv.Perm (Fin 1782) := ((f a : suzM) : Equiv.Perm (Fin 1782))
  have ha' : orderOf a' = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha]
  have hinj : Function.Injective (suzM.subtype.comp f.toMonoidHom) :=
    suzM.subtype_injective.comp f.injective
  have g1 : Subgroup.centralizer ({a} : Set S) ≃*
      (suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) :=
    ((Subgroup.centralizer ({a} : Set S)).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr (centralizer_map_equiv f a))
  obtain ⟨c, hc, h01⟩ := suzM_involution_class (f a).2 ha'
  have key : ∀ i < 4, c * suzInv i * c⁻¹ = a' →
      Nonempty ((suzM ⊓ Subgroup.centralizer {a'} : Subgroup (Equiv.Perm (Fin 1782))) ≃*
        invE i) := by
    intro i hi hca
    have hmap := map_conj_inf_centralizer (Γ := suzM) (c := c) (suzM_conj_iff hc) (suzInv i)
    rw [hca] at hmap
    have e2 := (Subgroup.equivMapOfInjective (suzM ⊓ Subgroup.centralizer {suzInv i})
      (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)
    have e3 : invE i = suzM ⊓ Subgroup.centralizer {suzInv i} := by
      rw [invE_eq_centM hi, centM, inf_comm]
    exact ⟨e2.symm.trans (MulEquiv.subgroupCongr e3.symm)⟩
  rcases h01 with h0 | h1
  · obtain ⟨g2⟩ := key 0 (by norm_num) h0
    set g := g1.trans g2
    obtain ⟨hB', hcard⟩ := component_quotient_of_equiv g hB
    rw [hcard]
    exact CTI_Suz_first_involution_local_component_simple_quotient_order _ hB'
  · obtain ⟨g2⟩ := key 1 (by norm_num) h1
    set g := g1.trans g2
    obtain ⟨hB', -⟩ := component_quotient_of_equiv g hB
    exact absurd hB' (CTI_Suz_second_involution_centralizer_has_no_components.2 _)

end CFSG.Sporadic.SuzOddCore
