module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.Lift

section Map

variable {C C' : Type} [Group C] [Group C'] (e : C ≃* C')

theorem map_aut_apply (φ : MulAut C') (x : C) : φ (e x) = e (((MulAut.congr e).symm φ) x) := by
  have h : ∀ ψ : MulAut C, (MulAut.congr e ψ) (e x) = e (ψ x) := fun ψ => by
    simp [MulAut.congr_apply]
  have := h ((MulAut.congr e).symm φ)
  rw [MulEquiv.apply_symm_apply] at this
  exact this

theorem map_aut_mem_autStab {S : Subgroup C} {φ : MulAut C'}
    (h : φ ∈ autStab (S.map e.toMonoidHom)) : (MulAut.congr e).symm φ ∈ autStab S := by
  rw [autStab_map, Subgroup.mem_map_equiv] at h
  exact h

theorem map_centralizer_le_iff (R : Subgroup C) (z : C) :
    Subgroup.centralizer ({e z} : Set C') ≤ R.map e.toMonoidHom ↔
      Subgroup.centralizer ({z} : Set C) ≤ R := by
  have := centralizer_le_transport e (R := R) (R' := R.map e.toMonoidHom) rfl (e z)
  rw [MulEquiv.symm_apply_apply] at this
  exact this.symm

theorem stdTwo_map {U P P' : Subgroup C} {z t : C} (S : StdTwo C U P P' z t) :
    StdTwo C' (U.map e.toMonoidHom) (P.map e.toMonoidHom) (P'.map e.toMonoidHom) (e z) (e t) where
  z_mem := ⟨z, S.z_mem, rfl⟩
  t_mem := ⟨t, S.t_mem, rfl⟩
  z_two := by rw [MulEquiv.orderOf_eq, S.z_two]
  t_two := by rw [MulEquiv.orderOf_eq, S.t_two]
  cls x hx := by
    have h2 : orderOf (e.symm x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
    rcases S.cls _ h2 with h | h
    · left
      simpa using e.toMonoidHom.map_isConj h
    · right
      simpa using e.toMonoidHom.map_isConj h
  noconj φ hφ := by
    apply S.noconj ((MulAut.congr e).symm φ)
    apply e.injective
    rw [← map_aut_apply, hφ]
  center := by
    rintro _ ⟨w, hw, rfl⟩ hc hw1
    obtain ⟨h, hh, hhw⟩ := S.center w hw (fun y hy => e.injective (by
      rw [map_mul, map_mul]
      exact hc (e y) ⟨y, hy, rfl⟩)) (fun h => hw1 (by rw [MulEquiv.coe_toMonoidHom, h, map_one]))
    refine ⟨e h, ⟨⟨h, (Subgroup.mem_inf.1 hh).1, rfl⟩, ⟨h, (Subgroup.mem_inf.1 hh).2, rfl⟩⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hhw]
    rfl
  aut_z φ h1 h2 := by
    obtain ⟨b, hb, hbz⟩ := S.aut_z _ (map_aut_mem_autStab e h1) (map_aut_mem_autStab e h2)
    refine ⟨e b, ⟨⟨b, (Subgroup.mem_inf.1 hb).1, rfl⟩, ⟨b, (Subgroup.mem_inf.1 hb).2, rfl⟩⟩, ?_⟩
    rw [map_aut_apply e φ z, hbz, map_mul, map_mul, map_inv]
  aut_t φ h1 h2 := by
    obtain ⟨b, hb, hbt⟩ := S.aut_t _ (map_aut_mem_autStab e h1) (map_aut_mem_autStab e h2)
    refine ⟨e b, ⟨⟨b, (Subgroup.mem_inf.1 hb).1, rfl⟩, ⟨b, (Subgroup.mem_inf.1 hb).2, rfl⟩⟩, ?_⟩
    rw [map_aut_apply e φ t, hbt, map_mul, map_mul, map_inv]
  cent_z := S.cent_z.imp (fun h => (map_centralizer_le_iff e P z).2 h)
    (fun h => (map_centralizer_le_iff e P' z).2 h)
  cent_t := S.cent_t.imp (fun h => (map_centralizer_le_iff e P t).2 h)
    (fun h => (map_centralizer_le_iff e P' t).2 h)

theorem unStdV_map {U P P' : Subgroup C} {z t : C} {V4 : Subgroup C}
    (S : UnStdV C U P P' z t V4) :
    UnStdV C' (U.map e.toMonoidHom) (P.map e.toMonoidHom) (P'.map e.toMonoidHom) (e z) (e t)
      (V4.map e.toMonoidHom) where
  V4_le := Subgroup.map_mono S.V4_le
  V4_ab := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, S.V4_ab a ha b hb]
  V4_sq := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, S.V4_sq a ha, map_one]
  V4_zt := ⟨⟨z, S.V4_zt.1, rfl⟩, ⟨t, S.V4_zt.2, rfl⟩⟩
  V4_eq := by
    rw [pCoreOf_map_of_injective e.toMonoidHom e.injective,
      centerOf_map_of_injective e.toMonoidHom e.injective]
    exact congrArg (Subgroup.map e.toMonoidHom) S.V4_eq
  V4_unique := by
    intro E hE hab hsq hcard
    have hback : (E.map e.symm.toMonoidHom).map e.toMonoidHom = E := by
      rw [Subgroup.map_map]
      ext x
      simp
    have hmem : ∀ {a : C}, a ∈ E.map e.symm.toMonoidHom → e a ∈ E := fun {a} ha => by
      rw [← hback]
      exact ⟨a, ha, rfl⟩
    have hle : E.map e.symm.toMonoidHom ≤ U := by
      have hinj : Function.Injective e.toMonoidHom := e.injective
      rw [← Subgroup.map_le_map_iff_of_injective hinj, hback]
      exact hE
    have hc : Nat.card (E.map e.symm.toMonoidHom) = Nat.card V4 := by
      rw [Subgroup.card_map_of_injective e.symm.injective, hcard,
        Subgroup.card_map_of_injective e.injective]
    have := S.V4_unique _ hle (fun a ha b hb => e.injective (by
      rw [map_mul, map_mul]
      exact hab _ (hmem ha) _ (hmem hb))) (fun a ha => e.injective (by
      rw [map_pow, map_one]
      exact hsq _ (hmem ha))) hc
    rw [← hback, this]
  z_ZP := by
    rw [perfectCore_map_of_injective e.toMonoidHom e.injective,
      centerOf_map_of_injective e.toMonoidHom e.injective]
    exact ⟨z, S.z_ZP, rfl⟩
  ZP_trans := by
    intro x hx hx1
    rw [perfectCore_map_of_injective e.toMonoidHom e.injective,
      centerOf_map_of_injective e.toMonoidHom e.injective] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨m, hm, hmz⟩ := S.ZP_trans x₀ hx₀ (fun h => hx1 (by
      rw [MulEquiv.coe_toMonoidHom, h, map_one]))
    refine ⟨e m, ⟨m, hm, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hmz]
    rfl
  cz := (map_centralizer_le_iff e P z).2 S.cz
  ct := (map_centralizer_le_iff e P' t).2 S.ct
  nz := fun h => S.nz ((map_centralizer_le_iff e P' z).1 h)
  nt := fun h => S.nt ((map_centralizer_le_iff e P t).1 h)

end Map

end CFSG.Quasithin.H13.F431.Un
