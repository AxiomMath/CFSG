module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Faith

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

theorem card_centralizer_aut_eq {G : Type*} [Group G] (α : MulAut G) (x : G) :
    Nat.card (Subgroup.centralizer ({α x} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨α.symm g.1, ?_⟩
      invFun := fun g => ⟨α g.1, ?_⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply α.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h
  · have h := Subgroup.mem_centralizer_singleton_iff.1 g.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]

section Pt


theorem exists_aut_d4z (α : MulAut D) : ∃ c : D, α d4z = c * d4z * c⁻¹ := by
  have hord : orderOf (α d4z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_d4z
  obtain ⟨c, hc | hc⟩ := exists_conj_of_orderOf_eq_two hord
  · exact ⟨c, hc⟩
  · exfalso
    have : Finite D := finite_D
    have hcard : Nat.card (Subgroup.centralizer ({d4z} : Set D)) =
        Nat.card (Subgroup.centralizer ({d4t} : Set D)) := by
      rw [← card_centralizer_aut_eq α d4z, hc, card_centralizer_conj']
    have h1 : Nat.card d4U ≤ Nat.card (Subgroup.centralizer ({d4z} : Set D)) :=
      Subgroup.card_le_of_le d4U_le_centralizer_z
    rw [card_d4U', hcard, centralizer_d4t_eq, card_d4Ct] at h1
    omega

theorem exists_aut_zElt (α : MulAut D) (i : Fin 819) : ∃ j : Fin 819, α (zElt i) = zElt j := by
  obtain ⟨c, hc⟩ := exists_aut_d4z α
  obtain ⟨g, hg⟩ := exists_smul_pt0_eq i
  have h1 : zElt i = g * d4z * g⁻¹ := by
    rw [← hg, smul_pt_def, zElt_act, zElt_zero]
  refine ⟨act (α g * c) pt0, ?_⟩
  rw [zElt_act, zElt_zero, h1, map_mul, map_mul, map_inv, hc]
  group

@[expose] noncomputable def autPtFun (α : MulAut D) (i : Fin 819) : Fin 819 :=
  Classical.choose (exists_aut_zElt α i)

theorem zElt_autPtFun (α : MulAut D) (i : Fin 819) : zElt (autPtFun α i) = α (zElt i) :=
  (Classical.choose_spec (exists_aut_zElt α i)).symm

@[expose] noncomputable def autPt : MulAut D →* Equiv.Perm (Fin 819) where
  toFun α :=
    { toFun := autPtFun α
      invFun := autPtFun α⁻¹
      left_inv := fun i => by
        apply zElt_injective
        rw [zElt_autPtFun, zElt_autPtFun]
        exact α.symm_apply_apply (zElt i)
      right_inv := fun i => by
        apply zElt_injective
        rw [zElt_autPtFun, zElt_autPtFun]
        exact α.apply_symm_apply (zElt i) }
  map_one' := Equiv.ext fun i => zElt_injective (by
    show zElt (autPtFun 1 i) = zElt i
    rw [zElt_autPtFun]
    rfl)
  map_mul' α β := Equiv.ext fun i => zElt_injective (by
    show zElt (autPtFun (α * β) i) = zElt (autPtFun α (autPtFun β i))
    rw [zElt_autPtFun, zElt_autPtFun, zElt_autPtFun]
    rfl)

theorem autPt_apply (α : MulAut D) (i : Fin 819) : zElt (autPt α i) = α (zElt i) :=
  zElt_autPtFun α i

theorem autPt_conj (g : D) : autPt (MulAut.conj g) = act g :=
  Equiv.ext fun i => zElt_injective (by rw [autPt_apply, zElt_act, MulAut.conj_apply])

theorem normal_closure_zElt : (Subgroup.closure (Set.range (zElt : Fin 819 → D))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨act g i, zElt_act g i⟩
  | one => simp
  | mul x y _ _ ihx ihy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ihx

theorem closure_zElt_eq_top (hs : IsSimpleGroup D) :
    Subgroup.closure (Set.range (zElt : Fin 819 → D)) = ⊤ := by
  have := normal_closure_zElt
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.closure (Set.range (zElt : Fin 819 → D))) with
    h | h
  · exfalso
    have hz : d4z ∈ Subgroup.closure (Set.range (zElt : Fin 819 → D)) :=
      Subgroup.subset_closure ⟨pt0, zElt_zero⟩
    rw [h] at hz
    exact d4z_sq.2 (Subgroup.mem_bot.1 hz)
  · exact h

theorem autPt_injective (hs : IsSimpleGroup D) : Function.Injective autPt := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro α hα
  have hfix : ∀ i : Fin 819, α (zElt i) = zElt i := fun i => by
    rw [← autPt_apply, MonoidHom.mem_ker.1 hα]
    rfl
  have heq : Set.EqOn α.toMonoidHom (MonoidHom.id D) (Set.range (zElt : Fin 819 → D)) := by
    rintro _ ⟨i, rfl⟩
    exact hfix i
  have := MonoidHom.eqOn_closure heq
  rw [closure_zElt_eq_top hs] at this
  exact MulEquiv.ext fun x => this (Set.mem_univ x)

end Pt

end CFSG.Quasithin.D4Hex
