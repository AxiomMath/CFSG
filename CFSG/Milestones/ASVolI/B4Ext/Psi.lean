module

public import CFSG.Milestones.ASVolI.B4Ext.WT

public section

namespace CFSG.ASVolI

open CFSG.Quasithin Module

section Psi

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) (φ : V ⧸ U ≃* DualGrp ↥U)

@[expose] noncomputable def burnsideB49x_psi (u : ↥U) : Dual (ZMod 2) (burnsideB49_W hV U) :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk'
    (fun w => Multiplicative.toAdd ((φ (F2Vec.toV (burnsideB49_hW hV U) w)) u))
    (fun w w' => by
      rw [F2Vec.toV_add, map_mul, DualGrp.mul_apply, toAdd_mul]))

theorem burnsideB49x_psi_apply (u : ↥U) (w : burnsideB49_W hV U) :
    burnsideB49x_psi hV U φ u w =
      Multiplicative.toAdd ((φ (F2Vec.toV (burnsideB49_hW hV U) w)) u) := rfl

theorem burnsideB49x_psi_mul (u u' : ↥U) :
    burnsideB49x_psi hV U φ (u * u') = burnsideB49x_psi hV U φ u + burnsideB49x_psi hV U φ u' := by
  ext w
  rw [LinearMap.add_apply, burnsideB49x_psi_apply, burnsideB49x_psi_apply,
    burnsideB49x_psi_apply, map_mul, toAdd_mul]

theorem burnsideB49x_psi_inv (u : ↥U) :
    burnsideB49x_psi hV U φ u⁻¹ = - burnsideB49x_psi hV U φ u := by
  ext w
  rw [LinearMap.neg_apply, burnsideB49x_psi_apply, burnsideB49x_psi_apply, map_inv, toAdd_inv]

include hV in
theorem burnsideB49x_psi_injective [Finite V] :
    Function.Injective (burnsideB49x_psi hV U φ) := by
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (hV u)
  intro u u' h
  by_contra hne
  have hne' : u * u'⁻¹ ≠ 1 := fun h' => hne (mul_inv_eq_one.1 h')
  obtain ⟨χ, hχ⟩ := exists_dualChar_ne_one hU2 hne'
  obtain ⟨x, hx⟩ := φ.surjective χ
  apply hχ
  have h1 := congrArg (fun F : Dual (ZMod 2) (burnsideB49_W hV U) =>
    F (F2Vec.ofV (burnsideB49_hW hV U) x)) h
  simp only [burnsideB49x_psi_apply, F2Vec.toV_ofV, hx] at h1
  rw [map_mul, map_inv, Multiplicative.toAdd.injective h1, mul_inv_cancel]

include hG in
theorem burnsideB49x_psi_equiv
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    (g : ↥G) (u : ↥U) (w : burnsideB49_W hV U) :
    burnsideB49x_psi hV U φ ⟨(g : MulAut V) u, hG g g.2 u u.2⟩ w =
      burnsideB49x_psi hV U φ u ((burnsideB49_iota hV U G hG g).symm w) := by
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) w)
  have hw : w = F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) := by
    rw [hv, F2Vec.ofV_toV]
  subst hw
  have hsymm : (burnsideB49_iota hV U G hG g).symm
      (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) =
      F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk (((g⁻¹ : ↥G) : MulAut V) v)) := by
    rw [LinearEquiv.symm_apply_eq, burnsideB49x_iota_mk]
    congr 2
    change v = ((g : MulAut V) * (g : MulAut V)⁻¹) v
    rw [mul_inv_cancel]
    rfl
  rw [hsymm, burnsideB49x_psi_apply, burnsideB49x_psi_apply, F2Vec.toV_ofV, F2Vec.toV_ofV]
  congr 1
  have hgg : (g : MulAut V) (((g⁻¹ : ↥G) : MulAut V) v) = v := by
    rw [Subgroup.coe_inv, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have h1 := hφ (g : MulAut V) g.2 (((g⁻¹ : ↥G) : MulAut V) v) ⟨(g : MulAut V) u, hG g g.2 u u.2⟩
    u rfl
  rw [hgg] at h1
  exact h1

include hV hG in
theorem burnsideB49x_mem_fixU_iff [Finite V]
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (u : ↥U) :
    (u : V) ∈ fixV A ↔ burnsideB49x_psi hV U φ u ∈
      (burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A)).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hu w hw
    refine burnsideB49x_wcomm_le_ker (ψ := burnsideB49x_psi hV U φ u)
      (E := burnsideB49x_hatW hV U G hG A) ?_ hw
    rintro _ ⟨g, hg, rfl⟩ x
    rw [map_sub, sub_eq_zero]
    have h1 := burnsideB49x_psi_equiv hV U G hG φ hφ g u (burnsideB49_iota hV U G hG g x)
    rw [LinearEquiv.symm_apply_apply] at h1
    have hgu : (⟨(g : MulAut V) u, hG g g.2 u u.2⟩ : ↥U) = u :=
      Subtype.ext (hu (g : MulAut V) hg)
    rw [hgu] at h1
    exact h1
  · intro h a ha
    set g : ↥G := ⟨a, hAG ha⟩ with hgdef
    have hga : g⁻¹ ∈ A.subgroupOf G := A.inv_mem ha
    change (g : MulAut V) (u : V) = u
    have hψ : burnsideB49x_psi hV U φ ⟨(g : MulAut V) u, hG g g.2 u u.2⟩ =
        burnsideB49x_psi hV U φ u := by
      ext w
      rw [burnsideB49x_psi_equiv hV U G hG φ hφ g u w]
      have hmem : (burnsideB49_iota hV U G hG g).symm w - w ∈
          burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A) := by
        have : (burnsideB49_iota hV U G hG g).symm = burnsideB49_iota hV U G hG g⁻¹ := by
          rw [map_inv]
          rfl
        rw [this]
        exact burnsideB49x_sub_mem_wcomm (Subgroup.mem_map_of_mem _ hga) w
      have := h _ hmem
      rw [map_sub, sub_eq_zero] at this
      exact this
    have := burnsideB49x_psi_injective hV U φ hψ
    exact congrArg Subtype.val this

include hV hG in
theorem burnsideB49x_quadU [Finite V]
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    {A : Subgroup (MulAut V)} (hAG : A ≤ G)
    (hq : burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A) ≤
      burnsideB49x_wfix (burnsideB49x_hatW hV U G hG A))
    (a : MulAut V) (ha : a ∈ A) (a' : MulAut V) (ha' : a' ∈ A) (u : V) (hu : u ∈ U) :
    a' (a u * u⁻¹) = a u * u⁻¹ := by
  set ga : ↥G := ⟨a, hAG ha⟩ with hga
  set ga' : ↥G := ⟨a', hAG ha'⟩ with hga'
  have hau : a u ∈ U := hG a (hAG ha) u hu
  have hy : a u * u⁻¹ ∈ U := U.mul_mem hau (U.inv_mem hu)
  have hay : a' (a u * u⁻¹) ∈ U := hG a' (hAG ha') _ hy
  have hsymm : ∀ g : ↥G, (burnsideB49_iota hV U G hG g).symm = burnsideB49_iota hV U G hG g⁻¹ :=
    fun g => by rw [map_inv]; rfl
  have hψy : ∀ x, burnsideB49x_psi hV U φ ⟨a u * u⁻¹, hy⟩ x =
      burnsideB49x_psi hV U φ ⟨u, hu⟩ ((burnsideB49_iota hV U G hG ga).symm x - x) := by
    intro x
    have e : (⟨a u * u⁻¹, hy⟩ : ↥U) = ⟨(ga : MulAut V) u, hG ga ga.2 u hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹ :=
      rfl
    rw [e, burnsideB49x_psi_mul, burnsideB49x_psi_inv, LinearMap.add_apply, LinearMap.neg_apply,
      burnsideB49x_psi_equiv hV U G hG φ hφ ga ⟨u, hu⟩ x, map_sub, sub_eq_add_neg]
  have key : burnsideB49x_psi hV U φ ⟨a' (a u * u⁻¹), hay⟩ =
      burnsideB49x_psi hV U φ ⟨a u * u⁻¹, hy⟩ := by
    ext w
    have h1 := burnsideB49x_psi_equiv hV U G hG φ hφ ga' ⟨a u * u⁻¹, hy⟩ w
    rw [show (⟨(ga' : MulAut V) (a u * u⁻¹), hG ga' ga'.2 _ hy⟩ : ↥U) =
      ⟨a' (a u * u⁻¹), hay⟩ from rfl] at h1
    rw [h1, hψy, hψy]
    set z := (burnsideB49_iota hV U G hG ga').symm w with hz
    have hmem : z - w ∈ burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A) := by
      rw [hz, hsymm ga']
      exact burnsideB49x_sub_mem_wcomm (Subgroup.mem_map_of_mem (burnsideB49_iota hV U G hG)
        (show ga'⁻¹ ∈ A.subgroupOf G from A.inv_mem ha')) w
    have hfix : burnsideB49_iota hV U G hG ga⁻¹ (z - w) = z - w :=
      hq hmem _ (Subgroup.mem_map_of_mem (burnsideB49_iota hV U G hG)
        (show ga⁻¹ ∈ A.subgroupOf G from A.inv_mem ha))
    rw [← hsymm ga] at hfix
    have e2 : (burnsideB49_iota hV U G hG ga).symm z - z =
        ((burnsideB49_iota hV U G hG ga).symm w - w) +
          ((burnsideB49_iota hV U G hG ga).symm (z - w) - (z - w)) := by
      rw [map_sub]
      abel
    rw [e2, hfix, sub_self, add_zero]
  have := burnsideB49x_psi_injective hV U φ key
  exact congrArg Subtype.val this

end Psi

section PsiCard

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(CFSG.Open.StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49x_card_fixU_dual (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL n K)).RealizesVia G U ⊥ π)
    (hdual : CFSG.ASVolI.ChB.QuotIsoDual G U) {A : Subgroup (MulAut V)} (hAG : A ≤ G) :
    Nat.card ↥(fixV A ⊓ U) = 2 ^ (n - finrank (ZMod 2) (burnsideB49x_wcomm
      (burnsideB49x_hatW hV U G (burnsideB49_hG hreal) A))) := by
  set hG := burnsideB49_hG hreal with hGdef
  have hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U := Or.inr hdual
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  haveI : Finite (Dual (ZMod 2) (burnsideB49_W hV U)) := Module.finite_of_finite (ZMod 2)
  have hn : finrank (ZMod 2) (burnsideB49_W hV U) = n := burnsideB49_finrank_W hV hK hreal hquot
  obtain ⟨φ, hφ⟩ := hdual
  have hann : Nat.card ↥(burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A)).dualAnnihilator =
      2 ^ (n - finrank (ZMod 2) (burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A))) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq (burnsideB49x_wcomm
      (burnsideB49x_hatW hV U G hG A))
    rw [hn] at this
    congr 1
    omega
  set S := (burnsideB49x_wcomm (burnsideB49x_hatW hV U G hG A)).dualAnnihilator with hS
  rw [← hann]
  have hinj := burnsideB49x_psi_injective hV U φ
  have hcardU : Nat.card ↥U = Nat.card (Dual (ZMod 2) (burnsideB49_W hV U)) := by
    rw [burnsideB49_card_U hreal, hK, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Subspace.dual_finrank_eq, hn]
  have hbij : Function.Bijective (burnsideB49x_psi hV U φ) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcardU⟩
  refine Nat.card_congr (Equiv.ofBijective
    (fun u : ↥(fixV A ⊓ U) => (⟨burnsideB49x_psi hV U φ ⟨(u : V), (Subgroup.mem_inf.1 u.2).2⟩,
      (burnsideB49x_mem_fixU_iff hV U G hG φ hφ hAG _).1 (Subgroup.mem_inf.1 u.2).1⟩ : ↥S))
    ⟨fun u u' h => ?_, fun s => ?_⟩)
  · have h' := congrArg (fun x : ↥S => (x : Dual (ZMod 2) (burnsideB49_W hV U))) h
    have h'' := hinj h'
    exact Subtype.ext (congrArg (fun x : ↥U => (x : V)) h'')
  · obtain ⟨u, hu⟩ := hbij.2 (s : Dual (ZMod 2) (burnsideB49_W hV U))
    have hfix : (u : V) ∈ fixV A := (burnsideB49x_mem_fixU_iff hV U G hG φ hφ hAG u).2
      (hu ▸ s.2)
    exact ⟨⟨(u : V), Subgroup.mem_inf.2 ⟨hfix, u.2⟩⟩, Subtype.ext (by simpa using hu)⟩

end PsiCard

end CFSG.ASVolI
