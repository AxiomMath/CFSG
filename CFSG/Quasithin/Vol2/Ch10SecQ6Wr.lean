module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrF
public import CFSG.Quasithin.Vol2.Ch10SecDFacts31
public import CFSG.Quasithin.Vol2.Ch10SecQ6WrAN2
public import CFSG.Quasithin.Vol2.Ch10SecQ6WrOG

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open C10P06

theorem factAParamWreath : FactAParamWreath := by
  intro W _ _ hW X Y S hX hYX _ hS hSY hSne hgen
  obtain ⟨φ⟩ := hX
  let ρ : SymFiveWrTwo →* MulAut W := X.subtype.comp φ.symm.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp φ.symm.injective
  have hρφ : ∀ x : X, ρ (φ x) = x := fun x => by
    change ((φ.symm (φ x) : X) : MulAut W) = x
    rw [MulEquiv.symm_apply_apply]
  have hXρ : X ≤ ρ.range := fun x hx => ⟨φ ⟨x, hx⟩, hρφ ⟨x, hx⟩⟩
  obtain ⟨hSX, hS2, hSi⟩ := hS
  have hS'2 : IsPGroup 2 ((S.subgroupOf X).map φ.toMonoidHom) :=
    (hS2.of_injective (Subgroup.subgroupOfEquivOfLe hSX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSX).injective).map _
  have hS'i : ¬ 2 ∣ ((S.subgroupOf X).map φ.toMonoidHom).index := by
    rw [show φ.toMonoidHom = (φ : X →* SymFiveWrTwo) from rfl, Subgroup.index_map_equiv]
    exact hSi
  have hS'Y' : (S.subgroupOf X).map φ.toMonoidHom ≤ (Y.subgroupOf X).map φ.toMonoidHom :=
    Subgroup.map_mono fun _ hx => hSY hx
  have hS'ne : (S.subgroupOf X).map φ.toMonoidHom ≠ (Y.subgroupOf X).map φ.toMonoidHom :=
    fun h => hSne (by
      have h1 := Subgroup.map_injective φ.injective h
      rwa [Subgroup.subgroupOf_inj, inf_of_le_left hSX, inf_of_le_left hYX] at h1)
  obtain ⟨g0, hg0⟩ := exists_conj_le hS'2 hS'i hS'Y' hS'ne
  have hY0 : ∀ y ∈ Y0, ρ (g0 * y * g0⁻¹) ∈ Y := fun y hy => by
    obtain ⟨x, hx, hxe⟩ := hg0 ⟨y, hy, rfl⟩
    have h1 : ρ (g0 * y * g0⁻¹) = x := by
      rw [← hρφ x]
      exact congrArg ρ hxe.symm
    rw [h1]
    exact hx
  have hgen' : (⨆ h : SymFiveWrTwo, (fixV (Y0.map ρ)).map (ρ h).toMonoidHom) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup₂_le fun x hx => ?_
    rintro _ ⟨w, hw, rfl⟩
    have hwC : (ρ g0)⁻¹ w ∈ fixV (Y0.map ρ) := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : ρ (g0 * y * g0⁻¹) w = w := hw _ (hY0 y hy)
      calc ρ y ((ρ g0)⁻¹ w) = (ρ g0)⁻¹ (ρ (g0 * y * g0⁻¹) w) := by
            simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]
        _ = (ρ g0)⁻¹ w := by rw [h1]
    refine Subgroup.mem_iSup_of_mem (φ ⟨x, hx⟩ * g0) ⟨(ρ g0)⁻¹ w, hwC, ?_⟩
    change ρ (φ ⟨x, hx⟩ * g0) ((ρ g0)⁻¹ w) = x w
    rw [map_mul, MulAut.mul_apply, MulAut.apply_inv_self, hρφ]
  apply aParam_le_one_of
  rw [Set.eq_empty_iff_forall_notMem]
  rintro A ⟨hAX, hA1, ⟨hAc, hA2⟩, hfix⟩
  have hAρ : A ≤ ρ.range := hAX.trans hXρ
  have hc' : ∀ a ∈ A.comap ρ, ∀ b ∈ A.comap ρ, a * b = b * a := fun a ha b hb =>
    hρ (by rw [map_mul, map_mul]; exact hAc _ ha _ hb)
  have h2' : ∀ a ∈ A.comap ρ, a * a = 1 := fun a ha =>
    hρ (by rw [map_mul, map_one, ← sq]; exact hA2 _ ha)
  have hA' : A.comap ρ ≠ ⊥ := by
    intro h
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨a', rfl⟩ := hAρ ha
    have ha' : a' ∈ A.comap ρ := ha
    rw [h, Subgroup.mem_bot] at ha'
    rw [ha', map_one]
    exact Subgroup.one_mem _
  obtain ⟨c, hc, hM | hN⟩ := exists_Phi_ne hW hρ hgen'
  · exact false_of_hypFix hW hρ hc (fun g v hv => gP_mem_Mcl g hv)
      (fun K hK hKi hKne => Mcl_le_of hK hKi hKne) hM hAρ hfix (hypFix_Mcl hc' h2' hA')
  · exact false_of_hypFix hW hρ hc (fun g v hv => gP_mem_Ncl g hv)
      (fun K hK hKi hKne => Ncl_le_of hK hKi hKne) hN hAρ hfix (hypFix_Ncl hc' h2' hA')

end CFSG.Quasithin.Vol2.Ch10.SecD
