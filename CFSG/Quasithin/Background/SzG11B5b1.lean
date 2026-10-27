module

public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.Quasithin.G11.SzG11S.B5b

open CFSG.Open

theorem fstar_normal (Y : Type*) [Group Y] : (genFittingFStar Y).Normal :=
  CFSG.ComponentClassification.GeneralizedFitting.normal Y

theorem isComponentOf_map_subtype {G : Type*} [Group G] (H : Subgroup G) {L : Subgroup ↥H}
    (hL : IsComponentOf L ⊤) : IsComponentOf (L.map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le L, ?_, ?_⟩
  · have h := CFSG.ComponentClassification.Components.chain_map H.subtype hL.2.1
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (L.equivMapOfInjective H.subtype H.subtype_injective).symm hL.2.2

theorem exists_normal_two_subgroup {Y : Type} [Group Y] [Finite Y] {y : Y} (hy : y * y = 1)
    (hF : ∀ f ∈ genFittingFitting Y, f * y = y * f)
    (hE : ∀ L : Subgroup Y, IsComponentOf L ⊤ → ∀ l ∈ L, l * y = y * l) :
    ∃ N : Subgroup Y, N.Normal ∧ IsPGroup 2 N ∧ y ∈ N := by
  set S := genFittingFStar Y with hS
  have hSn : S.Normal := fstar_normal Y
  have hle : S ≤ Subgroup.centralizer ({y} : Set Y) := by
    refine sup_le (fun f hf => ?_) (sSup_le fun L hL l hl => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hF f hf).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hE L hL l hl).symm
  have hcent : ∀ s ∈ S, s * y = y * s := by
    intro s hs
    have h := Subgroup.mem_centralizer_iff.1 (hle hs) y rfl
    exact h.symm
  have hyS : y ∈ S := CFSG.Adapters.generalized_fitting_self_centralizing Y
    (Subgroup.mem_centralizer_iff.2 fun s hs => hcent s hs)
  let N : Subgroup Y :=
    { carrier := {z | z ∈ S ∧ (∀ s ∈ S, s * z = z * s) ∧ z * z = 1}
      mul_mem' := by
        rintro a b ⟨haS, haC, ha2⟩ ⟨hbS, hbC, hb2⟩
        refine ⟨S.mul_mem haS hbS, fun s hs => ?_, ?_⟩
        · calc s * (a * b) = (s * a) * b := by group
            _ = (a * s) * b := by rw [haC s hs]
            _ = a * (s * b) := by group
            _ = a * (b * s) := by rw [hbC s hs]
            _ = (a * b) * s := by group
        · have hab : a * b = b * a := hbC a haS
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [← hab]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
      one_mem' := ⟨S.one_mem, fun s _ => by rw [mul_one, one_mul], mul_one 1⟩
      inv_mem' := by
        rintro a ⟨haS, haC, ha2⟩
        rw [inv_eq_of_mul_eq_one_right ha2]
        exact ⟨haS, haC, ha2⟩ }
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnS, hnC, hn2⟩ := hn
    have hgS : g * n * g⁻¹ ∈ S := hSn.conj_mem n hnS g
    refine ⟨hgS, fun s hs => ?_, ?_⟩
    · have hs' : g⁻¹ * s * g ∈ S := by
        have := hSn.conj_mem s hs g⁻¹
        rwa [inv_inv] at this
      have h1 : (g⁻¹ * s * g) * n = n * (g⁻¹ * s * g) := hnC _ hs'
      calc s * (g * n * g⁻¹) = g * ((g⁻¹ * s * g) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
        _ = (g * n * g⁻¹) * s := by group
    · calc g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
        _ = 1 := by rw [hn2]; group
  refine ⟨N, hNn, ?_, ⟨hyS, fun s hs => hcent s hs, hy⟩⟩
  rintro ⟨z, hz⟩
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_two] using hz.2.2

end CFSG.Quasithin.G11.SzG11S.B5b
