module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumW
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.PSL3Four

namespace Insp7

theorem l34_map_centralizer_conj
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ R) (r : Equiv.Perm (Fin 42)) :
    (Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * r * c⁻¹} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, ⟨hw, hwS⟩, rfl⟩
    refine ⟨?_, conj_mem_S hc hwS⟩
    have hw' : w * r = r * w := hw
    calc c * w * c⁻¹ * (c * r * c⁻¹) = c * (w * r) * c⁻¹ := by group
      _ = c * (r * w) * c⁻¹ := by rw [hw']
      _ = c * r * c⁻¹ * (c * w * c⁻¹) := by group
  · rintro ⟨hy, hyS⟩
    have hy' : y * (c * r * c⁻¹) = (c * r * c⁻¹) * y := hy
    refine ⟨c⁻¹ * y * c, ⟨?_, ?_⟩, by group⟩
    · show c⁻¹ * y * c * r = r * (c⁻¹ * y * c)
      calc c⁻¹ * y * c * r = c⁻¹ * (y * (c * r * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * r * c⁻¹) * y) * c := by rw [hy']
        _ = r * (c⁻¹ * y * c) := by group
    · refine conj_mem_S' hc ?_
      rw [show c * (c⁻¹ * y * c) * c⁻¹ = y by group]
      exact hyS

theorem map_centralizer_subtype_inf (H : Subgroup (Equiv.Perm (Fin 42))) (t : H) :
    (Subgroup.centralizer ({t} : Set H)).map H.subtype =
      Subgroup.centralizer ({(t : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
    Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by simpa using congrArg Subtype.val hy, y.2⟩
  · rintro ⟨hxt, hx⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxt, rfl⟩

theorem l34_involution_centralizer_card
    (t : S) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set S)) = 64 := by
  obtain ⟨-, -, -, -, -, hinv, -, -, -, -, -, -, hout, hC1, -⟩ := involution_enumeration
  let x : R := ⟨(t : Equiv.Perm (Fin 42)), S_le_R t.2⟩
  have hxord : orderOf x = 2 := by
    have h1 : orderOf (x : Equiv.Perm (Fin 42)) = orderOf x := Subgroup.orderOf_coe x
    have h2 : orderOf (t : Equiv.Perm (Fin 42)) = orderOf t := Subgroup.orderOf_coe t
    rw [← h1]
    show orderOf (t : Equiv.Perm (Fin 42)) = 2
    rw [h2, ht]
  rcases (hinv x).1 hxord with h1 | h2 | h3 | h4
  · obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h1
    have hmap := l34_map_centralizer_conj hc r₁
    have hct : (t : Equiv.Perm (Fin 42)) = c * r₁ * c⁻¹ := he
    have hcard : Nat.card (Subgroup.centralizer ({t} : Set S)) =
        Nat.card (Subgroup.centralizer ({(t : Equiv.Perm (Fin 42))} :
          Set (Equiv.Perm (Fin 42))) ⊓ S : Subgroup (Equiv.Perm (Fin 42))) := by
      rw [← map_centralizer_subtype_inf S t]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective _ S.subtype S.subtype_injective).toEquiv
    rw [hcard, hct, ← hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hC1
  · exact absurd t.2 (hout x (Or.inl h2))
  · exact absurd t.2 (hout x (Or.inr (Or.inl h3)))
  · exact absurd t.2 (hout x (Or.inr (Or.inr h4)))

theorem numFactAt_l34
    : NumFactAt (fun L _ => StatedClassicalModel L .PSL 3 2 2) := by
  have h : NumFactAt (fun L _ => Nonempty (L ≃* S)) := by
    refine numFactAt_of_model_dvd (X := S) ?_ (t := 12) ?_ {64} (by decide) ?_
    · rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have hcent : (x : Equiv.Perm (Fin 42)) ∈
          Subgroup.centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
        rw [Subgroup.mem_inf]
        refine ⟨?_, S_le_R x.2⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)
      rw [centralizer_S_inf_R, Subgroup.mem_bot] at hcent
      exact Subtype.ext hcent
    · have h12 := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound S 3 2 2
        statedClassicalModel_S).2.2.2.2 (by norm_num)
      norm_num at h12
      exact h12
    · intro x hx
      exact Finset.mem_singleton.mpr (l34_involution_centralizer_card x hx)
  exact numFactAt_of_cover (G := fun L _ => Nonempty (L ≃* S)) (H := fun L _ => Nonempty (L ≃* S))
    (fun L _ hL => Or.inl (nonempty_equiv_of_stated L hL)) h h

end Insp7

end CFSG.Quasithin
