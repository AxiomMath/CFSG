module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ENorm
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24EData
public import CFSG.Monster.CodeAut.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open Subgroup CFSG.Blueprint CFSG.Monster.Code CFSG.Sporadic.Th CFSG.Sporadic.Fi24
  CFSG.Sporadic.Mathieu CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "bP" => @famProd R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm

theorem octWord_map (σ : Equiv.Perm (Fin 24)) (S : Finset (Fin 24)) :
    octWord (S.map σ.toEmbedding) = octWord S ∘ ⇑(fi24ETau⁻¹ * σ⁻¹ * fi24ETau) := by
  funext i
  simp only [octWord, Function.comp_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
    Finset.mem_map_equiv, Equiv.Perm.inv_def]

theorem octWord_mem : ∀ k : Fin 759, octWord (octF k) ∈ C := by
  suffices h : ∀ n, ∀ k : Fin 759, k.val = n → octWord (octF k) ∈ C from fun k => h _ k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    by_cases h0 : k.val = 0
    · obtain rfl : k = 0 := Fin.ext h0
      exact octWord_zero_mem
    · obtain ⟨hlt, heq⟩ := octF_tree k h0
      rw [heq, image_permF, octWord_map]
      have hP : fi24ETau⁻¹ * (permE (octLabF k))⁻¹ * fi24ETau ∈ AutPerm := by
        have := inv_mem (tauConj_mem (octLabF k))
        rwa [show (fi24ETau⁻¹ * permE (octLabF k) * fi24ETau)⁻¹ =
          fi24ETau⁻¹ * (permE (octLabF k))⁻¹ * fi24ETau by group] at this
      exact comp_mem_of_mem_AutPerm hP (ih _ (by omega) _ rfl)


theorem mem_octads_of_bbarProd {S : Finset (Fin 24)} (hS : S.card = 8) (h : bP S = 1) :
    S ∈ octads :=
  @mem_of_famProd_eq_one R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm bbar_sq
    bbar_injective bbar_pair octads (fun _ hO => card_of_mem_octads hO)
    (fun _ hY => exists_octad_of_card_five hY) (fun _ hO => bbarProd_octad hO) S hS h


theorem map_octF_mem (n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) (k : Fin 759) :
    ∃ k', (octF k).map (fi24Pi n).toEmbedding = octF k' := by
  have hrel : bP ((octF k).map (fi24Pi n).toEmbedding) = 1 := by
    rw [@famProd_map R inferInstance (Fin 24) inferInstance inferInstance bbar bbar_comm
      (fi24Pi n) (jR n) (realizes_fi24Pi n) (octF k), bbarProd_octad (octF_mem k), mul_one,
      mul_inv_cancel]
  have hcard : ((octF k).map (fi24Pi n).toEmbedding).card = 8 := by
    rw [Finset.card_map, octF_card]
  obtain ⟨k', -, hk'⟩ := Finset.mem_image.1 (mem_octads_of_bbarProd hcard hrel)
  exact ⟨k', hk'.symm⟩

theorem basis_comp_mem (n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) (m : Fin 12) :
    B m ∘ ⇑(fi24ETau⁻¹ * fi24Pi n * fi24ETau) ∈ C := by
  obtain ⟨k', hk'⟩ := map_octF_mem n⁻¹ (fi24EKm m)
  have e : B m ∘ ⇑(fi24ETau⁻¹ * fi24Pi n * fi24ETau) = octWord (octF k') := by
    rw [← hk', octWord_map, basis_eq_octWord, map_inv, inv_inv]
  rw [e]
  exact octWord_mem k'

theorem tauConj_fi24Pi_mem (n : normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) :
    fi24ETau⁻¹ * fi24Pi n * fi24ETau ∈ AutPerm := by
  refine mem_AutPerm_of_basis (basis_comp_mem n) fun m => ?_
  rw [show (fi24ETau⁻¹ * fi24Pi n * fi24ETau)⁻¹ = fi24ETau⁻¹ * fi24Pi n⁻¹ * fi24ETau by
    rw [map_inv]; group]
  exact basis_comp_mem n⁻¹ m

theorem range_fi24Pi_le :
    fi24Pi.range ≤ NativeSporadic.M24.map (MulAut.conj fi24EC).toMonoidHom := by
  rintro _ ⟨n, rfl⟩
  have hp := tauConj_fi24Pi_mem n
  rw [AutPerm_eq_closure, bridge_closure_eq_map] at hp
  obtain ⟨g, hg, hgp⟩ := hp
  refine ⟨g, hg, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hgp
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, fi24EC]
  calc fi24ETau * bridgeQ⁻¹ * g * (fi24ETau * bridgeQ⁻¹)⁻¹ =
      fi24ETau * (bridgeQ⁻¹ * g * bridgeQ) * fi24ETau⁻¹ := by group
    _ = fi24Pi n := by rw [hgp]; group

theorem wordE_mem_range (w : List (Fin 2 × ℕ)) : wordE w ∈ fi24Pi.range := by
  unfold wordE
  refine list_prod_mem fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact pow_mem (permE_mem_range p.1) p.2

theorem map_le_range_fi24Pi :
    NativeSporadic.M24.map (MulAut.conj fi24EC).toMonoidHom ≤ fi24Pi.range := by
  rw [m24_eq, MonoidHom.map_closure, Set.image_pair, closure_le]
  rintro _ (rfl | rfl)
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_m24gA]
    exact wordE_mem_range _
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_m24gB]
    exact wordE_mem_range _

theorem range_fi24Pi : fi24Pi.range = NativeSporadic.M24.map (MulAut.conj fi24EC).toMonoidHom :=
  le_antisymm range_fi24Pi_le map_le_range_fi24Pi

theorem quotient_fi24E : Nonempty (↥(normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) ⧸
    fi24E.subgroupOf (normalizer (fi24E : Set CFSG.Sporadic.Fi24.J)) ≃* NativeSporadic.Carrier .M24) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq ker_fi24Pi.symm).trans
    ((QuotientGroup.quotientKerEquivRange fi24Pi).trans
      ((MulEquiv.subgroupCongr range_fi24Pi).trans
        (NativeSporadic.M24.equivMapOfInjective _ (MulAut.conj fi24EC).injective).symm))⟩

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
