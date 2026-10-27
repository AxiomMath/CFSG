
module

public import CFSG.Monster.B.Fischer.Fi22ModelBase1

public import CFSG.Monster.B.Fischer.Fi22GraphAut

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem card_mulAut_fi22P_le :
    Nat.card (MulAut fi22P) ≤ 129123503308800 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ :=
    CTUC_Fi22_faithful_automorphism_action_on_commuting_graph
  exact h.trans CTUC_Fi22_graph_automorphism_order_bound.1

theorem fi22ConjHom_bijective :
    Function.Bijective fi22ConjHom :=
  fi22ConjHom_injective.bijective_of_nat_card_le (by rw [card_fi22R]; exact card_mulAut_fi22P_le)

@[expose] def fi22RAut :
    fi22R ≃* MulAut fi22P :=
  MulEquiv.ofBijective fi22ConjHom fi22ConjHom_bijective

theorem fi22RAut_apply
    (r : fi22R) : fi22RAut r = fi22ConjHom r := rfl

theorem fi22RAut_inn :
    (fi22P.subgroupOf fi22R).map fi22RAut.toMonoidHom =
    (MulAut.conj : fi22P →* MulAut fi22P).range := by
  ext α
  rw [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨⟨r, Subgroup.mem_subgroupOf.1 hr⟩, MulEquiv.ext fun g => Subtype.ext ?_⟩
    rw [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, fi22RAut_apply, fi22ConjHom_apply]
    rfl
  · rintro ⟨g, rfl⟩
    refine ⟨⟨g, fi22P_le_R g.2⟩, Subgroup.mem_subgroupOf.2 g.2, MulEquiv.ext fun h => ?_⟩
    apply Subtype.ext
    rw [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, fi22RAut_apply, fi22ConjHom_apply]
    rfl

theorem card_fi22Out :
    Nat.card (MulAut fi22P ⧸ (MulAut.conj : fi22P →* MulAut fi22P).range) = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAut.conj : fi22P →* MulAut fi22P).range
  rw [← Nat.card_congr fi22RAut.toEquiv, card_fi22R,
    Nat.card_congr (MonoidHom.ofInjective fi22P_conj_injective).toEquiv.symm, card_fi22P] at h
  have h' : 2 * 64561751654400 =
      Nat.card (MulAut fi22P ⧸ (MulAut.conj : fi22P →* MulAut fi22P).range) * 64561751654400 := by
    rw [← h]
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h').symm

@[expose] def fi22OutEquiv :
    MulAut fi22P ⧸ (MulAut.conj : fi22P →* MulAut fi22P).range ≃* Multiplicative (ZMod 2) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  mulEquivOfPrimeCardEq card_fi22Out (by rw [Nat.card_eq_fintype_card]; rfl)

theorem CTUC_Fi22_full_automorphism_permutation_model :
    orderOf fi22U = 2 ∧ fi22U ∉ fi22P ∧ fi22P.map (MulAut.conj fi22U).toMonoidHom = fi22P ∧
    Subgroup.centralizer (fi22P : Set (Equiv.Perm (Fin 3510))) = ⊥ ∧
    (∃ ψ : fi22R ≃* MulAut fi22P,
      (∀ (r : fi22R) (g : fi22P), ((ψ r g : fi22P) : Equiv.Perm (Fin 3510)) =
        (r : Equiv.Perm (Fin 3510)) * g * (r : Equiv.Perm (Fin 3510))⁻¹) ∧
      (fi22P.subgroupOf fi22R).map ψ.toMonoidHom =
        (MulAut.conj : fi22P →* MulAut fi22P).range) ∧
    ((fi22P.subgroupOf fi22R).Normal ∧ fi22P ⊓ Subgroup.zpowers fi22U = ⊥ ∧
      fi22P ⊔ Subgroup.zpowers fi22U = fi22R) ∧
    Nat.card fi22R = 129123503308800 ∧
    Nonempty (MulAut fi22P ⧸ (MulAut.conj : fi22P →* MulAut fi22P).range ≃*
      Multiplicative (ZMod 2)) :=
  ⟨orderOf_fi22U, fi22U_not_mem, fi22U_conj_eq, fi22P_centralizer,
    ⟨fi22RAut, fun r g => fi22ConjHom_apply r g, fi22RAut_inn⟩, fi22R_semidirect, card_fi22R,
    ⟨fi22OutEquiv⟩⟩

end CFSG.Monster.B.Fischer
