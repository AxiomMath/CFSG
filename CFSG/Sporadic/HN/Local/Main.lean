module

public import CFSG.Sporadic.HN.Local.InvolutionClasses
public import CFSG.Sporadic.HN.Commutant
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 CFSG.Blueprint CFSG.Sporadic.HN.LocalK

noncomputable def hnEquiv :
    NativeSporadic.HN ≃* J dHN :=
  seedEquiv' (by decide) Certificates.certificate3166.1 Certificates.certificate3166.2.1

theorem isConj_equiv_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (a b : G) :
    IsConj (e a) (e b) ↔ IsConj a b :=
  ⟨fun h => by simpa using e.symm.toMonoidHom.map_isConj h, fun h => e.toMonoidHom.map_isConj h⟩

theorem card_centralizer_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (a : G) :
    Nat.card (Subgroup.centralizer {a}) = Nat.card (Subgroup.centralizer {e a}) :=
  Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun g => by
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
      rw [← map_mul, ← map_mul, h]
    · intro h
      simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe] at h
      rw [← map_mul, ← map_mul] at h
      exact e.injective h)

theorem isConj_hnEquiv_iff (a b : NativeSporadic.HN) :
    IsConj (hnEquiv a) (hnEquiv b) ↔ IsConj a b :=
  @isConj_equiv_iff NativeSporadic.HN (J dHN) Units.instGroup (Subgroup.toGroup _) hnEquiv a b

theorem card_centralizer_hnEquiv (a : NativeSporadic.HN) :
    Nat.card (Subgroup.centralizer {a}) = Nat.card (Subgroup.centralizer {hnEquiv a}) :=
  @card_centralizer_equiv NativeSporadic.HN (J dHN) Units.instGroup (Subgroup.toGroup _) hnEquiv a

@[expose] noncomputable def hnStab : Subgroup NativeSporadic.HN where
  carrier := {g | hnEquiv g ∈ stabHN}
  mul_mem' := fun {a b} ha hb => by
    show hnEquiv (a * b) ∈ stabHN
    rw [map_mul]; exact stabHN.mul_mem ha hb
  one_mem' := by
    show hnEquiv 1 ∈ stabHN
    rw [map_one]; exact stabHN.one_mem
  inv_mem' := fun {a} ha => by
    show hnEquiv a⁻¹ ∈ stabHN
    rw [map_inv]; exact stabHN.inv_mem ha

theorem mem_hnStab_iff
    (g : NativeSporadic.HN) : g ∈ hnStab ↔ hnEquiv g ∈ stabHN := Iff.rfl

@[expose] noncomputable def hnStabEquiv : hnStab ≃* stabHN where
  toFun g := ⟨hnEquiv g.1, g.2⟩
  invFun h := ⟨hnEquiv.symm h.1, by
    show hnEquiv (hnEquiv.symm h.1) ∈ stabHN
    rw [MulEquiv.apply_symm_apply]; exact h.2⟩
  left_inv g := Subtype.ext (hnEquiv.symm_apply_apply _)
  right_inv h := Subtype.ext (hnEquiv.apply_symm_apply _)
  map_mul' g h := Subtype.ext (map_mul hnEquiv _ _)

theorem hn_point_stabilizer_alternating_twelve :
    Nat.card hnStab = 239500800 ∧ Nonempty (hnStab ≃* alternatingGroup (Fin 12)) := by
  refine ⟨?_, ⟨hnStabEquiv.trans thetaS⟩⟩
  rw [Nat.card_congr hnStabEquiv.toEquiv, Nat.card_congr thetaS.toEquiv]
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide +kernel

@[expose] noncomputable def hnT2 :
    NativeSporadic.HN := hnEquiv.symm (wG 12)

@[expose] noncomputable def hnT4 :
    NativeSporadic.HN := hnEquiv.symm (wG 13)

theorem hnEquiv_hnT2 :
    hnEquiv hnT2 = wG 12 := hnEquiv.apply_symm_apply _

theorem hnEquiv_hnT4 :
    hnEquiv hnT4 = wG 13 := hnEquiv.apply_symm_apply _

theorem hnT2_mem :
    hnT2 ∈ hnStab := by
  rw [mem_hnStab_iff, hnEquiv_hnT2]; exact t2_mem_stabHN

theorem hnT4_mem :
    hnT4 ∈ hnStab := by
  rw [mem_hnStab_iff, hnEquiv_hnT4]; exact t4_mem_stabHN

theorem hnT2_sq : hnT2 ^ 2 = 1 := by
  apply hnEquiv.injective
  rw [map_pow, hnEquiv_hnT2, t2_sq, map_one]

theorem hnT4_sq : hnT4 ^ 2 = 1 := by
  apply hnEquiv.injective
  rw [map_pow, hnEquiv_hnT4, t4_sq, map_one]

theorem hnT2_ne_one :
    hnT2 ≠ 1 := fun h => t2_ne_one (by rw [← hnEquiv_hnT2, h, map_one])

theorem hnT4_ne_one :
    hnT4 ≠ 1 := fun h => t4_ne_one (by rw [← hnEquiv_hnT4, h, map_one])

theorem hn_cycleTypes :
    ((hnStabEquiv.trans thetaS) ⟨hnT2, hnT2_mem⟩ : Equiv.Perm (Fin 12)).cycleType =
        Multiset.replicate 2 2 ∧
      ((hnStabEquiv.trans thetaS) ⟨hnT4, hnT4_mem⟩ : Equiv.Perm (Fin 12)).cycleType =
        Multiset.replicate 4 2 := by
  have e2 : hnStabEquiv ⟨hnT2, hnT2_mem⟩ = ⟨wG 12, t2_mem_stabHN⟩ :=
    Subtype.ext hnEquiv_hnT2
  have e4 : hnStabEquiv ⟨hnT4, hnT4_mem⟩ = ⟨wG 13, t4_mem_stabHN⟩ :=
    Subtype.ext hnEquiv_hnT4
  refine ⟨?_, ?_⟩
  · change ((thetaS (hnStabEquiv ⟨hnT2, hnT2_mem⟩) : alternatingGroup (Fin 12)) :
      Equiv.Perm (Fin 12)).cycleType = _
    rw [e2]; exact theta_t2_type
  · change ((thetaS (hnStabEquiv ⟨hnT4, hnT4_mem⟩) : alternatingGroup (Fin 12)) :
      Equiv.Perm (Fin 12)).cycleType = _
    rw [e4]; exact theta_t4_type

theorem hn_involution_cover
    (g : NativeSporadic.HN) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    IsConj hnT2 g ∨ IsConj hnT4 g := by
  have h1 : (hnEquiv g) ^ 2 = 1 := by rw [← map_pow, hg2, map_one]
  have h2 : hnEquiv g ≠ 1 := fun e => hg1 (hnEquiv.injective (by rw [e, map_one]))
  rcases involution_cover _ h1 h2 with h | h
  · left
    refine (isConj_hnEquiv_iff hnT2 g).1 ?_
    rw [hnEquiv_hnT2]; exact h
  · right
    refine (isConj_hnEquiv_iff hnT4 g).1 ?_
    rw [hnEquiv_hnT4]; exact h

theorem hn_not_isConj_t2_t4 :
    ¬ IsConj hnT2 hnT4 := fun h => by
  have h' := (isConj_hnEquiv_iff hnT2 hnT4).2 h
  rw [hnEquiv_hnT2, hnEquiv_hnT4] at h'
  exact not_isConj_t2_t4 h'

theorem hn_card_centralizer_t2 :
    Nat.card (Subgroup.centralizer {hnT2}) = 177408000 := by
  rw [card_centralizer_hnEquiv, hnEquiv_hnT2]; exact card_centralizer_t2

theorem hn_card_centralizer_t4 :
    Nat.card (Subgroup.centralizer {hnT4}) = 3686400 := by
  rw [card_centralizer_hnEquiv, hnEquiv_hnT4]; exact card_centralizer_t4

theorem hn_involution_classes :
    ∃ (θ : hnStab ≃* alternatingGroup (Fin 12)) (t₂ t₄ : NativeSporadic.HN)
      (h₂ : t₂ ∈ hnStab) (h₄ : t₄ ∈ hnStab),
      (θ ⟨t₂, h₂⟩ : Equiv.Perm (Fin 12)).cycleType = Multiset.replicate 2 2 ∧
      (θ ⟨t₄, h₄⟩ : Equiv.Perm (Fin 12)).cycleType = Multiset.replicate 4 2 ∧
      t₂ ^ 2 = 1 ∧ t₂ ≠ 1 ∧ t₄ ^ 2 = 1 ∧ t₄ ≠ 1 ∧
      (∀ g : NativeSporadic.HN, g ^ 2 = 1 → g ≠ 1 → IsConj t₂ g ∨ IsConj t₄ g) ∧
      ¬ IsConj t₂ t₄ ∧ Nat.card (Subgroup.centralizer {t₂}) = 177408000 ∧
      Nat.card (Subgroup.centralizer {t₄}) = 3686400 :=
  ⟨hnStabEquiv.trans thetaS, hnT2, hnT4, hnT2_mem, hnT4_mem, hn_cycleTypes.1, hn_cycleTypes.2,
    hnT2_sq, hnT2_ne_one, hnT4_sq, hnT4_ne_one, hn_involution_cover, hn_not_isConj_t2_t4,
    hn_card_centralizer_t2, hn_card_centralizer_t4⟩

end CFSG.Sporadic.HN.Local
