module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace O8H

variable {G : Type} [Group G]

theorem conjugate_conjugate (I : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate I a) b = CFSG.conjugate I (a * b) := by
  ext g
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, by group⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨_, ⟨h, hh, rfl⟩, by group⟩

theorem conjugate_one (I : Subgroup G) : CFSG.conjugate I 1 = I := by
  ext g
  simp [CFSG.conjugate]

theorem conjugate_eq_self_iff (I : Subgroup G) (g : G) :
    CFSG.conjugate I g = I ↔ g ∈ Subgroup.normalizer (I : Set G) := by
  rw [← inv_mem_iff (x := g), Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

theorem mem_normalizer_of_card_two [Finite G] {H I : Subgroup G}
    (h2 : Nat.card {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate I h} = 2) {x : G}
    (hxH : x ∈ H) (hx : Odd (orderOf x)) : x ∈ Subgroup.normalizer (I : Set G) := by
  by_contra hxN
  have hfin : Finite {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate I h} :=
    Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have h01 : CFSG.conjugate I x ≠ I := fun h => hxN ((conjugate_eq_self_iff I x).mp h)
  have hx2 : CFSG.conjugate I (x * x) = I := by
    by_contra h02
    have h12 : CFSG.conjugate I (x * x) ≠ CFSG.conjugate I x := by
      intro h
      rw [← conjugate_conjugate] at h
      apply h01
      have h' := congrArg (fun J => CFSG.conjugate J x⁻¹) h
      simp only [conjugate_conjugate, mul_inv_cancel_right, mul_inv_cancel] at h'
      rw [conjugate_one] at h'
      exact h'
    let f : Fin 3 → {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate I h} :=
      ![⟨I, 1, H.one_mem, (conjugate_one I).symm⟩, ⟨_, x, hxH, rfl⟩,
        ⟨_, x * x, H.mul_mem hxH hxH, rfl⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have h := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;>
        first | exact h01 h.symm | exact h01 h | exact h02 h.symm | exact h02 h |
          exact h12 h.symm | exact h12 h
    have := Nat.card_le_card_of_injective f hf
    rw [h2, Nat.card_fin] at this
    omega
  apply hxN
  obtain ⟨k, hk⟩ := hx
  have hx' : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [hx']
  exact Subgroup.pow_mem _ ((conjugate_eq_self_iff I _).mp hx2) _

theorem isSubnormal_sup {Y X : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    IsSubnormal Y (Y ⊔ X) :=
  IsSubnormal.step le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Subgroup.le_normalizer hXY)) (IsSubnormal.refl _)

variable [Finite G]

theorem le_normalizer_of_mem_cComp (h121 : Id2519.Prop121Three) (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (hq : QTKECore G) {Y X J : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hX : Odd (Nat.card X))
    (hY : pCoreOf 2 Y ≠ ⊥) (hJ : J ∈ cComp Y) : X ≤ Subgroup.normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub := isSubnormal_sup hXY
  have hJH : J ∈ cComp (Y ⊔ X) := cComp_mem_of_subnormal hsub hJ
  have hH : pCoreOf 2 (Y ⊔ X) ≠ ⊥ := fun h =>
    hY (le_bot_iff.mp ((A4.pCoreOf_le_of_subnormal 2 hsub).trans h.le))
  rcases h121 G hs hna hq (Y ⊔ X) hH J hJH with hN | ⟨h2, -⟩
  · exact le_sup_right.trans hN
  · intro x hx
    exact mem_normalizer_of_card_two h2 ((le_sup_right : X ≤ Y ⊔ X) hx)
      (hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx))

end O8H

end CFSG.Quasithin.Vol2.Ch11.SecD
