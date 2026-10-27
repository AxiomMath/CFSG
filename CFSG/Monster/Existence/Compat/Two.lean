module

public import CFSG.Monster.Existence.Compat.Shapes
public import CFSG.Monster.Existence.Compat.Triangles
public import CFSG.Monster.Existence.Compat.Orbits
public import CFSG.Monster.Existence.Compat.Sp8
public import CFSG.Monster.Existence.Compat.U62

public section

namespace CFSG.Monster.Existence.Compat

open CFSG CFSG.Open CFSG.Blueprint CFSG.Monster.Existence

variable {G : Type} [Group G]

theorem card_cent2_of_shape_one (F : TwoAFacts) {H : Subgroup G} (h : TwoPointShape H 1) :
    Nat.card H = 2 ^ 2 * ordTwistedE6 2 := by
  obtain ⟨N, hn, -, hN, hm⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hN, F.e6_card _ hm, mul_comm]

theorem card_of_layered (F : TwoAFacts) {K : Subgroup G}
    (h : HasLayeredTwoShape K 3 20 fun X _ => LieModel X .PSU 6 2 1) :
    Nat.card K = 2 ^ 23 * ordTwistedA 5 2 := by
  obtain ⟨N, hn, N₀, -, -, -, -, -, hN, hm⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hN, F.u62_card _ hm, mul_comm]

theorem monsterHasLongTriangleShape_of_layered {K : Subgroup G}
    (h : HasLayeredTwoShape K 3 20 fun X _ => LieModel X .PSU 6 2 1) :
    MonsterHasLongTriangleShape K := by
  obtain ⟨N, hn, N₀, -, -, -, -, -, hN, hm⟩ := h
  obtain ⟨e⟩ := u62_equiv_of_lieModel _ hm
  exact ⟨N, hn, hN, ⟨e⟩⟩

theorem pointStab_triple (α β γ : G) : pointStab ({α, β, γ} : Set G) = cent2 α β ⊓ cent γ := by
  simp only [pointStab, iInf_insert, iInf_singleton, cent2, inf_assoc]

theorem card_identity : 2 ^ 2 * ordTwistedE6 2 = 2 ^ 23 * ordTwistedA 5 2 * 3968055 := by
  decide +kernel

theorem monsterTwoAGraphData_of_isTwoAGraphData (F : TwoAFacts) {a z : G} (ha : orderOf a = 2)
    (h : IsTwoAGraphData a z) : MonsterTwoAGraphData a z := by
  obtain ⟨h31, c, hcinj, hc0, hc1, hc2, hcord, hcover, hocc, hshape, h3iii, h3iv, h3v, -, h4edge,
    h4stab, h4gen⟩ := h
  have hex : ∀ i, ∃ b, IsConj a b ∧ IsConj (a * b) (c i) := by
    intro i
    obtain ⟨α, β, hα, hβ, hαβ⟩ := hocc i
    obtain ⟨g, rfl⟩ := isConj_iff.1 hα
    refine ⟨g⁻¹ * β * g, hβ.trans (isConj_iff.2 ⟨g⁻¹, by simp [mul_assoc]⟩), ?_⟩
    have : IsConj (g * a * g⁻¹ * β) (a * (g⁻¹ * β * g)) :=
      isConj_iff.2 ⟨g⁻¹, by simp [mul_assoc]⟩
    exact this.symm.trans hαβ
  choose β hβa hβc using hex
  have hβ0 : β 0 = a := by
    have h1 : IsConj (a * β 0) 1 := by simpa [hc0] using hβc 0
    have h2 : a * β 0 = 1 := isConj_one_left.1 h1
    rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_isConj ha (IsConj.refl a)]
  have conv3 : ∀ x, IsConj x (a * β 3) → IsConj x (c 3) := fun x hx => hx.trans (hβc 3)
  have conv3' : ∀ x, IsConj x (c 3) → IsConj x (a * β 3) := fun x hx => hx.trans (hβc 3).symm
  refine ⟨fun β' hβ' β'' hβ'' hconj => h31 a β' β'' (IsConj.refl a) hβ' hβ'' hconj, β, hβa, hβ0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => hcinj i j ((hβc i).symm.trans (hij.trans (hβc j)))
  · intro γ hγ
    obtain ⟨i, hi⟩ := hcover a γ (IsConj.refl a) hγ
    exact ⟨i, hi.trans (hβc i).symm⟩
  · exact hc1.trans (hβc 1).symm
  · exact hc2.trans (hβc 2).symm
  · exact fun i => (orderOf_eq_of_isConj (hβc i)).trans ((hcord i).trans rfl)
  · exact fun i => hasShape_of_twoPointShape F _ i
      (hshape a (β i) i (IsConj.refl a) (hβa i) (hβc i))
  ·
    intro β' hβ' hβ'3
    obtain ⟨hne, huniq, hsp⟩ := h3iii a β' (IsConj.refl a) hβ' (conv3 _ hβ'3)
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨γ, hγ⟩ := hne
      exact ⟨γ, hγ.1, conv3' _ hγ.2.1, hγ.2.2⟩
    · rintro γ γ' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
      exact huniq γ γ' h1 (conv3 _ h2) h3 h1' (conv3 _ h2') h3'
    · rintro γ ⟨h1, h2, h3⟩
      exact sp8_equiv_of_lieModel _ (hsp γ h1 (conv3 _ h2) h3)
  ·
    intro β' hβ' hβ'6
    obtain ⟨-, hnot, γ, hγ, hu⟩ := h3iv a β' (IsConj.refl a) hβ'
      (hβ'6.trans (hβc 6))
    have conv : ∀ γ, IsConj a (γ * β') ↔ IsConj a (β' * γ) := fun γ =>
      ⟨fun h => h.trans (isConj_mul_comm γ β'), fun h => h.trans (isConj_mul_comm β' γ)⟩
    exact ⟨hnot, γ, ⟨hγ.1, hγ.2.1, (conv γ).1 hγ.2.2⟩, fun y hy =>
      hu y ⟨hy.1, hy.2.1, (conv y).2 hy.2.2⟩⟩
  ·
    intro β' hβ' hβ'3
    exact h3v a β' (IsConj.refl a) hβ' (conv3 _ hβ'3)
  ·
    intro β' hβ' hedge
    have hα : IsConj a a := IsConj.refl a
    have hedge' : IsConj (a * β') (c 1) := hedge.symm.trans hc1
    obtain ⟨-, hlongcount⟩ := h4edge a β' hα hβ' hedge
    set S : Set G := {γ | ThirdVertex a a β' γ ∧ γ ≠ a * β'} with hS
    have hScard : S.ncard = 3968055 :=
      (ncard_longTriangles ha hα hβ' hedge).symm.trans hlongcount
    have hSfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
    have hlongiff : ∀ γ, IsLongTriangle a {a, β', γ} ↔ γ ∈ S := fun γ =>
      isLongTriangle_iff ha hα hβ' hedge
    have hmem : ∀ γ, γ ∈ S ↔ (IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ) ∧ γ ≠ a * β') :=
      fun γ => by
        show (IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ)) ∧ γ ≠ a * β' ↔ _
        simp only [and_assoc]
    have hcardH : Nat.card (cent2 a β') = 2 ^ 2 * ordTwistedE6 2 :=
      card_cent2_of_shape_one F (hshape a β' 1 hα hβ' hedge')
    have hstab : ∀ γ ∈ S, Nat.card ↥(cent2 a β' ⊓ cent γ) = 2 ^ 23 * ordTwistedA 5 2 := by
      intro γ hγ
      have h1 := (h4stab _ ((hlongiff γ).2 hγ)).2
      rw [pointStab_triple] at h1
      exact card_of_layered F h1
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 := ncard_thirdVertex ha hα hβ' hedge hSfin
      rw [hlongcount] at h1
      exact h1
    · rintro γ γ' hγ hγ'
      rw [← hmem] at hγ hγ'
      have hfin : Finite ↥(cent2 a β') :=
        Nat.finite_of_card_ne_zero (by rw [hcardH]; decide +kernel)
      have hstable : ∀ k ∈ cent2 a β', ∀ x ∈ S, k * x * k⁻¹ ∈ S := by
        intro k hk x hx
        have hka : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 hk.1
        have hkb : k * β' = β' * k := Subgroup.mem_centralizer_singleton_iff.1 hk.2
        obtain ⟨⟨hx1, hx2, hx3⟩, hx4⟩ := hx
        refine ⟨⟨hx1.trans (isConj_iff.2 ⟨k, rfl⟩), ?_, ?_⟩, ?_⟩
        · refine hx2.trans (isConj_iff.2 ⟨k, ?_⟩)
          calc k * (a * x) * k⁻¹ = (k * a) * x * k⁻¹ := by simp only [mul_assoc]
            _ = a * (k * x * k⁻¹) := by rw [hka]; simp only [mul_assoc]
        · refine hx3.trans (isConj_iff.2 ⟨k, ?_⟩)
          calc k * (β' * x) * k⁻¹ = (k * β') * x * k⁻¹ := by simp only [mul_assoc]
            _ = β' * (k * x * k⁻¹) := by rw [hkb]; simp only [mul_assoc]
        · intro hxe
          apply hx4
          have h1 : k * (a * β') * k⁻¹ = a * β' := by
            calc k * (a * β') * k⁻¹ = (k * a) * β' * k⁻¹ := by simp only [mul_assoc]
              _ = a * (k * β') * k⁻¹ := by rw [hka]; simp only [mul_assoc]
              _ = a * β' := by rw [hkb]; group
          rw [← h1] at hxe
          exact conj_injective hxe
      exact exists_conj_of_card (H := cent2 a β') (S := S) (n := 2 ^ 23 * ordTwistedA 5 2)
        hfin hSfin hstable hstab (by rw [hScard, hcardH]; exact card_identity.symm) hγ hγ'
    · intro γ hγ
      rw [← hmem] at hγ
      have h1 := (h4stab _ ((hlongiff γ).2 hγ)).2
      rw [pointStab_triple] at h1
      exact monsterHasLongTriangleShape_of_layered h1
    · obtain ⟨γ, δ, hlongγ, hδ, hδ1, hδ2, hsup, hsp⟩ := h4gen a β' hα hβ' hedge
      exact ⟨γ, δ, (hmem γ).1 ((hlongiff γ).1 hlongγ), hδ, conv3' _ hδ1, conv3' _ hδ2, hsup,
        sp8_equiv_of_lieModel _ hsp⟩

end CFSG.Monster.Existence.Compat
