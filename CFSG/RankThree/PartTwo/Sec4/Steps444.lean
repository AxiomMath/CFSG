module

public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Steps434

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem rank3II_4_35 :
    ∀ (G : Type) [Group G] [Finite G] (A M Q : Subgroup G), Ctx434 G A M Q →
      ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A :=
  fun _ _ _ _ _ _ h _ hx hx3 => h.rank3II_4_35 hx hx3

theorem rank3II_4_36 :
    ∀ (G : Type) [Group G] [Finite G] (A M Q : Subgroup G), Ctx434 G A M Q →
      inSubgroup generalizedFitting (Subgroup.centralizer (layer G : Set G)) = CFSG.pCore 3 G :=
  fun _ _ _ _ _ _ h => h.rank3II_4_36

theorem rank3II_4_38 :
    ∀ (G : Type) [Group G] [Finite G] (A M Q : Subgroup G), Ctx434 G A M Q →
      (CFSG.pCore 3 G = ⊥ ∧ generalizedFitting G = layer G ∧ IsSimpleGroup (layer G)) ∨
        (A ⊓ CFSG.pCore 3 G = A ⊓ Subgroup.centralizer (layer G : Set G) ∧
          Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3) :=
  fun _ _ _ _ _ _ h => h.rank3II_4_38

theorem Ctx444.rank3II_4_45 {G : Type} [Group G] [Finite G] {A M : Subgroup G}
    (h : Ctx444 G A M) {x : G} (hx : x ∈ Subgroup.centralizer (A : Set G)) (hx3 : x ^ 3 = 1) :
    x ∈ A :=
  mem_of_mem_centralizer_of_gamma_le h.isE27 h.gamma_le h.pRank_eq hx hx3

theorem rank3II_4_45 : Item4_45 := fun _ _ _ _ _ h _ hx hx3 => h.rank3II_4_45 hx hx3

variable {G : Type*} [Group G] [Finite G]

theorem map_conj_mem_thetaComponents {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) (g : G) :
    L.map (MulAut.conj g).toMonoidHom ∈ thetaComponents 3 G :=
  map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj g) hL

theorem commutator_le_normalizer_of_forall {A : Subgroup G}
    (hA : ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G)) (Q : Subgroup G)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) :
    ⁅Q, A⁆ ≤ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.commutator_le]
  intro q _ a ha
  have haL' := hA _ (map_conj_mem_thetaComponents hL q⁻¹) ha
  have hback : (L.map (MulAut.conj q⁻¹).toMonoidHom).map (MulAut.conj q).toMonoidHom = L := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id L
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have h1 : q * a * q⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    have := Subgroup.mem_map_of_mem (MulAut.conj q).toMonoidHom haL'
    rw [Subgroup.map_equiv_normalizer_eq, hback] at this
    simpa using this
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hA L hL ha))

theorem Ctx444.commutator_le_normalizer (h45 : Item4_5) {G : Type} [Group G] [Finite G]
    {A M : Subgroup G} (h : Ctx444 G A M) (Q : Subgroup G) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) : ⁅Q, A⁆ ≤ Subgroup.normalizer (L : Set G) :=
  commutator_le_normalizer_of_forall
    (fun L' hL' => h45 G h.sectionFourHyp A h.isE27.isPGroup
      (Or.inr ⟨h.isE27.1, 3, le_rfl, by rw [h.isE27.2]; norm_num⟩) L' hL') Q hL

end CFSG.RankThree.PartTwo.Sec4
