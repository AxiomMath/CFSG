module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L71

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

namespace T73a

theorem sylow_line (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) :
    S ⊓ Subgroup.centralizer (F : Set G) ≤ thetaOf θ F ∧
      IsPGroup r ↥(S ⊓ Subgroup.centralizer (F : Set G)) ∧
      Nat.Coprime ((S ⊓ Subgroup.centralizer (F : Set G)).relIndex (thetaOf θ F)) r ∧
      A ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G) := by
  obtain ⟨a, ha, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  rw [centralizer_zpowers_eq_singleton, h.isFunctor.thetaOf_zpowers ha ha1]
  exact sylow_of_isSr h hr hS ha ha1

end T73a

theorem zOf_inf_centralizer_le
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    zOf (S ⊓ Subgroup.centralizer (F : Set G)) ⊓ Subgroup.centralizer (E : Set G) ≤
      zOf (S ⊓ Subgroup.centralizer (E : Set G)) := by
  obtain ⟨hPH, hP, hidx, hAP⟩ := T73a.sylow_line h hr hS hB.mem
  have hkey := L71.zOf_inf_centralizer_eq (isRegFam_ind_E_of_typeB h hB) hr.1 hPH hP hidx hAP
    hF.1 (inf_line_eq_bot_of_typeB h hB hF hFE)
  intro x hx
  obtain ⟨hxF, hxE⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxS, hxc⟩ := mem_zOf_iff.mp hxF
  have hx' : x ∈ zOf (S ⊓ Subgroup.centralizer (E : Set G) ⊓
      Subgroup.centralizer (F : Set G)) :=
    mem_zOf_iff.mpr ⟨⟨⟨(Subgroup.mem_inf.mp hxS).1, hxE⟩, (Subgroup.mem_inf.mp hxS).2⟩,
      fun w hw => hxc w ⟨hw.1.1, hw.2⟩⟩
  rw [hkey] at hx'
  exact hx'.1

theorem zOf_le_sup
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    (hB : TypeBCore p A θ E K) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A)
    (_hFE : F ≠ E) :
    zOf (S ⊓ Subgroup.centralizer (F : Set G)) ≤
      (zOf S ⊓ Subgroup.centralizer (F : Set G)) ⊔
        (zOf (S ⊓ Subgroup.centralizer (F : Set G)) ⊓ Subgroup.centralizer (E : Set G)) := by
  obtain ⟨-, -, -, hAP⟩ := T73a.sylow_line h hr hS hF
  obtain ⟨f, -, hf1, hFf⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  have hfF : f ∈ F := hFf ▸ Subgroup.mem_zpowers f
  have hCF : Subgroup.centralizer (F : Set G) = Subgroup.centralizer {f} := by
    rw [← hFf, centralizer_zpowers_eq_singleton]
  set X := zOf (S ⊓ Subgroup.centralizer (F : Set G)) with hX
  have hXA : A ≤ Subgroup.normalizer (X : Set G) := fun g hg => mem_normalizer_zOf (hAP hg)
  have hXS : X ≤ S ⊓ Subgroup.centralizer (F : Set G) := zOf_le _
  have hcop : Nat.Coprime p (Nat.card X) :=
    hS.1.1.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le (hXS.trans inf_le_left))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p 2
    h.prime A X h.elemAbelian h.card.ge hXA hcop
  refine hgen.symm.le.trans (iSup_le fun B => iSup_le fun hB2 => ?_)
  by_cases hFB : F ≤ B
  · by_cases hEB : E ≤ B
    · exact (inf_le_inf_left X (Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr hEB))).trans le_sup_right
    · have hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ ¬ E ≤ B :=
        Or.inr ⟨E, K, hB, hEB⟩
      have h1 : X ⊓ Subgroup.centralizer (B : Set G) =
          zOf S ⊓ Subgroup.centralizer (B : Set G) := by
        rw [← lemma_7_1_b h hr hS hB2 hT, hX, hCF]
        exact lemma_7_1_a h hr hS hB2 hT (hFB hfF) hf1
      rw [h1]
      exact (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hFB))).trans
        le_sup_left
  · have hdisj : B ⊓ F = ⊥ := inf_eq_bot_of_not_le h.prime (by rw [hF.2, pow_one]) hFB
    have hcard := card_sup_of_le_elemAbelian h.elemAbelian hB2.1 hF.1 hdisj
    have hsup : B ⊔ F = A := Subgroup.eq_of_le_of_card_ge (sup_le hB2.1 hF.1) (by
      rw [hcard, hB2.2, hF.2, h.card]
      exact (by ring : p ^ 3 = p ^ 2 * p ^ 1).le)
    intro x hx
    have hxA : x ∈ Subgroup.centralizer (A : Set G) := by
      rw [← hsup, centralizer_sup]
      exact ⟨hx.2, (hXS hx.1).2⟩
    exact Subgroup.mem_sup_right ⟨hx.1, Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr hB.mem.1) hxA⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
