module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAux68
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.StructureAux

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Sec6S31

section Generic

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem card_cenIn_eq_pow (h : SemisimpleAction p A G) {c : ℕ}
    (hc : ∀ J ∈ lcal G, Nat.card (cenIn J (norIn A J)) = c) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card (cenIn G A) = c ^ m := by
  classical
  have hG := h.semisimple
  let S : Set (Subgroup Γ) := {X | ∃ J ∈ lcal G, X = smear J A}
  have hD : IsDirectProduct S (cenIn G A) := h.isDirectProduct_smear
  have : Fintype S := Fintype.ofFinite S
  have hcardX : ∀ X : S, Nat.card (X : Subgroup Γ) = c := by
    rintro ⟨_, J, hJ, rfl⟩
    rw [← hc J hJ]
    refine Nat.card_eq_of_bijective
      (fun y => ⟨crd G J y, crd_mem_cenIn_norIn h hJ (h.smear_le_cenIn hJ y.2)⟩) ⟨?_, ?_⟩
    · intro u v huv
      exact Subtype.ext (crd_inj_smear h hJ u.2 v.2 (congrArg Subtype.val huv))
    · intro z
      obtain ⟨y, hys, hyz⟩ := exists_smear_crd h hJ z.2
      exact ⟨⟨y, hys⟩, Subtype.ext hyz⟩
  have h1 : Nat.card (cenIn G A) = ∏ X : S, Nat.card (X : Subgroup Γ) := by
    rw [← Nat.card_congr hD.equiv.toEquiv, Nat.card_pi]
  obtain ⟨J₀, hJ₀⟩ : (lcal G).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply h.ne_bot
    rw [← hG.isDirectProduct_lcal.sSup_eq, hcon, sSup_empty]
  refine ⟨Fintype.card S, Fintype.card_pos_iff.mpr ⟨⟨smear J₀ A, J₀, hJ₀, rfl⟩⟩, ?_⟩
  rw [h1]
  simp [hcardX, Finset.prod_const]

end Generic

section Models

variable {p : ℕ} {X X' : Type*} [Group X] [Finite X] [Group X'] [Finite X']

omit [Finite X'] in
theorem card_fixed_eq_of_mulEquiv
    (h : NearSimple p X) (e : X ≃* X') {f : MulAut X}
    {f' : MulAut X'} (hf : orderOf f = p) (hf' : orderOf f' = p) :
    Nat.card (signalizerFixedSubgroup f) = Nat.card (signalizerFixedSubgroup f') := by
  have := Fact.mk h.prime
  set g : MulAut X := MulAut.congr e.symm f' with hg
  have hgo : orderOf g = p := by rw [hg, orderOf_congr, hf']
  obtain ⟨e₁⟩ := NearModels.signalizerFixedSubgroup_mulEquiv_of_orderOf_eq
    (near_aut_pSubgroup_card_dvd h) hf hgo
  have h2 := ModelFacts.card_fixed_congr e g
  have h3 : MulAut.congr e g = f' := by
    ext x
    simp [hg, MulAut.congr_apply]
  rw [h3] at h2
  rw [Nat.card_congr e₁.toEquiv, ← h2]

end Models

section Counterexample

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem exists_card_cenIn_norIn
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ∃ f : MulAut ↥J, orderOf f = p ∧
      Nat.card (cenIn J (norIn A J)) = Nat.card (signalizerFixedSubgroup f) := by
  obtain ⟨f, hf, hC, -⟩ := h.exists_frame_data hJ
  refine ⟨f, hf, ?_⟩
  rw [← hC, Subgroup.card_map_of_injective J.subtype_injective]

end Counterexample

section Main

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem nonempty_mulEquiv_of_mem_rSet
    (h : Counterexample p A θ) {E F J K' : Subgroup G}
    (hE : E ∈ rSet p A θ) (hF : F ∈ rSet p A θ) (hJ : J ∈ lcal (thetaOf θ E))
    (hK : K' ∈ lcal (thetaOf θ F)) : Nonempty (↥J ≃* ↥K') := by
  have HE := hyp h hE
  have HF := hyp h hF
  have hJ' : J ∈ lcal (kOf (thetaOf θ E)) := HE.lcal_kOf ▸ hJ
  have hK' : K' ∈ lcal (kOf (thetaOf θ F)) := HF.lcal_kOf ▸ hK
  obtain ⟨f, hf, hcf⟩ := exists_card_cenIn_norIn HE.semisimpleAction hJ'
  obtain ⟨f', hf', hcf'⟩ := exists_card_cenIn_norIn HF.semisimpleAction hK'
  have hcE : ∀ J₁ ∈ lcal (kOf (thetaOf θ E)),
      Nat.card (cenIn J₁ (norIn A J₁)) = Nat.card (cenIn J (norIn A J)) := by
    intro J₁ hJ₁
    obtain ⟨f₁, hf₁, hcf₁⟩ := exists_card_cenIn_norIn HE.semisimpleAction hJ₁
    obtain ⟨e⟩ := nonempty_mulEquiv h hE hJ₁ hJ'
    rw [hcf₁, hcf, card_fixed_eq_of_mulEquiv (HE.semisimpleAction.nearSimple hJ₁) e hf₁ hf]
  have hcF : ∀ J₁ ∈ lcal (kOf (thetaOf θ F)),
      Nat.card (cenIn J₁ (norIn A J₁)) = Nat.card (cenIn K' (norIn A K')) := by
    intro J₁ hJ₁
    obtain ⟨f₁, hf₁, hcf₁⟩ := exists_card_cenIn_norIn HF.semisimpleAction hJ₁
    obtain ⟨e⟩ := nonempty_mulEquiv h hF hJ₁ hK'
    rw [hcf₁, hcf', card_fixed_eq_of_mulEquiv (HF.semisimpleAction.nearSimple hJ₁) e hf₁ hf']
  obtain ⟨m, hm, hmc⟩ := card_cenIn_eq_pow HE.semisimpleAction hcE
  obtain ⟨m', hm', hmc'⟩ := card_cenIn_eq_pow HF.semisimpleAction hcF
  rw [cenIn_kOf_eq h hE] at hmc
  rw [cenIn_kOf_eq h hF] at hmc'
  refine nonempty_mulEquiv_of_card_pow_eq (HE.semisimpleAction.nearSimple hJ')
    (HF.semisimpleAction.nearSimple hK') hf hf' hm hm' ?_
  rw [← hcf, ← hcf', ← hmc, ← hmc']

end Main

end Sec6S31

end CFSG.SignalizerFunctorTheorem.McBride.Near
