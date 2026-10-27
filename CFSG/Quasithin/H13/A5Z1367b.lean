module

public import CFSG.Quasithin.H13.A5Y1367e

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

section Comp

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem eq_of_subnormal_qs {N M : Subgroup Γ} (hNM : IsSubnormal N M)
    (hqN : CFSG.IsQuasisimple ↥N) (hqM : CFSG.IsQuasisimple ↥M) : N = M := by
  have hle : N ≤ M := A3.subnormal_le hNM
  have hM : IsComponentOf M M := ⟨le_rfl, IsSubnormal.refl M, B1Red.isQuasisimple_to_open hqM⟩
  rcases B113.component_le_or_commutator_eq_bot hM hNM with h | h
  · exact le_antisymm hle h
  · exfalso
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact not_le_centralizer_self_of_qs hqN
      ((Subgroup.le_centralizer_iff.mp h).trans (Subgroup.centralizer_le fun x hx => hle hx))

omit [Finite Γ] in
theorem isComponentOf_of_le {N M J : Subgroup Γ} (hN : IsComponentOf N J) (hNM : N ≤ M)
    (hMJ : M ≤ J) : IsComponentOf N M :=
  ⟨hNM, A3.subnormal_of_le_of_le hN.2.1 hNM hMJ, hN.2.2⟩

end Comp

section List

variable {V : Type} [CommGroup V] [Finite V]

theorem le_or_le_of_component {G₁ G₂ J N : Subgroup (MulAut V)} (hsup : G₁ ⊔ G₂ = J)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hcomp : IsComponentOf N J) :
    N ≤ G₁ ∨ N ≤ G₂ := by
  have hq : CFSG.IsQuasisimple ↥N := B1Red.isQuasisimple_of_open hcomp.2.2
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hsup' : G₂ ⊔ G₁ = J := by rw [sup_comm]; exact hsup
  have hsub : ∀ {A B : Subgroup (MulAut V)}, A ⊔ B = J → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      IsSubnormal A J := fun {A B} hAB hcAB => by
    have hAJ : A ≤ J := hAB ▸ le_sup_left
    have hn := S153L.comp_normal_in_join hAB hcAB le_rfl fun g hg n hn =>
      A.mul_mem (A.mul_mem hg hn) (A.inv_mem hg)
    exact IsSubnormal.step hAJ ((Subgroup.normal_subgroupOf_iff hAJ).2 fun h k hh hk =>
      hn k hk h hh) (IsSubnormal.refl J)
  rcases B113.component_le_or_commutator_eq_bot hcomp (hsub hsup hc) with h1 | h1
  · exact Or.inl h1
  rcases B113.component_le_or_commutator_eq_bot hcomp (hsub hsup' hc') with h2 | h2
  · exact Or.inr h2
  exfalso
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2
  apply not_le_centralizer_self_of_qs hq
  have hJ : J ≤ Subgroup.centralizer (N : Set (MulAut V)) := by
    rw [← hsup]
    exact sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer_iff.mp h2)
  exact hcomp.1.trans hJ

theorem eq_of_components_le_factor {G N N' : Subgroup (MulAut V)} (hf : B56FactorList ↥G)
    (hN : IsComponentOf N G) (hN' : IsComponentOf N' G) : N = N' := by
  have hq := B1Red.isQuasisimple_of_open hN.2.2
  have hq' := B1Red.isQuasisimple_of_open hN'.2.2
  obtain ⟨hp, hne⟩ := qs_perfect_ne_bot hq
  obtain ⟨hp', -⟩ := qs_perfect_ne_bot hq'
  rcases S153L.factor_of_list hf with ⟨-, -, hFN⟩ | ⟨M, -, hFN⟩
  · exact absurd (le_bot_iff.mp (hFN.2.2.2 N hN.1 hp)) hne
  · have hNM := hFN.2.2.2 N hN.1 hp
    have hN'M := hFN.2.2.2 N' hN'.1 hp'
    have hqM : CFSG.IsQuasisimple ↥M := hFN.2.2.1.resolve_left fun h => hne (by
      rw [eq_bot_iff, ← h]
      exact hNM)
    rw [eq_of_subnormal_qs (A3.subnormal_of_le_of_le hN.2.1 hNM hFN.1) hq hqM,
      eq_of_subnormal_qs (A3.subnormal_of_le_of_le hN'.2.1 hN'M hFN.1) hq' hqM]

omit [Finite V] in
theorem factorList_of_sl3_two {G : Subgroup (MulAut V)}
    (e : ↥G ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) : B56FactorList ↥G :=
  Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, by simp, ⟨e⟩⟩)

theorem two_components_cases {J N N' : Subgroup (MulAut V)} (hN : IsComponentOf N J)
    (hN' : IsComponentOf N' J) (hne : N ≠ N')
    (h : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    ∃ G₁ G₂ : Subgroup (MulAut V), G₁ ⊔ G₂ = J ∧ G₁ ⊓ G₂ = ⊥ ∧
      (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧ B56FactorList ↥G₁ ∧ B56FactorList ↥G₂ ∧
      N ≤ G₁ ∧ N' ≤ G₂ := by
  have hq := B1Red.isQuasisimple_of_open hN.2.2
  have hq' := B1Red.isQuasisimple_of_open hN'.2.2
  have hfac : ∀ {G₁ G₂ : Subgroup (MulAut V)}, G₁ ⊔ G₂ = J → G₁ ⊓ G₂ = ⊥ →
      (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → B56FactorList ↥G₁ → B56FactorList ↥G₂ →
      ∃ G₁ G₂ : Subgroup (MulAut V), G₁ ⊔ G₂ = J ∧ G₁ ⊓ G₂ = ⊥ ∧
        (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧ B56FactorList ↥G₁ ∧ B56FactorList ↥G₂ ∧
        N ≤ G₁ ∧ N' ≤ G₂ := fun {G₁ G₂} hsup hinf hc hf₁ hf₂ => by
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    rcases le_or_le_of_component hsup hc hN with h1 | h1 <;>
      rcases le_or_le_of_component hsup hc hN' with h2 | h2
    · exact absurd (eq_of_components_le_factor hf₁ (isComponentOf_of_le hN h1 hG₁J)
        (isComponentOf_of_le hN' h2 hG₁J)) hne
    · exact ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, h1, h2⟩
    · exact ⟨G₂, G₁, by rw [sup_comm]; exact hsup, by rw [inf_comm]; exact hinf, hc', hf₂, hf₁,
        h1, h2⟩
    · exact absurd (eq_of_components_le_factor hf₂ (isComponentOf_of_le hN h1 hG₂J)
        (isComponentOf_of_le hN' h2 hG₂J)) hne
  rcases h with h1 | h2 | h3 | h4 | h5
  ·
    exfalso
    obtain ⟨hqF, -, -⟩ := h1
    have hFJ : quasithinGenFitting J ≤ J := quasithinGenFitting_le J
    have hFsub : IsSubnormal (quasithinGenFitting J) J :=
      IsSubnormal.step hFJ ((Subgroup.normal_subgroupOf_iff_le_normalizer hFJ).2
        (le_normalizer_quasithinGenFitting J)) (IsSubnormal.refl J)
    have key : ∀ {M : Subgroup (MulAut V)}, IsComponentOf M J → M = quasithinGenFitting J :=
      fun {M} hM => by
        have hqM := B1Red.isQuasisimple_of_open hM.2.2
        have hMF : M ≤ quasithinGenFitting J := by
          rcases B113.component_le_or_commutator_eq_bot hM hFsub with h | h
          · exact h
          · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
            exact (le_inf hM.1 h).trans (centralizer_quasithinGenFitting_le J)
        exact eq_of_subnormal_qs (A3.subnormal_of_le_of_le hM.2.1 hMF hFJ) hqM hqF
    exact hne ((key hN).trans (key hN').symm)
  ·
    exfalso
    obtain ⟨⟨e⟩, -, -⟩ := h2
    have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
    exact not_qs_of_le_solvable hN.1
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hq
  · obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ := h3
    exact hfac hsup hinf hc hf₁ hf₂
  ·
    exfalso
    obtain ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, h3, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
    have hMJ : G₁ ⊔ G₂ ≤ J := hJt ▸ le_sup_left
    have hs : IsSimpleGroup ↥G₁ :=
      @MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) e₁
    have hcard : Nat.card ↥G₁ = 360 := by
      rw [Nat.card_congr e₁.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hqG : CFSG.IsQuasisimple ↥G₁ :=
      S153L.comp_quasisimple_of_simple hs (by rw [hcard]; norm_num)
    have key : ∀ {M : Subgroup (MulAut V)}, IsComponentOf M J → M = G₁ := fun {M} hM => by
      have hqM := B1Red.isQuasisimple_of_open hM.2.2
      obtain ⟨hp, -⟩ := qs_perfect_ne_bot hqM
      have hMM : M ≤ G₁ ⊔ G₂ := by
        rw [← hp]
        exact (Subgroup.commutator_mono hM.1 hM.1).trans
          (commutator_le_of_zpowers hJt (mem_normalizer_sup ht₁ ht₂))
      rcases le_or_le_of_component rfl hc (isComponentOf_of_le hM hMM hMJ) with h | h
      · exact eq_of_subnormal_qs (A3.subnormal_of_le_of_le hM.2.1 h (le_sup_left.trans hMJ))
          hqM hqG
      · exfalso
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have : IsCyclic ↥G₂ := isCyclic_of_prime_card h3
        exact not_qs_of_le_solvable h inferInstance hqM
    exact hne ((key hN).trans (key hN').symm)
  · obtain ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, hG₂⟩ := h5
    have hf₂ : B56FactorList ↥G₂ := by
      rcases hG₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hπ⟩
      · exact factorList_of_sl3_two e₂
      · have hi := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
        let e₂ := MulEquiv.ofBijective π ⟨hi, hπ.1⟩
        exact Or.inl ⟨n, F, inferInstance, inferInstance, two_le_of_field hF, hF, ⟨e₂.symm⟩⟩
    exact hfac hsup hinf hc (factorList_of_sl3_two e₁) hf₂

end List

end CFSG.Quasithin.H13.A5
