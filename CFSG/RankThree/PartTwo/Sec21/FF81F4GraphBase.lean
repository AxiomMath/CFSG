
module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Outer
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.SeitzReduction.F4Pilot

theorem f4_exists_model {X : Type} [Group X] {Y : Subgroup X}
    (h : ChevalleyExceptionalModel (↥Y) .F4 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime), Nat.card K = 2 ∧
      Nonempty (↥Y ≃* adjointGroup ReeTag.F4.tag K) := by
  have hm : UntwistedChevalleyModel (↥Y) .F4 (2 ^ 1) := h.2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  have hK' : Nat.card K = 2 ^ 1 := hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) hK'
  exact ⟨K, inferInstance, inferInstance, this, by simpa using hK, ⟨e⟩⟩

theorem f4_center_trivial {K : Type} [Field K] [Finite K] :
    ∀ z : adjointGroup ReeTag.F4.tag K, (∀ w, z * w = w * z) → z = 1 := by
  intro z hz
  have : z ∈ Subgroup.center (adjointGroup ReeTag.F4.tag K) :=
    Subgroup.mem_center_iff.2 fun w => (hz w).symm
  rw [center_adjointGroup_eq_bot] at this
  exact Subgroup.mem_bot.1 this

theorem f4_outer_involutions {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∀ α β : MulAut (adjointGroup ReeTag.F4.tag K), α ^ 2 = 1 → β ^ 2 = 1 →
      α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range →
      β ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range →
        ∃ h : adjointGroup ReeTag.F4.tag K, β = MulAut.conj h * α * (MulAut.conj h)⁻¹ := by
  intro α β hα hβ hαo hβo
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  exact even_F4_outer_involutions_inner_conj (le_refl 1) K hK' α β hα hβ hαo hβo

section Transport

variable {X : Type} [Group X] {Y : Subgroup X} {C : Type} [Group C] (e : ↥Y ≃* C)

def fixSub (α : MulAut C) : Subgroup C := α.toMonoidHom.eqLocus (MonoidHom.id C)

def embedY (ψ : MulAut C) : C →* X :=
  (Y.subtype.comp e.symm.toMonoidHom).comp ψ.symm.toMonoidHom

theorem embedY_injective (ψ : MulAut C) : Function.Injective (embedY e ψ) := by
  intro a b hab
  have h1 : (e.symm (ψ.symm a) : X) = (e.symm (ψ.symm b) : X) := hab
  exact ψ.symm.injective (e.symm.injective (Subtype.ext h1))

theorem embedY_apply (ψ : MulAut C) (c : C) : embedY e ψ c = (e.symm (ψ.symm c) : X) := rfl

theorem inf_cen_eq_map {τ : X} (hτ : τ ∈ Nor Y) (ψ : MulAut C) (Γ' : Subgroup C)
    (hfix : (fixSub (indAut e hτ)).map ψ.toMonoidHom = Γ') :
    Y ⊓ Cen τ = Γ'.map (embedY e ψ) := by
  subst hfix
  ext x
  constructor
  · rintro ⟨hxY, hxC⟩
    have hxC' : τ * x * τ⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_singleton_iff.1 hxC]; group
    refine ⟨ψ (e ⟨x, hxY⟩), ⟨e ⟨x, hxY⟩, ?_, rfl⟩, ?_⟩
    · show indAut e hτ (e ⟨x, hxY⟩) = e ⟨x, hxY⟩
      apply e.symm.injective
      apply Subtype.ext
      rw [indAut_apply, MulEquiv.symm_apply_apply]
      exact hxC'
    · rw [embedY_apply]
      simp
  · rintro ⟨g, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : indAut e hτ w = w := hw
    have hx : embedY e ψ (ψ.toMonoidHom w) = (e.symm w : X) := by
      rw [embedY_apply]; simp
    rw [hx]
    refine ⟨(e.symm w).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := indAut_apply e hτ w
    rw [hw'] at h1
    calc (e.symm w : X) * τ = τ * (e.symm w : X) * τ⁻¹ * τ := by rw [← h1]
      _ = τ * (e.symm w : X) := by group

end Transport

section F4Facts

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_fixSub_map_eq (hK : Nat.card K = 2) {α : MulAut (adjointGroup ReeTag.F4.tag K)}
    (hα : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range) :
    ∃ ψ : MulAut (adjointGroup ReeTag.F4.tag K),
      (fixSub α).map ψ.toMonoidHom = reeFixed ReeTag.F4 K 0 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨ψ, -, -, -, hfix, -⟩ :=
    even_F4_all_outer_involutions_canonical (f := 1) (le_refl 1) K hK' α hα hαo
  refine ⟨ψ, hfix.trans ?_⟩
  ext g
  rw [mem_reeFixed, ← ReeTag.finiteReeAut_eq_reeAut, finiteReeAut_zero_F4]
  simp [MonoidHom.eqLocus, pow_one]

theorem factorization_two_card_Gamma : (35942400 : ℕ).factorization 2 = 12 := by
  have h : (35942400 : ℕ) = 2 ^ 12 * 8775 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

end F4Facts

theorem kf_F4Graph_of_gamma
    (hΓ : ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
      ∃ V₀ : Subgroup (adjointGroup ReeTag.F4.tag K),
        IsSylowOf 2 V₀ (reeFixed ReeTag.F4 K 0) ∧ invClosure V₀ ≠ V₀) : KF_F4Graph := by
  intro X _ _ Y hY τ hτ2 hτN hout
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := f4_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ2' : τ ^ 2 = 1 := by rw [← hτ2]; exact pow_orderOf_eq_one τ
  have hα2 := indAut_sq e hτN hτ2'
  have hαo := (indAut_not_inner_iff e hτN).2 hout
  obtain ⟨ψ, hψ⟩ := exists_fixSub_map_eq hK hα2 hαo
  have hH := inf_cen_eq_map e hτN ψ _ hψ
  have hinj := embedY_injective e ψ
  have hcard : Nat.card ↥(Y ⊓ Cen τ) = 35942400 := by
    rw [hH, Subgroup.card_map_of_injective hinj,
      CFSG.RankThree.PartTwo.Census.Carrier.Tits.card_reeFixed hK]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]; norm_num
  · intro V hV
    have hc := isSylowOf_card_p hV
    rw [hcard, factorization_two_card_Gamma] at hc
    refine ⟨by rw [hc], ?_⟩
    obtain ⟨V₀, hV₀, hV₀ne⟩ := hΓ K hK
    have : Finite (adjointGroup ReeTag.F4.tag K) := by
      have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
      infer_instance
    have hc₀ := isSylowOf_card_p hV₀
    rw [CFSG.RankThree.PartTwo.Census.Carrier.Tits.card_reeFixed hK] at hc₀
    have hV₁ : IsSylowOf 2 (V₀.map (embedY e ψ)) (Y ⊓ Cen τ) := by
      refine isSylowOf_of_card_p ?_ ?_
      · rw [hH]; exact Subgroup.map_mono hV₀.1
      · rw [Subgroup.card_map_of_injective hinj, hc₀, hcard]
    refine forall_isSylowOf_of_one hV₁ (fun V => invClosure V ≠ V) ?_ ?_ V hV
    · intro g _ V' hV' heq
      apply hV'
      rw [invClosure_conjBy] at heq
      exact (Subgroup.map_injective (MulAut.conj g).injective) heq
    · exact (invClosure_ne_iff_map _ hinj V₀).2 hV₀ne
  · intro σ hσ hσ2 hσY
    have hσ2' : σ ^ 2 = 1 := by rw [← hσ2]; exact pow_orderOf_eq_one σ
    obtain ⟨c, hcY, hc⟩ := exists_conj_of_outer e f4_center_trivial (f4_outer_involutions hK) hτN
      hτ2' hout hσ hσ2' hσY
    refine ⟨c⁻¹, Subgroup.mem_sup_left (Y.inv_mem hcY), ?_⟩
    rw [← hc]; group

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
