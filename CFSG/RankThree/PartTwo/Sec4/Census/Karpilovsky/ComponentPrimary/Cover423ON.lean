module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentON
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.RigidOuter
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofMcL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank Subgroup
open CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple CFSG.Blueprint

@[expose] def Alt6Index9 (C : Type) [Group C] : Prop :=
  ∃ E : Subgroup C, E.Normal ∧ Nonempty (↥E ≃* alternatingGroup (Fin 6)) ∧
    Nat.card (C ⧸ E) = 9

theorem Alt6Index9.of_mulEquiv {C C' : Type} [Group C] [Group C'] (ψ : C ≃* C')
    (h : Alt6Index9 C) : Alt6Index9 C' := by
  obtain ⟨E, hE, ⟨eE⟩, hq⟩ := h
  refine ⟨E.map ψ.toMonoidHom, hE.map ψ.toMonoidHom ψ.surjective,
    ⟨(E.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.trans eE⟩, ?_⟩
  rw [← hq]
  exact (Nat.card_congr (QuotientGroup.congr E (E.map ψ.toMonoidHom) ψ rfl).toEquiv).symm

theorem center_eq_bot_of_equiv_alt6 {E : Type} [Group E] (eE : E ≃* alternatingGroup (Fin 6)) :
    Subgroup.center E = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup E := eE.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center E) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : E, a * b = b * a := fun a b =>
      ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a : a ∈ Subgroup.center E)) b).symm
    have hs : Group.IsSolvable E := (IsSimpleGroup.comm_iff_isSolvable (G := E)).1 hc
    exact not_isSolvable_alt_six
      (Group.isSolvable_of_isSolvable_injective (f := eE.symm.toMonoidHom) eE.symm.injective)

theorem Alt6Index9.theta_eq_bot {C : Type} [Group C] [Finite C] (h : Alt6Index9 C) :
    aschbacherSolvableCore 3 C = ⊥ := by
  obtain ⟨E, hE, ⟨eE⟩, hq⟩ := h
  obtain ⟨hsol, -, h3, -⟩ := solvable_prime_complement_core_characterization (H := C) Nat.prime_three
  set N := aschbacherSolvableCore 3 C with hN
  have hNn : N.Normal := by
    obtain ⟨-, hchar, -⟩ := solvable_prime_complement_core_characterization (H := C) Nat.prime_three
    exact inferInstance
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥E := eE.isSimpleGroup
  have hNE : N ⊓ E = ⊥ := by
    have hnorm : ((N ⊓ E).subgroupOf E).Normal := Subgroup.Normal.subgroupOf inferInstance E
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ E).subgroupOf E) with h1 | h1
    · rw [Subgroup.subgroupOf_eq_bot] at h1
      exact h1.eq_bot_of_le inf_le_right
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h1
      have hEN : E ≤ N := h1.trans inf_le_left
      have : Group.IsSolvable ↥E :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hEN)
          (Subgroup.inclusion_injective hEN)
      exact not_isSolvable_alt_six
        (Group.isSolvable_of_isSolvable_injective (f := eE.symm.toMonoidHom) eE.symm.injective)
  let f : ↥N →* C ⧸ E := (QuotientGroup.mk' E).comp N.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hnE : (n : C) ∈ E := (QuotientGroup.eq_one_iff (n : C)).1 hn
    have : (n : C) ∈ N ⊓ E := ⟨n.2, hnE⟩
    rw [hNE, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hdvd : Nat.card N ∣ 9 := hq ▸ Subgroup.card_dvd_of_injective f hf
  have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have h1 : Nat.card N = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm (by simpa using Nat.Coprime.pow_left 2 hcop)) hdvd
  exact Subgroup.eq_bot_of_card_eq N h1

theorem Alt6Index9.pow_nine_eq_one {C : Type} [Group C] (h : Alt6Index9 C) {g : C}
    (hg : ∀ c : C, g * c = c * g) : g ^ 9 = 1 := by
  obtain ⟨E, hE, ⟨eE⟩, hq⟩ := h
  have hmem : g ^ 9 ∈ E := by
    have h1 : ((g : C ⧸ E)) ^ 9 = 1 := by
      rw [← hq]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hcen : (⟨g ^ 9, hmem⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro e
    exact Subtype.ext (Commute.pow_left (hg e) 9).eq.symm
  rw [center_eq_bot_of_equiv_alt6 eE, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen


theorem Alt6Index9.centralizer_of_conj {G : Type} [Group G] {x b g : G} (hb : b = g * x * g⁻¹)
    (h : Alt6Index9 ↥(centralizer ({x} : Set G))) :
    Alt6Index9 ↥(centralizer ({b} : Set G)) := by
  subst hb
  exact h.of_mulEquiv (Sec4.Res4Seven.centralizerMapEquiv (MulAut.conj g) x)

theorem alphaNine_of_data {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hOut : ∀ σ : MulAut S, ∃ k : ℕ, σ ^ (2 ^ k) ∈ (MulAut.conj : S →* MulAut S).range)
    (hNO : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.NoOuterFixesCentralizer 3 S)
    (hA : ∀ b : S, orderOf b = 3 → Alt6Index9 ↥(centralizer ({b} : Set S))) :
    Coordinator.Cover423.AlphaNine S := by
  intro D hD hcard
  have hD1 : D ≠ ⊥ := by
    rintro rfl
    simp at hcard
  have hb3 : ∀ b ∈ D, b ≠ 1 → orderOf b = 3 := fun b hb hb1 =>
    orderOf_eq_prime (hD.2 b hb) hb1
  refine Sec4.Res423Three.alphaVanishes_of_rigid hZ hD1 ?_ ?_
  · intro b hb hb1
    exact (hA b (hb3 b hb hb1)).theta_eq_bot
  · intro b hb hb1 σ hσ hfix
    have hb3' := hb3 b hb hb1
    refine Proving.eq_one_of_fix_of_outer hZ hOut (centralizer ({b} : Set S)) ?_ ?_ σ hσ hfix
    · intro g hg
      have hbC : b ∈ centralizer ({b} : Set S) := mem_centralizer_singleton_iff.2 rfl
      have hgC : g ∈ centralizer ({b} : Set S) :=
        mem_centralizer_singleton_iff.2 (hg b hbC)
      refine ⟨2, ?_⟩
      have h9 := (hA b hb3').pow_nine_eq_one (g := (⟨g, hgC⟩ : ↥(centralizer ({b} : Set S))))
        (fun c => Subtype.ext (hg c c.2))
      exact congrArg Subtype.val h9
    · intro τ hτ2 hτ hall
      obtain ⟨t, ht1, ht2⟩ := hNO τ hτ2 hτ b hb3'
      exact ht2 (hall t (mem_centralizer_singleton_iff.2 ht1.symm))

section ON

set_option linter.unusedSectionVars false


theorem fourth_pow_inner_of_equiv_ON {S : Type} [Group S] (e : S ≃* CFSG.ONSchreier.Pv)
    (σ : MulAut S) : σ ^ (2 ^ 2) ∈ (MulAut.conj : S →* MulAut S).range := by
  set σ' : MulAut CFSG.ONSchreier.Pv := MulAut.congr e σ with hσ'
  have hcard := CFSG.EvenSporadicStandard.Solomon78.card_outer_Pv_dvd_four
  have h1 : (QuotientGroup.mk σ' :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer CFSG.ONSchreier.Pv) ^ 4 = 1 := by
    obtain ⟨m, hm⟩ := hcard
    rw [hm, pow_mul, pow_card_eq_one', one_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hy, hσ',
    map_pow]
  rfl

theorem alphaNine_ON : Coordinator.Cover423.AlphaNine (NativeSporadic.Carrier .ONan) := by
  have : Finite (NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.ON ≠ 0
      rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  have e : NativeSporadic.Carrier .ONan ≃* CFSG.ONSchreier.Pv := CFSG.ONSchreier.onEquivPv
  obtain ⟨φ, hφ, hker, hconj, hcard⟩ := on_cover_data
  refine alphaNine_of_data CFSG.EvenSporadicStandard.Solomon78.center_eq_bot_on
    (fun σ => ⟨2, fourth_pow_inner_of_equiv_ON e σ⟩)
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.NoOuterFixesCentralizer.of_mulEquiv e
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.noOuterFixesCentralizer_Pv)
    (fun b hb => ?_)
  obtain ⟨g, hg⟩ := hconj b hb
  obtain ⟨E, hE, ⟨eE⟩, hq⟩ := alt6_normal_of_cover φ hφ hker hcard
  exact Alt6Index9.centralizer_of_conj hg ⟨E, hE, ⟨eE⟩, hq⟩

end ON

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
