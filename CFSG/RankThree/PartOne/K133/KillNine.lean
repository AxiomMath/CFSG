module

public import CFSG.RankThree.PartOne.K133.KillBasic
import CFSG.RankThree.PartOne.CTP.SeitzLinearOuter
import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.K133.Quot
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlane
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
import CFSG.RankThree.PartOne.KC.UnitaryNonsplitNoninnerPlane
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.Census3 TauCeti

theorem not_pow_three_dvd_of_primeFactors {N : ℕ} (hN : N ≠ 0) (S : Finset ℕ)
    (hS : N.primeFactors = S) (h3 : ∀ p ∈ S, 5 ≤ p → ¬ p ^ 3 ∣ N) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : ¬ p ^ 3 ∣ N := by
  intro h
  have hpN : p ∣ N := (dvd_pow_self p (by norm_num)).trans h
  have : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpN, hN⟩
  rw [hS] at this
  exact h3 p this h5 h

theorem inner_of_mem_rankThree {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hplanes : ∀ E : Subgroup (MulAut X), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      ∀ φ ∈ E, ∃ g : X, φ = MulAut.conj g)
    {Ē : Subgroup (MulAut X)} (hEl : IsElementaryAbelian p Ē) (hcard : Nat.card Ē = p ^ 3)
    {φ : MulAut X} (hφ : φ ∈ Ē) : ∃ g : X, φ = MulAut.conj g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hφ1 : φ = 1
  · exact ⟨1, by rw [hφ1, map_one]⟩
  have hcomm : ∀ a ∈ Ē, ∀ b ∈ Ē, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEl.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hpow : ∀ a ∈ Ē, a ^ p = 1 := fun a ha => by
    have := hEl
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := Ē) a ha
  have hφord : orderOf φ = p := orderOf_eq_prime (hpow φ hφ) hφ1
  obtain ⟨ψ, hψ, hψφ⟩ : ∃ ψ ∈ Ē, ψ ∉ Subgroup.zpowers φ := by
    by_contra hcon
    push Not at hcon
    have hle : Ē ≤ Subgroup.zpowers φ := hcon
    have : Finite (Subgroup.zpowers φ) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hφord]; exact hp.ne_zero)
    have h1 : Nat.card Ē ≤ Nat.card (Subgroup.zpowers φ) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [Nat.card_zpowers, hφord, hcard] at h1
    have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  have hψ1 : ψ ≠ 1 := fun h1 => hψφ (h1 ▸ Subgroup.one_mem _)
  have hψord : orderOf ψ = p := orderOf_eq_prime (hpow ψ hψ) hψ1
  have hE'le : Subgroup.zpowers φ ⊔ Subgroup.zpowers ψ ≤ Ē := sup_le
    (Subgroup.zpowers_le.2 hφ) (Subgroup.zpowers_le.2 hψ)
  have hE'card : Nat.card ↥(Subgroup.zpowers φ ⊔ Subgroup.zpowers ψ) = p ^ 2 := by
    rw [card_sup_zpowers (Y := Subgroup.zpowers φ) hp hψord
      (fun y hy => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ((Commute.zpow_left (show Commute φ ψ from hcomm φ hφ ψ hψ) n)).eq) hψφ,
      Nat.card_zpowers, hφord]
    ring
  have hE'el : IsElementaryAbelian p ↥(Subgroup.zpowers φ ⊔ Subgroup.zpowers ψ) :=
    isElementaryAbelian_of_le hEl hE'le
  exact hplanes _ hE'el hE'card φ (Subgroup.mem_sup_left (Subgroup.mem_zpowers φ))

theorem noRankThree_of_planes_inner {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hplanes : ∀ E : Subgroup (MulAut X), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      ∀ φ ∈ E, ∃ g : X, φ = MulAut.conj g)
    (hX : ¬ p ^ 3 ∣ Nat.card X) : NoRankThree p X := by
  rintro ⟨Ē, hEl, hcard⟩
  have hle : Ē ≤ inner X := fun φ hφ => by
    obtain ⟨g, hg⟩ := inner_of_mem_rankThree hp hplanes hEl hcard hφ
    exact ⟨g, hg.symm⟩
  have h1 : Nat.card Ē ∣ Nat.card (inner X) := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card (inner X) ∣ Nat.card X := Subgroup.card_range_dvd _
  exact hX (hcard ▸ h1.trans h2)

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCLinComm
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.RankThree.PartOne.CTP

theorem inner_of_mem_linear_two {m : ℕ} (hm : 2 ≤ m) {q : PrimePower} (hqp : q.p = 2)
    (hqe : q.exponent = 1) {X : Type} [Group X] (hX : IsoLie X (.A m q)) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) {E : Subgroup (MulAut X)} (hE : IsElementaryAbelian p E) {φ : MulAut X}
    (hφ : φ ∈ E) : ∃ g : X, φ = MulAut.conj g := by
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  by_contra hout
  push Not at hout
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hn : 3 ≤ m + 1 := by omega
  let e : X ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hφp : φ ^ p = 1 := by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) φ hφ
  have hφ'p : MulAut.congr e φ ^ p = 1 := by rw [← map_pow, hφp, map_one]
  have hφ'out : MulAut.congr e φ ∉ innSL (m + 1) (GaloisField q.p q.exponent) := by
    rintro ⟨g, hg⟩
    exact hout (e.symm g) (eq_conj_of_congr_eq_conj e hg.symm)
  have hF : Nat.card (GaloisField q.p q.exponent) = 2 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hqp, hqe]
    norm_num
  have hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card (GaloisField q.p q.exponent) - 1)) := by
    rw [hF]
    simp
  have hdvd := p_dvd_card_fieldAut_of_outer hn hp (by omega) hcop hφ'p hφ'out
  have hcardAut : Nat.card (GaloisField q.p q.exponent ≃+* GaloisField q.p q.exponent) =
      q.exponent := by
    obtain ⟨-, -, -, -, hcardAut, -⟩ := finite_field_automorphism_fixed_field_cardinality
      q.prime_p q.exponent_pos (GaloisField.card q.p q.exponent q.exponent_pos.ne')
    exact hcardAut
  rw [hcardAut, hqe] at hdvd
  have := Nat.le_of_dvd one_pos hdvd
  omega

theorem noRankThree_linear_two {m : ℕ} (hm4 : 4 ≤ m) (hm6 : m ≤ 6) {q : PrimePower}
    (hqp : q.p = 2) (hqe : q.exponent = 1) {X : Type} [Group X] [Finite X]
    (hX : IsoLie X (.A m q)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : NoRankThree p X := by
  refine noRankThree_of_planes_inner hp
    (fun E hE _ φ hφ => inner_of_mem_linear_two (by omega) hqp hqe hX hp h5 hE hφ) ?_
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
  rw [hqp, hqe] at hmod
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).1 rfl
  rw [hcard]
  interval_cases m
  · exact not_pow_three_dvd_of_primeFactors (by decide) {2, 3, 5, 7, 31} (by decide +kernel)
      (by decide) hp h5
  · exact not_pow_three_dvd_of_primeFactors (by decide) {2, 3, 5, 7, 31} (by decide +kernel)
      (by decide) hp h5
  · exact not_pow_three_dvd_of_primeFactors (by decide) {2, 3, 5, 7, 31, 127} (by decide +kernel)
      (by decide) hp h5

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

theorem inner_of_mem_plane_unitary_five {q : PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {X : Type} [Group X] (hX : IsoLie X (.twistedA 5 q)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {E : Subgroup (MulAut X)} (hE : IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 2)
    {φ : MulAut X} (hφ : φ ∈ E) : ∃ g : X, φ = MulAut.conj g := by
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  by_contra hout
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e0)
  let ψ : MulAut X ≃* MulAut (primeFormP hU (idGram F (5 + 1))) := MulAut.congr θ
  have hψconj : ∀ g : X, ψ (MulAut.conj g) = MulAut.conj (θ g) := by
    intro g
    refine MulEquiv.ext fun x => ?_
    simp [ψ, MulAut.congr_apply, MulAut.conj_apply]
  let A : Subgroup (MulAut (primeFormP hU (idGram F (5 + 1)))) := E.map ψ.toMonoidHom
  have hAel : IsElementaryAbelian p A := CFSG.IsElementaryAbelian.map _
  have hAcard : Nat.card A = p ^ 2 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hcard]
  have hAnot : ¬ A ≤ innU hU (5 + 1) := by
    intro hle
    obtain ⟨t, ht⟩ := hle ⟨φ, hφ, rfl⟩
    refine hout ⟨θ.symm t, ψ.injective ?_⟩
    rw [hψconj, MulEquiv.apply_symm_apply]
    exact ht.symm
  have hpℓ : p ≠ q.p := by rw [hqp]; omega
  have hpq : ¬ p ∣ q.p ^ q.exponent + 1 := by
    rw [hqp, hqe]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have h2 := nonsplit_unitary_noninner_plane_local_core_product_odd q.p q.exponent (5 + 1) p F hU
    hp (by omega) hpℓ hpq hn3 hne ⊤ le_top A le_top hAel hAcard hAnot
  have h3 := Nat.le_of_dvd hf h2.2.1
  omega

theorem noRankThree_unitary_five {q : PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {X : Type} [Group X] [Finite X] (hX : IsoLie X (.twistedA 5 q)) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : NoRankThree p X := by
  refine noRankThree_of_planes_inner hp
    (fun E hE hc φ hφ => inner_of_mem_plane_unitary_five hqp hqe hX hp h5 hE hc hφ) ?_
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e0
  rw [hqp, hqe] at hmod
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  rw [hcard]
  exact not_pow_three_dvd_of_primeFactors (by decide) {2, 3, 5, 7, 11} (by decide +kernel)
    (by decide) hp h5

end Unitary

section Symplectic

open CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCSpComm

theorem noRankThree_symplectic_four {q : PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {X : Type} [Group X] [Finite X] (hX : IsoLie X (.B 4 q)) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : NoRankThree p X := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine noRankThree_of_planes_inner hp ?_ ?_
  · intro E hE _ φ hφ
    obtain ⟨hv, ⟨e0⟩⟩ := hX
    have hF := card_fixedField_B 4 q hv
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 4 q, hv⟩) :=
      Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ q.prime_p.ne_zero)
    exact outer_vacuous_of_psp_model q.prime_p q.exponent_pos (by omega) hF hp h5 (by omega)
      (e0.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 4 q hv hqp
        (by omega))) E φ hφ
  · obtain ⟨hv, ⟨e0⟩⟩ := hX
    have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hqp
      (by omega) e0
    rw [hqp, hqe] at hmod
    have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.1 rfl
    rw [hcard]
    exact not_pow_three_dvd_of_primeFactors (by decide) {2, 3, 5, 7, 17} (by decide +kernel)
      (by decide) hp h5

end Symplectic

section Orthogonal

open CFSG.RankThree.PartOne.CTP

theorem inner_of_mem_plane_orthogonal_four {q : PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {X : Type} [Group X] [Finite X] (hX : IsoLie X (.D 4 q)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {E : Subgroup (MulAut X)} (hE : IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 2)
    {φ : MulAut X} (hφ : φ ∈ E) : ∃ g : X, φ = MulAut.conj g := by
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  by_contra hout
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hqp e0
  have hpq : p ≠ q.p := by rw [hqp]; omega
  obtain ⟨-, hpf, -⟩ := orthogonal_noninner_plane_local_core_product_odd_of_subfield
      orthogonal_prime_subfield_core_clause_unconditional X
    .POmegaPlus q.p q.exponent 4 p (Or.inr (Or.inl rfl)) hmodel hp (by omega) hpq ⊤ le_top E
    le_top hE hcard fun hle => hout (by
      obtain ⟨g, hg⟩ := hle hφ
      exact ⟨g, hg.symm⟩)
  have := Nat.le_of_dvd q.exponent_pos hpf
  omega

theorem noRankThree_orthogonal_four {q : PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {X : Type} [Group X] [Finite X] (hX : IsoLie X (.D 4 q)) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : NoRankThree p X := by
  refine noRankThree_of_planes_inner hp
    (fun E hE hc φ hφ => inner_of_mem_plane_orthogonal_four hqp hqe hX hp h5 hE hc hφ) ?_
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hqp e0
  rw [hqp, hqe] at hmod
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.2.1 rfl
  rw [hcard]
  exact not_pow_three_dvd_of_primeFactors (by decide) {2, 3, 5, 7} (by decide +kernel)
    (by decide) hp h5

end Orthogonal

section Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem inner_of_mem_F4_two {q : PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {X : Type} [Group X] (hX : IsoLie X (.F4 q)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {E : Subgroup (MulAut X)} (hE : IsElementaryAbelian p E) {φ : MulAut X} (hφ : φ ∈ E) :
    ∃ g : X, φ = MulAut.conj g := by
  by_contra hout
  have : Fact p.Prime := ⟨hp⟩
  have hout' : ¬ ∀ φ ∈ E, ∃ g : X, φ = MulAut.conj g := fun h => hout (h φ hφ)
  have hdvd := dvd_card_outer_of_not_inner (p := p) E hout'
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hqp e0
  obtain ⟨Y, _, _, hY, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hmodel
  rw [hqp, hqe] at hY
  have hY' : Nat.card Y = 2 ^ 1 := by simpa using hY
  have : CharP Y 2 := finite_field_prime_power_characteristic Nat.prime_two (le_refl 1) hY'
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form (le_refl 1) Y hY'
  have h1 : Nat.card (Outer X) = Nat.card (Outer (adjointGroup ReeTag.F4.tag Y)) :=
    Nat.card_congr (equivalence e).toEquiv
  rw [h1, card_outer_eq_of_hom Θ hsurj hker] at hdvd
  have hc : Nat.card (Multiplicative (ZMod (2 * 1))) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  rw [hc] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem noRankThree_F4_two {q : PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {X : Type} [Group X] [Finite X] (hX : IsoLie X (.F4 q)) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) : NoRankThree p X := by
  refine noRankThree_of_planes_inner hp
    (fun E hE _ φ hφ => inner_of_mem_F4_two hqp hqe hX hp h5 hE hφ) ?_
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hqp e0
  rw [hqp, hqe] at hmodel
  have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hmodel
  rw [hcard]
  exact not_pow_three_dvd_of_primeFactors (by decide) {2, 3, 5, 7, 13, 17} (by decide +kernel)
    (by decide) hp h5

theorem kf133ResMaxAt_leaf9 : ∀ i, KF133ResMaxAt (leaf9 i) := by
  intro i
  refine KF133ResMaxAt.of_noRankThree fun X _ _ hX p hp h5 => ?_
  fin_cases i
  · obtain ⟨q, hqp, hqe, hX⟩ := hX
    exact noRankThree_linear_two (by norm_num) (by norm_num) hqp hqe hX hp h5
  · obtain ⟨q, hqp, hqe, hX⟩ := hX
    exact noRankThree_linear_two (by norm_num) (by norm_num) hqp hqe hX hp h5
  · obtain ⟨q, hqp, hqe, hX⟩ := hX
    exact noRankThree_linear_two (by norm_num) (by norm_num) hqp hqe hX hp h5
  · obtain ⟨q, hqp, hqe, hX⟩ := hX
    exact noRankThree_unitary_five hqp hqe hX hp h5
  · obtain ⟨q, hqp, hqe, hX⟩ := hX
    exact noRankThree_symplectic_four hqp hqe hX hp h5
  · obtain ⟨q, hqp, hqe, hX⟩ := hX
    exact noRankThree_orthogonal_four hqp hqe hX hp h5
  · obtain ⟨q, hqp, hqe, hX⟩ := hX
    exact noRankThree_F4_two hqp hqe hX hp h5

end Exceptional

end CFSG.RankThree.PartOne.K133
