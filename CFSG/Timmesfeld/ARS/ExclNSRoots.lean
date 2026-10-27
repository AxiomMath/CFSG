module

public import CFSG.Timmesfeld.ARS.ExclNSStab
public import CFSG.Timmesfeld.ARS.CaseENatural
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.ExclNSClique
public import CFSG.Timmesfeld.ARS.ExclNSDefs
public import CFSG.Timmesfeld.ARS.ExclNSPolar
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.ARS.Sec5Ten
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity
open scoped commutatorElement

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem ht_weylAction_pos_of_neg {w₀ : W} (hw₀ : ∀ i, (cs).IsRightDescent w₀ i)
    {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (h : ht δ < 0) : 0 < ht (ρ w₀ δ) := by
  have h1 := ht_weylAction_neg hw₀ ((Φ).neg_mem _ hδ) (by rw [ht_neg]; omega)
  rw [map_neg, ht_neg] at h1
  omega

theorem exists_ne_pos_of_ht_pos (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hpos : 0 < ht γ) {k : Fin D.rank} (hne : γ ≠ Pi.single k 1) :
    ∃ i, i ≠ k ∧ 0 < γ i := by
  obtain ⟨i, hik, hi⟩ := exists_ne_lt_zero_of_ht_neg hdiv ((Φ).neg_mem _ hγ)
    (by rw [ht_neg]; omega) (fun e => hne (neg_inj.1 e))
  refine ⟨i, hik, ?_⟩
  rw [Pi.neg_apply] at hi
  omega

theorem ht_pos_reflection (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hpos : 0 < ht γ) {k : Fin D.rank} (hne : γ ≠ Pi.single k 1) :
    0 < ht (ρ ((cs).simple k) γ) := by
  obtain ⟨i, hik, hi⟩ := exists_ne_pos_of_ht_pos hdiv hγ hpos hne
  have hmem := weylAction_mem_roots D.isFiniteType ((cs).simple k) hγ
  refine ht_pos_of_nonneg hmem ?_
  rcases nonneg_or_nonpos D.isFiniteType D.divisible hmem with h | h
  · exact h
  · exfalso
    have h1 : ρ ((cs).simple k) γ i ≤ 0 := h i
    rw [weylAction_simple_apply_of_ne D.isFiniteType k γ hik] at h1
    omega

theorem ht_neg_reflection (hdiv : D.divisible = ∅) {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots)
    (hneg : ht δ < 0) {k : Fin D.rank} (hne : δ ≠ -Pi.single k 1) :
    ht (ρ ((cs).simple k) δ) < 0 ∧ ρ ((cs).simple k) δ ≠ -Pi.single k 1 := by
  obtain ⟨i, hik, hi⟩ := exists_ne_lt_zero_of_ht_neg hdiv hδ hneg hne
  have hmem := weylAction_mem_roots D.isFiniteType ((cs).simple k) hδ
  have hi' : ρ ((cs).simple k) δ i < 0 := by
    rw [weylAction_simple_apply_of_ne D.isFiniteType k δ hik]
    exact hi
  refine ⟨ht_neg_of_nonpos hmem ?_, fun e => ?_⟩
  · rcases nonneg_or_nonpos D.isFiniteType D.divisible hmem with h | h
    · exact absurd (h i) (not_le.2 hi')
    · exact h
  · rw [e, Pi.neg_apply, Pi.single_eq_of_ne hik] at hi'
    omega

theorem eq_neg_single_of_le {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (hβ0 : β ≤ 0)
    {k : Fin D.rank} (h : -Pi.single k 1 ≤ β) : β = -Pi.single k 1 := by
  have hne := ne_zero_of_mem_roots D.isFiniteType D.divisible hβ
  have hj : ∀ j, j ≠ k → β j = 0 := fun j hj => by
    have h1 : 0 ≤ β j := by simpa [Pi.single_eq_of_ne hj] using h j
    exact le_antisymm (hβ0 j) h1
  have hk : β k = -1 := by
    have h1 : -1 ≤ β k := by simpa using h k
    have h2 : β k ≤ 0 := hβ0 k
    by_contra hk'
    refine hne (funext fun j => ?_)
    by_cases hjk : j = k
    · subst hjk
      show β j = 0
      omega
    · rw [hj j hjk, Pi.zero_apply]
  funext j
  by_cases hjk : j = k
  · subst hjk
    rw [hk, Pi.neg_apply, Pi.single_eq_same]
  · rw [hj j hjk, Pi.neg_apply, Pi.single_eq_of_ne hjk, neg_zero]

theorem ht_pos_or_neg {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    (0 ≤ γ ∧ 0 < ht γ) ∨ (γ ≤ 0 ∧ ht γ < 0) := by
  rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ with h | h
  · exact Or.inl ⟨h, ht_pos_of_nonneg hγ h⟩
  · exact Or.inr ⟨h, ht_neg_of_nonpos hγ h⟩

theorem linIndepPair_of_ht_neg (hdiv : D.divisible = ∅) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hγ0 : ht γ < 0) (hδ : δ ∈ D.roots) (hδ0 : ht δ < 0) (hne : γ ≠ δ) :
    LinIndepPair γ δ :=
  (Φ).linIndepPair_of_mem_neg ⟨hγ, hγ0⟩ (isIndiv_of_divisible_eq_empty hdiv hγ) ⟨hδ, hδ0⟩
    (isIndiv_of_divisible_eq_empty hdiv hδ) hne

theorem linIndepPair_neg_right {α β : Fin D.rank → ℤ} (h : LinIndepPair α β) :
    LinIndepPair α (-β) := fun a b hab => by
  have := h a (-b) (by rw [neg_smul, ← smul_neg]; exact hab)
  exact ⟨this.1, neg_eq_zero.1 this.2⟩

variable (hct : IsCTGroupDatum (cs) ρ D.roots D.rootGroup n H)

include hct in
theorem nrep_conj_mem_posUnipotent {w₀ : W} (hw₀ : ∀ i, (cs).IsRightDescent w₀ i) {u : K}
    (hu : u ∈ negUnipotent D) : nrep hct w₀ * u * (nrep hct w₀)⁻¹ ∈ posUnipotent D :=
  conj_mem_of_forall_mem (fun _ hγ _ hy => rootGroup_le_posUnipotent
    (weylAction_mem_roots _ w₀ hγ.1) (ht_weylAction_pos_of_neg hw₀ hγ.1 hγ.2)
    ((actsAs_nrep hct w₀).conj_mem hγ.1 hy)) hu

include hct in
theorem eq_one_of_mem_negUnipotent_of_mem_center (hext : SteinbergExtras D n H) {z : K}
    (hz : z ∈ negUnipotent D) (hzc : z ∈ Subgroup.center K) : z = 1 := by
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have h1 := nrep_conj_mem_posUnipotent hct hw₀ hz
  rw [Subgroup.mem_center_iff.1 hzc (nrep hct w₀), mul_inv_cancel_right] at h1
  have h2 : z ∈ posUnipotent D ⊓ negUnipotent D := ⟨h1, hz⟩
  rw [posUnipotent_inf_negUnipotent hext] at h2
  exact h2

include hct in
theorem eq_of_rootGroup_eq (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (h : D.rootGroup γ = D.rootGroup δ) : γ = δ := by
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single hdiv hγ
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (Φ).single_mem i
  have hδ'R : ρ w⁻¹ δ ∈ D.roots := weylAction_mem_roots _ _ hδ
  have key : D.rootGroup (Pi.single i 1) = D.rootGroup (ρ w⁻¹ δ) := by
    have h1 := (actsAs_nrep hct w).inv _ (weylAction_mem_roots _ w hα)
    have h2 := (actsAs_nrep hct w).inv _ hδ
    rw [weylAction_inv_apply_apply] at h1
    rw [← h1, h, h2]
  suffices hδ' : ρ w⁻¹ δ = Pi.single i 1 by
    rw [← hδ', weylAction_apply_inv_apply]
  by_contra hne
  rcases ht_pos_or_neg hδ'R with ⟨-, hpos⟩ | ⟨-, hneg⟩
  · have hneg' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (Φ).neg_mem _ hα
    have h3 := actsAs_n hct i _ hα
    have h4 := actsAs_n hct i _ hδ'R
    rw [weylAction_simple_single] at h3
    have key2 : D.rootGroup (-Pi.single i 1) =
        D.rootGroup (ρ ((cs).simple i) (ρ w⁻¹ δ)) := by
      rw [← h3, key, h4]
    apply hext.ne_bot _ hneg'
    rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
    refine le_inf ?_ (rootGroup_le_negUnipotent hneg' (by rw [ht_neg, ht_single]; omega))
    rw [key2]
    exact rootGroup_le_posUnipotent (weylAction_mem_roots _ _ hδ'R)
      (ht_pos_reflection hdiv hδ'R hpos hne)
  · apply hext.ne_bot _ hα
    rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
    exact le_inf (rootGroup_le_posUnipotent hα (ht_single_pos i))
      (key ▸ rootGroup_le_negUnipotent hδ'R hneg)

include hct in
theorem eq_top_of_negUnipotent_le {P : Subgroup K} (hU : negUnipotent D ≤ P)
    (hn : ∀ s, n s ∈ P) : P = ⊤ := by
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have hnrep : nrep hct w₀ ∈ P := by
    obtain ⟨ω, hω, e⟩ := (cs).exists_isReduced w₀
    rw [e, nrep_wordProd hct hω]
    refine P.list_prod_mem fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hn i
  rw [eq_top_iff, ← hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  rcases ht_pos_or_neg hγ with ⟨-, hpos⟩ | ⟨-, hneg⟩
  · have hδ : ρ w₀⁻¹ γ ∈ D.roots := weylAction_mem_roots _ _ hγ
    have hδneg : ht (ρ w₀⁻¹ γ) < 0 := by
      rcases ht_pos_or_neg hδ with ⟨-, h⟩ | ⟨-, h⟩
      · have h' := ht_weylAction_neg hw₀ hδ h
        rw [weylAction_apply_inv_apply] at h'
        omega
      · exact h
    have e := actsAs_nrep hct w₀ _ hδ
    rw [weylAction_apply_inv_apply] at e
    rw [← e]
    rintro _ ⟨y, hy, rfl⟩
    exact P.mul_mem (P.mul_mem hnrep (hU (rootGroup_le_negUnipotent hδ hδneg hy)))
      (P.inv_mem hnrep)
  · exact (rootGroup_le_negUnipotent hγ hneg).trans hU

omit hct in
theorem isPGroup_negUnipotent (hext : SteinbergExtras D n H) {p : ℕ}
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) : IsPGroup p (negUnipotent D) := by
  have h := isPGroup_iSup_posSet hext hX (-htHom)
  have e : posSet D.roots (-htHom) = {γ | γ ∈ D.roots ∧ ht γ < 0} := by
    ext γ
    refine and_congr_right fun _ => ?_
    rw [AddMonoidHom.neg_apply, htHom_apply, Left.neg_pos_iff]
  rw [e] at h
  exact h

omit hct in
theorem commuting_of_forall_notMem_openCone (hext : SteinbergExtras D n H)
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hind : LinIndepPair γ δ)
    (h : ∀ ε ∈ D.roots, ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ε = a • γ + b • δ) :
    Commuting (D.rootGroup γ) (D.rootGroup δ) := by
  intro x hx y hy
  have h1 := hext.commutator_mem γ hγ δ hδ hind x hx y hy
  have hbot : (⨆ ε ∈ openCone D.roots γ δ, D.rootGroup ε) = ⊥ :=
    le_bot_iff.1 (iSup₂_le fun ε hε => absurd hε.2 (h ε hε.1))
  rw [hbot, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_commute.1 h1

@[expose] def lowerRoots (D : UniversalRootDatum K) (S : Set (Fin D.rank → ℤ)) :
    Set (Fin D.rank → ℤ) :=
  {δ | δ ∈ D.roots ∧ ∃ β ∈ S, δ ≤ β}

omit hct in
theorem negUnipotent_le_normalizer_lower (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    {S : Set (Fin D.rank → ℤ)} (hS0 : ∀ β ∈ S, β ≤ 0) :
    negUnipotent D ≤
      Subgroup.normalizer ((⨆ δ ∈ lowerRoots D S, D.rootGroup δ : Subgroup K) : Set K) := by
  refine iSup₂_le fun ε hε => le_normalizer_iSup₂ fun x hx δ hδ y hy => ?_
  rw [conj_eq_commutator_mul]
  refine Subgroup.mul_mem _ ?_ (le_iSup₂_of_le (f := fun δ (_ : δ ∈ lowerRoots D S) =>
    D.rootGroup δ) δ hδ le_rfl hy)
  obtain ⟨β, hβS, hδβ⟩ := hδ.2
  have hδ0 : δ ≤ 0 := hδβ.trans (hS0 β hβS)
  by_cases he : ε = δ
  · subst he
    refine le_iSup₂_of_le (f := fun δ (_ : δ ∈ lowerRoots D S) => D.rootGroup δ) ε hδ le_rfl ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · have hind : LinIndepPair ε δ := linIndepPair_of_ht_neg hdiv hε.1 hε.2 hδ.1
      (ht_neg_of_nonpos hδ.1 hδ0) he
    refine (iSup₂_le (f := fun ζ (_ : ζ ∈ openCone D.roots ε δ) => D.rootGroup ζ)
      fun ζ hζ => ?_ : _ ≤ ⨆ δ ∈ lowerRoots D S, D.rootGroup δ)
      (hext.commutator_mem ε hε.1 δ hδ.1 hind x hx y hy)
    refine le_iSup₂_of_le (f := fun δ (_ : δ ∈ lowerRoots D S) => D.rootGroup δ) ζ
      ⟨hζ.1, β, hβS, ?_⟩ le_rfl
    obtain ⟨-, a, b, ha, hb, rfl⟩ := hζ
    have hε0 : ε ≤ 0 := by
      rcases ht_pos_or_neg hε.1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd hε.2 (not_lt.2 h.le)
      · exact h
    intro j
    have h1 : ε j ≤ 0 := hε0 j
    have h2 : δ j ≤ 0 := hδ0 j
    have h3 : δ j ≤ β j := hδβ j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith

omit hct in
theorem negUnipotent_le_normalizer_rootGroup {γ : Fin D.rank → ℤ}
    (h : ∀ δ ∈ D.roots, ht δ < 0 → δ ≠ γ → Commuting (D.rootGroup γ) (D.rootGroup δ)) :
    negUnipotent D ≤ Subgroup.normalizer (D.rootGroup γ : Set K) := by
  refine iSup₂_le fun δ hδ => ?_
  by_cases he : δ = γ
  · subst he
    exact Subgroup.le_normalizer
  · exact le_normalizer_of_commuting' (h δ hδ.1 hδ.2 he)

omit hct in
theorem negUnipotent_le_normalizer_of_forall_ht_le (hext : SteinbergExtras D n H)
    (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hmin : ∀ ε ∈ D.roots, ht γ ≤ ht ε) :
    negUnipotent D ≤ Subgroup.normalizer (D.rootGroup γ : Set K) := by
  have hγ0 : ht γ < 0 := by
    have h1 := hmin _ ((Φ).neg_mem _ hγ)
    rw [ht_neg] at h1
    rcases ht_pos_or_neg hγ with ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · exact h
  refine negUnipotent_le_normalizer_rootGroup fun δ hδ hδ0 hne => ?_
  refine commuting_of_forall_notMem_openCone hext hγ hδ
    (linIndepPair_of_ht_neg hdiv hγ hγ0 hδ hδ0 (Ne.symm hne)) ?_
  rintro ε hε ⟨a, b, ha, hb, rfl⟩
  have h1 := hmin _ hε
  rw [ht_add, ht_nsmul, ht_nsmul] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

include hct in
theorem false_of_commuting (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅)
    {β β' : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (hβ' : β' ∈ D.roots)
    (hc : Commuting (D.rootGroup β) (D.rootGroup β')) (hind : LinIndepPair β' (-β))
    (hcone : ∀ ε ∈ D.roots, ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ε = a • β' + b • (-β))
    {w : W} {i : Fin D.rank} (hw : ρ w (Pi.single i 1) = β)
    (hne : ρ ((cs).simple i) (ρ w⁻¹ β') ≠ ρ w⁻¹ β') : False := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (Φ).single_mem i
  have hc' : Commuting (D.rootGroup β') (D.rootGroup (-β)) :=
    commuting_of_forall_notMem_openCone hext hβ' ((Φ).neg_mem _ hβ) hind hcone
  set m := nrep hct w * n i * (nrep hct w)⁻¹ with hm
  have hmem : m ∈ D.rootGroup β ⊔ D.rootGroup (-β) := by
    have e1 := actsAs_nrep hct w _ hα
    have e2 := actsAs_nrep hct w _ ((Φ).neg_mem _ hα)
    rw [hw] at e1
    rw [map_neg, hw] at e2
    have e : (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).map
        (MulAut.conj (nrep hct w)).toMonoidHom = D.rootGroup β ⊔ D.rootGroup (-β) := by
      rw [Subgroup.map_sup, e1, e2]
    rw [← e]
    exact ⟨n i, hct.n_mem i, rfl⟩
  have hmc : ∀ y ∈ D.rootGroup β', Commute m y := fun y hy =>
    ((hc.symm.sup_right hc') y hy m hmem).symm
  have hact : ActsAs D m (w * (cs).simple i * w⁻¹) :=
    ((actsAs_nrep hct w).mul (actsAs_n hct i)).mul (actsAs_nrep hct w).inv
  have e : conjSub (D.rootGroup β') m = D.rootGroup (ρ (w * (cs).simple i * w⁻¹) β') :=
    hact β' hβ'
  rw [conjSub_of_forall_commute hmc] at e
  have h1 := eq_of_rootGroup_eq hct hext hdiv hβ' (weylAction_mem_roots _ _ hβ') e
  apply hne
  rw [weylAction_mul_apply, weylAction_mul_apply] at h1
  calc ρ ((cs).simple i) (ρ w⁻¹ β') =
        ρ w⁻¹ (ρ w (ρ ((cs).simple i) (ρ w⁻¹ β'))) := by rw [weylAction_inv_apply_apply]
    _ = ρ w⁻¹ β' := by rw [← h1]

end CFSG.Timmesfeld.ARS.ExclNS
