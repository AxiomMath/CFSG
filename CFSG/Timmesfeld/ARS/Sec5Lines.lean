module

public import CFSG.Timmesfeld.ARS.QDClass
public import CFSG.Timmesfeld.ARS.Sec4WeakTI

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem commutatorElement_mul_right_eq_of_commute {a x c : G} (h : Commute a c) :
    ⁅a, x * c⁆ = ⁅a, x⁆ := by
  have h1 : c * a⁻¹ * c⁻¹ = a⁻¹ := by rw [← h.inv_left.eq, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (x * c) * a⁻¹ * (x * c)⁻¹ = a * x * (c * a⁻¹ * c⁻¹) * x⁻¹ := by group
    _ = a * x * a⁻¹ * x⁻¹ := by rw [h1]

theorem commutatorElement_mul_left_eq_of_commute {a x c : G} (h : Commute a c) :
    ⁅x * a, c⁆ = ⁅x, c⁆ := by
  have h1 : a * c * a⁻¹ = c := by rw [h.eq, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc x * a * c * (x * a)⁻¹ * c⁻¹ = x * (a * c * a⁻¹) * x⁻¹ * c⁻¹ := by group
    _ = x * c * x⁻¹ * c⁻¹ := by rw [h1]

theorem conjSub_conjSub_of_mul_self {H : Subgroup G} {g : G} (hg : g * g = 1) :
    conjSub (conjSub H g) g = H := by
  rw [← conjSub_mul, hg, conjSub_one]

section Comm

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

theorem commutator_conjSub_right_eq {A C E : Subgroup G} (hE : E ∈ R) (hC : C ∈ R)
    (hEC : Special R E C) {e : G} (he : e ∈ E) (he1 : e ≠ 1) (hAC : Commuting A C) :
    ⁅A, conjSub C e⁆ = ⁅A, ⁅E, C⁆⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro a ha _ ⟨c, hc, rfl⟩
    change ⁅a, e * c * e⁻¹⁆ ∈ _
    rw [conj_eq_commutator_mul, commutatorElement_mul_right_eq_of_commute (hAC a ha c hc)]
    exact Subgroup.commutator_mem_commutator ha (Subgroup.commutator_mem_commutator he hc)
  · rw [Subgroup.commutator_le]
    intro a ha f hf
    obtain ⟨c, hc, rfl⟩ := (bijOn_commutator hR hiso hE hC hEC he he1).surjOn hf
    have h1 : ⁅a, ⁅e, c⁆⁆ = ⁅a, e * c * e⁻¹⁆ := by
      rw [conj_eq_commutator_mul, commutatorElement_mul_right_eq_of_commute (hAC a ha c hc)]
    change ⁅a, ⁅e, c⁆⁆ ∈ _
    rw [h1]
    exact Subgroup.commutator_mem_commutator ha (conj_mem_conjSub e hc)

theorem commutator_conjSub_left_eq {A C E : Subgroup G} (hE : E ∈ R) (hA : A ∈ R)
    (hEA : Special R E A) {e : G} (he : e ∈ E) (he1 : e ≠ 1) (hAC : Commuting A C) :
    ⁅conjSub A e, C⁆ = ⁅⁅E, A⁆, C⁆ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro _ ⟨a, ha, rfl⟩ c hc
    change ⁅e * a * e⁻¹, c⁆ ∈ _
    rw [conj_eq_commutator_mul, commutatorElement_mul_left_eq_of_commute (hAC a ha c hc)]
    exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator he ha) hc
  · rw [Subgroup.commutator_le]
    intro f hf c hc
    obtain ⟨a, ha, rfl⟩ := (bijOn_commutator hR hiso hE hA hEA he he1).surjOn hf
    have h1 : ⁅⁅e, a⁆, c⁆ = ⁅e * a * e⁻¹, c⁆ := by
      rw [conj_eq_commutator_mul, commutatorElement_mul_left_eq_of_commute (hAC a ha c hc)]
    change ⁅⁅e, a⁆, c⁆ ∈ _
    rw [h1]
    exact Subgroup.commutator_mem_commutator (conj_mem_conjSub e ha) hc

end Comm

section Stab

variable (hR : IsRootClass R) {Δ : Set (Subgroup G)}
include hR

theorem conjSub_mem_of_commuting (hΔ : IsWeakTI R Δ) {U E F : Subgroup G} (hU : U ∈ R)
    (hE : E ∈ Δ) (hUE : Commuting U E) {u : G} (hu : u ∈ U) (hF : F ∈ Δ) : conjSub F u ∈ Δ :=
  hΔ.conjSub_mem hR hU hu hE (conjSub_of_forall_commute fun x hx => hUE u hu x hx) hF

theorem le_stabSet_of_commuting (hΔ : IsWeakTI R Δ) {U E : Subgroup G} (hU : U ∈ R)
    (hE : E ∈ Δ) (hUE : Commuting U E) : U ≤ stabSet Δ := fun u hu =>
  mem_stabSet_of_mul_self (hR.mul_self U hU u hu) fun _ hF =>
    conjSub_mem_of_commuting hR hΔ hU hE hUE hu hF

end Stab

section Lines

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {Δ : Set (Subgroup G)}
include hR hiso

theorem mem_of_le_sup (hΔ : IsWeakTI R Δ) {P Q T : Subgroup G} (hP : P ∈ Δ) (hQ : Q ∈ Δ)
    (hQP : Q ∈ lambdaSet R P) (hT : T ∈ R) (hTle : T ≤ P ⊔ Q) : T ∈ Δ := by
  by_cases hTP : T = P
  · exact hTP ▸ hP
  obtain ⟨U, hU, u, hu, hQu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso (hΔ.1 hP) hQP
    (hΔ.1 hQ) le_sup_right hQP.1.2.1 hT hTle hTP
  rw [← hQu]
  exact conjSub_mem_of_commuting hR hΔ hU.1.1 hP hU.1.2.2.symm hu hQ

theorem commutator_mem (hΔ : IsWeakTI R Δ) {P F E : Subgroup G} (hP : P ∈ Δ) (hF : F ∈ R)
    (hE : E ∈ Δ) (hFE : Commuting F E) (hPF : Special R P F) : ⁅P, F⁆ ∈ Δ := by
  have hPR := hΔ.1 hP
  obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hF
  have hPf : conjSub P f ∈ Δ := conjSub_mem_of_commuting hR hΔ hF hE hFE hf hP
  have hLΛ : ⁅P, F⁆ ∈ lambdaSet R P :=
    mem_lambdaSet_comm hPF.1 (mem_lambdaSet_commutator hR hiso hPR hF hPF).1
  have hne : conjSub P f ≠ P := Sec3.conjSub_ne_of_special hR hiso hF hPR hPF.symm hf hf1
  have hle : conjSub P f ≤ P ⊔ ⁅P, F⁆ := (conjSub_le_commutator_sup hf).trans (sup_comm _ _).le
  obtain ⟨hPfl, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hPR hLΛ hPR le_sup_left
    (hR.conjSub_mem hPR f) hle hne.symm
  exact mem_of_le_sup hR hiso hΔ hP hPf hPfl hPF.1 (hsup ▸ le_sup_right)

theorem exists_opposite_special {Y P S : Subgroup G} (hY : Y ∈ R) (hP : P ∈ lambdaSet R Y)
    (hS : S ∈ R) (hSle : S ≤ Y ⊔ P) (hSY : S ≠ Y) :
    ∃ F ∈ R, Opposite Y F ∧ Special R F S := by
  obtain ⟨D₀, hD₀, hYD₀⟩ := hiso Y hY
  obtain ⟨S₀, ⟨hS₀R, hS₀le, hS₀ψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hY hD₀ hYD₀ hP
  have hS₀Y : S₀ ≠ Y := by
    rintro rfl
    exact Special.not_opposite hR hD₀ hS₀ψ.2 hYD₀.symm
  obtain ⟨U, hU, u, hu, hS₀u⟩ :=
    exists_mem_lambdaSet_conjSub_eq hR hiso hY hP hS₀R hS₀le hS₀Y hS hSle hSY
  refine ⟨conjSub D₀ u, hR.conjSub_mem hD₀ u, ?_, ?_⟩
  · have := Opposite.conj hYD₀ u
    rwa [conjSub_of_forall_commute fun y hy => (hU.1.2.2 y hy u hu).symm] at this
  · have := Sec3.special_conjSub hR hS₀ψ.2 u
    rwa [hS₀u] at this

end Lines

section Collinear

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem mem_lambdaSet_of_le_M {A C : Subgroup G} (hA : A ∈ R) (hC : C ∈ R) (hle : C ≤ M R A)
    (hne : C ≠ A) : C ∈ lambdaSet R A := by
  have hmem : C ∈ {B | B ∈ R ∧ B ≤ M R A} := ⟨hC, hle⟩
  rw [(Q_eq_M_of_omegaSet hR hiso hnd hΩ hA).2.1] at hmem
  exact hmem.resolve_left hne

omit hΩ in
theorem commuting_of_mem (hΔ : IsWeakTI R Δ) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ) :
    Commuting A B :=
  (commuting_gen_of_isWeakTI_of hR hiso hnd hΔ).mono (le_gen hA) (le_gen hB)

theorem mem_lambdaSet_or_exists (hΔ : IsWeakTI R Δ) {A B : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) (hAB : A ≠ B) :
    B ∈ lambdaSet R A ∨ ∃ D ∈ Δ, D ∈ lambdaSet R A ∧ B ∈ lambdaSet R D := by
  by_cases hBl : B ∈ lambdaSet R A
  · exact Or.inl hBl
  right
  have hAR := hΔ.1 hA
  have hBR := hΔ.1 hB
  have hABc := commuting_of_mem hR hiso hnd hΔ hA hB
  obtain ⟨C, hC, hBC⟩ : ∃ C ∈ lambdaSet R A, ¬ Commuting B C := by
    by_contra! hall
    have hBM : Commuting B (M R A) := commuting_iff_le_centralizer.2
      (sup_le (commuting_iff_le_centralizer.1 hABc.symm)
        (iSup₂_le fun C hC => commuting_iff_le_centralizer.1 (hall C hC)))
    have hmem : B ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hBR, hBM⟩
    rw [setOf_commuting_M_eq_singleton hR hiso hnd hΩ hAR] at hmem
    exact hAB (Set.mem_singleton_iff.1 hmem).symm
  have hCR : C ∈ R := hC.1.1
  have hne : B ≠ C := fun e => hBl (e ▸ hC)
  have hs : Special R B C := by
    rcases hR.rel B hBR C hCR hne with h | h | h
    · exact absurd h hBC
    · exact absurd hABc.symm
        (not_commuting_of_opposite_of_mem_lambdaSet hR hBR h (mem_lambdaSet_comm hAR hC))
    · exact h
  have hDΔ : ⁅B, C⁆ ∈ Δ := commutator_mem hR hiso hΔ hB hCR hA hC.1.2.2.symm hs
  have hDl := mem_lambdaSet_commutator hR hiso hBR hCR hs
  have hDM : ⁅B, C⁆ ≤ M R A := by
    rw [Subgroup.commutator_le]
    intro b hb c hc
    have hbn := QD.le_normalizer_M hR hAR (⟨hBR, hABc⟩ : B ∈ centralSet R A) hb
    have hcM : c ∈ M R A := QD.le_M hC hc
    rw [commutatorElement_def]
    exact (M R A).mul_mem ((Subgroup.mem_normalizer_iff.1 hbn c).1 hcM) ((M R A).inv_mem hcM)
  have hDA : ⁅B, C⁆ ≠ A := fun e => hBl (e ▸ hDl.1)
  exact ⟨_, hDΔ, mem_lambdaSet_of_le_M hR hiso hnd hΩ hAR hs.1 hDM hDA, hDl.1⟩

omit hΩ in
theorem commuting_commutator_of_special (hΔ : IsWeakTI R Δ) {A C E B : Subgroup G}
    (hA : A ∈ Δ) (hC : C ∈ Δ) (hE : E ∈ R) (hEA : Special R E A) (hEC : Special R E C)
    (hB : B ∈ Δ) (hBE : Opposite B E) : Commuting ⁅E, C⁆ A := by
  by_contra hnc
  have hAR := hΔ.1 hA
  have hCR := hΔ.1 hC
  have hFR : ⁅E, C⁆ ∈ R := hEC.1
  have hAC := commuting_of_mem hR hiso hnd hΔ hA hC
  have hCl : C ∈ lambdaSet R ⁅E, C⁆ := (mem_lambdaSet_commutator hR hiso hE hCR hEC).2
  have hAl : A ∈ lambdaSet R ⁅E, A⁆ := (mem_lambdaSet_commutator hR hiso hE hAR hEA).2
  have hAF : Special R A ⁅E, C⁆ := by
    have hne : A ≠ ⁅E, C⁆ := fun e => hnc (e ▸ hR.commuting_self hAR)
    rcases hR.rel A hAR _ hFR hne with h | h | h
    · exact absurd h.symm hnc
    · exact absurd hAC (not_commuting_of_opposite_of_mem_lambdaSet hR hAR h hCl)
    · exact h
  have hL : ⁅A, ⁅E, C⁆⁆ ∈ Δ := commutator_mem hR hiso hΔ hA hFR hC hEC.2.2 hAF
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
  have hee : e * e = 1 := hR.mul_self E hE e he
  have hLe : conjSub ⁅A, ⁅E, C⁆⁆ e = ⁅⁅E, A⁆, C⁆ := by
    rw [← commutator_conjSub_right_eq hR hiso hE hCR hEC he he1 hAC, conjSub,
      Subgroup.map_commutator, ← conjSub, ← conjSub, conjSub_conjSub_of_mul_self hee,
      commutator_conjSub_left_eq hR hiso hE hAR hEA he he1 hAC]
  have hF'R : ⁅E, A⁆ ∈ R := hEA.1
  have hnc' : ¬ Commuting ⁅E, A⁆ C := by
    intro h
    apply hR.ne_bot _ (hR.conjSub_mem hAF.1 e)
    rw [hLe]
    exact commuting_iff_commutator_eq_bot.1 h
  have hCF' : Special R C ⁅E, A⁆ := by
    have hne : C ≠ ⁅E, A⁆ := fun e => hnc' (e ▸ hR.commuting_self hCR)
    rcases hR.rel C hCR _ hF'R hne with h | h | h
    · exact absurd h.symm hnc'
    · exact absurd hAC.symm (not_commuting_of_opposite_of_mem_lambdaSet hR hCR h hAl)
    · exact h
  have hL' : ⁅C, ⁅E, A⁆⁆ ∈ Δ := commutator_mem hR hiso hΔ hC hF'R hA hEA.2.2 hCF'
  rw [Subgroup.commutator_comm, ← hLe] at hL'
  have hint : Δ ∩ conjSet Δ e = Δ := by
    rcases hΔ.2.2.2 e ⟨E, hE, he, he1⟩ with h | h
    · exact absurd (h ▸ (⟨hL', conjSub_mem_conjSet hL e⟩ : _ ∈ Δ ∩ conjSet Δ e) :
        conjSub ⁅A, ⁅E, C⁆⁆ e ∈ (∅ : Set (Subgroup G))) id
    · exact h
  have hBe : conjSub B e ∈ Δ := by
    have h1 : B ∈ conjSet Δ e := (hint.symm ▸ hB : B ∈ Δ ∩ conjSet Δ e).2
    rw [mem_conjSet, hR.inv_eq hE he] at h1
    exact h1
  obtain ⟨b, hb, -, hbe⟩ := hBE.2.2 e he he1
  have hop : Opposite B (conjSub B e) := by
    have := Sec3.opposite_conjSub hBE b
    rwa [conjSub_of_mem hb, hbe] at this
  exact not_opposite_of_isWeakTI hR hiso hnd hΔ hB hBe hop

omit hΩ in
theorem le_M_of_special (hΔ : IsWeakTI R Δ) {A B C E : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hC : C ∈ Δ) (hAB : A ∈ lambdaSet R B) (hCB : C ∈ lambdaSet R B) (hE : E ∈ R)
    (hBE : Opposite B E) (hEA : Special R E A) (hEC : Special R E C) : C ≤ M R A := by
  have hAR := hΔ.1 hA
  have hBR := hΔ.1 hB
  have hcomm := commuting_commutator_of_special hR hiso hnd hΔ hA hC hE hEA hEC hB hBE
  have hFn : ⁅E, C⁆ ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) :=
    QD.le_normalizer_M hR hAR ⟨hEC.1, hcomm.symm⟩
  have hBM : B ≤ M R A := QD.le_M (mem_lambdaSet_comm hBR hAB)
  intro c hc
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
  obtain ⟨e, he, -, hbe⟩ := hBE.2.1 b hb hb1
  have key := Sec3.commutatorElement_commutatorElement_eq hR hiso hBR hE hBE hCB
    ⟨hΔ.1 hC, hEC⟩ hb hb1 he hbe hc
  have hf : ⁅e, c⁆ ∈ ⁅E, C⁆ := Subgroup.commutator_mem_commutator he hc
  rw [← key, commutatorElement_def,
    show b * ⁅e, c⁆ * b⁻¹ * ⁅e, c⁆⁻¹ = b * (⁅e, c⁆ * b⁻¹ * ⁅e, c⁆⁻¹) by group]
  exact (M R A).mul_mem (hBM hb)
    ((Subgroup.mem_normalizer_iff.1 (hFn hf) b⁻¹).1 ((M R A).inv_mem (hBM hb)))

theorem mem_lambdaSet_of_mem_lambdaSet (hΔ : IsWeakTI R Δ) {A B C : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) (hC : C ∈ Δ) (hAB : A ∈ lambdaSet R B) (hCB : C ∈ lambdaSet R B)
    (hAC : A ≠ C) : C ∈ lambdaSet R A := by
  have hAR := hΔ.1 hA
  have hBR := hΔ.1 hB
  have hCR := hΔ.1 hC
  obtain ⟨E, hE, hBE, hEA⟩ :=
    exists_opposite_special hR hiso hBR hAB hAR le_sup_right hAB.1.2.1
  have hEC : ¬ Commuting E C := not_commuting_of_opposite_of_mem_lambdaSet hR hE hBE.symm hCB
  have hne : E ≠ C := fun e => hEC (e ▸ hR.commuting_self hE)
  refine mem_lambdaSet_of_le_M hR hiso hnd hΩ hAR hCR ?_ hAC.symm
  rcases hR.rel E hE C hCR hne with h | h | h
  · exact absurd h hEC
  ·
    obtain ⟨C', ⟨hC'R, hC'le, hC'ψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hBR hE hBE hCB
    have hBC' : B ≠ C' := by
      rintro rfl
      exact Special.not_opposite hR hE hC'ψ.2 hBE.symm
    have hC'Δ : C' ∈ Δ := mem_of_le_sup hR hiso hΔ hB hC hCB hC'R hC'le
    obtain ⟨hC'l, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hBR hCB hBR le_sup_left hC'R hC'le hBC'
    have hC'M : C' ≤ M R A := by
      by_cases hC'A : C' = A
      · exact hC'A ▸ QD.le_M_self
      · exact le_M_of_special hR hiso hnd hΔ hA hB hC'Δ hAB hC'l hE hBE hEA hC'ψ.2
    have hBM : B ≤ M R A := QD.le_M (mem_lambdaSet_comm hBR hAB)
    calc C ≤ B ⊔ C := le_sup_right
      _ = B ⊔ C' := hsup.symm
      _ ≤ M R A := sup_le hBM hC'M
  · exact le_M_of_special hR hiso hnd hΔ hA hB hC hAB hCB hE hBE hEA h

theorem mem_lambdaSet (hΔ : IsWeakTI R Δ) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hAB : A ≠ B) : B ∈ lambdaSet R A := by
  rcases mem_lambdaSet_or_exists hR hiso hnd hΩ hΔ hA hB hAB with h | ⟨D, hD, hDA, hBD⟩
  · exact h
  · exact mem_lambdaSet_of_mem_lambdaSet hR hiso hnd hΩ hΔ hA hD hB
      (mem_lambdaSet_comm (hΔ.1 hA) hDA) hBD hAB

theorem exists_mem_le_of_mem_gen (hΔ : IsWeakTI R Δ) {S : Set (Subgroup G)} (hS : S ⊆ Δ)
    {x : G} (hx : x ∈ gen S) (hx1 : x ≠ 1) : ∃ T ∈ Δ, T ≤ gen S ∧ x ∈ T := by
  have key : x = 1 ∨ ∃ T ∈ Δ, T ≤ gen S ∧ x ∈ T := by
    refine gen_induction (p := fun x => x = 1 ∨ ∃ T ∈ Δ, T ≤ gen S ∧ x ∈ T) hx
      (fun B hB y hy => Or.inr ⟨B, hS hB, le_gen hB, hy⟩) (Or.inl rfl) ?_
    rintro y z (rfl | ⟨T₁, hT₁, hT₁le, hy⟩) (rfl | ⟨T₂, hT₂, hT₂le, hz⟩)
    · exact Or.inl (one_mul 1)
    · rw [one_mul]
      exact Or.inr ⟨T₂, hT₂, hT₂le, hz⟩
    · rw [mul_one]
      exact Or.inr ⟨T₁, hT₁, hT₁le, hy⟩
    · by_cases hT : T₁ = T₂
      · subst hT
        exact Or.inr ⟨T₁, hT₁, hT₁le, T₁.mul_mem hy hz⟩
      by_cases hyz : y * z = 1
      · exact Or.inl hyz
      have hl := mem_lambdaSet hR hiso hnd hΩ hΔ hT₁ hT₂ hT
      obtain ⟨T, hTR, hTle, hyzT⟩ :=
        hl.2 _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hz)) hyz
      exact Or.inr ⟨T, mem_of_le_sup hR hiso hΔ hT₁ hT₂ hl hTR hTle, hTle.trans
        (sup_le hT₁le hT₂le), hyzT⟩
  exact key.resolve_left hx1

theorem coveredBy_gen (hΔ : IsWeakTI R Δ) : CoveredBy R (gen Δ) := fun x hx hx1 => by
  obtain ⟨T, hT, hTle, hxT⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ subset_rfl hx hx1
  exact ⟨T, hΔ.1 hT, hTle, hxT⟩

theorem mem_of_le_gen (hΔ : IsWeakTI R Δ) {S : Set (Subgroup G)} (hS : S ⊆ Δ) {B : Subgroup G}
    (hB : B ∈ R) (hle : B ≤ gen S) : B ∈ Δ := by
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  obtain ⟨T, hT, -, hbT⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ hS (hle hb) hb1
  rw [Sec3.eq_of_mem_of_mem hR hiso hB (hΔ.1 hT) hb hbT hb1]
  exact hT

theorem exists_mem_stabSet_conjSub_eq (hΔ : IsWeakTI R Δ) {A B : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) : ∃ g ∈ stabSet Δ, conjSub A g = B := by
  by_cases hAB : A = B
  · exact ⟨1, one_mem _, by rw [hAB, conjSub_one]⟩
  have hAR := hΔ.1 hA
  have hBR := hΔ.1 hB
  have hl := mem_lambdaSet hR hiso hnd hΩ hΔ hA hB hAB
  obtain ⟨Y, hY, hYle, hYA, hYB⟩ := exists_mem_le_sup_ne_ne hR hiso hAR hl A B
  have hYΔ : Y ∈ Δ := mem_of_le_sup hR hiso hΔ hA hB hl hY hYle
  obtain ⟨hAY, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hAR hl hY hYle hAR le_sup_left hYA
  obtain ⟨U, hU, u, hu, hAu⟩ := exists_mem_lambdaSet_conjSub_eq hR hiso hY hAY hAR le_sup_right
    (Ne.symm hYA) hBR (hsup ▸ le_sup_right) (Ne.symm hYB)
  exact ⟨u, le_stabSet_of_commuting hR hΔ hU.1.1 hYΔ hU.1.2.2.symm hu, hAu⟩

end Collinear

end Sec5

end CFSG.Timmesfeld.ARS
