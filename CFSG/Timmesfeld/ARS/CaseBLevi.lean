module

public import CFSG.Timmesfeld.ARS.CaseBPlane
public import CFSG.Timmesfeld.ARS.Sec8Natural
public import CFSG.Timmesfeld.ARS.Sec8Components

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne Matrix

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseB

section Natural

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G} (hA : A ∈ R)
  (hB : B ∈ R) (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A) (hBC : C ∈ psiSet R B)
include hR hiso hA hB hAB hAC hBC

theorem exists_conjSub_eq_of_natural {P₁ P₂ : Subgroup G} (hP₁ : P₁ ∈ R)
    (hP₁N : P₁ ≤ C ⊔ ⁅B, C⁆) (hP₁C : P₁ ≠ C) (hP₂ : P₂ ∈ R) (hP₂N : P₂ ≤ C ⊔ ⁅B, C⁆)
    (hP₂C : P₂ ≠ C) : ∃ a ∈ A, conjSub P₁ a = P₂ := by
  obtain ⟨n, -, -, φ, hφA, -⟩ := hAB.exists_mulEquiv_SL2' hR hA
  set k := GaloisField 2 n
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hAC.1.1
  obtain ⟨θ, hθ, hrange, -⟩ :=
    Sec3.exists_isNaturalModule hR hiso hA hB hAB hAC hBC φ hφA hw hw1
  have hmem : ∀ y ∈ C ⊔ ⁅B, C⁆, ∃ v, θ v = y := fun y hy => by
    rw [← SetLike.mem_coe, ← hrange] at hy
    exact hy
  have hθN : ∀ v, θ v ∈ C ⊔ ⁅B, C⁆ := fun v => by
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨v, rfl⟩
  have hfixC : ∀ v : Fin 2 → k, v 1 = 0 → θ v ∈ C := fun v hv =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC (hθN v)
      ((hθ.forall_commute_upper_iff hφA le_sup_left v).2 hv)
  have hCfix : ∀ v, θ v ∈ C → v 1 = 0 := fun v hv =>
    (hθ.forall_commute_upper_iff hφA le_sup_left v).1 fun a ha => hAC.1.2.2 a ha _ hv
  have hline : ∀ {P : Subgroup G}, P ∈ R → P ≤ C ⊔ ⁅B, C⁆ → ∀ v, θ v ∈ P → θ v ≠ 1 →
      ∀ c : k, θ (c • v) ∈ P := by
    intro P hP hPN v hvP hv1 c
    obtain ⟨x, hx, hvx⟩ :=
      Sec3.exists_mem_conjSub_of_mem_sup hR hiso hA hB hAB hAC hBC (hPN hvP) hv1
    have hPx : P = conjSub C x :=
      Sec3.eq_of_mem_of_mem hR hiso hP (hR.conjSub_mem hAC.1.1 x) hvP hvx hv1
    set y : ↥(A ⊔ B) := ⟨x, hx⟩
    have e1 : θ ((φ y⁻¹ : Matrix (Fin 2) (Fin 2) k) *ᵥ v) = x⁻¹ * θ v * x := by
      rw [hθ.map_mulVec]
      simp [y]
    have hu : θ ((φ y⁻¹ : Matrix (Fin 2) (Fin 2) k) *ᵥ v) ∈ C := by
      rw [e1]
      exact (mem_conjSub (H := C) (g := x)).1 (hPx ▸ hvP)
    have hu1 := hCfix _ hu
    have hcu : θ (c • ((φ y⁻¹ : Matrix (Fin 2) (Fin 2) k) *ᵥ v)) ∈ C :=
      hfixC _ (by rw [Pi.smul_apply, hu1, smul_zero])
    have e2 : θ (c • v) = x * θ (c • ((φ y⁻¹ : Matrix (Fin 2) (Fin 2) k) *ᵥ v)) * x⁻¹ := by
      have := hθ.map_mulVec y (c • ((φ y⁻¹ : Matrix (Fin 2) (Fin 2) k) *ᵥ v))
      rw [← this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        ← map_mul, mul_inv_cancel, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [e2, hPx]
    exact conj_mem_conjSub x hcu
  obtain ⟨n₁, hn₁, hn₁1⟩ := hR.exists_ne_one hP₁
  obtain ⟨n₂, hn₂, hn₂1⟩ := hR.exists_ne_one hP₂
  obtain ⟨v₁, rfl⟩ := hmem n₁ (hP₁N hn₁)
  obtain ⟨v₂, rfl⟩ := hmem n₂ (hP₂N hn₂)
  have hv₁ : v₁ 1 ≠ 0 := fun h0 =>
    hP₁C (Sec3.eq_of_mem_of_mem hR hiso hP₁ hAC.1.1 hn₁ (hfixC v₁ h0) hn₁1)
  have hv₂ : v₂ 1 ≠ 0 := fun h0 =>
    hP₂C (Sec3.eq_of_mem_of_mem hR hiso hP₂ hAC.1.1 hn₂ (hfixC v₂ h0) hn₂1)
  set lam : k := v₁ 1 / v₂ 1
  set t : k := (lam * v₂ 0 - v₁ 0) / v₁ 1
  obtain ⟨a, ha, hat⟩ : ∃ a ∈ A, ∀ v : Fin 2 → k, ⁅a, θ v⁆ = θ ![t * v 1, 0] := by
    refine ⟨((φ.symm (upperElt k t) : ↥(A ⊔ B)) : G), (NaturalModule.coe_mem_iff hφA _).2 (by
      rw [MulEquiv.apply_symm_apply]
      exact (mem_upperUnipotent_iff k).2 ⟨t, rfl⟩), fun v => ?_⟩
    rw [hθ.commutatorElement_eq, MulEquiv.apply_symm_apply, NaturalModule.upperElt_mulVec_sub]
  refine ⟨a, ha, ?_⟩
  have hconj : a * θ v₁ * a⁻¹ = θ (lam • v₂) := by
    rw [show a * θ v₁ * a⁻¹ = ⁅a, θ v₁⁆ * θ v₁ by rw [commutatorElement_def]; group, hat,
      ← hθ.map_add]
    congr 1
    ext i
    fin_cases i
    · simp only [lam, t]
      simp
      field_simp
      ring
    · simp only [lam, t]
      simp
      field_simp
  have hmemP₂ : a * θ v₁ * a⁻¹ ∈ P₂ := by
    rw [hconj]
    exact hline hP₂ hP₂N v₂ hn₂ hn₂1 lam
  have h1 : a * θ v₁ * a⁻¹ ≠ 1 := by
    intro e
    apply hn₁1
    rw [show θ v₁ = a⁻¹ * (a * θ v₁ * a⁻¹) * a by group, e]
    group
  exact Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hP₁ a) hP₂ (conj_mem_conjSub a hn₁)
    hmemP₂ h1

end Natural

theorem gen_pair (X Y : Subgroup G) : gen {X, Y} = X ⊔ Y := by
  rw [Sec5.gen_insert]
  congr 1
  simp [gen]

section Line

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hA₀ : A₀ ∈ omegaSet R A)
  {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) (hAΔ : A ∈ Δ)
include h hA hA₀ hΔ hAΔ

theorem existsUnique_mem_lambdaStar_of_le {P : Subgroup G} (hP : P ∈ Δ) (hPA : P ≠ A) :
    ∃! Q, (Q ∈ Δ ∧ Q ∈ lambdaStar R A A₀) ∧ Q ≤ A ⊔ P := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have hPl : P ∈ lambdaSet R A := Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hAΔ hP hPA.symm
  obtain ⟨D, ⟨hDR, hDle, hDψ⟩, huniq⟩ :=
    existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hPl
  have hDΔ : D ∈ Δ := Sec5.mem_of_le_sup hR hiso hΔ hAΔ hP hPl hDR hDle
  have hDA : D ≠ A := by
    rintro rfl
    exact hDψ.2.not_opposite hR hA₀.1 hA₀.2.symm
  refine ⟨D, ⟨⟨hDΔ, Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hAΔ hDΔ hDA.symm, hDψ⟩, hDle⟩, ?_⟩
  rintro Q ⟨⟨hQΔ, hQs⟩, hQle⟩
  exact huniq Q ⟨hΔ.1 hQΔ, hQle, hQs.2⟩

omit hA₀ in
theorem sup_eq_of_le_sup {P Q : Subgroup G} (hP : P ∈ Δ) (hPA : P ≠ A) (hQ : Q ∈ Δ)
    (hQA : Q ≠ A) (hQle : Q ≤ A ⊔ P) : A ⊔ Q = A ⊔ P := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hQle) ?_
  rw [card_sup_of_mem_lambdaSet h hA (Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hAΔ hP hPA.symm),
    card_sup_of_mem_lambdaSet h hA (Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hAΔ hQ hQA.symm)]

theorem commuting_gen_of_forall {X : Subgroup G} (hXA : Commuting X A)
    (hXL : ∀ Q ∈ Δ, Q ∈ lambdaStar R A A₀ → Commuting X Q) : Commuting X (gen Δ) := by
  refine commuting_iff_le_centralizer.2 (gen_le fun Y hY => ?_)
  by_cases hYA : Y = A
  · exact hYA ▸ commuting_iff_le_centralizer.1 hXA
  obtain ⟨Q, ⟨⟨hQΔ, hQs⟩, hQle⟩, -⟩ :=
    existsUnique_mem_lambdaStar_of_le h hA hA₀ hΔ hAΔ hY hYA
  have hQA : Q ≠ A := hQs.1.1.2.1
  have hline := sup_eq_of_le_sup h hA hΔ hAΔ hY hYA hQΔ hQA hQle
  exact (le_sup_right.trans hline.symm.le).trans
    (commuting_iff_le_centralizer.1 (hXA.sup_right (hXL Q hQΔ hQs)))

end Line

section Levi

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (h8 : Sec8 R A)
  (hA₀ : A₀ ∈ omegaSet R A) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) (hAΔ : A ∈ Δ)
include h hA h8 hA₀ hΔ hAΔ

omit hA h8 hA₀ in
theorem commuting_or_special_of_mem_leviSet {C F : Subgroup G} (hC : C ∈ leviSet R A A₀)
    (hF : F ∈ Δ) : Commuting C F ∨ Special R C F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hCR : C ∈ R := hC.1.1
  have hFR := hΔ.1 hF
  by_cases hCF : C = F
  · exact Or.inl (hCF ▸ hR.commuting_self hCR)
  rcases hR.rel C hCR F hFR hCF with h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
    have hFc : conjSub F c ∈ Δ :=
      Sec5.conjSub_mem_of_commuting hR hΔ hCR hAΔ hC.1.2.2.symm hc hF
    exact not_opposite_of_isWeakTI hR hiso hnd hΔ hF hFc
      (Sec5.opposite_conjSub_self h1.symm hc hc1)
  · exact Or.inr h1

theorem exists_special_lambdaStar :
    ∃ C ∈ leviSet R A A₀, ∃ F ∈ Δ, F ∈ lambdaStar R A A₀ ∧ Special R F C := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  obtain ⟨B, hBs, hBl⟩ : ∃ B ∈ sigmaSet R A, B ∉ lambdaSet R A := by
    by_contra! hall
    exact h8.2 (Set.Subset.antisymm hall fun B hB => hB.1)
  obtain ⟨m, -, hC₀⟩ := exists_mem_M_conjSub_mem_leviSet h hA h8.2 hA₀ hBs hBl
  set C₀ := conjSub B m
  by_contra! hall
  have hC₀R : C₀ ∈ R := hC₀.1.1
  have hcomm : Commuting C₀ (gen Δ) := by
    refine commuting_gen_of_forall h hA hA₀ hΔ hAΔ hC₀.1.2.2.symm fun Q hQ hQs => ?_
    rcases commuting_or_special_of_mem_leviSet h hΔ hAΔ hC₀ hQ with h1 | h1
    · exact h1
    · exact absurd h1.symm (hall C₀ hC₀ Q hQ hQs)
  have hC₀Δ : C₀ ∈ Δ := Sec5.mem_of_commuting_gen hR hiso hnd hΩ hΔ hC₀R hcomm
  have hC₀l : C₀ ∈ lambdaSet R A :=
    Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hAΔ hC₀Δ hC₀.1.2.1.symm
  exact not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hC₀l hC₀.2.2.2

omit hA h8 hA₀ in
theorem commutator_mem_of_mem_leviSet {C F : Subgroup G} (hC : C ∈ leviSet R A A₀)
    (hF : F ∈ Δ) (hFC : Special R F C) : ⁅F, C⁆ ∈ Δ :=
  have := h.finite
  Sec5.commutator_mem h.root h.noIsolated hΔ hF hC.1.1 hAΔ hC.1.2.2.symm hFC

theorem mem_of_le_sup_commutator {C F : Subgroup G} (hC : C ∈ leviSet R A A₀) (hF : F ∈ Δ)
    (hF' : F ∈ lambdaStar R A A₀) (hFC : Special R F C) {P : Subgroup G} (hP : P ∈ R)
    (hPle : P ≤ F ⊔ ⁅F, C⁆) : P ∈ Δ ∧ P ∈ lambdaStar R A A₀ := by
  have := h.finite
  have hFC' := commutator_mem_of_mem_leviSet h hΔ hAΔ hC hF hFC
  exact ⟨Sec5.mem_of_le_gen h.root h.noIsolated h.nondeg (eq_of_omegaSet h) hΔ subset_rfl hP
    (hPle.trans (sup_le (le_gen hF) (le_gen hFC'))),
    (exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hC hF' hFC).1 P hP hPle⟩

omit h8 hA₀ hAΔ in
theorem card_sup_commutator {C F : Subgroup G} (hC : C ∈ leviSet R A A₀) (hF : F ∈ Δ)
    (hFC : Special R F C) : Nat.card ↥(F ⊔ ⁅F, C⁆) = Nat.card A ^ 2 := by
  have := h.finite
  have hR := h.root
  have hFR := hΔ.1 hF
  have hl : ⁅F, C⁆ ∈ lambdaSet R F :=
    mem_lambdaSet_comm hFC.1 (mem_lambdaSet_commutator hR h.noIsolated hFR hC.1.1 hFC).1
  rw [card_sup_of_mem_lambdaSet h hFR hl, hR.card_eq hFR hA]

theorem le_sup_commutator_of_mem {C F : Subgroup G} (hC : C ∈ leviSet R A A₀) (hF : F ∈ Δ)
    (hF' : F ∈ lambdaStar R A A₀) (hFC : Special R F C) {Q : Subgroup G} (hQ : Q ∈ Δ)
    (hQ' : Q ∈ lambdaStar R A A₀) : Q ≤ F ⊔ ⁅F, C⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have hFC' := commutator_mem_of_mem_leviSet h hΔ hAΔ hC hF hFC
  have hQA : Q ≠ A := hQ'.1.1.2.1
  have hq : 2 ≤ Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)
  have h3 := card_gen_eq_pow_three h hΔ hAΔ h8
  have hAQ : Nat.card ↥(A ⊔ Q) = Nat.card A ^ 2 :=
    card_sup_of_mem_lambdaSet h hA (Sec5.mem_lambdaSet hR hiso hnd hΩ hΔ hAΔ hQ hQA.symm)
  have hN := card_sup_commutator h hA hΔ hC hF hFC
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ (A ⊔ Q) ⊓ (F ⊔ ⁅F, C⁆), x ≠ 1 := by
    by_contra! hall
    have hinf : (A ⊔ Q) ⊓ (F ⊔ ⁅F, C⁆) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
    have h1 := card_mul_card_le_card_sup hinf
    have h2 : Nat.card ↥((A ⊔ Q) ⊔ (F ⊔ ⁅F, C⁆)) ≤ Nat.card ↥(gen Δ) :=
      Subgroup.card_le_of_le (sup_le (sup_le (le_gen hAΔ) (le_gen hQ))
        (sup_le (le_gen hF) (le_gen hFC')))
    rw [hAQ, hN, h3] at *
    have := h1.trans h2
    have : Nat.card A ^ 2 * Nat.card A ^ 2 ≤ Nat.card A ^ 3 := this
    nlinarith
  obtain ⟨T, hT, -, hxT⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ
    (S := {A, Q}) (by rintro _ (rfl | rfl) <;> assumption) (by rw [gen_pair]; exact hx.1) hx1
  obtain ⟨T', hT', hT'le, hxT'⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ
    (S := {F, ⁅F, C⁆}) (by rintro _ (rfl | rfl) <;> assumption) (by rw [gen_pair]; exact hx.2)
    hx1
  rw [gen_pair] at hT'le
  obtain rfl : T = T' := Sec3.eq_of_mem_of_mem hR hiso (hΔ.1 hT) (hΔ.1 hT') hxT hxT' hx1
  have hTs := (mem_of_le_sup_commutator h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC (hΔ.1 hT) hT'le).2
  have hTle : T ≤ A ⊔ Q := by
    obtain ⟨T₁, hT₁, hT₁le, hxT₁⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ
      (S := {A, Q}) (by rintro _ (rfl | rfl) <;> assumption) (by rw [gen_pair]; exact hx.1) hx1
    rw [gen_pair] at hT₁le
    rwa [Sec3.eq_of_mem_of_mem hR hiso (hΔ.1 hT) (hΔ.1 hT₁) hxT hxT₁ hx1]
  obtain ⟨Q₀, -, huniq⟩ := existsUnique_mem_lambdaStar_of_le h hA hA₀ hΔ hAΔ hQ hQA
  have e1 := huniq T ⟨⟨hT, hTs⟩, hTle⟩
  have e2 := huniq Q ⟨⟨hQ, hQ'⟩, le_sup_right⟩
  rw [e2.trans e1.symm]
  exact hT'le

end Levi

section Stab

variable (hR : IsRootClass R) {A A₀ : Subgroup G} {Θ : Set (Subgroup G)}
  (hΘ : IsWeakTI R Θ) (hAΘ : A ∈ Θ)
include hR hΘ hAΘ

theorem levi_le_stabSet : levi R A A₀ ≤ stabSet Θ :=
  iSup₂_le fun _ hB => Sec5.le_stabSet_of_commuting hR hΘ hB.1.1 hAΘ hB.1.2.2.symm

theorem M_le_stabSet : M R A ≤ stabSet Θ :=
  sup_le (fun _ ha => hΘ.mem_stabSet hR hAΘ ha)
    (iSup₂_le fun _ hB => Sec5.le_stabSet_of_commuting hR hΘ hB.1.1 hAΘ hB.1.2.2.symm)

end Stab

section Faithful

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (h8 : Sec8 R A)
  (hA₀ : A₀ ∈ omegaSet R A) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) (hAΔ : A ∈ Δ)
include h hA h8 hA₀ hΔ hAΔ

theorem commute_of_mem_conjSet {g : G} (hgA : conjSub A g = A) (hne : conjSet Δ g ≠ Δ) {v : G}
    (hv : v ∈ levi R A A₀) (hvV : ∀ d ∈ gen Δ, Commute v d)
    {Y : Subgroup G} (hY : Y ∈ conjSet Δ g) (hY' : Y ∈ lambdaStar R A A₀) :
    ∀ y ∈ Y, Commute v y := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have h3 := card_gen_eq_pow_three h hΔ hAΔ h8
  set Δ' := conjSet Δ g with hΔ'def
  have hΔ' : IsWeakTI R Δ' := Sec5.isWeakTI_conjSet hR hΔ g
  have hAΔ' : A ∈ Δ' := hgA ▸ conjSub_mem_conjSet hAΔ g
  have h3' : Nat.card ↥(gen Δ') = Nat.card A ^ 3 := by rw [Sec5.card_gen_conjSet, h3]
  have hint : ∀ X ∈ Δ, X ∈ Δ' → X = A := fun X hX hX' =>
    eq_of_mem_conjSet hR hiso hnd hΩ hΔ hne hX hX' hAΔ hAΔ'
  have hYl : Y ∈ lambdaSet R A := hY'.1
  have hYA : Y ≠ A := hYl.1.2.1
  have hYΔ : Y ∉ Δ := fun hY₀ => hYA (hint Y hY₀ hY)
  obtain ⟨P, hP, hPax, hPA⟩ := exists_mem_le_axis_ne h hΔ hAΔ h3 hYl hYΔ
  have hax := axis_eq_sup h hΔ hAΔ h3 hYl hYΔ hP hPax hPA
  obtain ⟨Q, ⟨⟨hQΔ, hQs⟩, hQle⟩, -⟩ := existsUnique_mem_lambdaStar_of_le h hA hA₀ hΔ hAΔ hP hPA
  have hQY : Commuting Q Y := (Sec5.le_axis_iff hQΔ).1 (hax ▸ hQle)
  have hQA : Q ≠ A := hQs.1.1.2.1
  have hQΔ' : Q ∉ Δ' := fun hQ' => hQA (hint Q hQΔ hQ')
  obtain ⟨P', hP', hP'ax, hP'A⟩ := exists_mem_le_axis_ne h hΔ' hAΔ' h3' hQs.1 hQΔ'
  have hax' := axis_eq_sup h hΔ' hAΔ' h3' hQs.1 hQΔ' hP' hP'ax hP'A
  obtain ⟨Y₀, -, huniq⟩ := existsUnique_mem_lambdaStar_of_le h hA hA₀ hΔ' hAΔ' hP' hP'A
  have hvA : conjSub A v = A := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hv) a ha).symm
  have hvA₀ : conjSub A₀ v = A₀ := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hv) a ha).symm
  have hvQ : conjSub Q v = Q :=
    conjSub_of_forall_commute fun q hq => hvV q (le_gen hQΔ hq)
  have hYv : conjSub Y v = Y := by
    have hYvΔ' : conjSub Y v ∈ Δ' := by
      rw [← mem_stabSet.1 (levi_le_stabSet hR hΔ' hAΔ' hv)]
      exact conjSub_mem_conjSet hY v
    have hYvs : conjSub Y v ∈ lambdaStar R A A₀ := by
      refine ⟨hvA ▸ conjSub_mem_lambdaSet hR hYl v, hR.conjSub_mem hY'.2.1 v, ?_⟩
      have := Sec3.special_conjSub hR hY'.2.2 v
      rwa [hvA₀] at this
    have hQYv : Commuting Q (conjSub Y v) := hvQ ▸ hQY.conjSub v
    have e1 := huniq Y ⟨⟨hY, hY'⟩, hax' ▸ (Sec5.le_axis_iff hY).2 hQY.symm⟩
    have e2 := huniq (conjSub Y v) ⟨⟨hYvΔ', hYvs⟩, hax' ▸ (Sec5.le_axis_iff hYvΔ').2 hQYv.symm⟩
    exact e2.trans e1.symm
  have hYst : Y ≤ stabSet Δ := Sec5.le_stabSet_of_commuting hR hΔ hYl.1.1 hAΔ hYl.1.2.2.symm
  obtain ⟨D, hD, hDY, -⟩ := Sec5.exists_special hR hiso hnd hΩ hΔ hAΔ hYl hYΔ
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one (hΔ.1 hD)
  intro y hy
  have hy' : v * y * v⁻¹ ∈ Y := hYv ▸ conj_mem_conjSub v hy
  have hyd : y * d * y⁻¹ ∈ gen Δ := by
    have := conj_mem_conjSub y (le_gen hD hd)
    rwa [conjSub_gen, mem_stabSet.1 (hYst hy)] at this
  have hcomm : Commute d (y⁻¹ * (v * y * v⁻¹)) := by
    have c1 : v⁻¹ * d = d * v⁻¹ := (hvV d (le_gen hD hd)).inv_left.eq
    have c2 : v * (y * d * y⁻¹) = (y * d * y⁻¹) * v := (hvV _ hyd).eq
    show d * (y⁻¹ * (v * y * v⁻¹)) = (y⁻¹ * (v * y * v⁻¹)) * d
    calc d * (y⁻¹ * (v * y * v⁻¹)) = y⁻¹ * ((y * d * y⁻¹) * v) * y * v⁻¹ := by group
      _ = y⁻¹ * (v * (y * d * y⁻¹)) * y * v⁻¹ := by rw [c2]
      _ = y⁻¹ * v * y * (d * v⁻¹) := by group
      _ = y⁻¹ * v * y * (v⁻¹ * d) := by rw [c1]
      _ = (y⁻¹ * (v * y * v⁻¹)) * d := by group
  have h1 : y⁻¹ * (v * y * v⁻¹) = 1 :=
    eq_one_of_commute_of_special hR hiso (hΔ.1 hD) hYl.1.1 hDY hd hd1
      (Y.mul_mem (Y.inv_mem hy) hy') hcomm
  have : v * y * v⁻¹ = y := by
    rw [← mul_left_cancel_iff (a := y⁻¹), h1, inv_mul_cancel]
  show v * y = y * v
  calc v * y = (v * y * v⁻¹) * v := by group
    _ = y * v := by rw [this]

theorem exists_conjSet_of_mem_lambdaStar {P : Subgroup G} (hP : P ∈ lambdaStar R A A₀) :
    ∃ c : G, conjSub A c = A ∧ conjSub A₀ c = A₀ ∧ P ∈ conjSet Δ c := by
  have := h.finite
  have hR := h.root
  have h3 := card_gen_eq_pow_three h hΔ hAΔ h8
  have hTI : ¬ IsTI R Δ := fun hTI => ((exists_isTI_iff h hA).2 ⟨Δ, hTI, hAΔ⟩) h8.1
  obtain ⟨g₁, hg₁A, hPg₁⟩ := exists_mem_conjSet_of_mem_lambdaSet h hΔ hTI hAΔ h3 hP.1
  have hA₀' : conjSub A₀ g₁ ∈ omegaSet R A :=
    ⟨hR.conjSub_mem hA₀.1 g₁, hg₁A ▸ Sec3.opposite_conjSub hA₀.2 g₁⟩
  obtain ⟨m, hm, hmA₀⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet h hA h8.2 hA₀ hA₀'
  set c := m⁻¹ * g₁ with hc
  have hcA₀ : conjSub A₀ c = A₀ := by
    rw [hc, conjSub_mul, ← hmA₀, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hmA : conjSub A m⁻¹ = A := conjSub_of_forall_commute fun a ha =>
    (QD.commuting_M hR hA a ha _ ((M R A).inv_mem hm)).symm
  have hcA : conjSub A c = A := by rw [hc, conjSub_mul, hg₁A, hmA]
  have hΔc : IsWeakTI R (conjSet Δ c) := Sec5.isWeakTI_conjSet hR hΔ c
  have hAΔc : A ∈ conjSet Δ c := hcA ▸ conjSub_mem_conjSet hAΔ c
  refine ⟨c, hcA, hcA₀, ?_⟩
  have e : g₁ = m * c := by rw [hc, mul_inv_cancel_left]
  rw [e, conjSet_mul, mem_stabSet.1 (M_le_stabSet hR hΔc hAΔc hm)] at hPg₁
  exact hPg₁

theorem eq_one_of_mem_levi_of_commute {C F : Subgroup G} (hC : C ∈ leviSet R A A₀)
    (hF : F ∈ Δ) (hF' : F ∈ lambdaStar R A A₀) (hFC : Special R F C) {v : G}
    (hv : v ∈ levi R A A₀) (hvM : ∀ m ∈ F ⊔ ⁅F, C⁆, Commute v m) : v = 1 := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ := eq_of_omegaSet h
  have h3 := card_gen_eq_pow_three h hΔ hAΔ h8
  have hTI : ¬ IsTI R Δ := fun hTI => ((exists_isTI_iff h hA).2 ⟨Δ, hTI, hAΔ⟩) h8.1
  have hFC' := commutator_mem_of_mem_leviSet h hΔ hAΔ hC hF hFC
  set N := F ⊔ ⁅F, C⁆ with hNdef
  have hvA : ∀ a ∈ A, Commute v a := fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hv) a ha).symm
  have hAN : A ⊓ N = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    by_contra hx1
    obtain ⟨T, hT, hTle, hxT⟩ := Sec5.exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ
      (S := {F, ⁅F, C⁆}) (by rintro _ (rfl | rfl) <;> assumption)
      (by rw [gen_pair]; exact hx.2) hx1
    rw [gen_pair] at hTle
    obtain rfl : A = T := Sec3.eq_of_mem_of_mem hR hiso hA (hΔ.1 hT) hx.1 hxT hx1
    exact (mem_of_le_sup_commutator h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hA hTle).2.1.1.2.1 rfl
  have hcommAN : Commuting A N := (Sec5.commuting_of_mem hR hiso hnd hΔ hAΔ hF).sup_right
    (Sec5.commuting_of_mem hR hiso hnd hΔ hAΔ hFC')
  have hgen : A ⊔ N = gen Δ := Subgroup.eq_of_le_of_card_ge
    (sup_le (le_gen hAΔ) (sup_le (le_gen hF) (le_gen hFC'))) (by
      rw [h3, le_antisymm (card_sup_le_of_commuting hcommAN) (card_mul_card_le_card_sup hAN),
        card_sup_commutator h hA hΔ hC hF hFC]
      ring_nf
      exact le_rfl)
  have hvV : ∀ d ∈ gen Δ, Commute v d := by
    intro d hd
    rw [← hgen] at hd
    have : A ⊔ N ≤ Subgroup.centralizer {v} := sup_le
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hvA a ha).symm)
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.2 (hvM m hm).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (this hd)).symm
  have hvS : ∀ P ∈ lambdaStar R A A₀, ∀ p ∈ P, Commute v p := by
    intro P hP
    obtain ⟨c, hcA, -, hPc⟩ := exists_conjSet_of_mem_lambdaStar h hA h8 hA₀ hΔ hAΔ hP
    by_cases hΔeq : conjSet Δ c = Δ
    · rw [hΔeq] at hPc
      exact fun p hp => hvM p (le_sup_commutator_of_mem h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hPc hP hp)
    · exact commute_of_mem_conjSet h hA h8 hA₀ hΔ hAΔ hcA hΔeq hv hvV hPc hP
  have hcent : gen (lambdaSet R A) ⊔ A₀ ≤ Subgroup.centralizer {v} := by
    refine sup_le (gen_le fun B hB => ?_) fun a ha => Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hv) a ha)
    have hBM : B ≤ M R A := QD.le_M hB
    rw [M_eq_gen_lambdaStar h hA hA₀] at hBM
    refine hBM.trans (gen_le fun P hP p hp => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.2 (hvS P hP p hp).symm
  rw [gen_lambdaSet_sup_eq_top h hA hA₀] at hcent
  have hz : v ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (hcent (Subgroup.mem_top g))
  rw [h.center] at hz
  exact hz

theorem levi_eq_sup {C F : Subgroup G} (hC : C ∈ leviSet R A A₀) (hF : F ∈ Δ)
    (hF' : F ∈ lambdaStar R A A₀) (hFC : Special R F C) {D : Subgroup G}
    (hD : D ∈ leviSet R A A₀) (hCD : Opposite C D) (hFD : F ∈ lambdaSet R D) :
    levi R A A₀ = C ⊔ D := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hCR : C ∈ R := hC.1.1
  have hDR : D ∈ R := hD.1.1
  have hFR : F ∈ R := hΔ.1 hF
  have hFψ : F ∈ psiSet R C := ⟨hFR, hFC.symm⟩
  have hDC : Opposite D C := hCD.symm
  have hcomm' : ⁅C, F⁆ = ⁅F, C⁆ := Subgroup.commutator_comm C F
  set M := F ⊔ ⁅F, C⁆ with hMdef
  have hMeq : F ⊔ ⁅C, F⁆ = M := by rw [hcomm']
  have hCDle : C ⊔ D ≤ levi R A A₀ := sup_le (le_gen hC) (le_gen hD)
  have hDCle : D ⊔ C ≤ levi R A A₀ := sup_le (le_gen hD) (le_gen hC)
  have hfaith : ∀ w ∈ levi R A A₀, (∀ m ∈ M, Commute w m) → w = 1 := fun w hw hwM =>
    eq_one_of_mem_levi_of_commute h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hw hwM
  have hnorm : ∀ {B : Subgroup G}, B ∈ leviSet R A A₀ → ∀ {P : Subgroup G}, P ∈ R → P ≤ M →
      ∀ b ∈ B, conjSub P b ≤ M := by
    intro B hB P hP hPM b hb
    have hPs := mem_of_le_sup_commutator h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hP hPM
    have hbv : b ∈ levi R A A₀ := le_gen hB hb
    have hPbΔ : conjSub P b ∈ Δ := by
      rw [← mem_stabSet.1 (levi_le_stabSet hR hΔ hAΔ hbv)]
      exact conjSub_mem_conjSet hPs.1 b
    have hbA : conjSub A b = A := conjSub_of_forall_commute fun a ha =>
      (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hbv) a ha).symm
    have hbA₀ : conjSub A₀ b = A₀ := conjSub_of_forall_commute fun a ha =>
      (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hbv) a ha).symm
    have hPbs : conjSub P b ∈ lambdaStar R A A₀ := by
      refine ⟨hbA ▸ conjSub_mem_lambdaSet hR hPs.2.1 b, hR.conjSub_mem hP b, ?_⟩
      have := Sec3.special_conjSub hR hPs.2.2.2 b
      rwa [hbA₀] at this
    exact le_sup_commutator_of_mem h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hPbΔ hPbs
  refine le_antisymm (iSup₂_le fun B hB => ?_) hCDle
  have hBR : B ∈ R := hB.1.1
  obtain ⟨F₁, hF₁, hF₁M, hBF₁⟩ : ∃ F₁ ∈ R, F₁ ≤ M ∧ ¬ Commuting B F₁ := by
    by_contra! hall
    obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
    refine hb1 (hfaith b (le_gen hB hb) fun m hm => ?_)
    by_cases hm1 : m = 1
    · rw [hm1]; exact Commute.one_right b
    obtain ⟨P, hP, hPM, hmP⟩ := Sec3.coveredBy_sup_commutator hR hiso hDR hCR hDC hFD hFψ m
      (hMeq ▸ hm) hm1
    exact hall P hP (hMeq ▸ hPM) b hb m hmP
  have hF₁s := mem_of_le_sup_commutator h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hF₁ hF₁M
  have hBsp : Special R B F₁ :=
    (commuting_or_special_of_mem_leviSet h hΔ hAΔ hB hF₁s.1).resolve_left hBF₁
  set Y := ⁅B, F₁⁆ with hYdef
  have hYR : Y ∈ R := hBsp.1
  have hYcomm : ⁅F₁, B⁆ = Y := Subgroup.commutator_comm F₁ B
  have hYs : Y ∈ Δ ∧ Y ∈ lambdaStar R A A₀ := by
    refine ⟨hYcomm ▸ commutator_mem_of_mem_leviSet h hΔ hAΔ hB hF₁s.1 hBsp.symm, ?_⟩
    exact (exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hB hF₁s.2 hBsp.symm).1 Y hYR
      (hYcomm ▸ le_sup_right)
  have hYM : Y ≤ M := le_sup_commutator_of_mem h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hYs.1 hYs.2
  have hF₁Y : F₁ ≠ Y := fun e => hBF₁ (e ▸ hBsp.2.1.symm)
  obtain ⟨y₀, hy₀, hy₀1⟩ := hR.exists_ne_one hYR
  obtain ⟨x, hx, hy₀x⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hDR hCR hDC hFD hFψ
    (hMeq ▸ hYM hy₀) hy₀1
  have hYx : Y = conjSub F x :=
    Sec3.eq_of_mem_of_mem hR hiso hYR (hR.conjSub_mem hFR x) hy₀ hy₀x hy₀1
  have hNx : conjSub M x = M := by
    rw [← hMeq]; exact Sec3.conjSub_sup_commutator_eq hR hiso hDR hCR hDC hFD hFψ hx
  have hNx' : conjSub M x⁻¹ = M := by
    rw [← hNx, ← conjSub_mul, inv_mul_cancel, conjSub_one, hNx]
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1]; exact Subgroup.one_mem _
  set Z := conjSub F₁ b with hZdef
  have hZR : Z ∈ R := hR.conjSub_mem hF₁ b
  have hZM : Z ≤ M := hnorm hB hF₁ hF₁M b hb
  have hZY : Z ≠ Y := by
    intro e
    apply hF₁Y
    have hYb : conjSub Y b⁻¹ = Y := conjSub_of_forall_commute fun z hz =>
      (hBsp.2.1 z hz _ (B.inv_mem hb)).symm
    rw [← hYb, ← e, hZdef, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hpt : ∀ {P : Subgroup G}, P ∈ R → P ≤ M → P ≠ Y →
      conjSub P x⁻¹ ∈ R ∧ conjSub P x⁻¹ ≤ F ⊔ ⁅C, F⁆ ∧ conjSub P x⁻¹ ≠ F := by
    intro P hP hPM hPY
    refine ⟨hR.conjSub_mem hP x⁻¹, hMeq ▸ hNx' ▸ Subgroup.map_mono hPM, fun e => hPY ?_⟩
    rw [hYx, ← e, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  obtain ⟨h1R, h1N, h1F⟩ := hpt hF₁ hF₁M hF₁Y
  obtain ⟨h2R, h2N, h2F⟩ := hpt hZR hZM hZY
  obtain ⟨d, hd, hdeq⟩ := exists_conjSub_eq_of_natural hR hiso hDR hCR hDC hFD hFψ h1R h1N h1F h2R
    h2N h2F
  set b'' := x * d * x⁻¹ with hb''
  have hb''D : b'' ∈ D ⊔ C := Subgroup.mul_mem _ (Subgroup.mul_mem _ hx (Subgroup.mem_sup_left hd))
    (Subgroup.inv_mem _ hx)
  have hF₁b'' : conjSub F₁ b'' = Z := by
    rw [hb'', conjSub_mul, conjSub_mul, hdeq, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hb''Y : ∀ y ∈ Y, Commute b'' y := by
    intro y hy
    rw [hYx] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    change Commute (x * d * x⁻¹) (x * f * x⁻¹)
    have : Commute d f := hFD.1.2.2 d hd f hf
    simp only [Commute, SemiconjBy] at this ⊢
    calc x * d * x⁻¹ * (x * f * x⁻¹) = x * (d * f) * x⁻¹ := by group
      _ = x * (f * d) * x⁻¹ := by rw [this]
      _ = x * f * x⁻¹ * (x * d * x⁻¹) := by group
  have hb''M : ∀ m ∈ M, ⁅b'', m⁆ ∈ Y := by
    intro m hm
    have hm' : x⁻¹ * m * x ∈ F ⊔ ⁅C, F⁆ := by
      have := conj_mem_conjSub x⁻¹ hm
      rw [hNx', inv_inv] at this
      exact hMeq ▸ this
    have := Sec3.commutatorElement_mem_of_mem_sup hR hiso hDR hCR hDC hFD hFψ hd hm'
    rw [hYx]
    refine ⟨_, this, ?_⟩
    change x * ⁅d, x⁻¹ * m * x⁆ * x⁻¹ = ⁅b'', m⁆
    rw [hb'', commutatorElement_def, commutatorElement_def]
    group
  have hl : Y ∈ lambdaSet R F₁ :=
    mem_lambdaSet_comm hYR (mem_lambdaSet_commutator hR hiso hBR hF₁ hBsp).2
  have hMF : F₁ ⊔ Y = M := Subgroup.eq_of_le_of_card_ge (sup_le hF₁M hYM) (by
    rw [card_sup_commutator h hA hΔ hC hF hFC, card_sup_of_mem_lambdaSet h hF₁ hl,
      hR.card_eq hF₁ hA])
  have hZYinf : Z ⊓ Y = ⊥ := inf_eq_bot hR hiso hZR hYR hZY
  have hbF : ∀ f ∈ F₁, b * f * b⁻¹ = b'' * f * b''⁻¹ := by
    intro f hf
    have h1 : ⁅b, f⁆ ∈ Y := Subgroup.commutator_mem_commutator hb hf
    have h2 : ⁅b'', f⁆ ∈ Y := hb''M f (hF₁M hf)
    have h3 : b * f * b⁻¹ ∈ Z := conj_mem_conjSub b hf
    have h4 : b'' * f * b''⁻¹ ∈ Z := hF₁b'' ▸ conj_mem_conjSub b'' hf
    have hu : (b * f * b⁻¹) * (b'' * f * b''⁻¹)⁻¹ = ⁅b, f⁆ * ⁅b'', f⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    have hu1 : ⁅b, f⁆ * ⁅b'', f⁆⁻¹ ∈ Z ⊓ Y :=
      ⟨hu ▸ Z.mul_mem h3 (Z.inv_mem h4), Y.mul_mem h1 (Y.inv_mem h2)⟩
    rw [hZYinf, Subgroup.mem_bot, ← hu] at hu1
    exact mul_inv_eq_one.1 hu1
  have hbM : ∀ m ∈ M, b * m * b⁻¹ = b'' * m * b''⁻¹ := by
    intro m hm
    have hle : Y ≤ Subgroup.normalizer (F₁ : Set G) :=
      (commuting_iff_le_centralizer.1 hl.1.2.2).trans (Subgroup.centralizer_le_normalizer _)
    rw [← hMF, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left F₁ Y hle] at hm
    obtain ⟨f, hf, y, hy, rfl⟩ := hm
    have hby : b * y * b⁻¹ = y := by
      rw [(hBsp.2.1 y hy b hb).symm.eq, mul_inv_cancel_right]
    have hb''y : b'' * y * b''⁻¹ = y := by rw [(hb''Y y hy).eq, mul_inv_cancel_right]
    calc b * (f * y) * b⁻¹ = (b * f * b⁻¹) * (b * y * b⁻¹) := by group
      _ = (b'' * f * b''⁻¹) * (b'' * y * b''⁻¹) := by rw [hbF f hf, hby, hb''y]
      _ = b'' * (f * y) * b''⁻¹ := by group
  have hw : b''⁻¹ * b = 1 := by
    refine hfaith _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hDCle hb''D)) (le_gen hB hb))
      fun m hm => ?_
    show b''⁻¹ * b * m = m * (b''⁻¹ * b)
    have := hbM m hm
    calc b''⁻¹ * b * m = b''⁻¹ * (b * m * b⁻¹) * b := by group
      _ = b''⁻¹ * (b'' * m * b''⁻¹) * b := by rw [this]
      _ = m * (b''⁻¹ * b) := by group
  have : b = b'' := by rw [← mul_left_cancel_iff (a := b''⁻¹), hw, inv_mul_cancel]
  rw [this, sup_comm]
  exact hb''D

theorem exists_levi_eq_sup : ∃ C ∈ leviSet R A A₀, ∃ D ∈ leviSet R A A₀,
    Opposite C D ∧ levi R A A₀ = C ⊔ D := by
  obtain ⟨C, hC, F, hF, hF', hFC⟩ := exists_special_lambdaStar h hA h8 hA₀ hΔ hAΔ
  obtain ⟨-, D, hD, hCD, hFD⟩ := exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hC hF' hFC
  exact ⟨C, hC, D, hD, hCD, levi_eq_sup h hA h8 hA₀ hΔ hAΔ hC hF hF' hFC hD hCD hFD⟩

theorem opposite_of_mem_leviSet {B₁ B₂ : Subgroup G} (hB₁ : B₁ ∈ leviSet R A A₀)
    (hB₂ : B₂ ∈ leviSet R A A₀) (hne : B₁ ≠ B₂) : Opposite B₁ B₂ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨C, hC, D, hD, hCD, hV⟩ := exists_levi_eq_sup h hA h8 hA₀ hΔ hAΔ
  by_contra hop
  have hp := isPGroup_sup_of_not_opposite hR hB₁.1.1 hB₂.1.1 hop
  have hle : B₁ ⊔ B₂ ≤ C ⊔ D := hV ▸ sup_le (le_gen hB₁) (le_gen hB₂)
  have hq : 2 ≤ Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)
  have hcard : Nat.card A ^ 2 ≤ Nat.card ↥(B₁ ⊔ B₂) := by
    have := card_mul_card_le_card_sup (inf_eq_bot hR hiso hB₁.1.1 hB₂.1.1 hne)
    rwa [hR.card_eq hB₁.1.1 hA, hR.card_eq hB₂.1.1 hA, ← sq] at this
  have hr := hCD.isElemAbRankOne_of_mul_self (hsq := hR.mul_self C hC.1.1)
  have hodd := ElemAbRankOne.not_two_dvd_index hr
  have hP : IsPGroup 2 ↥((B₁ ⊔ B₂).subgroupOf (C ⊔ D)) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have hdvd : 2 ^ a ∣ Nat.card ↥(C.subgroupOf (C ⊔ D)) * (C.subgroupOf (C ⊔ D)).index := by
    rw [Subgroup.card_mul_index, ← ha]
    exact Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime (2 ^ a) (C.subgroupOf (C ⊔ D)).index :=
    Nat.Coprime.pow_left a ((Nat.prime_two.coprime_iff_not_dvd).2 hodd)
  have h1 := hcop.dvd_of_dvd_mul_right hdvd
  rw [← ha, CFSG.Timmesfeld.card_subgroupOf_of_le le_sup_left,
    CFSG.Timmesfeld.card_subgroupOf_of_le hle, hR.card_eq hC.1.1 hA] at h1
  have := Nat.le_of_dvd (by omega) h1
  nlinarith

theorem exists_mem_leviSet_mem_lambdaSet {P : Subgroup G} (hP : P ∈ lambdaStar R A A₀) :
    ∃ B ∈ leviSet R A A₀, P ∈ lambdaSet R B := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨c, hcA, -, hPc⟩ := exists_conjSet_of_mem_lambdaStar h hA h8 hA₀ hΔ hAΔ hP
  have hΔc : IsWeakTI R (conjSet Δ c) := Sec5.isWeakTI_conjSet hR hΔ c
  have hAΔc : A ∈ conjSet Δ c := hcA ▸ conjSub_mem_conjSet hAΔ c
  obtain ⟨C₁, hC₁, F₁, hF₁, hF₁', hFC₁⟩ := exists_special_lambdaStar h hA h8 hA₀ hΔc hAΔc
  obtain ⟨-, D₁, hD₁, hCD₁, hFD₁⟩ := exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hC₁ hF₁' hFC₁
  have hPle := le_sup_commutator_of_mem h hA h8 hA₀ hΔc hAΔc hC₁ hF₁ hF₁' hFC₁ hPc hP
  have hF₁ψ : F₁ ∈ psiSet R C₁ := ⟨hΔc.1 hF₁, hFC₁.symm⟩
  obtain ⟨p, hp, hp1⟩ := hR.exists_ne_one hP.1.1.1
  have hpN : p ∈ F₁ ⊔ ⁅C₁, F₁⁆ := by
    rw [Subgroup.commutator_comm]
    exact hPle hp
  obtain ⟨x, hx, hpx⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hD₁.1.1 hC₁.1.1 hCD₁.symm
    hFD₁ hF₁ψ hpN hp1
  have hPx : P = conjSub F₁ x :=
    Sec3.eq_of_mem_of_mem hR hiso hP.1.1.1 (hR.conjSub_mem (hΔc.1 hF₁) x) hp hpx hp1
  have hxV : x ∈ levi R A A₀ := sup_le (le_gen hD₁) (le_gen hC₁) hx
  refine ⟨conjSub D₁ x, Levi.conjSub_mem_leviSet_of_mem_levi hR hD₁ hxV, ?_⟩
  rw [hPx]
  exact conjSub_mem_lambdaSet hR hFD₁ x

end Faithful

end CaseB

end CFSG.Timmesfeld.ARS
