module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutD
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

section Pair

variable {τ : Tag} {K : Type} [Field K]


theorem pinnedX_mul_injective₂ {α₁ α₂ : Fin τ.rank → ℤ} (h₁ : IsRoot τ α₁ ∧ 0 < height α₁)
    (h₂ : IsRoot τ α₂ ∧ 0 < height α₂) (h12 : α₁ ≠ α₂) {a b a' b' : K}
    (h : pinnedX τ K α₁ a * pinnedX τ K α₂ b = pinnedX τ K α₁ a' * pinnedX τ K α₂ b') :
    a = a' ∧ b = b' := by
  classical
  have hL := pinnedX_list_prod_injective (R := K) [α₁, α₂] (by simp [h12])
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl
      exacts [h₁, h₂])
    (fun α => if α = α₁ then a else b) (fun α => if α = α₁ then a' else b')
    (by simpa [Ne.symm h12] using h)
  have e1 := hL α₁ (by simp)
  have e2 := hL α₂ (by simp)
  simp only [Ne.symm h12, ite_true, ite_false] at e1 e2
  exact ⟨by simpa using e1, e2⟩

theorem pinnedX_mul_injective₃ {α₁ α₂ α₃ : Fin τ.rank → ℤ} (h₁ : IsRoot τ α₁ ∧ 0 < height α₁)
    (h₂ : IsRoot τ α₂ ∧ 0 < height α₂) (h₃ : IsRoot τ α₃ ∧ 0 < height α₃) (h12 : α₁ ≠ α₂)
    (h13 : α₁ ≠ α₃) (h23 : α₂ ≠ α₃) {a b c a' b' c' : K}
    (h : pinnedX τ K α₁ a * pinnedX τ K α₂ b * pinnedX τ K α₃ c =
      pinnedX τ K α₁ a' * pinnedX τ K α₂ b' * pinnedX τ K α₃ c') :
    a = a' ∧ b = b' ∧ c = c' := by
  classical
  have hL := pinnedX_list_prod_injective (R := K) [α₁, α₂, α₃] (by simp [h12, h13, h23])
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl | rfl
      exacts [h₁, h₂, h₃])
    (fun α => if α = α₁ then a else if α = α₂ then b else c)
    (fun α => if α = α₁ then a' else if α = α₂ then b' else c')
    (by simpa [Ne.symm h12, Ne.symm h13, Ne.symm h23, mul_assoc] using h)
  have e1 := hL α₁ (by simp)
  have e2 := hL α₂ (by simp)
  have e3 := hL α₃ (by simp)
  simp only [Ne.symm h12, Ne.symm h13, Ne.symm h23, ite_true, ite_false] at e1 e2 e3
  exact ⟨by simpa using e1, by simpa using e2, e3⟩

theorem pinnedX_mul_injective₄ {α₁ α₂ α₃ α₄ : Fin τ.rank → ℤ}
    (h₁ : IsRoot τ α₁ ∧ 0 < height α₁) (h₂ : IsRoot τ α₂ ∧ 0 < height α₂)
    (h₃ : IsRoot τ α₃ ∧ 0 < height α₃) (h₄ : IsRoot τ α₄ ∧ 0 < height α₄) (h12 : α₁ ≠ α₂)
    (h13 : α₁ ≠ α₃) (h14 : α₁ ≠ α₄) (h23 : α₂ ≠ α₃) (h24 : α₂ ≠ α₄) (h34 : α₃ ≠ α₄)
    {a b c d a' b' c' d' : K}
    (h : pinnedX τ K α₁ a * pinnedX τ K α₂ b * pinnedX τ K α₃ c * pinnedX τ K α₄ d =
      pinnedX τ K α₁ a' * pinnedX τ K α₂ b' * pinnedX τ K α₃ c' * pinnedX τ K α₄ d') :
    a = a' := by
  classical
  have hL := pinnedX_list_prod_injective (R := K) [α₁, α₂, α₃, α₄]
    (by simp [h12, h13, h14, h23, h24, h34])
    (by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl | rfl | rfl
      exacts [h₁, h₂, h₃, h₄])
    (fun α => if α = α₁ then a else if α = α₂ then b else if α = α₃ then c else d)
    (fun α => if α = α₁ then a' else if α = α₂ then b' else if α = α₃ then c' else d')
    (by simpa [Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h23, Ne.symm h24, Ne.symm h34,
      mul_assoc] using h)
  simpa using hL α₁ (by simp)

theorem height_pos_of_pinnedX_mul_eq {β₁ β₂ γ₁ γ₂ : Fin τ.rank → ℤ} (hβ₁ : IsRoot τ β₁)
    (hβ₂ : IsRoot τ β₂) (hγ₁ : IsRoot τ γ₁ ∧ 0 < height γ₁) (hγ₂ : IsRoot τ γ₂ ∧ 0 < height γ₂)
    (hγ : γ₁ ≠ γ₂) {p₁ p₂ r₁ r₂ : K} (hp₁ : p₁ ≠ 0) (hr₁ : r₁ ≠ 0)
    (h : pinnedX τ K β₁ p₁ * pinnedX τ K β₂ p₂ = pinnedX τ K γ₁ r₁ * pinnedX τ K γ₂ r₂) :
    0 < height β₁ := by
  have hB : ∀ {α : Fin τ.rank → ℤ}, IsRoot τ α ∧ 0 < height α → ∀ c : K,
      pinnedX τ K α c ∈ borelGroup τ K := fun hα c =>
    Subgroup.mem_sup_right (pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α}) hα c)
  have hN : ∀ {α : Fin τ.rank → ℤ}, IsRoot τ α → height α < 0 → ∀ c : K,
      pinnedX τ K α c ∈ negUnipotent τ K := fun hα hn c =>
    pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ height α < 0}) ⟨hα, hn⟩ c
  by_contra hn
  have hn' : height β₁ < 0 := lt_of_le_of_ne (not_lt.1 hn) hβ₁.height_ne_zero
  rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg hβ₂ with h2 | h2
  · have e : pinnedX τ K β₁ p₁ =
        pinnedX τ K γ₁ r₁ * pinnedX τ K γ₂ r₂ * (pinnedX τ K β₂ p₂)⁻¹ := by
      rw [← h]
      group
    have hBβ : pinnedX τ K β₁ p₁ ∈ borelGroup τ K := by
      rw [e]
      exact mul_mem (mul_mem (hB hγ₁ _) (hB hγ₂ _)) (inv_mem (hB ⟨hβ₂, h2⟩ _))
    have h0 := Subgroup.mem_inf.2 ⟨hBβ, hN hβ₁ hn' p₁⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at h0
    exact hp₁ (pinnedX_injective τ K _ (h0.trans (pinnedX_zero τ K _).symm))
  · have hNβ : pinnedX τ K β₁ p₁ * pinnedX τ K β₂ p₂ ∈ negUnipotent τ K :=
      mul_mem (hN hβ₁ hn' _) (hN hβ₂ h2 _)
    have hBβ : pinnedX τ K β₁ p₁ * pinnedX τ K β₂ p₂ ∈ borelGroup τ K := by
      rw [h]
      exact mul_mem (hB hγ₁ _) (hB hγ₂ _)
    have h0 := Subgroup.mem_inf.2 ⟨hBβ, hNβ⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, h] at h0
    have := pinnedX_mul_injective₂ hγ₁ hγ₂ hγ (a := r₁) (b := r₂) (a' := (0 : K)) (b' := 0)
      (by rw [pinnedX_zero, pinnedX_zero, mul_one]; exact h0)
    exact hr₁ this.1

theorem pinnedX_mul_eq_pinnedX_mul {β₁ β₂ γ₁ γ₂ : Fin τ.rank → ℤ} (hβ₁ : IsRoot τ β₁)
    (hβ₂ : IsRoot τ β₂) (hγ₁ : IsRoot τ γ₁ ∧ 0 < height γ₁) (hγ₂ : IsRoot τ γ₂ ∧ 0 < height γ₂)
    (hβ : β₁ ≠ β₂) (hγ : γ₁ ≠ γ₂)
    (hcβ : ∀ s t : K, pinnedX τ K β₁ s * pinnedX τ K β₂ t = pinnedX τ K β₂ t * pinnedX τ K β₁ s)
    (hcγ : ∀ s t : K, pinnedX τ K γ₁ s * pinnedX τ K γ₂ t = pinnedX τ K γ₂ t * pinnedX τ K γ₁ s)
    {p₁ p₂ r₁ r₂ : K} (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) (hr₁ : r₁ ≠ 0)
    (h : pinnedX τ K β₁ p₁ * pinnedX τ K β₂ p₂ = pinnedX τ K γ₁ r₁ * pinnedX τ K γ₂ r₂) :
    (β₁ = γ₁ ∧ β₂ = γ₂ ∧ p₁ = r₁ ∧ p₂ = r₂) ∨ (β₁ = γ₂ ∧ β₂ = γ₁ ∧ p₁ = r₂ ∧ p₂ = r₁) := by
  have hpos₁ := height_pos_of_pinnedX_mul_eq hβ₁ hβ₂ hγ₁ hγ₂ hγ hp₁ hr₁ h
  have h' : pinnedX τ K β₂ p₂ * pinnedX τ K β₁ p₁ = pinnedX τ K γ₁ r₁ * pinnedX τ K γ₂ r₂ := by
    rw [← hcβ, h]
  have hpos₂ := height_pos_of_pinnedX_mul_eq hβ₂ hβ₁ hγ₁ hγ₂ hγ hp₂ hr₁ h'
  have hb₁ : IsRoot τ β₁ ∧ 0 < height β₁ := ⟨hβ₁, hpos₁⟩
  have hb₂ : IsRoot τ β₂ ∧ 0 < height β₂ := ⟨hβ₂, hpos₂⟩
  have hγ' : pinnedX τ K γ₂ r₂ * pinnedX τ K γ₁ r₁ = pinnedX τ K γ₁ r₁ * pinnedX τ K γ₂ r₂ :=
    (hcγ r₁ r₂).symm
  by_cases h11 : β₁ = γ₁
  · subst h11
    by_cases h22 : β₂ = γ₂
    · subst h22
      exact Or.inl ⟨rfl, rfl, pinnedX_mul_injective₂ hb₁ hb₂ hβ h⟩
    · exfalso
      have e := pinnedX_mul_injective₃ hb₁ hγ₂ hb₂ hγ hβ (Ne.symm h22) (a := p₁) (b := 0) (c := p₂)
        (a' := r₁) (b' := r₂) (c' := 0) (by
          rw [pinnedX_zero, pinnedX_zero, mul_one, mul_one]
          exact h)
      exact hp₂ e.2.2
  · by_cases h12 : β₁ = γ₂
    · subst h12
      by_cases h21 : β₂ = γ₁
      · subst h21
        refine Or.inr ⟨rfl, rfl, ?_⟩
        have e := pinnedX_mul_injective₂ hb₂ hb₁ (Ne.symm hβ) (a := p₂) (b := p₁) (a' := r₁)
          (b' := r₂) (by rw [← hcβ]; exact h)
        exact ⟨e.2, e.1⟩
      · exfalso
        have e := pinnedX_mul_injective₃ hb₁ hγ₁ hb₂ (Ne.symm hγ) hβ (Ne.symm h21) (a := p₁) (b := 0)
          (c := p₂) (a' := r₂) (b' := r₁) (c' := 0) (by
            rw [pinnedX_zero, pinnedX_zero, mul_one, mul_one, hγ']
            exact h)
        exact hp₂ e.2.2
    · by_cases h21 : β₂ = γ₁
      · subst h21
        exfalso
        have e := pinnedX_mul_injective₃ hb₂ hγ₂ hb₁ hγ (Ne.symm hβ) (Ne.symm h12) (a := p₂)
          (b := 0) (c := p₁) (a' := r₁) (b' := r₂) (c' := 0) (by
            rw [pinnedX_zero, pinnedX_zero, mul_one, mul_one]
            exact h')
        exact hp₁ e.2.2
      · by_cases h22 : β₂ = γ₂
        · subst h22
          exfalso
          have e := pinnedX_mul_injective₃ hb₂ hγ₁ hb₁ (Ne.symm hγ) (Ne.symm hβ) (Ne.symm h11)
            (a := p₂) (b := 0) (c := p₁) (a' := r₂) (b' := r₁) (c' := 0) (by
              rw [pinnedX_zero, pinnedX_zero, mul_one, mul_one, hγ']
              exact h')
          exact hp₁ e.2.2
        · exfalso
          have e := pinnedX_mul_injective₄ hb₁ hb₂ hγ₁ hγ₂ hβ h11 h12 h21 h22 hγ
            (a := p₁) (b := p₂) (c := 0) (d := 0) (a' := 0) (b' := 0) (c' := r₁) (d' := r₂) (by
              simp only [pinnedX_zero, mul_one, one_mul]
              exact h)
          exact hp₁ e

end Pair

section Fixed

variable {τ : Tag} {K : Type} [Field K]


theorem mem_rootSpan_of_forall_mem_centralizer_list (L : List (Fin τ.rank → Kˣ)) :
    ∀ {S : Set (Fin τ.rank → ℤ)}, (∀ α ∈ S, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot τ (m • α + n • β) →
        m • α + n • β ∈ S) →
      ∀ {x : ModGL τ K}, x ∈ rootSpan τ K S →
        (∀ b ∈ L, x ∈ centralizer ({rootDiagUnit τ b} : Set (ModGL τ K))) →
        x ∈ rootSpan τ K {α | α ∈ S ∧ ∀ b ∈ L, rootChar b α = 1} := by
  induction L with
  | nil =>
    intro S _ _ x hx _
    refine rootSpan_mono ?_ hx
    intro α hα
    exact ⟨hα, fun b hb => absurd hb List.not_mem_nil⟩
  | cons b L ih =>
    intro S hSpos hScl x hx hcent
    have h1 := EPilot.mem_rootSpan_inter_of_mem_centralizer hSpos hScl hx
      (hcent b List.mem_cons_self)
    have h2 := ih (fun α hα => hSpos α hα.2) (EPilot.rootCharKernel_inter_closed hScl) h1
      fun b' hb' => hcent b' (List.mem_cons_of_mem _ hb')
    refine rootSpan_mono ?_ h2
    rintro α ⟨⟨⟨-, hαb⟩, hαS⟩, hαL⟩
    refine ⟨hαS, fun b' hb' => ?_⟩
    rcases List.mem_cons.1 hb' with rfl | h
    · exact hαb
    · exact hαL b' h

theorem bruhat_factors_of_conj_list {w : WeylGroup τ} {h u v : ModGL τ K}
    (hh : h ∈ torusGroup τ K) (hu : u ∈ posUnipotent τ K) (hv : v ∈ rootSpan τ K (inversionSet w))
    (L : List ((Fin τ.rank → Kˣ) × (Fin τ.rank → Kˣ)))
    (hL : ∀ p ∈ L, rootDiagUnit τ p.1 ∈ torusGroup τ K ∧ rootDiagUnit τ p.2 ∈ torusGroup τ K ∧
      h * u * canonicalRep (coxeterSystem τ) K w * v * rootDiagUnit τ p.2 =
        rootDiagUnit τ p.1 * (h * u * canonicalRep (coxeterSystem τ) K w * v)) :
    u ∈ rootSpan τ K {α | (IsRoot τ α ∧ 0 < height α) ∧ ∀ b ∈ L.map Prod.fst, rootChar b α = 1} ∧
      v ∈ rootSpan τ K {α | α ∈ inversionSet w ∧ ∀ b ∈ L.map Prod.snd, rootChar b α = 1} ∧
      ∀ p ∈ L, rootDiagUnit τ p.1 = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ p.2 *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  have hcomm : ∀ {t x : ModGL τ K}, t * x * t⁻¹ = x →
      x ∈ centralizer ({t} : Set (ModGL τ K)) := by
    intro t x htx
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mul_inv_eq_iff_eq_mul.1 htx
  have hposcl : ∀ α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α},
      ∀ β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}, ∀ m n : ℕ, 1 ≤ m →
        1 ≤ n → IsRoot τ (m • α + n • β) →
          m • α + n • β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} := by
    intro α hα β hβ m n hm hn hmn
    refine ⟨hmn, ?_⟩
    rw [height_nsmul_add_nsmul]
    have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith [hα.2, hβ.2]
  have key := fun p (hp : p ∈ L) =>
    E6Pilot.twisted_torus_bruhat hh hu hv (hL p hp).1 (hL p hp).2.1 (hL p hp).2.2
  refine ⟨mem_rootSpan_of_forall_mem_centralizer_list _ (fun α hα => hα) hposcl hu
    fun b hb => ?_, mem_rootSpan_of_forall_mem_centralizer_list _
      (fun α hα => inversionSet_pos hα) (inversionSet_closed w) hv fun b hb => ?_,
    fun p hp => (key p hp).2.2⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    exact hcomm (key p hp).1
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    exact hcomm (key p hp).2.1

end Fixed

section PairDiag

variable {τ : Tag} {K : Type} [Field K]

@[expose] def pairDiag (j j' : Fin τ.rank) (μ ν : Kˣ) : Fin τ.rank → Kˣ :=
  fun k => μ ^ τ.cartan j k * ν ^ τ.cartan j' k

theorem rootChar_pairDiag (j j' : Fin τ.rank) (μ ν : Kˣ) (α : Fin τ.rank → ℤ) :
    rootChar (pairDiag j j' μ ν) α = μ ^ coPair τ j α * ν ^ coPair τ j' α := by
  have h : rootChar (pairDiag j j' μ ν) α =
      rootChar (fun k => μ ^ τ.cartan j k) α * rootChar (fun k => ν ^ τ.cartan j' k) α := by
    simp only [rootChar, pairDiag, mul_zpow, Finset.prod_mul_distrib]
  rw [h, EPilot.rootChar_cartan_row, EPilot.rootChar_cartan_row]


theorem rootDiagUnit_pairDiag (j j' : Fin τ.rank) (μ ν : Kˣ) :
    rootDiagUnit τ (pairDiag j j' μ ν) = torusElt τ K j μ * torusElt τ K j' ν := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  rfl

theorem rootDiagUnit_pairDiag_mem_torusGroup (j j' : Fin τ.rank) (μ ν : Kˣ) :
    rootDiagUnit τ (pairDiag j j' μ ν) ∈ torusGroup τ K := by
  rw [rootDiagUnit_pairDiag]
  exact mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)

theorem rootDiagUnit_pairDiag_mem_subsystemGroup {A : Set (Fin τ.rank)} {j j' : Fin τ.rank}
    (hj : j ∈ A) (hj' : j' ∈ A) (μ ν : Kˣ) :
    rootDiagUnit τ (pairDiag j j' μ ν) ∈ subsystemGroup τ K A := by
  rw [rootDiagUnit_pairDiag]
  exact mul_mem (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hj μ))
    (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hj' ν))


theorem twistHom_rootDiagUnit_pairDiag {t : TwistTag} (σ : K →+* K) {j : Fin t.tag.rank}
    (hj : t.perm (t.perm j) = j) {μ ν : Kˣ} (hμ : Units.map σ.toMonoidHom μ = ν)
    (hν : Units.map σ.toMonoidHom ν = μ) :
    twistHom t K σ (rootDiagUnit t.tag (pairDiag j (t.perm j) μ ν)) =
      rootDiagUnit t.tag (pairDiag j (t.perm j) μ ν) := by
  have e : ∀ (i i' : Fin t.tag.rank) (a b : Kˣ),
      torusElt t.tag K i a * torusElt t.tag K i' b = torusElt t.tag K i' b * torusElt t.tag K i a := by
    intro i i' a b
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      mul_comm]
  rw [rootDiagUnit_pairDiag, map_mul, twistHom_torusElt, twistHom_torusElt, hj, hμ, hν, e]

end PairDiag

section Kernel

local instance twistedE6PilotLeviCentralizerNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

theorem coPair_pair_bounds : ∀ α ∈ rootFinset .E6,
    |coPair .E6 0 α + coPair .E6 5 α| ≤ 2 ∧ |coPair .E6 0 α - coPair .E6 5 α| ≤ 2 ∧
      |coPair .E6 2 α + coPair .E6 4 α| ≤ 2 ∧ |coPair .E6 2 α - coPair .E6 4 α| ≤ 2 := by
  decide +kernel

theorem not_forall_coPair_D4_eq_zero : ∀ α ∈ rootFinset .E6,
    ¬ (coPair .E6 1 α = 0 ∧ coPair .E6 2 α = 0 ∧ coPair .E6 3 α = 0 ∧ coPair .E6 4 α = 0) := by
  decide +kernel

variable {K : Type} [Field K] [CharP K 2]

theorem eq_zero_of_pair_char {μ ζ : Kˣ} (hμ : μ ≠ 1) (hζ : ζ ≠ 1) {c c' : ℤ} (hp : |c + c'| ≤ 2)
    (hm : |c - c'| ≤ 2) (h1 : μ ^ c * μ ^ c' = 1) (h2 : ζ ^ c * ζ⁻¹ ^ c' = 1) :
    c = 0 ∧ c' = 0 := by
  rw [← zpow_add] at h1
  rw [inv_zpow', ← zpow_add, ← sub_eq_add_neg] at h2
  have e1 := EPilot.eq_zero_of_zpow_eq_one_of_charTwo hμ hp h1
  have e2 := EPilot.eq_zero_of_zpow_eq_one_of_charTwo hζ hm h2
  omega


theorem eq_highRoot_or_neg_of_rootChar_X {μ ζ : Kˣ} (hμ : μ ≠ 1) (hζ : ζ ≠ 1)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (h1 : rootChar (pairDiag 0 5 μ μ) α = 1) (h2 : rootChar (pairDiag 0 5 ζ ζ⁻¹) α = 1)
    (h3 : rootChar (pairDiag 2 4 μ μ) α = 1) (h4 : rootChar (pairDiag 2 4 ζ ζ⁻¹) α = 1)
    (h5 : rootChar (fun k => μ ^ Tag.E6.cartan 3 k) α = 1) :
    α = highRoot .E6 ∨ α = -highRoot .E6 := by
  obtain ⟨b1, b2, b3, b4⟩ := coPair_pair_bounds α (mem_rootFinset.2 hα)
  rw [rootChar_pairDiag] at h1 h2 h3 h4
  rw [EPilot.rootChar_cartan_row] at h5
  obtain ⟨e0, e5⟩ := eq_zero_of_pair_char hμ hζ b1 b2 h1 h2
  obtain ⟨e2, e4⟩ := eq_zero_of_pair_char hμ hζ b3 b4 h3 h4
  have e3 := EPilot.eq_zero_of_zpow_eq_one_of_charTwo hμ
    (EPilot.abs_coPair_le_two (Or.inl rfl) hα 3) h5
  refine EPilot.eq_highRoot_or_neg_of_coPair_eq_zero (Or.inl rfl) hα fun j hj => ?_
  fin_cases j
  · exact e0
  · exact absurd rfl hj
  · exact e2
  · exact e3
  · exact e4
  · exact e5

theorem false_of_rootChar_Y {μ ζ : Kˣ} (hμ : μ ≠ 1) (hζ : ζ ≠ 1)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (h1 : rootChar (fun k => μ ^ Tag.E6.cartan 1 k) α = 1)
    (h2 : rootChar (fun k => μ ^ Tag.E6.cartan 3 k) α = 1)
    (h3 : rootChar (pairDiag 2 4 μ μ) α = 1) (h4 : rootChar (pairDiag 2 4 ζ ζ⁻¹) α = 1) :
    False := by
  obtain ⟨-, -, b3, b4⟩ := coPair_pair_bounds α (mem_rootFinset.2 hα)
  rw [rootChar_pairDiag] at h3 h4
  rw [EPilot.rootChar_cartan_row] at h1 h2
  obtain ⟨e2, e4⟩ := eq_zero_of_pair_char hμ hζ b3 b4 h3 h4
  have e1 := EPilot.eq_zero_of_zpow_eq_one_of_charTwo hμ
    (EPilot.abs_coPair_le_two (Or.inl rfl) hα 1) h1
  have e3 := EPilot.eq_zero_of_zpow_eq_one_of_charTwo hμ
    (EPilot.abs_coPair_le_two (Or.inl rfl) hα 3) h2
  exact not_forall_coPair_D4_eq_zero α (mem_rootFinset.2 hα) ⟨e1, e2, e3, e4⟩

end Kernel

section Members

variable {K : Type} [Field K]


theorem torusElt_mem_inf {t : TwistTag} {σ : K →+* K} {A : Set (Fin t.tag.rank)}
    {j : Fin t.tag.rank} (hjA : j ∈ A) (hj : t.perm j = j) {μ : Kˣ}
    (hμ : Units.map σ.toMonoidHom μ = μ) :
    torusElt t.tag K j μ ∈ subsystemGroup t.tag K A ⊓ twistedFixedGroup t K σ :=
  ⟨subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hjA μ),
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨torusElt_mem_adjointGroup j μ, by rw [twistHom_torusElt, hj, hμ]⟩⟩

theorem rootDiagUnit_pairDiag_mem_inf {t : TwistTag} {σ : K →+* K} {A : Set (Fin t.tag.rank)}
    {j : Fin t.tag.rank} (hjA : j ∈ A) (hρjA : t.perm j ∈ A) (hj : t.perm (t.perm j) = j)
    {μ ν : Kˣ} (hμ : Units.map σ.toMonoidHom μ = ν) (hν : Units.map σ.toMonoidHom ν = μ) :
    rootDiagUnit t.tag (pairDiag j (t.perm j) μ ν) ∈
      subsystemGroup t.tag K A ⊓ twistedFixedGroup t K σ := by
  refine ⟨rootDiagUnit_pairDiag_mem_subsystemGroup hjA hρjA μ ν,
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨?_, twistHom_rootDiagUnit_pairDiag σ hj hμ hν⟩⟩
  rw [rootDiagUnit_pairDiag]
  exact mul_mem (torusElt_mem_adjointGroup _ _) (torusElt_mem_adjointGroup _ _)


theorem pinnedX_single_mem_inf {t : TwistTag} {σ : K →+* K} (h2 : (2 : K) = 0)
    {A : Set (Fin t.tag.rank)} {j : Fin t.tag.rank} (hjA : j ∈ A) (hj : t.perm j = j) {c : K}
    (hc : σ c = c) :
    pinnedX t.tag K (Pi.single j 1) c ∈ subsystemGroup t.tag K A ⊓ twistedFixedGroup t K σ := by
  refine ⟨by rw [pinnedX_single]; exact xUnit_mem_subsystemGroup hjA c,
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨pinnedX_mem_adjointGroup _ _, ?_⟩⟩
  rw [twistHom_pinnedX_eq_of_charTwo h2 σ (isRoot_single _ j), permLattice_single, hj, hc]

theorem twistedE6PairX_single_mem_subsystemGroup (σ : K →+* K) {A : Set (Fin TwistTag.E6.tag.rank)}
    {j : Fin TwistTag.E6.tag.rank} (hjA : j ∈ A) (hρjA : TwistTag.E6.perm j ∈ A) (c : K) :
    twistedE6PairX σ (Pi.single j 1) c ∈ subsystemGroup TwistTag.E6.tag K A := by
  rw [twistedE6PairX, permLattice_single, pinnedX_single, pinnedX_single]
  exact mul_mem (xUnit_mem_subsystemGroup hjA c) (xUnit_mem_subsystemGroup hρjA _)

theorem twistedE6PairX_single_mem_inf [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {A : Set (Fin TwistTag.E6.tag.rank)} {j : Fin TwistTag.E6.tag.rank} (hjA : j ∈ A)
    (hρjA : TwistTag.E6.perm j ∈ A) (c : K) :
    twistedE6PairX σ (Pi.single j 1) c ∈
      subsystemGroup TwistTag.E6.tag K A ⊓ twistedFixedGroup TwistTag.E6 K σ :=
  ⟨twistedE6PairX_single_mem_subsystemGroup σ hjA hρjA c,
    twistedE6PairX_mem_twistedFixedGroup hσσ (isRoot_single _ j) c⟩

end Members

end CFSG.SeitzReduction.TwistedE6Pilot
