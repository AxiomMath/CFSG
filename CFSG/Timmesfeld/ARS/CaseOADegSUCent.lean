module

public import CFSG.Timmesfeld.ARS.CaseOADegLevi
public import CFSG.Timmesfeld.ARS.CaseOADegSUAlign
public import CFSG.Timmesfeld.ARS.CaseMSpLevi

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.Pres

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOADeg

abbrev j0 : Fin (4 / 2) := ⟨0, by decide⟩

abbrev j1 : Fin (4 / 2) := ⟨1, by decide⟩

section Vectors

variable {F : Type*} [Field F] (σ : F ≃+* F)

theorem uForm_of_low_eq_zero₄ {v w : Fin 4 → F} (hv : ∀ x : Fin 4, x.val < 2 → v x = 0)
    (hw : ∀ x : Fin 4, x.val < 2 → w x = 0) : uForm σ v w = 0 := by
  rw [uForm_eq]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x.val < 2
  · rw [hv x hx, map_zero, zero_mul]
  · rw [hw (Fin.rev x) (by rw [Fin.val_rev]; omega), mul_zero]

theorem uForm_of_high_eq_zero₄ {v w : Fin 4 → F} (hv : ∀ x : Fin 4, 2 ≤ x.val → v x = 0)
    (hw : ∀ x : Fin 4, 2 ≤ x.val → w x = 0) : uForm σ v w = 0 := by
  rw [uForm_eq]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : 2 ≤ x.val
  · rw [hv x hx, map_zero, zero_mul]
  · rw [hw (Fin.rev x) (by rw [Fin.val_rev]; omega), mul_zero]

end Vectors

theorem apply_eq_zero_of_commuting {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)
    {c₀ : F} (hc₀ : c₀ ≠ 0) (hc₀' : c₀ + σ c₀ = 0) {H : Type*} [Group H]
    {Φ : SU σ 4 →* H} (hker : Φ.ker ≤ Subgroup.center _) {v : Fin 4 → F}
    {X Y : Subgroup (SU σ 4)} (hX : IsUTransGroup σ v X) (hv : v ≠ 0) (hvv : uForm σ v v = 0)
    {y : Fin 4} (hy : y ≠ Fin.rev y) (hY : IsUTransGroup σ (Pi.single y 1) Y)
    (hc : Commuting (X.map Φ) (Y.map Φ)) : v (Fin.rev y) = 0 := by
  rcases hX.uForm_eq_zero_of_center hσ hc₀ hc₀' hY hv hvv (uForm_single_self hy)
      (CaseMSU.commutator_mem_center hker hc) with h | ⟨l, hl⟩
  · rw [uForm_single_right, map_eq_zero] at h
    exact h
  · have h1 := congrFun hl y
    have h2 := congrFun hl (Fin.rev y)
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul, ite_eq_right hy.symm] at h1 h2
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at h1
    exact (mul_eq_zero.1 h2.symm).resolve_left hl0

namespace DegOA

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)} (hD : DegOA R A A₀ Δ₁ Δ₂)
include hD

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem conjSub_mem_deltaSet_su (hF : Nat.card F = (p ^ f) ^ 2)
    {Φ : SU (unitaryInvolution F p f) 4 →* G} (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g, X = (conjSub (Unitary.rootGroup
      (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1))
        g).map Φ)
    {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (W : (Fin 4 → F) → Prop)
    (hW : ∀ (v : Fin 4 → F) (X' : Subgroup (SU (unitaryInvolution F p f) 4)),
      IsUTransGroup (unitaryInvolution F p f) v X' → v ≠ 0 →
        uForm (unitaryInvolution F p f) v v = 0 → X'.map Φ ∈ deltaSet R A A₀ B → W v)
    (hWW : ∀ v w, W v → W w → uForm (unitaryInvolution F p f) v w = 0)
    {s : SU (unitaryInvolution F p f) 4} (hs : ∀ v, W v → W (suMat _ 4 s *ᵥ v)) :
    ∀ X ∈ deltaSet R A A₀ B, conjSub X (Φ s) ∈ deltaSet R A A₀ B := by
  have hσ : ∀ c, unitaryInvolution F p f (unitaryInvolution F p f c) = c :=
    unitaryInvolution_involutive hF
  have hR := hD.hyp.root
  have hzV : Φ s ∈ gen Δ₁ := hrange ▸ ⟨s, rfl⟩
  have hzl : Φ s ∈ levi R A A₀ := hD.gen₁_le_levi hzV
  have hz₂ : ∀ {Y : Subgroup G}, Y ∈ Δ₂ → ∀ y ∈ Y, Commute (Φ s) y := fun hY y hy =>
    hD.commuting_gen _ hzV y (le_gen hY hy)
  intro X hX
  rcases hD.mem_or_mem hX.1 with hX₁ | hX₂
  · obtain ⟨g, hXg⟩ := (hΔ X).1 hX₁
    obtain ⟨v, hv0, hvv, hvT⟩ := exists_isUTransGroup_of_mem₄ hF g
    have hWv : W v := hW v _ hvT hv0 hvv (hXg ▸ hX)
    have hconj : conjSub X (Φ s) = (conjSub (conjSub (Unitary.rootGroup
        (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1))
          g) s).map Φ := by
      rw [hXg]
      exact Transvection.ModelRank.conjSub_map Φ _ s
    have hmem : conjSub X (Φ s) ∈ leviSet R A A₀ :=
      Levi.conjSub_mem_leviSet_of_mem_levi hR hX.1 hzl
    refine hD.sec12.mem_deltaSet_of_forall_commuting hB hmem fun Y hY => ?_
    rcases hD.mem_or_mem hY.1 with hY₁ | hY₂
    · obtain ⟨g', hYg⟩ := (hΔ Y).1 hY₁
      obtain ⟨w, hw0, hww, hwT⟩ := exists_isUTransGroup_of_mem₄ hF g'
      rw [hconj, hYg]
      exact CaseMSU.commuting_map Φ ((hvT.conjSub s).commuting hσ hwT
        (hWW _ _ (hs v hWv) (hW w _ hwT hw0 hww (hYg ▸ hY))))
    · have hle : conjSub X (Φ s) ≤ gen Δ₁ := by
        rw [hconj, ← hrange]
        exact Subgroup.map_le_range Φ _
      exact hD.commuting_gen.mono hle (le_gen hY₂)
  · rw [conjSub_of_forall_commute (hz₂ hX₂)]
    exact hX

theorem commute_of_preserves_su {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : Sec12.IsSubframe R A A₀ E C P Q) (h0 : P 0 ∈ Δ₂ ∧ Q 0 ∈ Δ₂)
    (hF : Nat.card F = (p ^ f) ^ 2) {Φ : SU (unitaryInvolution F p f) 4 →* G}
    (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g, X = (conjSub (Unitary.rootGroup
      (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1))
        g).map Φ)
    (WE WC : (Fin 4 → F) → Prop)
    (hWE : ∀ (v : Fin 4 → F) (X' : Subgroup (SU (unitaryInvolution F p f) 4)),
      IsUTransGroup (unitaryInvolution F p f) v X' → v ≠ 0 →
        uForm (unitaryInvolution F p f) v v = 0 → X'.map Φ ∈ deltaSet R A A₀ E → WE v)
    (hWC : ∀ (v : Fin 4 → F) (X' : Subgroup (SU (unitaryInvolution F p f) 4)),
      IsUTransGroup (unitaryInvolution F p f) v X' → v ≠ 0 →
        uForm (unitaryInvolution F p f) v v = 0 → X'.map Φ ∈ deltaSet R A A₀ C → WC v)
    (hWWE : ∀ v w, WE v → WE w → uForm (unitaryInvolution F p f) v w = 0)
    (hWWC : ∀ v w, WC v → WC w → uForm (unitaryInvolution F p f) v w = 0)
    {s : SU (unitaryInvolution F p f) 4} (hsE : ∀ v, WE v → WE (suMat _ 4 s *ᵥ v))
    (hsC : ∀ v, WC v → WC (suMat _ 4 s *ᵥ v)) (hs2 : s * s = 1) :
    (∀ e ∈ E, Commute (Φ s) e) ∧ ∀ c ∈ C, Commute (Φ s) c := by
  have hzV : Φ s ∈ gen Δ₁ := hrange ▸ ⟨s, rfl⟩
  have hzl : Φ s ∈ levi R A A₀ := hD.gen₁_le_levi hzV
  have hz2' : Φ s * Φ s = 1 := by rw [← map_mul, hs2, map_one]
  have hz₂ : ∀ {Y : Subgroup G}, Y ∈ Δ₂ → ∀ y ∈ Y, Commute (Φ s) y := fun hY y hy =>
    hD.commuting_gen _ hzV y (le_gen hY hy)
  have hEz := hD.sec12.conjSub_eq_of_deltaSet_subset hfr.memE hzl hz2'
    (hD.conjSub_mem_deltaSet_su hF hrange hΔ hfr.memE WE hWE hWWE hsE)
  have hCz := hD.sec12.conjSub_eq_of_deltaSet_subset hfr.memC hzl hz2'
    (hD.conjSub_mem_deltaSet_su hF hrange hΔ hfr.memC WC hWC hWWC hsC)
  exact ⟨hD.sec12.commute_of_conjSub_eq_of_pair hfr.memE (hfr.memP 0).1 (hfr.memQ 0).1
      (hfr.opposite 0) (hfr.memQ 0).2.1.2.2.symm hEz (hz₂ h0.1) (hz₂ h0.2) hz2',
    hD.sec12.commute_of_conjSub_eq_of_pair hfr.memC (hfr.memQ 0).1 (hfr.memP 0).1
      (hfr.opposite 0).symm (hfr.memP 0).2.1.2.2.symm hCz (hz₂ h0.2) (hz₂ h0.1) hz2'⟩

theorem commute_shortSU {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : Sec12.IsSubframe R A A₀ E C P Q) (h0 : P 0 ∈ Δ₂ ∧ Q 0 ∈ Δ₂) [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) {Φ : SU (unitaryInvolution F 2 f) 4 →* G}
    (hker : Φ.ker ≤ Subgroup.center _) (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g, X = (conjSub (Unitary.rootGroup
      (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1))
        g).map Φ)
    (hP : ∀ i, (Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 4
      (longC2 i)).map Φ = ![P 2, P 1] i)
    (hQ : ∀ i, (Unitary.rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) 4
      (-longC2 i)).map Φ = ![Q 2, Q 1] i)
    {a b : Fin (4 / 2) ⊕ Fin (4 / 2)}
    (hab : (a = Sum.inl j0 ∧ b = Sum.inr j1) ∨ (a = Sum.inr j0 ∧ b = Sum.inl j1)) (t : F) :
    (∀ e ∈ E, Commute (Φ (suElt _ (unitaryInvolution_involutive hF) a b t)) e) ∧
      ∀ x ∈ C, Commute (Φ (suElt _ (unitaryInvolution_involutive hF) a b t)) x := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hζ' : (ζ : F) + (unitaryInvolution F 2 f) ζ = 0 := ζ.2
  have hR := hD.hyp.root
  have hQE : ∀ i, (Unitary.rootGroup (unitaryInvolution F 2 f) hσ 4 (-longC2 i)).map Φ ∈
      deltaSet R A A₀ E := fun i => by
    rw [hQ i]; fin_cases i; exacts [hfr.memQ 2, hfr.memQ 1]
  have hPC : ∀ i, (Unitary.rootGroup (unitaryInvolution F 2 f) hσ 4 (longC2 i)).map Φ ∈
      deltaSet R A A₀ C := fun i => by
    rw [hP i]; fin_cases i; exacts [hfr.memP 2, hfr.memP 1]
  have hWE : ∀ (v : Fin 4 → F) (X' : Subgroup (SU (unitaryInvolution F 2 f) 4)),
      IsUTransGroup (unitaryInvolution F 2 f) v X' → v ≠ 0 →
      uForm (unitaryInvolution F 2 f) v v = 0 → X'.map Φ ∈ deltaSet R A A₀ E → ∀ x : Fin 4,
      x.val < 2 → v x = 0 := by
    intro v X' hT hv hvv hX x hx
    have hx' : x = Fin.rev (c4' ⟨x.val, hx⟩) := by
      rw [rev_c4']
    rw [hx']
    exact apply_eq_zero_of_commuting hσ hζ hζ' hker hT hv hvv (c4'_ne_rev _)
      (isUTransGroup_neg₄ hF _) (hD.sec12.commuting_of_mem_deltaSet' hfr.memE hX (hQE _))
  have hWC : ∀ (v : Fin 4 → F) (X' : Subgroup (SU (unitaryInvolution F 2 f) 4)),
      IsUTransGroup (unitaryInvolution F 2 f) v X' → v ≠ 0 →
      uForm (unitaryInvolution F 2 f) v v = 0 → X'.map Φ ∈ deltaSet R A A₀ C → ∀ x : Fin 4,
      2 ≤ x.val → v x = 0 := by
    intro v X' hT hv hvv hX x hx
    have hx' : x = Fin.rev (c4 ⟨3 - x.val, by omega⟩) := by
      rw [rev_c4]
      ext
      show x.val = 3 - (3 - x.val)
      omega
    rw [hx']
    exact apply_eq_zero_of_commuting hσ hζ hζ' hker hT hv hvv (c4_ne_rev _)
      (isUTransGroup_pos₄ hF _) (hD.sec12.commuting_of_mem_deltaSet' hfr.memC hX (hPC _))
  have hidx : idx a ≠ idx b := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  set s₀ := suElt (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) a b t with hs₀
  have hmat : ∀ v : Fin 4 → F, suMat (unitaryInvolution F 2 f) 4 s₀ *ᵥ v =
      v + Pi.single (crd a) (t * v (crd (Sum.swap b))) -
        Pi.single (crd b) ((unitaryInvolution F 2 f) t * v (crd (Sum.swap a))) := by
    intro v
    have e := mat_suElt hσ hidx t
    change suMat (unitaryInvolution F 2 f) 4 s₀ = _ at e
    rw [e, sub_mulVec, add_mulVec, one_mulVec, single_mulVec, single_mulVec]
    rfl
  have hpres : ∀ v : Fin 4 → F, ((∀ x : Fin 4, x.val < 2 → v x = 0) →
      ∀ x : Fin 4, x.val < 2 → (suMat (unitaryInvolution F 2 f) 4 s₀ *ᵥ v) x = 0) ∧
      ((∀ x : Fin 4, 2 ≤ x.val → v x = 0) →
        ∀ x : Fin 4, 2 ≤ x.val → (suMat (unitaryInvolution F 2 f) 4 s₀ *ᵥ v) x = 0) := by
    intro v
    rw [hmat]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have c0 : crd (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2)) = 0 := rfl
      have c1 : crd (Sum.swap (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2))) = 1 := rfl
      have c2 : crd (Sum.inr j1 : Fin (4 / 2) ⊕ Fin (4 / 2)) = 2 := rfl
      have c3 : crd (Sum.swap (Sum.inl j0 : Fin (4 / 2) ⊕ Fin (4 / 2))) = 3 := rfl
      rw [c0, c1, c2, c3]
      refine ⟨fun hv x hx => ?_, fun hv x hx => ?_⟩
      · have h0 := hv 0 (by decide)
        have h1 := hv 1 (by decide)
        fin_cases x <;> simp_all
      · have h2 := hv 2 (by decide)
        have h3 := hv 3 (by decide)
        fin_cases x <;> simp_all
    · have c0 : crd (Sum.inr j0 : Fin (4 / 2) ⊕ Fin (4 / 2)) = 3 := rfl
      have c1 : crd (Sum.swap (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2))) = 2 := rfl
      have c2 : crd (Sum.inl j1 : Fin (4 / 2) ⊕ Fin (4 / 2)) = 1 := rfl
      have c3 : crd (Sum.swap (Sum.inr j0 : Fin (4 / 2) ⊕ Fin (4 / 2))) = 0 := rfl
      rw [c0, c1, c2, c3]
      refine ⟨fun hv x hx => ?_, fun hv x hx => ?_⟩
      · have h0 := hv 0 (by decide)
        have h1 := hv 1 (by decide)
        fin_cases x <;> simp_all
      · have h2 := hv 2 (by decide)
        have h3 := hv 3 (by decide)
        fin_cases x <;> simp_all
  have hs2 : s₀ * s₀ = 1 := by
    rw [hs₀, ← suElt_add, CharTwo.add_self_eq_zero, suElt_zero]
  exact hD.commute_of_preserves_su hfr h0 hF hrange hΔ _ _ hWE hWC
    (fun v w hv hw => uForm_of_low_eq_zero₄ (unitaryInvolution F 2 f) hv hw)
    (fun v w hv hw => uForm_of_high_eq_zero₄ (unitaryInvolution F 2 f) hv hw)
    (fun v hv => (hpres v).1 hv) (fun v hv => (hpres v).2 hv) hs2

end DegOA

end CaseOADeg

end CFSG.Timmesfeld.ARS
