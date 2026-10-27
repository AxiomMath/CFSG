module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualInv
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVICoord

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z X B : Subgroup G}

theorem caseVIMeet_of_coord {n : ℕ} (hcB : Ctx M Q Z B) (hw : Width Q Z n) (hn : 2 < n)
    {S : Subgroup G} (hSH : S ≤ H0 M Z) (hQS : Q ≤ S)
    (hSn : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hcard : Nat.card K = Nat.card Z)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) (e : M₀.E), M₀.Qf (φ m e) = M₀.Qf e)
    {F : Type} [Field F] [Finite F] (ρ' : ↥S →* GL (Fin n) F) (hrange : ρ'.range = StatedSL n F)
    (C : NatDualCoord (φ.comp (Subgroup.inclusion hSH)) ρ') :
    ¬ (LB M Q B ⊓ S ≤ Q) := by
  intro hle
  set ρ : ↥S →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hSH) with hρ
  have hn3 : 3 ≤ n := hn
  have hq4 : 4 ≤ Nat.card Z := hcB.hyp.q4
  have hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 :=
    exists_ne_zero_sq_ne_one_of_two_lt_card K (by rw [hcard]; omega)
  haveI : CharP F 2 := charP_of_injective_ringHom C.θ₁.toRingHom.injective 2
  let Qd : QuadDatum K M₀.E := quadDatumOfModel M₀
  have hQρ : ∀ (g : ↥S) (e : M₀.E), Qd.Qf (ρ g e) = Qd.Qf e := fun g e => hφiso _ e
  have hLH : LB M Q B ≤ H0 M Z := hcB.LB_le_H0
  have hLM : LB M Q B ≤ M := hcB.LB_le_M
  let T : ↥(LB M Q B) → (M₀.E ≃ₗ[K] M₀.E) := fun p => φ ⟨p, hLH p.2⟩
  have hTsq : ∀ (p : ↥(LB M Q B)) (e : M₀.E), T p (T p e) = e := by
    intro p e
    have h1 : φ ((⟨p, hLH p.2⟩ : ↥(H0 M Z)) ^ 2) = 1 := by
      rw [hφQ]
      exact hcB.sq_mem_Q_of_mem_LB p.2
    rw [pow_two, map_mul] at h1
    have h2 := LinearEquiv.congr_fun h1 e
    exact h2
  have hTQ : ∀ (p : ↥(LB M Q B)) (e : M₀.E), Qd.Qf (T p e) = Qd.Qf e := fun p e => hφiso _ e
  have hTnorm : ∀ (p : ↥(LB M Q B)) (g : ↥S), ∃ g' : ↥S, ∀ e, ρ g (T p e) = T p (ρ g' e) := by
    intro p g
    have hpM : (p : G) ∈ M := hLM p.2
    have hmem : (p : G)⁻¹ * (g : G) * ((p : G)⁻¹)⁻¹ ∈ S :=
      hSn _ (M.inv_mem hpM) _ g.2
    rw [inv_inv] at hmem
    refine ⟨⟨(p : G)⁻¹ * (g : G) * (p : G), hmem⟩, fun e => ?_⟩
    have key : (⟨g, hSH g.2⟩ : ↥(H0 M Z)) * ⟨p, hLH p.2⟩ =
        ⟨p, hLH p.2⟩ * ⟨(p : G)⁻¹ * (g : G) * (p : G), hSH hmem⟩ :=
      Subtype.ext (by simp [mul_assoc])
    show φ ⟨g, _⟩ (φ ⟨p, _⟩ e) = φ ⟨p, _⟩ (φ ⟨_, _⟩ e)
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, key]
  have hdich : ∀ p : ↥(LB M Q B), C.Preserves (T p) ∨ C.Swaps (T p) := fun p =>
    C.preserves_or_swaps hn3 hrange (T p) (hTnorm p)
  have hpresQ : ∀ p : ↥(LB M Q B), C.Preserves (T p) → (p : G) ∈ Q := by
    intro p hp
    obtain ⟨g, hg⟩ := C.exists_eq_of_preserves Qd hn3 hrange hQρ hK (T p) (hTsq p) (hTQ p) hp
    have h1 : φ (⟨p, hLH p.2⟩ * (⟨g, hSH g.2⟩ : ↥(H0 M Z))⁻¹) = 1 := by
      rw [map_mul, map_inv]
      have : φ ⟨g, hSH g.2⟩ = T p := hg
      rw [this]
      exact mul_inv_cancel _
    have h2 : (p : G) * (g : G)⁻¹ ∈ Q := (hφQ _).mp h1
    have h3 : (p : G) ∈ S := by
      have := S.mul_mem (hQS h2) g.2
      simpa using this
    exact hle ⟨p.2, h3⟩
  have hcardLB := hcB.card_LB_ge hw (by omega)
  have hpow : 16 ≤ Nat.card Z ^ (n - 1) := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ Nat.card Z ^ 2 := Nat.pow_le_pow_left hq4 2
      _ ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  by_cases hall : ∀ p : ↥(LB M Q B), C.Preserves (T p)
  · have hLQ : LB M Q B ≤ Q := fun p hp => hpresQ ⟨p, hp⟩ (hall ⟨p, hp⟩)
    have := Subgroup.card_le_of_le hLQ
    nlinarith
  · push Not at hall
    obtain ⟨p₁, hp₁⟩ := hall
    have hsw₁ : C.Swaps (T p₁) := (hdich p₁).resolve_left hp₁
    have hsub : (LB M Q B : Set G) ⊆ (Q : Set G) ∪ (fun x => (p₁ : G) * x) '' (Q : Set G) := by
      intro p hp
      by_cases hpp : C.Preserves (T ⟨p, hp⟩)
      · exact Or.inl (hpresQ _ hpp)
      · right
        have hsw : C.Swaps (T ⟨p, hp⟩) := (hdich ⟨p, hp⟩).resolve_left hpp
        refine ⟨(p₁ : G)⁻¹ * p, ?_, by group⟩
        have hmem : (p₁ : G)⁻¹ * p ∈ LB M Q B := (LB M Q B).mul_mem ((LB M Q B).inv_mem p₁.2) hp
        refine hpresQ ⟨_, hmem⟩ ?_
        have hTe : ∀ e, T ⟨(p₁ : G)⁻¹ * p, hmem⟩ e = T p₁ (T ⟨p, hp⟩ e) := by
          intro e
          have h1 : φ (⟨(p₁ : G)⁻¹ * p, hLH hmem⟩ : ↥(H0 M Z)) =
              φ (⟨p₁, hLH p₁.2⟩ : ↥(H0 M Z))⁻¹ * φ ⟨p, hLH hp⟩ := by
            have e' : (⟨(p₁ : G)⁻¹ * p, hLH hmem⟩ : ↥(H0 M Z)) =
                (⟨p₁, hLH p₁.2⟩ : ↥(H0 M Z))⁻¹ * ⟨p, hLH hp⟩ := Subtype.ext rfl
            rw [e', map_mul, map_inv]
          have h2 : φ (⟨p₁, hLH p₁.2⟩ : ↥(H0 M Z))⁻¹ = T p₁ := by
            have hmul1 : φ (⟨p₁, hLH p₁.2⟩ : ↥(H0 M Z)) * T p₁ = 1 :=
              LinearEquiv.ext fun e' => hTsq p₁ e'
            rw [map_inv]
            exact inv_eq_of_mul_eq_one_right hmul1
          show φ _ e = T p₁ (T ⟨p, hp⟩ e)
          rw [h1, h2]
          rfl
        refine ⟨fun x => ?_, fun y => ?_⟩
        · rw [hTe]
          obtain ⟨y', hy'⟩ : ∃ y', T ⟨p, hp⟩ (C.inl x) = C.inr y' :=
            ⟨_, C.eq_inr_of_mem_W₂ (hsw.1 x)⟩
          rw [hy']
          exact hsw₁.2 y'
        · rw [hTe]
          obtain ⟨x', hx'⟩ : ∃ x', T ⟨p, hp⟩ (C.inr y) = C.inl x' :=
            ⟨_, C.eq_inl_of_mem_W₁ (hsw.2 y)⟩
          rw [hx']
          exact hsw₁.1 x'
    have hfin : ((Q : Set G) ∪ (fun x => (p₁ : G) * x) '' (Q : Set G)).Finite := Set.toFinite _
    have h1 : Nat.card (LB M Q B) ≤ 2 * Nat.card Q := by
      rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq,
        Nat.card_coe_set_eq]
      calc (LB M Q B : Set G).ncard
          ≤ ((Q : Set G) ∪ (fun x => (p₁ : G) * x) '' (Q : Set G)).ncard :=
            Set.ncard_le_ncard hsub hfin
        _ ≤ (Q : Set G).ncard + ((fun x => (p₁ : G) * x) '' (Q : Set G)).ncard :=
            Set.ncard_union_le _ _
        _ = 2 * (Q : Set G).ncard := by
            rw [Set.ncard_image_of_injective _ (mul_right_injective (p₁ : G))]
            ring
    nlinarith

end CFSG.RankThree.GF2n.Stroth80
