module

public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F112W

section Normal

variable {G : Type*} [Group G] {H U : Subgroup G}

theorem isNormalIn_of_le_normalizer {N : Subgroup G} (hNU : N ≤ U)
    (h : H ≤ Subgroup.normalizer (N : Set G)) : IsNormalIn H U N :=
  ⟨hNU, fun _ hg x hx => (Subgroup.mem_normalizer_iff.mp (h hg) x).mp hx⟩

theorem isNormalIn_sup {K K' : Subgroup G} (hK : IsNormalIn H U K) (hK' : IsNormalIn H U K') :
    IsNormalIn H U (K ⊔ K') :=
  isNormalIn_of_le_normalizer (sup_le hK.1 hK'.1)
    (F1.le_normalizer_sup (D14.le_normalizer_of_isNormalIn hK) (D14.le_normalizer_of_isNormalIn hK'))

theorem isNormalIn_inf {K K' : Subgroup G} (hK : IsNormalIn H U K) (hK' : IsNormalIn H U K') :
    IsNormalIn H U (K ⊓ K') :=
  isNormalIn_of_le_normalizer (inf_le_left.trans hK.1)
    (le_normalizer_inf (D14.le_normalizer_of_isNormalIn hK) (D14.le_normalizer_of_isNormalIn hK'))

theorem sup_eq_of_isChiefStep {L₁ L₂ N : Subgroup G} (h₁ : IsChiefStep H U L₁ N)
    (h₂ : IsChiefStep H U L₂ N) (hne : L₁ ≠ L₂) : L₁ ⊔ L₂ = N := by
  have hs : IsNormalIn H U (L₁ ⊔ L₂) := isNormalIn_sup h₁.2.1 h₂.2.1
  have hle : L₁ ⊔ L₂ ≤ N := sup_le h₁.2.2.1.le h₂.2.2.1.le
  rcases h₁.2.2.2 (L₁ ⊔ L₂) hs le_sup_left hle with h | h
  · have h2 : L₂ ≤ L₁ := h ▸ le_sup_right
    rcases h₂.2.2.2 L₁ h₁.2.1 h2 h₁.2.2.1.le with h3 | h3
    · exact absurd h3 hne
    · exact absurd h3 h₁.2.2.1.ne
  · exact h

theorem isChiefStep_inf_left (hUH : U ≤ H) {L₁ L₂ N : Subgroup G} (h₁ : IsChiefStep H U L₁ N)
    (h₂ : IsChiefStep H U L₂ N) (hne : L₁ ≠ L₂) : IsChiefStep H U (L₁ ⊓ L₂) L₁ := by
  have hsup := sup_eq_of_isChiefStep h₁ h₂ hne
  refine ⟨h₁.2.1, isNormalIn_inf h₁.2.1 h₂.2.1, ?_, ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h1 : L₁ ≤ L₂ := inf_eq_left.mp h
    have h2 : L₁ ⊔ L₂ = L₂ := sup_eq_right.mpr h1
    rw [hsup] at h2
    exact h₂.2.2.1.ne h2.symm
  · intro K hK hMK hKL
    have hKU : K ≤ U := hK.1
    have hKnorm : K ≤ Subgroup.normalizer (L₂ : Set G) :=
      (hKU.trans hUH).trans (D14.le_normalizer_of_isNormalIn h₂.2.1)
    have hKs : IsNormalIn H U (K ⊔ L₂) := isNormalIn_sup hK h₂.2.1
    rcases h₂.2.2.2 (K ⊔ L₂) hKs le_sup_right
      (sup_le (hKL.trans h₁.2.2.1.le) h₂.2.2.1.le) with h | h
    · left
      have hK2 : K ≤ L₂ := h ▸ le_sup_left
      exact le_antisymm (le_inf hKL hK2) hMK
    · right
      apply le_antisymm hKL
      intro x hx
      have hxN : x ∈ K ⊔ L₂ := h ▸ (h₁.2.2.1.le hx)
      obtain ⟨k, hk, l, hl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hKnorm).mp hxN
      have hlL₁ : l ∈ L₁ := by
        have := L₁.mul_mem (L₁.inv_mem (hKL hk)) hx
        simpa using this
      exact K.mul_mem hk (hMK ⟨hlL₁, hl⟩)

theorem isChiefStep_inf_right (hUH : U ≤ H) {L₁ L₂ N : Subgroup G} (h₁ : IsChiefStep H U L₁ N)
    (h₂ : IsChiefStep H U L₂ N) (hne : L₁ ≠ L₂) : IsChiefStep H U (L₁ ⊓ L₂) L₂ := by
  rw [inf_comm]
  exact isChiefStep_inf_left hUH h₂ h₁ hne.symm

theorem isCentralStep_sup_iff (hUH : U ≤ H) {L₁ L₂ : Subgroup G} (h₁ : IsNormalIn H U L₁)
    (h₂ : IsNormalIn H U L₂) :
    IsCentralStep H L₂ (L₁ ⊔ L₂) ↔ IsCentralStep H (L₁ ⊓ L₂) L₁ := by
  have hN₂ := D14.le_normalizer_of_isNormalIn h₂
  constructor
  · intro h g hg x hx
    refine ⟨?_, h g hg x (Subgroup.mem_sup_left hx)⟩
    exact L₁.mul_mem (h₁.2 g hg x hx) (L₁.inv_mem hx)
  · intro h g hg x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
      ((h₁.1.trans hUH).trans hN₂)).mp hx
    have hc₁ : g * a * g⁻¹ * a⁻¹ ∈ L₂ := (h g hg a ha).2
    have hc₂ : g * b * g⁻¹ * b⁻¹ ∈ L₂ := L₂.mul_mem (h₂.2 g hg b hb) (L₂.inv_mem hb)
    have hc₂' : a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ ∈ L₂ :=
      (Subgroup.mem_normalizer_iff.mp (hN₂ (hUH (h₁.1 ha))) _).mp hc₂
    have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
        (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact L₂.mul_mem hc₁ hc₂'

end Normal

section Weight

variable {G : Type*} [Group G] {H U : Subgroup G}

open Classical in
@[expose] noncomputable def stepWeight (H L N : Subgroup G) : ℕ :=
  if IsCentralStep H L N then 0 else 1

theorem stepWeight_of_central {L N : Subgroup G} (h : IsCentralStep H L N) :
    stepWeight H L N = 0 := by
  simp [stepWeight, h]

theorem stepWeight_of_not_central {L N : Subgroup G} (h : ¬ IsCentralStep H L N) :
    stepWeight H L N = 1 := by
  simp [stepWeight, h]

theorem stepWeight_congr {L N L' N' : Subgroup G}
    (h : IsCentralStep H L N ↔ IsCentralStep H L' N') : stepWeight H L N = stepWeight H L' N' := by
  classical
  unfold stepWeight
  exact if_congr h rfl rfl

theorem isChiefSeriesFrom_of_step {L N : Subgroup G} {n : ℕ} (hstep : IsChiefStep H U L N)
    (hs : IsChiefSeriesFrom H U L n) : IsChiefSeriesFrom H U N (n + stepWeight H L N) := by
  by_cases hc : IsCentralStep H L N
  · rw [stepWeight_of_central hc, add_zero]
    exact .central hstep hc hs
  · rw [stepWeight_of_not_central hc]
    exact .noncentral hstep hc hs

theorem exists_step_of_isChiefSeriesFrom {N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) (hN : N ≠ ⊥) :
    ∃ (L : Subgroup G) (n' : ℕ), IsChiefStep H U L N ∧ IsChiefSeriesFrom H U L n' ∧
      n = n' + stepWeight H L N := by
  cases h with
  | bot => exact absurd rfl hN
  | central hstep hc hs => exact ⟨_, _, hstep, hs, by rw [stepWeight_of_central hc, add_zero]⟩
  | noncentral hstep hc hs => exact ⟨_, _, hstep, hs, by rw [stepWeight_of_not_central hc]⟩

theorem eq_zero_of_isChiefSeriesFrom_bot {n : ℕ} (h : IsChiefSeriesFrom H U ⊥ n) : n = 0 := by
  cases h with
  | bot => rfl
  | central hstep => exact absurd hstep.2.2.1 not_lt_bot
  | noncentral hstep => exact absurd hstep.2.2.1 not_lt_bot

end Weight

section Series

variable {G : Type*} [Group G] [Finite G] {H U : Subgroup G}

theorem isChiefSeriesFrom_unique (hUH : U ≤ H) {N : Subgroup G} {n m : ℕ}
    (h₁ : IsChiefSeriesFrom H U N n) (h₂ : IsChiefSeriesFrom H U N m) : n = m := by
  induction N using WellFoundedLT.induction generalizing n m with
  | _ N ih =>
    by_cases hN : N = ⊥
    · subst hN
      rw [eq_zero_of_isChiefSeriesFrom_bot h₁, eq_zero_of_isChiefSeriesFrom_bot h₂]
    obtain ⟨L₁, n₁, hs₁, hser₁, hn₁⟩ := exists_step_of_isChiefSeriesFrom h₁ hN
    obtain ⟨L₂, n₂, hs₂, hser₂, hn₂⟩ := exists_step_of_isChiefSeriesFrom h₂ hN
    by_cases heq : L₁ = L₂
    · subst heq
      have := ih L₁ hs₁.2.2.1 hser₁ hser₂
      omega
    · have hsup := sup_eq_of_isChiefStep hs₁ hs₂ heq
      have hM₁ : IsChiefStep H U (L₁ ⊓ L₂) L₁ := isChiefStep_inf_left hUH hs₁ hs₂ heq
      have hM₂ : IsChiefStep H U (L₁ ⊓ L₂) L₂ := isChiefStep_inf_right hUH hs₁ hs₂ heq
      obtain ⟨r, hr⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := U) (L₁ ⊓ L₂) hM₁.2.1
      have hL₁ := isChiefSeriesFrom_of_step hM₁ hr
      have hL₂ := isChiefSeriesFrom_of_step hM₂ hr
      have e₁ := ih L₁ hs₁.2.2.1 hser₁ hL₁
      have e₂ := ih L₂ hs₂.2.2.1 hser₂ hL₂
      have w₁ : stepWeight H L₂ N = stepWeight H (L₁ ⊓ L₂) L₁ := by
        apply stepWeight_congr
        have := isCentralStep_sup_iff hUH hs₁.2.1 hs₂.2.1
        rwa [hsup] at this
      have w₂ : stepWeight H L₁ N = stepWeight H (L₁ ⊓ L₂) L₂ := by
        apply stepWeight_congr
        have := isCentralStep_sup_iff hUH hs₂.2.1 hs₁.2.1
        rwa [sup_comm, hsup, inf_comm] at this
      omega

open Classical in
@[expose] noncomputable def eta (H U N : Subgroup G) : ℕ :=
  if h : ∃ n, IsChiefSeriesFrom H U N n then Classical.choose h else 0

theorem isChiefSeriesFrom_iff_eta (hUH : U ≤ H) {N : Subgroup G} (hN : IsNormalIn H U N) {n : ℕ} :
    IsChiefSeriesFrom H U N n ↔ eta H U N = n := by
  have hex := D15Proof.exists_isChiefSeriesFrom (H := H) (U := U) N hN
  have hspec := Classical.choose_spec hex
  have heta : eta H U N = Classical.choose hex := by
    simp [eta, hex]
  rw [heta]
  constructor
  · intro h
    exact isChiefSeriesFrom_unique hUH hspec h
  · rintro rfl
    exact hspec

theorem isChiefSeriesFrom_eta (hUH : U ≤ H) {N : Subgroup G} (hN : IsNormalIn H U N) :
    IsChiefSeriesFrom H U N (eta H U N) :=
  (isChiefSeriesFrom_iff_eta hUH hN).mpr rfl

end Series

section Between

variable {G : Type*} [Group G] {H U : Subgroup G}

inductive IsChiefSeriesBetween (H U W : Subgroup G) : Subgroup G → ℕ → Prop
  | refl : IsChiefSeriesBetween H U W W 0
  | central {N L : Subgroup G} {n : ℕ} : IsChiefStep H U L N → IsCentralStep H L N →
      IsChiefSeriesBetween H U W L n → IsChiefSeriesBetween H U W N n
  | noncentral {N L : Subgroup G} {n : ℕ} : IsChiefStep H U L N → ¬ IsCentralStep H L N →
      IsChiefSeriesBetween H U W L n → IsChiefSeriesBetween H U W N (n + 1)

theorem IsChiefSeriesBetween.le {W N : Subgroup G} {n : ℕ} (h : IsChiefSeriesBetween H U W N n) :
    W ≤ N := by
  induction h with
  | refl => exact le_rfl
  | central hstep _ _ ih => exact ih.trans hstep.2.2.1.le
  | noncentral hstep _ _ ih => exact ih.trans hstep.2.2.1.le

theorem IsChiefSeriesBetween.append {W N : Subgroup G} {a b : ℕ}
    (h : IsChiefSeriesBetween H U W N a) (hW : IsChiefSeriesFrom H U W b) :
    IsChiefSeriesFrom H U N (a + b) := by
  induction h with
  | refl => rwa [zero_add]
  | central hstep hc _ ih => exact .central hstep hc ih
  | noncentral hstep hc _ ih =>
    have := IsChiefSeriesFrom.noncentral hstep hc ih
    rwa [add_right_comm] at this

theorem isChiefSeriesBetween_bot_of_from {N : Subgroup G} {n : ℕ} (h : IsChiefSeriesFrom H U N n) :
    IsChiefSeriesBetween H U ⊥ N n := by
  induction h with
  | bot => exact .refl
  | central hstep hc _ ih => exact .central hstep hc ih
  | noncentral hstep hc _ ih => exact .noncentral hstep hc ih

theorem isChiefSeriesFrom_of_between_bot {N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesBetween H U ⊥ N n) : IsChiefSeriesFrom H U N n := by
  have := h.append (IsChiefSeriesFrom.bot : IsChiefSeriesFrom H U ⊥ 0)
  rwa [add_zero] at this

theorem isNormalIn_of_isChiefSeriesFrom {N : Subgroup G} {n : ℕ} (h : IsChiefSeriesFrom H U N n) :
    IsNormalIn H U N := by
  cases h with
  | bot => exact D15Proof.isNormalIn_bot H U
  | central hstep => exact hstep.1
  | noncentral hstep => exact hstep.1

theorem commutator_le_self_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h hb) a⁻¹).mp (A.inv_mem ha)
  have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
  show a * b * a⁻¹ * b⁻¹ ∈ A
  rw [e]
  exact A.mul_mem ha h1

variable [Finite G]

theorem exists_isChiefSeriesBetween {W : Subgroup G} (hW : IsNormalIn H U W) :
    ∀ N : Subgroup G, IsNormalIn H U N → W ≤ N → ∃ n, IsChiefSeriesBetween H U W N n := by
  intro N
  induction N using WellFoundedLT.induction with
  | _ N ih =>
    intro hN hWN
    by_cases hne : W = N
    · subst hne
      exact ⟨0, .refl⟩
    have hlt : W < N := lt_of_le_of_ne hWN hne
    obtain ⟨L, hL⟩ := (Set.toFinite {K : Subgroup G | IsNormalIn H U K ∧ W ≤ K ∧ K < N}).exists_maximal
      ⟨W, hW, le_rfl, hlt⟩
    have hLs : IsNormalIn H U L ∧ W ≤ L ∧ L < N := hL.1
    have hstep : IsChiefStep H U L N := by
      refine ⟨hN, hLs.1, hLs.2.2, fun K hK hLK hKN => ?_⟩
      by_cases hKN' : K = N
      · exact Or.inr hKN'
      · exact Or.inl (le_antisymm
          (hL.2 ⟨hK, hLs.2.1.trans hLK, lt_of_le_of_ne hKN hKN'⟩ hLK) hLK)
    obtain ⟨n, hn⟩ := ih L hLs.2.2 hLs.1 hLs.2.1
    by_cases hc : IsCentralStep H L N
    · exact ⟨n, .central hstep hc hn⟩
    · exact ⟨n + 1, .noncentral hstep hc hn⟩

theorem isChiefSeriesBetween_unique (hUH : U ≤ H) {W N : Subgroup G} (hW : IsNormalIn H U W)
    {a a' : ℕ} (h : IsChiefSeriesBetween H U W N a) (h' : IsChiefSeriesBetween H U W N a') :
    a = a' := by
  obtain ⟨b, hb⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := U) W hW
  have := isChiefSeriesFrom_unique hUH (h.append hb) (h'.append hb)
  omega

theorem eta_eq_add (hUH : U ≤ H) {W N : Subgroup G} (hW : IsNormalIn H U W) {a : ℕ}
    (h : IsChiefSeriesBetween H U W N a) : eta H U N = eta H U W + a := by
  have h1 := h.append (isChiefSeriesFrom_eta hUH hW)
  have hN : IsNormalIn H U N := isNormalIn_of_isChiefSeriesFrom h1
  have := (isChiefSeriesFrom_iff_eta hUH hN).mp h1
  omega

theorem eta_le_of_le (hUH : U ≤ H) {W N : Subgroup G} (hW : IsNormalIn H U W)
    (hN : IsNormalIn H U N) (hWN : W ≤ N) : eta H U W ≤ eta H U N := by
  obtain ⟨a, ha⟩ := exists_isChiefSeriesBetween hW N hN hWN
  have := eta_eq_add hUH hW ha
  omega

end Between

section Lemma17

variable {G : Type*} [Group G] [Finite G] {H U : Subgroup G}

theorem count_eq_zero_of_commutator_le (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) {W N : Subgroup G}
    {a : ℕ} (h : IsChiefSeriesBetween H U W N a) (hc : ⁅N, oTwoUpper H⁆ ≤ W) : a = 0 := by
  obtain ⟨T, hT, hQT⟩ := F1.exists_isSylowTwoOf_ge (pCoreOf_le 2 H) (pCoreOf_isPGroup 2 H)
  induction h with
  | refl => rfl
  | @central N L n hstep hcent hs ih =>
    exact ih ((Subgroup.commutator_mono hstep.2.2.1.le le_rfl).trans hc)
  | @noncentral N L n hstep hnc hs ih =>
    exfalso
    apply hnc
    refine D15Proof.isCentralStep_of_commutator_le hT hUH ?_ hstep (hc.trans hs.le)
    exact hstep.1.1.trans (hUQ.trans (isSylowTwoOf_pCoreOf_le hT))

theorem isChiefSeriesBetween_zero_iff (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) {W N : Subgroup G}
    (hW : IsNormalIn H U W) (hN : IsNormalIn H U N) (hWN : W ≤ N) :
    IsChiefSeriesBetween H U W N 0 ↔ ⁅N, oTwoUpper H⁆ ≤ W := by
  constructor
  · have key : ∀ {N' : Subgroup G} {n : ℕ}, IsChiefSeriesBetween H U W N' n → n = 0 →
        ⁅N', oTwoUpper H⁆ ≤ W := by
      intro N' n hs
      induction hs with
      | refl =>
        intro _
        exact commutator_le_self_of_le_normalizer
          ((oTwoUpper_le H).trans (D14.le_normalizer_of_isNormalIn hW))
      | @central N L n hstep hcent hs ih =>
        intro hn
        have hL : ⁅L, oTwoUpper H⁆ ≤ W := ih hn
        have hHW : H ≤ Subgroup.normalizer (W : Set G) := D14.le_normalizer_of_isNormalIn hW
        have key := A4.commutator_le_of_oTwoUpper (A := oTwoUpper H) (N := W) (B := L) (D := N)
          ((oTwoUpper_le H).trans hHW) (hstep.1.1.trans (hUH.trans hHW)) hstep.2.2.1.le
          (D14.exists_pow_mem_of_isPGroup ((pCoreOf_isPGroup 2 H).to_le hUQ) hstep.1.1)
          (D14.commutator_le_of_isCentralStep hcent)
          (by rw [Subgroup.commutator_comm]; exact hL)
        rw [D14.oTwoUpper_oTwoUpper, Subgroup.commutator_comm] at key
        exact key
      | noncentral hstep hnc hs ih =>
        intro hn
        exact absurd hn (Nat.succ_ne_zero _)
    exact fun h => key h rfl
  · intro hc
    obtain ⟨a, ha⟩ := exists_isChiefSeriesBetween hW N hN hWN
    have := count_eq_zero_of_commutator_le hUH hUQ ha hc
    subst this
    exact ha

theorem isChiefSeriesFrom_zero_iff (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) {N : Subgroup G}
    (hN : IsNormalIn H U N) : IsChiefSeriesFrom H U N 0 ↔ ⁅N, oTwoUpper H⁆ = ⊥ := by
  have := isChiefSeriesBetween_zero_iff hUH hUQ (D15Proof.isNormalIn_bot H U) hN bot_le
  constructor
  · intro h
    exact le_bot_iff.mp (this.mp (isChiefSeriesBetween_bot_of_from h))
  · intro h
    exact isChiefSeriesFrom_of_between_bot (this.mpr h.le)

theorem eta_eq_zero_iff (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) {N : Subgroup G}
    (hN : IsNormalIn H U N) : eta H U N = 0 ↔ ⁅N, oTwoUpper H⁆ = ⊥ := by
  rw [← isChiefSeriesFrom_zero_iff hUH hUQ hN, isChiefSeriesFrom_iff_eta hUH hN]

theorem eta_eq_of_commutator_le (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) {W N : Subgroup G}
    (hW : IsNormalIn H U W) (hN : IsNormalIn H U N) (hWN : W ≤ N)
    (hc : ⁅N, oTwoUpper H⁆ ≤ W) : eta H U N = eta H U W := by
  have h0 := (isChiefSeriesBetween_zero_iff hUH hUQ hW hN hWN).mpr hc
  have := eta_eq_add hUH hW h0
  omega

theorem commutator_le_of_isChiefStep {Q L N : Subgroup G} (hQ : IsPGroup 2 Q) (hQH : Q ≤ H)
    (hQn : H ≤ Subgroup.normalizer (Q : Set G)) (hstep : IsChiefStep H U L N) (hNQ : N ≤ Q) :
    ⁅N, Q⁆ ≤ L := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hLN : L ≤ N := hstep.2.2.1.le
  set K := centralizerMod L N Q with hK
  have hKN : K ≤ N := centralizerMod_le_left L N Q
  have hLK : L ≤ K := by
    intro l hl
    refine ⟨hLN hl, Subgroup.le_normalizer hl, fun t ht => ?_⟩
    have h1 : t * l⁻¹ * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hHL (hQH ht)) _).mp (L.inv_mem hl)
    have e : l * t * l⁻¹ * t⁻¹ = l * (t * l⁻¹ * t⁻¹) := by group
    rw [e]
    exact L.mul_mem hl h1
  have hHK : ∀ h ∈ H, ∀ y ∈ K, h * y * h⁻¹ ∈ K := by
    intro h hh y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHN hh) y).mp hy.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHL hh) hy.2.1) (Subgroup.inv_mem _ (hHL hh)),
      fun t ht => ?_⟩
    have hq : h⁻¹ * t * h ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem hh)) t).mp ht
      simpa using this
    have h1 : y * (h⁻¹ * t * h) * y⁻¹ * (h⁻¹ * t * h)⁻¹ ∈ L := hy.2.2 _ hq
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHL hh) _).mp h1
    have e : h * y * h⁻¹ * t * (h * y * h⁻¹)⁻¹ * t⁻¹ =
        h * (y * (h⁻¹ * t * h) * y⁻¹ * (h⁻¹ * t * h)⁻¹) * h⁻¹ := by group
    rw [e]
    exact h2
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := fun h hh =>
    B6.mem_normalizer_of_forall_mem (hHK h hh) fun y hy => by simpa using hHK h⁻¹ (H.inv_mem hh) y hy
  have hKnorm : IsNormalIn H U K :=
    ⟨hKN.trans hstep.1.1, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHKn hg) x).mp hx⟩
  obtain ⟨x, hxN, hxL, hxQ⟩ := D14.exists_fixed_of_lt hQ hNQ hstep.2.2.1 (hQH.trans hHN)
    (hQH.trans hHL)
  have hxK : x ∈ K := by
    refine ⟨hxN, hHL (hQH (hNQ hxN)), fun t ht => ?_⟩
    have h1 := L.inv_mem (hxQ t ht)
    have e : (t * x * t⁻¹ * x⁻¹)⁻¹ = x * t * x⁻¹ * t⁻¹ := by group
    rwa [e] at h1
  have hKeq : K = N :=
    (hstep.2.2.2 K hKnorm hLK hKN).resolve_left fun h => hxL (h ▸ hxK)
  rw [Subgroup.commutator_le]
  intro n hn q hq
  have hnK : n ∈ K := hKeq ▸ hn
  exact hnK.2.2 q hq

end Lemma17

end F112W

end CFSG.Quasithin
