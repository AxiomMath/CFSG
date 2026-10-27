module

public import CFSG.Milestones.ASVolI.F48.Small.Pres

public section

namespace CFSG.ASVolI

open CFSG.CosetTable

section Gen

variable {D Y : Type} [Group D] [Group Y] {A B : Subgroup D} {n : ℕ} (L : Fin n → D)
  (f₁ : ↥A →* Y) (f₂ : ↥B →* Y)

open Classical in
noncomputable def burnsideF48s_yL (i : Fin n) : Y :=
  if h : L i ∈ A then f₁ ⟨L i, h⟩ else if h' : L i ∈ B then f₂ ⟨L i, h'⟩ else 1

variable {L f₁ f₂}

theorem burnsideF48s_ev_yL_A (w : List (Fin n × Bool)) (hw : ∀ l ∈ w, L l.1 ∈ A) :
    ∃ h : burnsideF48s_ev L w ∈ A,
      burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w = f₁ ⟨burnsideF48s_ev L w, h⟩ := by
  classical
  let LA : Fin n → ↥A := fun i => if h : L i ∈ A then ⟨L i, h⟩ else 1
  have e1 : ((burnsideF48s_ev LA w : ↥A) : D) = burnsideF48s_ev L w :=
    (burnsideF48s_ev_map A.subtype LA w).symm.trans
      (burnsideF48s_ev_congr w fun l hl => by simp [LA, hw l hl])
  refine ⟨e1 ▸ (burnsideF48s_ev LA w).2, ?_⟩
  have e2 : burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w = f₁ (burnsideF48s_ev LA w) :=
    (burnsideF48s_ev_congr w fun l hl => by simp [burnsideF48s_yL, LA, hw l hl]).trans
      (burnsideF48s_ev_map f₁ LA w)
  rw [e2]
  congr 1
  exact Subtype.ext e1

theorem burnsideF48s_ev_yL_B (h12 : ∀ (t : D) (h : t ∈ A ⊓ B), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (w : List (Fin n × Bool)) (hw : ∀ l ∈ w, L l.1 ∈ B) :
    ∃ h : burnsideF48s_ev L w ∈ B,
      burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w = f₂ ⟨burnsideF48s_ev L w, h⟩ := by
  classical
  let LB : Fin n → ↥B := fun i => if h : L i ∈ B then ⟨L i, h⟩ else 1
  have e1 : ((burnsideF48s_ev LB w : ↥B) : D) = burnsideF48s_ev L w :=
    (burnsideF48s_ev_map B.subtype LB w).symm.trans
      (burnsideF48s_ev_congr w fun l hl => by simp [LB, hw l hl])
  refine ⟨e1 ▸ (burnsideF48s_ev LB w).2, ?_⟩
  have e2 : burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w = f₂ (burnsideF48s_ev LB w) := by
    refine (burnsideF48s_ev_congr w fun l hl => ?_).trans (burnsideF48s_ev_map f₂ LB w)
    have hB := hw l hl
    by_cases hA : L l.1 ∈ A
    · simp only [burnsideF48s_yL, LB, dif_pos hA, dif_pos hB]
      exact h12 _ ⟨hA, hB⟩
    · simp [burnsideF48s_yL, LB, hA, hB]
  rw [e2]
  congr 1
  exact Subtype.ext e1

theorem burnsideF48s_closure_yL (h12 : ∀ (t : D) (h : t ∈ A ⊓ B), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤)
    (hcovA : ∀ x ∈ A, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ A) ∧ burnsideF48s_ev L w = x)
    (hcovB : ∀ x ∈ B, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ B) ∧ burnsideF48s_ev L w = x) :
    Subgroup.closure (Set.range (burnsideF48s_yL L f₁ f₂)) = ⊤ := by
  rw [eq_top_iff, ← hgen]
  have hmem : ∀ w : List (Fin n × Bool), burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w ∈
      Subgroup.closure (Set.range (burnsideF48s_yL L f₁ f₂)) :=
    fun w => burnsideF48s_ev_mem _ w fun l _ => Subgroup.subset_closure ⟨l.1, rfl⟩
  refine sup_le ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨w, hl, hw⟩ := hcovA z z.2
    obtain ⟨h, e⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) w hl
    have hz : z = ⟨burnsideF48s_ev L w, h⟩ := Subtype.ext hw.symm
    rw [hz, ← e]
    exact hmem w
  · rintro _ ⟨z, rfl⟩
    obtain ⟨w, hl, hw⟩ := hcovB z z.2
    obtain ⟨h, e⟩ := burnsideF48s_ev_yL_B h12 w hl
    have hz : z = ⟨burnsideF48s_ev L w, h⟩ := Subtype.ext hw.symm
    rw [hz, ← e]
    exact hmem w

theorem burnsideF48s_closure_L (hAB : A ⊔ B = ⊤)
    (hcovA : ∀ x ∈ A, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ A) ∧ burnsideF48s_ev L w = x)
    (hcovB : ∀ x ∈ B, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ B) ∧ burnsideF48s_ev L w = x) :
    Subgroup.closure (Set.range L) = ⊤ := by
  rw [eq_top_iff, ← hAB]
  have hmem : ∀ w : List (Fin n × Bool), burnsideF48s_ev L w ∈ Subgroup.closure (Set.range L) :=
    fun w => burnsideF48s_ev_mem _ w fun l _ => Subgroup.subset_closure ⟨l.1, rfl⟩
  refine sup_le (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨w, -, rfl⟩ := hcovA z hz
    exact hmem w
  · obtain ⟨w, -, rfl⟩ := hcovB z hz
    exact hmem w

theorem burnsideF48s_core_gen [Finite D] {ws : List (List (Fin n × Bool))}
    (h12 : ∀ (t : D) (h : t ∈ A ⊓ B), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hAB : A ⊔ B = ⊤)
    (hcovA : ∀ x ∈ A, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ A) ∧ burnsideF48s_ev L w = x)
    (hcovB : ∀ x ∈ B, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ B) ∧ burnsideF48s_ev L w = x)
    (hD : ∀ w ∈ ws, burnsideF48s_ev L w = 1)
    (hY : ∀ w ∈ ws, burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w = 1)
    [Finite (PG n ws)] (hcardP : Nat.card (PG n ws) ≤ Nat.card D)
    (hcardY : Nat.card D ≤ Nat.card Y) :
    ∃ φ : Y ≃* D, (∀ z : ↥A, φ (f₁ z) = z) ∧ (∀ z : ↥B, φ (f₂ z) = z) := by
  obtain ⟨φ, hφ⟩ := burnsideF48s_equiv_of_pres hY hD (burnsideF48s_closure_yL h12 hgen hcovA hcovB)
    (burnsideF48s_closure_L hAB hcovA hcovB) hcardP hcardY
  have hφw : ∀ w : List (Fin n × Bool),
      φ (burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w) = burnsideF48s_ev L w := fun w =>
    (burnsideF48s_ev_map φ.toMonoidHom _ w).symm.trans (burnsideF48s_ev_congr w fun l _ => hφ l.1)
  refine ⟨φ, fun z => ?_, fun z => ?_⟩
  · obtain ⟨w, hl, hw⟩ := hcovA z z.2
    obtain ⟨h, e⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) w hl
    have hz : z = ⟨burnsideF48s_ev L w, h⟩ := Subtype.ext hw.symm
    rw [hz, ← e, hφw]
  · obtain ⟨w, hl, hw⟩ := hcovB z z.2
    obtain ⟨h, e⟩ := burnsideF48s_ev_yL_B h12 w hl
    have hz : z = ⟨burnsideF48s_ev L w, h⟩ := Subtype.ext hw.symm
    rw [hz, ← e, hφw]

theorem burnsideF48s_core_card_le {ws : List (List (Fin n × Bool))}
    (h12 : ∀ (t : D) (h : t ∈ A ⊓ B), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤)
    (hcovA : ∀ x ∈ A, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ A) ∧ burnsideF48s_ev L w = x)
    (hcovB : ∀ x ∈ B, ∃ w : List (Fin n × Bool), (∀ l ∈ w, L l.1 ∈ B) ∧ burnsideF48s_ev L w = x)
    (hY : ∀ w ∈ ws, burnsideF48s_ev (burnsideF48s_yL L f₁ f₂) w = 1) [Finite (PG n ws)] :
    Nat.card Y ≤ Nat.card (PG n ws) :=
  burnsideF48s_card_le_of_pres hY (burnsideF48s_closure_yL h12 hgen hcovA hcovB)

end Gen

end CFSG.ASVolI
