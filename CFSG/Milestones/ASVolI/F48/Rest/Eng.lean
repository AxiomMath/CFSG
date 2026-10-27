module

public import CFSG.Milestones.ASVolI.F48.Small.Eng

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.CosetTable

section Cover

variable {D : Type*} [Group D] {n : ℕ} (G : Fin n → D)

theorem burnsideF48t_closure_cover (S : Set (Fin n)) :
    ∀ z ∈ Subgroup.closure (G '' S), ∃ w : List (Fin n × Bool), (∀ l ∈ w, l.1 ∈ S) ∧
      burnsideF48s_ev G w = z := by
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨[(i, true)], ?_, ?_⟩
    · intro l hl
      rw [List.mem_singleton] at hl
      rw [hl]
      exact hi
    · simp [burnsideF48s_ev]
  | one => exact ⟨[], by simp, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨u ++ v, fun l hl => (List.mem_append.1 hl).elim (hu l) (hv l),
      burnsideF48s_ev_append G u v⟩
  | inv x _ hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨burnsideF48s_eInvW u, ?_, burnsideF48s_e_ev_invW G u⟩
    intro l hl
    simp only [burnsideF48s_eInvW, List.mem_reverse, List.mem_map] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact hu l' hl'

theorem burnsideF48t_letter_mem {S : Set (Fin n)} {i : Fin n} (hi : i ∈ S) :
    G i ∈ Subgroup.closure (G '' S) :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem burnsideF48t_ev_mem_closure {S : Set (Fin n)} {w : List (Fin n × Bool)}
    (hw : ∀ l ∈ w, l.1 ∈ S) : burnsideF48s_ev G w ∈ Subgroup.closure (G '' S) :=
  burnsideF48s_ev_mem G w fun l hl => burnsideF48t_letter_mem G (hw l hl)

end Cover

section Facts

variable {D : Type} [Group D] {n : ℕ}

structure burnsideF48t_Facts (G : Fin n → D) (P1 P2 : Subgroup D) (S1 S2 : Set (Fin n))
    (K : Subgroup D) (R1 R2 XW YW KW : List (List (Fin n × Bool))) (m : ℕ) : Prop where
  hP1 : P1 = Subgroup.closure (G '' S1)
  hP2 : P2 = Subgroup.closure (G '' S2)
  rel1 : ∀ r ∈ R1, (∀ l ∈ r, l.1 ∈ S1) ∧ burnsideF48s_ev G r = 1
  rel2 : ∀ r ∈ R2, (∀ l ∈ r, l.1 ∈ S2) ∧ burnsideF48s_ev G r = 1
  sup : P1 ⊔ P2 = ⊤
  K_le : K ≤ P1 ⊓ P2
  KW_let : ∀ w ∈ KW, ∀ l ∈ w, l.1 ∈ S1
  KW_cov : ∀ c ∈ K, ∃ w ∈ KW, burnsideF48s_ev G w = c
  XW_let : ∀ w ∈ XW, ∀ l ∈ w, l.1 ∈ S1
  YW_let : ∀ w ∈ YW, ∀ l ∈ w, l.1 ∈ S2
  xred : ∀ x ∈ P1, x ∉ P2 → (∀ k ∈ K, x * k * x⁻¹ ∈ K) → x * x ∈ K →
    ∃ w ∈ XW, (burnsideF48s_ev G w)⁻¹ * x ∈ K
  yred : ∀ y ∈ P2, y ∉ P1 → (∀ k ∈ K, y * k * y⁻¹ ∈ K) → y * y ∈ K →
    ∃ w ∈ YW, (burnsideF48s_ev G w)⁻¹ * y ∈ K
  cand : ∀ u ∈ XW, ∀ v ∈ YW, ∀ c ∈ KW,
    burnsideF48s_ev G u * burnsideF48s_ev G v * burnsideF48s_ev G c =
      burnsideF48s_ev G c * (burnsideF48s_ev G u * burnsideF48s_ev G v) →
    Finite (PG n (burnsideF48s_eWs R1 R2 m u v c)) ∧
      (Nat.card (PG n (burnsideF48s_eWs R1 R2 m u v c)) < Nat.card D ∨
        (Nat.card (PG n (burnsideF48s_eWs R1 R2 m u v c)) ≤ Nat.card D ∧
          burnsideF48s_ev G (burnsideF48s_eCandRel m u v c) = 1))

end Facts

section Comm

variable {D : Type*} [Group D] {P1 P2 : Subgroup D} {Y : Type*} [Group Y]
  (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y)

theorem burnsideF48t_comm_of (h12 : ∀ (t : D) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hinj : Function.Injective f₁) {u v c : D} (hu : u ∈ P1) (hv : v ∈ P2) (hc : c ∈ P1 ⊓ P2)
    (hvc : v * c * v⁻¹ ∈ P1 ⊓ P2)
    (hcomm : f₁ ⟨u, hu⟩ * f₂ ⟨v, hv⟩ * f₁ ⟨c, hc.1⟩ = f₁ ⟨c, hc.1⟩ * (f₁ ⟨u, hu⟩ * f₂ ⟨v, hv⟩)) :
    u * v * c = c * (u * v) := by
  have hm : u * (v * c * v⁻¹) * u⁻¹ ∈ P1 :=
    P1.mul_mem (P1.mul_mem hu hvc.1) (P1.inv_mem hu)
  have e1 : f₂ ⟨v, hv⟩ * f₁ ⟨c, hc.1⟩ = f₁ ⟨v * c * v⁻¹, hvc.1⟩ * f₂ ⟨v, hv⟩ := by
    rw [h12 c hc, h12 _ hvc, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show v * c = v * c * v⁻¹ * v
    group
  have e2 : f₁ ⟨u, hu⟩ * f₁ ⟨v * c * v⁻¹, hvc.1⟩ =
      f₁ ⟨u * (v * c * v⁻¹) * u⁻¹, hm⟩ * f₁ ⟨u, hu⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show u * (v * c * v⁻¹) = u * (v * c * v⁻¹) * u⁻¹ * u
    group
  have e3 : f₁ ⟨u * (v * c * v⁻¹) * u⁻¹, hm⟩ = f₁ ⟨c, hc.1⟩ := by
    have h := hcomm
    rw [mul_assoc, e1, ← mul_assoc, e2, mul_assoc] at h
    exact mul_right_cancel h
  have e4 := congrArg Subtype.val (hinj e3)
  simp only at e4
  calc u * v * c = (u * (v * c * v⁻¹) * u⁻¹) * (u * v) := by group
    _ = c * (u * v) := by rw [e4]

end Comm

section Core

variable {D : Type} [Group D] {n : ℕ} {G : Fin n → D} {P1 P2 : Subgroup D} {S1 S2 : Set (Fin n)}
  {K : Subgroup D} {R1 R2 XW YW KW : List (List (Fin n × Bool))} {m : ℕ}

theorem burnsideF48t_core [Finite D] (hF : burnsideF48t_Facts G P1 P2 S1 S2 K R1 R2 XW YW KW m)
    {Y : Type} [Group Y] (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y)
    (h12 : ∀ (t : D) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hinj : Function.Injective f₁)
    (hcard : Nat.card D ≤ Nat.card Y) {x y : D} (hx : x ∈ P1) (hx2 : x ∉ P2)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hxx : x * x ∈ K) (hy : y ∈ P2) (hy1 : y ∉ P1)
    (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hyy : y * y ∈ K)
    (hrel : ∀ k₁ (hk₁ : k₁ ∈ K) k₂ (hk₂ : k₂ ∈ K), ∃ c, ∃ hc : c ∈ K,
      (f₁ ⟨x * k₁, P1.mul_mem hx (hF.K_le hk₁).1⟩ * f₂ ⟨y * k₂, P2.mul_mem hy (hF.K_le hk₂).2⟩) ^ m =
        f₁ ⟨c, (hF.K_le hc).1⟩) :
    ∃ φ : Y ≃* D, (∀ z : ↥P1, φ (f₁ z) = z) ∧ ∀ z : ↥P2, φ (f₂ z) = z := by
  obtain ⟨u, hu, hxu⟩ := hF.xred x hx hx2 hxK hxx
  obtain ⟨v, hv, hyv⟩ := hF.yred y hy hy1 hyK hyy
  set U := burnsideF48s_ev G u with hU
  set V := burnsideF48s_ev G v with hV
  have hk₁ : x⁻¹ * U ∈ K := by
    have := K.inv_mem hxu
    rwa [mul_inv_rev, inv_inv] at this
  have hk₂ : y⁻¹ * V ∈ K := by
    have := K.inv_mem hyv
    rwa [mul_inv_rev, inv_inv] at this
  have eU : x * (x⁻¹ * U) = U := by group
  have eV : y * (y⁻¹ * V) = V := by group
  have hU1 : U ∈ P1 := by rw [hF.hP1]; exact burnsideF48t_ev_mem_closure G (hF.XW_let u hu)
  have hV2 : V ∈ P2 := by rw [hF.hP2]; exact burnsideF48t_ev_mem_closure G (hF.YW_let v hv)
  obtain ⟨c, hcK, hrelc⟩ := hrel _ hk₁ _ hk₂
  have hrel' : (f₁ ⟨U, hU1⟩ * f₂ ⟨V, hV2⟩) ^ m = f₁ ⟨c, (hF.K_le hcK).1⟩ := by
    rw [← hrelc]
    congr 3
    · exact Subtype.ext eU.symm
    · exact Subtype.ext eV.symm
  obtain ⟨cw, hcw, hcwc⟩ := hF.KW_cov c hcK
  have hVK : ∀ k ∈ K, V * k * V⁻¹ ∈ K := by
    intro k hk
    have e : V * k * V⁻¹ = y * ((y⁻¹ * V) * k * (y⁻¹ * V)⁻¹) * y⁻¹ := by group
    rw [e]
    exact hyK _ (K.mul_mem (K.mul_mem hk₂ hk) (K.inv_mem hk₂))
  have hcomm : U * V * c = c * (U * V) := by
    refine burnsideF48t_comm_of f₁ f₂ h12 hinj hU1 hV2 (hF.K_le hcK) (hF.K_le (hVK c hcK)) ?_
    rw [← hrel', ← pow_succ', ← pow_succ]
  have hcomm' : U * V * burnsideF48s_ev G cw = burnsideF48s_ev G cw * (U * V) := by
    rw [hcwc]; exact hcomm
  obtain ⟨hfin, htc⟩ := hF.cand u hu v hv cw hcw hcomm'
  haveI := hfin
  have hlet1 : ∀ l ∈ u, G l.1 ∈ P1 := fun l hl => by
    rw [hF.hP1]; exact burnsideF48t_letter_mem G (hF.XW_let u hu l hl)
  have hlet2 : ∀ l ∈ v, G l.1 ∈ P2 := fun l hl => by
    rw [hF.hP2]; exact burnsideF48t_letter_mem G (hF.YW_let v hv l hl)
  have hletc : ∀ l ∈ cw, G l.1 ∈ P1 := fun l hl => by
    rw [hF.hP1]; exact burnsideF48t_letter_mem G (hF.KW_let cw hcw l hl)
  obtain ⟨mU, eUy⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) u hlet1
  obtain ⟨mV, eVy⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12 v hlet2
  obtain ⟨mC, eCy⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) cw hletc
  set yL := burnsideF48s_yL G f₁ f₂ with hyL
  have hcandY : burnsideF48s_ev yL (burnsideF48s_eCandRel m u v cw) = 1 := by
    unfold burnsideF48s_eCandRel
    rw [burnsideF48s_ev_append, burnsideF48s_ev_replicate, burnsideF48s_ev_append,
      burnsideF48s_e_ev_invW, eUy, eVy, eCy]
    have e1 : f₁ ⟨burnsideF48s_ev G u, mU⟩ = f₁ ⟨U, hU1⟩ := rfl
    have e2 : f₂ ⟨burnsideF48s_ev G v, mV⟩ = f₂ ⟨V, hV2⟩ := rfl
    have e3 : f₁ ⟨burnsideF48s_ev G cw, mC⟩ = f₁ ⟨c, (hF.K_le hcK).1⟩ :=
      congrArg f₁ (Subtype.ext hcwc)
    rw [e1, e2, e3, hrel', mul_inv_cancel]
  have hrelY : ∀ r ∈ R1 ++ R2, burnsideF48s_ev yL r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with hr1 | hr2
    · obtain ⟨hl, h1⟩ := hF.rel1 r hr1
      have hl' : ∀ l ∈ r, G l.1 ∈ P1 := fun l hl'' => by
        rw [hF.hP1]; exact burnsideF48t_letter_mem G (hl l hl'')
      obtain ⟨mr, e⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) r hl'
      rw [e]
      have : (⟨_, mr⟩ : ↥P1) = 1 := Subtype.ext h1
      rw [this, map_one]
    · obtain ⟨hl, h1⟩ := hF.rel2 r hr2
      have hl' : ∀ l ∈ r, G l.1 ∈ P2 := fun l hl'' => by
        rw [hF.hP2]; exact burnsideF48t_letter_mem G (hl l hl'')
      obtain ⟨mr, e⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12 r hl'
      rw [e]
      have : (⟨_, mr⟩ : ↥P2) = 1 := Subtype.ext h1
      rw [this, map_one]
  have hY : ∀ r ∈ burnsideF48s_eWs R1 R2 m u v cw, burnsideF48s_ev yL r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact hrelY r h
    · rw [List.mem_singleton] at h
      rw [h]
      exact hcandY
  have hcov1 : ∀ z ∈ P1, ∃ w : List (Fin n × Bool), (∀ l ∈ w, G l.1 ∈ P1) ∧
      burnsideF48s_ev G w = z := by
    intro z hz
    rw [hF.hP1] at hz
    obtain ⟨w, hw, rfl⟩ := burnsideF48t_closure_cover G S1 z hz
    exact ⟨w, fun l hl => by rw [hF.hP1]; exact burnsideF48t_letter_mem G (hw l hl), rfl⟩
  have hcov2 : ∀ z ∈ P2, ∃ w : List (Fin n × Bool), (∀ l ∈ w, G l.1 ∈ P2) ∧
      burnsideF48s_ev G w = z := by
    intro z hz
    rw [hF.hP2] at hz
    obtain ⟨w, hw, rfl⟩ := burnsideF48t_closure_cover G S2 z hz
    exact ⟨w, fun l hl => by rw [hF.hP2]; exact burnsideF48t_letter_mem G (hw l hl), rfl⟩
  have hYle := burnsideF48s_core_card_le (L := G) (f₁ := f₁) (f₂ := f₂) h12 hgen hcov1 hcov2 hY
  rcases htc with hlt | ⟨hle, hX1⟩
  · exact absurd (hcard.trans hYle) (not_le.2 hlt)
  · have hD : ∀ r ∈ burnsideF48s_eWs R1 R2 m u v cw, burnsideF48s_ev G r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with h | h
      · rcases List.mem_append.1 h with h1 | h2
        · exact (hF.rel1 r h1).2
        · exact (hF.rel2 r h2).2
      · rw [List.mem_singleton] at h
        rw [h]
        exact hX1
    exact burnsideF48s_core_gen h12 hgen hF.sup hcov1 hcov2 hD hY hle hcard

end Core

section Conj

open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF48t_ECore {D : Type} [Group D] (P1 P2 : Subgroup D) (m : ℕ)
    (Q : Subgroup D → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y),
    (∀ (t : D) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩) → f₁.range ⊔ f₂.range = ⊤ →
    Function.Injective f₁ → Nat.card D ≤ Nat.card Y →
    ∀ (K'' : Subgroup D) (hK''le : K'' ≤ P1 ⊓ P2), Q K'' →
    ∀ (x y : D) (hx : x ∈ P1) (hy : y ∈ P2), x ∉ P2 →
      (∀ k ∈ K'', x * k * x⁻¹ ∈ K'') → x * x ∈ K'' → y ∉ P1 →
      (∀ k ∈ K'', y * k * y⁻¹ ∈ K'') → y * y ∈ K'' →
      (∀ k₁ (hk₁ : k₁ ∈ K'') k₂ (hk₂ : k₂ ∈ K''), ∃ c, ∃ hc : c ∈ K'',
        (f₁ ⟨x * k₁, P1.mul_mem hx (hK''le hk₁).1⟩ *
          f₂ ⟨y * k₂, P2.mul_mem hy (hK''le hk₂).2⟩) ^ m = f₁ ⟨c, (hK''le hc).1⟩) →
      ∃ φ : Y ≃* D, (∀ z : ↥P1, φ (f₁ z) = z) ∧ ∀ z : ↥P2, φ (f₂ z) = z

variable {D : Type} [Group D] {n : ℕ} {G : Fin n → D} {P1 P2 : Subgroup D} {S1 S2 : Set (Fin n)}
  {K : Subgroup D} {R1 R2 XW YW KW : List (List (Fin n × Bool))} {m : ℕ}

theorem burnsideF48t_ecore [Finite D] (hF : burnsideF48t_Facts G P1 P2 S1 S2 K R1 R2 XW YW KW m)
    (hconj : ∀ K'' : Subgroup D, K'' ≤ P1 ⊓ P2 → Nat.card ↥K'' = Nat.card ↥K →
      ∃ t ∈ P1 ⊓ P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K) :
    burnsideF48t_ECore P1 P2 m (fun K'' => Nat.card ↥K'' = Nat.card ↥K) := by
  intro Y _ f₁ f₂ h12 hgen hinj hcard K'' hK''le hQ x y hx hy hx2 hxK hxx hy1 hyK hyy hrel
  obtain ⟨t, ht, hiff⟩ := hconj K'' hK''le hQ
  have hconjK : ∀ {z : D}, (∀ k ∈ K'', z * k * z⁻¹ ∈ K'') →
      ∀ k ∈ K, (t * z * t⁻¹) * k * (t * z * t⁻¹)⁻¹ ∈ K := by
    intro z hz k hk
    have h1 : t⁻¹ * k * t ∈ K'' := (hiff _).2 (by simpa [mul_assoc] using hk)
    have h2 := (hiff _).1 (hz _ h1)
    have e : t * (z * (t⁻¹ * k * t) * z⁻¹) * t⁻¹ = (t * z * t⁻¹) * k * (t * z * t⁻¹)⁻¹ := by
      group
    rwa [e] at h2
  have hsq : ∀ {z : D}, z * z ∈ K'' → (t * z * t⁻¹) * (t * z * t⁻¹) ∈ K := by
    intro z hz
    have e : t * (z * z) * t⁻¹ = (t * z * t⁻¹) * (t * z * t⁻¹) := by group
    rw [← e]
    exact (hiff _).1 hz
  have hx' : t * x * t⁻¹ ∈ P1 := P1.mul_mem (P1.mul_mem ht.1 hx) (P1.inv_mem ht.1)
  have hy' : t * y * t⁻¹ ∈ P2 := P2.mul_mem (P2.mul_mem ht.2 hy) (P2.inv_mem ht.2)
  have hx2' : t * x * t⁻¹ ∉ P2 := fun h => hx2 (by
    have := P2.mul_mem (P2.mul_mem (P2.inv_mem ht.2) h) ht.2
    simpa [mul_assoc] using this)
  have hy1' : t * y * t⁻¹ ∉ P1 := fun h => hy1 (by
    have := P1.mul_mem (P1.mul_mem (P1.inv_mem ht.1) h) ht.1
    simpa [mul_assoc] using this)
  have hkK'' : ∀ {k : D}, k ∈ K → t⁻¹ * k * t ∈ K'' := fun hk =>
    (hiff _).2 (by simpa [mul_assoc] using hk)
  have hrel' : ∀ k₁ (hk₁ : k₁ ∈ K) k₂ (hk₂ : k₂ ∈ K), ∃ c, ∃ hc : c ∈ K,
      (f₁ ⟨t * x * t⁻¹ * k₁, P1.mul_mem hx' (hF.K_le hk₁).1⟩ *
        f₂ ⟨t * y * t⁻¹ * k₂, P2.mul_mem hy' (hF.K_le hk₂).2⟩) ^ m =
          f₁ ⟨c, (hF.K_le hc).1⟩ := by
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨c, hc, hrc⟩ := hrel _ (hkK'' hk₁) _ (hkK'' hk₂)
    have hcK : t * c * t⁻¹ ∈ K := (hiff _).1 hc
    refine ⟨t * c * t⁻¹, hcK, ?_⟩
    have e1 : (⟨t * x * t⁻¹ * k₁, P1.mul_mem hx' (hF.K_le hk₁).1⟩ : ↥P1) =
        ⟨t, ht.1⟩ * ⟨x * (t⁻¹ * k₁ * t), P1.mul_mem hx (hK''le (hkK'' hk₁)).1⟩ *
          (⟨t, ht.1⟩ : ↥P1)⁻¹ := Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have e2 : (⟨t * y * t⁻¹ * k₂, P2.mul_mem hy' (hF.K_le hk₂).2⟩ : ↥P2) =
        ⟨t, ht.2⟩ * ⟨y * (t⁻¹ * k₂ * t), P2.mul_mem hy (hK''le (hkK'' hk₂)).2⟩ *
          (⟨t, ht.2⟩ : ↥P2)⁻¹ := Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have e3 : (⟨t * c * t⁻¹, (hF.K_le hcK).1⟩ : ↥P1) =
        ⟨t, ht.1⟩ * ⟨c, (hK''le hc).1⟩ * (⟨t, ht.1⟩ : ↥P1)⁻¹ := rfl
    rw [e1, e2, e3, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_mul, map_mul,
      map_inv, ← h12 t ht]
    have e : f₁ ⟨t, ht.1⟩ * f₁ ⟨x * (t⁻¹ * k₁ * t), P1.mul_mem hx (hK''le (hkK'' hk₁)).1⟩ *
          (f₁ ⟨t, ht.1⟩)⁻¹ *
        (f₁ ⟨t, ht.1⟩ * f₂ ⟨y * (t⁻¹ * k₂ * t), P2.mul_mem hy (hK''le (hkK'' hk₂)).2⟩ *
          (f₁ ⟨t, ht.1⟩)⁻¹) =
        f₁ ⟨t, ht.1⟩ * (f₁ ⟨x * (t⁻¹ * k₁ * t), P1.mul_mem hx (hK''le (hkK'' hk₁)).1⟩ *
          f₂ ⟨y * (t⁻¹ * k₂ * t), P2.mul_mem hy (hK''le (hkK'' hk₂)).2⟩) *
          (f₁ ⟨t, ht.1⟩)⁻¹ := by
      group
    rw [e, conj_pow, hrc]
  exact burnsideF48t_core hF f₁ f₂ h12 hgen hinj hcard hx' hx2' (hconjK hxK) (hsq hxx) hy' hy1'
    (hconjK hyK) (hsq hyy) hrel'

end Conj

end CFSG.ASVolI
