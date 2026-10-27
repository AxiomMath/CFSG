module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFLemA
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFLemB

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

structure FlipHyp (j n : ℕ) where
  P : (Fin j → Fin n → ZMod 2) →+ Matrix (Fin n) (Fin n) (ZMod 2)
  Q : (Fin j → Fin n → ZMod 2) →+ Matrix (Fin n) (Fin n) (ZMod 2)
  S : AddSubgroup (Fin j → Fin n → ZMod 2)
  T : (Fin j → Fin n → ZMod 2) → (Fin j → Fin n → ZMod 2)
  PP : ∀ Y₁ Y₂, P Y₁ * P Y₂ = 0
  P0 : ∃ Y, P Y ≠ 0
  Sm : ∀ Y Y', actM (P Y') Y ∈ S
  Tadd : ∀ s₁ ∈ S, ∀ s₂ ∈ S, T (s₁ + s₂) = T s₁ + T s₂
  Tinj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, T s₁ = T s₂ → s₁ = s₂
  TQ : ∀ Y Y', T (actM (P Y') Y) = actM (Q Y) Y'

namespace FlipHyp

variable {j n : ℕ} (F : FlipHyp j n)

@[expose] def Ue (e : Fin n → ZMod 2) : Set (Fin n → ZMod 2) :=
  Set.range fun Y' => (F.P Y').mulVec e

@[expose] def ImQ (e : Fin n → ZMod 2) (x : Fin j → ZMod 2) : Set (Fin n → ZMod 2) :=
  Set.range fun v => (F.Q (tens e x)).mulVec v

theorem T_zero : F.T 0 = 0 := by
  have h := F.Tadd 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at h
  simpa using h

theorem zero_mem_Ue (e : Fin n → ZMod 2) : (0 : Fin n → ZMod 2) ∈ F.Ue e :=
  ⟨0, by simp⟩

theorem add_mem_Ue (e : Fin n → ZMod 2) {u₁ u₂ : Fin n → ZMod 2} (h₁ : u₁ ∈ F.Ue e)
    (h₂ : u₂ ∈ F.Ue e) : u₁ + u₂ ∈ F.Ue e := by
  obtain ⟨Y₁, rfl⟩ := h₁
  obtain ⟨Y₂, rfl⟩ := h₂
  exact ⟨Y₁ + Y₂, by simp [Matrix.add_mulVec]⟩

theorem tens_mem_S (e : Fin n → ZMod 2) {u : Fin n → ZMod 2} (hu : u ∈ F.Ue e)
    (x : Fin j → ZMod 2) : tens u x ∈ F.S := by
  obtain ⟨Y', rfl⟩ := hu
  rw [← actM_tens]
  exact F.Sm _ _

theorem ncard_Ue_le (hn : n ≤ 5) (e : Fin n → ZMod 2) : (F.Ue e).ncard ≤ 16 := by
  obtain ⟨Y₀, hY₀⟩ := F.P0
  have hsub : F.Ue e ⊆ {v : Fin n → ZMod 2 | (F.P Y₀).mulVec v = 0} := by
    rintro _ ⟨Y', rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [Matrix.mulVec_mulVec, F.PP Y₀ Y', Matrix.zero_mulVec]
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_ker_le hn hY₀)

theorem T_image_eq (e : Fin n → ZMod 2) (x : Fin j → ZMod 2) :
    F.T '' ((fun u => tens u x) '' F.Ue e) = {Y | ∀ i, Y i ∈ F.ImQ e x} := by
  ext Y
  constructor
  · rintro ⟨_, ⟨u, ⟨Y', rfl⟩, rfl⟩, rfl⟩
    intro i
    have h : tens ((F.P Y').mulVec e) x = actM (F.P Y') (tens e x) := (actM_tens _ _ _).symm
    show F.T (tens ((F.P Y').mulVec e) x) i ∈ F.ImQ e x
    rw [h, F.TQ]
    exact ⟨Y' i, rfl⟩
  · intro hY
    have h1 : Y ∈ Set.range (fun Y' : Fin j → Fin n → ZMod 2 => actM (F.Q (tens e x)) Y') := by
      rw [range_actM_eq]
      exact hY
    obtain ⟨Y', hY'⟩ := h1
    refine ⟨tens ((F.P Y').mulVec e) x, ⟨(F.P Y').mulVec e, ⟨Y', rfl⟩, rfl⟩, ?_⟩
    rw [← actM_tens, F.TQ]
    exact hY'

theorem ncard_Ue_eq (e : Fin n → ZMod 2) {x : Fin j → ZMod 2} (hx : x ≠ 0) :
    (F.Ue e).ncard = (F.ImQ e x).ncard ^ j := by
  have hinj : Set.InjOn F.T ((fun u => tens u x) '' F.Ue e) := by
    rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ h
    exact F.Tinj _ (F.tens_mem_S e hu₁ x) _ (F.tens_mem_S e hu₂ x) h
  calc (F.Ue e).ncard = ((fun u => tens u x) '' F.Ue e).ncard :=
        (Set.ncard_image_of_injective _ (tens_left_injective hx)).symm
    _ = (F.T '' ((fun u => tens u x) '' F.Ue e)).ncard := hinj.ncard_image.symm
    _ = {Y : Fin j → Fin n → ZMod 2 | ∀ i, Y i ∈ F.ImQ e x}.ncard := by rw [F.T_image_eq]
    _ = (F.ImQ e x).ncard ^ j := ncard_colSet _


theorem ncard_ImQ_le_two (hj : 3 ≤ j) (hn : n ≤ 5) (e : Fin n → ZMod 2) {x : Fin j → ZMod 2}
    (hx : x ≠ 0) : (F.ImQ e x).ncard ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have h1 := F.ncard_Ue_eq e hx
  have h2 := F.ncard_Ue_le hn e
  have h3 : 3 ≤ (F.ImQ e x).ncard := hcon
  have h4 : 3 ^ 3 ≤ (F.ImQ e x).ncard ^ 3 := Nat.pow_le_pow_left h3 3
  have h5 : (F.ImQ e x).ncard ^ 3 ≤ (F.ImQ e x).ncard ^ j :=
    Nat.pow_le_pow_right (by omega) hj
  omega

theorem exists_nonzero_Ue : ∃ e : Fin n → ZMod 2, ∃ u ∈ F.Ue e, u ≠ 0 := by
  obtain ⟨Y₀, hY₀⟩ := F.P0
  obtain ⟨b, hb⟩ := exists_ne_zero_mulVec hY₀
  exact ⟨Pi.single b 1, (F.P Y₀).mulVec (Pi.single b 1), ⟨Y₀, rfl⟩, hb⟩

theorem zero_mem_ImQ (e : Fin n → ZMod 2) (x : Fin j → ZMod 2) :
    (0 : Fin n → ZMod 2) ∈ F.ImQ e x :=
  ⟨0, by simp⟩

theorem ncard_ImQ_eq_two (hj : 3 ≤ j) (hn : n ≤ 5) {e : Fin n → ZMod 2} {u₀ : Fin n → ZMod 2}
    (hu₀ : u₀ ∈ F.Ue e) (hne : u₀ ≠ 0) {x : Fin j → ZMod 2} (hx : x ≠ 0) :
    (F.ImQ e x).ncard = 2 := by
  have hle := F.ncard_ImQ_le_two hj hn e hx
  have h1 := F.ncard_Ue_eq e hx
  have hpair : ({0, u₀} : Set (Fin n → ZMod 2)).ncard = 2 :=
    Set.ncard_pair (Ne.symm hne)
  have hsub : ({0, u₀} : Set (Fin n → ZMod 2)) ⊆ F.Ue e := by
    intro v hv
    rcases hv with rfl | rfl
    · exact F.zero_mem_Ue e
    · exact hu₀
  have h2 : 2 ≤ (F.Ue e).ncard :=
    calc (2 : ℕ) = ({0, u₀} : Set (Fin n → ZMod 2)).ncard := hpair.symm
      _ ≤ (F.Ue e).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h1] at h2
  by_contra hne2
  have hc : (F.ImQ e x).ncard ≤ 1 := by omega
  have h3 : (F.ImQ e x).ncard ^ j ≤ 1 := by
    calc (F.ImQ e x).ncard ^ j ≤ 1 ^ j := Nat.pow_le_pow_left hc j
      _ = 1 := one_pow j
  omega

theorem ncard_Ue_eq_pow (hj : 3 ≤ j) (hn : n ≤ 5) {e : Fin n → ZMod 2} {u₀ : Fin n → ZMod 2}
    (hu₀ : u₀ ∈ F.Ue e) (hne : u₀ ≠ 0) : (F.Ue e).ncard = 2 ^ j := by
  have hx : (Pi.single ⟨0, by omega⟩ 1 : Fin j → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  rw [F.ncard_Ue_eq e hx, F.ncard_ImQ_eq_two hj hn hu₀ hne hx]

theorem exists_good (hj : 3 ≤ j) (hn : n ≤ 5) {e : Fin n → ZMod 2} {u₀ : Fin n → ZMod 2}
    (hu₀ : u₀ ∈ F.Ue e) (hne : u₀ ≠ 0) {x : Fin j → ZMod 2} (hx : x ≠ 0) :
    ∃ a : Fin n → ZMod 2, a ≠ 0 ∧ ∀ v, v ∈ F.ImQ e x ↔ v = 0 ∨ v = a :=
  exists_ne_zero_of_ncard_two (F.zero_mem_ImQ e x) (F.ncard_ImQ_eq_two hj hn hu₀ hne hx)

theorem T_tens_mem {e : Fin n → ZMod 2} {u : Fin n → ZMod 2} (hu : u ∈ F.Ue e)
    {x : Fin j → ZMod 2} {a : Fin n → ZMod 2} (ha : a ≠ 0)
    (haIm : ∀ v, v ∈ F.ImQ e x ↔ v = 0 ∨ v = a) : ∃ t, F.T (tens u x) = tens a t := by
  have h1 : F.T (tens u x) ∈ {Y : Fin j → Fin n → ZMod 2 | ∀ i, Y i ∈ F.ImQ e x} := by
    rw [← F.T_image_eq]
    exact ⟨tens u x, ⟨u, hu, rfl⟩, rfl⟩
  have h2 : F.T (tens u x) ∈ {Y : Fin j → Fin n → ZMod 2 | ∀ i, Y i = 0 ∨ Y i = a} := by
    intro i
    exact (haIm _).mp (h1 i)
  rw [colSet_two_eq_range_tens ha] at h2
  obtain ⟨t, ht⟩ := h2
  exact ⟨t, ht.symm⟩


structure GoodChoice (e : Fin n → ZMod 2) (a : (Fin j → ZMod 2) → (Fin n → ZMod 2))
    (θ₀ : (Fin n → ZMod 2) → (Fin j → ZMod 2) → (Fin j → ZMod 2)) : Prop where
  a_ne : ∀ x, x ≠ 0 → a x ≠ 0
  hθ : ∀ u ∈ F.Ue e, ∀ x, x ≠ 0 → F.T (tens u x) = tens (a x) (θ₀ u x)

theorem vec_add_self_nsbfa {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 := by
  funext i
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  exact h _

theorem vec_neg_self_nsbfa {k : ℕ} (x : Fin k → ZMod 2) : -x = x := by
  funext i
  have h : ∀ c : ZMod 2, -c = c := by decide
  exact h _

theorem exists_goodChoice (hj : 3 ≤ j) (hn : n ≤ 5) {e u₀ : Fin n → ZMod 2} (hu₀ : u₀ ∈ F.Ue e)
    (hne : u₀ ≠ 0) : ∃ a θ₀, F.GoodChoice e a θ₀ := by
  have h1 : ∀ x : Fin j → ZMod 2, ∃ a : Fin n → ZMod 2,
      x ≠ 0 → (a ≠ 0 ∧ ∀ v, v ∈ F.ImQ e x ↔ v = 0 ∨ v = a) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨a, ha⟩ := F.exists_good hj hn hu₀ hne hx
      exact ⟨a, fun _ => ha⟩
  choose a ha using h1
  have h2 : ∀ (u : Fin n → ZMod 2) (x : Fin j → ZMod 2), ∃ t : Fin j → ZMod 2,
      u ∈ F.Ue e → x ≠ 0 → F.T (tens u x) = tens (a x) t := by
    intro u x
    by_cases h : u ∈ F.Ue e ∧ x ≠ 0
    · obtain ⟨t, ht⟩ := F.T_tens_mem h.1 (ha x h.2).1 (ha x h.2).2
      exact ⟨t, fun _ _ => ht⟩
    · exact ⟨0, fun hu hx => absurd ⟨hu, hx⟩ h⟩
  choose θ₀ hθ using h2
  exact ⟨a, θ₀, ⟨fun x hx => (ha x hx).1, fun u hu x hx => hθ u x hu hx⟩⟩

variable {F} {e : Fin n → ZMod 2} {a : (Fin j → ZMod 2) → (Fin n → ZMod 2)}
  {θ₀ : (Fin n → ZMod 2) → (Fin j → ZMod 2) → (Fin j → ZMod 2)}

theorem GoodChoice.theta_ne_zero (G : F.GoodChoice e a θ₀) {u : Fin n → ZMod 2}
    (hu : u ∈ F.Ue e) (hu0 : u ≠ 0) {x : Fin j → ZMod 2} (hx : x ≠ 0) : θ₀ u x ≠ 0 := by
  intro h0
  have h1 := G.hθ u hu x hx
  rw [h0, tens_zero_right] at h1
  have h2 : tens u x = 0 :=
    F.Tinj _ (F.tens_mem_S e hu x) 0 (zero_mem _) (by rw [h1, F.T_zero])
  rcases (tens_eq_zero_iff u x).mp h2 with h | h
  · exact hu0 h
  · exact hx h

theorem GoodChoice.theta_zero (G : F.GoodChoice e a θ₀) {x : Fin j → ZMod 2} (hx : x ≠ 0) :
    θ₀ 0 x = 0 := by
  have h1 := G.hθ 0 (F.zero_mem_Ue e) x hx
  rw [tens_zero_left, F.T_zero] at h1
  have h2 : tens (a x) (θ₀ 0 x) = tens (a x) 0 := by rw [← h1, tens_zero_right]
  exact tens_right_injective (G.a_ne x hx) h2

theorem GoodChoice.a_ne_of_ne (G : F.GoodChoice e a θ₀) (hj : 3 ≤ j)
    (hUe : (F.Ue e).ncard = 2 ^ j) {x₁ x₂ : Fin j → ZMod 2} (h1 : x₁ ≠ 0) (h2 : x₂ ≠ 0)
    (h12 : x₁ ≠ x₂) : a x₁ ≠ a x₂ := by
  intro hEq
  set E : Set (Fin j → Fin n → ZMod 2) :=
    (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) => tens p.1 x₁ + tens p.2 x₂) ''
      (F.Ue e ×ˢ F.Ue e) with hE
  have hEcard : E.ncard = 2 ^ j * 2 ^ j := by
    have hinj := tens_pair_injective (n := n) h1 h2 h12
    rw [hE, Set.ncard_image_of_injective _ hinj, Set.ncard_prod, hUe]
  have hES : ∀ Y ∈ E, Y ∈ F.S := by
    rintro _ ⟨⟨u₁, u₂⟩, ⟨hu₁, hu₂⟩, rfl⟩
    exact add_mem (F.tens_mem_S e hu₁ x₁) (F.tens_mem_S e hu₂ x₂)
  have hTinjE : Set.InjOn F.T E := fun y₁ hy₁ y₂ hy₂ h =>
    F.Tinj _ (hES _ hy₁) _ (hES _ hy₂) h
  have hsub : F.T '' E ⊆ Set.range (fun t : Fin j → ZMod 2 => tens (a x₁) t) := by
    rintro _ ⟨_, ⟨⟨u₁, u₂⟩, ⟨hu₁, hu₂⟩, rfl⟩, rfl⟩
    refine ⟨θ₀ u₁ x₁ + θ₀ u₂ x₂, ?_⟩
    show tens (a x₁) (θ₀ u₁ x₁ + θ₀ u₂ x₂) = F.T (tens u₁ x₁ + tens u₂ x₂)
    rw [F.Tadd _ (F.tens_mem_S e hu₁ x₁) _ (F.tens_mem_S e hu₂ x₂), G.hθ u₁ hu₁ x₁ h1,
      G.hθ u₂ hu₂ x₂ h2, ← hEq, tens_add_right]
  have hle : E.ncard ≤ 2 ^ j := by
    calc E.ncard = (F.T '' E).ncard := hTinjE.ncard_image.symm
      _ ≤ (Set.range (fun t : Fin j → ZMod 2 => tens (a x₁) t)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = 2 ^ j := ncard_range_tens (G.a_ne x₁ h1)
  rw [hEcard] at hle
  have h8 : 8 ≤ 2 ^ j := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  nlinarith

theorem GoodChoice.flip_rel (G : F.GoodChoice e a θ₀) (hj : 3 ≤ j)
    (hUe : (F.Ue e).ncard = 2 ^ j) {u : Fin n → ZMod 2} (hu : u ∈ F.Ue e) (hu0 : u ≠ 0)
    {x₁ x₂ : Fin j → ZMod 2} (h1 : x₁ ≠ 0) (h2 : x₂ ≠ 0) (h12 : x₁ ≠ x₂) :
    θ₀ u x₁ = θ₀ u x₂ ∧ θ₀ u x₂ = θ₀ u (x₁ + x₂) ∧ a (x₁ + x₂) = a x₁ + a x₂ := by
  have h3 : x₁ + x₂ ≠ 0 := by
    intro h
    apply h12
    have : x₁ = -x₂ := eq_neg_of_add_eq_zero_left h
    rw [this, vec_neg_self_nsbfa]
  have hT : F.T (tens u (x₁ + x₂)) = F.T (tens u x₁) + F.T (tens u x₂) := by
    rw [tens_add_right]
    exact F.Tadd _ (F.tens_mem_S e hu x₁) _ (F.tens_mem_S e hu x₂)
  rw [G.hθ u hu _ h3, G.hθ u hu _ h1, G.hθ u hu _ h2] at hT
  have hane := G.a_ne_of_ne hj hUe h1 h2 h12
  exact rank_one_sum (G.a_ne x₁ h1) (G.a_ne x₂ h2) hane (G.a_ne _ h3)
    (G.theta_ne_zero hu hu0 h1) (G.theta_ne_zero hu hu0 h2) (G.theta_ne_zero hu hu0 h3) hT.symm


theorem flip_structure (F : FlipHyp j n) (hj : 3 ≤ j) (hn : n ≤ 5) :
    ∃ (U : AddSubgroup (Fin n → ZMod 2)) (ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2))
      (θ : (Fin n → ZMod 2) → (Fin j → ZMod 2)),
      Nat.card U = 2 ^ j ∧ Function.Injective ι ∧
        ∀ u ∈ U, ∀ x : Fin j → ZMod 2, tens u x ∈ F.S ∧ F.T (tens u x) = tens (ι x) (θ u) := by
  classical
  obtain ⟨e, u₀, hu₀, hne⟩ := F.exists_nonzero_Ue
  obtain ⟨a, θ₀, G⟩ := F.exists_goodChoice hj hn hu₀ hne
  have hUe := F.ncard_Ue_eq_pow hj hn hu₀ hne
  set xs : Fin j → ZMod 2 := Pi.single ⟨0, by omega⟩ 1 with hxs
  have hxs0 : xs ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp [hxs] at this
  let U : AddSubgroup (Fin n → ZMod 2) :=
    { carrier := F.Ue e
      add_mem' := fun {u₁ u₂} h₁ h₂ => F.add_mem_Ue e h₁ h₂
      zero_mem' := F.zero_mem_Ue e
      neg_mem' := fun {u} hu => by convert hu using 1; exact vec_neg_self_nsbfa u }
  let ι₀ : (Fin j → ZMod 2) → (Fin n → ZMod 2) := fun x => if x = 0 then 0 else a x
  have hι₀ : ∀ x₁ x₂, ι₀ (x₁ + x₂) = ι₀ x₁ + ι₀ x₂ := by
    intro x₁ x₂
    by_cases h1 : x₁ = 0
    · simp [ι₀, h1]
    by_cases h2 : x₂ = 0
    · simp [ι₀, h2]
    by_cases h12 : x₁ = x₂
    · subst h12
      simp [ι₀, h1, vec_add_self_nsbfa]
    · have h3 : x₁ + x₂ ≠ 0 := by
        intro h
        apply h12
        have : x₁ = -x₂ := eq_neg_of_add_eq_zero_left h
        rw [this, vec_neg_self_nsbfa]
      have := (G.flip_rel hj hUe hu₀ hne h1 h2 h12).2.2
      simp [ι₀, h1, h2, h3, this]
  let ι : (Fin j → ZMod 2) →+ (Fin n → ZMod 2) := AddMonoidHom.mk' ι₀ hι₀
  have hιapp : ∀ x, ι x = ι₀ x := fun x => rfl
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    rw [hιapp] at hx
    simp only [ι₀, if_neg hx0] at hx
    exact G.a_ne x hx0 hx
  have hθ : ∀ u ∈ F.Ue e, ∀ x, x ≠ 0 → θ₀ u x = θ₀ u xs := by
    intro u hu x hx
    by_cases hu0 : u = 0
    · subst hu0
      rw [G.theta_zero hx, G.theta_zero hxs0]
    · by_cases hxx : x = xs
      · rw [hxx]
      · exact (G.flip_rel hj hUe hu hu0 hx hxs0 hxx).1
  refine ⟨U, ι, fun u => θ₀ u xs, ?_, hιinj, ?_⟩
  · have : Nat.card U = (F.Ue e).ncard := Nat.card_coe_set_eq (F.Ue e)
    rw [this, hUe]
  · intro u hu x
    refine ⟨F.tens_mem_S e hu x, ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [tens_zero_right, F.T_zero, hιapp]
      simp [ι₀, tens_zero_left]
    · rw [G.hθ u hu x hx, hθ u hu x hx, hιapp]
      simp [ι₀, hx]

end FlipHyp

end CFSG.Quasithin.H13.Ch4.NSB
