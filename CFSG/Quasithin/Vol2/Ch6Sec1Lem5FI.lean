module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FE
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FF

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique

section DirectProduct

variable {Γ : Type*} [Group Γ] {G₁ G₂ : Subgroup Γ}

@[expose] def IsIndec_ch615 (G₁ : Subgroup Γ) : Prop :=
  ∀ A B : Subgroup Γ, A ≤ G₁ → B ≤ G₁ → (∀ g ∈ G₁, ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
    (∀ g ∈ G₁, ∀ b ∈ B, g * b * g⁻¹ ∈ B) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → A ⊓ B = ⊥ →
    G₁ ≤ A ⊔ B → A = ⊥ ∨ B = ⊥

@[expose] def projL_ch615 (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (N : Subgroup Γ) :
    Subgroup Γ where
  carrier := {a | a ∈ G₁ ∧ ∃ b ∈ G₂, a * b ∈ N}
  one_mem' := ⟨G₁.one_mem, 1, G₂.one_mem, by simp⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨G₁.mul_mem ha ha', b * b', G₂.mul_mem hb hb', ?_⟩
    have e : a * a' * (b * b') = a * b * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
        _ = a * b * (a' * b') := by group
    rw [e]
    exact N.mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨G₁.inv_mem ha, b⁻¹, G₂.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      rw [mul_inv_rev, ← (hc a⁻¹ (G₁.inv_mem ha) b⁻¹ (G₂.inv_mem hb))]
    rw [e]
    exact N.inv_mem hab

theorem mem_projL_ch615 {hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a} {N : Subgroup Γ} {a : Γ} :
    a ∈ projL_ch615 hc N ↔ a ∈ G₁ ∧ ∃ b ∈ G₂, a * b ∈ N := Iff.rfl

theorem le_or_le_of_isIndec_ch615 (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hinf : G₁ ⊓ G₂ = ⊥) (hZ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1)
    (hind : IsIndec_ch615 G₁) {N₁ N₂ : Subgroup Γ} (hN₁ : N₁ ≤ G₁ ⊔ G₂) (hN₂ : N₂ ≤ G₁ ⊔ G₂)
    (hn₁ : ∀ g ∈ G₁, ∀ n ∈ N₁, g * n * g⁻¹ ∈ N₁) (hn₂ : ∀ g ∈ G₁, ∀ n ∈ N₂, g * n * g⁻¹ ∈ N₂)
    (hc₁₂ : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hsup : G₁ ≤ N₁ ⊔ N₂) :
    N₁ ≤ G₂ ∨ N₂ ≤ G₂ := by
  have hdec : ∀ n ∈ G₁ ⊔ G₂, ∃ a ∈ G₁, ∃ b ∈ G₂, a * b = n := fun n hn =>
    (mem_sup_iff_of_commute_ch615 hc).mp hn
  have hnorm : ∀ N : Subgroup Γ, (∀ g ∈ G₁, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      ∀ g ∈ G₁, ∀ a ∈ projL_ch615 hc N, g * a * g⁻¹ ∈ projL_ch615 hc N := by
    rintro N hn g hg a ⟨ha, b, hb, hab⟩
    refine ⟨G₁.mul_mem (G₁.mul_mem hg ha) (G₁.inv_mem hg), b, hb, ?_⟩
    have hgb := hc g⁻¹ (G₁.inv_mem hg) b hb
    have e : g * a * g⁻¹ * b = g * (a * b) * g⁻¹ := by
      calc g * a * g⁻¹ * b = g * a * (g⁻¹ * b) := by group
        _ = g * a * (b * g⁻¹) := by rw [hgb]
        _ = g * (a * b) * g⁻¹ := by group
    rw [e]
    exact hn g hg _ hab
  have hAB : ∀ a ∈ projL_ch615 hc N₁, ∀ a' ∈ projL_ch615 hc N₂, a * a' = a' * a := by
    rintro a ⟨ha, b, hb, hab⟩ a' ⟨ha', b', hb', hab'⟩
    have h1 := hc₁₂ _ hab _ hab'
    have e1 : a * b * (a' * b') = a * a' * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [hc a' ha' b hb]
        _ = a * a' * (b * b') := by group
    have e2 : a' * b' * (a * b) = a' * a * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [hc a ha b' hb']
        _ = a' * a * (b' * b) := by group
    rw [e1, e2] at h1
    exact (Lin2.unique_decomp hinf (G₁.mul_mem ha ha') (G₁.mul_mem ha' ha) (G₂.mul_mem hb hb')
      (G₂.mul_mem hb' hb) h1).1
  have hGAB : G₁ ≤ projL_ch615 hc N₁ ⊔ projL_ch615 hc N₂ := by
    intro g hg
    obtain ⟨n₁, hn₁', n₂, hn₂', rfl⟩ := (mem_sup_iff_of_commute_ch615 hc₁₂).mp (hsup hg)
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdec n₁ (hN₁ hn₁')
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hdec n₂ (hN₂ hn₂')
    have e : a₁ * b₁ * (a₂ * b₂) = a₁ * a₂ * (b₁ * b₂) := by
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [hc a₂ ha₂ b₁ hb₁]
        _ = a₁ * a₂ * (b₁ * b₂) := by group
    have hu := Lin2.unique_decomp hinf (G₁.mul_mem ha₁ ha₂) hg (G₂.mul_mem hb₁ hb₂) G₂.one_mem
      (e.symm.trans (mul_one _).symm)
    rw [← hu.1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha₁, b₁, hb₁, hn₁'⟩)
      (Subgroup.mem_sup_right ⟨ha₂, b₂, hb₂, hn₂'⟩)
  have hinfAB : projL_ch615 hc N₁ ⊓ projL_ch615 hc N₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haA, haB⟩
    rw [Subgroup.mem_bot]
    refine hZ a haA.1 fun x hx => ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := (mem_sup_iff_of_commute_ch615 hAB).mp (hGAB hx)
    have h1 := hAB y hy a haB
    have h2 := hAB a haA z hz
    calc a * (y * z) = a * y * z := by group
      _ = y * a * z := by rw [h1]
      _ = y * (a * z) := by group
      _ = y * (z * a) := by rw [h2]
      _ = y * z * a := by group
  rcases hind _ _ (fun a ha => (mem_projL_ch615.mp ha).1) (fun a ha => (mem_projL_ch615.mp ha).1)
    (hnorm N₁ hn₁) (hnorm N₂ hn₂) hAB hinfAB hGAB with hA | hB
  · left
    intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec n (hN₁ hn)
    have ha1 : a ∈ projL_ch615 hc N₁ := ⟨ha, b, hb, hn⟩
    rw [hA, Subgroup.mem_bot] at ha1
    rw [ha1, one_mul]
    exact hb
  · right
    intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec n (hN₂ hn)
    have ha1 : a ∈ projL_ch615 hc N₂ := ⟨ha, b, hb, hn⟩
    rw [hB, Subgroup.mem_bot] at ha1
    rw [ha1, one_mul]
    exact hb

theorem map_conj_eq_or_swap_ch615 [Finite Γ] (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hinf : G₁ ⊓ G₂ = ⊥) (hZ₁ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1)
    (hZ₂ : ∀ g ∈ G₂, (∀ x ∈ G₂, g * x = x * g) → g = 1) (hind₁ : IsIndec_ch615 G₁)
    (hind₂ : IsIndec_ch615 G₂) (h₁ : G₁ ≠ ⊥) (h₂ : G₂ ≠ ⊥) {x : Γ}
    (hx : x ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Γ) : Set Γ)) :
    (G₁.map (MulAut.conj x).toMonoidHom = G₁ ∧ G₂.map (MulAut.conj x).toMonoidHom = G₂) ∨
      (G₁.map (MulAut.conj x).toMonoidHom = G₂ ∧ G₂.map (MulAut.conj x).toMonoidHom = G₁) := by
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hxi : x⁻¹ ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Γ) : Set Γ) :=
    Subgroup.inv_mem _ hx
  set N₁ := G₁.map (MulAut.conj x).toMonoidHom with hN₁def
  set N₂ := G₂.map (MulAut.conj x).toMonoidHom with hN₂def
  have hle : ∀ Gi : Subgroup Γ, Gi ≤ G₁ ⊔ G₂ → Gi.map (MulAut.conj x).toMonoidHom ≤ G₁ ⊔ G₂ := by
    rintro Gi hGi _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx _).mp (hGi ha)
  have hnorm : ∀ Gi : Subgroup Γ, G₁ ⊔ G₂ ≤ Subgroup.normalizer (Gi : Set Γ) →
      ∀ g ∈ G₁ ⊔ G₂, ∀ n ∈ Gi.map (MulAut.conj x).toMonoidHom,
        g * n * g⁻¹ ∈ Gi.map (MulAut.conj x).toMonoidHom := by
    rintro Gi hGi g hg _ ⟨a, ha, rfl⟩
    have hg' : x⁻¹ * g * x⁻¹⁻¹ ∈ G₁ ⊔ G₂ := (Subgroup.mem_normalizer_iff.mp hxi g).mp hg
    rw [inv_inv] at hg'
    refine ⟨_, (Subgroup.mem_normalizer_iff.mp (hGi hg') a).mp ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hN₁G : N₁ ≤ G₁ ⊔ G₂ := hle G₁ le_sup_left
  have hN₂G : N₂ ≤ G₁ ⊔ G₂ := hle G₂ le_sup_right
  have hG₂n : G₁ ⊔ G₂ ≤ Subgroup.normalizer (G₂ : Set Γ) := by
    rw [sup_comm]
    exact sup_le_normalizer_ch615 hc'
  have hn₁ := hnorm G₁ (sup_le_normalizer_ch615 hc)
  have hn₂ := hnorm G₂ hG₂n
  have hc₁₂ : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hc a ha b hb
    calc x * a * x⁻¹ * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
      _ = x * (b * a) * x⁻¹ := by rw [this]
      _ = x * b * x⁻¹ * (x * a * x⁻¹) := by group
  have hsup : G₁ ⊔ G₂ ≤ N₁ ⊔ N₂ := by
    intro g hg
    have hg' : x⁻¹ * g * x⁻¹⁻¹ ∈ G₁ ⊔ G₂ := (Subgroup.mem_normalizer_iff.mp hxi g).mp hg
    rw [inv_inv] at hg'
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_commute_ch615 hc).mp hg'
    have e : g = (x * a * x⁻¹) * (x * b * x⁻¹) := by
      calc g = x * (x⁻¹ * g * x) * x⁻¹ := by group
        _ = x * (a * b) * x⁻¹ := by rw [hab]
        _ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, ha, rfl⟩)
      (Subgroup.mem_sup_right ⟨b, hb, rfl⟩)
  have hc₂₁ : ∀ a ∈ N₂, ∀ b ∈ N₁, a * b = b * a := fun a ha b hb => (hc₁₂ b hb a ha).symm
  have hcard₁ : Nat.card N₁ = Nat.card G₁ :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hcard₂ : Nat.card N₂ = Nat.card G₂ :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hne : ∀ N Gi : Subgroup Γ, Nat.card N = Nat.card Gi → Gi ≠ ⊥ → N ≠ ⊥ := by
    intro N Gi h hGi hN
    rw [hN, Subgroup.card_bot] at h
    exact hGi (Subgroup.eq_bot_of_card_eq Gi h.symm)
  have hA := le_or_le_of_isIndec_ch615 hc hinf hZ₁ hind₁ hN₁G hN₂G
    (fun g hg n hn => hn₁ g (Subgroup.mem_sup_left hg) n hn)
    (fun g hg n hn => hn₂ g (Subgroup.mem_sup_left hg) n hn) hc₁₂ (le_sup_left.trans hsup)
  have hB := le_or_le_of_isIndec_ch615 hc' hinf' hZ₂ hind₂ (sup_comm G₁ G₂ ▸ hN₁G)
    (sup_comm G₁ G₂ ▸ hN₂G) (fun g hg n hn => hn₁ g (Subgroup.mem_sup_right hg) n hn)
    (fun g hg n hn => hn₂ g (Subgroup.mem_sup_right hg) n hn) hc₁₂ (le_sup_right.trans hsup)
  rcases hA with h1 | h1 <;> rcases hB with h2 | h2
  · exfalso
    exact hne N₁ G₁ hcard₁ h₁ (by rw [eq_bot_iff, ← hinf]; exact le_inf h2 h1)
  · right
    have c1 : Nat.card G₁ ≤ Nat.card G₂ := hcard₁ ▸ Subgroup.card_le_of_le h1
    have c2 : Nat.card G₂ ≤ Nat.card G₁ := hcard₂ ▸ Subgroup.card_le_of_le h2
    exact ⟨Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard₁]; omega),
      Subgroup.eq_of_le_of_card_ge h2 (by rw [hcard₂]; omega)⟩
  · left
    refine ⟨Subgroup.eq_of_le_of_card_ge h2 (by rw [hcard₁]),
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard₂])⟩
  · exfalso
    exact hne N₂ G₂ hcard₂ h₂ (by rw [eq_bot_iff, ← hinf]; exact le_inf h2 h1)

theorem isIndec_of_isSimpleGroup_ch615 (hs : IsSimpleGroup ↥G₁)
    (hZ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1) : IsIndec_ch615 G₁ := by
  intro A B hA hB hnA _ hAB _ _
  have hAn : (A.subgroupOf G₁).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnA g g.2 n hn⟩
  rcases hAn.eq_bot_or_eq_top with h | h
  · left
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hA ha⟩ : ↥G₁) ∈ A.subgroupOf G₁ := ha
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · right
    rw [eq_bot_iff]
    intro b hb
    refine Subgroup.mem_bot.mpr (hZ b (hB hb) fun x hx => ?_)
    have hxA : x ∈ A := by
      have : (⟨x, hx⟩ : ↥G₁) ∈ A.subgroupOf G₁ := h ▸ Subgroup.mem_top _
      exact this
    exact (hAB x hxA b hb).symm

theorem eq_bot_of_card_two_ch615 [Finite Γ] (hZ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1)
    {C : Subgroup Γ} (hC : C ≤ G₁) (hnC : ∀ g ∈ G₁, ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    (h2 : Nat.card C = 2) : False := by
  classical
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp (fun h => by
    rw [h, Subgroup.card_bot] at h2; omega) : ∃ c : ↥C, c ≠ 1)
  have hcz := hZ c (hC c.2) fun x hx => by
    by_contra hne
    have h1 : (⟨x * c * x⁻¹, hnC x hx c c.2⟩ : ↥C) ≠ 1 := fun h => hc1 (Subtype.ext (by
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_one] at this
      have : (c : Γ) = x⁻¹ * (x * c * x⁻¹) * x := by group
      rw [this, show x * (c : Γ) * x⁻¹ = 1 from by
        simpa using congrArg Subtype.val h, mul_one, inv_mul_cancel]; rfl))
    have h2' : (⟨x * c * x⁻¹, hnC x hx c c.2⟩ : ↥C) ≠ c := fun h => hne (by
      have := congrArg Subtype.val h
      simp only at this
      exact (calc x * (c : Γ) = x * c * x⁻¹ * x := by group
        _ = c * x := by rw [this]).symm)
    have hcard : 3 ≤ Nat.card ↥C := by
      have := Fintype.ofFinite ↥C
      have hs : ({1, c, ⟨x * c * x⁻¹, hnC x hx c c.2⟩} : Finset ↥C).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h2')]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hc1, Ne.symm h1⟩
      rw [← hs, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    omega
  exact hc1 (Subtype.ext hcz)

theorem isIndec_of_card_six_ch615 [Finite Γ] (h6 : Nat.card G₁ = 6)
    (hZ : ∀ g ∈ G₁, (∀ x ∈ G₁, g * x = x * g) → g = 1) : IsIndec_ch615 G₁ := by
  intro A B hA hB hnA hnB hAB hinf hsup
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).1
  rw [le_antisymm (sup_le hA hB) hsup, hinf, Subgroup.card_bot, mul_one, h6] at hcard
  by_contra hne
  obtain ⟨hA1, hB1⟩ := not_or.mp hne
  have hA2 : Nat.card A ≠ 1 := fun h => hA1 (Subgroup.eq_bot_of_card_eq A h)
  have hB2 : Nat.card B ≠ 1 := fun h => hB1 (Subgroup.eq_bot_of_card_eq B h)
  have hAd : Nat.card A ∣ 6 := ⟨_, hcard⟩
  have hBd : Nat.card B ∣ 6 := ⟨_, hcard.trans (mul_comm _ _)⟩
  have hApos := Nat.card_pos (α := A)
  have hBpos := Nat.card_pos (α := B)
  have hA6 : Nat.card A ≤ 6 := Nat.le_of_dvd (by norm_num) hAd
  have hB6 : Nat.card B ≤ 6 := Nat.le_of_dvd (by norm_num) hBd
  interval_cases hca : Nat.card A <;> interval_cases hcb : Nat.card B <;> try omega
  · exact eq_bot_of_card_two_ch615 hZ hA hnA hca
  · exact eq_bot_of_card_two_ch615 hZ hB hnB hcb

theorem mem_zpowers_of_pow_prime_ch615 {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {p : ℕ}
    (hp : p.Prime) {w z : Q} (hwp : w ^ p = 1) (hw1 : w ≠ 1) (hzp : z ^ p = 1) :
    z ∈ Subgroup.zpowers w := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hz1 : z = 1
  · rw [hz1]
    exact Subgroup.one_mem _
  have hw := orderOf_eq_prime hwp hw1
  have hz := orderOf_eq_prime hzp hz1
  have : Subgroup.zpowers z = Subgroup.zpowers w :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hw, hz])
  rw [← this]
  exact Subgroup.mem_zpowers z

theorem exists_mem_of_not_le_centralizer_ch615 [Finite Γ] {F Y B D S : Subgroup Γ}
    (hout : ∀ α : MulAut ↥F, Odd (orderOf α) → ∃ g : ↥F, α = MulAut.conj g)
    (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hS2 : IsPGroup 2 S) (hSF : S ≤ F) (hNS : ∀ g ∈ F, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → g ∈ S)
    (hself : ∀ R : Subgroup Γ, S ≤ R → R ≤ F → R ≠ S → Group.IsSolvable ↥R →
      ∀ g ∈ F, (∀ r ∈ R, g * r * g⁻¹ ∈ R) → g ∈ R)
    (hSY : S ≤ Y) (hDY : D ≤ Y) (hY : Group.IsSolvable ↥Y)
    (hDN : D ≤ Subgroup.normalizer (F : Set Γ)) (hDodd : ∀ d ∈ D, Odd (orderOf d))
    (hYB : ∀ y ∈ Y, Odd (orderOf y) → y ∈ B)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x ∈ B, ∀ y ∈ B, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ≠ 1 → y ∈ Subgroup.zpowers x)
    (hD : ¬ D ≤ Subgroup.centralizer (F : Set Γ)) :
    ∃ d ∈ D, d ∈ F ∧ d ≠ 1 ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ d ^ p = 1 := by
  classical
  have hinner : ∀ d ∈ D, ∃ g ∈ F, (∀ x ∈ F, d * x * d⁻¹ = g * x * g⁻¹) ∧
      orderOf g ∣ orderOf d := by
    intro d hd
    set φ := F.normalizerMonoidHom with hφ
    set α := φ ⟨d, hDN hd⟩ with hα
    have hαo : orderOf α ∣ orderOf d := by
      have := orderOf_map_dvd φ ⟨d, hDN hd⟩
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨g, hg⟩ := hout α (Odd.of_dvd_nat (hDodd d hd) hαo)
    refine ⟨g, g.2, fun x hx => ?_, ?_⟩
    · have := congrArg (fun β : MulAut ↥F => ((β ⟨x, hx⟩ : ↥F) : Γ)) hg
      simpa [hα, hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
    · have hinj : Function.Injective (MulAut.conj : ↥F →* MulAut ↥F) := by
        rw [injective_iff_map_eq_one]
        intro y hy
        apply Subtype.ext
        refine hZ y y.2 fun x hx => ?_
        have := congrArg (fun β : MulAut ↥F => ((β ⟨x, hx⟩ : ↥F) : Γ)) hy
        simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at this
        calc (y : Γ) * x = (y : Γ) * x * (y : Γ)⁻¹ * (y : Γ) := by group
          _ = x * y := by rw [this]
      have : orderOf (g : Γ) = orderOf α := by
        rw [hg, orderOf_injective _ hinj, Subgroup.orderOf_coe]
      rw [this]
      exact hαo
  have hR : ∀ d ∈ D, ∀ g ∈ F, (∀ x ∈ F, d * x * d⁻¹ = g * x * g⁻¹) → Odd (orderOf g) →
      g ≠ 1 → g ∈ Y := by
    intro d hd g hg hdg hgodd hg1
    have hgS : g ∉ S := fun hgS => hg1 (eq_one_of_odd_of_mem_l32_ch615 hS2 hgS hgodd)
    have hex : ∃ s ∈ S, g * s * g⁻¹ ∉ S := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hgS (hNS g hg hall)
    obtain ⟨s, hs, hgs⟩ := hex
    have hsG : s ∈ F := hSF hs
    have hxe : d * s * d⁻¹ = g * s * g⁻¹ := hdg s hsG
    have hxY : d * s * d⁻¹ * s⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem (hDY hd) (hSY hs)) (Y.inv_mem (hDY hd)))
        (Y.inv_mem (hSY hs))
    have hxG : d * s * d⁻¹ * s⁻¹ ∈ F := by
      rw [hxe]
      exact F.mul_mem (F.mul_mem (F.mul_mem hg hsG) (F.inv_mem hg)) (F.inv_mem hsG)
    have hxS : d * s * d⁻¹ * s⁻¹ ∉ S := fun hx => hgs (by
      have := S.mul_mem hx hs
      rwa [hxe, inv_mul_cancel_right] at this)
    have hRS : Y ⊓ F ≠ S := fun h => hxS (h ▸ ⟨hxY, hxG⟩)
    have hRs : Group.IsSolvable ↥(Y ⊓ F) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
        (inf_le_left : Y ⊓ F ≤ Y))
    have hgR : ∀ r ∈ Y ⊓ F, g * r * g⁻¹ ∈ Y ⊓ F := by
      intro r hr
      have hrG : r ∈ F := hr.2
      rw [← hdg r hrG]
      refine ⟨Y.mul_mem (Y.mul_mem (hDY hd) hr.1) (Y.inv_mem (hDY hd)), ?_⟩
      rw [hdg r hrG]
      exact F.mul_mem (F.mul_mem hg hrG) (F.inv_mem hg)
    exact (hself (Y ⊓ F) (le_inf hSY hSF) inf_le_right hRS hRs g hg hgR).1
  obtain ⟨δ, hδ, hδG⟩ : ∃ δ ∈ D, ¬ δ ∈ Subgroup.centralizer (F : Set Γ) := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hD h
  obtain ⟨gδ, hgδG, hδg, hgδo⟩ := hinner δ hδ
  have hgδodd : Odd (orderOf gδ) := Odd.of_dvd_nat (hDodd δ hδ) hgδo
  have hgδ1 : gδ ≠ 1 := by
    rintro rfl
    apply hδG
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hδg x hx
    simp only [one_mul, inv_one, mul_one] at this
    calc x * δ = δ * x * δ⁻¹ * δ := by rw [this]
      _ = δ * x := by group
  have hgδY := hR δ hδ gδ hgδG hδg hgδodd hgδ1
  obtain ⟨p, hp', hpd⟩ := Nat.exists_prime_and_dvd (fun h => hgδ1 (orderOf_eq_one_iff.mp h))
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hgδodd) (even_iff_two_dvd.mpr hpd)
  set x := gδ ^ (orderOf gδ / p) with hx
  have hxo : orderOf x = p := by
    rw [hx, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos gδ) hpd) hp'.pos).ne'
      (Nat.div_dvd_of_dvd hpd)]
    exact Nat.div_div_self hpd (orderOf_pos gδ).ne'
  have hxF : x ∈ F := F.pow_mem hgδG _
  have hxB : x ∈ B := hYB x (Y.pow_mem hgδY _) (by rw [hxo]; exact hp'.odd_of_ne_two hp2)
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxo; exact hp'.one_lt.ne' hxo.symm
  have hpδ : p ∣ orderOf δ := hpd.trans hgδo
  set dp := δ ^ (orderOf δ / p) with hdp
  have hdpD : dp ∈ D := D.pow_mem hδ _
  have hdpo : orderOf dp = p := by
    rw [hdp, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos δ) hpδ) hp'.pos).ne'
      (Nat.div_dvd_of_dvd hpδ)]
    exact Nat.div_div_self hpδ (orderOf_pos δ).ne'
  have hdpp : dp ^ p = 1 := by rw [← hdpo]; exact pow_orderOf_eq_one dp
  have hdp1 : dp ≠ 1 := fun h => by rw [h, orderOf_one] at hdpo; exact hp'.one_lt.ne' hdpo.symm
  obtain ⟨gp, hgpG, hdpg, hgpo⟩ := hinner dp hdpD
  have hgpp : gp ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (hdpo ▸ hgpo)
  have hgpodd : Odd (orderOf gp) := Odd.of_dvd_nat (hDodd dp hdpD) hgpo
  have hgpB : gp ∈ B := by
    by_cases h1 : gp = 1
    · rw [h1]; exact B.one_mem
    · exact hYB gp (hR dp hdpD gp hgpG hdpg hgpodd h1) hgpodd
  have hdpB : dp ∈ B := hYB dp (hDY hdpD) (hDodd dp hdpD)
  set c := dp * gp⁻¹ with hc
  have hcC : ∀ y ∈ F, c * y = y * c := by
    intro y hy
    have hy' : gp⁻¹ * y * gp ∈ F := F.mul_mem (F.mul_mem (F.inv_mem hgpG) hy) hgpG
    have := hdpg _ hy'
    calc c * y = dp * (gp⁻¹ * y * gp) * dp⁻¹ * (dp * gp⁻¹) := by rw [hc]; group
      _ = y * c := by rw [this, hc]; group
  have hdg : dp * gp = gp * dp := by
    have := hdpg gp hgpG
    calc dp * gp = dp * gp * dp⁻¹ * dp := by group
      _ = gp * dp := by rw [this]; group
  have hcp : c ^ p = 1 := by
    rw [hc, (Commute.inv_right hdg).mul_pow, hdpp, one_mul, inv_pow, hgpp, inv_one]
  have hcB : c ∈ B := B.mul_mem hdpB (B.inv_mem hgpB)
  have hcz := hp p hp' hp2 x hxB c hcB hxp hcp (hcC x hxF).symm hx1
  have hc1 : c = 1 := hZ c ((Subgroup.zpowers_le.mpr hxF) hcz) hcC
  refine ⟨dp, hdpD, ?_, hdp1, p, hp', hp2, hdpp⟩
  have : dp = gp := by
    rw [hc] at hc1
    exact mul_inv_eq_one.mp hc1
  rw [this]
  exact hgpG

@[expose] def DLemmaFacts_ch615 [Finite Γ] (F : Subgroup Γ) : Prop :=
  ¬ Group.IsSolvable ↥F ∧ (∀ α : MulAut ↥F, Odd (orderOf α) → ∃ g : ↥F, α = MulAut.conj g) ∧
  (∀ S : Subgroup Γ, IsSylowTwoOf S F → ∀ g ∈ F, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → g ∈ S) ∧
  (∀ S : Subgroup Γ, IsSylowTwoOf S F → ∀ R : Subgroup Γ, S ≤ R → R ≤ F → R ≠ S →
    Group.IsSolvable ↥R → ∀ g ∈ F, (∀ r ∈ R, g * r * g⁻¹ ∈ R) → g ∈ R)

@[expose] def BorelFacts_ch615 [Finite Γ] (F : Subgroup Γ) : Prop :=
  ¬ Group.IsSolvable ↥F ∧ ∀ S : Subgroup Γ, IsSylowTwoOf S F → ∀ R : Subgroup Γ, S ≤ R →
    R ≤ F → Group.IsSolvable ↥R → ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S

structure FactorFacts_ch615 [Finite Γ] (F : Subgroup Γ) : Prop where
  ne_bot : F ≠ ⊥
  center : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1
  indec : IsIndec_ch615 F
  kind : Nat.card F = 6 ∨ DLemmaFacts_ch615 F ∨ BorelFacts_ch615 F

end DirectProduct

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.LieType.BorelTits

theorem mem_zpowers_of_autI_borelL_prime_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : MulAut (IntMod (UX615 T L H) hU)}
    (hx : x ∈ autI hU (borelL T L)) (hy : y ∈ autI hU (borelL T L)) (hx3 : x ^ p = 1)
    (hy3 : y ^ p = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) : y ∈ Subgroup.zpowers x := by
  classical
  have h := c.hyp.toHyp5_0_1
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hBN : borelL T L ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_left.trans hXN
  have hDN : D ≤ Subgroup.normalizer (UX615 T L H : Set G) := hD.1.trans hBN
  have hSN : T ⊓ L ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    (Hyp5_0_1.inf_le_borel T L).trans hBN
  set Bs := autI hU (borelL T L) with hBs
  set A := autI hU (T ⊓ L) with hA
  set Ds := autI hU D with hDs
  have hBeq : Bs = Ds ⊔ A := by rw [hBs, ← h.borelL_eq_sup hD, autI_sup hU hDN hSN]
  have hAB : A ≤ Bs := autI_mono hU (Hyp5_0_1.inf_le_borel T L)
  have hBA : Bs ≤ Subgroup.normalizer (A : Set (MulAut _)) := fun b hb =>
    Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => C124.autI_conj_mem hU
      (inf_le_right : borelL T L ≤ _) b hb a ha, fun ha => by
        have := C124.autI_conj_mem hU (inf_le_right : borelL T L ≤ _) b⁻¹ (Bs.inv_mem hb) _ ha
        simpa [mul_assoc] using this⟩
  have hA2 : IsPGroup 2 ↥A := by
    have hT2 : IsPGroup 2 ↥(T ⊓ L) := c.hyp.sylow.1.to_le inf_le_left
    rw [hA, ← range_convHom hU _ hSN]
    exact hT2.of_surjective _ (convHom hU _ hSN).rangeRestrict_surjective
  have hAn : (A.subgroupOf Bs).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mpr hBA
  set mk := QuotientGroup.mk' (A.subgroupOf Bs) with hmk
  have hDcyc : IsCyclic ↥Ds := (c.autI_hall_ch615 hU hD).1
  have hDB : Ds ≤ Bs := autI_mono hU hD.1
  have hsurj : Function.Surjective (mk.comp (Subgroup.inclusion hDB)) := by
    intro q
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hb' : b ∈ ((Ds ⊔ A : Subgroup _) : Set (MulAut _)) := by rw [← hBeq]; exact hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Ds A (hDB.trans hBA)] at hb'
    obtain ⟨δ, hδ, a, ha, rfl⟩ := hb'
    refine ⟨⟨δ, hδ⟩, ?_⟩
    simp only [MonoidHom.comp_apply, hmk, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    show (⟨δ, hDB hδ⟩ : ↥Bs)⁻¹ * ⟨δ * a, hb⟩ ∈ A.subgroupOf Bs
    rw [Subgroup.mem_subgroupOf]
    simpa using ha
  have hQcyc : IsCyclic (↥Bs ⧸ A.subgroupOf Bs) := isCyclic_of_surjective _ hsurj
  have hker : ∀ g : ↥Bs, g.1 ^ p = 1 → mk g = 1 → g = 1 := by
    intro g hg3 hg1
    have hgA : g.1 ∈ A := by
      have := (QuotientGroup.eq_one_iff (N := A.subgroupOf Bs) g).mp hg1
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨k, hk⟩ := hA2 ⟨g, hgA⟩
    have hk' : g.1 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h1 : orderOf g.1 = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hg3) hcop)
      (orderOf_dvd_of_pow_eq_one hk')
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  set x' : ↥Bs := ⟨x, hx⟩
  set y' : ↥Bs := ⟨y, hy⟩
  have hx'3 : x' ^ p = 1 := Subtype.ext (by simpa using hx3)
  have hy'3 : y' ^ p = 1 := Subtype.ext (by simpa using hy3)
  have hmx1 : mk x' ≠ 1 := fun h1 => hx1 (congrArg Subtype.val (hker x' hx3 h1))
  have hmx3 : mk x' ^ p = 1 := by rw [← map_pow, hx'3, map_one]
  have hmy3 : mk y' ^ p = 1 := by rw [← map_pow, hy'3, map_one]
  obtain ⟨k, hk⟩ :=
    Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_pow_prime_ch615 hp hmx3 hmx1 hmy3)
  have hcomm : x' * y' = y' * x' := Subtype.ext hxy
  have hyx3 : (y' * (x' ^ k)⁻¹) ^ p = 1 := by
    have hc : Commute y' (x' ^ k)⁻¹ := (Commute.zpow_right (hcomm.symm : Commute y' x') k).inv_right
    rw [hc.mul_pow, hy'3, one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hx'3, one_zpow, inv_one]
  have hyx1 : mk (y' * (x' ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  have := hker _ (by simpa using congrArg Subtype.val hyx3) hyx1
  have hyk : y' = x' ^ k := by
    rw [mul_inv_eq_one] at this
    exact this
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using (congrArg Subtype.val hyk).symm⟩

theorem isSolvable_oTwoUpper_ch615 (c : Cx615C G T M L V H n) :
    Group.IsSolvable ↥(oTwoUpper H) := by
  have hHN : H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) := le_normalizer_conjClosure _ _
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (Cx615.UH T H : Set G) :=
    (oTwoUpper_le H).trans hHN
  set g := (convHom c.hU (oTwoUpper H) hKN).rangeRestrict with hg
  have hrange : (convHom c.hU (oTwoUpper H) hKN).range ≤ autI c.hU (thompsonJ H) := by
    rw [range_convHom]
    refine autI_mono c.hU ?_
    rw [← twoResidual_eq_oTwoUpper']
    exact c.e23.1
  have hJs := c.toCx615B.blocks_ch615.1
  have hs1 : Group.IsSolvable ↥(convHom c.hU (oTwoUpper H) hKN).range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hrange)
      (Subgroup.inclusion_injective hrange)
  have hkerle : oTwoUpper H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤ pCoreOf 2 H := by
    rw [← c.cent]
    exact inf_le_inf_right _ (oTwoUpper_le H)
  have hs2 : Group.IsSolvable ↥(oTwoUpper H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G)) := by
    have : IsPGroup 2 ↥(oTwoUpper H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G)) :=
      (pCoreOf_isPGroup 2 H).to_le hkerle
    have := this.isNilpotent
    infer_instance
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (inf_le_left :
      oTwoUpper H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤ oTwoUpper H)) g ?_
  intro k hk
  rw [hg, MonoidHom.ker_rangeRestrict, ker_convHom] at hk
  exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩

theorem isSolvable_autI_oTwoUpper_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) : Group.IsSolvable ↥(autI hU (oTwoUpper H)) := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    ((oTwoUpper_le H).trans le_sup_right).trans hXN
  have := c.isSolvable_oTwoUpper_ch615
  rw [← range_convHom hU _ hKN]
  exact Group.isSolvable_of_surjective (convHom hU _ hKN).rangeRestrict_surjective

end Cx615C

end CFSG.Quasithin.H13
