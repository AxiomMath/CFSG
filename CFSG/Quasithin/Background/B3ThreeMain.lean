module

public import CFSG.Quasithin.Background.B3ThreeCore
public import CFSG.Quasithin.Background.B3ThreeChief
public import CFSG.Quasithin.Background.B3ThreeTop

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {V : Type*} [CommGroup V]

section Setup

variable {ρ : LG n →* MulAut V} {A B : Subgroup V}

theorem extBot_of_threeStep (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B)
    (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) :
    ExtBot n (resAct ρ B hS.invB) (A.subgroupOf B)
      (ψ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf B))) where
  sq m := Subtype.ext (by simpa using hV m.1)
  surj := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  equiv g m := by
    have h := hψ g (QuotientGroup.mk m)
    rw [secAct_mk] at h
    exact h
  ker m := by
    show ψ (QuotientGroup.mk m) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  fix g a ha := Subtype.ext (hS.trivA g a ha)

theorem commOn_eq_of_threeStep (hn5 : 5 ≤ n) (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B)
    (hindec : IsIndec ρ) : commOn ρ B = B := by
  have h := (commG_eq_of_threeStep hV hS hindec).1
  have h2 := commOn_commG (commutator_LG hn5) hV ρ
  rw [h] at h2
  exact h2

theorem mem_commG_resAct (hB : IsInv ρ B) (h : commOn ρ B = B) (b : ↥B) :
    b ∈ commG (resAct ρ B hB) := by
  have hle : commOn ρ B ≤ (commG (resAct ρ B hB)).map B.subtype := by
    refine commOn_le (fun g m hm => ?_)
    refine ⟨resAct ρ B hB g (⟨m, hm⟩ : ↥B) * (⟨m, hm⟩ : ↥B)⁻¹,
      mul_inv_mem_commG g (⟨m, hm⟩ : ↥B), ?_⟩
    rfl
  have hb : (b : V) ∈ commOn ρ B := by
    rw [h]
    exact b.2
  obtain ⟨b', hb', hbb⟩ := hle hb
  have : b' = b := Subtype.ext hbb
  rw [this] at hb'
  exact hb'

theorem card_subgroupOf_of_le (hle : A ≤ B) : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem eq_bot_of_subgroupOf_bot (hle : A ≤ B) (h : A.subgroupOf B = ⊥) : A = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have : (⟨a, hle ha⟩ : ↥B) ∈ A.subgroupOf B := ha
  rw [h, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

theorem card_threeStep (hS : ThreeStep ρ A B) (ψ : Sec B A ≃* WV n) :
    Nat.card ↥B = Nat.card ↥A * Nat.card (WV n) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf B)
  rw [card_subgroupOf_of_le hS.le] at h1
  have h2 : Nat.card (↥B ⧸ A.subgroupOf B) = Nat.card (WV n) := Nat.card_congr ψ.toEquiv
  rw [h2] at h1
  rw [h1, mul_comm]

theorem subgroupOf_le_commG (hn5 : 5 ≤ n) (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B)
    (hindec : IsIndec ρ) : A.subgroupOf B ≤ commG (resAct ρ B hS.invB) := fun a _ =>
  mem_commG_resAct hS.invB (commOn_eq_of_threeStep hn5 hV hS hindec) a

theorem A_bot_of_odd [Finite V] (hn : n = 5 ∨ n = 7) (hV : ∀ v : V, v ^ 2 = 1)
    (hS : ThreeStep ρ A B) (hindec : IsIndec ρ) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) : A = ⊥ := by
  have hn5 : 5 ≤ n := by omega
  exact eq_bot_of_subgroupOf_bot hS.le (eq_bot_of_zeroClass hn5 (extBot_of_threeStep hV hS ψ hψ)
    (subgroupOf_le_commG hn5 hV hS hindec) (H1_natural_odd hn))

theorem A_card_of_even [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hS : ThreeStep ρ A B) (hindec : IsIndec ρ) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) :
    A = ⊥ ∨ Nat.card ↥A = 2 := by
  have hn5 : 5 ≤ n := by omega
  have hle := card_le_two_of_twoClass hn5 (extBot_of_threeStep hV hS ψ hψ)
    (subgroupOf_le_commG hn5 hV hS hindec) (H1_natural_even hn)
  rw [card_subgroupOf_of_le hS.le] at hle
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  by_cases h1 : Nat.card ↥A = 1
  · exact Or.inl (Subgroup.eq_bot_of_card_eq A h1)
  · right
    omega

theorem exists_iso_of_bot (hV : ∀ v : V, v ^ 2 = 1) (hS : ThreeStep ρ A B) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) (hA : A = ⊥) :
    ∃ φ : ↥B ≃* WV n, IsModIso (resAct ρ B hS.invB) (actL n Mod.ut0) φ := by
  have E := extBot_of_threeStep hV hS ψ hψ
  have hinj : Function.Injective (ψ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf B))) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : m ∈ A.subgroupOf B := (E.ker m).1 hm
    have h2 : (m : V) ∈ A := h1
    rw [hA, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, E.surj⟩, fun g m => E.equiv g m⟩

theorem exists_iso_of_eq_top {W : Type*} [CommGroup W] {ρW : LG n →* MulAut W} (hB : IsInv ρ B)
    (h : B = ⊤) (φ : ↥B ≃* W) (hφ : IsModIso (resAct ρ B hB) ρW φ) :
    ∃ Φ : V ≃* W, IsModIso ρ ρW Φ := by
  let e : V ≃* ↥B := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)
  refine ⟨e.trans φ, fun g v => ?_⟩
  show φ (e (ρ g v)) = ρW g (φ (e v))
  have : e (ρ g v) = resAct ρ B hB g (e v) := Subtype.ext rfl
  rw [this, hφ g (e v)]

theorem top_dichotomy {X : Type*} [CommGroup X] {ρX : LG n →* MulAut X} {d₀ : LG n → X}
    (hX2 : ∀ x : X, x ^ 2 = 1) (ht : TwoClass ρX d₀) (hfixB : fixG ρ ≤ B)
    (hM : ∀ g v, ρ g v * v⁻¹ ∈ B) (φ : ↥B ≃* X)
    (hφ : IsModIso (resAct ρ B (isInv_of_trivQ hM)) ρX φ) :
    B = ⊤ ∨ ∃ s : V, s ∉ B ∧ B ⊔ Subgroup.zpowers s = ⊤ ∧
      ∀ x, ρ x s * s⁻¹ = ((φ.symm (d₀ x) : ↥B) : V) := by
  rcases top_classify_two hX2 ht hM φ hφ with h | ⟨s, hs, hcoc, hVs⟩
  · left
    rwa [sup_eq_left.2 hfixB] at h
  · right
    rw [sup_eq_left.2 hfixB] at hs hVs
    exact ⟨s, hs, hVs, hcoc⟩

theorem classify_even_aux [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hS : ThreeStep ρ A B) (hindec : IsIndec ρ) (ψ : Sec B A ≃* WV n)
    (hψ : ∀ g x, ψ (secAct ρ hS.invB hS.invA g x) = actL n Mod.ut0 g (ψ x)) :
    (A = ⊥ ∧ ((B = ⊤ ∧ ∃ Φ : V ≃* WV n, IsModIso ρ (actL n Mod.ut0) Φ) ∨
        (B ≠ ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ))) ∨
    (Nat.card ↥A = 2 ∧ ((B = ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
        (B ≠ ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.u, IsModIso ρ (actL n Mod.u) Φ))) := by
  have hn5 : 5 ≤ n := by omega
  have hfix : fixG ρ = A := (commG_eq_of_threeStep hV hS hindec).2
  have hfixB : fixG ρ ≤ B := hfix ▸ hS.le
  rcases A_card_of_even hn hV hS hindec ψ hψ with hA | hA2
  · left
    refine ⟨hA, ?_⟩
    obtain ⟨φ, hφ⟩ := exists_iso_of_bot hV hS ψ hψ hA
    rcases top_dichotomy (V_sq' Mod.ut0) (H1_natural_even hn) hfixB hS.trivQ φ hφ with
      h | ⟨s, hs, hVs, hcoc⟩
    · exact Or.inl ⟨h, exists_iso_of_eq_top hS.invB h φ hφ⟩
    · refine Or.inr ⟨fun h => hs (h ▸ Subgroup.mem_top s), ?_⟩
      exact exists_iso_top_ut hn hV hS.trivQ φ hφ hs hVs hcoc
  · right
    refine ⟨hA2, ?_⟩
    obtain ⟨φ, hφ⟩ := exists_iso_core hn5 hn (extBot_of_threeStep hV hS ψ hψ)
      (subgroupOf_le_commG hn5 hV hS hindec) (by rw [card_subgroupOf_of_le hS.le]; exact hA2)
    rcases top_dichotomy (V_sq' Mod.u0) (H1_core_even hn) hfixB hS.trivQ φ hφ with
      h | ⟨s, hs, hVs, hcoc⟩
    · exact Or.inl ⟨h, exists_iso_of_eq_top hS.invB h φ hφ⟩
    · refine Or.inr ⟨fun h => hs (h ▸ Subgroup.mem_top s), ?_⟩
      exact exists_iso_top_u hn hV hS.trivQ φ hφ hs hVs hcoc

end Setup

variable {ρ : LG n →* MulAut V}

theorem classify_odd [Finite V] (hn : n = 5 ∨ n = 7) (hV : ∀ v : V, v ^ 2 = 1)
    (hone : HasOneChief n ρ) (hindec : IsIndec ρ) :
    fixG ρ = ⊥ ∧ commG ρ = ⊤ ∧ ∃ Φ : V ≃* WV n, IsModIso ρ (actL n Mod.ut0) Φ := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨A, B, hA, hB, hS, ψ, hψ⟩ := threeStep_of_chief hn5 hone
  have hc := commG_eq_of_threeStep hV hS hindec
  have hAbot : A = ⊥ := A_bot_of_odd hn hV hS hindec ψ hψ
  obtain ⟨φ, hφ⟩ := exists_iso_of_bot hV hS ψ hψ hAbot
  have hBtop : B = ⊤ := by
    rw [eq_top_iff]
    intro s _
    obtain ⟨m, hm⟩ := exists_corr_zero (H1_natural_odd hn) hS.trivQ φ hφ s
    rw [hc.2, hAbot, Subgroup.mem_bot] at hm
    have : s = (m : V) := by
      have := mul_inv_eq_one.1 hm
      exact this
    rw [this]
    exact m.2
  exact ⟨hc.2.trans hAbot, hc.1.trans hBtop, exists_iso_of_eq_top hS.invB hBtop φ hφ⟩

theorem classify_even [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hone : HasOneChief n ρ) (hindec : IsIndec ρ) :
    Nat.card ↥(commG ρ) = Nat.card ↥(fixG ρ) * Nat.card (WV n) ∧
    ((fixG ρ = ⊥ ∧ ((commG ρ = ⊤ ∧ ∃ Φ : V ≃* WV n, IsModIso ρ (actL n Mod.ut0) Φ) ∨
        (commG ρ ≠ ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ))) ∨
    (Nat.card ↥(fixG ρ) = 2 ∧ ((commG ρ = ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.u0,
          IsModIso ρ (actL n Mod.u0) Φ) ∨
        (commG ρ ≠ ⊤ ∧ ∃ Φ : V ≃* Mod.V n Mod.u, IsModIso ρ (actL n Mod.u) Φ)))) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨A, B, hA, hB, hS, ψ, hψ⟩ := threeStep_of_chief hn5 hone
  have hc := commG_eq_of_threeStep hV hS hindec
  rw [hc.1, hc.2]
  exact ⟨card_threeStep hS ψ, classify_even_aux hn hV hS hindec ψ hψ⟩

theorem modIso_ut0_ut_odd (hn : n = 5 ∨ n = 7) :
    ∃ Φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.ut, IsModIso (actL n Mod.ut0) (actL n Mod.ut) Φ := by
  have hn1 : 1 ≤ n := by omega
  have hW : Mod.W n Mod.ut0 ≤ Mod.W n Mod.ut := fun _ _ => Subgroup.mem_top _
  have hN : ∀ w ∈ Mod.W n Mod.ut0, w ∈ Mod.N n Mod.ut0 → w ∈ Mod.N n Mod.ut := fun _ _ h => h
  have hinj : Function.Injective (incl n Mod.ut0 Mod.ut hW hN) :=
    incl_injective hW hN (fun _ _ h => h)
  have h1 := card_V_mul (n := n) Mod.ut
  have h2 : cN n Mod.ut = 2 := by
    show Nat.card ↥(Esub n ⊓ (⊤ : Subgroup (U n))) = 2
    rw [inf_top_eq]
    exact card_Esub hn1
  have h3 : Nat.card ↥(Mod.W n Mod.ut) = 2 ^ n := by
    show Nat.card ↥(⊤ : Subgroup (U n)) = 2 ^ n
    rw [Subgroup.card_top, card_U']
  rw [h2, h3] at h1
  have h4 : Nat.card (Mod.V n Mod.ut0) = 2 ^ (n - 1) := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one (V_sq' (n := n) Mod.ut0)),
      rk_Vut0 hn1]
    have : ¬ n % 2 = 0 := by omega
    simp [this]
  have h5 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hcard : Nat.card (Mod.V n Mod.ut) ≤ Nat.card (Mod.V n Mod.ut0) := by omega
  exact ⟨MulEquiv.ofBijective _ (hinj.bijective_of_nat_card_le hcard),
    fun g v => incl_act hW hN g.1 v⟩

theorem B3_3_1_odd [Finite V] (hn : n = 5 ∨ n = 7) (hV : ∀ v : V, v ^ 2 = 1)
    (hone : HasOneChief n ρ) (hindec : IsIndec ρ) :
    Nat.card (H1 (actL n Mod.ut0)) = 1 ∧
    (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ) ∧
    (∃ Φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.u0, IsModIso (actL n Mod.ut0) (actL n Mod.u0) Φ) ∧
    (∃ Φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.ut, IsModIso (actL n Mod.ut0) (actL n Mod.ut) Φ) := by
  refine ⟨card_H1_natural_odd hn, (classify_odd hn hV hone hindec).2.2, ?_, ?_⟩
  · obtain ⟨-, -, -, φ, hφ⟩ := B3_1_2 (by omega : 5 ≤ n) (by omega : n % 2 = 1)
    exact ⟨φ, fun g v => hφ g.1 v⟩
  · exact modIso_ut0_ut_odd hn

theorem B3_3_1_even (hn : n = 6 ∨ n = 8) : Nat.card (H1 (actL n Mod.ut0)) = 2 :=
  card_H1_natural_even hn

theorem B3_3_2 [Finite V] {H : Type*} [Group H] (j : LG n →* H) (ρH : H →* MulAut V)
    (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1) (hone : HasOneChief n (ρH.comp j))
    (hindec : IsIndec (ρH.comp j))
    (hquot : ∃ θ : (V ⧸ fixG ρH) ≃* WV n, ∀ x v,
      θ (QuotientGroup.mk ((ρH.comp j) x v)) = actL n Mod.ut0 x (θ (QuotientGroup.mk v))) :
    (∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso (ρH.comp j) (actL n Mod.u0) Φ) ∨
    (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso (ρH.comp j) (actL n Mod.ut0) Φ) := by
  obtain ⟨θ, -⟩ := hquot
  obtain ⟨hcard, hcases⟩ := classify_even hn hV hone hindec
  have hle : fixG ρH ≤ fixG (ρH.comp j) := fun v hv =>
    mem_fixG.2 (fun x => mem_fixG.1 hv (j x))
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (fixG ρH)
  have h2 : Nat.card (V ⧸ fixG ρH) = Nat.card (WV n) := Nat.card_congr θ.toEquiv
  have h3 : Nat.card ↥(fixG ρH) ≤ Nat.card ↥(fixG (ρH.comp j)) := Subgroup.card_le_of_le hle
  have h5 : Nat.card V = Nat.card (WV n) * Nat.card ↥(fixG ρH) := by rw [h1, h2]
  have h6 : Nat.card V ≤ Nat.card ↥(commG (ρH.comp j)) := by
    rw [hcard, h5, mul_comm (Nat.card ↥(fixG (ρH.comp j)))]
    exact Nat.mul_le_mul_left _ h3
  have htop : commG (ρH.comp j) = ⊤ := Subgroup.eq_top_of_card_eq _
    (le_antisymm (Subgroup.card_le_card_group _) h6)
  rcases hcases with ⟨-, ⟨-, hΦ⟩ | ⟨hne, -⟩⟩ | ⟨-, ⟨-, hΦ⟩ | ⟨hne, -⟩⟩
  · exact Or.inr hΦ
  · exact absurd htop hne
  · exact Or.inl hΦ
  · exact absurd htop hne

theorem B3_3_2_L [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hone : HasOneChief n ρ) (hindec : IsIndec ρ)
    (hquot : ∃ θ : (V ⧸ fixG ρ) ≃* WV n, ∀ x v,
      θ (QuotientGroup.mk (ρ x v)) = actL n Mod.ut0 x (θ (QuotientGroup.mk v))) :
    (∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
    (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ) := by
  simpa using B3_3_2 (MonoidHom.id (LG n)) ρ hn hV (by simpa using hone) (by simpa using hindec)
    (by simpa using hquot)

theorem B3_3_2_G [Finite V] (ρG : Gp n →* MulAut V) (hn : n = 6 ∨ n = 8)
    (hV : ∀ v : V, v ^ 2 = 1) (hone : HasOneChief n (ρG.comp (alternatingGroup (Fin n)).subtype))
    (hindec : IsIndec (ρG.comp (alternatingGroup (Fin n)).subtype))
    (hquot : ∃ θ : (V ⧸ fixG ρG) ≃* WV n, ∀ x v,
      θ (QuotientGroup.mk ((ρG.comp (alternatingGroup (Fin n)).subtype) x v)) =
        actL n Mod.ut0 x (θ (QuotientGroup.mk v))) :
    (∃ Φ : V ≃* Mod.V n Mod.u0,
      IsModIso (ρG.comp (alternatingGroup (Fin n)).subtype) (actL n Mod.u0) Φ) ∨
    (∃ Φ : V ≃* Mod.V n Mod.ut0,
      IsModIso (ρG.comp (alternatingGroup (Fin n)).subtype) (actL n Mod.ut0) Φ) :=
  B3_3_2 (alternatingGroup (Fin n)).subtype ρG hn hV hone hindec hquot

theorem B3_3_3 [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hone : HasOneChief n ρ) (hindec : IsIndec ρ)
    (hcomm : ∃ φ : ↥(commG ρ) ≃* WV n,
      IsModIso (resAct ρ (commG ρ) (isInv_commG ρ)) (actL n Mod.ut0) φ) :
    (∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ) ∨
    (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ) := by
  obtain ⟨φ, -⟩ := hcomm
  obtain ⟨hcard, hcases⟩ := classify_even hn hV hone hindec
  have h1 : Nat.card ↥(commG ρ) = Nat.card (WV n) := Nat.card_congr φ.toEquiv
  have hpos : 0 < Nat.card (WV n) := Nat.card_pos
  rcases hcases with ⟨-, ⟨-, hΦ⟩ | ⟨-, hΦ⟩⟩ | ⟨h2, -⟩
  · exact Or.inr hΦ
  · exact Or.inl hΦ
  · exfalso
    rw [h1, h2] at hcard
    omega

theorem B3_3_4 [Finite V] (hn : n = 6 ∨ n = 8) (hV : ∀ v : V, v ^ 2 = 1)
    (hone : HasOneChief n ρ) (hindec : IsIndec ρ) :
    (∃ Φ : V ≃* Mod.V n Mod.u, IsModIso ρ (actL n Mod.u) Φ) ∨
    (∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
    (∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ) ∨
    (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ) := by
  obtain ⟨-, hcases⟩ := classify_even hn hV hone hindec
  rcases hcases with ⟨-, ⟨-, hΦ⟩ | ⟨-, hΦ⟩⟩ | ⟨-, ⟨-, hΦ⟩ | ⟨-, hΦ⟩⟩
  · exact Or.inr (Or.inr (Or.inr hΦ))
  · exact Or.inr (Or.inr (Or.inl hΦ))
  · exact Or.inr (Or.inl hΦ)
  · exact Or.inl hΦ

theorem hasOneChief_natural (hn : 5 ≤ n) : HasOneChief n (actL n Mod.ut0) := by
  have hirr : ∀ Z : Subgroup (WV n), IsInv (actL n Mod.ut0) Z → Z = ⊥ ∨ Z = ⊤ := fun Z hZ =>
    (B3_1_1 hn).2 Z (fun g hg v hv => hZ ⟨g, hg⟩ v hv)
  have hnt : Nontrivial (WV n) := (B3_1_1 hn).1
  let ψ₀ : Sec (⊤ : Subgroup (WV n)) (⊥ : Subgroup (WV n)) ≃* WV n :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := (⊤ : Subgroup (WV n))))).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  refine ⟨⟨1, fun i => if i = 0 then ⊥ else ⊤, ?_, 0, Nat.one_pos, by simp, by simp, ?_, ?_,
    ψ₀, ?_⟩⟩
  · intro i _
    by_cases h : i = 0
    · simp only [h, ite_true]
      intro g w hw
      rw [Subgroup.mem_bot] at hw ⊢
      rw [hw, map_one]
    · simp only [h, ite_false]
      intro _ _ _
      exact Subgroup.mem_top _
  · intro i hi
    have h0 : i = 0 := by omega
    subst h0
    refine ⟨bot_lt_top, fun Z hZ _ _ => hirr Z hZ⟩
  · intro i hi hne
    exact absurd (by omega) hne
  · intro g x
    induction x using QuotientGroup.induction_on with
    | H w => rfl

theorem isIndec_natural (hn : 5 ≤ n) : IsIndec (actL n Mod.ut0) := by
  intro X Y hX hY hXY _
  rcases (B3_1_1 hn).2 X (fun g hg v hv => hX ⟨g, hg⟩ v hv) with h | h
  · exact Or.inl h
  · right
    rw [h, top_inf_eq] at hXY
    exact hXY

end CFSG.Quasithin.B3
