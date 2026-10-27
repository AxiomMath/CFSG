module

public import CFSG.Quasithin.Vol2.Ch10SecV1E
public import CFSG.Quasithin.Background.B4L3FactA

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_compl (hV : ∀ v : V, v ^ 2 = 1) {A F : Subgroup V} (hAF : A ≤ F) :
    ∃ B : Subgroup V, B ≤ F ∧ A ⊓ B = ⊥ ∧ A ⊔ B = F := by
  obtain ⟨B, -, hB⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup V => B ≤ F ∧ A ⊓ B = ⊥) (a := ⊥) ⟨bot_le, inf_bot_eq A⟩
  refine ⟨B, hB.1.1, hB.1.2, le_antisymm (sup_le hAF hB.1.1) fun f hf => ?_⟩
  by_contra hnot
  have hB' : B ⊔ Subgroup.zpowers f ≤ F ∧ A ⊓ (B ⊔ Subgroup.zpowers f) = ⊥ := by
    refine ⟨sup_le hB.1.1 (Subgroup.zpowers_le.mpr hf), ?_⟩
    rw [eq_bot_iff]
    rintro x ⟨hxA, hx⟩
    rcases (mem_sup_zpowers_iff hV).mp hx with h | h
    · rw [← hB.1.2]
      exact ⟨hxA, h⟩
    · refine (hnot ?_).elim
      have e : f = x⁻¹ * (x * f) := by group
      rw [e]
      exact Subgroup.mul_mem_sup (A.inv_mem hxA) h
  have hle := hB.2 hB' le_sup_left
  exact hnot (Subgroup.mem_sup_right (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))))

variable {G : Subgroup (MulAut V)} {W₂ W₁ : Subgroup V}

omit [Finite V] in
theorem sup_zpowers_inf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {A F : Subgroup V} {w : V}
    (hAF : A ⊓ F = ⊥) (hw : w ∉ A ⊔ F) : (A ⊔ Subgroup.zpowers w) ⊓ F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxF⟩
  rcases (mem_sup_zpowers_iff hV).mp hx with h | h
  · rw [← hAF]
    exact ⟨h, hxF⟩
  · refine (hw ?_).elim
    have e : w = (x * w) * x⁻¹ := by rw [mul_comm x w, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.mul_mem_sup h (F.inv_mem hxF)

omit [Finite V] in
theorem card_eq_one_of_forall {W X : Subgroup V} (hXW : X ≤ W) (hWF : W ⊓ fixV G = ⊥)
    (hX : ∀ x ∈ X, ∀ g ∈ G, g x * x⁻¹ ∈ (⊥ : Subgroup V)) : Nat.card X = 1 := by
  rw [Subgroup.card_eq_one, eq_bot_iff, ← hWF]
  intro x hx
  refine ⟨hXW hx, fun g hg => ?_⟩
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hX x hx g hg))

theorem two_lt_of_inf_eq_bot (D : L3Data G W₂ W₁) {W : Subgroup V}
    (hW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) (hWF : W ⊓ fixV G = ⊥) (h8 : 8 < Nat.card W) :
    2 < Nat.card ↥(W.map (commHom (D.rho L3.x12)) ⊔ ⊥) := by
  by_contra h
  obtain ⟨X, hXW, hX8, hX⟩ := fix_bound D hW bot_le (by rw [Subgroup.card_bot]; omega)
  rw [card_eq_one_of_forall hXW hWF hX] at hX8
  omega

omit [Finite V] in
theorem exists_not_mem_of_ne_top {A : Subgroup V} (h : A ≠ ⊤) : ∃ w, w ∉ A := by
  by_contra hc
  apply h
  rw [eq_top_iff]
  intro x _
  by_contra hx
  exact hc ⟨x, hx⟩

theorem card_of_natural (hV : ∀ v : V, v ^ 2 = 1) (D : L3Data G W₂ W₁) {U : Subgroup V}
    (hUc : ∀ g ∈ G, ∀ v, g v * v⁻¹ ∈ U) (hU8 : Nat.card U = 8) (hUF : U ⊓ fixV G = ⊥)
    (hUt : ∃ u ∈ U, D.rho L3.x12 u ≠ u) (hind : IsIndecompModule G) :
    Nat.card V = 8 ∨ Nat.card V = 16 := by
  have hinv : ∀ A : Subgroup V, U ≤ A → ∀ g ∈ G, ∀ a ∈ A, g a ∈ A := by
    intro A hUA g hg a ha
    have e : g a = (g a * a⁻¹) * a := by group
    rw [e]
    exact A.mul_mem (hUA (hUc g hg a)) ha
  have hFinv : ∀ g ∈ G, ∀ x ∈ fixV G, g x ∈ fixV G := fixV_invariant G
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU8
    omega
  have ht : ∀ v, D.rho L3.x12 (D.rho L3.x12 v) = v := rho_invol D L3.x12_invol
  by_cases h1 : U ⊔ fixV G = ⊤
  · rcases hind U (fixV G) (hinv U le_rfl) hFinv hUF h1 with h | h
    · exact (hUne h).elim
    · left
      rw [h, sup_bot_eq] at h1
      rw [← Subgroup.card_top (G := V), ← h1, hU8]
  obtain ⟨w, hw⟩ := exists_not_mem_of_ne_top h1
  have hwU : w ∉ U := fun h => hw (Subgroup.mem_sup_left h)
  have hM16 : Nat.card ↥(U ⊔ Subgroup.zpowers w) = 16 := by rw [card_sup_zpowers hV hwU, hU8]
  have hMF := sup_zpowers_inf_eq_bot hV hUF hw
  by_cases h2 : U ⊔ Subgroup.zpowers w ⊔ fixV G = ⊤
  · rcases hind _ (fixV G) (hinv _ le_sup_left) hFinv hMF h2 with h | h
    · rw [h, Subgroup.card_bot] at hM16
      omega
    · right
      rw [h, sup_bot_eq] at h2
      rw [← Subgroup.card_top (G := V), ← h2, hM16]
  exfalso
  obtain ⟨w', hw'⟩ := exists_not_mem_of_ne_top h2
  have hw'M : w' ∉ U ⊔ Subgroup.zpowers w := fun h => hw' (Subgroup.mem_sup_left h)
  obtain ⟨V₅, hV₅⟩ : ∃ V₅, V₅ = U ⊔ Subgroup.zpowers w ⊔ Subgroup.zpowers w' := ⟨_, rfl⟩
  have h32 : Nat.card V₅ = 32 := by rw [hV₅, card_sup_zpowers hV hw'M, hM16]
  have h5F : V₅ ⊓ fixV G = ⊥ := hV₅ ▸ sup_zpowers_inf_eq_bot hV hMF hw'
  have hUV₅ : U ≤ V₅ := hV₅ ▸ le_sup_left.trans le_sup_left
  have hc5 : Nat.card ↥(V₅.map (commHom (D.rho L3.x12)) ⊔ ⊥) = 4 := by
    have hsq := sq_bound D hV (hinv V₅ hUV₅) bot_le bot_le
    rw [pow_two, h32, Subgroup.card_bot] at hsq
    have := card_eq_four_mul hV (K := ⊥) le_sup_right
      (by rw [Subgroup.card_bot]; exact two_lt_of_inf_eq_bot D (hinv V₅ hUV₅) h5F (by omega))
      (by rw [Subgroup.card_bot]; omega)
    rwa [Subgroup.card_bot, mul_one] at this
  have hf5 := card_sup_mul_card_fixRel (D.rho L3.x12) V₅ ⊥
  rw [hc5, h32, Subgroup.card_bot] at hf5
  have hfU := card_sup_mul_card_fixRel (D.rho L3.x12) U ⊥
  rw [hU8, Subgroup.card_bot] at hfU
  have hcU : 2 ≤ Nat.card ↥(U.map (commHom (D.rho L3.x12)) ⊔ ⊥) := by
    obtain ⟨u, hu, hut⟩ := hUt
    have hne : U.map (commHom (D.rho L3.x12)) ⊔ ⊥ ≠ ⊥ := by
      intro h
      have hm : commHom (D.rho L3.x12) u ∈ U.map (commHom (D.rho L3.x12)) ⊔ ⊥ :=
        Subgroup.mem_sup_left ⟨u, hu, rfl⟩
      rw [h, Subgroup.mem_bot, commHom_apply, mul_inv_eq_one] at hm
      exact hut hm
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hbU : 2 * Nat.card ↥(fixRel (D.rho L3.x12) U ⊥) ≤ 8 := by
    calc 2 * Nat.card ↥(fixRel (D.rho L3.x12) U ⊥)
        ≤ Nat.card ↥(U.map (commHom (D.rho L3.x12)) ⊔ ⊥) *
            Nat.card ↥(fixRel (D.rho L3.x12) U ⊥) := Nat.mul_le_mul_right _ hcU
      _ = 8 := by rw [hfU]
  obtain ⟨x, hx, hxU⟩ : ∃ x ∈ fixRel (D.rho L3.x12) V₅ ⊥, x ∉ U := by
    by_contra hc
    have hle : fixRel (D.rho L3.x12) V₅ ⊥ ≤ fixRel (D.rho L3.x12) U ⊥ := fun y hy =>
      ⟨by_contra fun hyU => hc ⟨y, hy, hyU⟩, hy.2⟩
    have := Subgroup.card_le_of_le hle
    omega
  have hM'16 : Nat.card ↥(U ⊔ Subgroup.zpowers x) = 16 := by rw [card_sup_zpowers hV hxU, hU8]
  have hM'V₅ : U ⊔ Subgroup.zpowers x ≤ V₅ := sup_le hUV₅ (Subgroup.zpowers_le.mpr hx.1)
  have hM'F : (U ⊔ Subgroup.zpowers x) ⊓ fixV G = ⊥ :=
    le_bot_iff.mp (h5F ▸ inf_le_inf_right _ hM'V₅)
  have hinvM := hinv _ (le_sup_left : U ≤ U ⊔ Subgroup.zpowers x)
  have hcM : Nat.card ↥((U ⊔ Subgroup.zpowers x).map (commHom (D.rho L3.x12)) ⊔ ⊥) = 4 := by
    have hsq := sq_bound D hV hinvM bot_le bot_le
    rw [pow_two, hM'16, Subgroup.card_bot] at hsq
    have := card_eq_four_mul hV (K := ⊥) le_sup_right
      (by rw [Subgroup.card_bot]; exact two_lt_of_inf_eq_bot D hinvM hM'F (by omega))
      (by rw [Subgroup.card_bot]; omega)
    rwa [Subgroup.card_bot, mul_one] at this
  have hfM := card_sup_mul_card_fixRel (D.rho L3.x12) (U ⊔ Subgroup.zpowers x) ⊥
  rw [hcM, hM'16, Subgroup.card_bot] at hfM
  have hle := map_sup_le_fixRel hV ht (hinvM _ (D.rho_mem _)) bot_le
    (fun _ hk => by rw [Subgroup.mem_bot.mp hk, map_one])
  have heq := Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hxM : x ∈ fixRel (D.rho L3.x12) (U ⊔ Subgroup.zpowers x) ⊥ :=
    ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers x), hx.2⟩
  rw [← heq, sup_bot_eq] at hxM
  obtain ⟨m, -, hm⟩ := hxM
  rw [commHom_apply] at hm
  exact hxU (hm ▸ hUc _ (D.rho_mem _) m)

end CFSG.Quasithin.Vol2.Ch10.V1C
