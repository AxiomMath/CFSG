module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3TenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3TenHyper
public import CFSG.Quasithin.Background.B1Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c167_card_ge_of_inverted_aux {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w * w = 1) {z : MulAut W} (hz : z * z = 1) (n : ℕ) :
    ∀ (T : Subgroup (MulAut W)) (E : Subgroup W), (∀ t ∈ T, t ^ 7 = 1) →
      (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → Nat.card T = 7 ^ n → (∀ t ∈ T, z * t * z⁻¹ = t⁻¹) →
      (∀ t ∈ T, ∀ e ∈ E, t e ∈ E) → (∀ e ∈ E, z e ∈ E) →
      (∀ t ∈ T, (∀ e ∈ E, t e = e) → t = 1) → 2 ^ (6 * n) ≤ Nat.card E := by
  have hsq' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hsq w
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  induction n with
  | zero =>
    intro T E _ _ _ _ _ _ _
    rw [Nat.mul_zero, pow_zero]
    exact Nat.card_pos
  | succ n ih =>
    intro T E hT7 hTc hTcard hinv hTE hzE hfaith
    have hT1 : T ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hTcard
      have : 1 < 7 ^ (n + 1) := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    obtain ⟨B, hBT, hBcard, e₀, he₀E, he₀B, t₀, ht₀, ht₀e⟩ :=
      s16c167b_hyperplane_fixed_moved hsq hT7 hTc hT1 hTE hfaith
    have hBcard' : Nat.card B = 7 ^ n := by
      have h : Nat.card B * 7 = 7 ^ n * 7 := by rw [hBcard, hTcard, pow_succ]
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    have hBE : ∀ b ∈ B, ∀ e ∈ E, b e ∈ E := fun b hb e he => hTE b (hBT hb) e he
    have hodd : Odd (Nat.card B) := by
      rw [hBcard']
      exact Odd.pow (by decide)
    obtain ⟨hdec, hinf⟩ := B1.coprime_decomp hsq' hodd hBE
    have hCT : ∀ t ∈ T, ∀ c ∈ E ⊓ fixV B, t c ∈ E ⊓ fixV B := by
      intro t ht c hc
      refine ⟨hTE t ht c hc.1, fun b hb => ?_⟩
      calc b (t c) = (b * t) c := rfl
        _ = (t * b) c := by rw [hTc b (hBT hb) t ht]
        _ = t (b c) := rfl
        _ = t c := by rw [hc.2 b hb]
    have hCz : ∀ c ∈ E ⊓ fixV B, z c ∈ E ⊓ fixV B := by
      intro c hc
      refine ⟨hzE c hc.1, fun b hb => ?_⟩
      have h1 : z * b * z = b⁻¹ := by
        have := hinv b (hBT hb)
        rwa [hzinv] at this
      have h2 : b * z = z * b⁻¹ := by
        calc b * z = (z * z) * b * z := by rw [hz, one_mul]
          _ = z * (z * b * z) := by group
          _ = z * b⁻¹ := by rw [h1]
      calc b (z c) = (b * z) c := rfl
        _ = (z * b⁻¹) c := by rw [h2]
        _ = z (b⁻¹ c) := rfl
        _ = z c := by rw [hc.2 b⁻¹ (B.inv_mem hb)]
    have hE'B : ∀ b ∈ B, ∀ e ∈ commSub E B, b e ∈ commSub E B := by
      intro b hb e he
      refine s16c167_commSub_stable (hBE b hb) (fun x hx => ?_) he
      have h := hTc b (hBT hb) x (hBT hx)
      rw [show b * x * b⁻¹ = x by rw [h]; group]
      exact hx
    have hE'T : ∀ t ∈ T, ∀ e ∈ commSub E B, t e ∈ commSub E B := by
      intro t ht e he
      refine s16c167_commSub_stable (hTE t ht) (fun x hx => ?_) he
      have h := hTc t ht x (hBT hx)
      rw [show t * x * t⁻¹ = x by rw [h]; group]
      exact hx
    have hE'z : ∀ e ∈ commSub E B, z e ∈ commSub E B := by
      intro e he
      refine s16c167_commSub_stable hzE (fun x hx => ?_) he
      rw [hinv x (hBT hx)]
      exact B.inv_mem hx
    have hfaithB : ∀ b ∈ B, (∀ e ∈ commSub E B, b e = e) → b = 1 := by
      intro b hb hbE'
      apply hfaith b (hBT hb)
      intro e he
      have hsup : e ∈ (E ⊓ fixV B) ⊔ commSub E B := by rw [hdec]; exact he
      have hle : (E ⊓ fixV B) ⊔ commSub E B ≤
          MonoidHom.eqLocus b.toMonoidHom (MonoidHom.id W) := by
        refine sup_le (fun c hc => ?_) (fun c hc => hbE' c hc)
        exact hc.2 b hb
      exact hle hsup
    have hE'card : 2 ^ (6 * n) ≤ Nat.card (commSub E B) :=
      ih B (commSub E B) (fun b hb => hT7 b (hBT hb))
        (fun s hs t ht => hTc s (hBT hs) t (hBT ht)) hBcard'
        (fun b hb => hinv b (hBT hb)) hE'B hE'z hfaithB
    have hzp : Subgroup.zpowers t₀ ≤ T := Subgroup.zpowers_le.2 ht₀
    have hCt : ∀ x ∈ Subgroup.zpowers t₀, ∀ w ∈ E ⊓ fixV B, x w ∈ E ⊓ fixV B :=
      fun x hx w hw => hCT x (hzp hx) w hw
    have hUC : commSub (E ⊓ fixV B) (Subgroup.zpowers t₀) ≤ E ⊓ fixV B :=
      commSub_le_of_invariant hCt
    have hnorm : ∀ x ∈ Subgroup.zpowers t₀, ∀ g : MulAut W, g ∈ Subgroup.zpowers t₀ →
        g * x * g⁻¹ ∈ Subgroup.zpowers t₀ := by
      intro x hx g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [show t₀ ^ l * t₀ ^ k * (t₀ ^ l)⁻¹ = t₀ ^ k by group]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t₀) k
    have hτU : t₀ ∈ stabSub (commSub (E ⊓ fixV B) (Subgroup.zpowers t₀)) := by
      refine s16c167_mem_stabSub_of_forward (fun u hu => ?_) (fun u hu => ?_)
      · exact s16c167_commSub_stable (hCT t₀ ht₀)
          (fun x hx => hnorm x hx t₀ (Subgroup.mem_zpowers t₀)) hu
      · exact s16c167_commSub_stable (hCT t₀⁻¹ (T.inv_mem ht₀))
          (fun x hx => hnorm x hx t₀⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t₀))) hu
    have hzU : z ∈ stabSub (commSub (E ⊓ fixV B) (Subgroup.zpowers t₀)) := by
      have hf : ∀ u ∈ commSub (E ⊓ fixV B) (Subgroup.zpowers t₀),
          z u ∈ commSub (E ⊓ fixV B) (Subgroup.zpowers t₀) := by
        intro u hu
        refine s16c167_commSub_stable hCz (fun x hx => ?_) hu
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← conj_zpow, hinv t₀ ht₀]
        exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t₀)) k
      refine s16c167_mem_stabSub_of_forward hf (fun u hu => ?_)
      rw [hzinv]
      exact hf u hu
    have hU1 : commSub (E ⊓ fixV B) (Subgroup.zpowers t₀) ≠ ⊥ := by
      intro h
      have hmem : t₀ e₀ * e₀⁻¹ ∈ commSub (E ⊓ fixV B) (Subgroup.zpowers t₀) :=
        Subgroup.subset_closure ⟨t₀, Subgroup.mem_zpowers t₀, e₀, ⟨he₀E, he₀B⟩, rfl⟩
      rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact ht₀e hmem
    have hoddY : Odd (Nat.card (Subgroup.zpowers t₀)) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (hT7 t₀ ht₀))
    have hfix : ∀ u ∈ commSub (E ⊓ fixV B) (Subgroup.zpowers t₀), t₀ u = u → u = 1 := by
      intro u hu hfixu
      obtain ⟨-, hinfY⟩ := B1.coprime_decomp hsq' hoddY hCt
      have hu' : u ∈ ((E ⊓ fixV B) ⊓ fixV (Subgroup.zpowers t₀)) ⊓
          commSub (E ⊓ fixV B) (Subgroup.zpowers t₀) :=
        ⟨⟨hUC hu, (mem_fixV_zpowers_iff_apply).2 hfixu⟩, hu⟩
      rw [hinfY, Subgroup.mem_bot] at hu'
      exact hu'
    have hC6 : 2 ^ 6 ≤ Nat.card (E ⊓ fixV B : Subgroup W) :=
      (s16c167_card_ge_of_seven_inverted_sub hsq hU1 hτU hzU (hT7 t₀ ht₀) hfix hz
        (hinv t₀ ht₀)).trans (Subgroup.card_le_of_le hUC)
    have hcardE : Nat.card E = Nat.card (E ⊓ fixV B : Subgroup W) * Nat.card (commSub E B) := by
      have h := CFSG.Quasithin.card_sup_mul_card_inf (E ⊓ fixV B) (commSub E B)
      rw [hdec, hinf, Subgroup.card_bot, mul_one] at h
      exact h
    calc 2 ^ (6 * (n + 1)) = 2 ^ 6 * 2 ^ (6 * n) := by
          rw [show 6 * (n + 1) = 6 + 6 * n by ring, pow_add]
      _ ≤ Nat.card (E ⊓ fixV B : Subgroup W) * Nat.card (commSub E B) :=
          Nat.mul_le_mul hC6 hE'card
      _ = Nat.card E := hcardE.symm

theorem s16c167_card_ge_of_inverted {n : ℕ} {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w * w = 1) {T : Subgroup (MulAut W)} (hT7 : ∀ t ∈ T, t ^ 7 = 1)
    (hTc : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hTcard : Nat.card T = 7 ^ n) {z : MulAut W}
    (hz : z * z = 1) (hinv : ∀ t ∈ T, z * t * z⁻¹ = t⁻¹) : 2 ^ (6 * n) ≤ Nat.card W := by
  have h := s16c167_card_ge_of_inverted_aux hsq hz n T ⊤ hT7 hTc hTcard hinv
    (fun _ _ _ _ => Subgroup.mem_top _) (fun _ _ => Subgroup.mem_top _)
    (fun t _ ht => MulEquiv.ext fun w => ht w (Subgroup.mem_top w))
  rwa [Subgroup.card_top] at h

theorem s16c167_no_inversion {W : Type} [CommGroup W] [Finite W] (hsq : ∀ w : W, w * w = 1)
    (hcard : Nat.card W ≤ 2 ^ 12) {T : Subgroup (MulAut W)} (hT : IsElemAbelianOfRank 7 3 ↥T)
    {z : MulAut W} (hz : z * z = 1) (hinv : ∀ t ∈ T, z * t * z⁻¹ = t⁻¹) : False := by
  have hT7 : ∀ t ∈ T, t ^ 7 = 1 := fun t ht =>
    congrArg Subtype.val (s16c167_pow_seven_of_isElemAbelianOfRank hT ⟨t, ht⟩)
  have hTc : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    obtain ⟨e⟩ := hT
    intro s hs t ht
    have h : e ⟨s, hs⟩ * e ⟨t, ht⟩ = e ⟨t, ht⟩ * e ⟨s, hs⟩ := mul_comm _ _
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (e.injective h)
  have hTcard : Nat.card T = 7 ^ 3 := by
    rw [s16c167_card_isElemAbelianOfRank hT]
  have h := s16c167_card_ge_of_inverted (n := 3) hsq hT7 hTc hTcard hz hinv
  have h2 : (2 : ℕ) ^ 12 < 2 ^ (6 * 3) := by norm_num
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
