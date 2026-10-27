module

public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c15t_rk_add_of_compl {A B : Subgroup W} (h1 : A ⊓ B = ⊥) (h2 : A ⊔ B = ⊤) :
    rk ↥A + rk ↥B = rk W := by
  have h := rk_sup_add_rk_inf A B
  rw [h1, h2, rk_bot, rk_top] at h
  omega

theorem s16c15t_rk_le_rkIdx_of_swap {φ : MulAut W} {A B : Subgroup W} (hAB : A ⊓ B = ⊥)
    (hφ : A.map φ.toMonoidHom = B) : rk ↥A ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
  have hker : A ⊓ (commHom φ).ker = ⊥ := by
    rw [ker_commHom, eq_bot_iff, ← hAB]
    intro a ha
    refine ⟨ha.1, ?_⟩
    have hfix : φ a = a := mem_fixV_zpowers_iff.1 ha.2
    rw [← hφ]
    exact ⟨a, ha.1, hfix⟩
  have h1 := rk_map_add_rk_inf_ker (commHom φ) A
  rw [hker, rk_bot, add_zero] at h1
  have h2 : rk (A.map (commHom φ)) ≤ rk (commV (Subgroup.zpowers φ)) := by
    rw [commV_zpowers_eq_map]
    exact rk_mono (Subgroup.map_mono le_top)
  rw [rkIdx_fixV_zpowers]
  omega

theorem s16c15t_rk_fixV_split {A B : Subgroup W} {E : Subgroup (MulAut W)}
    (h1 : A ⊓ B = ⊥) (h2 : A ⊔ B = ⊤) (hA : ∀ e ∈ E, ∀ x ∈ A, e x ∈ A)
    (hB : ∀ e ∈ E, ∀ x ∈ B, e x ∈ B) :
    rk ↥(fixV E) = rk ↥(A ⊓ fixV E) + rk ↥(B ⊓ fixV E) := by
  have hsup : A ⊓ fixV E ⊔ B ⊓ fixV E = fixV E := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    intro w hw
    have hwAB : w ∈ A ⊔ B := by rw [h2]; exact Subgroup.mem_top w
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hwAB
    have hfixa : a ∈ fixV E := by
      rw [mem_fixV]
      intro e he
      have heq : e a * e b = a * b := by
        have h := mem_fixV.1 hw e he
        rw [← hab, map_mul] at h
        exact h
      have hc : e a * a⁻¹ = b * (e b)⁻¹ := by
        rw [mul_inv_eq_mul_inv_iff_mul_eq_mul]
        rw [heq, mul_comm]
      have hcA : e a * a⁻¹ ∈ A := A.mul_mem (hA e he a ha) (A.inv_mem ha)
      have hcB : b * (e b)⁻¹ ∈ B := B.mul_mem hb (B.inv_mem (hB e he b hb))
      have hcbot : e a * a⁻¹ ∈ (⊥ : Subgroup W) := by
        rw [← h1]
        exact ⟨hcA, by rw [hc]; exact hcB⟩
      exact mul_inv_eq_one.1 (by simpa using hcbot)
    have hfixb : b ∈ fixV E := by
      rw [mem_fixV]
      intro e he
      have heq : e a * e b = a * b := by
        have h := mem_fixV.1 hw e he
        rw [← hab, map_mul] at h
        exact h
      rw [mem_fixV.1 hfixa e he] at heq
      exact mul_left_cancel heq
    rw [← hab]
    exact Subgroup.mul_mem_sup ⟨ha, hfixa⟩ ⟨hb, hfixb⟩
  have hdisj : A ⊓ fixV E ⊓ (B ⊓ fixV E) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨⟨hxA, -⟩, ⟨hxB, -⟩⟩ := hx
    have hxAB : x ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [h1] at hxAB
    exact hxAB
  have h := rk_sup_add_rk_inf (A ⊓ fixV E) (B ⊓ fixV E)
  rw [hsup, hdisj, rk_bot] at h
  omega

theorem s16c15t_eq_one_of_fix_summand {F₀ F₁ F₂ : Subgroup W} (h12 : F₁ ⊓ F₂ = ⊥)
    (j01 : F₀ ⊔ F₁ = ⊤) (j02 : F₀ ⊔ F₂ = ⊤) {e : MulAut W}
    (hF₁ : ∀ x ∈ F₁, e x ∈ F₁) (hF₂ : ∀ x ∈ F₂, e x ∈ F₂) (he : ∀ x ∈ F₀, e x = x) :
    e = 1 := by
  ext w
  have hfix1 : ∀ y ∈ F₁, e y = y := by
    intro y hy
    have hy_top : y ∈ F₀ ⊔ F₂ := by rw [j02]; exact Subgroup.mem_top y
    obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.1 hy_top
    have hcy : e y * y⁻¹ = e c * c⁻¹ := by
      rw [← hac, map_mul, he a ha, mul_inv_rev]
      rw [show a * e c * (c⁻¹ * a⁻¹) = (a * a⁻¹) * (e c * c⁻¹) by ac_rfl]
      simp
    have hleft : e y * y⁻¹ ∈ F₁ := F₁.mul_mem (hF₁ y hy) (F₁.inv_mem hy)
    have hright : e c * c⁻¹ ∈ F₂ := F₂.mul_mem (hF₂ c hc) (F₂.inv_mem hc)
    have hmem : e y * y⁻¹ ∈ F₁ ⊓ F₂ := ⟨hleft, by rw [hcy]; exact hright⟩
    rw [h12] at hmem
    exact mul_inv_eq_one.1 (by simpa using hmem)
  have hw : w ∈ F₀ ⊔ F₁ := by rw [j01]; exact Subgroup.mem_top w
  obtain ⟨a, ha, y, hy, hay⟩ := Subgroup.mem_sup.1 hw
  simp only [MulAut.one_apply]
  rw [← hay, map_mul, he a ha, hfix1 y hy]

private theorem s16c15t_mul_mem_of_index_two_notMem {A H : Subgroup W}
    (hidx : (H.subgroupOf A).index = 2) {a b : W} (ha : a ∈ A) (hb : b ∈ A)
    (haH : a ∉ H) (hbH : b ∉ H) : a * b ∈ H := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf A) hidx
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  change (⟨a, ha⟩ * ⟨b, hb⟩ : ↥A) ∈ H.subgroupOf A
  rw [h]
  exact ⟨fun hh => absurd (Subgroup.mem_subgroupOf.1 hh) haH,
    fun hh => absurd (Subgroup.mem_subgroupOf.1 hh) hbH⟩

theorem s16c15t_rk_le_of_codim_one (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup W}
    {E : Subgroup (MulAut W)} (hA : ∀ e ∈ E, ∀ x ∈ A, e x ∈ A)
    (hfaith : ∀ e ∈ E, (∀ x ∈ A, e x = x) → e = 1)
    (hcod : rk ↥A ≤ rk ↥(A ⊓ fixV E) + 1) : rk ↥E ≤ rk ↥A - 1 := by
  by_cases hcase : rk ↥A ≤ rk ↥(A ⊓ fixV E)
  · have hHA : A ⊓ fixV E = A := eq_of_le_of_rk_le hW inf_le_left hcase
    have hAle : A ≤ fixV E := by rw [← hHA]; exact inf_le_right
    have hE : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro e he
      exact hfaith e he (fun x hx => mem_fixV.1 (hAle hx) e he)
    rw [hE, rk_bot]
    exact Nat.zero_le _
  · have hHlt : rk ↥(A ⊓ fixV E) < rk ↥A := not_le.1 hcase
    have hrankA : rk ↥A = rk ↥(A ⊓ fixV E) + 1 := by omega
    have hHA : A ⊓ fixV E ≤ A := inf_le_left
    have hcardA : Nat.card ↥A = 2 * Nat.card ↥(A ⊓ fixV E) := by
      have h1 := card_eq_two_pow hW A
      have h2 := card_eq_two_pow hW (A ⊓ fixV E)
      rw [hrankA, pow_succ] at h1
      omega
    have hidx : ((A ⊓ fixV E).subgroupOf A).index = 2 := by
      have h1 := Subgroup.card_mul_index ((A ⊓ fixV E).subgroupOf A)
      have h2 : Nat.card ↥((A ⊓ fixV E).subgroupOf A) = Nat.card ↥(A ⊓ fixV E) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv
      rw [h2, hcardA] at h1
      have hpos : 0 < Nat.card ↥(A ⊓ fixV E) := Nat.card_pos
      rw [mul_comm 2 (Nat.card ↥(A ⊓ fixV E))] at h1
      exact Nat.mul_left_cancel hpos h1
    have hne : A ⊓ fixV E ≠ A := by
      intro h
      rw [h] at hHlt
      exact lt_irrefl _ hHlt
    have hex0 : ∃ x : W, x ∈ A ∧ x ∉ A ⊓ fixV E := by
      by_contra hcon
      have hAH : A ≤ A ⊓ fixV E := by
        intro x hx
        by_contra hxH
        exact hcon ⟨x, hx, hxH⟩
      exact hne (le_antisymm hHA hAH)
    obtain ⟨x₀, hx₀A, hx₀H⟩ := hex0
    have hmemH : ∀ e : E, (e : MulAut W) x₀ * x₀⁻¹ ∈ A ⊓ fixV E := by
      intro e
      by_contra hψ
      have heA : (e : MulAut W) x₀ * x₀⁻¹ ∈ A :=
        A.mul_mem (hA e e.2 x₀ hx₀A) (A.inv_mem hx₀A)
      have hprod := s16c15t_mul_mem_of_index_two_notMem hidx heA hx₀A hψ hx₀H
      have hex : (e : MulAut W) x₀ ∈ A ⊓ fixV E := by
        rwa [show (e : MulAut W) x₀ * x₀⁻¹ * x₀ = (e : MulAut W) x₀ from
          inv_mul_cancel_right _ _] at hprod
      have hfixe : (e : MulAut W)⁻¹ ((e : MulAut W) x₀) = (e : MulAut W) x₀ :=
        mem_fixV.1 ((inf_le_right : A ⊓ fixV E ≤ fixV E) hex) ((e : MulAut W)⁻¹)
          (E.inv_mem e.2)
      have hx₀ : x₀ ∈ A ⊓ fixV E := by
        have h1 : (e : MulAut W)⁻¹ ((e : MulAut W) x₀) = x₀ := by simp
        rw [← h1, hfixe]
        exact hex
      exact hx₀H hx₀
    have hinj : Function.Injective
        (fun e : E => (⟨(e : MulAut W) x₀ * x₀⁻¹, hmemH e⟩ : ↥(A ⊓ fixV E))) := by
      intro e e' hee
      have hee' : (e : MulAut W) x₀ * x₀⁻¹ = (e' : MulAut W) x₀ * x₀⁻¹ :=
        Subtype.ext_iff.1 hee
      have hx0 : (e : MulAut W) x₀ = (e' : MulAut W) x₀ := by
        have h := congrArg (· * x₀) hee'
        simpa only [inv_mul_cancel_right] using h
      have hfixA : ∀ x ∈ A, ((e⁻¹ * e' : E) : MulAut W) x = x := by
        intro x hx
        by_cases hxH : x ∈ A ⊓ fixV E
        · exact mem_fixV.1 ((inf_le_right : A ⊓ fixV E ≤ fixV E) hxH) _
            (E.mul_mem (E.inv_mem e.2) e'.2)
        · have hxx0 : x * x₀ ∈ A ⊓ fixV E :=
            s16c15t_mul_mem_of_index_two_notMem hidx hx hx₀A hxH hx₀H
          have hfix := mem_fixV.1 ((inf_le_right : A ⊓ fixV E ≤ fixV E) hxx0) _
            (E.mul_mem (E.inv_mem e.2) e'.2)
          have hz0 : ((e : MulAut W)⁻¹ * (e' : MulAut W)) x₀ = x₀ := by
            rw [MulAut.mul_apply, ← hx0]
            exact MulAut.inv_apply_self W (e : MulAut W) x₀
          rw [map_mul, hz0] at hfix
          exact mul_right_cancel hfix
      have hg : (e⁻¹ * e' : E) = 1 := by
        apply Subtype.ext
        exact hfaith _ (E.mul_mem (E.inv_mem e.2) e'.2) hfixA
      have h2 : e' = e := by
        have h := congrArg (fun z : E => e * z) hg
        simpa using h
      exact h2.symm
    have hcardE : Nat.card ↥E ≤ Nat.card ↥(A ⊓ fixV E) :=
      Nat.card_le_card_of_injective _ hinj
    have hcardH : Nat.card ↥(A ⊓ fixV E) = 2 ^ rk ↥(A ⊓ fixV E) :=
      card_eq_two_pow hW (A ⊓ fixV E)
    have hdvd : 2 ^ rk ↥E ∣ Nat.card ↥E := pow_padicValNat_dvd
    have hle : 2 ^ rk ↥E ≤ 2 ^ rk ↥(A ⊓ fixV E) :=
      calc 2 ^ rk ↥E ≤ Nat.card ↥E := Nat.le_of_dvd Nat.card_pos hdvd
        _ ≤ Nat.card ↥(A ⊓ fixV E) := hcardE
        _ = 2 ^ rk ↥(A ⊓ fixV E) := hcardH
    have hRE : rk ↥E ≤ rk ↥(A ⊓ fixV E) :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).1 hle
    omega

theorem s16c15t_rk_commSub_le_one {A : Subgroup W} {E : Subgroup (MulAut W)}
    (hA : ∀ e ∈ E, ∀ x ∈ A, e x ∈ A) (hcod : rk ↥A ≤ rk ↥(A ⊓ fixV E) + 1) {e : MulAut W}
    (he : e ∈ E) : rk ↥(commSub A (Subgroup.zpowers e)) ≤ 1 := by
  have hinv : ∀ x ∈ Subgroup.zpowers e, ∀ w ∈ A, x w ∈ A := by
    intro x hx w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hE : e ^ n ∈ E := E.zpow_mem he n
    exact hA _ hE w hw
  have h1 := rk_commSub_add_rk_inf_fixV hinv
  have h2 : A ⊓ fixV E ≤ A ⊓ fixV (Subgroup.zpowers e) := by
    refine inf_le_inf_left _ ?_
    intro v hv
    exact mem_fixV_zpowers_iff.2 (hv e he)
  have h3 := rk_mono h2
  omega

theorem s16c15t_core (hW : ∀ w : W, w ^ 2 = 1) {F : Fin 3 → Subgroup W}
    (hmeet : ∀ i j, i ≠ j → F i ⊓ F j = ⊥) (hjoin : ∀ i j, i ≠ j → F i ⊔ F j = ⊤)
    {E : Subgroup (MulAut W)}
    (hperm : ∀ e ∈ E, ∀ i, ∃ j, (F i).map (e : MulAut W).toMonoidHom = F j)
    (hr : 4 ≤ rk ↥(F 0)) (hfix : rkIdx (fixV E) ≤ 3) :
    (∀ e ∈ E, ∀ i, (F i).map (e : MulAut W).toMonoidHom = F i) ∧
    (∀ e ∈ E, (∀ x ∈ F 0, e x = x) → e = 1) ∧
    (∀ e ∈ E, rk ↥(commSub (F 0) (Subgroup.zpowers e)) ≤ 1) ∧
    rk ↥E ≤ rk ↥(F 0) - 1 := by
  have hcompl : ∀ i j, i ≠ j → rk ↥(F i) + rk ↥(F j) = rk W :=
    fun i j hij => s16c15t_rk_add_of_compl (hmeet i j hij) (hjoin i j hij)
  have h01 := hcompl 0 1 (by decide)
  have h02 := hcompl 0 2 (by decide)
  have h12 := hcompl 1 2 (by decide)
  have hr1 : rk ↥(F 1) = rk ↥(F 0) := by omega
  have hr2 : rk ↥(F 2) = rk ↥(F 0) := by omega
  have hrall : ∀ i, rk ↥(F i) = rk ↥(F 0) := by
    intro i
    fin_cases i
    · rfl
    · exact hr1
    · exact hr2
  have hstab : ∀ e ∈ E, ∀ i, (F i).map (e : MulAut W).toMonoidHom = F i := by
    intro e he i
    obtain ⟨j, hj⟩ := hperm e he i
    by_cases hij : i = j
    · rw [hj, hij]
    · exfalso
      have h1 := s16c15t_rk_le_rkIdx_of_swap (hmeet i j hij) hj
      have h2 : fixV E ≤ fixV (Subgroup.zpowers e) := by
        intro v hv
        exact mem_fixV_zpowers_iff.2 (hv e he)
      have h3 := rkIdx_anti h2
      have h4 := hrall i
      omega
  have hinv : ∀ e ∈ E, ∀ i, ∀ x ∈ F i, e x ∈ F i := by
    intro e he i x hx
    have : e x ∈ (F i).map (e : MulAut W).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hstab e he i] at this
  have hsplit : ∀ i j, i ≠ j → rk ↥(fixV E) = rk ↥(F i ⊓ fixV E) + rk ↥(F j ⊓ fixV E) :=
    fun i j hij => s16c15t_rk_fixV_split (hmeet i j hij) (hjoin i j hij) (hinv · · i)
      (hinv · · j)
  have hidx := rk_add_rkIdx (fixV E)
  have s01 := hsplit 0 1 (by decide)
  have s02 := hsplit 0 2 (by decide)
  have s12 := hsplit 1 2 (by decide)
  have hcod : rk ↥(F 0) ≤ rk ↥(F 0 ⊓ fixV E) + 1 := by omega
  have hfaith : ∀ e ∈ E, (∀ x ∈ F 0, e x = x) → e = 1 := fun e he hfx =>
    s16c15t_eq_one_of_fix_summand (hmeet 1 2 (by decide)) (hjoin 0 1 (by decide))
      (hjoin 0 2 (by decide)) (hinv e he 1) (hinv e he 2) hfx
  exact ⟨hstab, hfaith,
    fun e he => s16c15t_rk_commSub_le_one (hinv · · 0) hcod he,
    s16c15t_rk_le_of_codim_one hW (hinv · · 0) hfaith hcod⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
