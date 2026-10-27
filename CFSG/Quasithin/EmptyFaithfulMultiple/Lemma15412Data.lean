module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Class
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

namespace Setup

variable (h : Setup T M) {𝓗 I : Finset (Subgroup (MulAut (IntMod (VZ T M) h.elem)))}

theorem exists_inv_fix (B : E2.Blocks h.elem M 𝓗 I) {L : Subgroup (MulAut (IntMod (VZ T M) h.elem))}
    (hL : L ∈ I) :
    ∃ t ∈ L, t ∈ autI h.elem (thompsonJ T) ∧ orderOf t = 2 ∧
      ∀ u ∈ commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) L,
        (u ∈ fixV (autI h.elem (thompsonJ T)) ↔ t u = u) := by
  classical
  have hex : ∀ L' : Subgroup (MulAut (IntMod (VZ T M) h.elem)),
      ∃ t : MulAut (IntMod (VZ T M) h.elem),
      L' ∈ I → t ∈ L' ∧ t ∈ autI h.elem (thompsonJ T) ∧ orderOf t = 2 := by
    intro L'
    by_cases hL' : L' ∈ I
    · obtain ⟨t, htL, -, htJ, ht2⟩ := B.exists_orderOf_eq_two h.red h.sylowM hL'
      exact ⟨t, fun _ => ⟨htL, htJ, ht2⟩⟩
    · exact ⟨1, fun h' => absurd h' hL'⟩
  choose t ht using hex
  have hJ := B.autI_thompsonJ_eq h.sylowM h.solv h.red h.notJ t (fun L' hL' => ht L' hL')
  refine ⟨t L, (ht L hL).1, (ht L hL).2.1, (ht L hL).2.2, fun u hu =>
    ⟨fun hfix => hfix _ (ht L hL).2.1, fun htu => ?_⟩⟩
  intro x hx
  rw [hJ] at hx
  have hle : (⨆ L' ∈ I, Subgroup.zpowers (t L')) ≤
      MulAction.stabilizer (MulAut (IntMod (VZ T M) h.elem)) u := by
    refine iSup₂_le fun L' hL' => Subgroup.zpowers_le.2 ?_
    rw [MulAction.mem_stabilizer_iff]
    by_cases hLL : L' = L
    · subst hLL
      exact htu
    · exact B.hb.triv L' (B.sub hL') L (B.sub hL) hLL (t L') (ht L' hL').1 u hu
  exact hle hx

theorem data {Y : Subgroup G} (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ Nat.card (autI h.elem Y) = 3 ^ s ∧
      IsElemAbelian 3 (autI h.elem Y) ∧
      (∀ g ∈ autI h.elem M, B1.conjAut g (autI h.elem Y) = autI h.elem Y) ∧
      Nat.card (commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) (autI h.elem Y)) = 4 ^ s ∧
      Nat.card ↥(commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) (autI h.elem Y) ⊓
        fixV (autI h.elem (thompsonJ T))) = 2 ^ s ∧
      ∀ d : MulAut (IntMod (VZ T M) h.elem), (∃ k : ℕ, d ^ 2 ^ k = 1) →
        (∀ x ∈ autI h.elem Y, d * x = x * d) →
        ∀ u ∈ commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) (autI h.elem Y), d u = u := by
  have hW : ∀ w : IntMod (VZ T M) h.elem, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨𝓗, I, B, hI2⟩ := h.exists_blocks
  have hp : ∀ {f : MulAut (IntMod (VZ T M) h.elem)}, orderOf f = 3 → f ^ 3 = 1 := fun hf => by
    rw [← hf]
    exact pow_orderOf_eq_one _
  rcases h.classify B hI2 hY hYM with
    ⟨L, hL, f, hf, hf3, hD, hfix⟩ | ⟨L₁, hL₁, L₂, hL₂, h12, hI', f₁, hf₁, f₂, hf₂, h3₁, h3₂, hD, -⟩
  ·
    obtain ⟨t, htL, -, ht2, htfix⟩ := h.exists_inv_fix B hL
    have hUf := commSub_zpowers_eq hW B.hb (B.sub hL) hf hf3
    refine ⟨1, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hD, Nat.card_zpowers, hf3, pow_one]
    · rw [hD]
      exact isElemAbelian_zpowers (hp hf3)
    · rw [hD]
      exact conjAut_zpowers_of_fix B hL hf hf3 hfix
    · rw [hD, hUf, B.hb.card_comm L (B.sub hL), pow_one]
    · have heq : commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) (autI h.elem Y) ⊓
          fixV (autI h.elem (thompsonJ T)) =
          fixV (Subgroup.zpowers t) ⊓ commSub ⊤ L := by
        rw [hD, hUf]
        ext u
        constructor
        · rintro ⟨hu, hfx⟩
          exact ⟨mem_fixV_zpowers.mpr ((htfix u hu).mp hfx), hu⟩
        · rintro ⟨hfx, hu⟩
          exact ⟨hu, (htfix u hu).mpr (mem_fixV_zpowers.mp hfx)⟩
      rw [heq, card_fixV_zpowers_inf hW B.hb (B.sub hL) htL ht2, pow_one]
    · intro d hd hdc u hu
      rw [hD, hUf] at hu
      exact fix_of_commute hW B.hb (B.sub hL) hf hf3 hd
        (hdc f (hD ▸ Subgroup.mem_zpowers f)) u hu
  ·
    obtain ⟨t₁, ht₁L, ht₁J, ht₁2, ht₁fix⟩ := h.exists_inv_fix B hL₁
    obtain ⟨t₂, ht₂L, ht₂J, ht₂2, ht₂fix⟩ := h.exists_inv_fix B hL₂
    have s₁ := B.sub hL₁
    have s₂ := B.sub hL₂
    have hU : commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) (autI h.elem Y) =
        commSub ⊤ L₁ ⊔ commSub ⊤ L₂ := by
      rw [hD, commSub_sup_eq, commSub_zpowers_eq hW B.hb s₁ hf₁ h3₁,
        commSub_zpowers_eq hW B.hb s₂ hf₂ h3₂]
    have hinf := commSub_inf_eq_bot_of_ne hW B.hb s₁ s₂ h12
    have hc : ∀ {X₁ X₂ : Subgroup (IntMod (VZ T M) h.elem)}, ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a :=
      fun a _ b _ => mul_comm a b
    refine ⟨2, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hD, card_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂]
      norm_num
    · rw [hD]
      exact comm_of_mem_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂
    · rw [hD]
      exact conjAut_sup_zpowers B hL₁ hL₂ h12 hI' hf₁ hf₂ h3₁ h3₂
    · have h1 := card_sup_mul_card_inf_of_commute (hc (X₁ := commSub ⊤ L₁) (X₂ := commSub ⊤ L₂))
      rw [hinf, Subgroup.card_bot, mul_one, B.hb.card_comm L₁ s₁, B.hb.card_comm L₂ s₂] at h1
      rw [hU, h1]
      norm_num
    · set X₁ := fixV (Subgroup.zpowers t₁) ⊓ commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) L₁
        with hX₁
      set X₂ := fixV (Subgroup.zpowers t₂) ⊓ commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) L₂
        with hX₂
      have heq : commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) (autI h.elem Y) ⊓
          fixV (autI h.elem (thompsonJ T)) = X₁ ⊔ X₂ := by
        rw [hU]
        apply le_antisymm
        · rintro u ⟨hu, hfx⟩
          obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
          have e₁ : t₁ u₂ = u₂ := B.hb.triv L₁ s₁ L₂ s₂ h12 t₁ ht₁L u₂ hu₂
          have e₂ : t₂ u₁ = u₁ := B.hb.triv L₂ s₂ L₁ s₁ (Ne.symm h12) t₂ ht₂L u₁ hu₁
          have f₁' := hfx t₁ ht₁J
          have f₂' := hfx t₂ ht₂J
          rw [map_mul, e₁, mul_left_inj] at f₁'
          rw [map_mul, e₂, mul_right_inj] at f₂'
          exact Subgroup.mul_mem_sup ⟨mem_fixV_zpowers.mpr f₁', hu₁⟩ ⟨mem_fixV_zpowers.mpr f₂', hu₂⟩
        · refine sup_le ?_ ?_
          · rintro x ⟨hfx, hx⟩
            exact ⟨Subgroup.mem_sup_left hx, (ht₁fix x hx).mpr (mem_fixV_zpowers.mp hfx)⟩
          · rintro x ⟨hfx, hx⟩
            exact ⟨Subgroup.mem_sup_right hx, (ht₂fix x hx).mpr (mem_fixV_zpowers.mp hfx)⟩
      have hXinf : X₁ ⊓ X₂ = ⊥ :=
        le_bot_iff.1 ((inf_le_inf inf_le_right inf_le_right).trans hinf.le)
      have h1 := card_sup_mul_card_inf_of_commute (hc (X₁ := X₁) (X₂ := X₂))
      rw [hXinf, Subgroup.card_bot, mul_one, card_fixV_zpowers_inf hW B.hb s₁ ht₁L ht₁2,
        card_fixV_zpowers_inf hW B.hb s₂ ht₂L ht₂2] at h1
      rw [heq, h1]
      norm_num
    · intro d hd hdc u hu
      rw [hU] at hu
      have hd₁ := fix_of_commute hW B.hb s₁ hf₁ h3₁ hd
        (hdc f₁ (hD ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers f₁)))
      have hd₂ := fix_of_commute hW B.hb s₂ hf₂ h3₂ hd
        (hdc f₂ (hD ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers f₂)))
      have hle : commSub (⊤ : Subgroup (IntMod (VZ T M) h.elem)) L₁ ⊔ commSub ⊤ L₂ ≤
          fixV (Subgroup.zpowers d) :=
        sup_le (fun x hx => mem_fixV_zpowers.mpr (hd₁ x hx))
          (fun x hx => mem_fixV_zpowers.mpr (hd₂ x hx))
      exact mem_fixV_zpowers.mp (hle hu)


variable {Y : Subgroup G}
include h

theorem le_normalizer_of_mem (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    M ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨s, -, -, -, hnorm, -⟩ := h.data hY hYM
  intro g hg
  have hmem := mem_normalizer_psi h.elem h.le_normalizer hg
    (hnorm _ (convI_mem_autI h.elem hg (h.le_normalizer hg)))
  rwa [← h.eq_psi hY hYM] at hmem

theorem odd_card_autI (hY : IsYFamily T Y) (hYM : Y ≤ M) : Odd (Nat.card (autI h.elem Y)) := by
  obtain ⟨s, -, hcard, -⟩ := h.data hY hYM
  rw [hcard]
  exact Odd.pow (by decide)

theorem isPGroup_inf' (hYM : Y ≤ M) :
    IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
  h.isPGroup_inf.to_le (inf_le_inf_right _ hYM)

theorem pCoreOf_eq (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (VZ T M : Set G) :=
  pCoreOf_eq_inf_centralizer h.elem (hYM.trans h.le_normalizer) (h.odd_card_autI hY hYM)
    (h.isPGroup_inf' hYM)

theorem commutator_eq (hYM : Y ≤ M) :
    ⁅VZ T M, Y⁆ = (commSub ⊤ (autI h.elem Y)).map (E2.valHom h.elem) :=
  commutator_eq_map_commSub h.elem (hYM.trans h.le_normalizer)

theorem three (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ (pCoreOf 2 Y).relIndex Y = 3 ^ s ∧
      (∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) ∧ Nat.card (⁅VZ T M, Y⁆ : Subgroup G) = 4 ^ s ∧
      Nat.card ↥(⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G)) = 2 ^ s := by
  obtain ⟨s, hs, hcard, hel, -, hU, hUJ, -⟩ := h.data hY hYM
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans h.le_normalizer
  refine ⟨s, hs, ?_, fun y hy => ?_, ?_, ?_⟩
  · rw [relIndex_pCoreOf_eq h.elem hYN (h.odd_card_autI hY hYM) (h.isPGroup_inf' hYM), hcard]
  · rw [h.pCoreOf_eq hY hYM]
    refine ⟨Y.pow_mem hy 3, ?_⟩
    have h3 := hel.2 _ (h.convI_mem_autI' hy (hYM hy))
    rw [← map_pow] at h3
    exact (convI_eq_one_iff h.elem ⟨y ^ 3, _⟩).1 h3
  · rw [h.commutator_eq hYM, card_map_valHom, hU]
  · have hJN : thompsonJ T ≤ Subgroup.normalizer (VZ T M : Set G) :=
      (thompsonJ_le_self T).trans h.T_le_normalizer
    have e : ⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G) =
        (commSub ⊤ (autI h.elem Y) ⊓ fixV (autI h.elem (thompsonJ T))).map (E2.valHom h.elem) := by
      rw [map_valHom_inf, E2.map_valHom_fixV hJN, ← h.commutator_eq hYM, ← inf_assoc,
        inf_eq_left.2 (E2.commutator_le_self hYN)]
    rw [e, card_map_valHom, hUJ]

theorem commutator_inf_centralizer (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  have hW : ∀ w : IntMod (VZ T M) h.elem, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hYN : Y ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans h.le_normalizer
  have e : ⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (Y : Set G) =
      (fixV (autI h.elem Y) ⊓ commSub ⊤ (autI h.elem Y)).map (E2.valHom h.elem) := by
    have hUV := E2.commutator_le_self (V := VZ T M) hYN
    rw [map_valHom_inf, E2.map_valHom_fixV hYN, ← h.commutator_eq hYM]
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hUV h1, h2⟩, h1⟩, fun ⟨⟨_, h2⟩, h1⟩ => ⟨h1, h2⟩⟩
  rw [e, fixV_inf_commSub_eq_bot hW (h.odd_card_autI hY hYM), Subgroup.map_bot]

theorem centralizer_commutator_le (hY : IsYFamily T Y) (hYM : Y ≤ M) {y : G} (hy : y ∈ Y)
    (hyU : y ∈ Subgroup.centralizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G)) :
    y ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hW : ∀ w : IntMod (VZ T M) h.elem, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hyN := h.le_normalizer (hYM hy)
  have hyD := h.convI_mem_autI' hy (hYM hy)
  refine (convI_eq_one_iff h.elem ⟨y, hyN⟩).1 ?_
  refine eq_one_of_fix_fixV_commSub hW (h.odd_card_autI hY hYM) (fun w hw => hw _ hyD)
    fun w hw => ?_
  have hwU : w.val ∈ ⁅VZ T M, Y⁆ := by
    rw [h.commutator_eq hYM]
    exact ⟨w, hw, rfl⟩
  apply IntMod.val_injective
  rw [convI_apply_val]
  show y * w.val * y⁻¹ = w.val
  rw [← Subgroup.mem_centralizer_iff.mp hyU w.val hwU, mul_inv_cancel_right]

theorem mem_centralizer_commutator (hY : IsYFamily T Y) (hYM : Y ≤ M) {g : G} (hg : g ∈ M)
    (h2 : ∃ k : ℕ, g ^ 2 ^ k ∈ Subgroup.centralizer (VZ T M : Set G))
    (hc : ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G)) :
    g ∈ Subgroup.centralizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) := by
  obtain ⟨s, -, -, -, -, -, -, hfix⟩ := h.data hY hYM
  set N := Subgroup.normalizer (VZ T M : Set G)
  have hgN : g ∈ N := h.le_normalizer hg
  set d := convI h.elem ⟨g, hgN⟩ with hd
  have hd2 : ∃ k : ℕ, d ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    rw [hd, ← map_pow]
    exact (convI_eq_one_iff h.elem _).2 hk
  have hdc : ∀ x ∈ autI h.elem Y, d * x = x * d := by
    intro x hx
    obtain ⟨y, hyY, hyN, rfl⟩ := h.exists_mem_of_mem_autI hx
    have hcN : g * y * g⁻¹ * y⁻¹ ∈ N := N.mul_mem (N.mul_mem (N.mul_mem hgN hyN) (N.inv_mem hgN))
      (N.inv_mem hyN)
    have h1 : convI h.elem ⟨g * y * g⁻¹ * y⁻¹, hcN⟩ = 1 := (convI_eq_one_iff h.elem _).2 (hc y hyY)
    have e : (⟨g * y * g⁻¹ * y⁻¹, hcN⟩ : N) = ⟨g, hgN⟩ * ⟨y, hyN⟩ * (⟨g, hgN⟩ : N)⁻¹ *
        (⟨y, hyN⟩ : N)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc d * convI h.elem ⟨y, hyN⟩ = (d * convI h.elem ⟨y, hyN⟩ * d⁻¹ *
          (convI h.elem ⟨y, hyN⟩)⁻¹) * (convI h.elem ⟨y, hyN⟩ * d) := by group
      _ = convI h.elem ⟨y, hyN⟩ * d := by rw [hd, h1, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rw [h.commutator_eq hYM] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  have h1 := hfix d hd2 hdc w hw
  have h2' : (d w).val = w.val := congrArg IntMod.val h1
  rw [hd, convI_apply_val] at h2'
  show w.val * g = g * w.val
  calc w.val * g = (g * w.val * g⁻¹) * g := by rw [h2']
    _ = g * w.val := by group

theorem not_thompsonJ_le (hY : IsYFamily T Y) (hYM : Y ≤ M) :
    ¬ thompsonJ T ≤ Subgroup.centralizer ((⁅VZ T M, Y⁆ : Subgroup G) : Set G) := by
  intro hle
  obtain ⟨s, hs, -, -, hU, hUJ⟩ := h.three hY hYM
  have e : ⁅VZ T M, Y⁆ ⊓ Subgroup.centralizer (thompsonJ T : Set G) = ⁅VZ T M, Y⁆ :=
    inf_eq_left.2 (Subgroup.le_centralizer_iff.mp hle)
  rw [e, hU] at hUJ
  rcases hs with rfl | rfl <;> norm_num at hUJ

theorem pCoreOf_ne_bot' (hY : IsYFamily T Y) (hYM : Y ≤ M) : pCoreOf 2 Y ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  rw [h.pCoreOf_eq hY hYM] at hbot
  have hnorm := h.le_normalizer_of_mem hY hYM
  have hYC : Y ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxM : x ∈ M := pCoreOf_le 2 M hx
    have hyM : y ∈ M := hYM hy
    have h1 : y * x * y⁻¹ * x⁻¹ ∈ Y := by
      have h0 : x * y⁻¹ * x⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hnorm hxM) y⁻¹).mp (Y.inv_mem hy)
      have := Y.mul_mem hy h0
      simpa [mul_assoc] using this
    have h2 : y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 M := by
      have h0 : y * x * y⁻¹ ∈ pCoreOf 2 M :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hyM) x).mp hx
      exact (pCoreOf 2 M).mul_mem h0 ((pCoreOf 2 M).inv_mem hx)
    have h3 : y * x * y⁻¹ * x⁻¹ ∈ Y ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      ⟨h1, (h.cent.symm ▸ h2 : y * x * y⁻¹ * x⁻¹ ∈ M ⊓ _).2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    calc x * y = (y * x * y⁻¹ * x⁻¹)⁻¹ * (y * x) := by group
      _ = y * x := by rw [h3, inv_one, one_mul]
  have hYQ : Y ≤ pCoreOf 2 M := fun y hy => h.charTwo ⟨hYM hy, hYC hy⟩
  exact not_le_of_isPGroup hY (pCoreOf_isPGroup 2 M) hYQ

theorem eq_normalizer (hY : IsYFamily T Y) (hYM : Y ≤ M) : M = Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := h.le_normalizer_of_mem hY hYM
  have h2 : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
    ⟨pCoreOf 2 Y, h.pCoreOf_ne_bot' hY hYM, pCoreOf_isPGroup 2 Y, rfl⟩
  have hNN := normalizer_le_normalizer_pCoreOf 2 Y
  have heq := h.inM.1.2 _ h2 (hle.trans hNN)
  exact le_antisymm hle (heq ▸ hNN)

end Setup

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
