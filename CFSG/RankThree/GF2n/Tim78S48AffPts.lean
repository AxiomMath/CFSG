module

public import CFSG.RankThree.GF2n.Tim78S48AffElem
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

open Aff

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H


theorem exists_Q_conj_eq (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {b' : G}
    (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1) {c : G} (hc : c ∈ H.aC g) :
    ∃ y₁ ∈ Q, y₁ * b' * y₁⁻¹ = c * b' := by
  obtain ⟨-, hsurj⟩ := H.card_aC h48 hP hBgQ h1 hcent hb' hb'1
  obtain ⟨p, hp, β, hβ, hpc⟩ := hsurj c hc
  obtain ⟨t, ht, htβ⟩ := H.exists_comm_eq_T h48 hP h1.relIndex_T hb' hb'1 (B.inv_mem hβ)
  refine ⟨p * t, Q.mul_mem (H.P_le_Q hp) (H.T_le_Q ht), ?_⟩
  have hβ2 : β * β = 1 := IsElemAbelian.mul_self_eq_one H.elemAb hβ
  have h1c : ⁅t, b'⁆ = β := by rw [← commutatorElement_inv, htβ, inv_inv]
  have e1 : (p * t) * b' * (p * t)⁻¹ = p * (⁅t, b'⁆ * b') * p⁻¹ := by
    simp only [commutatorElement_def]; group
  have hpβ : p * β * p⁻¹ = β := by
    rw [(H.center_Q hβ (H.P_le_Q hp)).symm]; group
  have hβc : β * c = c * β := H.center_Q hβ (H.aC_le_Q hc)
  rw [e1, h1c]
  calc p * (β * b') * p⁻¹ = (p * β * p⁻¹) * (p * b' * p⁻¹) := by group
    _ = β * (⁅p, b'⁆ * b') := by rw [hpβ]; simp only [commutatorElement_def]; group
    _ = β * (c * β * b') := by rw [hpc]
    _ = (β * c) * β * b' := by group
    _ = (c * β) * β * b' := by rw [hβc]
    _ = c * (β * β) * b' := by group
    _ = c * b' := by rw [hβ2]; group

theorem exists_Tg_not_cent_B (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTgnc : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t) {β : G} (hβ : β ∈ B)
    (hβ1 : β ≠ 1) : ∃ t' ∈ conjSubgroup g T, t' * β ≠ β * t' := by
  by_contra hcon
  push Not at hcon
  apply hTgnc
  intro t ht b hb
  have hM : t ∈ M := H.normalizer_eq_and_centralizer_le.2 β hβ hβ1
    (Subgroup.mem_centralizer_singleton_iff.mpr (hcon t ht))
  have hnorm : t ∈ Subgroup.normalizer (B : Set G) := H.M_le_normalizer_B hM
  have h2 : ⁅b, t⁆ ∈ B := by
    have e : ⁅b, t⁆ = b * (t * b⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.mp hnorm b⁻¹).mp (B.inv_mem hb))
  have h3 : ⁅b, t⁆ ∈ conjSubgroup g B := h48.comm_Tg b hb t ht
  have h4 : ⁅b, t⁆ ∈ B ⊓ conjSubgroup g B := ⟨h2, h3⟩
  rw [H.B_inf_Bg hP, Subgroup.mem_bot] at h4
  exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm

theorem exists_good_conj (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTgnc : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t) {c : G} (hc : c ∈ H.aC g)
    (hcB : c ∉ B) :
    ∃ y₁ ∈ Q, ∃ t' ∈ conjSubgroup g T, t' * (y₁⁻¹ * c * y₁) ≠ (y₁⁻¹ * c * y₁) * t' := by
  by_cases hc0 : ∃ t' ∈ conjSubgroup g T, t' * c ≠ c * t'
  · obtain ⟨t', ht', hne⟩ := hc0
    exact ⟨1, Q.one_mem, t', ht', by simpa using hne⟩
  push Not at hc0
  have hncQ : ∃ x ∈ Q, x * c ≠ c * x := by
    by_contra hcon
    push Not at hcon
    apply hcB
    rw [← H.base_facts.2.1]
    exact ⟨H.aC_le_Q hc, Subgroup.mem_centralizer_iff.mpr hcon⟩
  obtain ⟨x, hx, hxc⟩ := hncQ
  have hβ : ⁅x, c⁆ ∈ B := H.commutator_mem hx (H.aC_le_Q hc)
  have hβ1 : ⁅x, c⁆ ≠ 1 := fun h => hxc (commutatorElement_eq_one_iff_mul_comm.mp h)
  obtain ⟨t', ht', hne⟩ := H.exists_Tg_not_cent_B h48 hP hTgnc hβ hβ1
  refine ⟨x⁻¹, Q.inv_mem hx, t', ht', fun heq => hne ?_⟩
  have e : x⁻¹⁻¹ * c * x⁻¹ = ⁅x, c⁆ * c := by simp only [commutatorElement_def]; group
  rw [e] at heq
  have hct := hc0 t' ht'
  have h2 : t' * ⁅x, c⁆ * c = ⁅x, c⁆ * t' * c := by
    calc t' * ⁅x, c⁆ * c = t' * (⁅x, c⁆ * c) := by group
      _ = (⁅x, c⁆ * c) * t' := heq
      _ = ⁅x, c⁆ * (c * t') := by group
      _ = ⁅x, c⁆ * (t' * c) := by rw [hct]
      _ = ⁅x, c⁆ * t' * c := by group
  exact mul_right_cancel h2


theorem aL_le_conj_M
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) :
    H.aC g ⊔ conjSubgroup g B ≤ conjSubgroup g M :=
  sup_le (H.aC_le_conj_M hcent) (Subgroup.map_mono H.B_le_M)

theorem hyp48_pair (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {k : G} (hk : k ∈ Q) :
    Hyp48 M B T (g⁻¹ * k * g) := by
  have hkN : k ∈ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
    H.Q_le_normalizer_aL h48 hP hBgQ h1.part_W hcent hk
  have hBgL : conjSubgroup g B ≤ H.aC g ⊔ conjSubgroup g B := le_sup_right
  have hLM := H.aL_le_conj_M hcent
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_conj_iff.mp hz
    have hL : k * (g * b * g⁻¹) * k⁻¹ ∈ H.aC g ⊔ conjSubgroup g B :=
      conj_le_of_mem_normalizer hkN hBgL
        (mem_conj_iff.mpr ⟨g * b * g⁻¹, mem_conj_iff.mpr ⟨b, hb, rfl⟩, rfl⟩)
    have := mem_conjSubgroup.mp (hLM hL)
    convert this using 1
    group
  · intro a ha t ht
    obtain ⟨b, hb, rfl⟩ := mem_conj_iff.mp ha
    have ha₁ : k * (g * b * g⁻¹) * k⁻¹ ∈ H.aC g ⊔ conjSubgroup g B :=
      conj_le_of_mem_normalizer hkN hBgL
        (mem_conj_iff.mpr ⟨g * b * g⁻¹, mem_conj_iff.mpr ⟨b, hb, rfl⟩, rfl⟩)
    have ht' : g * t * g⁻¹ ∈ conjSubgroup g T :=
      mem_conj_iff.mpr ⟨t, ht, rfl⟩
    have hcm := H.L_comm_Tg h48 h1 hTgW hcent ha₁ ht'
    have e : ⁅(g⁻¹ * k * g) * b * (g⁻¹ * k * g)⁻¹, t⁆ =
        g⁻¹ * ⁅k * (g * b * g⁻¹) * k⁻¹, g * t * g⁻¹⁆ * g := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mem_conjSubgroup.mp hcm
  · intro b hb t ht
    obtain ⟨t₀, ht₀, rfl⟩ := mem_conj_iff.mp ht
    have ht' : g * t₀ * g⁻¹ ∈ conjSubgroup g T := mem_conj_iff.mpr ⟨t₀, ht₀, rfl⟩
    have hd : k⁻¹ * (g * b * g⁻¹) * k ∈ H.aC g ⊔ conjSubgroup g B :=
      conj_le_of_mem_normalizer (Subgroup.inv_mem _ hkN) hBgL
        (mem_conj_iff.mpr ⟨g * b * g⁻¹, mem_conj_iff.mpr ⟨b, hb, rfl⟩,
          by simp⟩)
    have hcm := H.L_comm_Tg h48 h1 hTgW hcent hd ht'
    obtain ⟨b'', hb'', hbb⟩ := mem_conj_iff.mp hcm
    refine mem_conj_iff.mpr ⟨b'', hb'', ?_⟩
    have e : ⁅b, (g⁻¹ * k * g) * t₀ * (g⁻¹ * k * g)⁻¹⁆ =
        g⁻¹ * k * ⁅k⁻¹ * (g * b * g⁻¹) * k, g * t₀ * g⁻¹⁆ * k⁻¹ * g := by
      simp only [commutatorElement_def]; group
    rw [e, hbb]
    group


theorem point_through_good (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g')
    {c : G} (hc : c ∈ H.aC g) (hc1 : c ≠ 1)
    (hgood : ∃ t' ∈ conjSubgroup g T, t' * c ≠ c * t') :
    ∃ r ∈ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G),
      c ∈ conjSubgroup r B ∧ conjSubgroup r B ≤ H.aC g ⊔ conjSubgroup g B := by
  set L : Subgroup G := H.aC g ⊔ conjSubgroup g B with hLdef
  obtain ⟨⟨b', hb'⟩, hb'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (H.conj_B_ne_bot g)
  have hb'1' : b' ≠ 1 := fun h => hb'1 (Subtype.ext h)
  obtain ⟨k, hk, hkb⟩ := H.exists_Q_conj_eq h48 hP hBgQ h1 hcent hb' hb'1' hc
  have hkN : k ∈ Subgroup.normalizer (L : Set G) :=
    H.Q_le_normalizer_aL h48 hP hBgQ h1.part_W hcent hk
  have h48' := H.hyp48_pair h48 hP hBgQ h1 hTgW hcent hk
  have hb'B : g⁻¹ * b' * g ∈ B := mem_conjSubgroup.mp hb'
  have hzmem : g⁻¹ * (c * b') * g ∈ conjSubgroup (g⁻¹ * k * g) B := by
    refine mem_conj_iff.mpr ⟨g⁻¹ * b' * g, hb'B, ?_⟩
    rw [← hkb]; group
  have hnP : ¬ conjSubgroup (g⁻¹ * k * g) B ≤ P := by
    intro hle
    obtain ⟨t', ht', hne⟩ := hgood
    have ht : g⁻¹ * t' * g ∈ T := mem_conjSubgroup.mp ht'
    have hzt := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) _ (hle hzmem)
    have h2 : (c * b') * t' = t' * (c * b') := by
      have := congrArg (fun x => g * x * g⁻¹) hzt
      simpa [mul_assoc] using this
    have h3 : t' * b' = b' * t' := H.Tg_comm_Bg ht' hb'
    apply hne
    have h4 : (t' * c) * b' = (c * t') * b' := by
      calc (t' * c) * b' = t' * (c * b') := by group
        _ = (c * b') * t' := h2.symm
        _ = c * (b' * t') := by group
        _ = c * (t' * b') := by rw [h3]
        _ = (c * t') * b' := by group
    exact mul_right_cancel h4
  have ph := hphase1 _ h48' hnP
  have hc''W : g⁻¹ * c * g ∈ B ⊔ conjSubgroup (g⁻¹ * k * g) B := by
    have : g⁻¹ * c * g = (g⁻¹ * (c * b') * g) * (g⁻¹ * b' * g)⁻¹ := by group
    rw [this]
    exact (B ⊔ conjSubgroup (g⁻¹ * k * g) B).mul_mem (Subgroup.mem_sup_right hzmem)
      ((B ⊔ conjSubgroup (g⁻¹ * k * g) B).inv_mem (Subgroup.mem_sup_left hb'B))
  have hc''1 : g⁻¹ * c * g ≠ 1 := by
    intro h
    apply hc1
    have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [this, h]; group
  obtain ⟨U'', ⟨hU''cls, hc''U⟩, -⟩ := ph.part_W _ hc''W hc''1
  obtain ⟨h, hhX, hU''h⟩ := ph.trans_X U'' hU''cls
  obtain ⟨x₀, hx₀X, hx₀B⟩ := h1.trans_X (conjSubgroup g B) ⟨⟨g, rfl⟩, le_sup_right⟩
  have hTgN := H.Tg_le_normalizer_aL h48 h1 hTgW hcent
  have hXN := H.X_le_normalizer_aL h48 hP h1 hBgQ hTgW hcent
  have hgh : g * h * g⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    have hconj : conjSubgroup g (T ⊔ conjSubgroup (g⁻¹ * k * g) T) ≤
        Subgroup.normalizer (L : Set G) := by
      rw [conj_sup, ← conjSubgroup_mul, show g * (g⁻¹ * k * g) = k * g by group,
        conjSubgroup_mul]
      exact sup_le hTgN (conj_le_of_mem hkN hTgN)
    exact hconj (mem_conj_iff.mpr ⟨h, hhX, rfl⟩)
  refine ⟨(g * h * g⁻¹) * x₀, Subgroup.mul_mem _ hgh (hXN hx₀X), ?_, ?_⟩
  · have e : conjSubgroup ((g * h * g⁻¹) * x₀) B = conjSubgroup g U'' := by
      rw [conjSubgroup_mul, ← hx₀B, hU''h, ← conjSubgroup_mul, ← conjSubgroup_mul]
      congr 1; group
    rw [e]
    exact mem_conj_iff.mpr ⟨g⁻¹ * c * g, hc''U, by group⟩
  · have e : conjSubgroup ((g * h * g⁻¹) * x₀) B = conjSubgroup g U'' := by
      rw [conjSubgroup_mul, ← hx₀B, hU''h, ← conjSubgroup_mul, ← conjSubgroup_mul]
      congr 1; group
    rw [e]
    have hle : conjSubgroup g U'' ≤ conjSubgroup g (B ⊔ conjSubgroup (g⁻¹ * k * g) B) :=
      Subgroup.map_mono hU''cls.2
    refine hle.trans ?_
    rw [conj_sup, ← conjSubgroup_mul, show g * (g⁻¹ * k * g) = k * g by group,
      conjSubgroup_mul]
    exact sup_le le_sup_right (conj_le_of_mem_normalizer hkN le_sup_right)


theorem point_through_C (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hTgnc : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g')
    {c : G} (hc : c ∈ H.aC g) (hc1 : c ≠ 1) :
    ∃ r ∈ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G),
      c ∈ conjSubgroup r B ∧ conjSubgroup r B ≤ H.aC g ⊔ conjSubgroup g B := by
  have hQN := H.Q_le_normalizer_aL h48 hP hBgQ h1.part_W hcent
  by_cases hcB : c ∈ B
  · refine ⟨1, Subgroup.one_mem _, by rwa [conjSubgroup_one], ?_⟩
    rw [conjSubgroup_one]
    exact (H.B_le_aC h48).trans le_sup_left
  obtain ⟨y₁, hy₁, hgood⟩ := H.exists_good_conj h48 hP hTgnc hc hcB
  have hc' : y₁⁻¹ * c * y₁ ∈ H.aC g := by
    simpa using H.aC_conj_Q h48 (Q.inv_mem hy₁) hc
  have hc'1 : y₁⁻¹ * c * y₁ ≠ 1 := by
    intro h
    apply hc1
    have : c = y₁ * (y₁⁻¹ * c * y₁) * y₁⁻¹ := by group
    rw [this, h]; group
  obtain ⟨r', hr', hcr', hLr'⟩ := H.point_through_good h48 hP hBgQ h1 hTgW hcent hphase1 hc' hc'1
    hgood
  refine ⟨y₁ * r', Subgroup.mul_mem _ (hQN hy₁) hr', ?_, ?_⟩
  · rw [conjSubgroup_mul]
    exact mem_conj_iff.mpr ⟨y₁⁻¹ * c * y₁, hcr', by group⟩
  · rw [conjSubgroup_mul]
    exact conj_le_of_mem_normalizer (hQN hy₁) hLr'

theorem point_through_aff (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c) {l : G}
    (hl : l ∈ H.aC g ⊔ conjSubgroup g B) (hlC : l ∉ H.aC g) :
    ∃ r ∈ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G),
      l ∈ conjSubgroup r B ∧ conjSubgroup r B ≤ H.aC g ⊔ conjSubgroup g B := by
  have hQN := H.Q_le_normalizer_aL h48 hP hBgQ h1.part_W hcent
  have hXN := H.X_le_normalizer_aL h48 hP h1 hBgQ hTgW hcent
  obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun y hy c hc => (hcent c hc y hy).symm) hl
  have hy1 : y ≠ 1 := fun h => hlC (by rw [h, mul_one]; exact hc)
  obtain ⟨y₁, hy₁, hy₁e⟩ := H.exists_Q_conj_eq h48 hP hBgQ h1 hcent hy hy1 hc
  obtain ⟨x₀, hx₀X, hx₀B⟩ := h1.trans_X (conjSubgroup g B) ⟨⟨g, rfl⟩, le_sup_right⟩
  refine ⟨y₁ * x₀, Subgroup.mul_mem _ (hQN hy₁) (hXN hx₀X), ?_, ?_⟩
  · rw [conjSubgroup_mul, ← hx₀B, ← hy₁e]
    exact mem_conj_iff.mpr ⟨y, hy, rfl⟩
  · rw [conjSubgroup_mul, ← hx₀B]
    exact conj_le_of_mem_normalizer (hQN hy₁) le_sup_right

theorem point_through (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hTgnc : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g') {l : G}
    (hl : l ∈ H.aC g ⊔ conjSubgroup g B) (hl1 : l ≠ 1) :
    ∃ r ∈ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G),
      l ∈ conjSubgroup r B ∧ conjSubgroup r B ≤ H.aC g ⊔ conjSubgroup g B := by
  by_cases hlC : l ∈ H.aC g
  · exact H.point_through_C h48 hP hBgQ h1 hTgW hTgnc hcent hphase1 hlC hl1
  · exact H.point_through_aff h48 hP hBgQ h1 hTgW hcent hl hlC

theorem part_aL (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hTgnc : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g') :
    ∀ l ∈ H.aC g ⊔ conjSubgroup g B, l ≠ 1 →
      ∃! U, U ∈ classIn B (H.aC g ⊔ conjSubgroup g B) ∧ l ∈ U := by
  intro l hl hl1
  obtain ⟨r, -, hlr, hLr⟩ := H.point_through h48 hP hBgQ h1 hTgW hTgnc hcent hphase1 hl hl1
  refine ⟨conjSubgroup r B, ⟨⟨⟨r, rfl⟩, hLr⟩, hlr⟩, ?_⟩
  rintro U ⟨⟨⟨s, rfl⟩, -⟩, hlU⟩
  refine H.conj_B_eq_of_inf_ne_bot fun hbot => ?_
  have : l ∈ conjSubgroup s B ⊓ conjSubgroup r B := ⟨hlU, hlr⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hl1 this

theorem trans_aL (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hBgQ : conjSubgroup g B ⊓ Q = ⊥) (h1 : Phase1 B T g)
    (hTgW : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B)
    (hTgnc : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t)
    (hcent : ∀ c ∈ H.aC g, ∀ y ∈ conjSubgroup g B, c * y = y * c)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g') :
    ∀ U ∈ classIn B (H.aC g ⊔ conjSubgroup g B),
      ∃ r ∈ Subgroup.normalizer ((H.aC g ⊔ conjSubgroup g B : Subgroup G) : Set G),
        U = conjSubgroup r B := by
  rintro U ⟨⟨s, rfl⟩, hUL⟩
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (H.conj_B_ne_bot s)
  have hl1' : l ≠ 1 := fun h => hl1 (Subtype.ext h)
  obtain ⟨r, hr, hlr, -⟩ := H.point_through h48 hP hBgQ h1 hTgW hTgnc hcent hphase1 (hUL hl) hl1'
  refine ⟨r, hr, H.conj_B_eq_of_inf_ne_bot fun hbot => ?_⟩
  have : l ∈ conjSubgroup s B ⊓ conjSubgroup r B := ⟨hl, hlr⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hl1' this


end Hyp4

end CFSG.RankThree.GF2n.Tim78
