module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSpTwo

public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_sup_of_coprime {p : ℕ} (hp : p.Prime) {Y L : Subgroup G}
    (hLY : L ≤ normalizer (Y : Set G)) {y : G} (hy : y ∈ Y ⊔ L) (hyp : y ^ p = 1) :
    ∃ B : Subgroup G, ((B = L ∧ p ∣ Nat.card L) ∨ B = ⊥) ∧ y ∈ Y ⊔ B := by
  by_cases h : p ∣ Nat.card L
  · exact ⟨L, Or.inl ⟨rfl, h⟩, hy⟩
  · refine ⟨⊥, Or.inr rfl, ?_⟩
    rw [sup_bot_eq]
    exact ggRCST_mem_of_mem_sup_coprime hp h hLY (by rwa [sup_comm] at hy) hyp

omit [Finite G] in
theorem le_normalizer_sup_of_centralizer {L A B : Subgroup G}
    (hA : L ≤ normalizer (A : Set G)) (hB : L ≤ centralizer (B : Set G)) :
    L ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := fun _ hg =>
  ggRCST_mem_normalizer_sup (hA hg) (centralizer_le_normalizer _ (hB hg))

omit [Finite G] in
theorem le_centralizer_of_eq_or_bot {L B C : Subgroup G} (hB : B = L ∨ B = ⊥)
    (hC : C ≤ centralizer (L : Set G)) : C ≤ centralizer (B : Set G) := by
  rcases hB with rfl | rfl
  · exact hC
  · intro g _
    rw [mem_centralizer_iff]
    intro x hx
    rw [(mem_bot.mp hx), one_mul, mul_one]

end Coprime

section Layer

variable {G : Type} [Group G] [Finite G]

theorem piece_of_summand {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X V Q L : Subgroup G}
    (hXV : X ≤ V) (hVX : V ≤ normalizer (X : Set G)) (hVQ : V ≤ normalizer (Q : Set G))
    (hQ2 : IsPGroup 2 Q) (hQX : Q ≤ X) (hLX : L ≤ X) (hLQ : L ≤ normalizer (Q : Set G))
    (hXN : X ≤ normalizer ((Q ⊔ L : Subgroup G) : Set G)) (hLq : CFSG.IsQuasisimple L)
    (hQL : Q ≤ ⁅Q ⊔ L, Q ⊔ L⁆) (hpL : p ∣ Nat.card L) : GGRCSLayerPiece p V (Q ⊔ L) := by
  have hXsn :=
    ggIsSubnormal_of_normal hXV ((Subgroup.normal_subgroupOf_iff_le_normalizer hXV).mpr hVX)
  have hYX : Q ⊔ L ≤ X := sup_le hQX hLX
  have hperfL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hLq.1
  refine Or.inl ⟨Q, hYX.trans hXV, ?_, ?_, ?_, le_sup_left, hQ2, hVQ, ?_⟩
  · exact ggIsSubnormal_trans
      (ggIsSubnormal_of_normal hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXN))
      hXsn
  · refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQL ?_)
    calc L = ⁅L, L⁆ := hperfL.symm
      _ ≤ ⁅Q ⊔ L, Q ⊔ L⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  · exact dvd_trans hpL (Subgroup.card_dvd_of_le le_sup_right)
  · intro _
    exact ggRCST_isQuasisimple_quot hp hp2 hLQ le_sup_right le_rfl hQ2 inf_le_right hLq hpL

@[expose] def GGRCSOmQuasiSummand (p : ℕ) (Q L : Subgroup G) : Prop :=
  p ∣ Nat.card L → CFSG.IsQuasisimple L ∧ Q ≤ ⁅Q ⊔ L, Q ⊔ L⁆

omit [Finite G] in
theorem ggRCSOmQuasiSummand_bot {p : ℕ} (hp : p.Prime) (Q : Subgroup G) :
    GGRCSOmQuasiSummand p Q ⊥ := by
  intro h
  rw [Subgroup.card_bot] at h
  exact absurd (Nat.le_of_dvd one_pos h) (by have := hp.two_le; omega)

theorem ggRCSLayer_of_three_summands {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ M : Subgroup G}
    (hG₀M : G₀ ≤ M) (hM : M ≤ normalizer (G₀ : Set G)) {r : G} {Q L₁ L₂ L₃ : Subgroup G}
    (hQ2 : IsPGroup 2 Q) (hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX G₀ r) = Q)
    (hX : ggRCSX G₀ r = Q ⊔ L₁ ⊔ L₂ ⊔ L₃) (h1Q : L₁ ≤ normalizer (Q : Set G))
    (h2Q : L₂ ≤ normalizer (Q : Set G)) (h3Q : L₃ ≤ normalizer (Q : Set G))
    (h12 : L₁ ≤ centralizer (L₂ : Set G)) (h13 : L₁ ≤ centralizer (L₃ : Set G))
    (h23 : L₂ ≤ centralizer (L₃ : Set G)) (hL₁ : GGRCSOmQuasiSummand p Q L₁)
    (hL₂ : GGRCSOmQuasiSummand p Q L₂) (hL₃ : GGRCSOmQuasiSummand p Q L₃) :
    GGRCSLayer p G₀ M r := by
  set X := ggRCSX G₀ r with hXdef
  set V := M ⊓ centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  have hVQ : V ≤ normalizer (Q : Set G) := by
    rw [← hO2]
    exact hVX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have h21 : L₂ ≤ centralizer (L₁ : Set G) := Subgroup.le_centralizer_iff.mp h12
  have h31 : L₃ ≤ centralizer (L₁ : Set G) := Subgroup.le_centralizer_iff.mp h13
  have h32 : L₃ ≤ centralizer (L₂ : Set G) := Subgroup.le_centralizer_iff.mp h23
  have hQX : Q ≤ X := by rw [hX]; exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hL₁X : L₁ ≤ X := by rw [hX]; exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hL₂X : L₂ ≤ X := by rw [hX]; exact le_sup_right.trans le_sup_left
  have hL₃X : L₃ ≤ X := by rw [hX]; exact le_sup_right
  have hQN : ∀ L : Subgroup G, Q ≤ normalizer ((Q ⊔ L : Subgroup G) : Set G) := fun L =>
    le_sup_left.trans le_normalizer
  have hLN : ∀ L : Subgroup G, L ≤ normalizer ((Q ⊔ L : Subgroup G) : Set G) := fun L =>
    le_sup_right.trans le_normalizer
  have hX₁ : X ≤ normalizer ((Q ⊔ L₁ : Subgroup G) : Set G) := by
    rw [hX]
    exact sup_le (sup_le (sup_le (hQN _) (hLN _)) (le_normalizer_sup_of_centralizer h2Q h21))
      (le_normalizer_sup_of_centralizer h3Q h31)
  have hX₂ : X ≤ normalizer ((Q ⊔ L₂ : Subgroup G) : Set G) := by
    rw [hX]
    exact sup_le (sup_le (sup_le (hQN _) (le_normalizer_sup_of_centralizer h1Q h12)) (hLN _))
      (le_normalizer_sup_of_centralizer h3Q h32)
  have hX₃ : X ≤ normalizer ((Q ⊔ L₃ : Subgroup G) : Set G) := by
    rw [hX]
    exact sup_le (sup_le (sup_le (hQN _) (le_normalizer_sup_of_centralizer h1Q h13))
      (le_normalizer_sup_of_centralizer h2Q h23)) (hLN _)
  set 𝒮 : Set (Subgroup G) := {Y | (Y = Q ⊔ L₁ ∧ p ∣ Nat.card L₁) ∨
    (Y = Q ⊔ L₂ ∧ p ∣ Nat.card L₂) ∨ (Y = Q ⊔ L₃ ∧ p ∣ Nat.card L₃)} with h𝒮
  refine ⟨𝒮, ?_, fun y hy hyp => ?_⟩
  · rintro Y (⟨rfl, hpL⟩ | ⟨rfl, hpL⟩ | ⟨rfl, hpL⟩)
    · exact piece_of_summand hp hp2 hXV hVX hVQ hQ2 hQX hL₁X h1Q hX₁ (hL₁ hpL).1 (hL₁ hpL).2 hpL
    · exact piece_of_summand hp hp2 hXV hVX hVQ hQ2 hQX hL₂X h2Q hX₂ (hL₂ hpL).1 (hL₂ hpL).2 hpL
    · exact piece_of_summand hp hp2 hXV hVX hVQ hQ2 hQX hL₃X h3Q hX₃ (hL₃ hpL).1 (hL₃ hpL).2 hpL
  have hy₀ : y ∈ (Q ⊔ L₂ ⊔ L₃) ⊔ L₁ := by
    have e : X = (Q ⊔ L₂ ⊔ L₃) ⊔ L₁ := by rw [hX]; ac_rfl
    rw [← e]; exact hy
  obtain ⟨B₁, hB₁, hy₁⟩ := exists_mem_sup_of_coprime hp
    (le_normalizer_sup_of_centralizer (le_normalizer_sup_of_centralizer h1Q h12) h13) hy₀ hyp
  have hB₁c : ∀ C : Subgroup G, C ≤ centralizer (L₁ : Set G) → C ≤ centralizer (B₁ : Set G) :=
    fun C hC => le_centralizer_of_eq_or_bot (hB₁.imp And.left id) hC
  have hy₁' : y ∈ (Q ⊔ B₁ ⊔ L₃) ⊔ L₂ := by
    have e : (Q ⊔ L₂ ⊔ L₃) ⊔ B₁ = (Q ⊔ B₁ ⊔ L₃) ⊔ L₂ := by ac_rfl
    rw [← e]; exact hy₁
  obtain ⟨B₂, hB₂, hy₂⟩ := exists_mem_sup_of_coprime hp
    (le_normalizer_sup_of_centralizer (le_normalizer_sup_of_centralizer h2Q (hB₁c _ h21)) h23)
    hy₁' hyp
  have hB₂c : ∀ C : Subgroup G, C ≤ centralizer (L₂ : Set G) → C ≤ centralizer (B₂ : Set G) :=
    fun C hC => le_centralizer_of_eq_or_bot (hB₂.imp And.left id) hC
  have hy₂' : y ∈ (Q ⊔ B₁ ⊔ B₂) ⊔ L₃ := by
    have e : (Q ⊔ B₁ ⊔ L₃) ⊔ B₂ = (Q ⊔ B₁ ⊔ B₂) ⊔ L₃ := by ac_rfl
    rw [← e]; exact hy₂
  obtain ⟨B₃, hB₃, hy₃⟩ := exists_mem_sup_of_coprime hp
    (le_normalizer_sup_of_centralizer (le_normalizer_sup_of_centralizer h3Q (hB₁c _ h31))
      (hB₂c _ h32)) hy₂' hyp
  have hmem : ∀ (L B : Subgroup G), Q ⊔ L ∈ 𝒮 ∨ ¬ p ∣ Nat.card L →
      ((B = L ∧ p ∣ Nat.card L) ∨ B = ⊥) → B ≤ sSup 𝒮 := by
    rintro L B hL (⟨rfl, hpL⟩ | rfl)
    · rcases hL with hL | hL
      · exact le_sup_right.trans (le_sSup hL)
      · exact absurd hpL hL
    · exact bot_le
  have h1S : Q ⊔ L₁ ∈ 𝒮 ∨ ¬ p ∣ Nat.card L₁ := by
    by_cases h : p ∣ Nat.card L₁
    · exact Or.inl (Or.inl ⟨rfl, h⟩)
    · exact Or.inr h
  have h2S : Q ⊔ L₂ ∈ 𝒮 ∨ ¬ p ∣ Nat.card L₂ := by
    by_cases h : p ∣ Nat.card L₂
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, h⟩))
    · exact Or.inr h
  have h3S : Q ⊔ L₃ ∈ 𝒮 ∨ ¬ p ∣ Nat.card L₃ := by
    by_cases h : p ∣ Nat.card L₃
    · exact Or.inl (Or.inr (Or.inr ⟨rfl, h⟩))
    · exact Or.inr h
  have hBS : B₁ ⊔ B₂ ⊔ B₃ ≤ sSup 𝒮 :=
    sup_le (sup_le (hmem _ _ h1S hB₁) (hmem _ _ h2S hB₂)) (hmem _ _ h3S hB₃)
  by_cases hne : 𝒮.Nonempty
  · obtain ⟨Y, hY⟩ := hne
    have hQS : Q ≤ sSup 𝒮 := by
      have hYS : Y ≤ sSup 𝒮 := le_sSup hY
      rcases hY with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact le_sup_left.trans hYS
    have e : Q ⊔ B₁ ⊔ B₂ ⊔ B₃ = Q ⊔ (B₁ ⊔ B₂ ⊔ B₃) := by ac_rfl
    rw [e] at hy₃
    exact sup_le hQS hBS hy₃
  ·
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hbot : ∀ (L B : Subgroup G), Q ⊔ L ∈ 𝒮 ∨ ¬ p ∣ Nat.card L →
        ((B = L ∧ p ∣ Nat.card L) ∨ B = ⊥) → B = ⊥ := by
      rintro L B hL (⟨rfl, hpL⟩ | rfl)
      · rcases hL with hL | hL
        · rw [hne] at hL; exact absurd hL (Set.notMem_empty _)
        · exact absurd hpL hL
      · rfl
    rw [hbot _ _ h1S hB₁, hbot _ _ h2S hB₂, hbot _ _ h3S hB₃, sup_bot_eq, sup_bot_eq,
      sup_bot_eq] at hy₃
    rw [ggRCS_eq_one_of_mem_two hp hp2 hQ2 hy₃ hyp]
    exact one_mem _

end Layer

section PCore

variable {G : Type} [Group G]

@[expose] def GGRCSOmSummand (L : Subgroup G) : Prop :=
  (∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1) ∧
    ∀ N : Subgroup G, N ≤ L → IsPGroup 2 N → L ≤ normalizer (N : Set G) → N = ⊥

theorem ggRCSOmSummand_bot : GGRCSOmSummand (⊥ : Subgroup G) :=
  ⟨fun _ hx _ => mem_bot.mp hx, fun _ hN _ _ => le_bot_iff.mp hN⟩

theorem eq_bot_of_subgroupOf_eq_bot {N L : Subgroup G} (hNL : N ≤ L)
    (h : N.subgroupOf L = ⊥) : N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hNL hx⟩ : ↥L) ∈ N.subgroupOf L := mem_subgroupOf.mpr hx
  rw [h, mem_bot] at hx'
  exact mem_bot.mpr (congrArg Subtype.val hx')

theorem eq_one_of_center_eq_bot {L : Subgroup G} (hZ : center L = ⊥) {x : G} (hx : x ∈ L)
    (h : ∀ y ∈ L, x * y = y * x) : x = 1 := by
  have hc : (⟨x, hx⟩ : ↥L) ∈ center L :=
    mem_center_iff.mpr fun g => Subtype.ext (h g g.2).symm
  rw [hZ, mem_bot] at hc
  exact congrArg Subtype.val hc

theorem ggRCSOmSummand_of_isQuasisimple [Finite G] {L : Subgroup G} (hq : CFSG.IsQuasisimple L)
    (hZ : center L = ⊥) : GGRCSOmSummand L := by
  refine ⟨fun x hx h => eq_one_of_center_eq_bot hZ hx h, fun N hNL hN2 hLN => ?_⟩
  have hNn : (N.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with h | h
  · exfalso
    have h2 : IsPGroup 2 ↥L := fun x => by
      have hx : x ∈ N.subgroupOf L := h ▸ Subgroup.mem_top x
      obtain ⟨k, hk⟩ := hN2 ⟨x, hx⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect ↥L := hq.1
    exact Group.IsPerfect.not_isNilpotent _ h2.isNilpotent
  · rw [hZ] at h
    exact eq_bot_of_subgroupOf_eq_bot hNL (le_bot_iff.mp h)

theorem perm_three_center : ∀ x : Equiv.Perm (Fin 3), (∀ y, x * y = y * x) → x = 1 := by
  decide +kernel

theorem ggRCSOmSummand_of_perm {L : Subgroup G} (e : ↥L ≃* Equiv.Perm (Fin 3)) :
    GGRCSOmSummand L := by
  refine ⟨fun x hx h => ?_, fun N hNL hN2 hLN => ?_⟩
  · have h1 := perm_three_center (e ⟨x, hx⟩) fun y => by
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (h y' y'.2))
    have h2 : (⟨x, hx⟩ : ↥L) = 1 := by rw [← e.map_eq_one_iff]; exact h1
    exact congrArg Subtype.val h2
  · have hNn : (N.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
    have h2 : IsPGroup 2 (N.subgroupOf L) := hN2.comap_of_injective L.subtype L.subtype_injective
    have hbot := ggRCSS_perm_three_normal_two ((N.subgroupOf L).map e.toMonoidHom)
      (hNn.map _ e.surjective) (h2.map _)
    refine eq_bot_of_subgroupOf_eq_bot hNL ?_
    rwa [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hbot

theorem pCoreOf_eq_of_three_summands {X Q L₁ L₂ L₃ : Subgroup G}
    (hX : X = Q ⊔ (L₁ ⊔ L₂ ⊔ L₃)) (hQ2 : IsPGroup 2 Q) (h1Q : L₁ ≤ normalizer (Q : Set G))
    (h2Q : L₂ ≤ normalizer (Q : Set G)) (h3Q : L₃ ≤ normalizer (Q : Set G))
    (h12 : L₁ ≤ centralizer (L₂ : Set G)) (h13 : L₁ ≤ centralizer (L₃ : Set G))
    (h23 : L₂ ≤ centralizer (L₃ : Set G)) (hS₁ : GGRCSOmSummand L₁) (hS₂ : GGRCSOmSummand L₂)
    (hS₃ : GGRCSOmSummand L₃) : CFSG.Assembly.pCoreOf 2 X = Q := by
  refine ggRCST_pCoreOf_eq hX hQ2 (sup_le (sup_le h1Q h2Q) h3Q) ?_
  intro N hNM hN2 hMN
  have h21 : L₂ ≤ centralizer (L₁ : Set G) := Subgroup.le_centralizer_iff.mp h12
  have h31 : L₃ ≤ centralizer (L₁ : Set G) := Subgroup.le_centralizer_iff.mp h13
  have h32 : L₃ ≤ centralizer (L₂ : Set G) := Subgroup.le_centralizer_iff.mp h23
  have hcn : ∀ {A B : Subgroup G}, A ≤ centralizer (B : Set G) → A ≤ normalizer (B : Set G) :=
    fun h => h.trans (centralizer_le_normalizer _)
  have hM1 : L₁ ⊔ L₂ ⊔ L₃ ≤ normalizer (L₁ : Set G) :=
    sup_le (sup_le le_normalizer (hcn h21)) (hcn h31)
  have hM2 : L₁ ⊔ L₂ ⊔ L₃ ≤ normalizer (L₂ : Set G) :=
    sup_le (sup_le (hcn h12) le_normalizer) (hcn h32)
  have hM3 : L₁ ⊔ L₂ ⊔ L₃ ≤ normalizer (L₃ : Set G) :=
    sup_le (sup_le (hcn h13) (hcn h23)) le_normalizer
  have hL1 : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hL2 : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hL3 : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have key : ∀ L : Subgroup G, GGRCSOmSummand L → L ≤ L₁ ⊔ L₂ ⊔ L₃ →
      L₁ ⊔ L₂ ⊔ L₃ ≤ normalizer (L : Set G) → ∀ n ∈ N, ∀ l ∈ L, n * l = l * n := by
    intro L hS hLM hML n hn l hl
    have hNL : N ⊓ L = ⊥ := hS.2 (N ⊓ L) inf_le_right (hN2.to_le (inf_le_left : N ⊓ L ≤ N))
      (le_trans (le_inf (hLM.trans hMN) le_normalizer) Subgroup.inf_normalizer_le_normalizer_inf)
    have hc : n * l * n⁻¹ * l⁻¹ ∈ N ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : l * n⁻¹ * l⁻¹ ∈ N :=
          (mem_normalizer_iff.mp (hMN (hLM hl)) n⁻¹).mp (inv_mem hn)
        have h2 := mul_mem hn h1
        rwa [show n * (l * n⁻¹ * l⁻¹) = n * l * n⁻¹ * l⁻¹ by group] at h2
      · exact mul_mem ((mem_normalizer_iff.mp (hML (hNM hn)) l).mp hl) (inv_mem hl)
    rw [hNL, mem_bot] at hc
    calc n * l = (n * l * n⁻¹ * l⁻¹) * (l * n) := by group
      _ = l * n := by rw [hc, one_mul]
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  have hn1 := key L₁ hS₁ hL1 hM1 n hn
  have hn2 := key L₂ hS₂ hL2 hM2 n hn
  have hn3 := key L₃ hS₃ hL3 hM3 n hn
  obtain ⟨a, ha, l₃, hl₃, hal⟩ := ggRCST_exists_of_mem_sup (A := L₁ ⊔ L₂) (Y := L₃)
    (sup_le (hcn h13) (hcn h23)) (hNM hn)
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := ggRCST_exists_of_mem_sup (A := L₁) (Y := L₂) (hcn h12) ha
  have c1 : ∀ x ∈ L₁, Commute l₂ x ∧ Commute l₃ x := fun x hx =>
    ⟨((mem_centralizer_iff.mp (h21 hl₂)) x hx).symm, ((mem_centralizer_iff.mp (h31 hl₃)) x hx).symm⟩
  have c2 : ∀ x ∈ L₂, Commute l₁ x ∧ Commute l₃ x := fun x hx =>
    ⟨((mem_centralizer_iff.mp (h12 hl₁)) x hx).symm, ((mem_centralizer_iff.mp (h32 hl₃)) x hx).symm⟩
  have c3 : ∀ x ∈ L₃, Commute l₁ x ∧ Commute l₂ x := fun x hx =>
    ⟨((mem_centralizer_iff.mp (h13 hl₁)) x hx).symm, ((mem_centralizer_iff.mp (h23 hl₂)) x hx).symm⟩
  have hl₁1 : l₁ = 1 := by
    refine hS₁.1 l₁ hl₁ fun x hx => ?_
    have hN : Commute (l₁ * l₂ * l₃) x := by rw [← hal]; exact hn1 x hx
    have e : l₁ = l₁ * l₂ * l₃ * (l₂ * l₃)⁻¹ := by group
    rw [e]
    exact (hN.mul_left ((c1 x hx).1.mul_left (c1 x hx).2).inv_left).eq
  have hl₂1 : l₂ = 1 := by
    refine hS₂.1 l₂ hl₂ fun x hx => ?_
    have hN : Commute (l₁ * l₂ * l₃) x := by rw [← hal]; exact hn2 x hx
    have e : l₂ = l₁⁻¹ * (l₁ * l₂ * l₃) * l₃⁻¹ := by group
    rw [e]
    exact (((c2 x hx).1.inv_left.mul_left hN).mul_left (c2 x hx).2.inv_left).eq
  have hl₃1 : l₃ = 1 := by
    refine hS₃.1 l₃ hl₃ fun x hx => ?_
    have hN : Commute (l₁ * l₂ * l₃) x := by rw [← hal]; exact hn3 x hx
    have e : l₃ = (l₁ * l₂)⁻¹ * (l₁ * l₂ * l₃) := by group
    rw [e]
    exact (((c3 x hx).1.mul_left (c3 x hx).2).inv_left.mul_left hN).eq
  rw [hal, hl₁1, hl₂1, hl₃1, mul_one, mul_one]

end PCore

section SThree

variable {G : Type} [Group G]

open CFSG.Quasithin (perfectCore derivedSeriesOf)

theorem perfectCore_sup_le_of_solvable [Finite G] {Q' S : Subgroup G}
    (hSQ : S ≤ normalizer (Q' : Set G)) (hS : Group.IsSolvable ↥S) :
    perfectCore (Q' ⊔ S) ≤ Q' := by
  have key : ∀ k, derivedSeriesOf (Q' ⊔ S) k ≤ Q' ⊔ (derivedSeries ↥S k).map S.subtype := by
    intro k
    induction k with
    | zero =>
      rw [CFSG.Quasithin.derivedSeriesOf_zero, derivedSeries_zero, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    | succ k ih =>
      rw [CFSG.Quasithin.derivedSeriesOf_succ]
      have hDk : (derivedSeries ↥S k).map S.subtype ≤ normalizer (Q' : Set G) :=
        (map_subtype_le _).trans hSQ
      refine (Subgroup.commutator_mono ih ih).trans
        ((CFSG.SeitzReduction.SymplecticPilot.commutator_sup_le_sup_commutator_of_le_normalizer
          hDk).trans ?_)
      rw [derivedSeries_succ, Subgroup.map_commutator]
  obtain ⟨k, hk⟩ := hS.solvable
  refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ k).trans ((key k).trans ?_)
  rw [hk, Subgroup.map_bot, sup_bot_eq]

theorem perfectCore_eq_of_solvable [Finite G] {X Q S T : Subgroup G} (hX : X = Q ⊔ (S ⊔ T))
    (hSN : S ≤ normalizer ((Q ⊔ T : Subgroup G) : Set G)) (hS : Group.IsSolvable ↥S)
    (hperf : ⁅Q ⊔ T, Q ⊔ T⁆ = Q ⊔ T) : perfectCore X = Q ⊔ T := by
  have hX' : X = (Q ⊔ T) ⊔ S := by rw [hX]; ac_rfl
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (by rw [hX']; exact le_sup_left)
    hperf)
  rw [hX']
  exact perfectCore_sup_le_of_solvable hSN hS

theorem ggRCSLayer_three_of_sThree [Finite G] {G₀ M : Subgroup G} (hG₀M : G₀ ≤ M)
    (hM : M ≤ normalizer (G₀ : Set G)) {r : G} {Q S T : Subgroup G}
    (hX : ggRCSX G₀ r = Q ⊔ (S ⊔ T)) (hQ2 : IsPGroup 2 Q)
    (hSQ : S ≤ normalizer (Q : Set G)) (hTQ : T ≤ normalizer (Q : Set G))
    (hST : S ≤ centralizer (T : Set G)) (hdQL : Disjoint Q (S ⊔ T)) (hdST : Disjoint S T)
    (hD : perfectCore (ggRCSX G₀ r) = Q ⊔ T) (eS : ↥S ≃* Equiv.Perm (Fin 3))
    (hTq : CFSG.IsQuasisimple T) (hTZ : center T = ⊥) (h3T : 3 ∣ Nat.card T) :
    GGRCSLayer 3 G₀ M r := by
  set X := ggRCSX G₀ r with hXdef
  set V := M ⊓ centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  set D := perfectCore X with hDdef
  have hVD : V ≤ normalizer (D : Set G) :=
    hVX.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
  have hDX : D ≤ X := CFSG.Quasithin.perfectCore_le _
  have hTS : T ≤ centralizer (S : Set G) := Subgroup.le_centralizer_iff.mp hST
  have hLQ : S ⊔ T ≤ normalizer (Q : Set G) := sup_le hSQ hTQ
  have hTcen : ∀ t ∈ T, (∀ t' ∈ T, t * t' = t' * t) → t = 1 := fun t ht h =>
    eq_one_of_center_eq_bot hTZ ht h
  have hQD : CFSG.Assembly.pCoreOf 2 D = Q := by
    rw [hD]
    refine ggRCST_pCoreOf_eq rfl hQ2 hTQ ?_
    intro N hNT hN2 hTN
    exact (ggRCSOmSummand_of_isQuasisimple hTq hTZ).2 N hNT hN2 hTN
  have hVQ : V ≤ normalizer (Q : Set G) := by
    rw [← hQD]
    exact hVD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D)
  have hQX : Q ≤ X := by rw [hX]; exact le_sup_left
  have hSX : S ≤ X := by rw [hX]; exact le_sup_left.trans le_sup_right
  have hTX : T ≤ X := by rw [hX]; exact le_sup_right.trans le_sup_right
  have hXQ : X ≤ normalizer (Q : Set G) := by rw [hX]; exact sup_le le_normalizer hLQ
  have hQn : (Q.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQX]
    exact hXQ
  have hdQT : Disjoint Q T := hdQL.mono_right le_sup_right
  have hSTN : S ≤ normalizer (T : Set G) := fun g hg => centralizer_le_normalizer _ (hST hg)
  have hdec : ∀ x ∈ X, ∃ s ∈ S, ∃ t ∈ T, ∃ q ∈ Q, x = s * t * q := by
    intro x hx
    rw [hX, sup_comm] at hx
    obtain ⟨l, hl, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hLQ hx
    obtain ⟨s', hs', t, ht, rfl⟩ := ggRCST_exists_of_mem_sup hSTN hl
    exact ⟨s', hs', t, ht, q, hq, rfl⟩
  set φ := QuotientGroup.mk' (Q.subgroupOf X) with hφ
  have hφq : ∀ q (hq : q ∈ Q), φ ⟨q, hQX hq⟩ = 1 := fun q hq => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq
  have hφST : ∀ s (hs : s ∈ S) t (ht : t ∈ T),
      φ ⟨s, hSX hs⟩ * φ ⟨t, hTX ht⟩ = φ ⟨t, hTX ht⟩ * φ ⟨s, hSX hs⟩ := by
    intro s hs t ht
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (show s * t = t * s from (mem_centralizer_iff.mp (hTS ht)) s hs)
  have hR₀ : ∀ x, x ∈ Q ⊔ S ↔ x ∈ X ∧ ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ Q := by
    intro x
    constructor
    · intro hx
      have hxX : x ∈ X := sup_le hQX hSX hx
      refine ⟨hxX, fun d hd => ?_⟩
      have hdX := hDX hd
      rw [RCSTSp2.comm_mem_iff hxX hdX]
      rw [sup_comm] at hx
      obtain ⟨s, hs, q, hq, rfl⟩ := ggRCST_exists_of_mem_sup hSQ hx
      rw [hD] at hd
      have hd' : d ∈ T ⊔ Q := by rwa [sup_comm] at hd
      obtain ⟨t, ht, q', hq', rfl⟩ := ggRCST_exists_of_mem_sup hTQ hd'
      have e1 : (⟨s * q, hxX⟩ : ↥X) = ⟨s, hSX hs⟩ * ⟨q, hQX hq⟩ := rfl
      have e2 : (⟨t * q', hdX⟩ : ↥X) = ⟨t, hTX ht⟩ * ⟨q', hQX hq'⟩ := rfl
      rw [e1, e2, map_mul, map_mul, hφq q hq, hφq q' hq', mul_one, mul_one]
      exact hφST s hs t ht
    · rintro ⟨hxX, hxD⟩
      obtain ⟨s, hs, t, ht, q, hq, rfl⟩ := hdec _ hxX
      have ht1 : t = 1 := by
        refine hTcen t ht fun t' ht' => ?_
        have h1 := hxD t' (by rw [hD]; exact Subgroup.mem_sup_right ht')
        rw [RCSTSp2.comm_mem_iff hxX (hTX ht')] at h1
        have e1 : (⟨s * t * q, hxX⟩ : ↥X) = ⟨s, hSX hs⟩ * ⟨t, hTX ht⟩ * ⟨q, hQX hq⟩ := rfl
        rw [e1, map_mul, map_mul, hφq q hq, mul_one] at h1
        have hc := hφST s hs t' ht'
        have h2 : φ ⟨t, hTX ht⟩ * φ ⟨t', hTX ht'⟩ = φ ⟨t', hTX ht'⟩ * φ ⟨t, hTX ht⟩ := by
          apply mul_left_cancel (a := φ ⟨s, hSX hs⟩)
          calc φ ⟨s, hSX hs⟩ * (φ ⟨t, hTX ht⟩ * φ ⟨t', hTX ht'⟩)
              = φ ⟨s, hSX hs⟩ * φ ⟨t, hTX ht⟩ * φ ⟨t', hTX ht'⟩ := (mul_assoc _ _ _).symm
            _ = φ ⟨t', hTX ht'⟩ * (φ ⟨s, hSX hs⟩ * φ ⟨t, hTX ht⟩) := h1
            _ = (φ ⟨t', hTX ht'⟩ * φ ⟨s, hSX hs⟩) * φ ⟨t, hTX ht⟩ := (mul_assoc _ _ _).symm
            _ = (φ ⟨s, hSX hs⟩ * φ ⟨t', hTX ht'⟩) * φ ⟨t, hTX ht⟩ := by rw [hc]
            _ = φ ⟨s, hSX hs⟩ * (φ ⟨t', hTX ht'⟩ * φ ⟨t, hTX ht⟩) := mul_assoc _ _ _
        have h3 := (RCSTSp2.comm_mem_iff (Q := Q) (hTX ht) (hTX ht')).mpr h2
        have h4 : t * t' * t⁻¹ * t'⁻¹ ∈ T :=
          T.mul_mem (T.mul_mem (T.mul_mem ht ht') (T.inv_mem ht)) (T.inv_mem ht')
        have h5 := (Subgroup.disjoint_def.mp hdQT) h3 h4
        calc t * t' = (t * t' * t⁻¹ * t'⁻¹) * (t' * t) := by group
          _ = t' * t := by rw [h5, one_mul]
      rw [ht1, mul_one]
      exact mul_mem (mem_sup_right hs) (mem_sup_left hq)
  have hVR : V ≤ normalizer ((Q ⊔ S : Subgroup G) : Set G) := by
    have key : ∀ v ∈ V, ∀ x ∈ Q ⊔ S, v * x * v⁻¹ ∈ Q ⊔ S := by
      intro v hv x hx
      rw [hR₀] at hx ⊢
      refine ⟨(mem_normalizer_iff.mp (hVX hv) x).mp hx.1, fun d hd => ?_⟩
      have hd' : v⁻¹ * d * v⁻¹⁻¹ ∈ D := (mem_normalizer_iff.mp (hVD (V.inv_mem hv)) d).mp hd
      rw [inv_inv] at hd'
      have h2 := (mem_normalizer_iff.mp (hVQ hv) _).mp (hx.2 _ hd')
      convert h2 using 1
      group
    intro v hv
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key v hv x, fun h => ?_⟩
    have := key v⁻¹ (V.inv_mem hv) _ h
    rwa [inv_inv, show v⁻¹ * (v * x * v⁻¹) * v = x by group] at this
  have hR₀V : Q ⊔ S ≤ V := (sup_le hQX hSX).trans hXV
  have hQR : Q ≤ Q ⊔ S := le_sup_left
  have hQnR : (Q.subgroupOf (Q ⊔ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQR]
    exact sup_le le_normalizer hSQ
  obtain ⟨eQS⟩ := RCSTSp2.quot_equiv_of_disjoint hSQ (hdQL.mono_right le_sup_left)
  obtain ⟨Sp, hSp, hSpcov⟩ := RCSTSp2.exists_sThree_piece hQR hR₀V hVR hQ2 hVQ (eQS.trans eS)
  have hDpiece : GGRCSLayerPiece 3 V D := by
    refine Or.inl ⟨Q, hDX.trans hXV, ggIsSubnormal_of_normal (hDX.trans hXV)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hDX.trans hXV)).mpr hVD),
      CFSG.Quasithin.perfectCore_perfect _, ?_, by rw [hD]; exact le_sup_left, hQ2, hVQ, ?_⟩
    · exact dvd_trans h3T (Subgroup.card_dvd_of_le (by rw [hD]; exact le_sup_right))
    · intro _
      exact ggRCST_isQuasisimple_quot Nat.prime_three (by norm_num) hTQ
        (by rw [hD]; exact le_sup_right) hD.le hQ2 inf_le_right hTq h3T
  refine ⟨{D, Sp}, ?_, fun y hy hy3 => ?_⟩
  · rintro P (rfl | rfl)
    · exact hDpiece
    · exact Or.inr ⟨rfl, Q ⊔ S, Q, hSp⟩
  · obtain ⟨s, hs, t, ht, q, hq, rfl⟩ := hdec y hy
    have hs3 : s ^ 3 = 1 := by
      have h1 : φ ⟨s * t * q, hy⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨s * t * q, hy⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
        rw [this, map_one]
      have e1 : (⟨s * t * q, hy⟩ : ↥X) = ⟨s, hSX hs⟩ * ⟨t, hTX ht⟩ * ⟨q, hQX hq⟩ := rfl
      rw [e1, map_mul, map_mul, hφq q hq, mul_one, (Commute.mul_pow (hφST s hs t ht) 3),
        ← map_pow, ← map_pow, ← map_mul] at h1
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      have h2 : s ^ 3 * t ^ 3 ∈ Q := by simpa using h1
      have h3 : s ^ 3 * t ^ 3 ∈ S ⊔ T :=
        mul_mem (mem_sup_left (pow_mem hs 3)) (mem_sup_right (pow_mem ht 3))
      have h4 := (Subgroup.disjoint_def.mp hdQL) h2 h3
      have h5 : s ^ 3 = (t ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h4
      have h6 : s ^ 3 ∈ T := h5 ▸ T.inv_mem (pow_mem ht 3)
      exact (Subgroup.disjoint_def.mp hdST) (pow_mem hs 3) h6
    have hsSp : s ∈ Sp := hSpcov s (mem_sup_right hs) hs3
    have htqD : t * q ∈ D := by
      rw [hD]
      exact mul_mem (mem_sup_right ht) (mem_sup_left hq)
    have hle₁ : Sp ≤ sSup ({D, Sp} : Set (Subgroup G)) := le_sSup (by simp)
    have hle₂ : D ≤ sSup ({D, Sp} : Set (Subgroup G)) := le_sSup (by simp)
    rw [mul_assoc]
    exact mul_mem (hle₁ hsSp) (hle₂ htqD)

end SThree

end RCSTOm

end CFSG.StandardType
