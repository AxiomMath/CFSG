module

public import CFSG.Quasithin.H13.GoldschmidtI51Trans
public import CFSG.Quasithin.H13.Sp62D3

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6 Equiv

structure ModelIdx (K : Type*) [Group K] (P₀ X₁ X₂ : Subgroup K) : Prop where
  p2 : IsPGroup 2 P₀
  syl : ¬ 2 ∣ P₀.index
  cls : ∀ Y : Subgroup K, P₀ ≤ Y → Y = P₀ ∨ Y = X₁ ∨ Y = X₂ ∨ Y = ⊤
  le₁ : P₀ ≤ X₁
  le₂ : P₀ ≤ X₂
  inc₁ : ¬ X₁ ≤ X₂
  inc₂ : ¬ X₂ ≤ X₁
  idx₁ : P₀.relIndex X₁ = 3
  idx₂ : P₀.relIndex X₂ = 3
  nn₁ : ¬ X₁ ≤ Subgroup.normalizer (P₀ : Set K)
  nn₂ : ¬ X₂ ≤ Subgroup.normalizer (P₀ : Set K)

theorem relIndex_eq_of_card {K : Type*} [Group K] {A B : Subgroup K} (hAB : A ≤ B) {k : ℕ}
    (h : Nat.card B = k * Nat.card A) (hA : 0 < Nat.card A) : A.relIndex B = k := by
  have h1 : A.relIndex B * Nat.card A = Nat.card B := by
    rw [Subgroup.relIndex, mul_comm, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv,
      Subgroup.card_mul_index]
  rw [h] at h1
  exact Nat.eq_of_mul_eq_mul_right hA h1

theorem not_le_normalizer_of_conj {K : Type*} [Group K] {P X : Subgroup K} {x p : K}
    (hx : x ∈ X) (hp : p ∈ P) (hxp : x * p * x⁻¹ ∉ P) :
    ¬ X ≤ Subgroup.normalizer (P : Set K) := fun h =>
  hxp ((Subgroup.mem_normalizer_iff.mp (h hx) p).mp hp)

section Transport

variable {G : Type} [Group G] [Finite G] {K : Type*} [Group K] [Finite K]

theorem ModelIdx.transport {P₀ X₁ X₂ : Subgroup K} (hM : ModelIdx K P₀ X₁ X₂) {X T : Subgroup G}
    (hiso : quasithinO2QuotientIso X K) (hT : IsSylowTwoOf T X) :
    ∃ A₁ A₂ : Subgroup G, T ≤ A₁ ∧ T ≤ A₂ ∧ A₁ ≤ X ∧ A₂ ≤ X ∧ ¬ A₁ ≤ A₂ ∧ ¬ A₂ ≤ A₁ ∧
      A₁ ≠ X ∧ A₂ ≠ X ∧ T.relIndex A₁ = 3 ∧ T.relIndex A₂ = 3 ∧
      ¬ A₁ ≤ Subgroup.normalizer (T : Set G) ∧ ¬ A₂ ≤ Subgroup.normalizer (T : Set G) ∧
      T.relIndex X = P₀.index ∧ (pCoreOf 2 X).relIndex T = Nat.card P₀ ∧
      ∀ Y : Subgroup G, T ≤ Y → Y ≤ X → Y = T ∨ Y = A₁ ∨ Y = A₂ ∨ Y = X := by
  obtain ⟨φ, hφ, hker, hTφ⟩ := I51.exists_model_hom hiso hT hM.p2 hM.syl
  have hTX := hT.1
  have hsub : ∀ B : Subgroup ↥X, ((B.map X.subtype).subgroupOf X) = B := fun B =>
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective B
  have hTc : T.subgroupOf X = P₀.comap φ := by
    rw [I51.subgroupOf_eq_comap_map hT φ hker le_rfl, hTφ]
  have hTm : T = (P₀.comap φ).map X.subtype := by
    rw [← hTc, map_subtype_subgroupOf hTX]
  set A₁ := (X₁.comap φ).map X.subtype with hA₁
  set A₂ := (X₂.comap φ).map X.subtype with hA₂
  have hle : ∀ {B C : Subgroup K}, (B.comap φ).map X.subtype ≤ (C.comap φ).map X.subtype ↔
      B ≤ C := fun {B C} => by
    rw [Subgroup.map_subtype_le_map_subtype, Subgroup.comap_le_comap_of_surjective hφ]
  have hTA : ∀ {B : Subgroup K}, P₀ ≤ B → T ≤ (B.comap φ).map X.subtype := fun {B} hB => by
    rw [hTm]
    exact hle.mpr hB
  have hne : ∀ {B : Subgroup K}, B ≠ ⊤ → (B.comap φ).map X.subtype ≠ X := fun {B} hB h => by
    apply hB
    have h1 : B.comap φ = ⊤ := by
      rw [← hsub (B.comap φ), h, Subgroup.subgroupOf_self]
    rw [← Subgroup.map_comap_eq_self_of_surjective hφ B, h1, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hφ]
  have hX₁ : X₁ ≠ ⊤ := fun h => hM.inc₂ (h ▸ le_top)
  have hX₂ : X₂ ≠ ⊤ := fun h => hM.inc₁ (h ▸ le_top)
  have hidx : ∀ {B : Subgroup K}, P₀ ≤ B → T.relIndex ((B.comap φ).map X.subtype) =
      P₀.relIndex B := fun {B} hB => by
    rw [← Subgroup.relIndex_subgroupOf (Subgroup.map_subtype_le _), hsub, hTc,
      Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hφ]
  have hnn : ∀ {B : Subgroup K}, ¬ B ≤ Subgroup.normalizer (P₀ : Set K) →
      ¬ (B.comap φ).map X.subtype ≤ Subgroup.normalizer (T : Set G) := fun {B} hB h => by
    apply hB
    intro b hbB
    obtain ⟨a, rfl⟩ := hφ b
    have haA : (a : G) ∈ (B.comap φ).map X.subtype := ⟨a, hbB, rfl⟩
    have haN := h haA
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    rw [← hTφ] at hp ⊢
    obtain ⟨t, ht, rfl⟩ := hp
    refine ⟨a * t * a⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    have := (Subgroup.mem_normalizer_iff.mp haN (t : G)).mp (Subgroup.mem_subgroupOf.mp ht)
    simpa using this
  refine ⟨A₁, A₂, hTA hM.le₁, hTA hM.le₂, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _,
    fun h => hM.inc₁ (hle.mp h), fun h => hM.inc₂ (hle.mp h), hne hX₁, hne hX₂,
    by rw [hidx hM.le₁, hM.idx₁], by rw [hidx hM.le₂, hM.idx₂], hnn hM.nn₁, hnn hM.nn₂, ?_, ?_,
    fun Y hTY hYX => ?_⟩
  ·
    rw [← Subgroup.relIndex_subgroupOf (le_rfl : X ≤ X), Subgroup.subgroupOf_self,
      Subgroup.relIndex_top_right, hTc, Subgroup.index_comap_of_surjective _ hφ]
  ·
    have hO : (pCoreOf 2 X).subgroupOf X = (⊥ : Subgroup K).comap φ := by
      rw [MonoidHom.comap_bot, hker]
      exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [← Subgroup.relIndex_subgroupOf hTX, hO, hTc, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hφ, Subgroup.relIndex_bot_left]
  ·
    have hYc := I51.subgroupOf_eq_comap_map hT φ hker hTY
    have hPY : P₀ ≤ (Y.subgroupOf X).map φ := by
      rw [← hTφ]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hTY)
    have hYm : Y = (((Y.subgroupOf X).map φ).comap φ).map X.subtype := by
      rw [← hYc, map_subtype_subgroupOf hYX]
    rcases hM.cls _ hPY with h | h | h | h
    · left
      rw [hYm, h, ← hTm]
    · right; left
      rw [hYm, h]
    · right; right; left
      rw [hYm, h]
    · right; right; right
      rw [hYm, h, Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Transport

theorem modelIdx_SL3 : ModelIdx SL3.S SL3.P0 SL3.X1 SL3.X2 where
  p2 := SL3.P0_sylow.1
  syl := SL3.P0_sylow.2
  cls := SL3.overgroups_SL3
  le₁ := inf_le_left
  le₂ := inf_le_right
  inc₁ := SL3.X_incomparable.1
  inc₂ := SL3.X_incomparable.2
  idx₁ := relIndex_eq_of_card (show SL3.P0 ≤ SL3.X1 from inf_le_left)
    (by rw [SL3.card_X1, SL3.card_P0]) (by rw [SL3.card_P0]; norm_num)
  idx₂ := relIndex_eq_of_card (show SL3.P0 ≤ SL3.X2 from inf_le_right)
    (by rw [SL3.card_X2, SL3.card_P0]) (by rw [SL3.card_P0]; norm_num)
  nn₁ := not_le_normalizer_of_conj (x := SL3.s2) (p := SL3.ey)
    (show SL3.InX1 SL3.s2 by decide +kernel)
    (show SL3.InX1 SL3.ey ∧ SL3.InX2 SL3.ey by decide +kernel)
    (show ¬ (SL3.InX1 (SL3.s2 * SL3.ey * SL3.s2⁻¹) ∧ SL3.InX2 (SL3.s2 * SL3.ey * SL3.s2⁻¹)) by
      decide +kernel)
  nn₂ := not_le_normalizer_of_conj (x := SL3.s1) (p := SL3.ex)
    (show SL3.InX2 SL3.s1 by decide +kernel)
    (show SL3.InX1 SL3.ex ∧ SL3.InX2 SL3.ex by decide +kernel)
    (show ¬ (SL3.InX1 (SL3.s1 * SL3.ex * SL3.s1⁻¹) ∧ SL3.InX2 (SL3.s1 * SL3.ex * SL3.s1⁻¹)) by
      decide +kernel)

theorem index_P0_SL3 : SL3.P0.index = 21 := by
  have h := Subgroup.card_mul_index SL3.P0
  rw [SL3.card_P0, SL3.card_S] at h
  omega

theorem modelIdx_S6 : ModelIdx (Perm (Fin 6)) D6sub P1sub P2sub where
  p2 := D6syl.isPGroup'
  syl := D6syl.not_dvd_index
  cls := overgroups_D6
  le₁ := fun _ hσ => (D6sub_le hσ).1
  le₂ := fun _ hσ => (D6sub_le hσ).2
  inc₁ := P1_not_le_P2.1
  inc₂ := P1_not_le_P2.2
  idx₁ := relIndex_eq_of_card (fun _ hσ => (D6sub_le hσ).1) (by rw [card_P1sub, card_D6sub])
    (by rw [card_D6sub]; norm_num)
  idx₂ := relIndex_eq_of_card (fun _ hσ => (D6sub_le hσ).2) (by rw [card_P2sub, card_D6sub])
    (by rw [card_D6sub]; norm_num)
  nn₁ := not_le_normalizer_of_conj (x := swap 1 2) (p := swap 0 1)
    (show InP1 (swap 1 2) by decide) (show InD6 (swap 0 1) by decide)
    (show ¬ InD6 (swap 1 2 * swap 0 1 * (swap 1 2)⁻¹) by decide)
  nn₂ := not_le_normalizer_of_conj (x := swap 0 4 * swap 1 5) (p := swap 0 2 * swap 1 3)
    (show InP2 (swap 0 4 * swap 1 5) by decide +kernel)
    (show InD6 (swap 0 2 * swap 1 3) by decide)
    (show ¬ InD6 (swap 0 4 * swap 1 5 * (swap 0 2 * swap 1 3) * (swap 0 4 * swap 1 5)⁻¹) by
      decide)

theorem index_D6 : D6sub.index = 45 := by
  have h := Subgroup.card_mul_index D6sub
  rw [card_D6sub, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have : Nat.factorial 6 = 720 := by decide
  omega

theorem card_A6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_QA6_A6 : Nat.card ↥(QA6sub.subgroupOf (alternatingGroup (Fin 6))) = 8 := by
  have hQA : QA6sub ≤ alternatingGroup (Fin 6) := inf_le_right
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv, card_QA6sub]

theorem index_QA6 : (QA6sub.subgroupOf (alternatingGroup (Fin 6))).index = 45 := by
  have h := Subgroup.card_mul_index (QA6sub.subgroupOf (alternatingGroup (Fin 6)))
  rw [card_QA6_A6, card_A6] at h
  omega

@[expose] def a6x : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 1 2 * swap 4 5, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

@[expose] def a6p : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 1 * swap 4 5, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

@[expose] def a6y : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 4 * swap 1 5, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

@[expose] def a6q : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 2 * swap 1 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

@[expose] def a6z : ↥(alternatingGroup (Fin 6)) :=
  ⟨swap 0 2 * swap 4 5, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩

theorem modelIdx_A6 : ModelIdx ↥(alternatingGroup (Fin 6))
    (QA6sub.subgroupOf (alternatingGroup (Fin 6))) (P1sub.subgroupOf (alternatingGroup (Fin 6)))
    (P2sub.subgroupOf (alternatingGroup (Fin 6))) := by
  have hQA : QA6sub ≤ alternatingGroup (Fin 6) := inf_le_right
  have hcardP : Nat.card ↥(QA6sub.subgroupOf (alternatingGroup (Fin 6))) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv, card_QA6sub]
  have hcard₁ : Nat.card ↥(P1sub.subgroupOf (alternatingGroup (Fin 6))) = 24 := by
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, card_P1A6]
  have hcard₂ : Nat.card ↥(P2sub.subgroupOf (alternatingGroup (Fin 6))) = 24 := by
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, card_P2A6]
  have hmap : ∀ Y : Subgroup ↥(alternatingGroup (Fin 6)),
      (Y.map (alternatingGroup (Fin 6)).subtype).subgroupOf (alternatingGroup (Fin 6)) = Y :=
    fun Y => Subgroup.comap_map_eq_self_of_injective (alternatingGroup (Fin 6)).subtype_injective Y
  have hle₁ : QA6sub.subgroupOf (alternatingGroup (Fin 6)) ≤
      P1sub.subgroupOf (alternatingGroup (Fin 6)) :=
    Subgroup.subgroupOf_mono _ (fun σ hσ => (D6sub_le hσ.1).1)
  have hle₂ : QA6sub.subgroupOf (alternatingGroup (Fin 6)) ≤
      P2sub.subgroupOf (alternatingGroup (Fin 6)) :=
    Subgroup.subgroupOf_mono _ (fun σ hσ => (D6sub_le hσ.1).2)
  refine ⟨IsPGroup.of_card (n := 3) (by rw [hcardP]; norm_num), ?_, fun Y hY => ?_, hle₁, hle₂,
    ?_, ?_, relIndex_eq_of_card hle₁ (by rw [hcard₁, hcardP]) (by rw [hcardP]; norm_num),
    relIndex_eq_of_card hle₂ (by rw [hcard₂, hcardP]) (by rw [hcardP]; norm_num), ?_, ?_⟩
  · have := Subgroup.card_mul_index (QA6sub.subgroupOf (alternatingGroup (Fin 6)))
    rw [hcardP, card_A6] at this
    have h45 : (QA6sub.subgroupOf (alternatingGroup (Fin 6))).index = 45 := by omega
    rw [h45]
    norm_num
  · have hQY : QA6sub ≤ Y.map (alternatingGroup (Fin 6)).subtype := by
      intro σ hσ
      exact ⟨⟨σ, hQA hσ⟩, hY hσ, rfl⟩
    have hYA : Y.map (alternatingGroup (Fin 6)).subtype ≤ alternatingGroup (Fin 6) :=
      Subgroup.map_subtype_le Y
    rcases overgroups_QA6 _ hQY hYA with h | h | h | h
    · left
      rw [← hmap Y, h]
    · right; left
      rw [← hmap Y, h, Subgroup.inf_subgroupOf_right]
    · right; right; left
      rw [← hmap Y, h, Subgroup.inf_subgroupOf_right]
    · right; right; right
      rw [← hmap Y, h, Subgroup.subgroupOf_self]
  · intro h
    have hm : a6z ∈ P1sub.subgroupOf (alternatingGroup (Fin 6)) :=
      show InP1 (swap 0 2 * swap 4 5) by decide
    exact absurd (h hm) (show ¬ InP2 (swap 0 2 * swap 4 5) by decide)
  · intro h
    have hm : a6y ∈ P2sub.subgroupOf (alternatingGroup (Fin 6)) :=
      show InP2 (swap 0 4 * swap 1 5) by decide +kernel
    exact absurd (h hm) (show ¬ InP1 (swap 0 4 * swap 1 5) by decide)
  · refine not_le_normalizer_of_conj (x := a6x) (p := a6p)
      (show InP1 (swap 1 2 * swap 4 5) by decide)
      ⟨show InD6 (swap 0 1 * swap 4 5) by decide, a6p.2⟩ fun hc => ?_
    exact absurd (Subgroup.mem_subgroupOf.mp hc).1
      (show ¬ InD6 (swap 1 2 * swap 4 5 * (swap 0 1 * swap 4 5) * (swap 1 2 * swap 4 5)⁻¹) by
        decide)
  · refine not_le_normalizer_of_conj (x := a6y) (p := a6q)
      (show InP2 (swap 0 4 * swap 1 5) by decide +kernel)
      ⟨show InD6 (swap 0 2 * swap 1 3) by decide, a6q.2⟩ fun hc => ?_
    exact absurd (Subgroup.mem_subgroupOf.mp hc).1
      (show ¬ InD6 (swap 0 4 * swap 1 5 * (swap 0 2 * swap 1 3) * (swap 0 4 * swap 1 5)⁻¹) by
        decide)

end CFSG.Quasithin.H13.L32A
