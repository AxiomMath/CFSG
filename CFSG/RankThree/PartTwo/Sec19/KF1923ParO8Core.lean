module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

@[expose] def KFParO8Data (X : Type) [Group X] : Prop :=
  (∀ S : Subgroup X, IsSylowOf 2 S ⊤ → ¬ 5 ∣ Nat.card (Subgroup.normalizer (S : Set X))) ∧
  ∀ S : Subgroup X, IsSylowOf 2 S ⊤ → ∀ D E : Subgroup X,
    Subgroup.normalizer (S : Set X) ≤ D → ¬ 5 ∣ Nat.card D → E ≤ D → (∀ e ∈ E, e ^ 3 = 1) →
    Nat.card E = 9 → ∀ t ∈ S, (∀ e ∈ E, t * e * t⁻¹ ∈ E) →
      ¬ ∀ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ = e⁻¹

private theorem kfParO8_sylowConj {X : Type} [Group X] [Finite X] {S U : Subgroup X}
    (hS : IsSylowOf 2 S ⊤) (hU : IsSylowOf 2 U ⊤) :
    ∃ g : X, S.map (MulAut.conj g).toMonoidHom = U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have toSyl : ∀ S : Subgroup X, IsSylowOf 2 S ⊤ → ∃ P : Sylow 2 X, (P : Subgroup X) = S := by
    intro S hS
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right] at hS
    exact ⟨hS.2.1.toSylow hS.2.2, IsPGroup.toSylow_coe _ _⟩
  obtain ⟨P₁, rfl⟩ := toSyl S hS
  obtain ⟨P₂, rfl⟩ := toSyl U hU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul] at this
  rw [← this, Subgroup.pointwise_smul_def]
  rfl

theorem KFParO8Data.of_std {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hU : IsSylowOf 2 U ⊤) (hB : ¬ 5 ∣ Nat.card (Subgroup.normalizer (U : Set X)))
    (hH : ∀ D E : Subgroup X, Subgroup.normalizer (U : Set X) ≤ D → ¬ 5 ∣ Nat.card D → E ≤ D →
      (∀ e ∈ E, e ^ 3 = 1) → Nat.card E = 9 → ∀ t ∈ U, (∀ e ∈ E, t * e * t⁻¹ ∈ E) →
      ¬ ∀ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ = e⁻¹) :
    KFParO8Data X := by
  refine ⟨fun S hS => ?_, fun S hS D E hND hD5 hED hE3 hE9 t htS htN hinv => ?_⟩
  · obtain ⟨g, hg⟩ := kfParO8_sylowConj hS hU
    have hN : Subgroup.normalizer (U : Set X) =
        (Subgroup.normalizer (S : Set X)).map (MulAut.conj g).toMonoidHom := by
      rw [← hg]
      exact (Subgroup.map_equiv_normalizer_eq S (MulAut.conj g)).symm
    rw [hN, Subgroup.card_map_of_injective (MulAut.conj g).injective] at hB
    exact hB
  · obtain ⟨g, hg⟩ := kfParO8_sylowConj hS hU
    set φ : X →* X := (MulAut.conj g).toMonoidHom with hφ
    have hinj : Function.Injective φ := (MulAut.conj g).injective
    have hN : Subgroup.normalizer (U : Set X) = (Subgroup.normalizer (S : Set X)).map φ := by
      rw [← hg]
      exact (Subgroup.map_equiv_normalizer_eq S (MulAut.conj g)).symm
    refine hH (D.map φ) (E.map φ) (hN ▸ Subgroup.map_mono hND) ?_ (Subgroup.map_mono hED) ?_ ?_
      (φ t) (hg ▸ Subgroup.mem_map_of_mem φ htS) ?_ ?_
    · rwa [Subgroup.card_map_of_injective hinj]
    · rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hE3 e he, map_one]
    · rwa [Subgroup.card_map_of_injective hinj]
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨t * e * t⁻¹, htN e he, by simp [map_mul, map_inv]⟩
    · rintro _ ⟨e, he, rfl⟩
      have := hinv e he
      simpa [map_mul, map_inv, map_pow] using congrArg φ this

private theorem kfParO8_pow_odd_inverts {S : Type} [Group S] {s : S} {D : Subgroup S}
    (hs : ∀ d ∈ D, s * d * s⁻¹ = d⁻¹) {m : ℕ} (hm : Odd m) :
    ∀ d ∈ D, s ^ m * d * (s ^ m)⁻¹ = d⁻¹ := by
  have h2 : ∀ d ∈ D, s ^ 2 * d * (s ^ 2)⁻¹ = d := by
    intro d hd
    have h1 := hs d hd
    have h1' := hs d⁻¹ (D.inv_mem hd)
    rw [inv_inv] at h1'
    calc s ^ 2 * d * (s ^ 2)⁻¹ = s * (s * d * s⁻¹) * s⁻¹ := by rw [pow_two]; group
      _ = s * d⁻¹ * s⁻¹ := by rw [h1]
      _ = d := h1'
  have key : ∀ j : ℕ, ∀ d ∈ D, s ^ (2 * j + 1) * d * (s ^ (2 * j + 1))⁻¹ = d⁻¹ := by
    intro j
    induction j with
    | zero => intro d hd; simpa using hs d hd
    | succ j ih =>
      intro d hd
      have e1 : s ^ (2 * (j + 1) + 1) = s ^ 2 * s ^ (2 * j + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [e1]
      generalize s ^ (2 * j + 1) = u at ih ⊢
      calc s ^ 2 * u * d * (s ^ 2 * u)⁻¹ = s ^ 2 * (u * d * u⁻¹) * (s ^ 2)⁻¹ := by group
        _ = s ^ 2 * d⁻¹ * (s ^ 2)⁻¹ := by rw [ih d hd]
        _ = (s ^ 2 * d * (s ^ 2)⁻¹)⁻¹ := by group
        _ = d⁻¹ := by rw [h2 d hd]
  obtain ⟨j, rfl⟩ := hm
  exact key j

private theorem kfParO8_pow_normalizes {X : Type} [Group X] {E : Subgroup X} {t : X}
    (htN : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (n : ℕ) : ∀ e ∈ E, t ^ n * e * (t ^ n)⁻¹ ∈ E := by
  induction n with
  | zero => intro e he; simpa using he
  | succ n ih =>
    intro e he
    have h := htN _ (ih e he)
    simpa [pow_succ', mul_assoc] using h

private theorem kfParO8_exists_sylow {X : Type} [Group X] [Finite X] {P : Subgroup X} {z : X}
    {k : ℕ} (hzP : z ∈ P) (hz : z ^ 2 ^ k = 1) :
    ∃ Q : Subgroup X, IsSylowOf 2 Q P ∧ z ∈ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpz : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hz)
  have hA : IsPGroup 2 ((Subgroup.zpowers z).subgroupOf P) := by
    rw [← Subgroup.comap_subtype]
    exact hpz.comap_subtype
  obtain ⟨Q', hQ'⟩ := IsPGroup.exists_le_sylow hA
  refine ⟨(Q' : Subgroup P).map P.subtype, ⟨Q', rfl⟩, ?_⟩
  exact Subgroup.mem_map.2
    ⟨⟨z, hzP⟩, hQ' (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers z)), rfl⟩

private theorem kfParO8_isSylow_top {X : Type} [Group X] [Finite X] {P Q T : Subgroup X}
    (hT : IsSylowOf 2 T ⊤) (hTP : T ≤ P) (hQ : IsSylowOf 2 Q P) : IsSylowOf 2 Q ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT hQ ⊢
  obtain ⟨-, -, hTd⟩ := hT
  obtain ⟨hQP, hQ2, hQd⟩ := hQ
  refine ⟨le_top, hQ2, ?_⟩
  have hP : ¬ 2 ∣ P.relIndex ⊤ := fun h2 => hTd (by
    rw [← Subgroup.relIndex_mul_relIndex T P ⊤ hTP le_top]
    exact Dvd.dvd.mul_left h2 _)
  rw [← Subgroup.relIndex_mul_relIndex Q P ⊤ hQP le_top]
  intro h
  rcases (Nat.prime_two.dvd_mul).1 h with h1 | h1
  · exact hQd h1
  · exact hP h1

private theorem kfParO8_normalizer_le {X : Type} [Group X] [Finite X] {P Q T : Subgroup X}
    (hT : IsSylowOf 2 T ⊤) (hTP : Subgroup.normalizer (T : Set X) ≤ P) (hQ : IsSylowOf 2 Q P) :
    Subgroup.normalizer (Q : Set X) ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTle : T ≤ P := le_trans Subgroup.le_normalizer hTP
  have hTP' : IsSylowOf 2 T P := hT.of_le hTle le_top
  obtain ⟨T', hT'⟩ := hTP'.exists_sylow_eq_subgroupOf
  obtain ⟨Q', hQ'⟩ := hQ.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P T' Q'
  have h1 : (g • T' : Sylow 2 P) = Q' := hg
  have h2 := congrArg (fun S : Sylow 2 P => (S : Subgroup P)) h1
  simp only [Sylow.coe_subgroup_smul, hT', hQ'] at h2
  have hmem : ∀ y : P, y ∈ Q.subgroupOf P ↔ ∃ w : P, w ∈ T.subgroupOf P ∧ g * w * g⁻¹ = y := by
    intro y
    rw [← h2, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.smul_def, MulAut.conj_apply]
  have hQT : ∀ h : X, h ∈ T ↔ (g : X) * h * (g : X)⁻¹ ∈ Q := by
    intro h
    constructor
    · intro hh
      have hhP : h ∈ P := hTle hh
      have := (hmem ⟨(g : X) * h * (g : X)⁻¹, P.mul_mem (P.mul_mem g.2 hhP) (P.inv_mem g.2)⟩).2
        ⟨⟨h, hhP⟩, hh, rfl⟩
      exact this
    · intro hh
      have hQP : (g : X) * h * (g : X)⁻¹ ∈ P := hQ.le hh
      obtain ⟨w, hw, hwe⟩ := (hmem ⟨(g : X) * h * (g : X)⁻¹, hQP⟩).1 hh
      have : (w : X) = h := by
        have := congrArg Subtype.val hwe
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        have h3 : (g : X)⁻¹ * ((g : X) * (w : X) * (g : X)⁻¹) * (g : X) =
            (g : X)⁻¹ * ((g : X) * h * (g : X)⁻¹) * (g : X) := by rw [this]
        simpa [mul_assoc] using h3
      exact this ▸ hw
  intro x hx
  have hx' : (g : X)⁻¹ * x * (g : X) ∈ Subgroup.normalizer (T : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hQT h, hQT ((g : X)⁻¹ * x * (g : X) * h * ((g : X)⁻¹ * x * (g : X))⁻¹)]
    have e1 : (g : X) * ((g : X)⁻¹ * x * (g : X) * h * ((g : X)⁻¹ * x * (g : X))⁻¹) *
        (g : X)⁻¹ = x * ((g : X) * h * (g : X)⁻¹) * x⁻¹ := by group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.1 hx) _
  have := hTP hx'
  have hg' : (g : X) * ((g : X)⁻¹ * x * (g : X)) * (g : X)⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem g.2 this) (P.inv_mem g.2)
  simpa [mul_assoc] using hg'

private theorem kfParO8_not_five_dvd_sup_aux {H : Type} [Group H] [Finite H] (Y N : Subgroup H)
    [Y.Normal] (hY : ¬ 5 ∣ Nat.card Y) (hN : ¬ 5 ∣ Nat.card N) :
    ¬ 5 ∣ Nat.card (Y ⊔ N : Subgroup H) := by
  intro h5
  have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal Y N
  have h2 := Subgroup.relIndex_mul_card N (Y ⊔ N)
  have h3 := Subgroup.relIndex_mul_card N Y
  rw [inf_eq_left.2 (le_sup_right : N ≤ Y ⊔ N), h1] at h2
  rw [← h2] at h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 h5 with h | h
  · exact hY (h.trans (Dvd.intro _ h3))
  · exact hN h

private theorem kfParO8_not_five_dvd_sup {X : Type} [Group X] [Finite X] {P Y N : Subgroup X}
    (hYP : Y ≤ P) (hNP : N ≤ P) (hYn : ∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y)
    (hY : ¬ 5 ∣ Nat.card Y) (hN : ¬ 5 ∣ Nat.card N) :
    ¬ 5 ∣ Nat.card (Y ⊔ N : Subgroup X) := by
  haveI : (Y.subgroupOf P).Normal := ⟨fun y hy g => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simpa using hYn g g.2 y hy⟩
  have hYc : Nat.card (Y.subgroupOf P) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv
  have hNc : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hsup : Y ⊔ N ≤ P := sup_le hYP hNP
  have hSc : Nat.card ((Y ⊔ N).subgroupOf P) = Nat.card (Y ⊔ N : Subgroup X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsup).toEquiv
  have := kfParO8_not_five_dvd_sup_aux (Y.subgroupOf P) (N.subgroupOf P)
    (by rwa [hYc]) (by rwa [hNc])
  rwa [← Subgroup.subgroupOf_sup hYP hNP, hSc] at this

theorem kfParO8_core {X : Type} [Group X] [Finite X] (hd : KFParO8Data X) {P Y E : Subgroup X}
    (hTP : ∃ T : Subgroup X, IsSylowOf 2 T ⊤ ∧ Subgroup.normalizer (T : Set X) ≤ P)
    (hYP : Y ≤ P) (hYn : ∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) (hY5 : ¬ 5 ∣ Nat.card Y)
    (hEY : E ≤ Y) (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9) {t : X} (htP : t ∈ P)
    (htN : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (hinv : ∀ e ∈ E, t ^ 2 * e * (t ^ 2)⁻¹ = e⁻¹) : False := by
  obtain ⟨T, hT, hTN⟩ := hTP
  have hTle : T ≤ P := le_trans Subgroup.le_normalizer hTN
  obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
  set z : X := t ^ m with hz
  have hzk : z ^ 2 ^ k = 1 := by
    rw [hz, ← pow_mul, mul_comm m, ← hk, pow_orderOf_eq_one]
  have hzP : z ∈ P := pow_mem htP m
  have hzN : ∀ e ∈ E, z * e * z⁻¹ ∈ E := kfParO8_pow_normalizes htN m
  have hz2 : ∀ e ∈ E, z ^ 2 * e * (z ^ 2)⁻¹ = e⁻¹ := by
    have h2 : z ^ 2 = (t ^ 2) ^ m := by rw [hz, ← pow_mul, ← pow_mul, mul_comm]
    rw [h2]
    exact kfParO8_pow_odd_inverts hinv hm
  obtain ⟨Q, hQP, hzQ⟩ := kfParO8_exists_sylow hzP hzk
  have hQ2 : IsSylowOf 2 Q ⊤ := kfParO8_isSylow_top hT hTle hQP
  have hNQ : Subgroup.normalizer (Q : Set X) ≤ P := kfParO8_normalizer_le hT hTN hQP
  have hD5 : ¬ 5 ∣ Nat.card (Y ⊔ Subgroup.normalizer (Q : Set X) : Subgroup X) :=
    kfParO8_not_five_dvd_sup hYP hNQ hYn hY5 (hd.1 Q hQ2)
  exact hd.2 Q hQ2 (Y ⊔ Subgroup.normalizer (Q : Set X)) E le_sup_right hD5
    (hEY.trans le_sup_left) hE3 hE9 z hzQ hzN hz2

theorem kfParO8_sylow_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    {S : Subgroup X} (hS : IsSylowOf 2 S ⊤) : IsSylowOf 2 (S.map e.toMonoidHom) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS ⊢
  obtain ⟨-, hp, hd⟩ := hS
  refine ⟨le_top, hp.map _, ?_⟩
  rw [Subgroup.relIndex_top_right] at hd ⊢
  rwa [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]

theorem KFParO8Data.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : KFParO8Data Y) : KFParO8Data X := by
  refine ⟨fun S hS => ?_, fun S hS D E hND hD5 hED hE3 hE9 t htS htN hinv => ?_⟩
  · have := h.1 _ (kfParO8_sylow_map e hS)
    rwa [← Subgroup.map_equiv_normalizer_eq S e,
      Subgroup.card_map_of_injective e.injective] at this
  · refine h.2 _ (kfParO8_sylow_map e hS) (D.map e.toMonoidHom) (E.map e.toMonoidHom) ?_ ?_
      (Subgroup.map_mono hED) ?_ ?_ (e t) (Subgroup.mem_map_of_mem _ htS) ?_ ?_
    · rw [← Subgroup.map_equiv_normalizer_eq S e]
      exact Subgroup.map_mono hND
    · rwa [Subgroup.card_map_of_injective e.injective]
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_pow, hE3 x hx, map_one]
    · rwa [Subgroup.card_map_of_injective e.injective]
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨t * x * t⁻¹, htN x hx, by simp⟩
    · rintro _ ⟨x, hx, rfl⟩
      have := congrArg e.toMonoidHom (hinv x hx)
      simpa [map_mul, map_inv, map_pow] using this

end CFSG.RankThree.PartTwo.Late
