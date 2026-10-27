module

public import CFSG.Walter.W67.Section5.P56R1512
public import CFSG.Walter.W67.Section5.P56N9

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace Std

variable (s : Std G)

theorem core_three
    (h26i : S_lemma_2_6_i) (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts)
    (hp : s.p = 3) (hf3 : s.f = 3) {x : G} (hxE : x ∈ s.fr.E) (hox : orderOf x = 3)
    {T : Subgroup G} (hTc : Nat.card T = 27)
    (hTx : T ≤ Subgroup.centralizer ({x} : Set G)) (hTE : T ⊓ s.fr.E = ⊥)
    (hET : s.fr.E ≤ Subgroup.normalizer (T : Set G)) :
    (∃ y ∈ T, y ^ 3 ≠ 1) ∧
      ∀ u ∈ T, (∀ w ∈ T, u * w = w * u) → u * s.J = s.J * u → u = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.zpowers x with hXdef
  have hXE : X ≤ s.fr.E := Subgroup.zpowers_le.mpr hxE
  have hXcard : Nat.card X = 3 := by rw [hXdef, Nat.card_zpowers, hox]
  have hX1 : X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have heX : s.eX X = 3 := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one, hXcard]
  have hEX : s.fr.E = X := by
    have heE : s.eX s.fr.E = Nat.card s.fr.E := by
      rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
    obtain ⟨hediv, -, -⟩ := h26i G s.toHyp s.fr le_rfl s.E_ne_bot
    rw [heE, hf3] at hediv
    have h1 := Subgroup.card_dvd_of_le hXE
    rw [hXcard] at h1
    have h2 : Nat.card s.fr.E = 3 := Nat.dvd_antisymm hediv h1
    exact (Subgroup.eq_of_le_of_card_ge hXE (by rw [h2, hXcard])).symm
  have hEc : ∀ e ∈ s.fr.E, ∀ e' ∈ s.fr.E, e * e' = e' * e := Std.E_comm_all s
  have hE3 : ∀ e ∈ s.fr.E, e ^ 3 = 1 := by
    intro e he
    rw [hEX] at he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hox,
      pow_orderOf_eq_one, one_zpow]
  set L := s.L X with hLdef
  have hLS := s.L_spec X hXE hX1
  obtain ⟨K', hK'jr, -⟩ := hLS.jr
  have hfpos : 0 < s.f / s.eX X := by rw [heX, hf3]; norm_num
  obtain ⟨hL, hLp, hLf, -, -⟩ := hJR G s.p_ne_two hfpos hK'jr
  have hLq : hL.q = 3 := by
    rw [JRGroup.q, hLp, hLf, heX, hf3, hp]
    norm_num
  have hCX : Subgroup.centralizer (X : Set G) = L ⊔ s.fr.E := by
    rw [hLS.centralizer_eq (by rw [s.F_eq_bot]; exact bot_le)]
    have : Subgroup.centralizer (X : Set G) ⊓ s.fr.E = s.fr.E := inf_eq_right.mpr (fun e he =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hEc _ (hXE hy) _ he)
    rw [this]
  have hLC : L ≤ Subgroup.centralizer (s.fr.E : Set G) := by
    rw [hEX]
    exact hLS.le_centralizer
  have hEL : s.fr.E ≤ Subgroup.normalizer (L : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLC hl) e he).symm)
  have hCLE : Subgroup.centralizer ({x} : Set G) = L ⊔ s.fr.E := by
    rw [← hCX, hXdef, Sec52.centralizer_zpowers_eq]
  have hTLE : T ≤ L ⊔ s.fr.E := hCLE ▸ hTx
  have hLE : L ⊓ s.fr.E = ⊥ := by
    have hn : ((L ⊓ s.fr.E).subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgn : (g : G) * n * (g : G)⁻¹ = n := by
        rw [(Subgroup.mem_centralizer_iff.mp (hLC g.2) n (Subgroup.mem_inf.mp hn).2).symm,
          mul_inv_cancel_right]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hgn]
      exact hn⟩
    have hodd : Odd (Nat.card ((L ⊓ s.fr.E).subgroupOf L)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact Odd.of_dvd_nat s.fr.odd_card_E (Subgroup.card_dvd_of_le inf_le_right)
    have h1 := Sec6.eq_bot_of_normal_odd hR hL hLq _ hn hodd
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, (Subgroup.mem_inf.mp hy).1⟩ : L) ∈ (L ⊓ s.fr.E).subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hy
    rw [h1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hTEcard : Nat.card (T ⊔ s.fr.E : Subgroup G) = 81 := by
    rw [Sec54.card_sup_eq_mul hET hTE, hTc, hEX, hXcard]
  have hTE3 : IsPGroup 3 (T ⊔ s.fr.E : Subgroup G) := IsPGroup.of_card (n := 4) (by
    rw [hTEcard]; norm_num)
  have hLEcard : Nat.card (L ⊔ s.fr.E : Subgroup G) = Nat.card L * 3 := by
    rw [Sec54.card_sup_eq_mul hEL hLE, hEX, hXcard]
  have hTEN : T ⊔ s.fr.E ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hTLE.trans (sup_le Subgroup.le_normalizer hEL)) hEL
  set T' := L ⊓ (T ⊔ s.fr.E) with hT'def
  have hT'3 : IsPGroup 3 T' := hTE3.to_le inf_le_right
  have e1 := Sec52.card_sup_mul_card_inf hTEN
  have hsupLE : T ⊔ s.fr.E ⊔ L ≤ L ⊔ s.fr.E := sup_le (sup_le hTLE le_sup_right) le_sup_left
  have h1 := Subgroup.card_le_of_le hsupLE
  rw [hLEcard] at h1
  rw [hTEcard] at e1
  have hT'ge : 27 ≤ Nat.card T' := by
    have hLpos : 0 < Nat.card L := Nat.card_pos
    have : Nat.card L * 81 ≤ Nat.card L * 3 * Nat.card T' := by
      rw [← e1]
      exact Nat.mul_le_mul_right _ h1
    have : Nat.card L * 27 ≤ Nat.card L * Nat.card T' := by
      have h2 : Nat.card L * 81 = Nat.card L * 27 * 3 := by ring
      have h3 : Nat.card L * 3 * Nat.card T' = Nat.card L * Nat.card T' * 3 := by ring
      rw [h2, h3] at this
      exact Nat.le_of_mul_le_mul_right this (by norm_num)
    exact Nat.le_of_mul_le_mul_left this hLpos
  have hns : ¬ Group.IsSolvable L := by
    intro hsolv
    obtain ⟨-, -, -, hsolv'⟩ := (hR L hL (by rw [hLq]; norm_num)).1
    obtain ⟨-, h168, -⟩ := hsolv' hsolv
    have h2 := Subgroup.card_dvd_of_le (inf_le_left : T' ≤ L)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT'3
    rw [h168, hk] at h2
    rw [hk] at hT'ge
    have hk3 : 3 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k <;> norm_num at hT'ge
    have : 3 ^ 3 ∣ 168 := (pow_dvd_pow 3 hk3).trans h2
    norm_num at this
  have h1512 := Sec6.card_eq_1512 hR hL hLq hns
  have hT'c : Nat.card T' = 27 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT'3
    have h2 := Subgroup.card_dvd_of_le (inf_le_left : T' ≤ L)
    rw [h1512, hk] at h2
    have hk3 : k ≤ 3 := by
      by_contra h
      have : 3 ^ 4 ∣ 1512 := (pow_dvd_pow 3 (by omega)).trans h2
      norm_num at this
    rw [hk] at hT'ge ⊢
    have hk3' : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
      (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hT'ge)
    rw [show k = 3 by omega]
    norm_num
  set T'' := T'.subgroupOf L with hT''def
  have hT''3 : IsPGroup 3 T'' := hT'3.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hT''c : Nat.card T'' = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hT'c]
  have hdecTE : ∀ g ∈ T ⊔ s.fr.E, ∃ t ∈ T, ∃ e ∈ s.fr.E, g = t * e := by
    intro g hg
    obtain ⟨t, ht, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hET).mp hg
    exact ⟨t, ht, e, he, rfl⟩
  have hdecLE : ∀ g ∈ L ⊔ s.fr.E, ∃ l ∈ L, ∃ e ∈ s.fr.E, g = l * e := by
    intro g hg
    obtain ⟨l, hl, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEL).mp hg
    exact ⟨l, hl, e, he, rfl⟩
  have hTEc : ∀ t ∈ T, ∀ e ∈ s.fr.E, t * e = e * t := by
    intro t ht e he
    have htx : t ∈ Subgroup.centralizer (X : Set G) := by
      rw [hXdef, Sec52.centralizer_zpowers_eq]
      exact hTx ht
    rw [← hEX] at htx
    exact (Subgroup.mem_centralizer_iff.mp htx e he).symm
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨ℓ, hℓT, hℓ3⟩ := Sec56.exists_pow_three_ne_one_of_card hR hL hLq hns hT''3 hT''c
    have hℓ : (ℓ : G) ∈ T ⊔ s.fr.E := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hℓT)).2
    obtain ⟨t, ht, e, he, hte⟩ := hdecTE _ hℓ
    refine ⟨t, ht, fun h => hℓ3 (Subtype.ext ?_)⟩
    have hcomm : Commute t e := hTEc t ht e he
    rw [Subgroup.coe_pow, hte, hcomm.mul_pow, h, hE3 e he, one_mul]
    rfl
  ·
    intro u hu huc huJ
    obtain ⟨l, hl, e, he, hle⟩ := hdecLE _ (hTLE hu)
    have hlu : l = u * e⁻¹ := by rw [hle]; group
    have hlT' : l ∈ T' := Subgroup.mem_inf.mpr ⟨hl, by
      rw [hlu]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
        (Subgroup.mem_sup_right (s.fr.E.inv_mem he))⟩
    have hlc : ∀ w ∈ T'', (⟨l, hl⟩ : L) * w = w * ⟨l, hl⟩ := by
      intro w hw
      apply Subtype.ext
      obtain ⟨t, ht, e', he', hte⟩ := hdecTE _ (Subgroup.mem_inf.mp
        (Subgroup.mem_subgroupOf.mp hw)).2
      simp only [Subgroup.coe_mul]
      rw [hte, hlu]
      have h1 := huc t ht
      have h2 := hTEc u hu e' he'
      have h3 := hTEc t ht e⁻¹ (s.fr.E.inv_mem he)
      have h4 := hEc e⁻¹ (s.fr.E.inv_mem he) e' he'
      calc u * e⁻¹ * (t * e') = u * (e⁻¹ * t) * e' := by group
        _ = u * (t * e⁻¹) * e' := by rw [← h3]
        _ = (u * t) * (e⁻¹ * e') := by group
        _ = (t * u) * (e' * e⁻¹) := by rw [h1, h4]
        _ = t * (u * e') * e⁻¹ := by group
        _ = t * (e' * u) * e⁻¹ := by rw [h2]
        _ = t * e' * (u * e⁻¹) := by group
    have hJL : s.J ∈ L := hK'jr.J_mem
    have hlJ : (⟨l, hl⟩ : L) * ⟨s.J, hJL⟩ = ⟨s.J, hJL⟩ * ⟨l, hl⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hlu]
      have heJ : e⁻¹ * s.J = s.J * e⁻¹ := s.commute_J (s.fr.E_le_H (s.fr.E.inv_mem he))
      calc u * e⁻¹ * s.J = u * (s.J * e⁻¹) := by rw [mul_assoc, heJ]
        _ = s.J * u * e⁻¹ := by rw [← mul_assoc, huJ]
        _ = s.J * (u * e⁻¹) := by group
    have hoJ : orderOf (⟨s.J, hJL⟩ : L) = 2 := by rw [Subgroup.orderOf_mk, s.orderOf_J]
    have hl1 := Sec56.eq_one_of_mem_center hR hL hLq hns hT''3 hT''c
      (Subgroup.mem_subgroupOf.mpr hlT') hlc hoJ hlJ
    have hl1' : l = 1 := congrArg Subtype.val hl1
    have hue : u = e := by rw [hle, hl1', one_mul]
    have : u ∈ T ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨hu, hue ▸ he⟩
    rwa [hTE, Subgroup.mem_bot] at this

end Std

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

theorem inf_centralizer_facts
    (h26i : S_lemma_2_6_i) (hp : s.p = 3) {Q : Subgroup G}
    (hQ3 : IsPGroup 3 Q) (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E) :
    (Q ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ s.fr.E = ⊥ ∧
      s.fr.E ≤ Subgroup.normalizer
        ((Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  refine ⟨?_, fun e he => Sec54.mem_normalizer_inf (hEQ he) (Subgroup.le_normalizer
    (Subgroup.mem_centralizer_singleton_iff.mpr (Std.E_comm_all s _ he _ hxE)))⟩
  have := f5.inf_E_eq_bot h26i hp hQ3 hBQ
  rw [eq_bot_iff, ← this]
  exact inf_le_inf_right _ inf_le_left

theorem exists_pow_three_ne_one_three
    (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) (hf3 : s.f = 3)
    {Q : Subgroup G} (hQ3 : IsPGroup 3 Q) (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3)
    (hQx : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q) :
    ∃ y ∈ Q, y ^ 3 ≠ 1 := by
  obtain ⟨hTE, hET⟩ := f5.inf_centralizer_facts h26i hp hQ3 hBQ hEQ hxE
  have hTc : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 27 := by
    rw [hQx, Hyp.q, hp, hf3]
    norm_num
  obtain ⟨y, hyT, hy3⟩ := (s.core_three h26i hJR hR hp hf3 hxE hox hTc
    inf_le_right hTE hET).1
  exact ⟨y, (Subgroup.mem_inf.mp hyT).1, hy3⟩

theorem false_of_center_three
    (h26i : S_lemma_2_6_i)
    (hJR : S_IsJRSubgroup_nonempty_jrGroup) (hR : RFacts) (hp : s.p = 3) (hf3 : s.f = 3)
    {Q : Subgroup G} (hQ3 : IsPGroup 3 Q) (hP₁Q : f5.P₁ ≤ Q)
    (hP₁C : f5.P₁ ≤ Subgroup.centralizer (Q : Set G))
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hxE : x ∈ s.fr.E)
    (hox : orderOf x = 3)
    (hQx : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = s.q) : False := by
  obtain ⟨hTE, hET⟩ := f5.inf_centralizer_facts h26i hp hQ3 hBQ hEQ hxE
  have hTc : Nat.card (Q ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 27 := by
    rw [hQx, Hyp.q, hp, hf3]
    norm_num
  have h2 := (s.core_three h26i hJR hR hp hf3 hxE hox hTc
    inf_le_right hTE hET).2
  obtain ⟨u, hu, hu1, hux⟩ := f5.exists_mem_P₁_comm hp hxE hox
  exact hu1 (h2 u (Subgroup.mem_inf.mpr ⟨hP₁Q hu,
    Subgroup.mem_centralizer_singleton_iff.mpr hux.symm⟩)
    (fun w hw => (Subgroup.mem_centralizer_iff.mp (hP₁C hu) w (Subgroup.mem_inf.mp hw).1).symm)
    (s.commute_J (s.K_le_H (f5.P₁_le hu))))

end Frame5

end CFSG.Walter.W67
