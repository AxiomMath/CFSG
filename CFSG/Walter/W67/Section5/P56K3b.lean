module

public import CFSG.Walter.W67.Section5.P56K3a
public import CFSG.Walter.W67.Section6.Basic

public section

namespace CFSG.Walter.W67

variable {G : Type} [Group G] [Finite G]

namespace Frame5

variable {s : Std G} {f5 : Frame5 s}

theorem odd_card_B (hp : s.p = 3) : Odd (Nat.card f5.B) := by
  have h := f5.card_B
  have h4 := s.q_mod_four hp
  rw [Nat.odd_iff]
  omega

namespace K3Data

variable {R V : Subgroup G} (hK : f5.K3Data R V)
include hK

theorem mem_of_fix
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {g w : G}
    (hgR : g ∈ Subgroup.normalizer (R : Set G))
    (hg3 : ¬ 3 ∣ orderOf g) (hC : ∀ y ∈ V, g * y = y * g → y ∈ R) (hw : w ∈ V)
    (hfix : g * w * g⁻¹ * w⁻¹ ∈ R) : w ∈ R := by
  have hVR := hK.le_normalizer h22 h26i hp
  set Q := R ⊔ Subgroup.zpowers w with hQdef
  have hQV : Q ≤ V := sup_le hK.le (Subgroup.zpowers_le.mpr hw)
  let T : Subgroup G :=
    { carrier := {y | y ∈ V ∧ g * y * g⁻¹ * y⁻¹ ∈ R}
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by
        have h1 : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
            (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [h1]
        exact R.mul_mem ha.2 ((Subgroup.mem_normalizer_iff.mp (hVR ha.1) _).mp hb.2)⟩
      one_mem' := ⟨V.one_mem, by rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact R.one_mem⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by
        have h1 : g * a⁻¹ * g⁻¹ * a⁻¹⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [h1]
        have := (Subgroup.mem_normalizer_iff.mp (hVR (V.inv_mem ha.1)) _).mp (R.inv_mem ha.2)
        simpa using this⟩ }
  have hQT : Q ≤ T := sup_le (fun r hr => ⟨hK.le hr, R.mul_mem
    ((Subgroup.mem_normalizer_iff.mp hgR r).mp hr) (R.inv_mem hr)⟩)
    (Subgroup.zpowers_le.mpr ⟨hw, hfix⟩)
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    have hyT := hQT hy
    have h1 : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    rw [h1]
    exact Q.mul_mem (Subgroup.mem_sup_left hyT.2) hy
  let S : Subgroup G :=
    { carrier := {r | r ∈ Subgroup.normalizer (R : Set G) ∧ r ∈ Subgroup.normalizer (Q : Set G) ∧
        ∀ y ∈ Q, r * y * r⁻¹ * y⁻¹ ∈ R}
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1,
        Subgroup.mul_mem _ ha.2.1 hb.2.1,
        fun y hy => by
          have h1 : a * b * y * (a * b)⁻¹ * y⁻¹ =
              (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
          rw [h1]
          exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp ha.1 _).mp (hb.2.2 y hy))
            (ha.2.2 y hy)⟩
      one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun y _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact R.one_mem⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, Subgroup.inv_mem _ ha.2.1, fun y hy => by
        have hy' : a⁻¹ * y * a ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha.2.1) y).mp hy
          simpa using this
        have h1 := ha.2.2 _ hy'
        have h2 : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹)⁻¹ := by
          group
        rw [h2]
        exact R.inv_mem h1⟩ }
  have hgS : g ∈ S := ⟨hgR, hgQ, fun y hy => (hQT hy).2⟩
  have hR₀S : Subgroup.zpowers g ≤ S := Subgroup.zpowers_le.mpr hgS
  have hwQ : w ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  refine Sec56.le_of_coprime_trivial (Q := Q) (M := R) (R₀ := Subgroup.zpowers g)
    (hK.isPGroup.to_le hQV) le_sup_left (by rwa [Nat.card_zpowers])
    (fun r hr => (hR₀S hr).2.1) (fun r hr => (hR₀S hr).1) (fun y hy => hVR (hQV hy))
    (fun r hr y hy => (hR₀S hr).2.2 y hy) (fun y hy hyg => ?_) hwQ
  exact hC y (hQV hy) (hyg g (Subgroup.mem_zpowers g))

theorem eq_one_of_fix
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {c w : G}
    (hc : c ∈ Subgroup.zpowers s.J ⊔ f5.B) (hw : w ∈ V) (hwR : w ∉ R)
    (hfix : c * w * c⁻¹ * w⁻¹ ∈ R) : c = 1 := by
  have hJB : f5.B ≤ Subgroup.normalizer ((Subgroup.zpowers s.J : Subgroup G) : Set G) := by
    intro b hb
    apply Sec53.mem_normalizer_of_conj_le
    intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hbJ : Commute b s.J := s.commute_J (s.K_le_H (f5.B_le hb))
    rw [show b * s.J ^ i * b⁻¹ = s.J ^ i by
      rw [(Commute.zpow_right hbJ i).eq, mul_inv_cancel_right]]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨j, hj, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hJB).mp hc
  have hBfix : ∀ b ∈ f5.B, b * w * b⁻¹ * w⁻¹ ∈ R → b = 1 := by
    intro b hb hbw
    by_contra hb1
    apply hwR
    refine hK.mem_of_fix h22 h26i hp (hK.rdata.B_le hb) (fun h3 =>
      f5.three_not_dvd_B hp (h3.trans (Subgroup.orderOf_dvd_natCard _ hb))) (fun y hy hby => ?_)
      hw hbw
    rw [hK.fpf h22 h26i hp b hb hb1 y hy hby]
    exact R.one_mem
  have hJR : s.J ∈ Subgroup.normalizer (R : Set G) := hK.rdata.J_le
  rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
  · rw [one_mul] at hfix ⊢
    exact hBfix b hb hfix
  · exfalso
    have hbJ : b * s.J = s.J * b := s.commute_J (s.K_le_H (f5.B_le hb))
    have hcR : s.J * b ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.mul_mem _ hJR (hK.rdata.B_le hb)
    have hb2 : b * b * w * (b * b)⁻¹ * w⁻¹ ∈ R := by
      have h1 : b * b = (s.J * b) * (s.J * b) := by
        calc b * b = (s.J * s.J) * (b * b) := by rw [s.J_mul_J, one_mul]
          _ = s.J * (s.J * b) * b := by group
          _ = s.J * (b * s.J) * b := by rw [hbJ]
          _ = (s.J * b) * (s.J * b) := by group
      set t := s.J * b * w * (s.J * b)⁻¹ * w⁻¹ with ht
      have h2 : (s.J * b) * (s.J * b) * w * ((s.J * b) * (s.J * b))⁻¹ * w⁻¹ =
          ((s.J * b) * t * (s.J * b)⁻¹) * t := by rw [ht]; group
      rw [h1, h2]
      exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp hcR t).mp hfix) hfix
    have hb1 : b = 1 := by
      have h := hBfix (b * b) (f5.B.mul_mem hb hb) hb2
      have hodd : Odd (orderOf b) :=
        Odd.of_dvd_nat (odd_card_B hp) (Subgroup.orderOf_dvd_natCard _ hb)
      have h2 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h])
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
      · exact orderOf_eq_one_iff.mp h3
      · rw [h3] at hodd
        exact absurd hodd (by decide)
    rw [hb1, mul_one] at hfix
    apply hwR
    refine hK.mem_of_fix h22 h26i hp hJR (by rw [s.orderOf_J]; norm_num) (fun y hy hJy => ?_)
      hw hfix
    have : y ∈ V ⊓ s.H := Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr
      hJy.symm⟩
    rw [hK.inf_H h22 h26i hp] at this
    exact hK.rdata.P₁_le this

omit hK in
theorem card_JB (hp : s.p = 3) :
    Nat.card (Subgroup.zpowers s.J ⊔ f5.B : Subgroup G) = s.q - 1 := by
  have hJB : Subgroup.zpowers s.J ≤ Subgroup.normalizer (f5.B : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => s.commute_J (s.K_le_H (f5.B_le hb))))
  have h1 := Sec52.card_sup_mul_card_inf hJB
  have hinf : f5.B ⊓ Subgroup.zpowers s.J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzB, hzJ⟩ := Subgroup.mem_inf.mp hz
    rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hzJ with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exfalso
      rw [h] at hzB
      have h2 := Subgroup.orderOf_dvd_natCard _ hzB
      rw [s.orderOf_J] at h2
      have : Odd (Nat.card f5.B) := odd_card_B hp
      rw [Nat.odd_iff] at this
      omega
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, s.orderOf_J, mul_comm] at h1
  rw [h1, f5.card_B]

theorem exists_conj
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3) {w₀ w : G}
    (hw₀ : w₀ ∈ V) (hw₀R : w₀ ∉ R) (hw : w ∈ V) (hwR : w ∉ R) :
    ∃ c ∈ Subgroup.zpowers s.J ⊔ f5.B, (c * w₀ * c⁻¹)⁻¹ * w ∈ R := by
  have hVR := hK.le_normalizer h22 h26i hp
  set JB := Subgroup.zpowers s.J ⊔ f5.B with hJBdef
  have hJBV : JB ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hK.J_le) hK.B_le
  have hJBR : JB ≤ Subgroup.normalizer (R : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hK.rdata.J_le) hK.rdata.B_le
  have hcV : ∀ c : JB, (c : G) * w₀ * (c : G)⁻¹ ∈ V := fun c =>
    (Subgroup.mem_normalizer_iff.mp (hJBV c.2) w₀).mp hw₀
  have hRn : (R.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK.le).mpr hVR
  let F : JB → V ⧸ R.subgroupOf V := fun c => QuotientGroup.mk (⟨_, hcV c⟩ : V)
  have hmk : ∀ a b : V, (QuotientGroup.mk a : V ⧸ R.subgroupOf V) = QuotientGroup.mk b ↔
      (a : G)⁻¹ * b ∈ R := fun a b => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hinj : Function.Injective F := by
    intro c c' h0
    have h : (QuotientGroup.mk (⟨_, hcV c⟩ : V) : V ⧸ R.subgroupOf V) =
        QuotientGroup.mk (⟨_, hcV c'⟩ : V) := h0
    rw [hmk] at h
    have h1 : ((c : G)⁻¹ * c') * w₀ * ((c : G)⁻¹ * c')⁻¹ * w₀⁻¹ ∈ R := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hJBR c.2)) _).mp h
      have h3 : (c : G)⁻¹ * (((c : G) * w₀ * (c : G)⁻¹)⁻¹ * ((c' : G) * w₀ * (c' : G)⁻¹)) *
          (c : G)⁻¹⁻¹ = w₀⁻¹ * (((c : G)⁻¹ * c') * w₀ * ((c : G)⁻¹ * c')⁻¹) := by group
      rw [h3] at h2
      have h4 := (Subgroup.mem_normalizer_iff.mp (hVR hw₀) _).mp h2
      have h5 : w₀ * (w₀⁻¹ * (((c : G)⁻¹ * c') * w₀ * ((c : G)⁻¹ * c')⁻¹)) * w₀⁻¹ =
          ((c : G)⁻¹ * c') * w₀ * ((c : G)⁻¹ * c')⁻¹ * w₀⁻¹ := by group
      rwa [h5] at h4
    have h6 := hK.eq_one_of_fix h22 h26i hp (JB.mul_mem (JB.inv_mem c.2) c'.2) hw₀ hw₀R h1
    apply Subtype.ext
    calc (c : G) = c * ((c : G)⁻¹ * c') := by rw [h6, mul_one]
      _ = c' := by group
  have hrange : Set.range F ⊆ {z | z ≠ 1} := by
    rintro _ ⟨c, rfl⟩ h
    have h1 : F c = QuotientGroup.mk (1 : V) := h
    rw [hmk] at h1
    simp only [OneMemClass.coe_one, mul_one] at h1
    apply hw₀R
    have h2 : (c : G) * w₀ * (c : G)⁻¹ ∈ R := by simpa using R.inv_mem h1
    exact (Subgroup.mem_normalizer_iff.mp (hJBR c.2) w₀).mpr h2
  have hcardQ : Nat.card (V ⧸ R.subgroupOf V) = s.q := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.le).toEquiv, hK.card_V, hK.card_R] at h1
    have hq := s.one_lt_q
    have : s.q ^ 2 * s.q = s.q ^ 2 * Nat.card (V ⧸ R.subgroupOf V) := by
      rw [← pow_succ, mul_comm (s.q ^ 2)]
      exact h1
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
  have hncard : ({z | z ≠ 1} : Set (V ⧸ R.subgroupOf V)).ncard = s.q - 1 := by
    have : ({z | z ≠ 1} : Set (V ⧸ R.subgroupOf V)) = ({1} : Set _)ᶜ := by
      ext z
      simp
    rw [this, Set.ncard_compl, Set.ncard_singleton, hcardQ]
  have heq : Set.range F = {z | z ≠ 1} := Set.eq_of_subset_of_ncard_le hrange
    (by rw [hncard, Set.ncard_range_of_injective hinj, card_JB (f5 := f5) hp])
  have hwm : (QuotientGroup.mk (⟨w, hw⟩ : V) : V ⧸ R.subgroupOf V) ∈ ({z | z ≠ 1} : Set _) := by
    intro h
    apply hwR
    have h1 : (QuotientGroup.mk (⟨w, hw⟩ : V) : V ⧸ R.subgroupOf V) = QuotientGroup.mk (1 : V) := h
    rw [hmk] at h1
    simpa using R.inv_mem h1
  rw [← heq] at hwm
  obtain ⟨c, hc⟩ := hwm
  exact ⟨c, c.2, (hmk _ _).mp hc⟩

theorem pow_three_ne_one
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hexp : ∃ y ∈ V, y ^ 3 ≠ 1) {v : G} (hv : v ∈ V) (hvR : v ∉ R) : v ^ 3 ≠ 1 := by
  obtain ⟨y₀, hy₀, hy₀3⟩ := hexp
  have hy₀R : y₀ ∉ R := fun h => hy₀3 (hK.pow_three h22 h26i hp h)
  obtain ⟨c, hc, hcv⟩ := hK.exists_conj h22 h26i hp hy₀ hy₀R hv hvR
  have hcV : c ∈ Subgroup.normalizer (V : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hK.J_le) hK.B_le hc
  have hcy : c * y₀ * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcV y₀).mp hy₀
  have hv' : v = (c * y₀ * c⁻¹) * ((c * y₀ * c⁻¹)⁻¹ * v) := by group
  rw [hv', hK.mul_pow_three h22 h26i hp hcy hcv, conj_pow]
  intro h
  apply hy₀3
  have := congrArg (fun z => c⁻¹ * z * c) h
  simpa [mul_assoc] using this

theorem mem_of_pow_three
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hexp : ∃ y ∈ V, y ^ 3 ≠ 1) {v : G} (hv : v ∈ V) (hv3 : v ^ 3 = 1) : v ∈ R := by
  by_contra hvR
  exact hK.pow_three_ne_one h22 h26i hp hexp hv hvR hv3

theorem eq_of_elementary
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hexp : ∃ y ∈ V, y ^ 3 ≠ 1) {P₀ : Subgroup G} (hP₀E : P₀ ≤ s.fr.E) {A : Subgroup G}
    (hA : A ≤ V ⊔ P₀) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAcard : s.q ^ 2 ≤ Nat.card A) : A = R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVR := hK.le_normalizer h22 h26i hp
  have hP₀V : P₀ ≤ Subgroup.normalizer (V : Set G) := hP₀E.trans hK.E_le
  have hVE : V ⊓ s.fr.E = ⊥ := f5.inf_E_eq_bot h26i hp hK.isPGroup hK.B_le
  have hdec : ∀ a ∈ A, ∃ v ∈ V, ∃ y ∈ P₀, a = v * y ∧ y ^ 3 = 1 := by
    intro a ha
    obtain ⟨v, hv, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer hP₀V).mp (hA ha)
    refine ⟨v, hv, y, hy, rfl, ?_⟩
    have h3 := hA3 _ ha
    have hyV : ∀ k : ℕ, y ^ k * v * (y ^ k)⁻¹ ∈ V := fun k =>
      (Subgroup.mem_normalizer_iff.mp (hP₀V (P₀.pow_mem hy k)) v).mp hv
    have e : (v * y) ^ 3 = (v * (y ^ 1 * v * (y ^ 1)⁻¹) * (y ^ 2 * v * (y ^ 2)⁻¹)) * y ^ 3 := by
      rw [pow_three' (v * y)]
      group
    rw [e] at h3
    have hy3V : y ^ 3 ∈ V := by
      rw [eq_inv_of_mul_eq_one_right h3]
      exact V.inv_mem (V.mul_mem (V.mul_mem hv (hyV 1)) (hyV 2))
    have : y ^ 3 ∈ V ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨hy3V, s.fr.E.pow_mem (hP₀E hy) 3⟩
    rwa [hVE, Subgroup.mem_bot] at this
  by_cases hAV : A ≤ V
  · have hAR : A ≤ R := fun a ha => hK.mem_of_pow_three h22 h26i hp hexp (hAV ha) (hA3 a ha)
    exact Subgroup.eq_of_le_of_card_ge hAR (by rw [hK.card_R]; exact hAcard)
  exfalso
  obtain ⟨a, haA, haV⟩ := Set.not_subset.mp hAV
  obtain ⟨v, hv, y, hy, rfl, hy3⟩ := hdec _ haA
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact haV (by rw [mul_one]; exact hv)
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyE := hP₀E hy
  have hzy : ∀ y' ∈ s.fr.E, y' ^ 3 = 1 → y' ∈ Subgroup.zpowers y := by
    intro y' hy'E hy'3
    by_cases hy'1 : y' = 1
    · rw [hy'1]
      exact Subgroup.one_mem _
    have hoy' : orderOf y' = 3 := orderOf_eq_prime hy'3 hy'1
    have := Sec6.isCyclic_E s
    have heq : Subgroup.zpowers (⟨y', hy'E⟩ : s.fr.E) = Subgroup.zpowers (⟨y, hyE⟩ : s.fr.E) :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr (by
        rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hoy',
          hoy])
    have hmem : (⟨y', hy'E⟩ : s.fr.E) ∈ Subgroup.zpowers (⟨y, hyE⟩ : s.fr.E) :=
      heq ▸ Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hcip := hK.center_inf_P₁
  have hcN := hK.card_center h22 h26i hp
  have hsup := hK.sup_center h22 h26i hp
  set N₁ := V ⊓ Subgroup.centralizer (V : Set G) with hN₁def
  have hN₁P : N₁ ≤ Subgroup.normalizer (f5.P₁ : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 u (hK.P₁_le hu))
  set X := f5.P₁ ⊓ Subgroup.centralizer ({y} : Set G) with hXdef
  have hAVD : V ⊓ A ≤ X ⊔ N₁ := by
    intro z hz
    obtain ⟨hzV, hzA⟩ := Subgroup.mem_inf.mp hz
    have hzR : z ∈ R := hK.mem_of_pow_three h22 h26i hp hexp hzV (hA3 z hzA)
    rw [← hsup] at hzR
    obtain ⟨u, hu, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer hN₁P).mp hzR
    have hcomm : (v * y) * (u * w) = (u * w) * (v * y) := hAc _ haA _ hzA
    set u' := y * u * y⁻¹ with hu'def
    set w' := y * w * y⁻¹ with hw'def
    have hu'P : u' ∈ f5.P₁ :=
      (Subgroup.mem_normalizer_iff.mp (f5.E_le_normalizer_P₁ hyE) u).mp hu
    have hw'N : w' ∈ N₁ :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_center (hK.E_le hyE)) w).mp hw
    have hn : u'⁻¹ * v * u' * v⁻¹ ∈ N₁ := by
      have := hK.commutator_mem h22 h26i hp (R.inv_mem (hK.rdata.P₁_le hu'P)) hv
      rwa [inv_inv] at this
    have hw'c : v * w' = w' * v :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw'N).2 v hv
    have hw'v : w' * v⁻¹ = v⁻¹ * w' := by
      calc w' * v⁻¹ = v⁻¹ * (v * w') * v⁻¹ := by group
        _ = v⁻¹ * (w' * v) * v⁻¹ := by rw [hw'c]
        _ = v⁻¹ * w' := by group
    have h1 : u * w = u' * (u'⁻¹ * v * u' * v⁻¹) * w' := by
      calc u * w = (u * w) * (v * y) * (v * y)⁻¹ := by group
        _ = (v * y) * (u * w) * (v * y)⁻¹ := by rw [hcomm]
        _ = v * u' * (w' * v⁻¹) := by rw [hu'def, hw'def]; group
        _ = v * u' * (v⁻¹ * w') := by rw [hw'v]
        _ = u' * (u'⁻¹ * v * u' * v⁻¹) * w' := by group
    have h2 : u'⁻¹ * u ∈ N₁ := by
      have : u'⁻¹ * u = (u'⁻¹ * v * u' * v⁻¹) * w' * w⁻¹ := by
        calc u'⁻¹ * u = u'⁻¹ * (u * w) * w⁻¹ := by group
          _ = u'⁻¹ * (u' * (u'⁻¹ * v * u' * v⁻¹) * w') * w⁻¹ := by rw [h1]
          _ = (u'⁻¹ * v * u' * v⁻¹) * w' * w⁻¹ := by group
      rw [this]
      exact N₁.mul_mem (N₁.mul_mem hn hw'N) (N₁.inv_mem hw)
    have h3 : u'⁻¹ * u ∈ N₁ ⊓ f5.P₁ :=
      Subgroup.mem_inf.mpr ⟨h2, f5.P₁.mul_mem (f5.P₁.inv_mem hu'P) hu⟩
    rw [hcip, Subgroup.mem_bot] at h3
    have hyu : y * u * y⁻¹ = u := inv_mul_eq_one.mp h3
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hu, ?_⟩))
      (Subgroup.mem_sup_right hw)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * y = y * u * y⁻¹ * y := by rw [hyu]
      _ = y * u := by group
  have hc3 := f5.card_inf_centralizer_pow_three h22 h26i hp (f5.isPGroup_P₁ hp)
    f5.B_le_normalizer_P₁ f5.E_le_normalizer_P₁ hyE hoy
  rw [f5.card_P₁] at hc3
  have hDcard : Nat.card (X ⊔ N₁ : Subgroup G) ≤ Nat.card X * s.q := by
    have hN₁X : N₁ ≤ Subgroup.normalizer (X : Set G) := fun w hw =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 u
          (hK.P₁_le (Subgroup.mem_inf.mp hu).1))
    have e := Sec52.card_sup_mul_card_inf hN₁X
    rw [sup_comm, hcN] at e
    have hpos : 0 < Nat.card (X ⊓ N₁ : Subgroup G) := Nat.card_pos
    calc Nat.card (X ⊔ N₁ : Subgroup G) ≤ Nat.card (X ⊔ N₁ : Subgroup G) *
          Nat.card (X ⊓ N₁ : Subgroup G) := Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card X * s.q := e
  have hAN : A ≤ Subgroup.normalizer (V : Set G) :=
    hA.trans (sup_le Subgroup.le_normalizer hP₀V)
  have e1 := Sec52.card_sup_mul_card_inf hAN
  have hAVy : A ⊔ V ≤ V ⊔ Subgroup.zpowers y := by
    refine sup_le (fun a' ha' => ?_) le_sup_left
    obtain ⟨v', hv', y', hy', rfl, hy'3⟩ := hdec _ ha'
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv')
      (Subgroup.mem_sup_right (hzy y' (hP₀E hy') hy'3))
  have hVy : Nat.card (V ⊔ Subgroup.zpowers y : Subgroup G) = Nat.card V * 3 := by
    have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set G) :=
      Subgroup.zpowers_le.mpr (hP₀V hy)
    have e2 := Sec52.card_sup_mul_card_inf hyN
    have hinf : V ⊓ Subgroup.zpowers y = ⊥ := by
      rw [eq_bot_iff, ← hVE]
      exact inf_le_inf_left _ (Subgroup.zpowers_le.mpr hyE)
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hoy, sup_comm] at e2
    exact e2
  have h1 : Nat.card A ≤ 3 * Nat.card (V ⊓ A : Subgroup G) := by
    have h2 := Subgroup.card_le_of_le hAVy
    rw [hVy] at h2
    have hVpos : 0 < Nat.card V := Nat.card_pos
    have : Nat.card V * Nat.card A ≤ Nat.card V * (3 * Nat.card (V ⊓ A : Subgroup G)) := by
      rw [← e1]
      calc Nat.card (A ⊔ V : Subgroup G) * Nat.card (V ⊓ A : Subgroup G)
          ≤ Nat.card V * 3 * Nat.card (V ⊓ A : Subgroup G) := Nat.mul_le_mul_right _ h2
        _ = Nat.card V * (3 * Nat.card (V ⊓ A : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_left this hVpos
  have h4 := Subgroup.card_le_of_le hAVD
  have hq := s.three_lt_q
  set c := Nat.card X with hcdef
  have h5 : s.q ^ 2 ≤ 3 * c * s.q := by
    calc s.q ^ 2 ≤ Nat.card A := hAcard
      _ ≤ 3 * Nat.card (V ⊓ A : Subgroup G) := h1
      _ ≤ 3 * (c * s.q) := Nat.mul_le_mul_left _ (h4.trans hDcard)
      _ = 3 * c * s.q := by ring
  have h6 : s.q ≤ 3 * c := by
    have : s.q * s.q ≤ (3 * c) * s.q := by rw [← pow_two]; exact h5
    exact Nat.le_of_mul_le_mul_right this (by omega)
  rcases Nat.lt_or_ge c 2 with hc | hc
  · interval_cases c <;> simp at hc3 <;> omega
  · have h7 : 4 ≤ c * c := Nat.mul_le_mul hc hc
    have h8 : 4 * c ≤ c ^ 3 := by
      calc 4 * c ≤ c * c * c := Nat.mul_le_mul_right c h7
        _ = c ^ 3 := by ring
    omega

end K3Data

end Frame5

end CFSG.Walter.W67
