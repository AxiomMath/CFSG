module

public import CFSG.Quasithin.Background.E6TwentyTwo

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Rank

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_sq_of_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : G} (h2 : y ^ 2 = 1)
    (hp' : y ^ p = 1) : y = 1 := by
  have h1 : orderOf y ∣ Nat.gcd 2 p := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one hp')
  have hcop : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem three_le_pRank_of_inverted {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {Y : Subgroup G}
    (hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) {y₁ y₂ y₃ e₂ e₃ : G} (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y)
    (hy₃ : y₃ ∈ Y) (hp₁ : y₁ ^ p = 1) (hp₂ : y₂ ^ p = 1) (hp₃ : y₃ ^ p = 1) (h1 : y₁ ≠ 1)
    (h2 : y₂ ≠ 1) (h3 : y₃ ≠ 1) (he₂₁ : e₂ * y₁ = y₁ * e₂) (he₂₂ : e₂ * y₂ * e₂⁻¹ = y₂⁻¹)
    (he₃₁ : e₃ * y₁ = y₁ * e₃) (he₃₂ : e₃ * y₂ = y₂ * e₃) (he₃₃ : e₃ * y₃ * e₃⁻¹ = y₃⁻¹) :
    3 ≤ CFSG.Open.pRank p Y := by
  have hp1 : 1 < p := hp.out.one_lt
  have hfix : ∀ {e y : G}, y ^ p = 1 → e * y * e⁻¹ = y⁻¹ → e * y = y * e → y = 1 := by
    intro e y hyp hinv hcomm
    have hyy : y = y⁻¹ := by
      rw [← hinv, hcomm, mul_inv_cancel_right]
    have hsq : y ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hyy]
      exact mul_inv_cancel y
    exact eq_one_of_sq_of_pow hp.out hp2 hsq hyp
  let F₀ : PUnit.{1} →* G := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hcard₀ : Nat.card PUnit.{1} = p ^ 0 := by simp
  have hx₁r : y₁ ∉ F₀.range := by
    rintro ⟨a, ha⟩
    exact h1 ha.symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrep₁⟩ := CFSG.SectionRank.exists_extend
    (fun _ _ => rfl) (fun _ => rfl) hcard₀ F₀ hF₀ hp₁ hx₁r (fun _ => Commute.one_left y₁)
  have hr₁ : ∀ a, ∃ n : ℕ, F₁ a = y₁ ^ n := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₁ a
    exact ⟨n, by rw [hb]; simp [F₀]⟩
  have hx₂r : y₂ ∉ F₁.range := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn⟩ := hr₁ a
    have hc : e₂ * y₂ = y₂ * e₂ := by
      rw [← ha, hn]
      exact (Commute.pow_right (show Commute e₂ y₁ from he₂₁) n).eq
    exact h2 (hfix hp₂ he₂₂ hc)
  have hc12 : ∀ a, Commute (F₁ a) y₂ := fun a => by
    obtain ⟨n, hn⟩ := hr₁ a
    rw [hn]
    exact Commute.pow_left (show Commute y₁ y₂ from hYab _ hy₁ _ hy₂) n
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrep₂⟩ :=
    CFSG.SectionRank.exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁ hp₂ hx₂r hc12
  have hr₂ : ∀ a, ∃ m n : ℕ, F₂ a = y₁ ^ m * y₂ ^ n := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₂ a
    obtain ⟨m, hm⟩ := hr₁ b
    exact ⟨m, n, by rw [hb, hm]⟩
  have hx₃r : y₃ ∉ F₂.range := by
    rintro ⟨a, ha⟩
    obtain ⟨m, n, hmn⟩ := hr₂ a
    have hc : e₃ * y₃ = y₃ * e₃ := by
      rw [← ha, hmn]
      exact ((Commute.pow_right (show Commute e₃ y₁ from he₃₁) m).mul_right
        (Commute.pow_right (show Commute e₃ y₂ from he₃₂) n)).eq
    exact h3 (hfix hp₃ he₃₃ hc)
  have hY₁ : ∀ m : ℕ, y₁ ^ m ∈ Y := fun m => Y.pow_mem hy₁ m
  have hY₂ : ∀ n : ℕ, y₂ ^ n ∈ Y := fun n => Y.pow_mem hy₂ n
  have hc3 : ∀ a, Commute (F₂ a) y₃ := fun a => by
    obtain ⟨m, n, hmn⟩ := hr₂ a
    rw [hmn]
    exact hYab _ (Y.mul_mem (hY₁ m) (hY₂ n)) _ hy₃
  obtain ⟨F₃, hF₃, hcomm₃, hpow₃, hcard₃, hrep₃⟩ :=
    CFSG.SectionRank.exists_extend hcomm₂ hpow₂ hcard₂ F₂ hF₂ hp₃ hx₃r hc3
  have hrange : F₃.range ≤ Y := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hrep₃ a
    obtain ⟨m, k, hmk⟩ := hr₂ b
    rw [hb, hmk]
    exact Y.mul_mem (Y.mul_mem (hY₁ m) (hY₂ k)) (Y.pow_mem hy₃ n)
  have := CFSG.SectionRank.le_pRank_of_injective hp1 hcomm₃ hpow₃ hcard₃ F₃ hF₃ hrange
  omega


theorem exists_inverted {p : ℕ} [hp : Fact p.Prime] {Y₀ : Subgroup G} (hY₀ : IsPGroup p Y₀)
    {v : G} (hv2 : v * v = 1) (hvN : v ∈ Subgroup.normalizer (Y₀ : Set G))
    (hvC : v ∉ Subgroup.centralizer (Y₀ : Set G)) :
    ∃ y ∈ Y₀, y ≠ 1 ∧ y ^ p = 1 ∧ v * y * v⁻¹ = y⁻¹ := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  obtain ⟨w, hwY, hw⟩ : ∃ w ∈ Y₀, w * v ≠ v * w := by
    by_contra hall
    push Not at hall
    exact hvC (Subgroup.mem_centralizer_iff.2 hall)
  have hvw : v * w * v⁻¹ ∈ Y₀ := (Subgroup.mem_normalizer_iff.1 hvN w).1 hwY
  set y₀ := v * w * v⁻¹ * w⁻¹ with hy₀def
  have hy₀Y : y₀ ∈ Y₀ := Y₀.mul_mem hvw (Y₀.inv_mem hwY)
  have hy₀1 : y₀ ≠ 1 := by
    intro h1
    apply hw
    have h2 : v * w * v⁻¹ = w := by
      rw [hy₀def, mul_inv_eq_one] at h1
      exact h1
    calc w * v = (v * w * v⁻¹) * v := by rw [h2]
      _ = v * w := by group
  have hy₀inv : v * y₀ * v⁻¹ = y₀⁻¹ := by
    rw [hy₀def, hvi]
    calc v * (v * w * v * w⁻¹) * v = (v * v) * w * v * w⁻¹ * v := by group
      _ = w * v * w⁻¹ * v := by rw [hv2, one_mul]
      _ = (v * w * v * w⁻¹)⁻¹ := by
        rw [show (v * w * v * w⁻¹)⁻¹ = w * v⁻¹ * w⁻¹ * v⁻¹ by group, hvi]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hY₀) ⟨y₀, hy₀Y⟩
  have hk' : orderOf y₀ = p ^ k := (Subgroup.orderOf_coe (⟨y₀, hy₀Y⟩ : Y₀)).trans hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk'
    exact hy₀1 hk'
  have hpdvd : p ∣ Nat.card (Subgroup.zpowers y₀) := by
    rw [Nat.card_zpowers, hk']
    exact dvd_pow_self p hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers y₀) p hpdvd
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 y.2
  have hyo : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe]; exact hy
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · rw [← hm]
    exact Y₀.zpow_mem hy₀Y m
  · intro h1
    rw [h1, orderOf_one] at hyo
    exact hp.out.one_lt.ne hyo
  · rw [← hyo]
    exact pow_orderOf_eq_one _
  · rw [← hm]
    have h1 : (MulAut.conj v) (y₀ ^ m) = ((MulAut.conj v) y₀) ^ m := map_zpow _ y₀ m
    simp only [MulAut.conj_apply] at h1
    rw [h1, hy₀inv, inv_zpow]

theorem mQuot_inf_centralizer_le_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {V Y : Subgroup G} (hV : IsElemAbelian 2 V) (hY : IsPGroup p Y)
    (hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hVY : V ≤ Subgroup.normalizer (Y : Set G))
    (hrk : CFSG.Open.pRank p Y ≤ 2) :
    E3.mQuot V (V ⊓ Subgroup.centralizer (Y : Set G)) ≤ 2 := by
  by_contra hgt
  push Not at hgt
  set K := V ⊓ Subgroup.centralizer (Y : Set G) with hKdef
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV ha hb
  have hYodd : Odd (Nat.card Y) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1 hY
    rw [hn]
    exact (hp.out.odd_of_ne_two hp2).pow
  have hV1 : V ≠ ⊥ := by
    rintro rfl
    have : K = ⊥ := le_bot_iff.1 inf_le_left
    rw [this, E3.mQuot_self] at hgt
    omega
  have hgen := E3.le_iSup_hyperplane_inf_centralizer hYodd hV hV1 hVY
  let Good : Subgroup G → Prop := fun S =>
    V ≤ Subgroup.centralizer ((Y ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G)
  have hkey : ∀ D : Subgroup G, D ≤ V →
      (∀ S, S ≤ V → Nat.card V = 2 * Nat.card S → ¬ Good S → D ≤ S) → D ≤ K := by
    intro D hDV hD
    refine le_inf hDV (Subgroup.le_centralizer_iff.1 ?_)
    refine hgen.trans (iSup₂_le fun S hS => ?_)
    by_cases hG : Good S
    · exact (Subgroup.le_centralizer_iff.1 hG).trans (Subgroup.centralizer_le hDV)
    · exact inf_le_right.trans (Subgroup.centralizer_le (hD S hS.1 hS.2 hG))
  have hmQ : ∀ D : Subgroup G, D ≤ K → E3.mQuot V K ≤ E3.mQuot V D := fun D hD =>
    E3.mQuot_mono hD
  obtain ⟨S₁, hS₁V, hS₁c, hG₁⟩ : ∃ S, S ≤ V ∧ Nat.card V = 2 * Nat.card S ∧ ¬ Good S := by
    by_contra hall
    push Not at hall
    have h1 := hmQ V (hkey V le_rfl fun S hS hc hG => absurd (hall S hS hc) hG)
    rw [E3.mQuot_self] at h1
    omega
  have hS₁1 : E3.mQuot V S₁ = 1 := mQuot_eq_one_of_card hS₁V hS₁c
  obtain ⟨S₂, hS₂V, hS₂c, hG₂, hne⟩ :
      ∃ S, S ≤ V ∧ Nat.card V = 2 * Nat.card S ∧ ¬ Good S ∧ S ≠ S₁ := by
    by_contra hall
    push Not at hall
    have h1 := hmQ S₁ (hkey S₁ hS₁V fun S hS hc hG => (hall S hS hc hG) ▸ le_rfl)
    omega
  have hS₂1 : E3.mQuot V S₂ = 1 := mQuot_eq_one_of_card hS₂V hS₂c
  obtain ⟨S₃, hS₃V, hS₃c, hG₃, hnot⟩ :
      ∃ S, S ≤ V ∧ Nat.card V = 2 * Nat.card S ∧ ¬ Good S ∧ ¬ S₁ ⊓ S₂ ≤ S := by
    by_contra hall
    push Not at hall
    have h1 := hmQ (S₁ ⊓ S₂) (hkey (S₁ ⊓ S₂) (inf_le_left.trans hS₁V) fun S hS hc hG =>
      hall S hS hc hG)
    have h2 := mQuot_inf_le (U := S₁) (U' := S₂) hV2
    omega
  have heig : ∀ S, S ≤ V → Nat.card V = 2 * Nat.card S → ¬ Good S →
      ∃ y ∈ Y ⊓ Subgroup.centralizer (S : Set G), y ≠ 1 ∧ y ^ p = 1 ∧
        ∀ v ∈ V, v ∉ S → v * y * v⁻¹ = y⁻¹ := by
    intro S hSV hSc hG
    have hidx : (S.subgroupOf V).index = 2 := by
      have h1 := Subgroup.relIndex_mul_card S V
      rw [inf_eq_left.2 hSV] at h1
      have hpos : 0 < Nat.card S := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans hSc)
    obtain ⟨v₀, hv₀V, hv₀C⟩ : ∃ v ∈ V, v ∉ Subgroup.centralizer
        ((Y ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
      by_contra hall
      push Not at hall
      exact hG hall
    have hY₀ : IsPGroup p ↥(Y ⊓ Subgroup.centralizer (S : Set G)) := hY.to_le inf_le_left
    have hv₀N : v₀ ∈ Subgroup.normalizer
        ((Y ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf hVY (B2F.le_normalizer_centralizer ((Subgroup.le_centralizer_iff.1
        (fun s hs => Subgroup.mem_centralizer_iff.2 fun w hw => hVc _ hw _ (hSV hs))).trans
        (Subgroup.centralizer_le_normalizer _))) hv₀V
    obtain ⟨y, hyY, hy1, hyp, hyinv⟩ :=
      exists_inverted hY₀ (by rw [← sq]; exact hV.2 v₀ hv₀V) hv₀N hv₀C
    have hv₀S : v₀ ∉ S := fun hv₀S => hv₀C (Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hw.2 v₀ hv₀S).symm)
    refine ⟨y, hyY, hy1, hyp, fun v hvV hvS => ?_⟩
    have hs : v₀⁻¹ * v ∈ S := by
      have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨v₀⁻¹, V.inv_mem hv₀V⟩)
        (b := ⟨v, hvV⟩)
      have hv₀S' : (⟨v₀⁻¹, V.inv_mem hv₀V⟩ : V) ∉ S.subgroupOf V := fun h =>
        hv₀S (by simpa using S.inv_mem h)
      exact key.2 (iff_of_false hv₀S' (fun h => hvS h))
    have hys : (v₀⁻¹ * v) * y = y * (v₀⁻¹ * v) := Subgroup.mem_centralizer_iff.1 hyY.2 _ hs
    calc v * y * v⁻¹ = v₀ * ((v₀⁻¹ * v) * y) * (v₀⁻¹ * v)⁻¹ * v₀⁻¹ := by group
      _ = v₀ * (y * (v₀⁻¹ * v)) * (v₀⁻¹ * v)⁻¹ * v₀⁻¹ := by rw [hys]
      _ = v₀ * y * v₀⁻¹ := by group
      _ = y⁻¹ := hyinv
  obtain ⟨y₁, hy₁, hy₁1, hy₁p, -⟩ := heig S₁ hS₁V hS₁c hG₁
  obtain ⟨y₂, hy₂, hy₂1, hy₂p, hy₂inv⟩ := heig S₂ hS₂V hS₂c hG₂
  obtain ⟨y₃, hy₃, hy₃1, hy₃p, hy₃inv⟩ := heig S₃ hS₃V hS₃c hG₃
  obtain ⟨e₂, he₂S₁, he₂S₂⟩ : ∃ e ∈ S₁, e ∉ S₂ := by
    by_contra hall
    push Not at hall
    apply hne
    exact (Subgroup.eq_of_le_of_card_ge hall (by omega)).symm
  obtain ⟨e₃, he₃S, he₃S₃⟩ : ∃ e ∈ S₁ ⊓ S₂, e ∉ S₃ := by
    by_contra hall
    push Not at hall
    exact hnot hall
  have hcen : ∀ {S : Subgroup G} {y e : G}, y ∈ Y ⊓ Subgroup.centralizer (S : Set G) → e ∈ S →
      e * y = y * e := fun hy he => (Subgroup.mem_centralizer_iff.1 hy.2 _ he)
  have h3 := three_le_pRank_of_inverted hp2 hYab hy₁.1 hy₂.1 hy₃.1 hy₁p hy₂p hy₃p hy₁1 hy₂1 hy₃1
    (hcen hy₁ he₂S₁) (hy₂inv e₂ (hS₁V he₂S₁) he₂S₂) (hcen hy₁ he₃S.1) (hcen hy₂ he₃S.2)
    (hy₃inv e₃ (hS₁V he₃S.1) he₃S₃)
  omega

end Rank

end E6

end CFSG.Quasithin
