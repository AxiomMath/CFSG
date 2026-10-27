module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Sub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E217R4

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_pow_mem {X Y : Subgroup G} (hYX : Y ≤ X) (hY : (Y.subgroupOf X).Normal)
    [Group.IsSolvable ↥Y] {p : ℕ} [Fact p.Prime] (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ Y) :
    Group.IsSolvable ↥X := by
  have hq : IsPGroup p (↥X ⧸ Y.subgroupOf X) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 (by simpa [Subgroup.mem_subgroupOf] using hk)
  have : Group.IsNilpotent (↥X ⧸ Y.subgroupOf X) := hq.isNilpotent
  have : Group.IsSolvable ↥(Y.subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYX).injective
  refine Group.isSolvable_of_ker_le_range (Y.subgroupOf X).subtype
    (QuotientGroup.mk' (Y.subgroupOf X)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

omit [Finite G] in
theorem mem_of_pow_nine_mem {X Q : Subgroup G} (hX : IsPGroup 2 X) {b : G} (hb : b ∈ X)
    (h9 : b ^ 9 ∈ Q) : b ∈ Q := by
  obtain ⟨k, hk⟩ := hX ⟨b, hb⟩
  have h2 : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hco : Nat.Coprime 9 (orderOf b) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h2) hcop
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
  rw [← hm]
  exact Subgroup.pow_mem _ h9 m

omit [Finite G] in
theorem exists_pow_mul {B : Subgroup G} {b t : G} (hb : b ∈ B)
    (ht : t ∈ Subgroup.normalizer (B : Set G)) (n : ℕ) : ∃ b' ∈ B, (b * t) ^ n = b' * t ^ n := by
  induction n with
  | zero => exact ⟨1, B.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨b', hb', h⟩ := ih
    have htn : t ^ n ∈ Subgroup.normalizer (B : Set G) := Subgroup.pow_mem _ ht n
    refine ⟨b' * (t ^ n * b * (t ^ n)⁻¹),
      B.mul_mem hb' ((Subgroup.mem_normalizer_iff.1 htn b).1 hb), ?_⟩
    rw [pow_succ, h]
    group

theorem false_of_lifted {H T M V B T₀ : Subgroup G} (h : E2.Hyp28 H T M V) (hchar : CharTwo H)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI h.elem H)) (hV16 : Nat.card V = 2 ^ 4)
    (hQB : pCoreOf 2 H ≤ B) (hBH : B ≤ H) (hidx : (pCoreOf 2 H).relIndex B = 9)
    (hB9 : ∀ b ∈ B, b ^ 9 ∈ pCoreOf 2 H) (hQT₀ : pCoreOf 2 H ≤ T₀) (hT₀T : T₀ ≤ T)
    (hT₀B : T₀ ≤ Subgroup.normalizer (B : Set G))
    (hirr : ∀ C : Subgroup G, pCoreOf 2 H ≤ C → C ≤ B → T₀ ≤ Subgroup.normalizer (C : Set G) →
      C = pCoreOf 2 H ∨ C = B)
    (hVT₀ : V ≤ T₀) {v : G} (hv : v ∈ V)
    (hinv : ∀ b ∈ B, v * b * v⁻¹ * b ∈ pCoreOf 2 H) : False := by
  set Q := pCoreOf 2 H with hQ
  set H₀ := B ⊔ T₀ with hH₀
  have hT2 : IsPGroup 2 T := h.minParabolic.isSylow.2.1
  have hQH : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hT₀H : T₀ ≤ H := hT₀T.trans h.minParabolic.isSylow.1
  have hH₀H : H₀ ≤ H := sup_le hBH hT₀H
  have hBH₀ : B ≤ H₀ := le_sup_left
  have hH₀mem : ∀ x ∈ H₀, ∃ b ∈ B, ∃ t ∈ T₀, b * t = x := by
    intro x hx
    have hx' : x ∈ (↑(B ⊔ T₀) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left B T₀ hT₀B] at hx'
    obtain ⟨b, hb, t, ht, rfl⟩ := hx'
    exact ⟨b, hb, t, ht, rfl⟩
  have hBT : ∀ b ∈ B, b ∈ T → b ∈ Q := fun b hb hbT =>
    mem_of_pow_nine_mem hT2 hbT (hB9 b hb)
  have hTH₀ : T ⊓ H₀ = T₀ := by
    refine le_antisymm ?_ (le_inf hT₀T le_sup_right)
    rintro x ⟨hxT, hxH₀⟩
    obtain ⟨b, hb, t, ht, rfl⟩ := hH₀mem x hxH₀
    have hbT : b ∈ T := by
      have : b = (b * t) * t⁻¹ := by group
      rw [this]
      exact T.mul_mem hxT (T.inv_mem (hT₀T ht))
    exact T₀.mul_mem (hQT₀ (hBT b hb hbT)) ht
  have hmax : ∀ Y : Subgroup G, T₀ ≤ Y → Y < H₀ → Y ≤ T₀ := by
    intro Y hTY hYH₀
    have hC : Y ⊓ B = Q ∨ Y ⊓ B = B := by
      refine hirr (Y ⊓ B) (le_inf (hQT₀.trans hTY) hQB) inf_le_right ?_
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxY, hxB⟩
        exact ⟨Y.mul_mem (Y.mul_mem (hTY ht) hxY) (Y.inv_mem (hTY ht)),
          (Subgroup.mem_normalizer_iff.1 (hT₀B ht) x).1 hxB⟩
      · rintro ⟨hxY, hxB⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.1 (hT₀B ht) x).2 hxB⟩
        have := Y.mul_mem (Y.mul_mem (Y.inv_mem (hTY ht)) hxY) (hTY ht)
        simpa [mul_assoc] using this
    rcases hC with hC | hC
    · intro y hy
      obtain ⟨b, hb, t, ht, rfl⟩ := hH₀mem y (hYH₀.le hy)
      have hbY : b ∈ Y := by
        have : b = (b * t) * t⁻¹ := by group
        rw [this]
        exact Y.mul_mem hy (Y.inv_mem (hTY ht))
      have hbQ : b ∈ Q := hC ▸ (⟨hbY, hb⟩ : b ∈ Y ⊓ B)
      exact T₀.mul_mem (hQT₀ hbQ) ht
    · exfalso
      have hBY : B ≤ Y := by
        rw [← hC]
        exact inf_le_left
      exact absurd (sup_le hBY hTY) (not_le_of_gt hYH₀)
  have hT₀2 : IsPGroup 2 T₀ := hT2.to_le hT₀T
  have hT₀H₀ : T₀ ≤ H₀ := le_sup_right
  obtain ⟨a₀, ha₀, ha₀Q⟩ : ∃ a ∈ B, a ∉ Q := by
    refine IsConcreteLE.not_le_iff_exists.1 fun hBQ => ?_
    have := Subgroup.relIndex_eq_one.2 hBQ
    omega
  have hsyl : IsSylowTwoOf T₀ H₀ := by
    obtain ⟨P, hP, hTP⟩ := A4.exists_isSylowTwoOf_ge hT₀H₀ hT₀2
    by_cases hPH : P = H₀
    · exfalso
      have hH2 : IsPGroup 2 H₀ := hPH ▸ hP.2.1
      exact ha₀Q (mem_of_pow_nine_mem hH2 (hBH₀ ha₀) (hB9 a₀ ha₀))
    · have hle := hmax P hTP (lt_of_le_of_ne hP.1 hPH)
      rwa [le_antisymm hle hTP] at hP
  have hconj : ∀ a ∈ B, a ∉ Q → a * v * a⁻¹ ∈ T₀ → False := by
    intro a ha haQ hav
    have hvT₀ : v ∈ T₀ := hVT₀ hv
    have hqQ : v * a⁻¹ * v⁻¹ * a⁻¹ ∈ Q := hinv a⁻¹ (B.inv_mem ha)
    have hc : a * (v * a⁻¹ * v⁻¹ * a⁻¹) * a = (a * v * a⁻¹) * v⁻¹ := by group
    have h1 : a * (v * a⁻¹ * v⁻¹ * a⁻¹) * a ∈ T₀ := by
      rw [hc]
      exact T₀.mul_mem hav (T₀.inv_mem hvT₀)
    have h2 : a * (v * a⁻¹ * v⁻¹ * a⁻¹) * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 (hQH (hBH ha)) _).1 hqQ
    have h3 : a ^ 2 = (a * (v * a⁻¹ * v⁻¹ * a⁻¹) * a⁻¹)⁻¹ * (a * (v * a⁻¹ * v⁻¹ * a⁻¹) * a) := by
      group
    have h4 : a ^ 2 ∈ T₀ := by
      rw [h3]
      exact T₀.mul_mem (T₀.inv_mem (hQT₀ h2)) h1
    have h5 : a ^ 2 ∈ Q := hBT (a ^ 2) (B.pow_mem ha 2) (hT₀T h4)
    have h6 : a = a ^ 9 * ((a ^ 2) ^ 4)⁻¹ := by group
    apply haQ
    rw [h6]
    exact Q.mul_mem (hB9 a ha) (Q.inv_mem (Subgroup.pow_mem _ h5 4))
  have hnn : ¬ H₀ ≤ Subgroup.normalizer (T₀ : Set G) := by
    intro hN
    exact hconj a₀ ha₀ ha₀Q
      ((Subgroup.mem_normalizer_iff.1 (hN (hBH₀ ha₀)) v).1 (hVT₀ hv))
  have hker : ¬ V ≤ kerIn T₀ H₀ := by
    intro hVk
    exact hconj a₀ ha₀ ha₀Q (hVk hv a₀ (hBH₀ ha₀))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQsolv : Group.IsSolvable ↥Q := by
    have := (pCoreOf_isPGroup 2 H).isNilpotent
    infer_instance
  have hBsolv : Group.IsSolvable ↥B := by
    refine isSolvable_of_pow_mem (Y := Q) (p := 3) hQB
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQB).2 (hBH.trans hQH)) ?_
    intro x hx
    exact ⟨2, by simpa using hB9 x hx⟩
  have hH₀N : H₀ ≤ Subgroup.normalizer (B : Set G) := sup_le Subgroup.le_normalizer hT₀B
  have hsolv : Group.IsSolvable ↥H₀ := by
    refine isSolvable_of_pow_mem (Y := B) (p := 2) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hH₀N) ?_
    intro x hx
    obtain ⟨b, hb, t, ht, rfl⟩ := hH₀mem x hx
    obtain ⟨k, hk⟩ := hT₀2 ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨b', hb', h⟩ := exists_pow_mul hb (hT₀B ht) (2 ^ k)
    refine ⟨k, ?_⟩
    rw [h, htk, mul_one]
    exact hb'
  refine false_of_subparabolic h hchar hq hV16 (hQB.trans le_sup_left) hH₀H
    (hVT₀.trans le_sup_right) ?_ ?_ ?_ ?_ hsolv hBH₀ hidx hB9 hv hinv
  · rw [hTH₀]
    exact hsyl
  · rw [hTH₀]
    exact hnn
  · rw [hTH₀]
    exact hmax
  · rw [hTH₀]
    exact hker

end E217R4

end CFSG.Quasithin
