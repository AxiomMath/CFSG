module

public import CFSG.Quasithin.Background.C1PackBasic
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S14110

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_block_of_mem_pCoreOf {H B : Subgroup G} (hB : IsBlock2 H B) {y k : G}
    (hy : y ∈ pCoreOf 2 H) (hk : k ∈ B) : y * k * y⁻¹ ∈ B := by
  have hN := (isBlock2_normal_sup_pCore hB).2
  have h := hN.conj_mem ⟨k, Subgroup.mem_sup_left hk⟩ (Subgroup.mem_subgroupOf.2 hk)
    ⟨y, Subgroup.mem_sup_right hy⟩
  simpa [Subgroup.mem_subgroupOf] using h

theorem commutator_mem_pCoreOf_block {H B : Subgroup G} (hB : IsBlock2 H B) {y k : G}
    (hy : y ∈ pCoreOf 2 H) (hk : k ∈ B) : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 B := by
  have h1 : y * k * y⁻¹ * k⁻¹ ∈ B :=
    B.mul_mem (conj_mem_block_of_mem_pCoreOf hB hy hk) (B.inv_mem hk)
  have h2 : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    have hkN : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (hB.2.1 hk)
    have h3 : k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.1 hkN y⁻¹).1 ((pCoreOf 2 H).inv_mem hy)
    have h4 : y * k * y⁻¹ * k⁻¹ = y * (k * y⁻¹ * k⁻¹) := by group
    rw [h4]
    exact (pCoreOf 2 H).mul_mem hy h3
  have h5 : y * k * y⁻¹ * k⁻¹ ∈ blockQ B := by
    rw [blockQ_eq_inf_pCoreOf hB]
    exact ⟨h1, h2⟩
  exact h5

theorem a4Data_eq_of_invariant {X W D : Subgroup G} {c : G} (h : A4Data X W c) (hDW : D ≤ W)
    (hD1 : D ≠ ⊥) (hc : ∀ d ∈ D, c * d * c⁻¹ ∈ D) : D = W := by
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
  have hd1' : d ≠ 1 := fun h' => hd1 (Subtype.ext h')
  have hdW : d ∈ W := hDW hdD
  have he : c * d * c⁻¹ ∈ D := hc d hdD
  have hed : c * d * c⁻¹ ≠ d := h.fpf d hdW hd1'
  have he1 : c * d * c⁻¹ ≠ 1 := fun h' => hd1' (by simpa using h')
  have h3 : 3 ≤ Nat.card D := by
    let f : Fin 3 → D := ![1, ⟨d, hdD⟩, ⟨c * d * c⁻¹, he⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢
      all_goals first | exact hd1' hij.symm | exact hd1' hij | exact he1 hij.symm | exact he1 hij |
        exact hed hij.symm | exact hed hij
    calc 3 = Nat.card (Fin 3) := by simp
      _ ≤ Nat.card D := Nat.card_le_card_of_injective f hf
  have hdvd : Nat.card D ∣ Nat.card W := Subgroup.card_dvd_of_le hDW
  rw [h.card_W] at hdvd
  have hle : Nat.card D ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have h4 : Nat.card D = 4 := by
    have : Nat.card D = 3 ∨ Nat.card D = 4 := by omega
    rcases this with h3' | h4'
    · rw [h3'] at hdvd
      norm_num at hdvd
    · exact h4'
  exact Subgroup.eq_of_le_of_card_ge hDW (by rw [h.card_W, h4])

omit [Finite G] in
theorem eq_of_odd_order_stable {a : G} {Y V : Subgroup G} (hodd : Odd (orderOf a))
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (haV : ∀ v ∈ V, a * v * a⁻¹ = v)
    (hY : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ ∈ V) : ∀ y ∈ Y, a * y * a⁻¹ = y := by
  intro y hy
  have hvV : a * y * a⁻¹ * y⁻¹ ∈ V := hY y hy
  set v := a * y * a⁻¹ * y⁻¹ with hv
  have hay : a * y * a⁻¹ = v * y := by rw [hv]; group
  have hav : a * v * a⁻¹ = v := haV v hvV
  have hiter : ∀ n : ℕ, a ^ n * y * (a ^ n)⁻¹ = v ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : a ^ (n + 1) * y * (a ^ (n + 1))⁻¹ = a * (a ^ n * y * (a ^ n)⁻¹) * a⁻¹ := by
        group
      rw [h1, ih]
      have h2 : a * (v ^ n * y) * a⁻¹ = (a * v ^ n * a⁻¹) * (a * y * a⁻¹) := by group
      have h3 : a * v ^ n * a⁻¹ = v ^ n := by rw [← conj_pow, hav]
      rw [h2, h3, hay]
      group
  have h1 := hiter (orderOf a)
  rw [pow_orderOf_eq_one a] at h1
  have hvm : v ^ orderOf a = 1 := by
    have h2 : v ^ orderOf a * y = y := by simpa using h1.symm
    simpa using h2
  obtain ⟨j, hj⟩ := hodd
  have hv2 : v ^ 2 = 1 := hV2 v hvV
  have hv1 : v = 1 := by
    have h5 : v ^ (2 * j + 1) = v := by rw [pow_succ, pow_mul, hv2, one_pow, one_mul]
    rw [← h5, ← hj]
    exact hvm
  rw [hay, hv1, one_mul]

theorem centralizerSection_le_pCoreOf {X V : Subgroup G} (hX : CharTwo X)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hXN : X ≤ Subgroup.normalizer (V : Set G)) :
    centralizerSection (X ⊓ Subgroup.centralizer (V : Set G)) (pCoreOf 2 X) V ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := centralizerSection (X ⊓ Subgroup.centralizer (V : Set G)) (pCoreOf 2 X) V with hA
  have hAX : A ≤ X := fun a ha => ha.1.1
  have hnormA : X ≤ Subgroup.normalizer (A : Set G) := by
    intro g hg
    have hgM : g ∈ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        B6.le_normalizer_centralizer hXN hg⟩
    have hgX : g ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hg
    have hgZ : g ∈ Subgroup.normalizer (V : Set G) := hXN hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_centralizerSection hgM hgX hgZ hx, fun hx => ?_⟩
    have := conj_mem_centralizerSection (Subgroup.inv_mem _ hgM) (Subgroup.inv_mem _ hgX)
      (Subgroup.inv_mem _ hgZ) hx
    simpa [mul_assoc] using this
  have hpow : ∀ a : A, ∃ n : ℕ, a ^ 2 ^ n = 1 := by
    intro a
    obtain ⟨i, m, hm, hmi⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (a : G)).ne'
    have hbA : (a : G) ^ 2 ^ i ∈ A := A.pow_mem a.2 _
    have hord : orderOf ((a : G) ^ 2 ^ i) = m := by
      have hdvd : 2 ^ i ∣ orderOf (a : G) := by rw [hmi]; exact dvd_mul_right _ _
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hmi]
      exact Nat.mul_div_cancel_left m (by positivity)
    have hbC : ∀ v ∈ V, (a : G) ^ 2 ^ i * v * ((a : G) ^ 2 ^ i)⁻¹ = v := by
      intro v hv
      have := Subgroup.mem_centralizer_iff.1 hbA.1.2 v hv
      rw [← this]
      group
    have hbY : ∀ y ∈ pCoreOf 2 X, (a : G) ^ 2 ^ i * y * ((a : G) ^ 2 ^ i)⁻¹ * y⁻¹ ∈ V := by
      intro y hy
      have h1 := hbA.2.2.2 y hy
      have h2 := V.inv_mem h1
      have : ((a : G) ^ 2 ^ i * y * ((a : G) ^ 2 ^ i)⁻¹ * y⁻¹) =
          (y * (a : G) ^ 2 ^ i * y⁻¹ * ((a : G) ^ 2 ^ i)⁻¹)⁻¹ := by group
      rw [this]
      exact h2
    have hoddb : Odd (orderOf ((a : G) ^ 2 ^ i)) := by rw [hord]; exact hm
    have hcen := eq_of_odd_order_stable hoddb hV2 hbC hbY
    have hbY' : (a : G) ^ 2 ^ i ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) :=
      ⟨hbA.1.1, Subgroup.mem_centralizer_iff.2 fun y hy => by
        have := hcen y hy
        calc y * (a : G) ^ 2 ^ i = ((a : G) ^ 2 ^ i * y * ((a : G) ^ 2 ^ i)⁻¹) * (a : G) ^ 2 ^ i := by
              rw [this]
          _ = (a : G) ^ 2 ^ i * y := by group⟩
    have hbQ : (a : G) ^ 2 ^ i ∈ pCoreOf 2 X := hX hbY'
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨(a : G) ^ 2 ^ i, hbQ⟩
    have hj' : ((a : G) ^ 2 ^ i) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hcop : Nat.Coprime m (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm)
    have hdvd : m ∣ 2 ^ j := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hj'
    have hm1 : m = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    refine ⟨i, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact orderOf_eq_one_iff.1 (hord.trans hm1)
  have hPG : IsPGroup 2 A := hpow
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAX hnormA hPG

end CFSG.Quasithin.C1Pack
