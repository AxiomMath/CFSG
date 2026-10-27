module

public import Mathlib.GroupTheory.Transfer
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res8Hess

open scoped Pointwise

variable {M : Type*} [Group M]

@[expose] def conjOn {E Y : Subgroup M} (h : E ≤ Subgroup.normalizer (Y : Set M)) :
    ↥E →* MulAut ↥Y :=
  Y.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem orderOf_conj_eq (y x : M) : orderOf (y * x * y⁻¹) = orderOf x := by
  simpa only [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj y) x

theorem le_normalizer_inf' {A X Y : Subgroup M} (hX : A ≤ Subgroup.normalizer (X : Set M))
    (hY : A ≤ Subgroup.normalizer (Y : Set M)) :
    A ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup M) : Set M) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hX ha) h,
    Subgroup.mem_normalizer_iff.mp (hY ha) h]

theorem coprime_orderOf_of_mem [Finite M] {U : Subgroup M} (hU3 : ¬ 3 ∣ Nat.card U) {x : M}
    (hx : x ∈ U) : Nat.Coprime 3 (orderOf x) := by
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => hU3 (h.trans ?_)
  have := orderOf_dvd_natCard (⟨x, hx⟩ : U)
  rwa [Subgroup.orderOf_mk] at this

theorem map_sylow_ne_bot [Finite M] {Y : Subgroup M} {r : ℕ} [Fact r.Prime] (S : Sylow r ↥Y)
    (hrY : r ∣ Nat.card Y) : (S : Subgroup Y).map Y.subtype ≠ ⊥ := by
  intro h
  have h1 : Nat.card ((S : Subgroup Y).map Y.subtype) = Nat.card S :=
    Subgroup.card_map_of_injective Y.subtype_injective
  rw [h, Subgroup.card_bot, S.card_eq_multiplicity] at h1
  have hk : (Nat.card Y).factorization r ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hrY).ne'
  have hr1 : r ≠ 1 := (Fact.out : r.Prime).one_lt.ne'
  rcases Nat.pow_eq_one.mp h1.symm with h2 | h2
  · exact hr1 h2
  · exact hk h2

variable [Finite M]

theorem exists_invariant_sylow {E Y : Subgroup M} (hE : IsPGroup 3 E) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set M)) (r : ℕ) [Fact r.Prime] :
    ∃ S : Sylow r ↥Y,
      E ≤ Subgroup.normalizer ((((S : Subgroup Y).map Y.subtype : Subgroup M)) : Set M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 r hE
    hY3 (conjOn hEY)
  refine ⟨S, fun e he => Subgroup.mem_normalizer_fintype fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : conjOn hEY ⟨e, he⟩ y ∈ (S : Subgroup Y) := by
    rw [← hS ⟨e, he⟩]
    exact ⟨y, hy, rfl⟩
  exact ⟨_, h1, rfl⟩

theorem exists_normal_complement {Y : Subgroup M} {r : ℕ} [Fact r.Prime] (S : Sylow r ↥Y)
    (hcomm : ∀ x ∈ Y,
      x ∈ Subgroup.normalizer ((((S : Subgroup Y).map Y.subtype : Subgroup M)) : Set M) →
        ∀ s ∈ (S : Subgroup Y).map Y.subtype, x * s = s * x) :
    ∃ N : Subgroup M, (∀ x, x ∈ N ↔ x ∈ Y ∧ Nat.Coprime r (orderOf x)) ∧
      Nat.card N * Nat.card S = Nat.card Y := by
  have hr : r.Prime := Fact.out
  have hP : Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤
      Subgroup.centralizer ((S : Subgroup Y) : Set Y) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hn' : (n : M) ∈
        Subgroup.normalizer ((((S : Subgroup Y).map Y.subtype : Subgroup M)) : Set M) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨n * y * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn y).mp hy, rfl⟩
    exact Subtype.ext (hcomm n n.2 hn' s ⟨s, hs, rfl⟩).symm
  set τ := MonoidHom.transferSylow S hP with hτ
  refine ⟨τ.ker.map Y.subtype, fun x => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 : orderOf y ∣ Nat.card τ.ker := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : τ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have h2 := MonoidHom.not_dvd_card_ker_transferSylow S hP
    change r.Coprime (orderOf (y : M))
    rw [Subgroup.orderOf_coe]
    exact (Nat.Prime.coprime_iff_not_dvd hr).mpr fun h => h2 (h.trans h1)
  · rintro ⟨hxY, hx⟩
    refine ⟨⟨x, hxY⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    obtain ⟨k, hk⟩ := S.isPGroup' (τ ⟨x, hxY⟩)
    have h1 : orderOf (τ ⟨x, hxY⟩) ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf (τ ⟨x, hxY⟩) ∣ orderOf x := by
      rw [← Subgroup.orderOf_mk x hxY]
      exact orderOf_map_dvd τ _
    have hcop : Nat.Coprime (r ^ k) (orderOf x) := Nat.Coprime.pow_left k hx
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  · rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact (MonoidHom.ker_transferSylow_isComplement' S hP).card_mul_card

theorem le_sup_inf_normalizer {Y N : Subgroup M} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set M)) {s : ℕ} [Fact s.Prime] (S : Sylow s ↥N) :
    Y ≤ N ⊔ (Y ⊓ Subgroup.normalizer
      ((((S : Subgroup N).map N.subtype : Subgroup M)) : Set M)) := by
  intro y hy
  set σ := N.normalizerMonoidHom ⟨y, hYN hy⟩ with hσ
  have hσx : ∀ x : N, ((σ x : N) : M) = y * x * y⁻¹ := fun x => rfl
  set T : Subgroup N := (S : Subgroup N).map σ.toMonoidHom with hT
  have hσinj : Function.Injective σ.toMonoidHom := σ.injective
  have hTc : Nat.card T = s ^ (Nat.card N).factorization s := by
    rw [hT, Subgroup.card_map_of_injective hσinj, S.card_eq_multiplicity]
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥N) (Sylow.ofCard T hTc) S
  have key : (m : M) * y ∈
      Subgroup.normalizer ((((S : Subgroup N).map N.subtype : Subgroup M)) : Set M) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨x', hx', rfl⟩ := hx
    have h1 : m * σ x' * m⁻¹ ∈ ((m • Sylow.ofCard T hTc : Sylow s N) : Subgroup N) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨σ x', ⟨x', hx', rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hm] at h1
    refine ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hσx]
    group
  have hmy : (m : M) * y ∈ Y := Y.mul_mem (hNY m.2) hy
  have e : y = (m : M)⁻¹ * ((m : M) * y) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (inv_mem m.2) ⟨hmy, key⟩

theorem exists_le_of_family {E : Subgroup M} (hE3 : IsPGroup 3 E) (Θ : M → Subgroup M)
    (hne : ∃ b ∈ E, b ≠ 1)
    (hab : ∀ b ∈ E, b ≠ 1 → ∀ x ∈ Θ b, ∀ y ∈ Θ b, x * y = y * x)
    (ha : ∀ (r : ℕ) [Fact r.Prime], r ≠ 3 → ∀ R : Subgroup M, IsPGroup r R → R ≠ ⊥ →
      E ≤ Subgroup.normalizer (R : Set M) →
      ∃ b ∈ E, b ≠ 1 ∧
        (∀ x ∈ Subgroup.centralizer (R : Set M), Nat.Coprime 3 (orderOf x) → x ∈ Θ b) ∧
        ∀ U : Subgroup M, U ≤ Subgroup.normalizer (R : Set M) → ¬ 3 ∣ Nat.card U →
          E ≤ Subgroup.normalizer (U : Set M) → U ≤ Θ b) :
    ∀ Y : Subgroup M, ¬ 3 ∣ Nat.card Y → E ≤ Subgroup.normalizer (Y : Set M) →
      ∃ b ∈ E, b ≠ 1 ∧ Y ≤ Θ b := by
  intro Y
  induction hn : Nat.card Y using Nat.strong_induction_on generalizing Y with
  | _ n ih =>
  intro hY3 hEY
  subst hn
  obtain ⟨b₀, hb₀E, hb₀1⟩ := hne
  by_cases hY : Y = ⊥
  · exact ⟨b₀, hb₀E, hb₀1, hY ▸ bot_le⟩
  have hY1 : Nat.card Y ≠ 1 := fun h => hY (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hr, hrY⟩ := Nat.exists_prime_and_dvd hY1
  have : Fact r.Prime := ⟨hr⟩
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact hY3 hrY
  obtain ⟨S, hSE⟩ := exists_invariant_sylow hE3 hY3 hEY r
  set R : Subgroup M := (S : Subgroup Y).map Y.subtype with hR
  have hRY : R ≤ Y := Subgroup.map_subtype_le _
  have hRr : IsPGroup r R := S.isPGroup'.map _
  have hRcard : Nat.card R = Nat.card S := Subgroup.card_map_of_injective Y.subtype_injective
  have hR1 : R ≠ ⊥ := map_sylow_ne_bot S hrY
  obtain ⟨b, hbE, hb1, -, hRn⟩ := ha r hr3 R hRr hR1 hSE
  have hNYE : E ≤ Subgroup.normalizer
      ((Y ⊓ Subgroup.normalizer (R : Set M) : Subgroup M) : Set M) :=
    le_normalizer_inf' hEY (hSE.trans Subgroup.le_normalizer)
  have hNYR : Y ⊓ Subgroup.normalizer (R : Set M) ≤ Θ b :=
    hRn _ inf_le_right (fun h => hY3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))) hNYE
  have hcomm : ∀ x ∈ Y, x ∈ Subgroup.normalizer (R : Set M) → ∀ s ∈ R, x * s = s * x :=
    fun x hxY hxN s hs => hab b hbE hb1 x (hNYR ⟨hxY, hxN⟩) s
      (hNYR ⟨hRY hs, Subgroup.le_normalizer hs⟩)
  obtain ⟨N, hNmem, hNcard⟩ := exists_normal_complement S hcomm
  have hNY : N ≤ Y := fun x hx => ((hNmem x).mp hx).1
  have hYNN : Y ≤ Subgroup.normalizer (N : Set M) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun x hx => by
      obtain ⟨hxY, hxo⟩ := (hNmem x).mp hx
      exact (hNmem _).mpr ⟨Y.mul_mem (Y.mul_mem hy hxY) (inv_mem hy), by
        rwa [orderOf_conj_eq]⟩
  have hEN : E ≤ Subgroup.normalizer (N : Set M) := fun e he =>
    Subgroup.mem_normalizer_fintype fun x hx => by
      obtain ⟨hxY, hxo⟩ := (hNmem x).mp hx
      exact (hNmem _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hEY he) x).mp hxY, by
        rwa [orderOf_conj_eq]⟩
  have hN3 : ¬ 3 ∣ Nat.card N := fun h => hY3 (h.trans (Subgroup.card_dvd_of_le hNY))
  have hS1 : 1 < Nat.card S := by
    rw [← hRcard]
    exact (Subgroup.one_lt_card_iff_ne_bot R).mpr hR1
  have hNlt : Nat.card N < Nat.card Y := by
    rw [← hNcard]
    exact lt_mul_of_one_lt_right Nat.card_pos hS1
  obtain ⟨b', hb'E, hb'1, hNb'⟩ := ih _ hNlt N rfl hN3 hEN
  have hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy =>
    hab b' hb'E hb'1 x (hNb' hx) y (hNb' hy)
  by_cases hN : N = ⊥
  ·
    have hYR : R = Y := by
      refine Subgroup.eq_of_le_of_card_ge hRY ?_
      rw [← hNcard, hN, Subgroup.card_bot, one_mul, hRcard]
    refine ⟨b, hbE, hb1, fun y hy => hNYR ⟨hy, ?_⟩⟩
    rw [← hYR] at hy
    exact Subgroup.le_normalizer hy
  · have hN1 : Nat.card N ≠ 1 := fun h => hN (Subgroup.card_eq_one.mp h)
    obtain ⟨s, hs, hsN⟩ := Nat.exists_prime_and_dvd hN1
    have : Fact s.Prime := ⟨hs⟩
    have hs3 : s ≠ 3 := by
      rintro rfl
      exact hN3 hsN
    obtain ⟨S', hS'E⟩ := exists_invariant_sylow hE3 hN3 hEN s
    set R' : Subgroup M := (S' : Subgroup N).map N.subtype with hR'
    have hR'N : R' ≤ N := Subgroup.map_subtype_le _
    have hR'r : IsPGroup s R' := S'.isPGroup'.map _
    have hR'1 : R' ≠ ⊥ := map_sylow_ne_bot S' hsN
    obtain ⟨b'', hb''E, hb''1, hR'c, hR'n⟩ := ha s hs3 R' hR'r hR'1 hS'E
    have hNb'' : N ≤ Θ b'' := fun x hx =>
      hR'c x (Subgroup.mem_centralizer_iff.mpr fun y hy => (hNab x hx y (hR'N hy)).symm)
        (coprime_orderOf_of_mem hN3 hx)
    have hY'' : Y ⊓ Subgroup.normalizer (R' : Set M) ≤ Θ b'' :=
      hR'n _ inf_le_right (fun h => hY3 (h.trans (Subgroup.card_dvd_of_le inf_le_left)))
        (le_normalizer_inf' hEY (hS'E.trans Subgroup.le_normalizer))
    exact ⟨b'', hb''E, hb''1, (le_sup_inf_normalizer hNY hYNN S').trans (sup_le hNb'' hY'')⟩

omit [Finite M] in
theorem pow_apply_ne_of_cube' {τ : MulAut M} {a : M} (h3 : (τ ^ 3) a = a) (h1 : τ a ≠ a)
    (h2 : (τ ^ 2) a ≠ a) {n : ℕ} (hn : ¬ 3 ∣ n) : (τ ^ n) a ≠ a := by
  have hk : ∀ m r : ℕ, (τ ^ (3 * m + r)) a = (τ ^ r) a := by
    intro m r
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 3 * (m + 1) + r = 3 + (3 * m + r) by ring, pow_add, MulAut.mul_apply, ih]
      rw [show (τ ^ 3) ((τ ^ r) a) = (τ ^ r) ((τ ^ 3) a) by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm], h3]
  have hn' : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
  have hr : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [hn', hk]
  rcases hr with hr | hr <;> rw [hr]
  · simpa using h1
  · exact h2

omit [Finite M] in
theorem three_dvd_orderOf_of_cycle {u t₁ t₂ t₃ : M} (h1 : u * t₁ * u⁻¹ = t₂)
    (h2 : u * t₂ * u⁻¹ = t₃) (h3 : u * t₃ * u⁻¹ = t₁) (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) :
    3 ∣ orderOf u := by
  by_contra hn
  have hτ1 : MulAut.conj u t₁ = t₂ := by rw [MulAut.conj_apply, h1]
  have hτ2 : (MulAut.conj u ^ 2) t₁ = t₃ := by
    rw [pow_two, MulAut.mul_apply, hτ1, MulAut.conj_apply, h2]
  have hτ3 : (MulAut.conj u ^ 3) t₁ = t₁ := by
    rw [pow_succ', MulAut.mul_apply, hτ2, MulAut.conj_apply, h3]
  have key := pow_apply_ne_of_cube' hτ3 (by rw [hτ1]; exact Ne.symm h12)
    (by rw [hτ2]; exact Ne.symm h13) hn
  apply key
  rw [← map_pow, pow_orderOf_eq_one, map_one, MulAut.one_apply]

omit [Finite M] in
theorem commute_of_perm_three {t₁ t₂ t₃ c : M} {U : Subgroup M} (ht₁ : t₁ * t₁ = 1)
    (ht₂ : t₂ * t₂ = 1) (hc12 : t₁ * t₂ = t₂ * t₁) (h12 : t₁ * t₂ = t₃) (ht₁1 : t₁ ≠ 1)
    (ht₂1 : t₂ ≠ 1) (hne : t₁ ≠ t₂) (hc1 : c * t₁ * c⁻¹ = t₂) (hc2 : c * t₂ * c⁻¹ = t₃)
    (hc3 : c * t₃ * c⁻¹ = t₁) (hcU : c ∈ Subgroup.normalizer (U : Set M))
    (hU3 : ∀ u ∈ U, ¬ 3 ∣ orderOf u)
    (hperm : ∀ u ∈ U, ∀ t, (t = t₁ ∨ t = t₂ ∨ t = t₃) →
      (u * t * u⁻¹ = t₁ ∨ u * t * u⁻¹ = t₂ ∨ u * t * u⁻¹ = t₃)) :
    ∀ u ∈ U, u * t₁ = t₁ * u ∧ u * t₂ = t₂ * u := by
  have h23 : t₂ * t₃ = t₁ := by
    rw [← h12, hc12, ← mul_assoc, ht₂, one_mul]
  have h13 : t₁ * t₃ = t₂ := by
    rw [← h12, ← mul_assoc, ht₁, one_mul]
  have h31 : t₃ * t₁ = t₂ := by
    rw [← h12, hc12, mul_assoc, ht₁, mul_one]
  have h32 : t₃ * t₂ = t₁ := by
    rw [← h12, mul_assoc, ht₂, mul_one]
  have h21 : t₂ * t₁ = t₃ := by rw [← hc12, h12]
  have hne13 : t₁ ≠ t₃ := by
    intro h
    apply ht₂1
    calc t₂ = t₁ * t₃ := h13.symm
      _ = t₁ * t₁ := by rw [h]
      _ = 1 := ht₁
  have hne23 : t₂ ≠ t₃ := by
    intro h
    apply ht₁1
    calc t₁ = t₂ * t₃ := h23.symm
      _ = t₂ * t₂ := by rw [h]
      _ = 1 := ht₂
  have hmulc : ∀ u a b : M, u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := fun u a b => by
    group
  have hinj : ∀ u a b : M, u * a * u⁻¹ = u * b * u⁻¹ → a = b := fun u a b h => by
    simpa using h
  have hci1 : c⁻¹ * t₂ * c = t₁ := by rw [← hc1]; group
  have hci2 : c⁻¹ * t₃ * c = t₂ := by rw [← hc2]; group
  have hci3 : c⁻¹ * t₁ * c = t₃ := by rw [← hc3]; group
  have hA : ∀ u ∈ U, u * t₁ * u⁻¹ = t₁ ∨ u * t₂ * u⁻¹ = t₂ ∨ u * t₃ * u⁻¹ = t₃ := by
    intro u hu
    by_contra hcon
    push Not at hcon
    obtain ⟨n1, n2, n3⟩ := hcon
    have hu3 := hU3 u hu
    have m1 := hperm u hu t₁ (Or.inl rfl)
    have m2 := hperm u hu t₂ (Or.inr (Or.inl rfl))
    have m3 : u * t₃ * u⁻¹ = (u * t₁ * u⁻¹) * (u * t₂ * u⁻¹) := by rw [← hmulc, h12]
    rcases m1 with e1 | e1 | e1
    · exact n1 e1
    · rcases m2 with e2 | e2 | e2
      · rw [e1, e2, h21] at m3
        exact n3 m3
      · exact n2 e2
      · rw [e1, e2, h23] at m3
        exact hu3 (three_dvd_orderOf_of_cycle e1 e2 m3 hne hne13)
    · rcases m2 with e2 | e2 | e2
      · rw [e1, e2, h31] at m3
        exact hu3 (three_dvd_orderOf_of_cycle e1 m3 e2 hne13 hne)
      · exact n2 e2
      · exact hne (hinj u _ _ (e1.trans e2.symm))
  have hB : ∀ u ∈ U, u * t₁ * u⁻¹ = t₁ → u * t₂ * u⁻¹ = t₂ := by
    intro u hu e1
    by_contra n2
    have m2 := hperm u hu t₂ (Or.inr (Or.inl rfl))
    have e2 : u * t₂ * u⁻¹ = t₃ := by
      rcases m2 with e2 | e2 | e2
      · exact absurd (hinj u _ _ (e2.trans e1.symm)) (Ne.symm hne)
      · exact absurd e2 n2
      · exact e2
    have e3 : u * t₃ * u⁻¹ = t₂ := by rw [← h12, hmulc, e1, e2, h13]
    set v := c * u * c⁻¹ with hv
    have hvU : v ∈ U := (Subgroup.mem_normalizer_iff.mp hcU u).mp hu
    have hvconj : ∀ t : M, v * t * v⁻¹ = c * (u * (c⁻¹ * t * c) * u⁻¹) * c⁻¹ := fun t => by
      rw [hv]
      group
    have v1 : v * t₁ * v⁻¹ = t₃ := by rw [hvconj, hci3, e3, hc2]
    have v2 : v * t₂ * v⁻¹ = t₂ := by rw [hvconj, hci1, e1, hc1]
    have v3 : v * t₃ * v⁻¹ = t₁ := by rw [hvconj, hci2, e2, hc3]
    have huvU : u * v ∈ U := U.mul_mem hu hvU
    have hw : ∀ t : M, u * v * t * (u * v)⁻¹ = u * (v * t * v⁻¹) * u⁻¹ := fun t => by group
    have w1 : u * v * t₁ * (u * v)⁻¹ = t₂ := by rw [hw, v1, e3]
    have w2 : u * v * t₂ * (u * v)⁻¹ = t₃ := by rw [hw, v2, e2]
    have w3 : u * v * t₃ * (u * v)⁻¹ = t₁ := by rw [hw, v3, e1]
    exact hU3 _ huvU (three_dvd_orderOf_of_cycle w1 w2 w3 hne hne13)
  have hconj_c : ∀ u ∈ U, c⁻¹ * u * c ∈ U := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcU) u).mp hu
    simpa using this
  intro u hu
  have key : u * t₁ * u⁻¹ = t₁ ∧ u * t₂ * u⁻¹ = t₂ := by
    rcases hA u hu with e1 | e2 | e3
    · exact ⟨e1, hB u hu e1⟩
    ·
      set w := c⁻¹ * u * c with hw
      have hwU : w ∈ U := hconj_c u hu
      have hwc : ∀ t : M, w * t * w⁻¹ = c⁻¹ * (u * (c * t * c⁻¹) * u⁻¹) * c := fun t => by
        rw [hw]
        group
      have w1 : w * t₁ * w⁻¹ = t₁ := by rw [hwc, hc1, e2, hci1]
      have w2 := hB w hwU w1
      rw [hwc, hc2] at w2
      have e3 : u * t₃ * u⁻¹ = t₃ := by
        have := congrArg (fun x => c * x * c⁻¹) w2
        rw [show c * (c⁻¹ * (u * t₃ * u⁻¹) * c) * c⁻¹ = u * t₃ * u⁻¹ by group, hc2] at this
        exact this
      have e1 : u * t₁ * u⁻¹ = t₁ := by rw [← h23, hmulc, e2, e3]
      exact ⟨e1, e2⟩
    ·
      set w := c * u * c⁻¹ with hw
      have hwU : w ∈ U := (Subgroup.mem_normalizer_iff.mp hcU u).mp hu
      have hwc : ∀ t : M, w * t * w⁻¹ = c * (u * (c⁻¹ * t * c) * u⁻¹) * c⁻¹ := fun t => by
        rw [hw]
        group
      have w1 : w * t₁ * w⁻¹ = t₁ := by rw [hwc, hci3, e3, hc3]
      have w2 := hB w hwU w1
      rw [hwc, hci1] at w2
      have e1 : u * t₁ * u⁻¹ = t₁ := by
        have := congrArg (fun x => c⁻¹ * x * c) w2
        rw [show c⁻¹ * (c * (u * t₁ * u⁻¹) * c⁻¹) * c = u * t₁ * u⁻¹ by group, hci1] at this
        exact this
      exact ⟨e1, hB u hu e1⟩
  obtain ⟨e1, e2⟩ := key
  refine ⟨?_, ?_⟩
  · calc u * t₁ = u * t₁ * u⁻¹ * u := by group
      _ = t₁ * u := by rw [e1]
  · calc u * t₂ = u * t₂ * u⁻¹ * u := by group
      _ = t₂ * u := by rw [e2]

end CFSG.RankThree.PartTwo.Sec14.Res8Hess
