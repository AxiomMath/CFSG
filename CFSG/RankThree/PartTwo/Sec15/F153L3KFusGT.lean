module

public import CFSG.Assembly.Defs

public section

section FusGT


namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.FusGT

def prodSub {Q : Type} [Group Q] (H : Subgroup Q) (y : Q) (hc : ∀ h ∈ H, h * y = y * h) :
    Subgroup Q where
  carrier := {g | ∃ h ∈ H, ∃ n : ℤ, g = h * y ^ n}
  one_mem' := ⟨1, H.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨h, hh, n, rfl⟩ ⟨h', hh', n', rfl⟩
    refine ⟨h * h', H.mul_mem hh hh', n + n', ?_⟩
    have hcm : y ^ n * h' = h' * y ^ n :=
      ((show Commute h' y from hc h' hh').zpow_right n).eq.symm
    calc h * y ^ n * (h' * y ^ n') = h * (y ^ n * h') * y ^ n' := by simp only [mul_assoc]
      _ = h * (h' * y ^ n) * y ^ n' := by rw [hcm]
      _ = h * h' * (y ^ n * y ^ n') := by simp only [mul_assoc]
      _ = h * h' * y ^ (n + n') := by rw [zpow_add]
  inv_mem' := by
    rintro _ ⟨h, hh, n, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, -n, ?_⟩
    have hc2 : Commute h⁻¹ (y ^ n) :=
      (show Commute h⁻¹ y from hc h⁻¹ (H.inv_mem hh)).zpow_right n
    rw [mul_inv_rev, zpow_neg]
    exact hc2.inv_right.eq.symm

theorem mem_prodSub {Q : Type} [Group Q] (H : Subgroup Q) (y : Q)
    (hc : ∀ h ∈ H, h * y = y * h) (g : Q) :
    g ∈ prodSub H y hc ↔ ∃ h ∈ H, ∃ n : ℤ, g = h * y ^ n :=
  Iff.rfl

theorem sup_zpowers_le_prodSub {Q : Type} [Group Q] (H : Subgroup Q) (y : Q)
    (hc : ∀ h ∈ H, h * y = y * h) : H ⊔ Subgroup.zpowers y ≤ prodSub H y hc := by
  refine sup_le (fun h hh => (mem_prodSub H y hc h).2 ⟨h, hh, 0, by simp⟩) ?_
  rw [Subgroup.zpowers_le]
  exact (mem_prodSub H y hc y).2 ⟨1, H.one_mem, 1, by simp⟩

theorem decomp_sup {Q : Type} [Group Q] (H : Subgroup Q) (y : Q) (hy : orderOf y = 3)
    (hc : ∀ h ∈ H, h * y = y * h) :
    ∀ g ∈ H ⊔ Subgroup.zpowers y, ∃ h ∈ H, ∃ j : ℕ, j < 3 ∧ g = h * y ^ j := by
  intro g hg
  obtain ⟨h, hh, n, rfl⟩ := (mem_prodSub H y hc _).1 (sup_zpowers_le_prodSub H y hc hg)
  have hnn : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hlt' : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hn : ((n % 3).toNat : ℤ) = n % 3 := Int.toNat_of_nonneg hnn
  have hlt : (n % 3).toNat < 3 := by omega
  refine ⟨h, hh, (n % 3).toNat, hlt, ?_⟩
  have key : y ^ (n % 3) = y ^ n := by
    have := zpow_mod_orderOf y n
    rw [hy] at this
    simpa using this
  rw [← zpow_natCast, hn, key]

def Yj {Q : Type} [Group Q] (B A : Subgroup Q) (x : Q) (j : ℕ) : Set Q :=
  {b | b ∈ B ∧ ∃ a ∈ A, b = a * x ^ j}

theorem mem_Yj {Q : Type} [Group Q] (B A : Subgroup Q) (x : Q) (j : ℕ) (b : Q) :
    b ∈ Yj B A x j ↔ b ∈ B ∧ ∃ a ∈ A, b = a * x ^ j :=
  Iff.rfl

theorem translate_mem {Q : Type} [Group Q] (A : Subgroup Q) (x : Q)
    (hc : ∀ a ∈ A, a * x = x * a) (j : ℕ) (a₀ a : Q) (ha₀ : a₀ ∈ A) (ha : a ∈ A) :
    (a₀ * x ^ j)⁻¹ * (a * x ^ j) ∈ A := by
  have hu : a₀⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha₀) ha
  have hcm : (a₀⁻¹ * a) * x ^ j = x ^ j * (a₀⁻¹ * a) :=
    ((show Commute (a₀⁻¹ * a) x from hc _ hu).pow_right j).eq
  have e : (a₀ * x ^ j)⁻¹ * (a * x ^ j) = (x ^ j)⁻¹ * ((a₀⁻¹ * a) * x ^ j) := by
    group
  have e2 : (a₀ * x ^ j)⁻¹ * (a * x ^ j) = a₀⁻¹ * a := by
    rw [e, hcm, inv_mul_cancel_left]
  rw [e2]
  exact hu

theorem ncard_le_of_translate {Q : Type} [Group Q] [Finite Q] (B H : Subgroup Q) (X : Set Q)
    (hX : X ⊆ (B : Set Q)) (y₀ : Q) (hy₀ : y₀ ∈ X) (hdiff : ∀ b ∈ X, y₀⁻¹ * b ∈ H) :
    X.ncard ≤ ((B ⊓ H : Subgroup Q) : Set Q).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun b => y₀⁻¹ * b) (fun b hb => ?_)
    (fun b _ b' _ h => ?_)
  · exact Subgroup.mem_inf.2 ⟨B.mul_mem (B.inv_mem (hX hy₀)) (hX hb), hdiff b hb⟩
  · exact mul_left_cancel h

theorem ncard_inter_ge {Q : Type} [Group Q] [Finite Q] (A : Subgroup Q) (x : Q)
    (hx : orderOf x = 3) (hc : ∀ a ∈ A, a * x = x * a) (B : Subgroup Q)
    (hBS : B ≤ A ⊔ Subgroup.zpowers x) (hB : (B : Set Q).ncard = 9) :
    3 ≤ ((B ⊓ A : Subgroup Q) : Set Q).ncard := by
  have hcov : (B : Set Q) ⊆ Yj B A x 0 ∪ Yj B A x 1 ∪ Yj B A x 2 := by
    intro b hb
    obtain ⟨a, ha, j, hj, rfl⟩ := decomp_sup A x hx hc _ (hBS hb)
    interval_cases j
    · exact Set.mem_union_left _ (Set.mem_union_left _ ((mem_Yj B A x 0 _).2 ⟨hb, a, ha, rfl⟩))
    · exact Set.mem_union_left _ (Set.mem_union_right _ ((mem_Yj B A x 1 _).2 ⟨hb, a, ha, rfl⟩))
    · exact Set.mem_union_right _ ((mem_Yj B A x 2 _).2 ⟨hb, a, ha, rfl⟩)
  have hYle : ∀ j, (Yj B A x j).ncard ≤ ((B ⊓ A : Subgroup Q) : Set Q).ncard := by
    intro j
    rcases (Yj B A x j).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
    · simp [h]
    · obtain ⟨hyB, a₀, ha₀, rfl⟩ := (mem_Yj B A x j _).1 hy₀
      refine ncard_le_of_translate B A (Yj B A x j) ?_ _ hy₀ ?_
      · intro b hb
        exact ((mem_Yj B A x j b).1 hb).1
      · intro b hb
        obtain ⟨-, a, ha, rfl⟩ := (mem_Yj B A x j b).1 hb
        exact translate_mem A x hc j a₀ a ha₀ ha
  have h1 := Set.ncard_le_ncard hcov
  have h2 := Set.ncard_union_le (Yj B A x 0 ∪ Yj B A x 1) (Yj B A x 2)
  have h3 := Set.ncard_union_le (Yj B A x 0) (Yj B A x 1)
  have h4 := hYle 0
  have h5 := hYle 1
  have h6 := hYle 2
  omega

theorem exists_ne_one_of_two_le {Q : Type} [Group Q] [Finite Q] (C : Subgroup Q)
    (h : 2 ≤ (C : Set Q).ncard) : ∃ a, a ∈ C ∧ a ≠ 1 := by
  by_contra hcon
  have hsub : (C : Set Q) ⊆ {1} := fun a ha => by
    by_contra hne
    exact hcon ⟨a, ha, hne⟩
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_singleton] at this
  omega

theorem fusion_b_vacuous
    {Q : Type} [Group Q] [Finite Q] (K : Subgroup Q) (x : Q) (hx3 : orderOf x = 3)
    (hxK : x ∉ K) (A₀ : Subgroup Q) (hA₀K : A₀ ≤ K)
    (hxA : ∀ a ∈ A₀, a * x = x * a) (hcard : Nat.card A₀ = 9)
    (hel : CFSG.Assembly.IsElemAbelian 3 A₀)
    (hnoinv : ∀ a ∈ A₀, a ≠ 1 → ∀ t ∈ K, orderOf t = 2 → t * a ≠ a * t) :
    ∀ B : Subgroup Q, B ≤ A₀ ⊔ Subgroup.zpowers x → Nat.card B = 9 →
      (∃ t ∈ K, orderOf t = 2 ∧ ∀ b ∈ B, t * b = b * t) → False := by
  intro B hBS hB ⟨t, htK, hto, htB⟩
  have hB' : (B : Set Q).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hB
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_two_le (B ⊓ A₀)
    (by have := ncard_inter_ge A₀ x hx3 hxA B hBS hB'; omega)
  have haB : a ∈ B := (Subgroup.mem_inf.1 ha).1
  have haA : a ∈ A₀ := (Subgroup.mem_inf.1 ha).2
  exact hnoinv a haA ha1 t htK hto (htB a haB)

theorem fusion_b_of_noInvolution
    {Q : Type} [Group Q] [Finite Q] (K : Subgroup Q) (x : Q) (hx3 : orderOf x = 3)
    (hxK : x ∉ K) (A₀ : Subgroup Q) (hA₀K : A₀ ≤ K)
    (hxA : ∀ a ∈ A₀, a * x = x * a) (hcard : Nat.card A₀ = 9)
    (hel : CFSG.Assembly.IsElemAbelian 3 A₀) {r : Q} (hr : r ∈ A₀) (hr1 : r ≠ 1)
    (hnoinv : ∀ t ∈ K, orderOf t = 2 → t * r ≠ r * t) :
    ∀ B : Subgroup Q, B ≤ A₀ ⊔ Subgroup.zpowers x → Nat.card B = 9 →
      (∃ t ∈ K, orderOf t = 2 ∧ ∀ b ∈ B, t * b = b * t) → ∃ k : ℕ, x * r ^ k ∈ B := by
  intro B hBS hB ⟨t, htK, hto, htB⟩
  obtain ⟨hcomm, hpow⟩ := hel
  have hAcomm : ∀ u ∈ A₀, ∀ v ∈ A₀, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : ∀ u ∈ A₀, u ^ 3 = 1 := hpow
  have hr3 : orderOf r = 3 := orderOf_eq_prime (hA3 r hr) hr1
  have hB' : (B : Set Q).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hB
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_two_le (B ⊓ A₀)
    (by have := ncard_inter_ge A₀ x hx3 hxA B hBS hB'; omega)
  have haB : a ∈ B := (Subgroup.mem_inf.1 ha).1
  have haA : a ∈ A₀ := (Subgroup.mem_inf.1 ha).2
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hA3 a haA) ha1
  have hta : t * a = a * t := htB a haB
  have hrnot : r ∉ Subgroup.zpowers a := by
    intro hr'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hr'
    apply hnoinv t htK hto
    rw [← hm]
    exact ((show Commute t a from hta).zpow_right m).eq
  have hcomm_za : ∀ h ∈ Subgroup.zpowers a, h * r = r * h := fun h hh =>
    hAcomm h (Subgroup.zpowers_le.2 haA hh) r hr
  obtain ⟨P, hPmem⟩ : ∃ P : Subgroup Q,
      ∀ g, g ∈ P ↔ ∃ h ∈ Subgroup.zpowers a, ∃ n : ℤ, g = h * r ^ n :=
    ⟨prodSub (Subgroup.zpowers a) r hcomm_za, fun g => Iff.rfl⟩
  have hPA : P ≤ A₀ := by
    intro g hg
    obtain ⟨h, hh, n, rfl⟩ := (hPmem g).1 hg
    exact A₀.mul_mem (Subgroup.zpowers_le.2 haA hh) (A₀.zpow_mem hr n)
  have hzP : Subgroup.zpowers a ≤ P := fun h hh => (hPmem h).2 ⟨h, hh, 0, by simp⟩
  have hrP : r ∈ P := (hPmem r).2 ⟨1, Subgroup.one_mem _, 1, by simp⟩
  have hdvd : Nat.card P ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hPA
    rw [hcard] at this
    simpa using this
  have hPcard : Nat.card P = 9 := by
    obtain ⟨i, hi, hiP⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hge : 3 ≤ Nat.card P := by
      have := Subgroup.card_le_of_le hzP
      rw [Nat.card_zpowers, ha3] at this
      exact this
    interval_cases i
    · have h1 : Nat.card P = 1 := by simpa using hiP
      omega
    · exfalso
      have h3 : Nat.card P = 3 := by simpa using hiP
      have heq : Subgroup.zpowers a = P :=
        Subgroup.eq_of_le_of_card_ge hzP (by rw [Nat.card_zpowers, ha3]; omega)
      apply hrnot
      rw [heq]
      exact hrP
    · have h9 : Nat.card P = 9 := by simpa using hiP
      exact h9
  have hPeq : P = A₀ := Subgroup.eq_of_le_of_card_ge hPA (by omega)
  have hcover : ∀ y ∈ A₀, ∃ m : ℤ, ∃ n : ℤ, y = a ^ m * r ^ n := by
    intro y hy
    have hyP : y ∈ P := by
      rw [hPeq]
      exact hy
    obtain ⟨h, hh, n, rfl⟩ := (hPmem y).1 hyP
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ⟨m, n, rfl⟩
  have hnotB : ¬ B ≤ A₀ := by
    intro hBA
    have hBeq : B = A₀ := Subgroup.eq_of_le_of_card_ge hBA (by omega)
    have hrB : r ∈ B := by
      rw [hBeq]
      exact hr
    exact hnoinv t htK hto (htB r hrB)
  obtain ⟨b, hbB, hbA⟩ : ∃ b ∈ B, b ∉ A₀ := by
    by_contra hcon
    refine hnotB (fun b hb => ?_)
    by_contra hbA
    exact hcon ⟨b, hb, hbA⟩
  have hx3pow : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  obtain ⟨c, hcB, a₂, ha₂, hc⟩ : ∃ c ∈ B, ∃ a₂ ∈ A₀, c = a₂ * x := by
    obtain ⟨a₁, ha₁, j, hj, hbj⟩ := decomp_sup A₀ x hx3 hxA b (hBS hbB)
    interval_cases j
    · exact (hbA (by rw [hbj, pow_zero, mul_one]; exact ha₁)).elim
    · exact ⟨b, hbB, a₁, ha₁, by rw [hbj, pow_one]⟩
    · have hx2 : (x ^ 2)⁻¹ = x :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hx3pow)
      refine ⟨b⁻¹, B.inv_mem hbB, a₁⁻¹, A₀.inv_mem ha₁, ?_⟩
      rw [hbj, mul_inv_rev, hx2]
      exact (hxA _ (A₀.inv_mem ha₁)).symm
  obtain ⟨m, n, ha₂eq⟩ := hcover a₂ ha₂
  have hrx : r ^ n * x = x * r ^ n :=
    ((show Commute r x from hxA r hr).zpow_left n).eq
  have hxr : x * r ^ n = (a ^ m)⁻¹ * c := by
    rw [hc, ha₂eq, mul_assoc, inv_mul_cancel_left]
    exact hrx.symm
  have hmem : x * r ^ n ∈ B := by
    rw [hxr]
    exact B.mul_mem (B.inv_mem (B.zpow_mem haB m)) hcB
  refine ⟨(n % 3).toNat, ?_⟩
  have hnn : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hn : ((n % 3).toNat : ℤ) = n % 3 := Int.toNat_of_nonneg hnn
  have key : r ^ (n % 3) = r ^ n := by
    have := zpow_mod_orderOf r n
    rw [hr3] at this
    simpa using this
  have hpow' : r ^ ((n % 3).toNat) = r ^ n := by
    rw [← zpow_natCast, hn, key]
  rw [hpow']
  exact hmem

end CFSG.RankThree.PartTwo.Sec15.F153L3K.FusGT

end FusGT

