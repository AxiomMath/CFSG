module

public import CFSG.Walter.J1.Tools

public section

namespace CFSG.Walter.J1

variable {G : Type*} [Group G] [Finite G]

theorem exists_odd_complement {K T : Subgroup G} (hTK : T ≤ K) (hT2 : IsPGroup 2 T)
    (hmax : ∀ R : Subgroup G, R ≤ K → IsPGroup 2 R → T ≤ R → R = T)
    (hNC : ∀ n ∈ K, n ∈ Subgroup.normalizer (T : Set G) → ∀ x ∈ T, n * x = x * n) :
    ∃ O : Subgroup G, O ≤ K ∧ (O.subgroupOf K).Normal ∧ ¬ 2 ∣ Nat.card O ∧
      Nat.card O * Nat.card T = Nat.card K ∧ ∀ g ∈ K, Odd (orderOf g) → g ∈ O := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P₀ := T.subgroupOf K
  have eP : P₀ ≃* T := Subgroup.subgroupOfEquivOfLe hTK
  have hP₀ : IsPGroup 2 P₀ := hT2.of_equiv eP.symm
  obtain ⟨Q, hQ⟩ := hP₀.exists_le_sylow
  have hQT : (Q : Subgroup K).map K.subtype = T := by
    apply hmax _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map _)
    intro x hx
    exact ⟨⟨x, hTK hx⟩, hQ (by simpa [P₀, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hQP : (Q : Subgroup K) = P₀ := by
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective (Q : Subgroup K), hQT]
    rfl
  have hNCQ : Subgroup.normalizer ((Q : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((Q : Subgroup K) : Set K) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hnT : (n : G) ∈ Subgroup.normalizer (T : Set G) := by
      refine mem_normalizer_of_conj_mem fun x hx => ?_
      have hxQ : (⟨x, hTK hx⟩ : K) ∈ (Q : Subgroup K) := by
        rw [hQP]
        simpa [P₀, Subgroup.mem_subgroupOf] using hx
      have := (Subgroup.mem_normalizer_iff.mp hn _).mp hxQ
      rw [hQP] at this
      simpa [P₀, Subgroup.mem_subgroupOf] using this
    have hyT : (y : G) ∈ T := by
      rw [hQP] at hy
      simpa [P₀, Subgroup.mem_subgroupOf] using hy
    exact Subtype.ext (hNC n n.2 hnT y hyT).symm
  set φ := MonoidHom.transferSylow Q hNCQ
  have hcomp : Subgroup.IsComplement' φ.ker (Q : Subgroup K) :=
    MonoidHom.ker_transferSylow_isComplement' Q hNCQ
  refine ⟨φ.ker.map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact MonoidHom.normal_ker φ
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact MonoidHom.not_dvd_card_ker_transferSylow Q hNCQ
  · have hQcard : Nat.card (Q : Subgroup K) = Nat.card T := by
      rw [show Nat.card (Q : Subgroup K) = Nat.card P₀ from
        congrArg (fun H : Subgroup K => Nat.card H) hQP]
      exact Nat.card_congr eP.toEquiv
    rw [Subgroup.card_map_of_injective K.subtype_injective, ← hcomp.card_mul_card, hQcard]
  · intro g hg hodd
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have h1 : orderOf (φ ⟨g, hg⟩) ∣ orderOf g := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have : (⟨g, hg⟩ : K) ^ orderOf g = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    obtain ⟨k, hk⟩ := Q.isPGroup' (φ ⟨g, hg⟩)
    have h2 : orderOf (φ ⟨g, hg⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

omit [Finite G] in
theorem mem_kleinFour_iff {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hc : Commute a b)
    {x : G} :
    x ∈ GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hc ↔
      x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
  change x ∈ ({a * b, a, b, 1} : Set G) ↔ _
  simp

omit [Finite G] in
theorem commute_of_odd_of_normalizer {a b n : G} (ha : a * a = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {m : ℕ} (hm : Odd m)
    (hnm : n ^ m = 1)
    (hT : ∀ x, x = a ∨ x = b → n * x * n⁻¹ = a * b ∨ n * x * n⁻¹ = a ∨ n * x * n⁻¹ = b)
    (P : G → Prop) (hPa : P a) (hPab : ¬ P (a * b)) (hP : ∀ z, P z → P (n * z * n⁻¹)) :
    n * a = a * n ∧ n * b = b * n := by
  have hinj : ∀ x y : G, n * x * n⁻¹ = n * y * n⁻¹ → x = y := fun x y hxy => by
    simpa using hxy
  have hab1 : a * b ≠ a := fun h1 => hb1 (by simpa using h1)
  have hab2 : a * b ≠ b := fun h1 => ha1 (by simpa using h1)
  have hpow : ∀ x : G, n * (n * x * n⁻¹) * n⁻¹ = x → ∀ k : ℕ,
      n ^ (2 * k) * x * (n ^ (2 * k))⁻¹ = x := by
    intro x hx k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_two]
      calc n ^ (2 * k) * (n * n) * x * (n ^ (2 * k) * (n * n))⁻¹ =
          n ^ (2 * k) * (n * (n * x * n⁻¹) * n⁻¹) * (n ^ (2 * k))⁻¹ := by group
        _ = x := by rw [hx, ih]
  obtain ⟨k, hk⟩ := hm
  have hodd : ∀ x : G, n * (n * x * n⁻¹) * n⁻¹ = x → n * x * n⁻¹ = x := by
    intro x hx
    have := hpow x hx k
    calc n * x * n⁻¹ = n * (n ^ (2 * k) * x * (n ^ (2 * k))⁻¹) * n⁻¹ := by rw [this]
      _ = n ^ m * x * (n ^ m)⁻¹ := by rw [hk, pow_succ']; group
      _ = x := by rw [hnm]; group
  have hconj_mul : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
  have hPna := hP a hPa
  rcases hT a (Or.inl rfl) with h1 | h1 | h1
  · exact absurd (h1 ▸ hPna) hPab
  ·
    rcases hT b (Or.inr rfl) with h2 | h2 | h2
    ·
      exfalso
      have h3 : n * (a * b) * n⁻¹ = b := by
        rw [hconj_mul, h1, h2, ← mul_assoc, ha, one_mul]
      have := hodd b (by rw [h2, h3])
      rw [this] at h2
      exact hab2 h2.symm
    · exact absurd (hinj _ _ (h1.trans h2.symm)) hab
    · refine ⟨?_, ?_⟩
      · calc n * a = (n * a * n⁻¹) * n := by group
          _ = a * n := by rw [h1]
      · calc n * b = (n * b * n⁻¹) * n := by group
          _ = b * n := by rw [h2]
  ·
    exfalso
    have hPb : P b := h1 ▸ hPna
    rcases hT b (Or.inr rfl) with h2 | h2 | h2
    · exact hPab (h2 ▸ hP b hPb)
    · have := hodd a (by rw [h1, h2])
      exact hab (this.symm.trans h1)
    · exact hab (hinj _ _ (h1.trans h2.symm))

theorem exists_odd_complement_four {K : Subgroup G} {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) (haK : a ∈ K) (hbK : b ∈ K)
    (hmax : ∀ R : Subgroup G, R ≤ K → IsPGroup 2 R →
      GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hc ≤ R →
      R = GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hc)
    (P : G → Prop) (hPa : P a) (hPab : ¬ P (a * b)) (hP : ∀ n ∈ K, ∀ z, P z → P (n * z * n⁻¹)) :
    ∃ O : Subgroup G, O ≤ K ∧ (O.subgroupOf K).Normal ∧ ¬ 2 ∣ Nat.card O ∧
      Nat.card O * 4 = Nat.card K ∧ ∀ g ∈ K, Odd (orderOf g) → g ∈ O := by
  classical
  have hcomm : Commute a b := hc
  set T := GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hc
  have hT4 : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    a b ha hb ha1 hb1 hab _
  have hmemT : ∀ x, x ∈ T ↔ x = a * b ∨ x = a ∨ x = b ∨ x = 1 := fun x => by
    change x ∈ ({a * b, a, b, 1} : Set G) ↔ _
    simp
  have hTK : T ≤ K := by
    intro x hx
    rcases (hmemT x).mp hx with rfl | rfl | rfl | rfl
    · exact K.mul_mem haK hbK
    · exact haK
    · exact hbK
    · exact K.one_mem
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4.card_four]; norm_num)
  obtain ⟨O, hOK, hON, hO2, hOcard, hOodd⟩ := exists_odd_complement hTK hT2 hmax (by
    intro n hnK hnT x hx
    have hn0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
    obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
    have hTconj : ∀ y : G, y ∈ Subgroup.normalizer (T : Set G) → ∀ x, x = a ∨ x = b →
        y * x * y⁻¹ = a * b ∨ y * x * y⁻¹ = a ∨ y * x * y⁻¹ = b := by
      intro y hy x hx
      have hxT : x ∈ T := by
        rcases hx with rfl | rfl
        · exact (hmemT _).mpr (Or.inr (Or.inl rfl))
        · exact (hmemT _).mpr (Or.inr (Or.inr (Or.inl rfl)))
      have hx1 : x ≠ 1 := by rcases hx with rfl | rfl <;> assumption
      rcases (hmemT _).mp ((Subgroup.mem_normalizer_iff.mp hy x).mp hxT) with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
      · exfalso
        apply hx1
        have := congrArg (fun z => y⁻¹ * z * y) h1
        simpa [mul_assoc] using this
    set n' := n ^ 2 ^ e
    have hn'm : n' ^ m = 1 := by
      rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
    have hn'K : n' ∈ K := K.pow_mem hnK _
    have hn'T : n' ∈ Subgroup.normalizer (T : Set G) := Subgroup.pow_mem _ hnT _
    obtain ⟨h1, h2⟩ := commute_of_odd_of_normalizer ha ha1 hb1 hab hm hn'm
      (hTconj n' hn'T) P hPa hPab (fun z hz => hP n' hn'K z hz)
    set n₂ := n ^ m
    have hn₂ : n₂ ^ 2 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
    have hn₂T : n₂ ∈ T := by
      have hZ : IsPGroup 2 (Subgroup.zpowers n₂) := by
        have hdvd : orderOf n₂ ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hn₂
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
        exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      have hR := IsPGroup.to_sup_of_normal_left' hT2 hZ (by
        rw [Subgroup.zpowers_le]
        exact Subgroup.pow_mem _ hnT _)
      have hRK : T ⊔ Subgroup.zpowers n₂ ≤ K :=
        sup_le hTK ((Subgroup.zpowers_le).mpr (K.pow_mem hnK _))
      have := hmax _ hRK hR le_sup_left
      rw [← this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hn₂c : ∀ y ∈ T, n₂ * y = y * n₂ := fun y hy =>
      congrArg Subtype.val (hT4.isMulCommutative.is_comm.comm ⟨n₂, hn₂T⟩ ⟨y, hy⟩)
    have hcop : Nat.Coprime m (2 ^ e) := Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hm)
    have hbez : (1 : ℤ) = m * m.gcdA (2 ^ e) + 2 ^ e * m.gcdB (2 ^ e) := by
      have := Nat.gcd_eq_gcd_ab m (2 ^ e)
      rw [hcop.gcd_eq_one] at this
      exact_mod_cast this
    have hn : n = n₂ ^ m.gcdA (2 ^ e) * n' ^ m.gcdB (2 ^ e) := by
      calc n = n ^ (1 : ℤ) := (zpow_one n).symm
        _ = n ^ ((m : ℤ) * m.gcdA (2 ^ e) + (2 ^ e : ℕ) * m.gcdB (2 ^ e)) := by
          rw [hbez]; push_cast; ring_nf
        _ = n₂ ^ m.gcdA (2 ^ e) * n' ^ m.gcdB (2 ^ e) := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    have hca : n' * a = a * n' := h1
    have hcb : n' * b = b * n' := h2
    have hn'x : n' * x = x * n' := by
      rcases (hmemT x).mp hx with rfl | rfl | rfl | rfl
      · rw [← mul_assoc, hca, mul_assoc, hcb, mul_assoc]
      · exact hca
      · exact hcb
      · simp
    have hn₂x := hn₂c x hx
    rw [hn]
    have e1 : Commute (n₂ ^ m.gcdA (2 ^ e)) x := (Commute.zpow_left hn₂x _)
    have e2 : Commute (n' ^ m.gcdB (2 ^ e)) x := (Commute.zpow_left hn'x _)
    exact (e1.mul_left e2).eq)
  exact ⟨O, hOK, hON, hO2, by rw [← hOcard, hT4.card_four], hOodd⟩

end CFSG.Walter.J1
