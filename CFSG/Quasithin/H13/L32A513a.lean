module

public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

theorem s3_sq_or_cube : ∀ a : Equiv.Perm (Fin 3), a ^ 2 = 1 ∨ a ^ 3 = 1 := by decide

theorem s3_cube_of_odd {a : Equiv.Perm (Fin 3)} (ha : Odd (orderOf a)) : a ^ 3 = 1 := by
  rcases s3_sq_or_cube a with h | h
  · have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf a = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
      · exact h3
      · rw [h3] at ha
        exact absurd ha (by decide)
    rw [orderOf_eq_one_iff.mp h2, one_pow]
  · exact h

theorem s3_mem_powers : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 → a ≠ 1 →
    b = 1 ∨ b = a ∨ b = a ^ 2 := by decide

theorem s3_comm : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a := by
  decide

theorem s3s3_comm (a b : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) : a * b = b * a := by
  have ha1 : a.1 ^ 3 = 1 := by rw [← Prod.pow_fst, ha, Prod.fst_one]
  have ha2 : a.2 ^ 3 = 1 := by rw [← Prod.pow_snd, ha, Prod.snd_one]
  have hb1 : b.1 ^ 3 = 1 := by rw [← Prod.pow_fst, hb, Prod.fst_one]
  have hb2 : b.2 ^ 3 = 1 := by rw [← Prod.pow_snd, hb, Prod.snd_one]
  exact Prod.ext (s3_comm _ _ ha1 hb1) (s3_comm _ _ ha2 hb2)

variable {G : Type*} [Group G] [Finite G]

theorem cube_of_odd {K : Subgroup G} (hK : quasithinO2QuotientIso K (Equiv.Perm (Fin 3)))
    {k : G} (hk : k ∈ K) (ho : Odd (orderOf k)) : k ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, -, hφk⟩ := hK
  have h1 : Odd (orderOf (φ ⟨k, hk⟩)) :=
    Odd.of_dvd_nat (by rwa [Subgroup.orderOf_mk]) (orderOf_map_dvd φ _)
  have h2 : (⟨k, hk⟩ : ↥K) ^ 3 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact s3_cube_of_odd h1
  rw [hφk] at h2
  obtain ⟨n, hn⟩ := LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥K) ⟨_, h2⟩
  have h3 : (k ^ 3) ^ 2 ^ n = 1 := by
    have := congrArg (fun x : ↥(Open.pCore 2 ↥K) => ((x : ↥K) : G)) hn
    simpa using this
  have h4 : orderOf (k ^ 3) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h3
  have h5 : Odd (orderOf (k ^ 3)) := Odd.of_dvd_nat ho (orderOf_pow_dvd 3)
  have h6 : orderOf (k ^ 3) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr h5)) h4
  exact orderOf_eq_one_iff.mp h6

theorem exists_eq_pow_of_odd {Q : Type*} [Group Q] {H K : Subgroup G} (hKH : K ≤ H)
    (hK : quasithinO2QuotientIso K (Equiv.Perm (Fin 3))) (π : ↥H →* Q)
    (hQ : ∀ a b : Q, a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1)
    {k₁ k₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (ho₁ : Odd (orderOf k₁))
    (ho₂ : Odd (orderOf k₂)) (hπ : π ⟨k₁, hKH hk₁⟩ ≠ 1) :
    ∃ j : ℕ, π ⟨k₂, hKH hk₂⟩ = π ⟨k₁, hKH hk₁⟩ ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc₁ := cube_of_odd hK hk₁ ho₁
  have hc₂ := cube_of_odd hK hk₂ ho₂
  obtain ⟨φ, -, hφk⟩ := hK
  have hφ₁ : φ ⟨k₁, hk₁⟩ ≠ 1 := by
    intro h
    have h1 : (⟨k₁, hk₁⟩ : ↥K) ∈ Open.pCore 2 ↥K := by
      rw [← hφk]
      exact h
    obtain ⟨n, hn⟩ := LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥K) ⟨_, h1⟩
    have h2 : k₁ ^ 2 ^ n = 1 := by
      have := congrArg (fun x : ↥(Open.pCore 2 ↥K) => ((x : ↥K) : G)) hn
      simpa using this
    have h3 : orderOf k₁ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf k₁ = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr ho₁)) h3
    apply hπ
    have : (⟨k₁, hKH hk₁⟩ : ↥H) = 1 := Subtype.ext (orderOf_eq_one_iff.mp h4)
    rw [this, map_one]
  have hφc : ∀ k (hk : k ∈ K), k ^ 3 = 1 → φ ⟨k, hk⟩ ^ 3 = 1 := fun k hk h3 => by
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, φ ⟨k₂, hk₂⟩ = φ ⟨k₁, hk₁⟩ ^ j := by
    rcases s3_mem_powers _ _ (hφc _ hk₁ hc₁) (hφc _ hk₂ hc₂) hφ₁ with h | h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
    · exact ⟨2, h⟩
  set q : ↥K := (⟨k₁, hk₁⟩ : ↥K)⁻¹ ^ j * ⟨k₂, hk₂⟩ with hq
  have hqk : q ∈ Open.pCore 2 ↥K := by
    rw [← hφk, MonoidHom.mem_ker, hq, map_mul, map_pow, map_inv, hj, inv_pow,
      inv_mul_cancel]
  obtain ⟨n, hn⟩ := LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥K) ⟨_, hqk⟩
  have hq2 : q ^ 2 ^ n = 1 := by
    have := congrArg (fun x : ↥(Open.pCore 2 ↥K) => (x : ↥K)) hn
    simpa using this
  set π' : ↥K →* Q := π.comp (Subgroup.inclusion hKH) with hπ'
  have hπ'1 : π' ⟨k₁, hk₁⟩ = π ⟨k₁, hKH hk₁⟩ := rfl
  have hπ'2 : π' ⟨k₂, hk₂⟩ = π ⟨k₂, hKH hk₂⟩ := rfl
  have hq3 : π' q ^ 3 = 1 := by
    have ha : ((π' ⟨k₁, hk₁⟩)⁻¹ ^ j) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, ← map_pow]
      have : (⟨k₁, hk₁⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc₁)
      rw [this, map_one, inv_one, one_pow]
    have hb : π' ⟨k₂, hk₂⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨k₂, hk₂⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc₂)
      rw [this, map_one]
    have := hQ _ _ ha hb
    rwa [hq, map_mul, map_pow, map_inv]
  have hq2' : π' q ^ 2 ^ n = 1 := by rw [← map_pow, hq2, map_one]
  have hq1 : π' q = 1 := by
    have h1 : orderOf (π' q) ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
    have h2 : orderOf (π' q) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hq2'
    have h3 : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  refine ⟨j, ?_⟩
  rw [hq, map_mul, map_pow, map_inv, mul_eq_one_iff_eq_inv, inv_pow, inv_inj] at hq1
  rw [← hπ'1, ← hπ'2, hq1]

theorem f618Two_cube {D : Type*} [Group D] [Finite D] (h : F6.IsF618CaseTwo D) {a b : D}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    (a * b) ^ 3 = 1 ∧ ⁅a, b⁆ * a = a * ⁅a, b⁆ ∧ ⁅a, b⁆ * b = b * ⁅a, b⁆ ∧ ⁅a, b⁆ ^ 3 = 1 ∧
      ∀ g : D, g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ ∨ g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ ^ 2 := by
  unfold F6.IsF618CaseTwo at h
  rcases h with hne | ⟨φ, -, hN⟩
  ·
    obtain ⟨e⟩ := hne
    have hab : a * b = b * a := by
      apply e.injective
      rw [map_mul, map_mul]
      exact s3s3_comm _ _ (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one])
    have hc : ⁅a, b⁆ = 1 := by
      rw [commutatorElement_def, hab, mul_inv_cancel_right, mul_inv_cancel]
    refine ⟨?_, ?_, ?_, ?_, fun g => Or.inl ?_⟩
    · rw [(Commute.mul_pow hab 3), ha, hb, one_mul]
    · rw [hc, one_mul, mul_one]
    · rw [hc, one_mul, mul_one]
    · rw [hc, one_pow]
    · rw [hc, mul_one, mul_inv_cancel]
  ·
    obtain ⟨hex, hcard, hexp⟩ := hN
    set N := φ.ker with hNdef
    have hmem : ∀ d : D, d ^ 3 = 1 → d ∈ N := by
      intro d hd
      rw [hNdef, MonoidHom.mem_ker]
      have h2 : φ d ^ 2 = 1 := by
        have : ∀ u : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u ^ 2 = 1 := by decide
        exact this _
      have h3 : φ d ^ 3 = 1 := by rw [← map_pow, hd, map_one]
      calc φ d = φ d ^ 2 * φ d := by rw [h2, one_mul]
        _ = φ d ^ 3 := by rw [← pow_succ]
        _ = 1 := h3
    have haN := hmem a ha
    have hbN := hmem b hb
    set a' : ↥N := ⟨a, haN⟩
    set b' : ↥N := ⟨b, hbN⟩
    have hcZ : ⁅a', b'⁆ ∈ Subgroup.center ↥N := by
      have hcomm := (CFSG.IsExtraspecial.quotient_elementary_abelian 3 ↥N).toIsMulCommutative
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥N)) ⁅a', b'⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_def, hcomm.is_comm.comm
          ((QuotientGroup.mk' (Subgroup.center ↥N)) a'), mul_inv_cancel_right, mul_inv_cancel]
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
    have hcv : ((⁅a', b'⁆ : ↥N) : D) = ⁅a, b⁆ := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := hexp (a' * b')
      simpa using congrArg Subtype.val this
    · have := Subgroup.mem_center_iff.mp hcZ a'
      have h2 := congrArg Subtype.val this
      simpa [hcv] using h2.symm
    · have := Subgroup.mem_center_iff.mp hcZ b'
      have h2 := congrArg Subtype.val this
      simpa [hcv] using h2.symm
    · have := hexp ⁅a', b'⁆
      simpa [hcv] using congrArg Subtype.val this
    · intro g
      by_cases hc1 : ⁅a, b⁆ = 1
      · left
        rw [hc1, mul_one, mul_inv_cancel]
      have hgN : g * ⁅a, b⁆ * g⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem _
        (hcv ▸ (⁅a', b'⁆ : ↥N).2) g
      have hgZ : (⟨_, hgN⟩ : ↥N) ∈ Subgroup.center ↥N := by
        rw [Subgroup.mem_center_iff]
        intro n
        apply Subtype.ext
        have hn : g⁻¹ * (n : D) * g ∈ N := by
          have := (inferInstance : N.Normal).conj_mem _ n.2 g⁻¹
          simpa using this
        have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨_, hn⟩)
        simp only [Subgroup.coe_mul] at h1
        rw [hcv] at h1
        show (n : D) * (g * ⁅a, b⁆ * g⁻¹) = (g * ⁅a, b⁆ * g⁻¹) * n
        calc (n : D) * (g * ⁅a, b⁆ * g⁻¹) = g * ((g⁻¹ * n * g) * ⁅a, b⁆) * g⁻¹ := by group
          _ = g * (⁅a, b⁆ * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
          _ = g * ⁅a, b⁆ * g⁻¹ * n := by group
      have hc3 : ⁅a', b'⁆ ^ 3 = 1 := hexp _
      have hc1' : ⁅a', b'⁆ ≠ 1 := fun h => hc1 (by rw [← hcv, h, Subgroup.coe_one])
      have hord : orderOf (⟨⁅a', b'⁆, hcZ⟩ : ↥(Subgroup.center ↥N)) = 3 := by
        apply orderOf_eq_prime
        · exact Subtype.ext hc3
        · exact fun h => hc1' (congrArg Subtype.val h)
      have hzp : Subgroup.zpowers (⟨⁅a', b'⁆, hcZ⟩ : ↥(Subgroup.center ↥N)) = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers, hord, CFSG.IsExtraspecial.center_order_p 3 ↥N]
      have hmemZ : (⟨⟨_, hgN⟩, hgZ⟩ : ↥(Subgroup.center ↥N)) ∈
          Subgroup.zpowers (⟨⁅a', b'⁆, hcZ⟩ : ↥(Subgroup.center ↥N)) := by
        rw [hzp]
        exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemZ
      have hk' : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ ^ (k % 3 : ℤ) := by
        have h1 := congrArg (fun u : ↥(Subgroup.center ↥N) => ((u : ↥N) : D)) hk
        simp only [SubgroupClass.coe_zpow] at h1
        rw [← h1, ← hcv]
        have hc3' : ((⁅a', b'⁆ : ↥N) : D) ^ 3 = 1 := by
          simpa using congrArg Subtype.val hc3
        rw [← zpow_mod_orderOf, orderOf_eq_prime hc3' (fun h => hc1 (by rw [← hcv, h]))]
        norm_cast
      have hk3 : (0 : ℤ) ≤ k % 3 ∧ k % 3 < 3 := ⟨Int.emod_nonneg _ (by norm_num),
        Int.emod_lt_of_pos _ (by norm_num)⟩
      have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · exfalso
        rw [h0, zpow_zero] at hk'
        apply hc1
        calc ⁅a, b⁆ = g⁻¹ * (g * ⁅a, b⁆ * g⁻¹) * g := by group
          _ = 1 := by rw [hk']; group
      · left
        rw [hk', h1, zpow_one]
      · right
        rw [hk', h2]
        norm_cast

theorem fix_of_comm_triple {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {x y b : MulAut W} (hb : b = x * y * x⁻¹ * y⁻¹) (hbx : b * x = x * b) (hby : b * y = y * b)
    (hb3 : b ^ 3 = 1) {v : W} (hyv : y v = v) (hxv : v * x v * x (x v) = 1) : b v = v := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by rw [← sq, hW])
  have hbx' : ∀ w, b (x w) = x (b w) := fun w => by
    have := congrArg (fun f : MulAut W => f w) hbx
    simpa [MulAut.mul_apply] using this
  have hby' : ∀ w, b (y w) = y (b w) := fun w => by
    have := congrArg (fun f : MulAut W => f w) hby
    simpa [MulAut.mul_apply] using this
  have hb3' : ∀ w, b (b (b w)) = w := fun w => by
    have := congrArg (fun f : MulAut W => f w) hb3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hyx : ∀ w, b (y (x w)) = x (y w) := fun w => by
    have h1 : b * y * x = x * y := by rw [hb]; group
    have := congrArg (fun f : MulAut W => f w) h1
    simpa [MulAut.mul_apply] using this
  set p := x v with hp
  set q := x (x v) with hq
  have hyp : y p = b (b p) := by
    have h1 : b (y p) = p := by rw [hp, hyx, hyv]
    calc y p = b (b (b (y p))) := (hb3' _).symm
      _ = b (b p) := by rw [h1]
  have hxp : x p = q := rfl
  have hyq : y q = b q := by
    have h1 : b (y q) = b (b q) := by
      rw [hq, hyx, ← hp, hyp, ← hbx', ← hbx', hxp]
    calc y q = b (b (b (y q))) := (hb3' _).symm
      _ = b (b (b (b q))) := by rw [h1]
      _ = b q := by rw [hb3']
  have e1 : v * p * q = 1 := hxv
  have e2 : v * b (b p) * b q = 1 := by
    have := congrArg y e1
    rwa [map_mul, map_mul, map_one, hyv, hyp, hyq] at this
  have e3 : v * b p * b (b q) = 1 := by
    have := congrArg y e2
    rw [map_mul, map_mul, map_one, hyv, ← hby', ← hby', hyp, ← hby', hyq] at this
    rwa [hb3'] at this
  set u := v * b v * b (b v) with hu
  have hbu : b u = u := by
    rw [hu, map_mul, map_mul, hb3']
    rw [mul_comm (b v * b (b v)) v, ← mul_assoc]
  have hxu : x u * x (x u) = v := by
    have h1 : x u = p * b (b p) * b p := by
      rw [hu, map_mul, map_mul, ← hbx', ← hbx', ← hbx', ← hp]
      rw [mul_assoc p, mul_comm (b p), ← mul_assoc]
    have h2 : x (x u) = q * b (b q) * b q := by
      rw [h1, map_mul, map_mul, ← hbx', ← hbx', hxp]
    have h3 : v * (x u * x (x u)) = 1 := by
      rw [h2, h1]
      have h4 : v * (p * b (b p) * b p * (q * b (b q) * b q)) * (v * v) =
          (v * p * q) * (v * b (b p) * b q) * (v * b p * b (b q)) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
      rw [e1, e2, e3, ← sq, hW] at h4
      simpa using h4
    calc x u * x (x u) = v⁻¹ := eq_inv_of_mul_eq_one_right h3
      _ = v := hinv v
  rw [← hxu, map_mul, hbx', hbx', hbx', hbu]

end CFSG.Quasithin.H13.L32A.T53

end
