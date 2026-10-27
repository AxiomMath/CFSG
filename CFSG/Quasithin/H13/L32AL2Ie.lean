module

public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.QuasithinUnique

variable {X : Type*} [Group X]

theorem mem_normalizer_of_forall_conj_mem [Finite X] {Λ : Subgroup X} {g : X}
    (h : ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) : g ∈ Subgroup.normalizer (Λ : Set X) := by
  have hle : Λ.map (MulAut.conj g).toMonoidHom ≤ Λ := by
    rintro _ ⟨l, hl, rfl⟩
    exact h l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm)

theorem le_of_isSylowTwoOf_of_le [Finite X] {U Y R : Subgroup X} (hU : IsSylowTwoOf U Y)
    (hRY : R ≤ Y) (hR : IsPGroup 2 R) (hUR : U ≤ R) : R ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : U.relIndex R * R.relIndex Y = U.relIndex Y :=
    Subgroup.relIndex_mul_relIndex U R Y hUR hRY
  obtain ⟨n, hn⟩ := hR.index (U.subgroupOf R)
  have h4 : U.relIndex R = 2 ^ n := hn
  by_contra hne
  have h6 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h4
    exact hne (Subgroup.relIndex_eq_one.mp h4)
  apply hU.2.2
  change 2 ∣ U.relIndex Y
  rw [← h1, h4]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 h6) _

theorem eq_one_of_mem_of_inf_eq_bot {K C : Subgroup X} (hKC : K ⊓ C = ⊥) {a : X} (haK : a ∈ K)
    (haC : a ∈ C) : a = 1 := by
  have h : a ∈ K ⊓ C := ⟨haK, haC⟩
  rwa [hKC, Subgroup.mem_bot] at h

theorem eq_and_eq_of_mul_eq_mul {K C : Subgroup X} (hKC : K ⊓ C = ⊥) {k k' c c' : X}
    (hk : k ∈ K) (hk' : k' ∈ K) (hc : c ∈ C) (hc' : c' ∈ C) (h : k * c = k' * c') :
    k = k' ∧ c = c' := by
  have h1 : k'⁻¹ * k = c' * c⁻¹ := by
    calc k'⁻¹ * k = k'⁻¹ * (k * c) * c⁻¹ := by group
      _ = k'⁻¹ * (k' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have h2 : k'⁻¹ * k = 1 :=
    eq_one_of_mem_of_inf_eq_bot hKC (mul_mem (inv_mem hk') hk) (h1 ▸ mul_mem hc' (inv_mem hc))
  have hkk : k = k' := by
    calc k = k' * (k'⁻¹ * k) := by group
      _ = k' := by rw [h2, mul_one]
  subst hkk
  exact ⟨rfl, mul_left_cancel h⟩

theorem pow_eq_one_and_of_mul {K C : Subgroup X} (hKC : K ⊓ C = ⊥)
    (hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a) {k c : X} (hk : k ∈ K) (hc : c ∈ C) {n : ℕ}
    (h : (k * c) ^ n = 1) : k ^ n = 1 ∧ c ^ n = 1 := by
  rw [(show Commute k c from hcomm k hk c hc).mul_pow] at h
  exact eq_and_eq_of_mul_eq_mul hKC (pow_mem hk n) (one_mem K) (pow_mem hc n) (one_mem C)
    (h.trans (mul_one 1).symm)

theorem exists_mul_of_mem_sup_comm {K C : Subgroup X} (hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a)
    {g : X} (hg : g ∈ K ⊔ C) : ∃ k ∈ K, ∃ c ∈ C, g = k * c := by
  have hCN : C ≤ Subgroup.normalizer (K : Set X) := fun b hb =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha b hb)
  exact (F1.mem_sup_iff_exists_mul_of_normalizes hCN).1 hg

theorem commute_and_of_mul {K C : Subgroup X} (hKC : K ⊓ C = ⊥)
    (hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a) {k k' c c' : X} (hk : k ∈ K) (hk' : k' ∈ K)
    (hc : c ∈ C) (hc' : c' ∈ C) (h : k * c * (k' * c') = k' * c' * (k * c)) :
    k * k' = k' * k ∧ c * c' = c' * c := by
  have e1 : k * c * (k' * c') = k * k' * (c * c') := by
    rw [mul_assoc k c, ← mul_assoc c k' c', ← hcomm k' hk' c hc]
    group
  have e2 : k' * c' * (k * c) = k' * k * (c' * c) := by
    rw [mul_assoc k' c', ← mul_assoc c' k c, ← hcomm k hk c' hc']
    group
  rw [e1, e2] at h
  exact eq_and_eq_of_mul_eq_mul hKC (mul_mem hk hk') (mul_mem hk' hk) (mul_mem hc hc')
    (mul_mem hc' hc) h

theorem zpow_pow_three_eq_one {a : X} (ha : a ^ 3 = 1) (j : ℤ) : (a ^ j) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

section Key

variable [Finite X] {K C Λ Q Θ : Subgroup X} {x : X}

theorem mem_of_mul_mem (hKC : K ⊓ C = ⊥) (hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a)
    (hΘ2 : IsPGroup 2 Θ) (hSyl : IsSylowTwoOf (Θ ⊓ K) K) {k c : X} (hk : k ∈ K) (hc : c ∈ C)
    (hkc : k * c ∈ Θ) : k ∈ Θ := by
  let R : Subgroup X :=
    { carrier := {a | a ∈ K ∧ ∃ b ∈ C, a * b ∈ Θ}
      one_mem' := ⟨one_mem K, 1, one_mem C, by simp⟩
      mul_mem' := by
        rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
        refine ⟨mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        have e : a * a' * (b * b') = a * b * (a' * b') := by
          rw [mul_assoc a a', ← mul_assoc a' b b', hcomm a' ha' b hb]
          group
        rw [e]
        exact mul_mem hab hab'
      inv_mem' := by
        rintro a ⟨ha, b, hb, hab⟩
        refine ⟨inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        have e : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
          rw [mul_inv_rev]
          exact hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
        rw [e]
        exact inv_mem hab }
  have hRK : R ≤ K := fun a ha => ha.1
  have hR2 : IsPGroup 2 R := by
    rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨n, hn⟩ := hΘ2 ⟨a * b, hab⟩
    have hn' : (a * b) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨n, Subtype.ext (by simpa using (pow_eq_one_and_of_mul hKC hcomm ha hb hn').1)⟩
  have hSR : Θ ⊓ K ≤ R := fun a ha => ⟨ha.2, 1, one_mem C, by simpa using ha.1⟩
  exact (le_of_isSylowTwoOf_of_le hSyl hRK hR2 hSR ⟨hk, c, hc, hkc⟩).1

omit [Finite X] in
theorem le_of_mem_of_cubes (hKC : K ⊓ C = ⊥) (hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a)
    (hQ2 : IsPGroup 2 Q) (hQKC : Q ≤ K ⊔ C) (hxQ : x ∈ Subgroup.normalizer (Q : Set X))
    (hΛQx : Λ ≤ Q ⊔ Subgroup.zpowers x) (hΛ3 : Λ ≤ Subgroup.closure {z | z ∈ Λ ∧ z ^ 3 = 1})
    (hxK : x ∈ K) : Λ ≤ K := by
  refine hΛ3.trans ((Subgroup.closure_le K).mpr ?_)
  rintro z ⟨hzΛ, hz3⟩
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set X) :=
    Subgroup.zpowers_le.mpr hxQ
  obtain ⟨q, hq, w, hw, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hzN).1 (hΛQx hzΛ)
  obtain ⟨qk, hqk, qc, hqc, rfl⟩ := exists_mul_of_mem_sup_comm hcomm (hQKC hq)
  have hwK : w ∈ K := Subgroup.zpowers_le.mpr hxK hw
  have e : qk * qc * w = qk * w * qc := by
    rw [mul_assoc, (hcomm w hwK qc hqc).symm, ← mul_assoc]
  rw [e] at hz3 ⊢
  have h3 := (pow_eq_one_and_of_mul hKC hcomm (mul_mem hqk hwK) hqc hz3).2
  obtain ⟨n, hn⟩ := hQ2 ⟨qk * qc, hq⟩
  have hn' : (qk * qc) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 := (pow_eq_one_and_of_mul hKC hcomm hqk hqc hn').2
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have h1 : orderOf qc = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one h2)
  rw [orderOf_eq_one_iff.mp h1, mul_one]
  exact mul_mem hqk hwK

theorem comp_mem_normalizer (hKC : K ⊓ C = ⊥) (hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a)
    (hΘ2 : IsPGroup 2 Θ) (hSyl : IsSylowTwoOf (Θ ⊓ K) K)
    (hΘΛ : Θ ≤ Subgroup.normalizer (Λ : Set X)) (hQΘ : Q ≤ Θ) (hQΛ : Q ≤ Λ) (hxΛ : x ∈ Λ)
    (hxQ : x ∈ Subgroup.normalizer (Q : Set X)) (hΛQx : Λ ≤ Q ⊔ Subgroup.zpowers x)
    (hQKC : Q ≤ K ⊔ C) {k c : X} (hk : k ∈ K) (hc : c ∈ C) (hx : x = k * c) :
    k ∈ Subgroup.normalizer (Λ : Set X) := by
  have hkx : k * x = x * k := by rw [hx, mul_assoc, ← hcomm k hk c hc]
  refine mem_normalizer_of_forall_conj_mem fun l hl => ?_
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set X) :=
    Subgroup.zpowers_le.mpr hxQ
  obtain ⟨q, hq, w, hw, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hzN).1 (hΛQx hl)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hkxn : k * x ^ n * k⁻¹ = x ^ n := by
    rw [(Commute.zpow_right (show Commute k x from hkx) n).eq, mul_inv_cancel_right]
  obtain ⟨qk, hqk, qc, hqc, rfl⟩ := exists_mul_of_mem_sup_comm hcomm (hQKC hq)
  have hqN := hΘΛ (mem_of_mul_mem hKC hcomm hΘ2 hSyl hqk hqc (hQΘ hq))
  have hcq : c * qk = qk * c := (hcomm qk hqk c hc).symm
  have hkqc : k * qc = qc * k := hcomm k hk qc hqc
  have e : k * (qk * qc) * k⁻¹ = x * (qk * x⁻¹ * qk⁻¹) * (qk * qc) := by
    rw [hx]
    calc k * (qk * qc) * k⁻¹ = k * qk * k⁻¹ * (k * qc * k⁻¹) := by group
      _ = k * qk * k⁻¹ * qc := by rw [hkqc, mul_inv_cancel_right]
      _ = k * (c * qk) * c⁻¹ * k⁻¹ * qc := by rw [hcq]; group
      _ = k * c * (qk * (k * c)⁻¹ * qk⁻¹) * (qk * qc) := by group
  have h1 : k * (qk * qc) * k⁻¹ ∈ Λ := by
    rw [e]
    refine mul_mem (mul_mem hxΛ ?_) (hQΛ hq)
    exact (Subgroup.mem_normalizer_iff.mp hqN _).mp (inv_mem hxΛ)
  have e2 : k * (qk * qc * x ^ n) * k⁻¹ = k * (qk * qc) * k⁻¹ * (k * x ^ n * k⁻¹) := by group
  rw [e2, hkxn]
  exact mul_mem h1 (zpow_mem hxΛ n)

theorem mem_normalizer_of_commute (hKC : K ⊓ C = ⊥) (hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a)
    (h3K : ∀ a ∈ K, ∀ a' ∈ K, a ^ 3 = 1 → a' ^ 3 = 1 → a * a' = a' * a →
      a = 1 ∨ a' ∈ Subgroup.zpowers a)
    (h3C : ∀ b ∈ C, ∀ b' ∈ C, b ^ 3 = 1 → b' ^ 3 = 1 → b * b' = b' * b →
      b = 1 ∨ b' ∈ Subgroup.zpowers b)
    (hΘ2 : IsPGroup 2 Θ) (hSyl : IsSylowTwoOf (Θ ⊓ K) K)
    (hΘΛ : Θ ≤ Subgroup.normalizer (Λ : Set X)) (hQ2 : IsPGroup 2 Q) (hQΘ : Q ≤ Θ) (hQΛ : Q ≤ Λ)
    (hxΛ : x ∈ Λ) (hxQ : x ∈ Subgroup.normalizer (Q : Set X)) (hΛQx : Λ ≤ Q ⊔ Subgroup.zpowers x)
    (hΛ3 : Λ ≤ Subgroup.closure {z | z ∈ Λ ∧ z ^ 3 = 1}) (hΛKC : Λ ≤ K ⊔ C) (hx3 : x ^ 3 = 1)
    {y : X} (hyKC : y ∈ K ⊔ C) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) :
    y ∈ Subgroup.normalizer (Λ : Set X) := by
  have hΛN : Λ ≤ Subgroup.normalizer (Λ : Set X) := Subgroup.le_normalizer
  have hQKC : Q ≤ K ⊔ C := hQΛ.trans hΛKC
  have hcomm' : ∀ b ∈ C, ∀ a ∈ K, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hCK : C ⊓ K = ⊥ := by rw [inf_comm]; exact hKC
  have hQCK : Q ≤ C ⊔ K := by rw [sup_comm]; exact hQKC
  have hCnorm : ∀ {b : X}, b ∈ C → Λ ≤ K → b ∈ Subgroup.normalizer (Λ : Set X) := fun hb hle =>
    mem_normalizer_of_forall_conj_mem fun l hl => by
      rw [← hcomm l (hle hl) _ hb, mul_inv_cancel_right]
      exact hl
  have hKnorm : ∀ {a : X}, a ∈ K → Λ ≤ C → a ∈ Subgroup.normalizer (Λ : Set X) := fun ha hle =>
    mem_normalizer_of_forall_conj_mem fun l hl => by
      rw [hcomm _ ha l (hle hl), mul_inv_cancel_right]
      exact hl
  obtain ⟨k, hk, c, hc, hxkc⟩ := exists_mul_of_mem_sup_comm hcomm (hΛKC hxΛ)
  obtain ⟨k', hk', c', hc', rfl⟩ := exists_mul_of_mem_sup_comm hcomm hyKC
  rw [hxkc] at hxy hx3
  obtain ⟨hkk, hcc⟩ := commute_and_of_mul hKC hcomm hk hk' hc hc' hxy
  obtain ⟨hk3, hc3⟩ := pow_eq_one_and_of_mul hKC hcomm hk hc hx3
  obtain ⟨hk'3, hc'3⟩ := pow_eq_one_and_of_mul hKC hcomm hk' hc' hy3
  rcases h3C c hc c' hc' hc3 hc'3 hcc with rfl | hz
  ·
    rw [mul_one] at hxkc
    have hle : Λ ≤ K := le_of_mem_of_cubes hKC hcomm hQ2 hQKC hxQ hΛQx hΛ3
      (by rw [hxkc]; exact hk)
    rcases h3K k hk k' hk' hk3 hk'3 hkk with rfl | hk'z
    ·
      have hleC : Λ ≤ C := le_of_mem_of_cubes hCK hcomm' hQ2 hQCK hxQ hΛQx hΛ3
        (by rw [hxkc]; exact one_mem C)
      have hbot : Λ = ⊥ := le_bot_iff.mp ((le_inf hle hleC).trans hKC.le)
      rw [hbot]
      exact mem_normalizer_of_forall_conj_mem fun l hl => by
        rw [Subgroup.mem_bot] at hl ⊢
        rw [hl, mul_one, mul_inv_cancel]
    · rw [← hxkc] at hk'z
      exact mul_mem (hΛN (Subgroup.zpowers_le.mpr hxΛ hk'z)) (hCnorm hc' hle)
  · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hkcj : (k * c) ^ (j : ℤ) = k ^ j * c ^ j :=
      (show Commute k c from hcomm k hk c hc).mul_zpow j
    have hy : k' * c ^ j = (k' * (k ^ j)⁻¹) * (k * c) ^ j := by
      rw [hkcj]
      group
    rw [hy, ← hxkc]
    refine mul_mem ?_ (hΛN (zpow_mem hxΛ j))
    have hk''K : k' * (k ^ j)⁻¹ ∈ K := mul_mem hk' (inv_mem (zpow_mem hk j))
    have hk''3 : (k' * (k ^ j)⁻¹) ^ 3 = 1 := by
      have hc1 : Commute k' (k ^ j)⁻¹ :=
        (Commute.zpow_right (show Commute k' k from hkk.symm) j).inv_right
      rw [hc1.mul_pow, hk'3, one_mul, inv_pow, zpow_pow_three_eq_one hk3 j, inv_one]
    have hk''c : k * (k' * (k ^ j)⁻¹) = (k' * (k ^ j)⁻¹) * k :=
      ((show Commute k k' from hkk).mul_right
        ((Commute.zpow_right (Commute.refl k) j).inv_right)).eq
    rcases h3K k hk _ hk''K hk3 hk''3 hk''c with rfl | hz'
    ·
      rw [one_mul] at hxkc
      exact hKnorm hk''K (le_of_mem_of_cubes hCK hcomm' hQ2 hQCK hxQ hΛQx hΛ3
        (by rw [hxkc]; exact hc))
    ·
      have hkN := comp_mem_normalizer hKC hcomm hΘ2 hSyl hΘΛ hQΘ hQΛ hxΛ hxQ hΛQx hQKC hk hc hxkc
      exact Subgroup.zpowers_le.mpr hkN hz'

end Key

end CFSG.Quasithin.H13.L32A.L2
