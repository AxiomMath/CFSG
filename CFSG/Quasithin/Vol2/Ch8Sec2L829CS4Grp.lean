module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

section Rank

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_three_of_elemAb9 {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian 3 E) (h9 : Nat.card E = 9) : 2 ≤ pRank 3 H := by
  unfold pRank
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEH, hE, ?_⟩
  · rintro k ⟨E', -, -, hE'⟩
    have h1 : 3 ^ k ≤ Nat.card G := by
      rw [← hE']
      exact Subgroup.card_le_card_group E'
    exact le_trans (Nat.lt_pow_self (by norm_num)).le h1
  · rw [h9]
    norm_num

end Rank

section TwoKernel

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAb9_of_two_kernel (P Y : Subgroup G) (hY : IsPGroup 2 Y) (hYP : Y ≤ P)
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Y)
    (hcube : ∀ p ∈ P, p ^ 3 ∈ Y) (hcard : Nat.card P = 9 * Nat.card Y) :
    ∃ F : Subgroup G, F ≤ P ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) 3 (n := 2)
    ⟨Nat.card Y, by rw [hcard]; norm_num⟩
  set F : Subgroup G := S.map P.subtype with hFdef
  have hFP : F ≤ P := Subgroup.map_subtype_le S
  have hFcard : Nat.card F = 9 := by
    rw [hFdef, Subgroup.card_map_of_injective P.subtype_injective, hS]
    norm_num
  have hFY : ∀ g ∈ F, g ∈ Y → g = 1 := by
    intro g hgF hgY
    have h1 : orderOf g ∣ 9 := by
      have h := orderOf_dvd_natCard (⟨g, hgF⟩ : F)
      rw [← Subgroup.orderOf_coe, hFcard] at h
      exact h
    obtain ⟨k, hk⟩ := hY ⟨g, hgY⟩
    have hk' : g ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have h3 : orderOf g ∣ Nat.gcd 9 (2 ^ k) := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hFc : ∀ g ∈ F, ∀ h ∈ F, g * h * g⁻¹ * h⁻¹ ∈ F := fun g hg h hh =>
    F.mul_mem (F.mul_mem (F.mul_mem hg hh) (F.inv_mem hg)) (F.inv_mem hh)
  refine ⟨F, hFP, ⟨?_, ?_⟩, hFcard⟩
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = 1 :=
      hFY _ (hFc _ a.2 _ b.2) (hcomm _ (hFP a.2) _ (hFP b.2))
    have : (a : G) * b = b * a := by
      calc (a : G) * b = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by group
        _ = (b : G) * (a : G) := by rw [hc, one_mul]
    simpa using this
  · intro x hx
    have h3 : x ^ 3 ∈ Y := hcube x (hFP hx)
    have h4 : x ^ 3 ∈ F := F.pow_mem hx 3
    exact hFY _ h4 h3

end TwoKernel

section Cube

theorem comm_rel {A : Type} [Group A] (a b : A) : b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by
  group

theorem cube_mul_central {A : Type} [Group A] {x y z : A} (hz : ∀ a : A, a * z = z * a)
    (hz3 : z * z * z = 1) (hyx : y * x = z * (x * y)) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hzl : ∀ a b : A, a * (z * b) = z * (a * b) := fun a b => by
    rw [← mul_assoc, hz a, mul_assoc]
  have hzz : ∀ a : A, a * (z * z) = (z * z) * a := fun a => by
    calc a * (z * z) = (a * z) * z := by simp only [mul_assoc]
      _ = (z * a) * z := by rw [hz a]
      _ = z * (a * z) := by simp only [mul_assoc]
      _ = z * (z * a) := by rw [hz a]
      _ = (z * z) * a := by simp only [mul_assoc]
  have hzzl : ∀ a b : A, a * (z * z * b) = z * z * (a * b) := fun a b => by
    rw [← mul_assoc, hzz, mul_assoc]
  have e2 : (x * y) ^ 2 = z * (x * x * (y * y)) := by
    calc (x * y) ^ 2 = x * y * (x * y) := by simp only [sq]
      _ = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (z * (x * y)) * y := by rw [hyx]
      _ = z * (x * (x * y)) * y := by rw [hzl]
      _ = z * (x * x * (y * y)) := by simp only [mul_assoc]
  have e3 : y * y * x = z * z * (x * (y * y)) := by
    calc y * y * x = y * (y * x) := by simp only [mul_assoc]
      _ = y * (z * (x * y)) := by rw [hyx]
      _ = z * (y * (x * y)) := by rw [hzl]
      _ = z * ((y * x) * y) := by simp only [mul_assoc]
      _ = z * ((z * (x * y)) * y) := by rw [hyx]
      _ = z * z * (x * (y * y)) := by simp only [mul_assoc]
  calc (x * y) ^ 3 = (x * y) ^ 2 * (x * y) := by simp only [pow_succ, pow_zero, one_mul]
    _ = z * (x * x * (y * y)) * (x * y) := by rw [e2]
    _ = z * (x * x * (y * y * x) * y) := by simp only [mul_assoc]
    _ = z * (x * x * (z * z * (x * (y * y))) * y) := by rw [e3]
    _ = z * (z * z * (x * x * (x * (y * y))) * y) := by rw [hzzl]
    _ = z * (z * z) * (x * x * (x * (y * y)) * y) := by simp only [mul_assoc]
    _ = z * z * z * (x * x * (x * (y * y)) * y) := by simp only [mul_assoc]
    _ = x ^ 3 * y ^ 3 := by
      rw [hz3, one_mul]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem isMulCommutative_sup_of_commute {A : Type} [Group A] {P Q : Subgroup A} [P.Normal]
    (hP : IsMulCommutative P) (hQ : IsMulCommutative Q)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) : IsMulCommutative ↥(P ⊔ Q) := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup_of_normal_left.mp a.2
  obtain ⟨p', hp', q', hq', hpq'⟩ := Subgroup.mem_sup_of_normal_left.mp b.2
  have hcp : p * p' = p' * p := by
    have := isMulCommutative_iff.mp hP
    exact congrArg (fun z : P => (z : A)) (this ⟨p, hp⟩ ⟨p', hp'⟩) |>.trans rfl
  have hcq : q * q' = q' * q := by
    have := isMulCommutative_iff.mp hQ
    exact congrArg (fun z : Q => (z : A)) (this ⟨q, hq⟩ ⟨q', hq'⟩) |>.trans rfl
  simp only [Subgroup.coe_mul]
  rw [← hpq, ← hpq']
  calc p * q * (p' * q') = p * (q * p') * q' := by simp only [mul_assoc]
    _ = p * (p' * q) * q' := by rw [← hPQ p' hp' q hq]
    _ = (p * p') * (q * q') := by simp only [mul_assoc]
    _ = (p' * p) * (q' * q) := by rw [hcp, hcq]
    _ = p' * (p * q') * q := by simp only [mul_assoc]
    _ = p' * (q' * p) * q := by rw [hPQ p hp q' hq']
    _ = p' * q' * (p * q) := by simp only [mul_assoc]

end Cube

section Comap

theorem card_comap_mk' {A : Type} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (F : Subgroup (A ⧸ N)) : Nat.card (F.comap (QuotientGroup.mk' N)) = Nat.card F * Nat.card N := by
  have hidx : (F.comap (QuotientGroup.mk' N)).index = F.index :=
    Subgroup.index_comap_of_surjective F (QuotientGroup.mk'_surjective N)
  have h1 := Subgroup.card_mul_index (F.comap (QuotientGroup.mk' N))
  have h2 := Subgroup.card_mul_index F
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : F.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos)
  rw [hidx] at h1
  calc Nat.card (F.comap (QuotientGroup.mk' N)) * F.index = Nat.card A := h1
    _ = Nat.card (A ⧸ N) * Nat.card N := h3
    _ = Nat.card F * F.index * Nat.card N := by rw [h2]
    _ = Nat.card F * Nat.card N * F.index := by ring

end Comap

section Psi

theorem exists_elemAb9_of_cube {A : Type} [Group A] [Finite A] (r : A) (hr3 : orderOf r = 3)
    (hrc : ∀ a : A, a * r = r * a) (B : Subgroup A) (hrB : r ∈ B) (hB : Nat.card B = 27)
    (hcube : ∀ b ∈ B, b ^ 3 ∈ Subgroup.zpowers r)
    (hcomm : ∀ b ∈ B, ∀ c ∈ B, b * c * b⁻¹ * c⁻¹ ∈ Subgroup.zpowers r) :
    ∃ F : Subgroup A, IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard_z : Nat.card (Subgroup.zpowers r) = 3 := by rw [Nat.card_zpowers, hr3]
  have hzcen : ∀ n ∈ Subgroup.zpowers r, ∀ a : A, a * n = n * a := by
    intro n hn a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact Commute.zpow_right (show Commute a r from hrc a) k
  have hzcube : ∀ n ∈ Subgroup.zpowers r, n ^ 3 = 1 := by
    intro n hn
    have h1 : orderOf n ∣ orderOf r := orderOf_dvd_of_mem_zpowers hn
    rw [hr3] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hnorm : (Subgroup.zpowers r).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgn : g * n * g⁻¹ = n := by
      rw [hzcen n hn g, mul_inv_cancel_right]
    rw [hgn]
    exact hn
  haveI := hnorm
  let φ : B →* A :=
    { toFun := fun b => (b : A) ^ 3
      map_one' := by simp
      map_mul' := fun b c => by
        have hc := hcomm b.1 b.2 c.1 c.2
        have hyx : (c : A) * (b : A) = (b * c * b⁻¹ * c⁻¹ : A)⁻¹ * ((b : A) * (c : A)) :=
          comm_rel (b : A) (c : A)
        simp only [Subgroup.coe_mul]
        refine cube_mul_central (z := (b * c * b⁻¹ * c⁻¹ : A)⁻¹) ?_ ?_ hyx
        · intro a
          exact (Commute.inv_right (show Commute a (b * c * b⁻¹ * c⁻¹ : A) from
            hzcen _ hc a)).eq
        · have h3 : (b * c * b⁻¹ * c⁻¹ : A) ^ 3 = 1 := hzcube _ hc
          rw [← pow_three', inv_pow, h3, inv_one] }
  have hφr : φ.range ≤ Subgroup.zpowers r := by
    rintro x ⟨b, rfl⟩
    exact hcube b.1 b.2
  have hker_range : Nat.card φ.ker * Nat.card φ.range = 27 := by
    rw [Subgroup.card_ker_mul_card_range, hB]
  have hrange_le : Nat.card φ.range ≤ 3 := by
    rw [← hcard_z]
    exact Subgroup.card_le_of_le hφr
  have hker_ge : 9 ≤ Nat.card φ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range ≤ 8 * 3 :=
      Nat.mul_le_mul (by omega) hrange_le
    omega
  obtain ⟨w, hwB, hwcube, hwr⟩ : ∃ w : A, w ∈ B ∧ w ^ 3 = 1 ∧ w ∉ Subgroup.zpowers r := by
    by_contra hno
    push Not at hno
    let X : Subgroup A := φ.ker.map B.subtype
    have hXle : X ≤ Subgroup.zpowers r := by
      rintro x ⟨b, hb, rfl⟩
      have hb' : φ b = 1 := hb
      have : (b : A) ^ 3 = 1 := hb'
      have hmem := hno b.1 b.2 this
      exact hmem
    have hXcard : Nat.card X = Nat.card φ.ker := by
      rw [Subgroup.card_map_of_injective B.subtype_injective]
    have := Subgroup.card_le_of_le hXle
    omega
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hwr (Subgroup.one_mem _)
  have hw3 : orderOf w = 3 := by
    have h1 : orderOf w ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hwcube
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hwc : ∀ n ∈ Subgroup.zpowers r, ∀ m ∈ Subgroup.zpowers w, n * m = m * n := by
    intro n hn m _
    exact (hzcen n hn m).symm
  set P : Subgroup A := Subgroup.zpowers r with hPdef
  set Q : Subgroup A := Subgroup.zpowers w with hQdef
  haveI : P.Normal := hnorm
  have hPc : IsMulCommutative ↥P := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self r i j).eq
  have hQc : IsMulCommutative ↥Q := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self w i j).eq
  have hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := fun p hp q _ => (hzcen p hp q).symm
  haveI hFc : IsMulCommutative ↥(P ⊔ Q) := isMulCommutative_sup_of_commute hPc hQc hPQ
  have hPQint : ∀ x ∈ P, x ∈ Q → x = 1 := by
    intro x hxP hxQ
    by_contra hx1
    have hxo : orderOf x = 3 := by
      have h1 : orderOf x ∣ 3 := by
        rw [← hr3]
        exact orderOf_dvd_of_mem_zpowers hxP
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hPeq : Subgroup.zpowers x = P := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.mpr hxP
      · rw [hcard_z, Nat.card_zpowers, hxo]
    have hQeq : Subgroup.zpowers x = Q := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.mpr hxQ
      · have hQc' : Nat.card Q = 3 := by rw [hQdef, Nat.card_zpowers, hw3]
        rw [hQc', Nat.card_zpowers, hxo]
    have hwP : w ∈ P := by
      rw [← hPeq, hQeq]
      exact Subgroup.mem_zpowers w
    exact hwr hwP
  let e : (P × Q) → ↥(P ⊔ Q) := fun pq =>
    ⟨pq.1.1 * pq.2.1, Subgroup.mul_mem_sup pq.1.2 pq.2.2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ h
      have h' : p * q = p' * q' := congrArg Subtype.val h
      have hx : p'⁻¹ * p = q' * q⁻¹ := by
        calc p'⁻¹ * p = p'⁻¹ * (p * q) * q⁻¹ := by group
          _ = p'⁻¹ * (p' * q') * q⁻¹ := by rw [h']
          _ = q' * q⁻¹ := by group
      have hPx : p'⁻¹ * p ∈ P := P.mul_mem (P.inv_mem hp') hp
      have hQx : q' * q⁻¹ ∈ Q := Q.mul_mem hq' (Q.inv_mem hq)
      have h1 : p'⁻¹ * p = 1 := hPQint _ hPx (by rw [hx]; exact hQx)
      have h2 : p = p' := (inv_mul_eq_one.mp h1).symm
      have h3 : q' * q⁻¹ = 1 := by rw [← hx, h1]
      have h4 : q = q' := (mul_inv_eq_one.mp h3).symm
      subst h2
      subst h4
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), Subtype.ext hpq⟩
  refine ⟨P ⊔ Q, ⟨hFc, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hcomm' : Commute p q := hPQ p hp q hq
    have hp3 : p ^ 3 = 1 := hzcube p hp
    have hq3 : q ^ 3 = 1 := by
      have h1 : orderOf q ∣ orderOf w := orderOf_dvd_of_mem_zpowers hq
      rw [hw3] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    rw [← hpq, hcomm'.mul_pow, hp3, hq3, one_mul]
  · rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_prod]
    have hQcard : Nat.card Q = 3 := by rw [hQdef, Nat.card_zpowers, hw3]
    rw [hcard_z, hQcard]

end Psi

section Central

theorem normal_zpowers_of_central {A : Type} [Group A] (r : A) (hrc : ∀ a : A, a * r = r * a) :
    (Subgroup.zpowers r).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hgk : g * r ^ k * g⁻¹ = r ^ k := by
    rw [(Commute.zpow_right (show Commute g r from hrc g) k).eq, mul_inv_cancel_right]
  rw [hgk]
  exact hn

theorem exists_elemAb9_of_central_kernel (V : Type) [Group V] [Finite V]
    (hV : IsElemAbelian 3 (⊤ : Subgroup V)) (hV9 : Nat.card V = 9) :
    ∀ (m : ℕ) (A : Type) [Group A] [Finite A] (f : A →* V), Nat.card A = m →
      Function.Surjective f → (∀ z ∈ f.ker, ∀ a : A, a * z = z * a) → IsPGroup 3 f.ker →
      ∃ F : Subgroup A, IsElemAbelian 3 F ∧ Nat.card F = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A _ _ f hAm hsurj hcen hP
  by_cases hker : f.ker = ⊥
  ·
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    let e : A ≃* V := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
    refine ⟨⊤, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      apply hinj
      show f ((a : A) * (b : A)) = f ((b : A) * (a : A))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        (isMulCommutative_iff.mp hV.1 ⟨f a, Subgroup.mem_top _⟩ ⟨f b, Subgroup.mem_top _⟩)
    · intro x _
      apply hinj
      rw [map_pow, map_one]
      exact hV.2 _ (Subgroup.mem_top _)
    · rw [Subgroup.card_top, Nat.card_congr e.toEquiv, hV9]
  ·
    obtain ⟨r, hrK, hr3⟩ : ∃ r ∈ f.ker, orderOf r = 3 := by
      have hcard1 : Nat.card f.ker ≠ 1 := fun h => hker ((Subgroup.eq_bot_iff_card _).mpr h)
      have hdvd : 3 ∣ Nat.card f.ker := by
        rcases IsPGroup.card_eq_or_dvd hP with h | h
        · exact absurd h hcard1
        · exact h
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      refine ⟨x.1, x.2, ?_⟩
      rw [Subgroup.orderOf_coe, hx]
    have hrc : ∀ a : A, a * r = r * a := fun a => hcen r hrK a
    have hzN : Subgroup.zpowers r ≤ f.ker := Subgroup.zpowers_le.mpr hrK
    haveI := normal_zpowers_of_central r hrc
    let f' : A ⧸ Subgroup.zpowers r →* V := QuotientGroup.lift (Subgroup.zpowers r) f hzN
    have hf'mk : ∀ a : A, f' (a : A ⧸ Subgroup.zpowers r) = f a := fun a => rfl
    have hf'surj : Function.Surjective f' := by
      intro v
      obtain ⟨a, rfl⟩ := hsurj v
      exact ⟨(a : A ⧸ Subgroup.zpowers r), hf'mk a⟩
    have hcen' : ∀ z ∈ f'.ker, ∀ a : A ⧸ Subgroup.zpowers r, a * z = z * a := by
      intro z hz a
      obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
      have hz₀ : z₀ ∈ f.ker := by
        have h1 : f' (z₀ : A ⧸ Subgroup.zpowers r) = 1 := hz
        rw [hf'mk] at h1
        exact h1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcen z₀ hz₀ a₀]
    have hP' : IsPGroup 3 f'.ker := by
      intro y
      obtain ⟨z, hz⟩ := y
      obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective z
      have hz₀ : z₀ ∈ f.ker := by
        have h1 : f' (z₀ : A ⧸ Subgroup.zpowers r) = 1 := hz
        rw [hf'mk] at h1
        exact h1
      obtain ⟨k, hk⟩ := hP ⟨z₀, hz₀⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : z₀ ^ 3 ^ k = 1 := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← QuotientGroup.mk_pow, hk']
      rfl
    have hcardq : Nat.card A = Nat.card (A ⧸ Subgroup.zpowers r) * 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers r),
        Nat.card_zpowers, hr3]
    have hqpos : 0 < Nat.card (A ⧸ Subgroup.zpowers r) := Nat.card_pos
    have hlt : Nat.card (A ⧸ Subgroup.zpowers r) < m := by omega
    obtain ⟨F₁, hF₁, hF₁c⟩ :=
      ih _ hlt (A ⧸ Subgroup.zpowers r) f' rfl hf'surj hcen' hP'
    let B : Subgroup A := F₁.comap (QuotientGroup.mk' (Subgroup.zpowers r))
    have hB : Nat.card B = 27 := by
      rw [card_comap_mk', hF₁c, Nat.card_zpowers, hr3]
    have hrB : r ∈ B := by
      have h1 : (QuotientGroup.mk' (Subgroup.zpowers r)) r = 1 :=
        (QuotientGroup.eq_one_iff r).mpr (Subgroup.mem_zpowers r)
      exact Subgroup.mem_comap.mpr (by rw [h1]; exact F₁.one_mem)
    have hcube : ∀ b ∈ B, b ^ 3 ∈ Subgroup.zpowers r := by
      intro b hb
      have h1 : (QuotientGroup.mk' (Subgroup.zpowers r) b) ^ 3 = 1 :=
        hF₁.2 _ (Subgroup.mem_comap.mp hb)
      rw [← map_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hcomm : ∀ b ∈ B, ∀ c ∈ B, b * c * b⁻¹ * c⁻¹ ∈ Subgroup.zpowers r := by
      intro b hb c hc
      have hcomm' := isMulCommutative_iff.mp hF₁.1
        ⟨QuotientGroup.mk' (Subgroup.zpowers r) b, Subgroup.mem_comap.mp hb⟩
        ⟨QuotientGroup.mk' (Subgroup.zpowers r) c, Subgroup.mem_comap.mp hc⟩
      have hc' : QuotientGroup.mk' (Subgroup.zpowers r) b *
          QuotientGroup.mk' (Subgroup.zpowers r) c =
          QuotientGroup.mk' (Subgroup.zpowers r) c *
          QuotientGroup.mk' (Subgroup.zpowers r) b := congrArg Subtype.val hcomm'
      have h1 : QuotientGroup.mk' (Subgroup.zpowers r) (b * c * b⁻¹ * c⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc']
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact exists_elemAb9_of_cube r hr3 hrc B hrB hB hcube hcomm

end Central


end CFSG.Quasithin.H13
