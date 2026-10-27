module

public import CFSG.RankThree.GF2n.Tim77.Sec414d
public import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G] [Finite G]

section Bender

theorem sec414t_eq_one_of_central {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {x : K} (hx : ∀ y : K, Commute x y) : x = 1 := by
  haveI : IsSimpleGroup K := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hK
  obtain ⟨a, b, hab⟩ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hK
  have hxZ : x ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g => (hx g).symm.eq
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center K) with hZ | hZ
  · rw [hZ, Subgroup.mem_bot] at hxZ
    exact hxZ
  · exfalso
    have haZ : a ∈ Subgroup.center K := by
      rw [hZ]
      exact Subgroup.mem_top _
    exact hab (Subgroup.mem_center_iff.mp haZ b).symm

theorem sec414t_odd_of_not_commute {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {x y : K} (hx : x * x = 1) (hy : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : ¬ Commute x y) : Odd (orderOf (x * y)) := by
  rcases Nat.even_or_odd (orderOf (x * y)) with ⟨l, hl⟩ | hodd
  · exfalso
    have hpos : 0 < orderOf (x * y) := orderOf_pos _
    have hl0 : 0 < l := by omega
    have hw2 : (x * y) ^ l * (x * y) ^ l = 1 := by
      rw [← pow_add, ← hl, pow_orderOf_eq_one]
    have hw1 : (x * y) ^ l ≠ 1 := by
      intro h
      have hdvd : orderOf (x * y) ∣ l := orderOf_dvd_of_pow_eq_one h
      rw [hl] at hdvd
      have hle := Nat.le_of_dvd hl0 hdvd
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
    have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
    have hwo : orderOf ((x * y) ^ l) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
    have hxw : Commute x ((x * y) ^ l) := by
      show x * (x * y) ^ l = (x * y) ^ l * x
      rw [sec414_dihedral_mul_pow hx (sec414_dihedral_left_inv hx hy) l,
        inv_eq_of_mul_eq_one_right hw2]
    have hwy : Commute ((x * y) ^ l) y := by
      show (x * y) ^ l * y = y * (x * y) ^ l
      rw [sec414_dihedral_mul_pow hy (sec414_dihedral_right_inv hx hy) l,
        inv_eq_of_mul_eq_one_right hw2]
    exact hxy (CFSG.Timmesfeld.Bridge.OddLocal.IsBenderGroup.commute_trans hK hxo hwo hyo hxw hwy)
  · exact hodd

end Bender

section Dihedral

variable {Γ : Type} [Group Γ]

theorem sec414t_dihedral_conj {x y : Γ} (hx : x * x = 1) (hy : y * y = 1) (m : ℕ) :
    ∃ c ∈ Subgroup.closure ({x, y} : Set Γ), ∃ x' : Γ,
      (x' = c * x * c⁻¹ ∨ x' = c * y * c⁻¹) ∧ y * x' = (x * y) ^ m := by
  obtain ⟨c, hc, h⟩ := sec414_exists_conj_mul_pow hx hy (m + 1)
  refine ⟨c, hc, x * (x * y) ^ (m + 1), h, ?_⟩
  have hxy : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  rw [pow_succ', ← mul_assoc x (x * y), hxy, ← mul_assoc, hy, one_mul]

theorem sec414t_dihedral_two_odd {x y : Γ} (hx : x * x = 1) (hy : y * y = 1) {j : ℕ}
    (hN : orderOf (x * y) = 2 * (2 * j + 1)) :
    (x * y) ^ (2 * j + 1) * (x * y) ^ (2 * j + 1) = 1 ∧
    x * (x * y) ^ (2 * j + 1) = (x * y) ^ (2 * j + 1) * x ∧
    y * (x * y) ^ (2 * j + 1) = (x * y) ^ (2 * j + 1) * y ∧
    x * (x * y) ^ (2 * j + 1) = ((x * y) ^ j)⁻¹ * y * (x * y) ^ j ∧
    y * (x * y) ^ (2 * j + 1) = ((x * y) ^ (j + 1))⁻¹ * x * (x * y) ^ (j + 1) := by
  have hzz : (x * y) ^ (2 * j + 1) * (x * y) ^ (2 * j + 1) = 1 := by
    rw [← pow_add, ← two_mul, ← hN, pow_orderOf_eq_one]
  have hzinv : ((x * y) ^ (2 * j + 1))⁻¹ = (x * y) ^ (2 * j + 1) := inv_eq_of_mul_eq_one_right hzz
  refine ⟨hzz, ?_, ?_, sec414_dihedral_pow_odd hx hy j, ?_⟩
  · rw [sec414_dihedral_mul_pow hx (sec414_dihedral_left_inv hx hy), hzinv]
  · rw [sec414_dihedral_mul_pow hy (sec414_dihedral_right_inv hx hy), hzinv]
  · have h := sec414_dihedral_pow_even hx hy (j + 1)
    have hxy : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ', ← mul_assoc, hxy] at h
    exact h

end Dihedral

section Central

theorem sec414t_comm_of_commute_ne_one {A A0 : Subgroup G} (S : Sec414Sys A A0) {a e : G}
    (ha : a ∈ A) (ha0 : a ∉ A0) (g : G) (he : e ∈ conjSubgroup g A) (he1 : e ≠ 1)
    (hae : a * e = e * a) : Sec414Comm A (conjSubgroup g A) := by
  have haN : a ∈ normalizer (conjSubgroup g A : Set G) :=
    mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup S.ti g) he he1 hae
  rcases S.rel g with hc | ⟨hlink, -⟩ | ⟨hfree, -⟩
  · exact hc
  · exfalso
    apply ha0
    rw [← hlink]
    unfold normalizerIn
    exact Subgroup.mem_inf.mpr ⟨ha, haN⟩
  · exfalso
    have : a ∈ normalizerIn A (conjSubgroup g A) := by
      unfold normalizerIn
      exact Subgroup.mem_inf.mpr ⟨ha, haN⟩
    rw [hfree, Subgroup.mem_bot] at this
    exact S.ne_one_of_not_mem ha0 this

theorem sec414t_conj_false {A A0 : Subgroup G} (S : Sec414Sys A A0) {x a g c : G} (hx : x ∈ A0)
    (hx1 : x ≠ 1) (ha : a ∈ A) (ha0 : a ∉ A0) (h : g * a * g⁻¹ = c * x * c⁻¹) : False := by
  set m := c⁻¹ * g with hm
  have hx' : x = m * a * m⁻¹ := by
    have : x = c⁻¹ * (g * a * g⁻¹) * c := by rw [h]; group
    rw [this, hm]; group
  have hxC : x ∈ conjSubgroup m A := (mem_conjSubgroup_exists_t77 m A x).2 ⟨a, ha, hx'.symm⟩
  have hne : A ⊓ conjSubgroup m A ≠ ⊥ := by
    intro hbot
    have : x ∈ A ⊓ conjSubgroup m A := Subgroup.mem_inf.2 ⟨S.a0_le hx, hxC⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx1 this
  have hN : m ∈ normalizer (A : Set G) :=
    conjSubgroup_eq_self_iff.1 (conjSubgroup_eq_of_isTI S.ti hne)
  have := S.a0_norm m⁻¹ (Subgroup.inv_mem _ hN) x hx
  apply ha0
  rwa [hx', show m⁻¹ * (m * a * m⁻¹) * m⁻¹⁻¹ = a by group] at this

theorem sec414t_inf_W_conj {A : Subgroup G} {g : G} (hg : g ∈ A ⊔ conjSubgroup g A)
    (hAW : ∀ t ∈ A, t ∈ sec414W (A ⊔ conjSubgroup g A) → t = 1) :
    ∀ t ∈ conjSubgroup g A, t ∈ sec414W (A ⊔ conjSubgroup g A) → t = 1 := by
  intro t ht htW
  obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 g A t).1 ht
  have h1 := sec414W_conj (V := A ⊔ conjSubgroup g A) (Subgroup.inv_mem _ hg) htW
  rw [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at h1
  rw [hAW a ha h1]
  group

theorem sec414t_choice {A A0 : Subgroup G} {g : G} (S : Sec414Sys A A0) {V : Subgroup G}
    (hV : A ⊔ conjSubgroup g A = V) {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (π : ↥V →* K) (hπ : Function.Surjective π)
    (hAinj : ∀ a : ↥V, (a : G) ∈ A → π a = 1 → a = 1)
    {a₀ : ↥V} (ha₀ : (a₀ : G) ∈ A) (ha₀1 : a₀ ≠ 1) :
    ∃ y : ↥V, (y : G) ∈ conjSubgroup g A ∧ (y : G) ∉ conjSubgroup g A0 ∧
      ¬ Commute (π a₀) (π y) := by
  by_contra hcon
  push Not at hcon
  have hAV : A ≤ V := hV ▸ le_sup_left
  have hBV : conjSubgroup g A ≤ V := hV ▸ le_sup_right
  set H : Subgroup ↥V := (Subgroup.centralizer ({π a₀} : Set K)).comap π with hH
  have hHmem : ∀ v : ↥V, v ∈ H ↔ Commute (π a₀) (π v) := by
    intro v
    rw [hH, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    simp [Commute, SemiconjBy]
  set Z : Subgroup G := H.map V.subtype with hZ
  have hAZ : A ≤ Z := by
    intro a ha
    refine ⟨⟨a, hAV ha⟩, (hHmem _).2 ?_, rfl⟩
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (S.comm_A ha₀ ha)
  have hBZ : conjSubgroup g A ≤ Z := by
    rw [← (S.conj g).closure_diff, Subgroup.closure_le]
    intro b hb
    exact ⟨⟨b, hBV hb.1⟩, (hHmem _).2 (hcon ⟨b, hBV hb.1⟩ hb.1 hb.2), rfl⟩
  have hVZ : V ≤ Z := hV ▸ sup_le hAZ hBZ
  have hall : ∀ k : K, Commute (π a₀) k := by
    intro k
    obtain ⟨v, rfl⟩ := hπ k
    obtain ⟨v', hv', hvv⟩ := hVZ v.2
    have : v' = v := Subtype.ext hvv
    rw [← this]
    exact (hHmem v').1 hv'
  exact ha₀1 (hAinj a₀ ha₀ (sec414t_eq_one_of_central hK hall))


theorem sec414t_not_four {A A0 : Subgroup G} {g : G} (S : Sec414Sys A A0) {V : Subgroup G}
    {K : Type} [Group K] (π : ↥V →* K)
    (hker : ∀ y : ↥V, y * y = 1 → π y = 1 → (y : G) ∈ sec414W V)
    (hBW : ∀ t ∈ conjSubgroup g A, t ∈ sec414W V → t = 1)
    {x y : ↥V} (hx : x * x = 1) (hy : y * y = 1) (hxA : (x : G) ∈ A)
    (hyB : (y : G) ∈ conjSubgroup g A) (hyB0 : (y : G) ∉ conjSubgroup g A0)
    (hodd : Odd (orderOf (π (x * y)))) (h4 : 4 ∣ orderOf (x * y)) : False := by
  obtain ⟨m, hm⟩ := h4
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (orderOf_pos (x * y)).ne' (by simpa using hm)
  obtain ⟨c, -, x', hx', hyx'⟩ := sec414t_dihedral_conj hx hy m
  have hx'sq : x' * x' = 1 := by
    rcases hx' with rfl | rfl
    · calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
        _ = 1 := by rw [hx]; group
    · calc c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := by group
        _ = 1 := by rw [hy]; group
  have h4' : orderOf (y * x') = 4 := by
    have hdvd : m ∣ orderOf (x * y) := ⟨4, by rw [hm, mul_comm]⟩
    rw [hyx', orderOf_pow_of_dvd hm0 hdvd, hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hk : ∃ k : G, (x' : G) ∈ conjSubgroup k (conjSubgroup g A) := by
    rcases hx' with rfl | rfl
    · refine ⟨(c : G) * g⁻¹, ?_⟩
      rw [← conjSubgroup_mul, inv_mul_cancel_right]
      simpa using (mem_conjSubgroup_conj_t77 (c : G) (x : G) A).2 hxA
    · refine ⟨(c : G), ?_⟩
      simpa using (mem_conjSubgroup_conj_t77 (c : G) (y : G) _).2 hyB
  obtain ⟨k, hk⟩ := hk
  have h4G : orderOf ((y : G) * (x' : G)) = 4 := by
    rw [← h4', ← Subgroup.orderOf_coe]
    rfl
  have hN' := (S.conj g).four12 (y : G) hyB hyB0 k (x' : G) hk h4G
  have hx'G : (x' : G) * (x' : G) = 1 := by simpa using congrArg Subtype.val hx'sq
  have hx'inv : (x' : G)⁻¹ = (x' : G) := inv_eq_of_mul_eq_one_right hx'G
  have hB : ((y : G) * (x' : G)) * ((y : G) * (x' : G)) ∈ conjSubgroup g A := by
    have h1 : (x' : G) * (y : G) * (x' : G)⁻¹ ∈ conjSubgroup g A :=
      (Subgroup.mem_normalizer_iff.mp hN' (y : G)).mp hyB
    have h2 := Subgroup.mul_mem _ hyB h1
    rwa [hx'inv, show (y : G) * ((x' : G) * (y : G) * (x' : G)) =
      ((y : G) * (x' : G)) * ((y : G) * (x' : G)) by group] at h2
  set t : ↥V := (x * y) ^ m * (x * y) ^ m with ht
  have htG : (t : G) = ((y : G) * (x' : G)) * ((y : G) * (x' : G)) := by
    rw [ht, ← hyx']
    simp
  have htt : t * t = 1 := by
    rw [ht, ← pow_add, ← pow_add, show m + m + (m + m) = 4 * m by ring, ← hm,
      pow_orderOf_eq_one]
  have hπt : π t = 1 := by
    have hdvd : orderOf (π (x * y)) ∣ m := by
      have h1 : orderOf (π (x * y)) ∣ 4 * m := hm ▸ orderOf_map_dvd π (x * y)
      have hcop : Nat.Coprime (orderOf (π (x * y))) 4 := by
        have := Nat.Coprime.pow_right 2 (hodd.coprime_two_right)
        simpa using this
      exact hcop.dvd_of_dvd_mul_left h1
    have hpm : π (x * y) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
    rw [ht, map_mul, map_pow, hpm, one_mul]
  have hW := hker t htt hπt
  have h1 : (t : G) = 1 := hBW _ (htG ▸ hB) hW
  have h2 : t = 1 := Subtype.ext (by simpa using h1)
  have h3 : orderOf (x * y) ∣ m + m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_add]
    exact h2
  have := Nat.le_of_dvd (by omega) h3
  omega

theorem sec414t_central_aux {A A0 : Subgroup G} (S : Sec414Sys A A0) {g k₁ k₂ a₀ b z : G}
    (ha₀ : a₀ ∈ A0) (ha₀1 : a₀ ≠ 1) (hb : b ∈ conjSubgroup g A) (hb0 : b ∉ conjSubgroup g A0)
    (hza : z * a₀ = a₀ * z) (hzb : z * b = b * z)
    (hc : a₀ * z ∈ conjSubgroup k₁ A) (hc0 : a₀ * z ∉ conjSubgroup k₁ A0)
    (hd : b * z ∈ conjSubgroup k₂ A) (hd1 : b * z ≠ 1) :
    Sec414Comm A (conjSubgroup k₁ A) ∧ (∀ a ∈ A, z * a = a * z) ∧
      ∀ y ∈ conjSubgroup g A, z * y = y * z := by
  have h1 : Sec414Comm (conjSubgroup k₁ A) (conjSubgroup k₁⁻¹ (conjSubgroup k₁ A)) :=
    sec414t_comm_of_commute_ne_one (S.conj k₁) hc hc0 k₁⁻¹ (e := a₀)
      (by rw [conjSubgroup_inv_conj_cancel]; exact S.a0_le ha₀) ha₀1 (by rw [mul_assoc, hza])
  rw [conjSubgroup_inv_conj_cancel] at h1
  have hcomm : Sec414Comm A (conjSubgroup k₁ A) := fun a ha c hc' => (h1 c hc' a ha).symm
  refine ⟨hcomm, fun a ha => ?_, fun y hy => ?_⟩
  · have h2 := hcomm a ha (a₀ * z) hc
    have h3 := S.comm_A (S.a0_le ha₀) ha
    apply mul_left_cancel (a := a₀)
    calc a₀ * (z * a) = (a₀ * z) * a := by rw [mul_assoc]
      _ = a * (a₀ * z) := h2.symm
      _ = (a * a₀) * z := by rw [mul_assoc]
      _ = (a₀ * a) * z := by rw [h3]
      _ = a₀ * (a * z) := by rw [mul_assoc]
  · have h4 : Sec414Comm (conjSubgroup g A) (conjSubgroup (k₂ * g⁻¹) (conjSubgroup g A)) :=
      sec414t_comm_of_commute_ne_one (S.conj g) hb hb0 (k₂ * g⁻¹) (e := b * z)
        (by rw [← conjSubgroup_mul, inv_mul_cancel_right]; exact hd) hd1 (by rw [mul_assoc, hzb])
    rw [← conjSubgroup_mul, inv_mul_cancel_right] at h4
    have h2 := h4 y hy (b * z) hd
    have h3 := (S.conj g).comm_A hy hb
    apply mul_left_cancel (a := b)
    calc b * (z * y) = (b * z) * y := by rw [mul_assoc]
      _ = y * (b * z) := h2.symm
      _ = (y * b) * z := by rw [mul_assoc]
      _ = (b * y) * z := by rw [h3]
      _ = b * (y * z) := by rw [mul_assoc]

theorem sec414t_central {A A0 : Subgroup G} {g : G} (S : Sec414Sys A A0)
    (hg : g ∈ A ⊔ conjSubgroup g A) {K : Type} [Group K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (π : ↥(A ⊔ conjSubgroup g A) →* K)
    (hπ : Function.Surjective π)
    (hAinj : ∀ a : ↥(A ⊔ conjSubgroup g A), (a : G) ∈ A → π a = 1 → a = 1)
    (hker : ∀ y : ↥(A ⊔ conjSubgroup g A), y * y = 1 → π y = 1 →
      (y : G) ∈ sec414W (A ⊔ conjSubgroup g A))
    (hAW : ∀ t ∈ A, t ∈ sec414W (A ⊔ conjSubgroup g A) → t = 1) :
    ∃ a₀ ∈ A0, ∃ z k : G, k ∈ A ⊔ conjSubgroup g A ∧ z * z = 1 ∧
      (∀ v ∈ A ⊔ conjSubgroup g A, z * v = v * z) ∧
      a₀ * z ∈ conjSubgroup k A ∧ a₀ * z ∉ conjSubgroup k A0 ∧
      Sec414Comm A (conjSubgroup k A) := by
  haveI : Finite K := Finite.of_surjective π hπ
  have hAV : A ≤ A ⊔ conjSubgroup g A := le_sup_left
  have hBW := sec414t_inf_W_conj hg hAW
  obtain ⟨x, hxA0, hx1⟩ : ∃ x : ↥(A ⊔ conjSubgroup g A), (x : G) ∈ A0 ∧ x ≠ 1 := by
    obtain ⟨⟨a₀, ha₀⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.a0_ne
    exact ⟨⟨a₀, hAV (S.a0_le ha₀)⟩, ha₀,
      fun e => h1 (Subtype.ext (by simpa using congrArg Subtype.val e))⟩
  have hxA : (x : G) ∈ A := S.a0_le hxA0
  obtain ⟨y, hyB, hyB0, hnc⟩ := sec414t_choice S rfl hK π hπ hAinj hxA hx1
  have hxsq : x * x = 1 := Subtype.ext (by simpa using S.sq_A hxA)
  have hysq : y * y = 1 := Subtype.ext (by simpa using (S.conj g).sq_A hyB)
  have hπx1 : π x ≠ 1 := fun h => hx1 (hAinj x hxA h)
  have hπy1 : π y ≠ 1 := fun h =>
    hyB0 (hBW _ hyB (hker y hysq h) ▸ (conjSubgroup g A0).one_mem)
  have hodd : Odd (orderOf (π (x * y))) := by
    rw [map_mul]
    exact sec414t_odd_of_not_commute hK (by rw [← map_mul, hxsq, map_one])
      (by rw [← map_mul, hysq, map_one]) hπx1 hπy1 hnc
  obtain ⟨a, ha, hya⟩ := (mem_conjSubgroup_exists_t77 g A (y : G)).1 hyB
  have ha0 : a ∉ A0 := fun h => hyB0 (hya ▸ (mem_conjSubgroup_conj_t77 g a A0).2 h)
  have hx1G : (x : G) ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hNodd : ¬ Odd (orderOf (x * y)) := by
    intro hN
    obtain ⟨c, -, hc⟩ := sec414_exists_conj_of_odd hxsq hysq hN
    exact sec414t_conj_false S hxA0 hx1G ha ha0 (c := (c : G))
      (by rw [hya]; simpa using congrArg Subtype.val hc)
  have h4 : ¬ 4 ∣ orderOf (x * y) := fun h4 =>
    sec414t_not_four S π hker hBW hxsq hysq hxA hyB hyB0 hodd h4
  obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.1 hNodd
  obtain ⟨j, hj⟩ : Odd r := by
    rcases Nat.even_or_odd r with ⟨s, hs⟩ | hodd'
    · exact absurd ⟨s, by omega⟩ h4
    · exact hodd'
  have hN2 : orderOf (x * y) = 2 * (2 * j + 1) := by omega
  obtain ⟨hzz, hxz, hyz, hxz', hyz'⟩ := sec414t_dihedral_two_odd hxsq hysq hN2
  generalize (x * y) ^ (2 * j + 1) = zV at hzz hxz hyz hxz' hyz'
  generalize (x * y) ^ j = Q at hxz'
  generalize (x * y) ^ (j + 1) = Q' at hyz'
  have hzzG : (zV : G) * (zV : G) = 1 := by simpa using congrArg Subtype.val hzz
  have hxzG : (x : G) * (zV : G) = (zV : G) * (x : G) := by simpa using congrArg Subtype.val hxz
  have hyzG : (y : G) * (zV : G) = (zV : G) * (y : G) := by simpa using congrArg Subtype.val hyz
  have hxz'G : (x : G) * (zV : G) = (Q : G)⁻¹ * (y : G) * (Q : G) := by
    simpa using congrArg Subtype.val hxz'
  have hyz'G : (y : G) * (zV : G) = (Q' : G)⁻¹ * (x : G) * (Q' : G) := by
    simpa using congrArg Subtype.val hyz'
  have hc : (x : G) * (zV : G) ∈ conjSubgroup ((Q : G)⁻¹ * g) A := by
    rw [hxz'G, ← hya]
    have := (mem_conjSubgroup_conj_t77 ((Q : G)⁻¹ * g) a A).2 ha
    rwa [show ((Q : G)⁻¹ * g) * a * ((Q : G)⁻¹ * g)⁻¹ = (Q : G)⁻¹ * (g * a * g⁻¹) * (Q : G) by
      group] at this
  have hc0 : (x : G) * (zV : G) ∉ conjSubgroup ((Q : G)⁻¹ * g) A0 := by
    rw [hxz'G, ← hya]
    intro h
    rw [show (Q : G)⁻¹ * (g * a * g⁻¹) * (Q : G) =
      ((Q : G)⁻¹ * g) * a * ((Q : G)⁻¹ * g)⁻¹ by group] at h
    exact ha0 ((mem_conjSubgroup_conj_t77 _ a A0).1 h)
  have hdeq : (y : G) * (zV : G) = (Q' : G)⁻¹ * (x : G) * ((Q' : G)⁻¹)⁻¹ := by
    rw [hyz'G, inv_inv]
  have hd : (y : G) * (zV : G) ∈ conjSubgroup ((Q' : G)⁻¹) A := by
    rw [hdeq]
    exact (mem_conjSubgroup_conj_t77 _ _ A).2 hxA
  have hd1 : (y : G) * (zV : G) ≠ 1 := by
    rw [hdeq]
    exact fun h => hx1G ((conj_eq_one_iff_t77 _ _).1 h)
  obtain ⟨hcomm, hzA, hzB⟩ := sec414t_central_aux S (g := g) hxA0 hx1G hyB hyB0
    (hxzG.symm) (hyzG.symm) hc hc0 hd hd1
  have hcent : A ⊔ conjSubgroup g A ≤ Subgroup.centralizer ({(zV : G)} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hzA a ha
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hzB b hb
  refine ⟨(x : G), hxA0, (zV : G), (Q : G)⁻¹ * g, Subgroup.mul_mem _ (Q⁻¹).2 hg, hzzG,
    fun v hv => ?_, hc, hc0, hcomm⟩
  have := Subgroup.mem_centralizer_iff.mp (hcent hv) (zV : G) (Set.mem_singleton _)
  exact this

end Central

end CFSG.RankThree.GF2n.Tim77
