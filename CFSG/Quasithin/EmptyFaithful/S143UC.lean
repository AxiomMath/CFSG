module

public import CFSG.Quasithin.EmptyFaithful.S143Q8Aux
public import CFSG.Quasithin.EmptyFaithful.S1422Center

public section

namespace CFSG.Quasithin.S143

section Q8Facts

theorem q8_unique_invol : ∀ p q : QuaternionGroup 2, p * p = 1 → q * q = 1 → p ≠ 1 → q ≠ 1 →
    p = q := by decide +kernel

theorem q8_sqone_central : ∀ p q : QuaternionGroup 2, p * p = 1 → p * q = q * p := by decide +kernel

theorem q8_central_sqone : ∀ p : QuaternionGroup 2, (∀ q, p * q = q * p) → p * p = 1 := by
  decide +kernel

variable {X : Type*} [Group X] (e : X ≃* QuaternionGroup 2)

include e in
theorem mulEquiv_q8_unique_invol {p q : X} (hp : p * p = 1) (hq : q * q = 1) (hp1 : p ≠ 1)
    (hq1 : q ≠ 1) : p = q := by
  apply e.injective
  refine q8_unique_invol _ _ (by rw [← map_mul, hp, map_one]) (by rw [← map_mul, hq, map_one])
    (fun h => hp1 (e.injective (by rw [h, map_one]))) (fun h => hq1 (e.injective (by rw [h, map_one])))

include e in
theorem mulEquiv_q8_sqone_central {p : X} (hp : p * p = 1) (q : X) : p * q = q * p := by
  apply e.injective
  rw [map_mul, map_mul]
  exact q8_sqone_central _ _ (by rw [← map_mul, hp, map_one])

include e in
theorem mulEquiv_q8_central_sqone {p : X} (hp : ∀ q : X, p * q = q * p) : p * p = 1 := by
  apply e.injective
  rw [map_mul, map_one]
  refine q8_central_sqone _ fun q => ?_
  have := congrArg e (hp (e.symm q))
  simpa using this

end Q8Facts

section Config

variable {P : Type*} [Group P]

theorem q8_pow_four : ∀ p : QuaternionGroup 2, p ^ 4 = 1 := by decide +kernel

theorem Q8SqData.pow_four_A (d : Q8SqData P) {u : P} (hu : u ∈ d.A) : u ^ 4 = 1 := by
  have h := q8_pow_four (d.eA ⟨u, hu⟩)
  rw [← map_pow] at h
  have := d.eA.injective (h.trans (map_one d.eA).symm)
  exact congrArg Subtype.val this

theorem Q8SqData.center_cases (d : Q8SqData P) {z : P} (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1) :
    ∀ c ∈ Subgroup.center P, c = 1 ∨ c = z := by
  intro c hc
  obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center P))).mp d.card_center
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  · right
    have h1 := hx ⟨c, hc⟩ (fun h => hc1 (congrArg Subtype.val h))
    have h2 := hx ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem Q8SqData.orderOf_four (d : Q8SqData P) {u : P} (hu : u ∈ d.A) (hsq : u * u ≠ 1) :
    orderOf u = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_)
  · intro h
    apply hsq
    simpa [pow_two] using h
  · simpa using d.pow_four_A hu

@[expose] def Q8SqData.swap' (d : Q8SqData P) : Q8SqData P where
  A := d.B
  B := d.A
  comm := fun _ hb => Subgroup.mem_centralizer_iff.mpr fun _ ha => d.mul_comm_of_mem ha hb
  sup := by rw [sup_comm]; exact d.sup
  eA := d.eB
  eB := d.eA
  card := d.card

theorem Q8SqData.mem_A_or_mem_B (d : Q8SqData P) {u : P} (hsq : u * u ≠ 1) :
    u ∈ d.A ∨ u ∈ d.B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul u
  have hcomm : b * a = a * b := (d.mul_comm_of_mem ha hb).symm
  have hsq' : (a * b) * (a * b) = (a * a) * (b * b) := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm]
      _ = (a * a) * (b * b) := by group
  have haa := d.sq_mem_center_A ha
  have hbb := d.sq_mem_center_B hb
  by_cases hb2 : b * b = 1
  · left
    have hcB : ∀ q : ↥d.B, (⟨b, hb⟩ : ↥d.B) * q = q * ⟨b, hb⟩ :=
      mulEquiv_q8_sqone_central d.eB (p := ⟨b, hb⟩) (Subtype.ext hb2)
    have hbc : b ∈ Subgroup.center P :=
      d.mem_center_of_central_B hb (fun b'' hb'' => congrArg Subtype.val (hcB ⟨b'', hb''⟩))
    rw [d.center_eq] at hbc
    exact d.A.mul_mem ha hbc.1
  · by_cases ha2 : a * a = 1
    · right
      have hcA : ∀ q : ↥d.A, (⟨a, ha⟩ : ↥d.A) * q = q * ⟨a, ha⟩ :=
        mulEquiv_q8_sqone_central d.eA (p := ⟨a, ha⟩) (Subtype.ext ha2)
      have hac : a ∈ Subgroup.center P :=
        d.mem_center_of_central_A ha (fun a'' ha'' => congrArg Subtype.val (hcA ⟨a'', ha''⟩))
      rw [d.center_eq] at hac
      exact d.B.mul_mem hac.2 hb
    · exfalso
      have hcases := d.center_cases haa ha2 _ hbb
      rcases hcases with h | h
      · exact hb2 h
      · apply hsq
        rw [hsq', h]
        calc a * a * (a * a) = a ^ 4 := by
              rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
          _ = 1 := d.pow_four_A ha

end Config

section Config2

variable {P : Type*} [Group P] (d : Q8SqData P) {u₀ : P} (hu₀A : u₀ ∈ d.A)
  (hu₀nc : u₀ ∉ Subgroup.center P) (hsq : u₀ * u₀ ≠ 1)

include hu₀A in
theorem Q8SqData.mul_comm_u0 {b : P} (hb : b ∈ d.B) : b * u₀ = u₀ * b :=
  (d.mul_comm_of_mem hu₀A hb).symm

include hu₀A hu₀nc in
theorem Q8SqData.u0_not_mem_B : u₀ ∉ d.B := fun hB =>
  hu₀nc (d.inf_le_center ⟨hu₀A, hB⟩)

include hu₀A in
theorem Q8SqData.sq_mem_B : u₀ * u₀ ∈ d.B := by
  have hc := d.sq_mem_center_A hu₀A
  rw [d.center_eq] at hc
  exact hc.2

include hu₀A hu₀nc hsq in
theorem Q8SqData.card_zpowers_inf_B [Finite P] : Nat.card ↥(Subgroup.zpowers u₀ ⊓ d.B) = 2 := by
  have h4 := d.orderOf_four hu₀A hsq
  have hz : u₀ * u₀ ∈ Subgroup.zpowers u₀ ⊓ d.B :=
    ⟨Subgroup.mul_mem _ (Subgroup.mem_zpowers u₀) (Subgroup.mem_zpowers u₀), d.sq_mem_B hu₀A⟩
  have hdvd : Nat.card ↥(Subgroup.zpowers u₀ ⊓ d.B) ∣ 4 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers u₀ ⊓ d.B ≤ Subgroup.zpowers u₀)
    rwa [Nat.card_zpowers, h4] at this
  have hne1 : Nat.card ↥(Subgroup.zpowers u₀ ⊓ d.B) ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    have := hz
    rw [h1, Subgroup.mem_bot] at this
    exact hsq this
  have hne4 : Nat.card ↥(Subgroup.zpowers u₀ ⊓ d.B) ≠ 4 := by
    intro h4'
    have heq : Subgroup.zpowers u₀ ⊓ d.B = Subgroup.zpowers u₀ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4', Nat.card_zpowers, h4])
    apply d.u0_not_mem_B hu₀A hu₀nc
    have : u₀ ∈ Subgroup.zpowers u₀ ⊓ d.B := by rw [heq]; exact Subgroup.mem_zpowers u₀
    exact this.2
  have hle : Nat.card ↥(Subgroup.zpowers u₀ ⊓ d.B) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ↥(Subgroup.zpowers u₀ ⊓ d.B) := Nat.card_pos
  have h3 : Nat.card ↥(Subgroup.zpowers u₀ ⊓ d.B) ≠ 3 := by
    intro h3'
    rw [h3'] at hdvd
    omega
  omega

include hu₀A hu₀nc hsq in
theorem Q8SqData.centralizer_eq_sup [Finite P] :
    Subgroup.centralizer ({u₀} : Set P) = Subgroup.zpowers u₀ ⊔ d.B := by
  have hcomm : Subgroup.zpowers u₀ ≤ Subgroup.centralizer (d.B : Set P) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    exact d.mul_comm_u0 hu₀A hb
  have hle : Subgroup.zpowers u₀ ⊔ d.B ≤ Subgroup.centralizer ({u₀} : Set P) := by
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact d.mul_comm_u0 hu₀A hb
  have h4 := d.orderOf_four hu₀A hsq
  have hprod := card_sup_mul_card_inf_of_le_centralizer hcomm
  rw [d.card_zpowers_inf_B hu₀A hu₀nc hsq, Nat.card_zpowers, h4, d.card_B] at hprod
  have hcent := card_centralizer_of_not_mem_center d.card d.card_center d.commutator_mem_center hu₀nc
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem pow_three_eq_one_of_two_group {v : P} (hv3 : v ^ 3 = 1) (hv32 : v ^ 32 = 1) : v = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨hv3, hv32⟩
  have hg : Nat.gcd 3 32 = 1 := by decide
  rw [hg, pow_one] at h
  exact h

include hu₀A hu₀nc hsq in
theorem Q8SqData.map_B_le [Finite P] (α : P ≃* P) (hu₀fix : α u₀ = u₀) :
    ∀ b ∈ d.B, α b ∈ d.B := by
  classical
  intro b hb
  by_contra hyB
  have hzB : u₀ * u₀ ∈ d.B := d.sq_mem_B hu₀A
  have hzc : u₀ * u₀ ∈ Subgroup.center P := d.sq_mem_center_A hu₀A
  have h4 : orderOf u₀ = 4 := d.orderOf_four hu₀A hsq
  have hu4 : u₀ ^ 4 = 1 := d.pow_four_A hu₀A
  have hzz : (u₀ * u₀) * (u₀ * u₀) = 1 := by
    rw [← hu4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have hαz : α (u₀ * u₀) = u₀ * u₀ := by rw [map_mul, hu₀fix]
  let X : Subgroup P := d.B.map α.toMonoidHom
  have hyX : α b ∈ X := ⟨b, hb, rfl⟩
  have hzX : u₀ * u₀ ∈ X := ⟨u₀ * u₀, hzB, hαz⟩
  let eX : ↥X ≃* QuaternionGroup 2 :=
    (Subgroup.equivMapOfInjective d.B α.toMonoidHom α.injective).symm.trans d.eB
  have hXcomm : ∀ x ∈ X, x * u₀ = u₀ * x := by
    rintro _ ⟨b'', hb'', rfl⟩
    show α b'' * u₀ = u₀ * α b''
    calc α b'' * u₀ = α b'' * α u₀ := by rw [hu₀fix]
      _ = α (b'' * u₀) := (map_mul α _ _).symm
      _ = α (u₀ * b'') := by rw [d.mul_comm_u0 hu₀A hb'']
      _ = α u₀ * α b'' := map_mul α _ _
      _ = u₀ * α b'' := by rw [hu₀fix]
  have hcomm : Subgroup.zpowers u₀ ≤ Subgroup.centralizer (d.B : Set P) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_)
    exact d.mul_comm_u0 hu₀A hb'
  have hymem : α b ∈ Subgroup.zpowers u₀ ⊔ d.B := by
    rw [← d.centralizer_eq_sup hu₀A hu₀nc hsq, Subgroup.mem_centralizer_singleton_iff]
    exact hXcomm _ hyX
  obtain ⟨e, he, b', hb', hyeq⟩ := mem_sup_of_commute hcomm hymem
  have hecomm : ∀ x : P, x * u₀ = u₀ * x → x * e = e * x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (Commute.zpow_right (show Commute x u₀ from hx) n).eq
  have hz1 : u₀ * u₀ ≠ 1 := hsq
  have hcenter := d.center_cases hzc hz1
  have he4 : e = 1 ∨ e = u₀ ∨ e = u₀ * u₀ ∨ e = u₀ * u₀ * u₀ := by
    rw [Subgroup.mem_zpowers_iff] at he
    obtain ⟨n, rfl⟩ := he
    have hmod : u₀ ^ n = u₀ ^ (n % 4) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 4]
      rw [zpow_add, zpow_mul]
      have : u₀ ^ (4 : ℤ) = 1 := by exact_mod_cast hu4
      rw [this, one_zpow, mul_one]
    rw [hmod]
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · left; simp
    · right; left; simp
    · right; right; left; exact zpow_two u₀
    · right; right; right
      simp [zpow_ofNat, pow_succ, mul_assoc]
  have hyB' : e = 1 ∨ e = u₀ * u₀ → α b ∈ d.B := by
    rintro (h | h)
    · rw [hyeq, h, one_mul]; exact hb'
    · rw [hyeq, h]; exact d.B.mul_mem hzB hb'
  have hee : (e = u₀ ∨ e = u₀ * u₀ * u₀) → e * e = u₀ * u₀ := by
    rintro (h | h)
    · rw [h]
    · rw [h]
      calc u₀ * u₀ * u₀ * (u₀ * u₀ * u₀) = (u₀ ^ 4) * (u₀ * u₀) := by
            rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, pow_three']; group
        _ = u₀ * u₀ := by rw [hu4, one_mul]
  have hmain : (e = u₀ ∨ e = u₀ * u₀ * u₀) → False := by
    intro hed
    have hee' := hee hed
    have hbe : b' * e = e * b' := hecomm b' (d.mul_comm_u0 hu₀A hb')
    have hyy : α b * α b = (u₀ * u₀) * (b' * b') := by
      rw [hyeq]
      calc e * b' * (e * b') = e * (b' * e) * b' := by group
        _ = e * (e * b') * b' := by rw [hbe]
        _ = (e * e) * (b' * b') := by group
        _ = (u₀ * u₀) * (b' * b') := by rw [hee']
    by_cases hy1 : α b * α b = 1
    · by_cases hy1' : α b = 1
      · exact hyB (hy1' ▸ d.B.one_mem)
      · have hz' : (⟨u₀ * u₀, hzX⟩ : ↥X) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
        have := mulEquiv_q8_unique_invol eX (p := ⟨α b, hyX⟩) (q := ⟨u₀ * u₀, hzX⟩)
          (Subtype.ext hy1) (Subtype.ext hzz) (fun h => hy1' (congrArg Subtype.val h)) hz'
        have h5 : α b = u₀ * u₀ := congrArg Subtype.val this
        exact hyB (by rw [h5]; exact hzB)
    · have hbc := d.sq_mem_center_B hb'
      rcases hcenter _ hbc with hbb | hbb
      ·
        have hcent : ∀ q : ↥d.B, (⟨b', hb'⟩ : ↥d.B) * q = q * ⟨b', hb'⟩ :=
          mulEquiv_q8_sqone_central d.eB (p := ⟨b', hb'⟩) (Subtype.ext hbb)
        have hb'c : b' ∈ Subgroup.center P :=
          d.mem_center_of_central_B hb' (fun b'' hb'' => congrArg Subtype.val (hcent ⟨b'', hb''⟩))
        have hb'z : b' ∈ Subgroup.zpowers u₀ := by
          rcases hcenter _ hb'c with h | h
          · rw [h]; exact Subgroup.one_mem _
          · rw [h]; exact Subgroup.mul_mem _ (Subgroup.mem_zpowers u₀) (Subgroup.mem_zpowers u₀)
        have hyz : α b ∈ Subgroup.zpowers u₀ := by
          rw [hyeq]; exact Subgroup.mul_mem _ he hb'z
        have hcentX : ∀ q : ↥X, (⟨α b, hyX⟩ : ↥X) * q = q * ⟨α b, hyX⟩ := by
          intro q
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyz
          apply Subtype.ext
          show α b * (q : P) = (q : P) * α b
          rw [← hk]
          exact ((Commute.zpow_left (show Commute u₀ (q : P) from (hXcomm q q.2).symm) k)).eq
        exact hy1 (by
          have := mulEquiv_q8_central_sqone eX hcentX
          exact congrArg Subtype.val this)
      · apply hy1
        rw [hyy, hbb, hzz]
  rcases he4 with h | h | h | h
  · exact hyB (hyB' (Or.inl h))
  · exact hmain (Or.inl h)
  · exact hyB (hyB' (Or.inr h))
  · exact hmain (Or.inr h)

include hu₀A hu₀nc hsq in
theorem Q8SqData.fix_of_fix_B [Finite P] (α : P ≃* P) (hα3 : ∀ p, α (α (α p)) = p)
    (hu₀fix : α u₀ = u₀) (hB : ∀ b ∈ d.B, α b = b) : ∀ p, α p = p := by
  classical
  set U₁ := Subgroup.centralizer ({u₀} : Set P) with hU₁
  have hU₁eq : U₁ = Subgroup.zpowers u₀ ⊔ d.B := d.centralizer_eq_sup hu₀A hu₀nc hsq
  have hcomm : Subgroup.zpowers u₀ ≤ Subgroup.centralizer (d.B : Set P) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_)
    exact d.mul_comm_u0 hu₀A hb'
  have hfixU₁ : ∀ x ∈ U₁, α x = x := by
    intro x hx
    rw [hU₁eq] at hx
    obtain ⟨e, he, b, hb, rfl⟩ := mem_sup_of_commute hcomm hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [map_mul, hB b hb, map_zpow, hu₀fix]
  have hcent : Nat.card U₁ = 16 :=
    card_centralizer_of_not_mem_center d.card d.card_center d.commutator_mem_center hu₀nc
  have hidx : U₁.index = 2 := by
    have h := Subgroup.card_mul_index U₁
    rw [hcent, d.card] at h
    omega
  intro p
  by_cases hp : p ∈ U₁
  · exact hfixU₁ p hp
  · have hαp : α p ∉ U₁ := by
      intro h
      apply hp
      have h1 := hfixU₁ _ h
      have : α p = p := α.injective h1
      rw [← this]; exact h
    have hp' : p⁻¹ ∉ U₁ := fun h => hp (by simpa using U₁.inv_mem h)
    have hv : p⁻¹ * α p ∈ U₁ :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr ⟨fun h => absurd h hp', fun h => absurd h hαp⟩
    set v := p⁻¹ * α p with hvdef
    have hαv : α v = v := hfixU₁ v hv
    have hαp' : α p = p * v := by rw [hvdef]; group
    have h3 : α (α (α p)) = p * (v * v * v) := by
      calc α (α (α p)) = α (α (p * v)) := by rw [hαp']
        _ = α (α p * α v) := by rw [map_mul]
        _ = α (p * v * v) := by rw [hαp', hαv]
        _ = α (p * v) * α v := by rw [map_mul]
        _ = (α p * α v) * α v := by rw [map_mul]
        _ = p * (v * v * v) := by rw [hαp', hαv]; group
    rw [hα3] at h3
    have hv3 : v ^ 3 = 1 := by
      have h' : v * v * v = 1 := by
        have e : p * (v * v * v) = p * 1 := by rw [mul_one]; exact h3.symm
        exact mul_left_cancel e
      rw [pow_three']; exact h'
    have hv32 : v ^ 32 = 1 := by rw [← d.card]; exact pow_card_eq_one'
    have hv1 : v = 1 := pow_three_eq_one_of_two_group hv3 hv32
    rw [hαp', hv1, mul_one]

end Config2

end CFSG.Quasithin.S143
