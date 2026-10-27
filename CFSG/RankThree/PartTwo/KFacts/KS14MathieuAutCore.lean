module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint

section Aut

variable {Y : Type*} [Group Y]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun φ : MulAut Y => φ g) hz
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * z = z * g * z⁻¹ * z := by rw [h]
    _ = z * g := by group

theorem exists_conj_of_card_mulAut_le [Finite Y] (hZ : Subgroup.center Y = ⊥)
    (hAut : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) (σ : MulAut Y)
    (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) : ∃ y : Y, σ = MulAut.conj y := by
  obtain ⟨k, hk⟩ := hσ
  set I := (MulAut.conj : Y →* MulAut Y).range with hI
  have hIcard : Nat.card I = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)).toEquiv).symm
  have hmul := I.card_mul_index
  rw [hIcard] at hmul
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have hAutpos : 0 < Nat.card (MulAut Y) := Nat.card_pos
  have hidx : I.index = 1 ∨ I.index = 2 := by
    have h1 : I.index ≤ 2 := by
      by_contra h
      have : Nat.card Y * 3 ≤ Nat.card Y * I.index := Nat.mul_le_mul_left _ (by omega)
      omega
    have h0 : I.index ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      omega
    omega
  have hσI : σ ∈ I := by
    rcases hidx with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top σ
    · have hsq := Subgroup.sq_mem_of_index_two h2 σ
      have hodd : 3 ^ k % 2 = 1 := Nat.odd_iff.mp (Odd.pow ⟨1, rfl⟩)
      obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = 2 * m + 1 := ⟨3 ^ k / 2, by omega⟩
      have hσm : σ = ((σ ^ 2) ^ m)⁻¹ := by
        rw [← pow_mul, eq_inv_iff_mul_eq_one, ← pow_succ', ← hm, hk]
      rw [hσm]
      exact inv_mem (pow_mem hsq m)
  obtain ⟨y, hy⟩ := hσI
  exact ⟨y, hy.symm⟩

end Aut

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem center_eq_bot_of_mulEquiv (e : X ≃* Y) (hZ : Subgroup.center Y = ⊥) :
    Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) x]
  rw [hZ, Subgroup.mem_bot, map_eq_one_iff _ e.injective] at hez
  rw [Subgroup.mem_bot]
  exact hez

theorem pow_three_eq_one_of_mulEquiv (e : X ≃* Y)
    (h : ∀ g : Y, (∃ k : ℕ, g ^ 3 ^ k = 1) → g ^ 3 = 1) (g : X)
    (hg : ∃ k : ℕ, g ^ 3 ^ k = 1) : g ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hg
  have h3 := h (e g) ⟨k, by rw [← map_pow, hk, map_one]⟩
  rwa [← map_pow, map_eq_one_iff _ e.injective] at h3

theorem isMulCommutative_of_mulEquiv (e : X ≃* Y)
    (h : ∀ Q : Subgroup Y, IsPGroup 3 Q → IsMulCommutative Q) (Q : Subgroup X)
    (hQ : IsPGroup 3 Q) : IsMulCommutative Q := by
  have hc := (h _ (hQ.map e.toMonoidHom)).is_comm.comm
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h2 := congrArg Subtype.val (hc ⟨e a, a, a.2, rfl⟩ ⟨e b, b, b.2, rfl⟩)
  simp only [Subgroup.coe_mul] at h2
  rw [← map_mul, ← map_mul] at h2
  exact e.injective h2

end Transport

section ElemNine

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_card_nine {E : Subgroup G} (hE : Nat.card E = 9)
    (hfac : (Nat.card G).factorization 3 = 2) {Q : Subgroup G} (hQ : IsPGroup 3 Q) :
    ∃ h : G, ∀ q ∈ Q, h⁻¹ * q * h ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 G := Sylow.ofCard E (by rw [hE, hfac]; norm_num)
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S P
  refine ⟨h, fun q hq => ?_⟩
  have hqP : q ∈ ((h • S : Sylow 3 G) : Subgroup G) := by
    rw [hh]
    exact hQP hq
  have hsm : ((h • S : Sylow 3 G) : Subgroup G) =
      (S : Subgroup G).map (MulAut.conj h).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hsm] at hqP
  obtain ⟨e, heS, rfl⟩ := hqP
  have he : h⁻¹ * (MulAut.conj h).toMonoidHom e * h = e := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [he]
  exact heS

theorem pow_three_eq_one_of_elemNine {E : Subgroup G} (hE : Nat.card E = 9)
    (hfac : (Nat.card G).factorization 3 = 2) (hcube : ∀ e ∈ E, e ^ 3 = 1) (g : G)
    (hg : ∃ k : ℕ, g ^ 3 ^ k = 1) : g ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hg
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hQ : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨h, hh⟩ := exists_conj_mem_of_card_nine hE hfac hQ
  have h3 := hcube _ (hh g (Subgroup.mem_zpowers g))
  have hconj : (h⁻¹ * g * h) ^ 3 = h⁻¹ * g ^ 3 * h := by
    have := conj_pow (a := h⁻¹) (b := g) (i := 3)
    rwa [inv_inv] at this
  rw [hconj] at h3
  calc g ^ 3 = h * (h⁻¹ * g ^ 3 * h) * h⁻¹ := by group
    _ = 1 := by rw [h3]; group

theorem isMulCommutative_of_elemNine {E : Subgroup G} (hE : Nat.card E = 9)
    (hfac : (Nat.card G).factorization 3 = 2) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (Q : Subgroup G) (hQ : IsPGroup 3 Q) : IsMulCommutative Q := by
  obtain ⟨h, hh⟩ := exists_conj_mem_of_card_nine hE hfac hQ
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hab := hcomm _ (hh a a.2) _ (hh b b.2)
  have hc : h⁻¹ * ((a : G) * b) * h = h⁻¹ * ((b : G) * a) * h := by
    calc h⁻¹ * ((a : G) * b) * h = (h⁻¹ * a * h) * (h⁻¹ * b * h) := by group
      _ = (h⁻¹ * b * h) * (h⁻¹ * a * h) := hab
      _ = h⁻¹ * ((b : G) * a) * h := by group
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_left_cancel (mul_right_cancel hc)

theorem card_closure_eq_nine (hfac : (Nat.card G).factorization 3 = 2) {x y : G}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hyx : ∀ n < 3, x ^ n ≠ y) : Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({x, y} : Set G) with hEdef
  have hT : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl)
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  have hcube : ∀ g ∈ E, g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact hx
      · exact hy
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (commute_of_mem_closure hT ha hb) 3), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hcube g g.2)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hm2 : m ≤ 2 := by
    have hdvd : 3 ^ m ∣ Nat.card G := hm ▸ Subgroup.card_subgroup_dvd_card E
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hG0, hfac] at hdvd
    exact hdvd
  have hxE : x ∈ E := Subgroup.subset_closure (Set.mem_insert x {y})
  have hyE : y ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hox : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hzx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
  have hzle : Subgroup.zpowers x ≤ E := (Subgroup.zpowers_le).mpr hxE
  have hm1 : 1 ≤ m := by
    have hdvd := Subgroup.card_dvd_of_le hzle
    rw [hzx, hm] at hdvd
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hdvd
      norm_num at hdvd
    · exact h0
  rcases (show m = 1 ∨ m = 2 by omega) with h1 | h2
  · exfalso
    have heq : Subgroup.zpowers x = E :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [hm, h1, hzx, pow_one])
    have hyz : y ∈ Subgroup.zpowers x := heq ▸ hyE
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hox, Finset.mem_image] at hyz
    obtain ⟨n, hn, hny⟩ := hyz
    exact hyx n (Finset.mem_range.mp hn) hny
  · rw [hm, h2]
    norm_num

end ElemNine

section Facts

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

theorem ks18A7M22_facts_of (e : X ≃* Y) (h3 : 3 ∣ Nat.card Y)
    (hZ : Subgroup.center Y = ⊥) (hAut : Nat.card (MulAut Y) ≤ 2 * Nat.card Y)
    (hfac : (Nat.card Y).factorization 3 = 2) {E : Subgroup Y} (hE : Nat.card E = 9)
    (hcube : ∀ g ∈ E, g ^ 3 = 1) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    3 ∣ Nat.card X ∧ Subgroup.center X = ⊥ ∧
      (∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x) ∧
      (∀ x : X, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1) ∧
      ∀ Q : Subgroup X, IsPGroup 3 Q → IsMulCommutative Q := by
  have hXY : Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv
  have hZX := center_eq_bot_of_mulEquiv e hZ
  refine ⟨hXY ▸ h3, hZX, fun σ hσ => exists_conj_of_card_mulAut_le hZX ?_ σ hσ,
    pow_three_eq_one_of_mulEquiv e (pow_three_eq_one_of_elemNine hE hfac hcube),
    isMulCommutative_of_mulEquiv e (isMulCommutative_of_elemNine hE hfac hcomm)⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv, hXY]
  exact hAut

omit [Finite Y] in
theorem ks18M12_facts_of (e : X ≃* Y) (h3 : 3 ∣ Nat.card Y) (hZ : Subgroup.center Y = ⊥)
    (hAut : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) [IsSimpleGroup Y] :
    3 ∣ Nat.card X ∧ Subgroup.center X = ⊥ ∧
      (∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x) ∧
      ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥ := by
  have hXY : Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv
  have hZX := center_eq_bot_of_mulEquiv e hZ
  refine ⟨hXY ▸ h3, hZX, fun σ hσ => exists_conj_of_card_mulAut_le hZX ?_ σ hσ,
    fun N hN hsol => ?_⟩
  · rw [Nat.card_congr (MulAut.congr e).toEquiv, hXY]
    exact hAut
  · have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map e.toMonoidHom) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hbot
    · exfalso
      have hsolY : Group.IsSolvable Y := by
        have hsolM : Group.IsSolvable (N.map e.toMonoidHom) :=
          Group.isSolvable_of_surjective
            (f := (N.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
            (N.equivMapOfInjective e.toMonoidHom e.injective).surjective
        have hsolT : Group.IsSolvable (⊤ : Subgroup Y) := htop ▸ hsolM
        exact Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).toMonoidHom)
          (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).surjective
      have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolY
      have htopZ : Subgroup.center Y = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_center_iff]
        exact fun h => hcomm h g
      rw [hZ] at htopZ
      have hnt : Nontrivial Y := IsSimpleGroup.toNontrivial
      exact bot_ne_top htopZ

end Facts

section A7

open CFSG.RankThree.PartTwo.KFacts.KP2

theorem card_mulAut_alternatingGroup_seven :
    Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num))).toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_eNine_subgroupOf :
    Nat.card (eNine.subgroupOf (alternatingGroup (Fin 7))) = 9 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv, card_eNine]

theorem a7_facts (X : Type) [Group X] [Finite X] (hX : Nonempty (X ≃* alternatingGroup (Fin 7))) :
    3 ∣ Nat.card X ∧ Subgroup.center X = ⊥ ∧
      (∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x) ∧
      (∀ x : X, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1) ∧
      ∀ Q : Subgroup X, IsPGroup 3 Q → IsMulCommutative Q := by
  obtain ⟨e⟩ := hX
  have hfac : (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [card_alternatingGroup_five_seven_ten.2.1, show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
        Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have h4 : 4 ≤ Nat.card (Fin 7) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  refine ks18A7M22_facts_of e (by rw [card_alternatingGroup_five_seven_ten.2.1]; norm_num)
    (alternatingGroup.center_eq_bot h4)
    (by rw [card_mulAut_alternatingGroup_seven, card_alternatingGroup_five_seven_ten.2.1]) hfac
    card_eNine_subgroupOf ?_ ?_
  · intro g hg
    rw [Subgroup.mem_subgroupOf, mem_eNine] at hg
    obtain ⟨i, j, hij⟩ := hg
    apply Subtype.ext
    rw [Subgroup.coe_pow, hij, eNineF_pow_three, Subgroup.coe_one]
  · intro a ha b hb
    rw [Subgroup.mem_subgroupOf, mem_eNine] at ha hb
    obtain ⟨i, j, hij⟩ := ha
    obtain ⟨k, l, hkl⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hij, hkl, eNineF_comm]

end A7

section M22

abbrev m22A : NativeSporadic.M22 :=
  ⟨CFSG.Sporadic.Bridge.M22.gen 0, CFSG.Sporadic.Bridge.M22.gen_mem 0⟩

abbrev m22B : NativeSporadic.M22 :=
  ⟨CFSG.Sporadic.Bridge.M22.gen 1, CFSG.Sporadic.Bridge.M22.gen_mem 1⟩

abbrev m22x : NativeSporadic.M22 :=
  m22B⁻¹ * m22A * m22B⁻¹ * m22A * m22B * m22A * m22B * m22A

abbrev m22y : NativeSporadic.M22 :=
  m22A * m22B * m22A * m22B⁻¹ * m22A * m22B⁻¹ * m22A * m22B * m22A * m22B * m22B * m22A *
    m22B⁻¹ * m22A * m22B * m22A * m22B * m22A * m22B⁻¹

theorem m22x_pow_three : m22x ^ 3 = 1 := by decide +kernel

theorem m22y_pow_three : m22y ^ 3 = 1 := by decide +kernel

theorem m22x_mul_comm : m22x * m22y = m22y * m22x := by decide +kernel

theorem m22x_ne_one : m22x ≠ 1 := by decide +kernel

theorem m22x_pow_ne_m22y : ∀ n < 3, m22x ^ n ≠ m22y := by decide +kernel

theorem factorization_card_m22 : (Nat.card NativeSporadic.M22).factorization 3 = 2 := by
  rw [card_nativeM22, show (443520 : ℕ) = 3 ^ 2 * 49280 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow
      Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem card_closure_m22xy :
    Nat.card (Subgroup.closure ({m22x, m22y} : Set NativeSporadic.M22)) = 9 :=
  card_closure_eq_nine factorization_card_m22 m22x_pow_three m22y_pow_three m22x_mul_comm
    m22x_ne_one m22x_pow_ne_m22y

theorem comm_of_mem_closure_m22xy {a b : NativeSporadic.M22}
    (ha : a ∈ Subgroup.closure ({m22x, m22y} : Set NativeSporadic.M22))
    (hb : b ∈ Subgroup.closure ({m22x, m22y} : Set NativeSporadic.M22)) : a * b = b * a := by
  refine commute_of_mem_closure ?_ ha hb
  rintro u (rfl | rfl) v (rfl | rfl)
  · rfl
  · exact m22x_mul_comm
  · exact m22x_mul_comm.symm
  · rfl

theorem pow_three_of_mem_closure_m22xy {g : NativeSporadic.M22}
    (hg : g ∈ Subgroup.closure ({m22x, m22y} : Set NativeSporadic.M22)) : g ^ 3 = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · exact m22x_pow_three
    · exact m22y_pow_three
  | one => exact one_pow 3
  | mul a b ha hb iha ihb =>
    rw [(Commute.mul_pow (comm_of_mem_closure_m22xy ha hb) 3), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end M22

end CFSG.RankThree.PartTwo.KFacts.KS14
