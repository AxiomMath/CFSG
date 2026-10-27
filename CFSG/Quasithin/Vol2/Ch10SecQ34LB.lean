module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

theorem odd_mem_of_index_two {X : Type*} [Group X] {H : Subgroup X} (hH : H.index = 2) {x : X}
    (hx : Odd (orderOf x)) : x ∈ H := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x = (x ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h1]
  exact H.pow_mem (Subgroup.sq_mem_of_index_two hH x) _

theorem oTwoUpper_ne_of_index_two {A : Type*} [Group A] {Y : Subgroup A} {N : Subgroup ↥Y}
    (hN : N.index = 2) : oTwoUpper Y ≠ Y := by
  intro h
  have hle : oTwoUpper Y ≤ N.map Y.subtype := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    refine ⟨⟨y, hy.1⟩, odd_mem_of_index_two hN ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    exact hy.2
  rw [h] at hle
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hzy⟩ := hle y.2
    have : z = y := Subtype.ext hzy
    exact this ▸ hz
  rw [hNtop, Subgroup.index_top] at hN
  exact absurd hN (by norm_num)

theorem orderOf_dvd_three_mul {A : Type*} [Group A] [Finite A] {Y : Subgroup A}
    (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) (y : A) (hy : y ∈ Y) :
    ∃ k : ℕ, orderOf y ∣ 3 * 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  obtain ⟨k, hk⟩ := hP ⟨_, hY3 y hy⟩
  refine ⟨k, orderOf_dvd_of_pow_eq_one ?_⟩
  have := congrArg Subtype.val hk
  rw [pow_mul]
  simpa using this

theorem not_orderOf_prime {A : Type*} [Group A] [Finite A] {Y : Subgroup A}
    (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {y : A}
    (hy : y ∈ Y) (hyq : orderOf y = q) : False := by
  obtain ⟨k, hk⟩ := orderOf_dvd_three_mul hY3 y hy
  rw [hyq] at hk
  rcases (Nat.Prime.dvd_mul hq).mp hk with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    omega

theorem card_eq_three_or_alt4 {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (e : A ≃* PSL(2, ZMod p)) {Y : Subgroup A}
    (hY1 : Y ≠ ⊥) (hYO : oTwoUpper Y = Y) (hY3 : ∀ y ∈ Y, y ^ 3 ∈ pCoreOf 2 Y) :
    Nat.card Y = 3 ∨ Nonempty (↥Y ≃* alternatingGroup (Fin 4)) := by
  set Y' : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup (ZMod p)) := Y.map e.toMonoidHom
    with hY'
  let eY : ↥Y ≃* ↥Y' := Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective
  have hcardY : Nat.card ↥Y = Nat.card ↥Y' := Nat.card_congr eY.toEquiv
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hnoq : ∀ q : ℕ, q.Prime → 5 ≤ q → q ∣ Nat.card ↥Y' → False := by
    intro q hq hq5 hdvd
    have : Fact q.Prime := ⟨hq⟩
    have := Fintype.ofFinite ↥Y'
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card (G := ↥Y') q
      (by rwa [← Nat.card_eq_fintype_card])
    have hy : orderOf ((eY.symm y' : ↥Y) : A) = q := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy']
    exact not_orderOf_prime hY3 hq hq5 (eY.symm y').2 hy
  have hno2 : ∀ N : Subgroup ↥Y', N.index = 2 → False := fun N hN =>
    oTwoUpper_ne_of_index_two (N := N.comap eY.toMonoidHom)
      (by rw [Subgroup.index_comap_of_surjective _ (f := eY.toMonoidHom) eY.surjective]; exact hN)
      hYO
  have hpdvd : ∀ k : ℕ, 1 ≤ k → p ∣ p ^ k := fun k hk => dvd_pow_self p (by omega)
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list (F := ZMod p) hF Y' with
    ⟨m, -, hcard, -⟩ | ⟨z, -, hcard, hcyc⟩ | ⟨z, hz2, -, ⟨eD⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ |
      ⟨-, ⟨eA5⟩⟩ | ⟨m, t, hm1, -, -, -, E, C, -, -, hEcard, -⟩ | ⟨m, hm, ⟨eL⟩⟩ | ⟨m, hm, -⟩
  ·
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      apply hY1
      rw [← Subgroup.card_eq_one, hcardY, hcard, h0, pow_zero]
    · exact (hnoq p hp.out hp5 (hcard ▸ hpdvd m h0)).elim
  ·
    left
    rcases Nat.even_or_odd (Nat.card ↥Y') with hev | hodd
    · exfalso
      have h2 : 2 ∣ Nat.card ↥Y' := even_iff_two_dvd.mp hev
      set φ : ↥Y' →* Multiplicative (ZMod 2) :=
        (AddMonoidHom.toMultiplicative (ZMod.castHom h2 (ZMod 2)).toAddMonoidHom).comp
          (zmodCyclicMulEquiv hcyc).symm.toMonoidHom with hφ
      have hφs : Function.Surjective φ :=
        (ZMod.castHom_surjective h2).comp (zmodCyclicMulEquiv hcyc).symm.surjective
      apply hno2 φ.ker
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top]
      simp
    · have hOdd : Odd (Nat.card ↥Y) := hcardY ▸ hodd
      have hO2 : pCoreOf 2 Y = ⊥ := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hd : Nat.card ↥(pCoreOf 2 Y) ∣ Nat.card ↥Y :=
          Subgroup.card_dvd_of_le (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) Y)
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
        rw [hk] at hd
        have hk0 : k = 0 := by
          by_contra h
          exact Nat.not_odd_iff_even.mpr ((Nat.even_pow.mpr ⟨even_two, h⟩).two_dvd.trans hd
            |> even_iff_two_dvd.mpr) hOdd
        rw [← Subgroup.card_eq_one, hk, hk0, pow_zero]
      have hcycY : IsCyclic ↥Y := isCyclic_of_surjective eY.symm.toMonoidHom eY.symm.surjective
      obtain ⟨g, hg⟩ := hcycY.exists_generator
      have hg3 : g ^ 3 = 1 := by
        have h := hY3 g g.2
        rw [hO2, Subgroup.mem_bot] at h
        exact Subtype.ext h
      have hord : orderOf g = Nat.card ↥Y := orderOf_eq_card_of_forall_mem_zpowers hg
      have hd3 : Nat.card ↥Y ∣ 3 := hord ▸ orderOf_dvd_of_pow_eq_one hg3
      rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h3
      · exact absurd (Subgroup.card_eq_one.mp h1) hY1
      · exact h3
  ·
    exfalso
    have : NeZero z := ⟨by omega⟩
    apply hno2 ((Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)).comap eD.toMonoidHom)
    rw [Subgroup.index_comap_of_surjective _ (f := eD.toMonoidHom) eD.surjective]
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z))
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < z) (by rw [h1, mul_comm])
  ·
    exact Or.inr ⟨eY.trans eA⟩
  ·
    exfalso
    apply hno2 ((alternatingGroup (Fin 4)).comap eS.toMonoidHom)
    rw [Subgroup.index_comap_of_surjective _ (f := eS.toMonoidHom) eS.surjective]
    exact alternatingGroup.index_eq_two
  ·
    have h60 : Nat.card ↥Y' = 60 := by
      rw [Nat.card_congr eA5.toEquiv]
      have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
      rw [Nat.card_perm, Nat.card_fin] at h
      have h5 : Nat.factorial 5 = 120 := by decide
      omega
    exact (hnoq 5 (by norm_num) le_rfl (by rw [h60]; norm_num)).elim
  ·
    have hdvd : Nat.card ↥E ∣ Nat.card ↥Y' := Subgroup.card_subgroup_dvd_card E
    exact (hnoq p hp.out hp5 ((hpdvd m hm1).trans (hEcard ▸ hdvd))).elim
  ·
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hm
    subst hm1
    have hcardL := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p 1)
      ⟨p, 1, hp.out, hp.out.odd_of_ne_two (by omega), le_rfl, GaloisField.card p 1 one_ne_zero⟩
    rw [GaloisField.card p 1 one_ne_zero, pow_one] at hcardL
    have hdvd : p ∣ Nat.card ↥Y' := by
      rw [Nat.card_congr eL.toEquiv]
      change p ∣ Nat.card (CFSG.GorensteinWalter.PSL2 (GaloisField p 1))
      rw [hcardL]
      have h2 : 2 ∣ p ^ 2 - 1 := by
        have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
        have : Odd (p ^ 2) := hodd.pow
        obtain ⟨k, hk⟩ := this
        omega
      obtain ⟨k, hk⟩ := h2
      rw [hk, show p * (2 * k) = 2 * (p * k) by ring,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      exact dvd_mul_right p k
    exact (hnoq p hp.out hp5 hdvd).elim
  ·
    exfalso
    have := Nat.eq_one_of_dvd_one hm
    omega

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
