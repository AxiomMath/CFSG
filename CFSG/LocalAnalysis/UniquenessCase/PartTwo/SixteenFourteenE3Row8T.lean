module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row8Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3E9Idem
public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.RankThree.PartTwo.Sec3.ElemNineAut
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.Asc83Table.GL23
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s1614e3_card_ieor {X : Type} [Group X] {p r : ℕ} [NeZero p]
    (h : IsElemAbelianOfRank p r X) : Nat.card X = p ^ r := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem s1614e3_card_mulAut_E9 {X : Type} [Group X] (h : IsElemAbelianOfRank 3 2 X) :
    Nat.card (MulAut X) = 48 := by
  obtain ⟨e⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    Nat.card_congr (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 3) 2).toEquiv]
  exact CFSG.RankThree.Asc83Table.card_GL23

private theorem s1614e3_isPGroup_three_of_iea {Y : Type} [Group Y] {E : Subgroup Y}
    (hE : IsElemAbelian 3 E) : IsPGroup 3 ↥E := fun x => ⟨1, by
  rw [pow_one]
  exact Subtype.ext (by simpa using hE.2 (x : Y) x.2)⟩

private def s1614e3_conjAut {Y : Type} [Group Y] {X A : Subgroup Y}
    (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (e : Y) (he : e ∈ X) : MulAut ↥A :=
  { toFun := fun a => ⟨e * a * e⁻¹, hn e he a a.2⟩
    invFun := fun a => ⟨e⁻¹ * a * e, by simpa using hn e⁻¹ (X.inv_mem he) a a.2⟩
    left_inv := fun a => by ext; group
    right_inv := fun a => by ext; group
    map_mul' := fun a b => by ext; simp only [Subgroup.coe_mul]; group }

private theorem s1614e3_conjAut_apply {Y : Type} [Group Y] {X A : Subgroup Y}
    (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A) (e : Y) (he : e ∈ X) (a : ↥A) :
    s1614e3_conjAut hn e he a = ⟨e * a * e⁻¹, hn e he a a.2⟩ := rfl

private def s1614e3_conjHom {Y : Type} [Group Y] {X A : Subgroup Y}
    (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {E : Subgroup Y} (hEX : E ≤ X) :
    ↥E →* MulAut ↥A where
  toFun e := s1614e3_conjAut hn (e : Y) (hEX e.2)
  map_one' := by ext a; simp [s1614e3_conjAut]
  map_mul' e f := by
    ext a
    simp only [s1614e3_conjAut_apply, MulAut.mul_apply, Subgroup.coe_mul]
    group

private theorem s1614e3_conjHom_apply {Y : Type} [Group Y] {X A : Subgroup Y}
    (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A) {E : Subgroup Y} (hEX : E ≤ X) (e : ↥E) :
    s1614e3_conjHom hn hEX e = s1614e3_conjAut hn (e : Y) (hEX e.2) := rfl

private theorem s1614e3_card_le_three_mul_inf {Y : Type} [Group Y] [Finite Y] {X A : Subgroup Y}
    (hAX : A ≤ X) (hA : IsElemAbelianOfRank 3 2 ↥A)
    (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hc : ∀ g ∈ X, (∀ a ∈ A, g * a = a * g) → g ∈ A)
    {E : Subgroup Y} (hEX : E ≤ X) (hE : IsPGroup 3 ↥E) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ A) := by
  classical
  let ρ : ↥E →* MulAut ↥A := s1614e3_conjHom hn hEX
  have hρe : ∀ e : ↥E, ρ e = s1614e3_conjAut hn (e : Y) (hEX e.2) :=
    fun e => s1614e3_conjHom_apply hn hEX e
  have hker_le : ρ.ker ≤ (E ⊓ A).subgroupOf E := by
    intro e he
    rw [MonoidHom.mem_ker] at he
    rw [Subgroup.mem_subgroupOf]
    refine ⟨e.2, ?_⟩
    apply hc (e : Y) (hEX e.2)
    intro a ha
    have h1 : ρ e ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [he, MulAut.one_apply]
    have h2 := congrArg Subtype.val h1
    rw [hρe e, s1614e3_conjAut_apply] at h2
    have h2' : (e : Y) * a * (e : Y)⁻¹ = a := by simpa using h2
    calc (e : Y) * a = (e : Y) * a * (e : Y)⁻¹ * (e : Y) := by group
      _ = a * (e : Y) := by rw [h2']
  have h1 : Nat.card ρ.ker ≤ Nat.card ↥(E ⊓ A) := by
    have h := Subgroup.card_le_of_le hker_le
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ A ≤ E)).toEquiv]
      at h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrange_pg : IsPGroup 3 ρ.range :=
    hE.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hrange_pg
  have hdvd : Nat.card ρ.range ∣ 48 := by
    rw [← s1614e3_card_mulAut_E9 hA]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  rw [hm] at hdvd
  have hm1 : m ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ m := by omega
    have h9 : 9 ∣ 3 ^ m := by
      obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h2
      exact ⟨3 ^ l, by ring⟩
    have h48 : 9 ∣ 48 := h9.trans hdvd
    norm_num at h48
  have hrange_le : Nat.card ρ.range ≤ 3 := by
    rw [hm]
    calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      _ = 3 := by norm_num
  have hcard := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at hcard
  rw [← hcard]
  calc Nat.card ρ.ker * Nat.card ρ.range ≤ Nat.card ↥(E ⊓ A) * 3 :=
        Nat.mul_le_mul h1 hrange_le
    _ = 3 * Nat.card ↥(E ⊓ A) := by ring

private theorem s1614e3_card_le_nine_of_inf {Y : Type} [Group Y] [Finite Y] {X A : Subgroup Y}
    (hAX : A ≤ X) (hA : IsElemAbelianOfRank 3 2 ↥A)
    (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hc : ∀ g ∈ X, (∀ a ∈ A, g * a = a * g) → g ∈ A)
    {E : Subgroup Y} (hEX : E ≤ X) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 2 := by
  have hcardA : Nat.card ↥A = 9 := s1614e3_card_ieor hA
  have hle := s1614e3_card_le_three_mul_inf hAX hA hn hc hEX
    (s1614e3_isPGroup_three_of_iea hE)
  have hdvd : Nat.card ↥(E ⊓ A) ∣ 9 := by
    rw [← hcardA]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hdvd' : Nat.card ↥(E ⊓ A) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]
    exact hdvd
  obtain ⟨i, hi2, hni⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd'
  by_cases h9 : Nat.card ↥(E ⊓ A) = 9
  · have hEq : E ⊓ A = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h9, hcardA])
    have hAE : A ≤ E := hEq ▸ inf_le_left
    have hEA : E ≤ A := by
      haveI : IsMulCommutative ↥E := hE.1
      intro e he
      apply hc e (hEX he)
      intro a ha
      have hcomm : (⟨e, he⟩ : ↥E) * ⟨a, hAE ha⟩ = ⟨a, hAE ha⟩ * ⟨e, he⟩ :=
        mul_comm' _ _
      exact congrArg Subtype.val hcomm
    calc Nat.card E ≤ Nat.card ↥A := Subgroup.card_le_of_le hEA
      _ = 9 := hcardA
      _ = 3 ^ 2 := by norm_num
  · have hi1 : i ≤ 1 := by
      rcases Nat.eq_or_lt_of_le hi2 with h2 | h2
      · exact absurd (by rw [hni, h2]; norm_num : Nat.card ↥(E ⊓ A) = 9) h9
      · omega
    have hle3 : Nat.card ↥(E ⊓ A) ≤ 3 := by
      calc Nat.card ↥(E ⊓ A) = 3 ^ i := hni
        _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi1
        _ = 3 := by norm_num
    calc Nat.card E ≤ 3 * Nat.card ↥(E ⊓ A) := hle
      _ ≤ 3 * 3 := Nat.mul_le_mul_left 3 hle3
      _ = 3 ^ 2 := by norm_num

theorem s1614e3_row8_pRank {Y : Type} [Group Y] [Finite Y] {X A : Subgroup Y} (hAX : A ≤ X)
    (hA : IsElemAbelianOfRank 3 2 ↥A) (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hc : ∀ g ∈ X, (∀ a ∈ A, g * a = a * g) → g ∈ A) : CFSG.Open.pRank 3 X ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
  intro E hEX hE
  exact s1614e3_card_le_nine_of_inf hAX hA hn hc hEX hE

theorem s1614e3_row8_inter {Y : Type} [Group Y] [Finite Y] {X A E : Subgroup Y} (hAX : A ≤ X)
    (hA : IsElemAbelianOfRank 3 2 ↥A) (hn : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hc : ∀ g ∈ X, (∀ a ∈ A, g * a = a * g) → g ∈ A) (hEX : E ≤ X)
    (hE : IsElemAbelianOfRank 3 2 ↥E) : ∃ e ∈ E, e ≠ 1 ∧ e ∈ A := by
  have hEea : IsElemAbelian 3 E := by
    obtain ⟨e⟩ := hE
    have h3 : ∀ y : Multiplicative (Fin 2 → ZMod 3), y ^ 3 = 1 := by
      intro y
      induction y using Multiplicative.rec with
      | ofAdd w =>
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3) 3 w, ZMod.natCast_self 3,
          zero_smul, ofAdd_zero]
    have hexp : ∀ y : ↥E, y ^ 3 = 1 := by
      intro y
      apply e.injective
      rw [map_pow, map_one]
      exact h3 (e y)
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply e.injective
      rw [map_mul, map_mul, mul_comm]
    · simpa using congrArg Subtype.val (hexp ⟨x, hx⟩)
  have hcardE : Nat.card ↥E = 9 := s1614e3_card_ieor hE
  have hle := s1614e3_card_le_three_mul_inf hAX hA hn hc hEX
    (s1614e3_isPGroup_three_of_iea hEea)
  have hS : 1 < Nat.card ↥(E ⊓ A) := by
    rw [hcardE] at hle
    omega
  haveI : Nontrivial ↥(E ⊓ A) := (Finite.one_lt_card_iff_nontrivial).1 hS
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(E ⊓ A))
  exact ⟨(x : Y), x.2.1, fun h => hx1 (Subtype.ext h), x.2.2⟩

private def s1614e3_conjAutT {Y : Type} [Group Y] {A : Subgroup Y} {t : Y} (ht2 : t * t = 1)
    (hnorm : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : MulAut ↥A :=
  { toFun := fun a => ⟨t * a * t⁻¹, hnorm a a.2⟩
    invFun := fun a => ⟨t⁻¹ * a * t, by
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      simpa [htinv] using hnorm a a.2⟩
    left_inv := fun a => by
      ext
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      simp only [Subtype.coe_mk]
      rw [htinv, show t * (t * ↑a * t) * t = (t * t) * ↑a * (t * t) by group, ht2]
      simp
    right_inv := fun a => by
      ext
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      simp only [Subtype.coe_mk]
      rw [htinv, show t * (t * ↑a * t) * t = (t * t) * ↑a * (t * t) by group, ht2]
      simp
    map_mul' := fun a b => by ext; simp only [Subtype.coe_mk, Subgroup.coe_mul]; group }

private theorem s1614e3_conjAutT_apply {Y : Type} [Group Y] {A : Subgroup Y} {t : Y}
    (ht2 : t * t = 1) (hnorm : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (a : ↥A) :
    s1614e3_conjAutT ht2 hnorm a = ⟨t * a * t⁻¹, hnorm a a.2⟩ := rfl

private theorem s1614e3_conjAutT_sq {Y : Type} [Group Y] {A : Subgroup Y} {t : Y}
    (ht2 : t * t = 1) (hnorm : ∀ a ∈ A, t * a * t⁻¹ ∈ A) :
    s1614e3_conjAutT ht2 hnorm * s1614e3_conjAutT ht2 hnorm = 1 := by
  ext a
  rw [MulAut.mul_apply, MulAut.one_apply, s1614e3_conjAutT_apply, s1614e3_conjAutT_apply]
  simp only [Subtype.coe_mk]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv, show t * (t * ↑a * t) * t = (t * t) * ↑a * (t * t) by group, ht2]
  simp

theorem s1614e3_row8_split {Y : Type} [Group Y] {A : Subgroup Y}
    (hA : IsElemAbelianOfRank 3 2 ↥A) {t : Y} (ht2 : t * t = 1)
    (hnorm : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hnc : ∃ a ∈ A, t * a ≠ a * t) :
    (∀ a ∈ A, t * a * t⁻¹ = a⁻¹) ∨
      ∃ κ ∈ A, ∃ k ∈ A, κ ^ 3 = 1 ∧ k ^ 3 = 1 ∧ κ * k = k * κ ∧ t * κ = κ * t ∧
        t * k * t⁻¹ = k⁻¹ ∧ ∀ x ∈ A, ∃ i j : ℕ, x = κ ^ i * k ^ j := by
  have h9 : Nat.card ↥A = 9 := s1614e3_card_ieor hA
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [h9]; norm_num)
  obtain ⟨e⟩ := hA
  have hcomm : ∀ x y : ↥A, x * y = y * x := by
    intro x y
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have h3 : ∀ x : ↥A, x ^ 3 = 1 := by
    intro x
    apply e.injective
    rw [map_pow, map_one]
    have h3' : ∀ y : Multiplicative (Fin 2 → ZMod 3), y ^ 3 = 1 := by
      intro y
      induction y using Multiplicative.rec with
      | ofAdd w =>
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3) 3 w, ZMod.natCast_self 3,
          zero_smul, ofAdd_zero]
    exact h3' (e x)
  letI : CommGroup ↥A := { (inferInstance : Group ↥A) with mul_comm := hcomm }
  let σ : MulAut ↥A := s1614e3_conjAutT ht2 hnorm
  have hσ : σ * σ = 1 := s1614e3_conjAutT_sq ht2 hnorm
  by_cases hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹
  · exact Or.inl hinv
  · right
    have hσι : ¬ ∀ b : ↥A, σ b = b⁻¹ := by
      intro h
      apply hinv
      intro a ha
      have hb := h ⟨a, ha⟩
      rw [s1614e3_conjAutT_apply] at hb
      have hb' := congrArg Subtype.val hb
      simpa using hb'
    have hσ1 : σ ≠ 1 := by
      intro h
      obtain ⟨a, ha, hne⟩ := hnc
      have hb := congrArg (fun f : MulAut ↥A => f ⟨a, ha⟩) h
      rw [MulAut.one_apply, s1614e3_conjAutT_apply] at hb
      have hb' := congrArg Subtype.val hb
      simp only [Subtype.coe_mk] at hb'
      apply hne
      calc t * a = t * a * t⁻¹ * t := by group
        _ = a * t := by rw [hb']
    obtain ⟨x, hx1, hσκ⟩ :=
      CFSG.RankThree.PartTwo.Sec3.exists_apply_eq_self_of_mul_self_eq_one h3 hσ hσι
    obtain ⟨d, hd1, hσd⟩ :=
      CFSG.RankThree.PartTwo.Sec3.exists_apply_eq_inv_of_mul_self_eq_one hσ hσ1
    have hd_notmem : d ∉ Subgroup.zpowers x := by
      intro hd
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hd
      have h2 : σ (x ^ n) = (x ^ n)⁻¹ := by rw [hn]; exact hσd
      have h1 : σ (x ^ n) = x ^ n := by rw [map_zpow, hσκ]
      have hx1' : x ^ n = 1 :=
        CFSG.RankThree.PartTwo.Sec3.eq_one_of_apply_eq_self_of_apply_eq_inv h3 h1 h2
      exact hd1 (by rw [← hn, hx1'])
    refine ⟨(x : Y), x.2, (d : Y), d.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg Subtype.val (h3 x)
    · simpa using congrArg Subtype.val (h3 d)
    · simpa using congrArg Subtype.val (hcomm x d)
    · have hb := hσκ
      rw [s1614e3_conjAutT_apply] at hb
      have hb' := congrArg Subtype.val hb
      simp only [Subtype.coe_mk] at hb'
      calc t * (x : Y) = t * (x : Y) * t⁻¹ * t := by group
        _ = (x : Y) * t := by rw [hb']
    · have hb := hσd
      rw [s1614e3_conjAutT_apply] at hb
      have hb' := congrArg Subtype.val hb
      simpa using hb'
    · intro y hy
      obtain ⟨⟨i, j⟩, hij⟩ :=
        (CFSG.RankThree.PartTwo.Sec3.bijective_pow_mul_pow h3 h9 hx1 hd_notmem).2 ⟨y, hy⟩
      refine ⟨(i : ℕ), (j : ℕ), ?_⟩
      have hval := congrArg Subtype.val hij
      simp only [Subgroup.coe_mul, Subgroup.coe_pow] at hval
      exact hval.symm

theorem s1614e3_row8_inv {T : Type} [CommGroup T] [Finite T] (hT : ∀ x : T, x ^ 2 = 1)
    (hrk : rk (⊤ : Subgroup T) = 8) {A : Subgroup (MulAut T)} (hA : IsElemAbelianOfRank 3 2 ↥A)
    (hfix : fixV A = ⊥) {t : MulAut T} (ht2 : t * t = 1)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) : rk (fixV (Subgroup.zpowers t)) ≤ 4 := by
  obtain ⟨a, haA, b, hbA, ha, hb, hab, hgen⟩ := s16t_exists_gens_E9 hA
  have hza : t * a * t⁻¹ = a⁻¹ := hinv a haA
  have hzb : t * b * t⁻¹ = b⁻¹ := hinv b hbA
  have hfix' : ∀ v : T, a v = v → b v = v → v = 1 := by
    intro v hav hbv
    have hv : v ∈ fixV A := by
      rw [mem_fixV]
      intro x hx
      obtain ⟨i, j, rfl⟩ := hgen x hx
      clear hx
      simp only [MulAut.mul_apply]
      have hb_pow : (b ^ j) v = v := by
        induction j with
        | zero => rfl
        | succ j ih => rw [pow_succ, MulAut.mul_apply, hbv, ih]
      rw [hb_pow]
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ, MulAut.mul_apply, hav, ih]
    rw [hfix, Subgroup.mem_bot] at hv
    exact hv
  have hle := s16t_fixV_le_commV_of_inv hT ha hb hab hza hzb hfix'
  have hmono : rk (fixV (Subgroup.zpowers t)) ≤ rk (commV (Subgroup.zpowers t)) := rk_mono hle
  have hsum := rk_commV_add_rk_fixV t
  have hT8 : rk T = 8 := by rw [← rk_top]; exact hrk
  rw [hT8] at hsum
  omega

theorem s1614e3_row8_witness {T : Type} [CommGroup T] [Finite T] (hT : ∀ x : T, x ^ 2 = 1)
    (hrk : rk (⊤ : Subgroup T) = 8) {A : Subgroup (MulAut T)} (hA : IsElemAbelianOfRank 3 2 ↥A)
    (hfix : fixV A = ⊥) {t : MulAut T} (ht2 : t * t = 1)
    (hnorm : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hnc : ∃ a ∈ A, t * a ≠ a * t) {W : Subgroup T}
    (hW : W ≤ fixV (Subgroup.zpowers t)) (hWr : rkIdx W ≤ 3) {e : MulAut T} (he : e ∈ A) :
    ∃ Z : Subgroup T, Z ≠ ⊥ ∧ Z ≤ W ∧ Z.map e.toMonoidHom = Z := by
  rcases s1614e3_row8_split hA ht2 hnorm hnc with
    hinv | ⟨κ, hκA, k, hkA, hκ, hk, hκk, htκ, htk, hgen⟩
  · exfalso
    have hri := s1614e3_row8_inv hT hrk hA hfix ht2 hinv
    have hmono : rk W ≤ rk (fixV (Subgroup.zpowers t)) := rk_mono hW
    have hsum := rk_add_rkIdx W
    have hT8 : rk T = 8 := by rw [← rk_top]; exact hrk
    rw [hT8] at hsum
    omega
  · have hfix' : ∀ x : T, κ x = x → k x = x → x = 1 := by
      intro x hκx hkx
      have hx : x ∈ fixV A := by
        rw [mem_fixV]
        intro y hy
        obtain ⟨i, j, rfl⟩ := hgen y hy
        clear hy
        simp only [MulAut.mul_apply]
        have hk_pow : (k ^ j) x = x := by
          induction j with
          | zero => rfl
          | succ j ih => rw [pow_succ, MulAut.mul_apply, hkx, ih]
        rw [hk_pow]
        induction i with
        | zero => rfl
        | succ i ih => rw [pow_succ, MulAut.mul_apply, hκx, ih]
      rw [hfix, Subgroup.mem_bot] at hx
      exact hx
    obtain ⟨i, j, hij⟩ := hgen e he
    exact s1614e3_row8_core hT hrk hκ hk hκk htκ htk ht2 hfix' hW hWr ⟨i, j, hij⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
