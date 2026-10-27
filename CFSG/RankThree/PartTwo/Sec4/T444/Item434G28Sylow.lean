module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Model
public import Certificates.Certificate9546
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GroupTheory.ElementaryAbelianTransport

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem exists_conj_le_of_card {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q E : Subgroup G} (hQ : Nat.card Q = p ^ (Nat.card G).factorization p)
    (hE : IsPGroup p E) : ∃ g : G, ∀ e ∈ E, g⁻¹ * e * g ∈ Q := by
  let S0 : Sylow p G := Sylow.ofCard Q hQ
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 S
  refine ⟨g, fun e he => ?_⟩
  have hmem : e ∈ ((g • S0 : Sylow p G) : Subgroup G) := by
    rw [hg]
    exact hS he
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  exact hmem

theorem factorization_eq_of_mul {n m k p : ℕ} [Fact p.Prime] (h : n = p ^ k * m) (hm : ¬ p ∣ m) :
    n.factorization p = k := by
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero p)
  rw [h, Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0]
  simp [Nat.factorization_eq_zero_of_not_dvd hm, (Fact.out : p.Prime).factorization_pow]

section Model


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem valid_u9Code : Valid u9Code := valid_wordCode _

theorem valid_z9Code : Valid z9Code := valid_wordCode _

theorem valid_omegaCode : Valid omegaCode := valid_wordCode _

theorem valid_uCode : Valid uCode := valid_powCode valid_u9Code 3

theorem valid_zCode : Valid zCode := valid_powCode valid_z9Code 3

theorem valid_t3L {i : ℕ} (hi : i < 243) : Valid t3L[i]! :=
  valid_t3List valid_u9Code valid_z9Code valid_omegaCode hi

theorem valid_e0L {i : ℕ} (hi : i < 9) : Valid e0L[i]! := valid_e0List valid_uCode valid_zCode hi

namespace G28Model

theorem eq_iff_codes {g h : ↥(adjointGroup .G2 K)} {A B : Array ℕ} (hA : Valid A) (hB : Valid B)
    (hg : M.rho g = decode A) (hh : M.rho h = decode B) : g = h ↔ A = B := by
  constructor
  · intro e
    rw [e] at hg
    exact eq_of_decode_eq hA hB (hg.symm.trans hh)
  · intro e
    subst e
    exact M.rho_injective (hg.trans hh.symm)

theorem eq_one_iff_code {g : ↥(adjointGroup .G2 K)} {A : Array ℕ} (hA : Valid A)
    (hg : M.rho g = decode A) : g = 1 ↔ A = idCode :=
  M.eq_iff_codes hA valid_idCode hg (by rw [map_one, decode_idCode])

theorem rho_mul_code {g h : ↥(adjointGroup .G2 K)} {A B : Array ℕ} (hA : Valid A) (hB : Valid B)
    (hg : M.rho g = decode A) (hh : M.rho h = decode B) :
    M.rho (g * h) = decode (mulCode A B) := by
  rw [map_mul, hg, hh, decode_mulCode hA hB]

@[expose] noncomputable def u9 : ↥(adjointGroup .G2 K) := M.wordElt u9W

@[expose] noncomputable def z9 : ↥(adjointGroup .G2 K) := M.wordElt z9W

@[expose] noncomputable def om : ↥(adjointGroup .G2 K) := M.wordElt omegaW

@[expose] noncomputable def uE : ↥(adjointGroup .G2 K) := M.u9 ^ 3

@[expose] noncomputable def zE : ↥(adjointGroup .G2 K) := M.z9 ^ 3

theorem rho_u9 : M.rho M.u9 = decode u9Code := M.rho_wordElt u9W

theorem rho_z9 : M.rho M.z9 = decode z9Code := M.rho_wordElt z9W

theorem rho_om : M.rho M.om = decode omegaCode := M.rho_wordElt omegaW

theorem rho_uE : M.rho M.uE = decode uCode := (M.rho_pow M.u9 valid_u9Code M.rho_u9 3).2

theorem rho_zE : M.rho M.zE = decode zCode := (M.rho_pow M.z9 valid_z9Code M.rho_z9 3).2

@[expose] noncomputable def t3Elt (n : ℕ) : ↥(adjointGroup .G2 K) :=
  M.u9 ^ (n / 27) * M.z9 ^ ((n / 3) % 9) * M.om ^ (n % 3)

theorem rho_t3Elt {n : ℕ} (hn : n < 243) : M.rho (M.t3Elt n) = decode t3L[n]! := by
  obtain ⟨h1, h1'⟩ := M.rho_pow M.u9 valid_u9Code M.rho_u9 (n / 27)
  obtain ⟨h2, h2'⟩ := M.rho_pow M.z9 valid_z9Code M.rho_z9 ((n / 3) % 9)
  obtain ⟨h3, h3'⟩ := M.rho_pow M.om valid_omegaCode M.rho_om (n % 3)
  rw [t3Elt, M.rho_mul_code (valid_mulCode h1 h2) h3 (M.rho_mul_code h1 h2 h1' h2') h3',
    t3L, getElem!_t3List _ _ _ hn]

@[expose] noncomputable def e0Elt (n : ℕ) : ↥(adjointGroup .G2 K) :=
  M.uE ^ (n / 3) * M.zE ^ (n % 3)

theorem rho_e0Elt {n : ℕ} (hn : n < 9) : M.rho (M.e0Elt n) = decode e0L[n]! := by
  obtain ⟨h1, h1'⟩ := M.rho_pow M.uE valid_uCode M.rho_uE (n / 3)
  obtain ⟨h2, h2'⟩ := M.rho_pow M.zE valid_zCode M.rho_zE (n % 3)
  rw [e0Elt, M.rho_mul_code h1 h2 h1' h2', e0L, getElem!_e0List _ _ hn]

end G28Model

end Model


section Sylow


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem t3L_spec :
    t3L.size = 243 ∧ t3L[0]! = idCode ∧ (∀ i < 243, ∀ j < i, t3L[i]! ≠ t3L[j]!) ∧
    (∀ i < 243, ∀ j < 243, ∃ k < 243, mulCode t3L[i]! t3L[j]! = t3L[k]!) ∧
    (∀ i < 243, ∃ j < 243, mulCode t3L[i]! t3L[j]! = idCode) :=
  t3OK_spec Certificates.certificate9546.1

namespace G28Model

@[expose] noncomputable def T3 : Subgroup ↥(adjointGroup .G2 K) where
  carrier := {g | ∃ i < 243, M.rho g = decode t3L[i]!}
  mul_mem' := by
    rintro a b ⟨i, hi, ha⟩ ⟨j, hj, hb⟩
    obtain ⟨k, hk, hk'⟩ := t3L_spec.2.2.2.1 i hi j hj
    exact ⟨k, hk, by rw [M.rho_mul_code (valid_t3L hi) (valid_t3L hj) ha hb, hk']⟩
  one_mem' := ⟨0, by norm_num, by rw [t3L_spec.2.1, map_one, decode_idCode]⟩
  inv_mem' := by
    rintro a ⟨i, hi, ha⟩
    obtain ⟨j, hj, hj'⟩ := t3L_spec.2.2.2.2 i hi
    refine ⟨j, hj, ?_⟩
    have h1 : M.rho a⁻¹ * M.rho a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : decode t3L[i]! * decode t3L[j]! = 1 := by
      rw [← decode_mulCode (valid_t3L hi) (valid_t3L hj), hj', decode_idCode]
    calc M.rho a⁻¹ = M.rho a⁻¹ * (decode t3L[i]! * decode t3L[j]!) := by rw [h2, mul_one]
      _ = (M.rho a⁻¹ * M.rho a) * decode t3L[j]! := by rw [← ha, mul_assoc]
      _ = decode t3L[j]! := by rw [h1, one_mul]

theorem mem_T3_iff (g : ↥(adjointGroup .G2 K)) :
    g ∈ M.T3 ↔ ∃ i < 243, M.rho g = decode t3L[i]! := Iff.rfl

theorem t3Elt_mem {n : ℕ} (hn : n < 243) : M.t3Elt n ∈ M.T3 := ⟨n, hn, M.rho_t3Elt hn⟩

theorem card_T3 : Nat.card M.T3 = 243 := by
  have hbij : Function.Bijective
      (fun i : Fin 243 => (⟨M.t3Elt i, M.t3Elt_mem i.2⟩ : M.T3)) := by
    constructor
    · intro i j hij
      have h : M.t3Elt i = M.t3Elt j := congrArg Subtype.val hij
      have hc := (M.eq_iff_codes (valid_t3L i.2) (valid_t3L j.2) (M.rho_t3Elt i.2)
        (M.rho_t3Elt j.2)).1 h
      by_contra hne
      have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne' with h | h
      · exact t3L_spec.2.2.1 j.val j.2 i.val h hc.symm
      · exact t3L_spec.2.2.1 i.val i.2 j.val h hc
    · rintro ⟨g, i, hi, hg⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      exact M.rho_injective ((M.rho_t3Elt hi).trans hg.symm)
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_X (hK : Nat.card K = 8) :
    Nat.card ↥(adjointGroup .G2 K) = 3 ^ 5 * 17816092672 := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
  norm_num [ordG2]

theorem factorization_X {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 8) :
    (Nat.card ↥(adjointGroup .G2 K)).factorization 3 = 5 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact factorization_eq_of_mul (card_X hK) (by norm_num)

theorem exists_conj_T3 (hK : Nat.card K = 8) {E : Subgroup ↥(adjointGroup .G2 K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    ∃ g : ↥(adjointGroup .G2 K), ∀ e ∈ E, g⁻¹ * e * g ∈ M.T3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥(adjointGroup .G2 K) := Subtype.finite
  exact exists_conj_le_of_card (by rw [M.card_T3, factorization_X hK]; norm_num)
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hE)

end G28Model

end Sylow

theorem exists_mem_notMem_zpowers {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE9 : Nat.card E = 9) (t : H) (ht3 : t ^ 3 = 1) : ∃ f ∈ E, f ∉ Subgroup.zpowers t := by
  by_contra hc
  push Not at hc
  have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers t from hc)
  rw [hE9, Nat.card_zpowers] at h1
  have h2 : orderOf t ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ht3)
  omega

theorem eq_one_or_eq_or_eq_sq_of_mem_zpowers {H : Type*} [Group H] {a g : H} (ha : a ^ 3 = 1)
    (hg : g ∈ Subgroup.zpowers a) : g = 1 ∨ g = a ∨ g = a * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h3 : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha
  have hk : a ^ k = a ^ (k % 3) := by
    have := Int.emod_add_mul_ediv k 3
    conv_lhs => rw [← this, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exact Or.inl (by rw [hk, h]; simp)
  · exact Or.inr (Or.inl (by rw [hk, h]; simp))
  · exact Or.inr (Or.inr (by rw [hk, h, zpow_two]))

section Classify


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem uz_spec :
    uCode ≠ idCode ∧ powCode uCode 3 = idCode ∧ powCode zCode 3 = idCode ∧
      mulCode uCode zCode = mulCode zCode uCode ∧ zCode ≠ idCode ∧ zCode ≠ uCode ∧
      zCode ≠ mulCode uCode uCode :=
  goodPair_spec Certificates.certificate9546.2.1

namespace G28Model

@[expose] noncomputable def E0 : Subgroup ↥(adjointGroup .G2 K) :=
  Subgroup.zpowers M.uE ⊔ Subgroup.zpowers M.zE

theorem uE_ne_one : M.uE ≠ 1 := fun h =>
  uz_spec.1 ((M.eq_one_iff_code valid_uCode M.rho_uE).1 h)

theorem zE_ne_one : M.zE ≠ 1 := fun h =>
  uz_spec.2.2.2.2.1 ((M.eq_one_iff_code valid_zCode M.rho_zE).1 h)

theorem uE_pow_three : M.uE ^ 3 = 1 := by
  obtain ⟨h1, h2⟩ := M.rho_pow M.uE valid_uCode M.rho_uE 3
  exact (M.eq_one_iff_code h1 h2).2 uz_spec.2.1

theorem zE_pow_three : M.zE ^ 3 = 1 := by
  obtain ⟨h1, h2⟩ := M.rho_pow M.zE valid_zCode M.rho_zE 3
  exact (M.eq_one_iff_code h1 h2).2 uz_spec.2.2.1

theorem uE_mul_zE : M.uE * M.zE = M.zE * M.uE := by
  have h1 := M.rho_mul_code valid_uCode valid_zCode M.rho_uE M.rho_zE
  have h2 := M.rho_mul_code valid_zCode valid_uCode M.rho_zE M.rho_uE
  exact (M.eq_iff_codes (valid_mulCode valid_uCode valid_zCode)
    (valid_mulCode valid_zCode valid_uCode) h1 h2).2 uz_spec.2.2.2.1

theorem zE_notMem_zpowers_uE : M.zE ∉ Subgroup.zpowers M.uE := by
  intro h
  rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers M.uE_pow_three h with h | h | h
  · exact M.zE_ne_one h
  · exact uz_spec.2.2.2.2.2.1 ((M.eq_iff_codes valid_zCode valid_uCode M.rho_zE M.rho_uE).1 h)
  · exact uz_spec.2.2.2.2.2.2
      ((M.eq_iff_codes valid_zCode (valid_mulCode valid_uCode valid_uCode) M.rho_zE
        (M.rho_mul_code valid_uCode valid_uCode M.rho_uE M.rho_uE)).1 h)

theorem isElemAbelian_zpowers {H : Type*} [Group H] {a : H} (ha : a ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a) := CFSG.Open.isElemAbelian_zpowers ha

theorem orderOf_uE : orderOf M.uE = 3 := orderOf_eq_prime M.uE_pow_three M.uE_ne_one

theorem isElemAbelian_E0_card :
    CFSG.Assembly.IsElemAbelian 3 M.E0 ∧ Nat.card M.E0 = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a ∈ Subgroup.zpowers M.uE, a * M.zE = M.zE * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left M.uE_mul_zE k).eq
  obtain ⟨h1, h2⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
    (isElemAbelian_zpowers M.uE_pow_three) M.zE_notMem_zpowers_uE M.zE_pow_three hcomm
  refine ⟨h1, ?_⟩
  rw [E0, h2, Nat.card_zpowers, M.orderOf_uE]

theorem uE_mem_E0 : M.uE ∈ M.E0 := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem zE_mem_E0 : M.zE ∈ M.E0 := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem e0Elt_mem {n : ℕ} : M.e0Elt n ∈ M.E0 :=
  Subgroup.mul_mem _ (pow_mem M.uE_mem_E0 _) (pow_mem M.zE_mem_E0 _)


@[expose] noncomputable def gElt (v : ℕ) : ↥(adjointGroup .G2 K) := M.wordElt conjW[v]!

@[expose] noncomputable def gElt' (v : ℕ) : ↥(adjointGroup .G2 K) := M.wordElt conjW[v]!.reverse

theorem conjW_size : conjW.size = 28 := by rfl

theorem rho_gElt {v : ℕ} (hv : v < conjW.size) : M.rho (M.gElt v) = decode conjG[v]! := by
  rw [gElt, M.rho_wordElt, conjG, getElem!_pos (conjW.map wordCode) v (by simpa using hv),
    Array.getElem_map, getElem!_pos conjW v hv]

theorem rho_gElt' {v : ℕ} (hv : v < conjW.size) : M.rho (M.gElt' v) = decode conjGi[v]! := by
  rw [gElt', M.rho_wordElt, conjGi, getElem!_pos (conjW.map invWordCode) v (by simpa using hv),
    Array.getElem_map, getElem!_pos conjW v hv]
  rfl

theorem exists_conj_E0 (hK : Nat.card K = 8) {E : Subgroup ↥(adjointGroup .G2 K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ h : ↥(adjointGroup .G2 K), ∀ e ∈ E, h * e * h⁻¹ ∈ M.E0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥(adjointGroup .G2 K) := Subtype.finite
  obtain ⟨g₁, hg₁⟩ := M.exists_conj_T3 hK hE
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [hbot, Subgroup.card_bot] at hE9
    omega
  have ha3 : a ^ 3 = 1 := hE.2 a haE
  obtain ⟨b, hbE, hb⟩ := exists_mem_notMem_zpowers hE9 a ha3
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hba : b ≠ a := fun h => hb (h ▸ Subgroup.mem_zpowers a)
  have hba2 : b ≠ a * a := fun h => hb (h ▸ Subgroup.mul_mem _ (Subgroup.mem_zpowers a)
    (Subgroup.mem_zpowers a))
  have hab : a * b = b * a := hE.1.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩ |> congrArg Subtype.val
  set φ : ↥(adjointGroup .G2 K) →* ↥(adjointGroup .G2 K) := (MulAut.conj g₁⁻¹).toMonoidHom
    with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g₁⁻¹).injective
  have hφapp : ∀ x, φ x = g₁⁻¹ * x * g₁ := fun x => by
    simp [hφ]
  obtain ⟨i, hi, hai⟩ := hg₁ a haE
  obtain ⟨j, hj, hbj⟩ := hg₁ b hbE
  rw [← hφapp] at hai hbj
  have hvi := valid_t3L hi
  have hvj := valid_t3L hj
  have hgood : goodPair t3L[i]! t3L[j]! = true := by
    refine goodPair_of ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h
      exact ha1 (hφinj (by rw [map_one]; exact (M.eq_one_iff_code hvi hai).2 h))
    · obtain ⟨h1, h2⟩ := M.rho_pow (φ a) hvi hai 3
      refine (M.eq_one_iff_code h1 h2).1 ?_
      rw [← map_pow, ha3, map_one]
    · obtain ⟨h1, h2⟩ := M.rho_pow (φ b) hvj hbj 3
      refine (M.eq_one_iff_code h1 h2).1 ?_
      rw [← map_pow, hE.2 b hbE, map_one]
    · exact (M.eq_iff_codes (valid_mulCode hvi hvj) (valid_mulCode hvj hvi)
        (M.rho_mul_code hvi hvj hai hbj) (M.rho_mul_code hvj hvi hbj hai)).1
        (by rw [← map_mul, ← map_mul, hab])
    · intro h
      exact hb1 (hφinj (by rw [map_one]; exact (M.eq_one_iff_code hvj hbj).2 h))
    · intro h
      exact hba (hφinj ((M.eq_iff_codes hvj hvi hbj hai).2 h))
    · intro h
      exact hba2 (hφinj (by
        rw [map_mul]
        exact (M.eq_iff_codes hvj (valid_mulCode hvi hvi) hbj
          (M.rho_mul_code hvi hvi hai hai)).2 h))
  obtain ⟨-, hconj⟩ := conjOK_spec Certificates.certificate9546.2.2
  obtain ⟨hinvs, -⟩ := conjOK_spec Certificates.certificate9546.2.2
  obtain ⟨v, hv, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩ := hconj i hi j hj hgood
  have hvW : v < conjW.size := by simpa [conjG] using hv
  have hm1' : m1 < 9 := by simpa [e0L, size_e0List] using hm1
  have hm2' : m2 < 9 := by simpa [e0L, size_e0List] using hm2
  have hgv := M.rho_gElt hvW
  have hgv' := M.rho_gElt' hvW
  have hvg : Valid conjG[v]! := by
    rw [conjG, getElem!_pos (conjW.map wordCode) v (by simpa using hvW), Array.getElem_map]
    exact valid_wordCode _
  have hvg' : Valid conjGi[v]! := by
    rw [conjGi, getElem!_pos (conjW.map invWordCode) v (by simpa using hvW), Array.getElem_map]
    exact valid_wordCode _
  have hinv : M.gElt v * M.gElt' v = 1 := by
    refine (M.eq_one_iff_code (valid_mulCode hvg hvg') (M.rho_mul_code hvg hvg' hgv hgv')).2 ?_
    exact hinvs v hv
  have hinv' : M.gElt' v = (M.gElt v)⁻¹ := eq_inv_of_mul_eq_one_right hinv
  have himg : ∀ x, ∀ k, k < 243 → M.rho (φ x) = decode t3L[k]! → ∀ m, m < 9 →
      mulCode (mulCode conjG[v]! t3L[k]!) conjGi[v]! = e0L[m]! →
      M.gElt v * φ x * (M.gElt v)⁻¹ ∈ M.E0 := by
    intro x k hk hx m hm he
    have hvk := valid_t3L hk
    have h1 := M.rho_mul_code (valid_mulCode hvg hvk) hvg'
      (M.rho_mul_code hvg hvk hgv hx) hgv'
    rw [he] at h1
    rw [← hinv']
    have : M.gElt v * φ x * M.gElt' v = M.e0Elt m :=
      M.rho_injective (h1.trans (M.rho_e0Elt hm).symm)
    rw [this]
    exact M.e0Elt_mem
  have hA := himg a i hi hai m1 hm1' e1
  have hB := himg b j hj hbj m2 hm2' e2
  have hAab : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a) := isElemAbelian_zpowers ha3
  have hcomm : ∀ x ∈ Subgroup.zpowers a, x * b = b * x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left hab k).eq
  obtain ⟨-, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hAab hb
    (hE.2 b hbE) hcomm
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ E :=
    sup_le (Subgroup.zpowers_le.mpr haE) (Subgroup.zpowers_le.mpr hbE)
  have hEeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = E := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard, Nat.card_zpowers, orderOf_eq_prime ha3 ha1, hE9]
  refine ⟨M.gElt v * g₁⁻¹, fun e he => ?_⟩
  rw [← hEeq] at he
  let N : Subgroup ↥(adjointGroup .G2 K) := M.E0.comap (MulAut.conj (M.gElt v * g₁⁻¹)).toMonoidHom
  have haN : a ∈ N := by
    show (MulAut.conj (M.gElt v * g₁⁻¹)) a ∈ M.E0
    have : (MulAut.conj (M.gElt v * g₁⁻¹)) a = M.gElt v * φ a * (M.gElt v)⁻¹ := by
      rw [hφapp]; simp only [MulAut.conj_apply]; group
    rw [this]; exact hA
  have hbN : b ∈ N := by
    show (MulAut.conj (M.gElt v * g₁⁻¹)) b ∈ M.E0
    have : (MulAut.conj (M.gElt v * g₁⁻¹)) b = M.gElt v * φ b * (M.gElt v)⁻¹ := by
      rw [hφapp]; simp only [MulAut.conj_apply]; group
    rw [this]; exact hB
  have hsN : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ N :=
    sup_le (Subgroup.zpowers_le.mpr haN) (Subgroup.zpowers_le.mpr hbN)
  have h4 : (MulAut.conj (M.gElt v * g₁⁻¹)) e ∈ M.E0 := hsN he
  rwa [MulAut.conj_apply] at h4

end G28Model

end Classify

end CFSG.RankThree.PartTwo.Sec4.Item434G28
