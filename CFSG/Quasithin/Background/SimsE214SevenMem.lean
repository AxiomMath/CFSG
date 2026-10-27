module

public import CFSG.Quasithin.Background.SimsE214SevenSp4
public import CFSG.Quasithin.Background.SimsE214SevenSz
public import CFSG.Quasithin.Background.SimsE214SevenDih
public import CFSG.Quasithin.Background.SimsE214NatThree
public import CFSG.Quasithin.Background.SimsE214NatFive
public import CFSG.Quasithin.Background.SimsE214Easy
public import CFSG.Quasithin.Background.SimsE2NParam
import CFSG.Quasithin.Vol2.GoldschmidtF431SpModelLie
import CFSG.CGT.Timmesfeld75.Sec3IsoParts

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214S

theorem exists_statedSL_of_isPSL {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSL 2 K)) := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  exact ⟨K, inferInstance, inferInstance, hcard,
    ⟨(e.trans CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj.symm).trans
      (specialLinearGroupEquivStatedSL 2 K)⟩⟩

theorem exists_statedSL_of_dihedral_three {X : Type} [Group X] (e : X ≃* DihedralGroup 3) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 1 ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSL 2 K)) := by
  obtain ⟨e'⟩ := CFSG.CGT.Timmesfeld75.sl2_mulEquiv_dihedral_three_of_card_two (F := ZMod 2)
    (by rw [Nat.card_zmod])
  exact ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(e.trans e').trans (specialLinearGroupEquivStatedSL 2 (ZMod 2))⟩⟩

theorem nonempty_statedSL_mulEquiv {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F']
    (h : Nat.card F = Nat.card F') :
    Nonempty (↥(CFSG.Open.StatedSL 2 F) ≃* ↥(CFSG.Open.StatedSL 2 F')) := by
  classical
  let _ := Fintype.ofFinite F
  let _ := Fintype.ofFinite F'
  let c : F ≃+* F' := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h])
  let φ : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F' :=
    Matrix.SpecialLinearGroup.map c.toRingHom
  let φ' : Matrix.SpecialLinearGroup (Fin 2) F' →* Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map c.symm.toRingHom
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F' :=
    MonoidHom.toMulEquiv φ φ'
      (by ext A i j; simp [φ, φ']) (by ext A i j; simp [φ, φ'])
  exact ⟨((specialLinearGroupEquivStatedSL 2 F).symm.trans e).trans
    (specialLinearGroupEquivStatedSL 2 F')⟩

theorem dParamPrime_five : E2.dParamPrime 5 = 2 := by
  have h : E2.dParam 5 = 4 := by
    unfold E2.dParam
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)
  unfold E2.dParamPrime
  rw [h]
  decide

theorem eq_three_or_five_of_dParamPrime_le {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hd : E2.dParamPrime (p ^ a) ≤ 2) : p ^ a = 3 ∨ p ^ a = 5 := by
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ a := ⟨_, rfl⟩
  rw [← hq] at hd ⊢
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by
    rw [hq]
    exact le_trans hp3 (Nat.le_self_pow (by omega) p)
  have hqodd : Odd q := by rw [hq]; exact (hp.odd_of_ne_two hp2).pow
  have : NeZero q := ⟨by omega⟩
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.2 hqodd
  have hpos : 0 < E2.dParam q := by
    unfold E2.dParam
    have h1 : orderOf (ZMod.unitOfCoprime 2 hcop) = orderOf (2 : ZMod q) := by
      rw [← orderOf_units]
      rfl
    rw [← h1]
    exact orderOf_pos _
  have hpow : (2 : ZMod q) ^ E2.dParam q = 1 := pow_orderOf_eq_one _
  have hdvd : q ∣ 2 ^ E2.dParam q - 1 := by
    have h1 : ((2 ^ E2.dParam q - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [hpow, sub_self]
    exact (CharP.cast_eq_zero_iff (ZMod q) q _).1 h1
  obtain ⟨d, hd'⟩ : ∃ d, E2.dParam q = d := ⟨_, rfl⟩
  rw [hd'] at hpos hdvd
  have hd4 : d ≤ 4 := by
    unfold E2.dParamPrime at hd
    rw [hd'] at hd
    split_ifs at hd with hev
    · obtain ⟨m, hm⟩ := hev
      omega
    · omega
  have hqle : q ≤ 15 := by
    have h15 : 2 ^ d - 1 ≤ 15 := by
      have : 2 ^ d ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hd4
      omega
    exact (Nat.le_of_dvd (by have := Nat.one_lt_two_pow (n := d) (by omega); omega) hdvd).trans
      h15
  interval_cases d
  ·
    exfalso
    norm_num at hdvd
    omega
  ·
    left
    norm_num at hdvd
    exact le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hq3
  ·
    exfalso
    norm_num at hdvd
    have h7 : q = 7 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases q <;> omega
    unfold E2.dParamPrime at hd
    rw [hd'] at hd
    split_ifs at hd with hev
    · exact absurd hev (by decide)
    · omega
  ·
    norm_num at hdvd
    have hq15 : q = 3 ∨ q = 5 ∨ q = 15 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases q <;> omega
    rcases hq15 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hpa : p ^ a = 15 := hq ▸ h
      have hp15 : p ∣ 15 := hpa ▸ dvd_pow_self p (by omega)
      have h35 : p = 3 ∨ p = 5 := by
        have : p ∣ 3 * 5 := by norm_num; exact hp15
        rcases (Nat.Prime.dvd_mul hp).1 this with h3 | h5
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5)
      rcases h35 with rfl | rfl
      · have h5 : 5 ∣ 3 ^ a := by rw [hpa]; norm_num
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_three).1
          ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h5))
        omega
      · have h3 : 3 ∣ 5 ^ a := by rw [hpa]; norm_num
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (by norm_num)).1
          ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3))
        omega

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem member_facts {H T M V I P Z : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I)
    (hZ : Z = V ⊓ conjSubgroup V g) :
    Z ≤ P ∧ P ≤ pCoreOf 2 I ∧ I ≤ Subgroup.normalizer (P : Set Γ) ∧
      I ≤ Subgroup.normalizer (Z : Set Γ) ∧ (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧
      (∀ x ∈ P, x ^ 2 ∈ Z) := by
  have hp := E214E.pair_of_isInIHTV h hI hg hgen
  have econj := E214E.conjSubgroup_eq_conjSub_inv V g
  have hPeq : P = (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) := by
    rw [hP, hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm, econj]
  rw [econj] at hZ
  subst hPeq hZ
  exact ⟨hp.inf_conj_le_P, hp.P_le_pCoreOf, hp.le_normalizer_P, hp.le_normalizer_Z,
    fun x hx y hy => (hp.commutator_sq_mem_Z hx hy).1, fun x hx => (hp.commutator_sq_mem_Z hx hx).2⟩

theorem numerics
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hc : CharTwo H)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g) :
    (V ⊓ conjSubgroup V g).relIndex (conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) =
        2 ^ (2 * rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I))) ∧
      (V ⊓ conjSubgroup V g).relIndex V =
        (V ⊓ pCoreOf 2 I).relIndex V * 2 ^ rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have econj := E214E.conjSubgroup_eq_conjSub_inv V g
  have hp := E214E.pair_of_isInIHTV h hI hg hgen
  obtain ⟨⟨hAeq, -, -, hCA, -⟩, -⟩ := e213_member H T M V h hc I g hI hg hgen _ rfl
  have hcard := E213.card_autI_eq_relIndex h hp rfl (by rw [hAeq]; exact inf_le_right) hCA
  obtain ⟨b, hb⟩ := E213M.exists_relIndex_eq_two_pow
    ((B6.isPGroup_of_isElemAbelian h.elem).to_le inf_le_right) (V ⊓ B6.conjSub g⁻¹ V)
  have hrk : rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = b := by
    unfold rk
    rw [hcard, hb, padicValNat.prime_pow]
  have hPeq : conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I =
      (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) := by
    rw [hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm, econj]
  rw [hrk, hPeq, econj, Ch3E213M.relIndex_P_eq hp, hb, ← pow_mul, mul_comm b 2]
  refine ⟨rfl, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex (V ⊓ B6.conjSub g⁻¹ V) (V ⊓ pCoreOf 2 I) V
    (le_inf inf_le_left hp.inf_conj_le_pCoreOf) inf_le_left, ← hp.kerIn_inf_eq, hb, mul_comm]

theorem relIndex_V_of_psl_or_sz
    {H T M V I : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hTI : IsTISetIn V M)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hIV : I = V ⊔ conjSubgroup V g)
    (hZ : V ⊓ conjSubgroup V g ≠ ⊥) {k : ℕ} (hk : 2 ≤ k)
    (hY : IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) :
    (V ⊓ pCoreOf 2 I).relIndex V = 2 ^ k := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have h1 := E214.inf_eq_inf_normalizer h hTI hI hg hIV hZ
  have e : conjSubgroup V g = B6.conjSub g⁻¹ V := SimsE210.conjSubgroup_eq_conjSub V g
  have hgen : I = V ⊔ B6.conjSub g⁻¹ V := e ▸ hIV
  have hg' : g⁻¹ ∈ I := I.inv_mem hg
  obtain ⟨hp, hVZ, -, -, -, -⟩ := RonanE211.e2_11C_all E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds h (E213M.noRoot_of_isInIHTV hI) hg' hgen
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set Γ) := h1.le.trans inf_le_right
  have hBorel := E214.isBorelIn_of_psl_or_sz hI hk hY
  obtain ⟨-, hVeq⟩ := E2.star_eq_center_of_psl_or_sz E2.kgSz8CoverInvolutions_holds
    E2.kgI22One_holds hp hsyl hTMI hg' hgen hVZ hMN hBorel hk hY
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  obtain ⟨hcZ, -⟩ := E2.exists_conj_of_mem_center hk hY hS
  rw [← hp.kerIn_inf_eq, ← E2.card_star_of_le hp.V_le, hVeq]
  exact hcZ

theorem exists_comm_not_mem {H T M V I P Z : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) (hZ : Z = V ⊓ conjSubgroup V g)
    (hne : Z ≠ P) : ∃ i ∈ I, ∃ y ∈ P, i * y * i⁻¹ * y⁻¹ ∉ Z := by
  by_contra hall
  push Not at hall
  obtain ⟨hZP, -, -, hIZ, -, -⟩ := member_facts h hI hg hgen hP hZ
  exact hne (e214_eq_of_forall_commutator_mem H T M V h I g hI hg hgen _ _ P Z rfl rfl hP hZ Z
    le_rfl hZP hIZ hall)

theorem qOf_le_one_of_trans {H T M V I P Z : Subgroup Γ} {g : Γ}
    (h : E2.Hyp28 H T M V) (hc : CharTwo H) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) (hZ : Z = V ⊓ conjSubgroup V g)
    (htr : ∀ x ∈ P, x ∉ Z → ∀ b ∈ P, b ∉ Z → ∃ i ∈ I, (i * b * i⁻¹)⁻¹ * x ∈ Z) :
    qOf (autI h.elem I) ≤ ((1 : ℚ) : WithTop ℚ) := by
  have hp := E214E.pair_of_isInIHTV h hI hg hgen
  have econj := E214E.conjSubgroup_eq_conjSub_inv V g
  have hgen' : I = V ⊔ B6.conjSub g⁻¹ V := by rw [← econj]; exact hgen
  have hcharI : CharTwo I := by
    have := E2.charTwo_of_charTwo h (hI.1 (I.inv_mem hg)) hc
    rwa [← hgen'] at this
  have hPeq : P = (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V) := by
    rw [hP, hp.conjSub_kerIn_inf_eq, hp.kerIn_inf_eq, sup_comm, econj]
  rw [econj] at hZ
  subst hPeq hZ
  have hsq := E214N.sq_eq_one_of_conj hp htr
  have hab : ∀ x ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V),
      ∀ y ∈ (kerIn (M ⊓ I) I ⊓ V) ⊔ B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V), x * y = y * x := by
    intro x hx y hy
    have e1 : x * y * (x * y) = 1 := by
      rw [← pow_two]
      exact hsq _ (Subgroup.mul_mem _ hx hy)
    have e2 : x * x = 1 := by
      rw [← pow_two]
      exact hsq x hx
    have e3 : y * y = 1 := by
      rw [← pow_two]
      exact hsq y hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right e1).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right e2, inv_eq_of_mul_eq_one_right e3]
  exact E214N.qOf_le_one_of_comm h hI hp hcharI fun b hb a ha =>
    hab b (le_sup_left (a := kerIn (M ⊓ I) I ⊓ V) hb) a
      (le_sup_right (b := B6.conjSub g⁻¹ (kerIn (M ⊓ I) I ⊓ V)) ha)

theorem sec_of_chief
    {H T M V I P Z : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hc : CharTwo H)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) (hZ : Z = V ⊓ conjSubgroup V g)
    (hne : Z ≠ P) {m : ℕ}
    (hchief : ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P →
      I ≤ Subgroup.normalizer (Y₁ : Set Γ) → I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
      (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
        Y = Y₂ ∨ Y = Y₁) → m ≤ E3.mQuot Y₁ Y₂)
    (hcard : Z.relIndex P < 2 ^ (2 * m)) : Sec I P Z (kerIn (M ⊓ I) I) := by
  obtain ⟨hZP, hPO, hIP, hIZ, hcomm, hsq⟩ := member_facts h hI hg hgen hP hZ
  obtain ⟨-, -, hP7⟩ := e213_member H T M V h hc I g hI hg hgen _ rfl
  have hJ : pCoreOf 2 I = kerIn (M ⊓ I) I := (hP7 _ rfl).2
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le hPO
  refine ⟨hZP, hPO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I), hIP, hIZ,
    kerIn_le.trans inf_le_right, le_normalizer_kerIn (M ⊓ I) I,
    hJ ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I, hcomm, hsq,
    fun Y hZY hYP hIY => eq_or_eq_of_chief hP2 hchief hIZ hIP hcard hZY hYP hIY, hne⟩

theorem l2_case
    {H T M V I P Z : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hc : CharTwo H)
    (hTI : IsTISetIn V M) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g) (hZ1 : V ⊓ conjSubgroup V g ≠ ⊥)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) (hZ : Z = V ⊓ conjSubgroup V g)
    {k : ℕ} (hk : E1.nParam (⊤ : Subgroup (E2.StarQuot (M ⊓ I) I)) = (k : ℕ∞))
    (hSL : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (E2.StarQuot (M ⊓ I) I ≃* ↥(CFSG.Open.StatedSL 2 F)))
    (hq : ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (E2.StarQuot (M ⊓ I) I ≃* ↥(CFSG.Open.StatedSL 2 F)) ∧
      ∃ r : ℕ, 2 ≤ r ∧ rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = k * r ∧
        IsSumOfNaturalSections r I P Z (kerIn (M ⊓ I) I) (CFSG.Open.StatedSL 2 F) := by
  obtain ⟨F₀, _, _, hF₀, ⟨e₀⟩⟩ := hSL
  obtain ⟨F, _, _, hF, r, hsum⟩ := e214_three H T M V h hc hTI I g hI hg hgen hZ1 _ _ _ _ _ _ _
    k rfl rfl rfl rfl rfl rfl rfl hk ⟨F₀, inferInstance, inferInstance, hF₀, ⟨e₀⟩⟩
  obtain ⟨e₁⟩ := nonempty_statedSL_mulEquiv (hF₀.trans hF.symm)
  refine ⟨F, inferInstance, inferInstance, hF, ⟨e₀.trans e₁⟩, r, ?_⟩
  obtain ⟨hPZ, -⟩ := numerics h hc hI hg hgen
  rw [← hP, ← hZ] at hPZ
  rw [← hP, ← hZ] at hsum
  obtain ⟨hZP, hPO, -, -, -, -⟩ := member_facts h hI hg hgen hP hZ
  obtain ⟨W, hW, hWP, hind⟩ := hsum
  have hc4 : ∀ i, Z.relIndex (W i) = (2 ^ k) ^ 2 := fun i => by
    rw [relIndex_of_isNaturalSection (hW i).2.2.2, Nat.card_fun, hF, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rcases Nat.lt_or_ge r 2 with hr | hr
  · exfalso
    interval_cases r
    ·
      have hP0 : P = ⊥ := by rw [← hWP]; exact iSup_of_empty _
      apply hZ1
      rw [← hZ]
      exact le_bot_iff.1 (hP0 ▸ hZP)
    ·
      have hP1 : W default = P := (iSup_unique W).symm.trans hWP
      have hnat := (hW default).2.2.2
      rw [hP1, hP, hZ] at hnat
      have h5 := (e214_five H T M V h hc hTI I g hI hg hgen hZ1 _ _ _ _ _ _ _ k rfl rfl rfl rfl rfl
        rfl rfl hk ⟨F, inferInstance, inferInstance, hF, Or.inl hnat⟩).2
      exact absurd h5 (not_le.mpr hq)
  · refine ⟨hr, ?_, ⟨W, hW, hWP, hind⟩⟩
    have hPr := relIndex_iSup_eq_pow (by omega) W (fun i => (hW i).1)
      (fun i => (hW i).2.1.trans (hPO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)))
      (fun i => (hW i).2.2.1) hc4 hind
    rw [hWP, hPZ, ← pow_mul, ← pow_mul] at hPr
    have h2 := Nat.pow_right_injective le_rfl hPr
    have h3 : 2 * rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = 2 * (k * r) := by
      rw [h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

theorem sz_case
    {H T M V I P Z : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hc : CharTwo H)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) (hZ : Z = V ⊓ conjSubgroup V g)
    {k : ℕ} (hSz : IsSz k (E2.StarQuot (M ⊓ I) I))
    (hrk : rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) ≤ 2 * k)
    (h4 : ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P →
      I ≤ Subgroup.normalizer (Y₁ : Set Γ) → I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
      (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
        Y = Y₂ ∨ Y = Y₁) → 4 * k ≤ E3.mQuot Y₁ Y₂) :
    rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = 2 * k ∧
      ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ a ∧ k = 2 * a + 1 ∧
        Nat.card F = 2 ^ k ∧
          IsNaturalSection I P Z (kerIn (M ⊓ I) I) (CFSG.Blueprint.suzukiGroup a F) := by
  have hrk2 : rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = 2 * k :=
    le_antisymm hrk ((e213_four_nondih H T M V h hc I g hI hg hgen _ rfl).2.1 k hSz)
  refine ⟨hrk2, ?_⟩
  obtain ⟨-, a, ha, K, _, _, hka, hK, ⟨e⟩⟩ := hSz
  obtain ⟨hPZ, -⟩ := numerics h hc hI hg hgen
  rw [← hP, ← hZ, hrk2] at hPZ
  have hk1 : 1 ≤ k := by omega
  have hne : Z ≠ P := by
    intro hZP
    rw [hZP, Subgroup.relIndex_self] at hPZ
    have : 1 < 2 ^ (2 * (2 * k)) := Nat.one_lt_two_pow (by omega)
    omega
  have hcard : Z.relIndex P < 2 ^ (2 * (4 * k)) := by
    rw [hPZ]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hS := sec_of_chief h hc hI hg hgen hP hZ hne h4 hcard
  haveI := hS.normal
  have hnt := exists_comm_not_mem h hI hg hgen hP hZ hne
  refine ⟨a, K, inferInstance, inferInstance, ha, hka, hK, ?_⟩
  rw [hka] at hK hPZ
  exact hS.isNaturalSection_of_sz hK e hnt (by rw [hPZ]; ring_nf)

theorem sp4_false
    {H T M V I P Z : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hc : CharTwo H)
    (hI : IsInIHTV H T M V I) (hg : g ∈ I) (hgen : I = V ⊔ conjSubgroup V g)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) (hZ : Z = V ⊓ conjSubgroup V g)
    {k : ℕ} (hk1 : 1 ≤ k) (hY : IsSp4Full k (E2.StarQuot (M ⊓ I) I))
    (h4 : ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P →
      I ≤ Subgroup.normalizer (Y₁ : Set Γ) → I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
      (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
        Y = Y₂ ∨ Y = Y₁) → 4 * k ≤ E3.mQuot Y₁ Y₂)
    (hne : Z ≠ P) (hcard : Z.relIndex P < 2 ^ (8 * k))
    (hq : ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I)) : False := by
  have hcard' : Z.relIndex P < 2 ^ (2 * (4 * k)) := by
    rw [show 2 * (4 * k) = 8 * k by ring]
    exact hcard
  have hS := sec_of_chief h hc hI hg hgen hP hZ hne h4 hcard'
  haveI := hS.normal
  have hnt := exists_comm_not_mem h hI hg hgen hP hZ hne
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ k ∧ Nonempty (E2.StarQuot (M ⊓ I) I ≃*
        CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp F) := by
    rcases hY with hY | ⟨rfl, ⟨e6⟩⟩
    · obtain ⟨-, F, hF1, hF2, hF3, hF, he⟩ :=
        CFSG.Quasithin.H13.F431.exists_equiv_antiSp (Or.inl ⟨by decide, hY⟩)
      exact ⟨F, hF1, hF2, hF3, hF, he⟩
    · exact ⟨ZMod 2, inferInstance, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
        ⟨e6.trans ((B5FinSp.theta (RingEquiv.refl (ZMod 2))).trans
          (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSpEquiv (ZMod 2)).symm)⟩⟩
  have htr : ∀ x ∈ P, x ∉ Z → ∀ b ∈ P, b ∉ Z → ∃ i ∈ I, (i * b * i⁻¹)⁻¹ * x ∈ Z :=
    fun x hx hxZ b hb hbZ => hS.exists_conj_of_antiSp hF hk1 e hnt hcard hx hxZ hb hbZ
  exact absurd (qOf_le_one_of_trans h hc hI hg hgen hP hZ htr) (not_le.mpr hq)

theorem dih5_case
    {H T M V I P Z : Subgroup Γ} {g : Γ} (h : E2.Hyp28 H T M V) (hc : CharTwo H)
    (hTI : IsTISetIn V M) (hI : IsInIHTV H T M V I) (hg : g ∈ I)
    (hgen : I = V ⊔ conjSubgroup V g) (hZ1 : V ⊓ conjSubgroup V g ≠ ⊥)
    (hP : P = conjSubgroup V g ⊓ pCoreOf 2 I ⊔ V ⊓ pCoreOf 2 I) (hZ : Z = V ⊓ conjSubgroup V g)
    (e : E2.StarQuot (M ⊓ I) I ≃* DihedralGroup 5)
    (hrk : rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) ≤ 2) :
    rk ↥(autI h.elem (conjSubgroup V g ⊓ pCoreOf 2 I)) = 2 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F)
        (S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)),
        Nat.card F = 4 ∧ S ≤ CFSG.Open.StatedSL 2 F ∧ Nonempty (↥S ≃* DihedralGroup 5) ∧
          IsNaturalSection I P Z (kerIn (M ⊓ I) I) S := by
  have hd := dihFour_holds Γ H T M V h hc I g hI hg hgen _ rfl 5 1 Nat.prime_five (by norm_num)
    le_rfl ⟨by rw [pow_one]; exact e⟩
  rw [pow_one, dParamPrime_five] at hd
  have hrk2 := le_antisymm hrk hd
  refine ⟨hrk2, ?_⟩
  obtain ⟨hPZ, -⟩ := numerics h hc hI hg hgen
  rw [← hP, ← hZ, hrk2] at hPZ
  norm_num at hPZ
  obtain ⟨r, W, hW, hWP, -⟩ := e214_ten H T M V h hc hTI I g hI hg hgen hZ1 _ _ _ _ _ _ _ 1
    rfl rfl rfl rfl rfl rfl rfl (by rw [nParam_eq_of_dihedral e]; rfl) 5 Nat.prime_five
    (by norm_num) ⟨e⟩
  rw [← hP] at hWP
  rw [← hP, ← hZ, dParamPrime_five] at hW
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exfalso
    obtain ⟨hZP, -⟩ := member_facts h hI hg hgen hP hZ
    have hP0 : P = ⊥ := by rw [← hWP]; exact iSup_of_empty _
    apply hZ1
    rw [← hZ]
    exact le_bot_iff.1 (hP0 ▸ hZP)
  ·
    obtain ⟨hZW, hWP0, hfi, hm4⟩ := hW ⟨0, hr⟩
    obtain ⟨hZP, hPO, -, -, hcomm, hsq⟩ := member_facts h hI hg hgen hP hZ
    have hW2 : IsPGroup 2 (W ⟨0, hr⟩) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le (hWP0.trans hPO)
    have hWZ : Z.relIndex (W ⟨0, hr⟩) = 16 := by
      rw [relIndex_eq_two_pow_mQuot hW2, hm4]
      norm_num
    have hWeq : W ⟨0, hr⟩ = P := by
      refine le_antisymm hWP0 ?_
      have h1 := Subgroup.relIndex_mul_relIndex Z (W ⟨0, hr⟩) P hZW hWP0
      rw [hWZ, hPZ] at h1
      have h2 : (W ⟨0, hr⟩).relIndex P = 1 := by omega
      exact Subgroup.relIndex_eq_one.1 h2
    rw [hWeq] at hfi
    obtain ⟨hZP', hIP, hIZ, -, -, hirr, hJ⟩ := hfi
    have hS : Sec I P Z (kerIn (M ⊓ I) I) :=
      ⟨hZP, hPO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I), hIP, hIZ,
        kerIn_le.trans inf_le_right, le_normalizer_kerIn (M ⊓ I) I,
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le
          (fun x hx => (e213_member H T M V h hc I g hI hg hgen _ rfl).2.2 _ rfl |>.2 ▸ hx)),
        hcomm, hsq, hirr, hZP'.ne⟩
    haveI := hS.normal
    exact hS.isNaturalSection_of_dih5 e (fun x hx hxP => (hJ x).2 ⟨hx, hxP⟩) hPZ

end E214S

end CFSG.Quasithin.SimsE2
