module

public import CFSG.Quasithin.Vol2.Ch10SecASL2OverAux
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

variable {K : Type} [Field K] [Finite K]

theorem odd_four_pow_sub_one {m : ℕ} (hm : m ≠ 0) : Odd (4 ^ m - 1) := by
  simpa [pow_mul] using odd_two_pow_sub_one (k := 2 * m) (by omega)

theorem le_two_of_dvd_60 {n N : ℕ} (h : 2 ^ n ∣ N) (hN : N ∣ 60) : n ≤ 2 :=
  le_of_two_pow_dvd (b := 2) (c := 15) (by decide) (h.trans (by simpa using hN))

theorem le_normalizer_or_eq_top_SL_two
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {S X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hS2 : IsPGroup 2 S)
    (hSc : Nat.card S = 2 ^ n) (hSX : S ≤ X) :
    X ≤ Subgroup.normalizer (S : Set (Matrix.SpecialLinearGroup (Fin 2) K)) ∨ X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hK'
  have hG := card_SL_two_pow hK
  have hodd4 : Odd (4 ^ n - 1) := odd_four_pow_sub_one (by omega)
  have hoddm : Odd (2 ^ n - 1) := odd_two_pow_sub_one (by omega)
  have hoddp : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hgcd : Nat.gcd (2 ^ n - 1) 2 = 1 := Nat.coprime_two_right.mpr hoddm
  have hSX' : 2 ^ n ∣ Nat.card X := hSc ▸ Subgroup.card_dvd_of_le hSX
  have hXG : Nat.card X ∣ 2 ^ n * (4 ^ n - 1) := hG ▸ Subgroup.card_subgroup_dvd_card X
  have h4n : 4 ∣ 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨2 ^ k, by ring⟩
  have htop : Nat.card X = 2 ^ n * (4 ^ n - 1) → X = ⊤ := fun h =>
    (Subgroup.card_eq_iff_eq_top X).mp (h.trans hG.symm)
  set e := slTwoEquivPSL K
  set X' := X.map e.toMonoidHom with hX'def
  have eX : ↥X ≃* ↥X' := X.equivMapOfInjective e.toMonoidHom e.injective
  have hX' : Nat.card X' = Nat.card X := (Nat.card_congr eX.toEquiv).symm
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK X' with
    hab | ⟨z, hz, hzc, -⟩ | ⟨z, hz, hzc, -⟩ | ⟨-, ⟨eA⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨eA⟩⟩ |
    ⟨m, t, -, htq, N, C, hNn, hNab, -, -, hCc, -, hsup⟩ | ⟨m, hm0, hmn, ⟨eP⟩⟩ |
    ⟨m, hm0, hmn, ⟨eP⟩⟩
  ·
    left
    have hPX : IsPGroup 2 ↥X := (@IsElementaryAbelian.isPGroup 2 _ _ hab).of_equiv eX.symm
    have hle : Nat.card X ≤ Nat.card S := by
      rw [hSc]
      exact Nat.le_of_dvd (by positivity)
        (dvd_two_pow_of_isPGroup hPX hodd4 hXG)
    rw [← Subgroup.eq_of_le_of_card_ge hSX hle]
    exact Subgroup.le_normalizer
  ·
    exfalso
    rw [hK, hgcd, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z :=
      hz.elim (fun h => Odd.of_dvd_nat hoddm h) (fun h => Odd.of_dvd_nat hoddp h)
    have h2 : 2 ∣ z := by
      rw [← hzc, hX']
      exact ((by norm_num : 2 ∣ 4).trans h4n).trans hSX'
    exact (Nat.not_even_iff_odd.mpr hzodd) (even_iff_two_dvd.mpr h2)
  ·
    exfalso
    rw [hK, hgcd, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z :=
      hz.elim (fun h => Odd.of_dvd_nat hoddm h) (fun h => Odd.of_dvd_nat hoddp h)
    have h4 : 4 ∣ 2 * z := by
      rw [← hzc, hX']
      exact h4n.trans hSX'
    obtain ⟨k, hk⟩ := hzodd
    omega
  ·
    left
    have h12 : Nat.card X = 12 := by
      rw [← hX', Nat.card_congr eA.toEquiv, card_alt 4 (by norm_num)]
      decide
    have hn2 : n = 2 := le_antisymm (le_two_of_dvd_60 hSX' (h12 ▸ by norm_num)) hn
    subst hn2
    have hS' : Nat.card (S.subgroupOf X) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hSc]
      norm_num
    exact le_normalizer_of_normal_subgroupOf hSX (normal_of_mulEquiv_alt4 (eX.trans eA) hS')
  ·
    exfalso
    obtain ⟨k, hk⟩ := odd_two_pow_sub_one (k := 2 * n) (by omega)
    rw [hk] at h16
    omega
  ·
    right
    have h60 : Nat.card X = 60 := by
      rw [← hX', Nat.card_congr eA.toEquiv, card_alt 5 (by norm_num)]
      decide
    have hn2 : n = 2 := le_antisymm (le_two_of_dvd_60 hSX' (h60 ▸ dvd_rfl)) hn
    subst hn2
    exact htop (by rw [h60]; norm_num)
  ·
    left
    rw [hgcd, Nat.div_one] at htq
    have htodd : Odd t := Odd.of_dvd_nat hoddm htq
    set S'' : Subgroup ↥X' := (S.subgroupOf X).map eX.toMonoidHom with hS''def
    have hS''c : Nat.card S'' = 2 ^ n := by
      rw [hS''def, Subgroup.card_map_of_injective eX.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hSc]
    have hS''2 : IsPGroup 2 S'' :=
      (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm).map eX.toMonoidHom
    have hN2 : IsPGroup 2 ↥N := @IsElementaryAbelian.isPGroup 2 _ _ hNab
    have hmax : ∀ P : Subgroup ↥X', IsPGroup 2 P → Nat.card P ≤ Nat.card S'' := by
      intro P hP
      rw [hS''c]
      exact Nat.le_of_dvd (by positivity) (dvd_two_pow_of_isPGroup hP hodd4
        ((Subgroup.card_subgroup_dvd_card P).trans (hX' ▸ hXG)))
    have := hNn
    have heq := eq_of_normal_complement hS''2 hN2 (hCc ▸ htodd) hsup hmax
    have hN' : (S.subgroupOf X).Normal := by
      have h1 : S''.Normal := heq ▸ hNn
      have h2 := h1.comap eX.toMonoidHom
      rwa [hS''def, Subgroup.comap_map_eq_self_of_injective eX.injective] at h2
    exact le_normalizer_of_normal_subgroupOf hSX hN'
  ·
    right
    have hc : Nat.card X = 2 ^ m * (4 ^ m - 1) := by
      rw [← hX', Nat.card_congr eP.toEquiv]
      exact card_psl_galois hm0
    have hle : n ≤ m := le_of_two_pow_dvd (odd_four_pow_sub_one hm0) (hc ▸ hSX')
    have hmn' : m = n := le_antisymm (Nat.le_of_dvd (by omega) hmn) hle
    subst hmn'
    exact htop hc
  ·
    exfalso
    have hd : Nat.card X ∣ 2 ^ m * ((2 ^ m - 1) * (4 ^ m - 1)) := by
      rw [← hX', Nat.card_congr eP.toEquiv]
      exact card_pgl_galois_dvd hm0
    have hle : n ≤ m := le_of_two_pow_dvd
      ((odd_two_pow_sub_one (by omega)).mul (odd_four_pow_sub_one hm0)) (hSX'.trans hd)
    have h2m : 2 * m ≤ n := Nat.le_of_dvd (by omega) hmn
    omega

end CFSG.Quasithin.Vol2.Ch10.SecA
