module

public import CFSG.Quasithin.H13.A6S13821zz5
public import CFSG.Quasithin.Background.F918C2
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem false_of_sl2_sl3_eq {q z : ℕ} (hq : 4 ≤ q)
    (h : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 3 - 1) * z) : False := by
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hq4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
  have hZ : ((q : ℤ) ^ 6 - 1) = ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 - 1) * z := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hq3, Nat.cast_sub hq6] at this
    linear_combination this
  have hne : ((q : ℤ) ^ 3 - 1) * ((q : ℤ) + 1) ≠ 0 := by
    have h1 : (0 : ℤ) < (q : ℤ) ^ 3 - 1 := by nlinarith
    have h2 : (0 : ℤ) < (q : ℤ) + 1 := by linarith
    exact mul_ne_zero h1.ne' h2.ne'
  have h1 : (q : ℤ) ^ 2 - q + 1 = ((q : ℤ) - 1) * z := by
    have h2 : ((q : ℤ) ^ 3 - 1) * ((q : ℤ) + 1) *
        (((q : ℤ) ^ 2 - q + 1) - ((q : ℤ) - 1) * z) = 0 := by
      linear_combination hZ
    have h3 := (mul_eq_zero.mp h2).resolve_left hne
    linear_combination h3
  have h4 : ((q : ℤ) - 1) ∣ 1 := ⟨z - q, by linear_combination h1⟩
  have h5 := Int.le_of_dvd one_pos h4
  linarith

theorem false_of_sp4_sl3_eq {q s z : ℕ} (hq : 4 ≤ q) (hz : 1 ≤ z) (hs : s ^ 4 = q ^ 3)
    (h : (s ^ 2 - 1) * (s ^ 4 - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) * z) : False := by
  have hq3 : 0 < q ^ 3 - 1 := by
    have : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  rw [hs] at h
  have h1 : s ^ 2 - 1 = (q ^ 2 - 1) * z := by
    apply Nat.eq_of_mul_eq_mul_right hq3
    calc (s ^ 2 - 1) * (q ^ 3 - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) * z := h
      _ = (q ^ 2 - 1) * z * (q ^ 3 - 1) := by ring
  have h2 : q ^ 2 - 1 ≤ s ^ 2 - 1 := by
    rw [h1]
    exact Nat.le_mul_of_pos_right _ hz
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have h3 : q ^ 2 ≤ s ^ 2 := by omega
  have h4 : q ^ 4 ≤ s ^ 4 := by
    have := Nat.mul_le_mul h3 h3
    calc q ^ 4 = q ^ 2 * q ^ 2 := by ring
      _ ≤ s ^ 2 * s ^ 2 := this
      _ = s ^ 4 := by ring
  have h5 : q ^ 3 < q ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem false_of_g2_sl3_eq {q s z : ℕ} (hq : 4 ≤ q) (hz : 1 ≤ z) (hs : s ^ 6 = q ^ 3)
    (h : (s ^ 6 - 1) * (s ^ 2 - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) * z) : False := by
  have hq3 : 0 < q ^ 3 - 1 := by
    have : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have hs2 : s ^ 2 = q := by
    have : (s ^ 2) ^ 3 = q ^ 3 := by rw [← pow_mul]; exact hs
    exact Nat.pow_left_injective (by norm_num) this
  rw [hs, hs2] at h
  have h1 : q - 1 = (q ^ 2 - 1) * z := by
    apply Nat.eq_of_mul_eq_mul_left hq3
    calc (q ^ 3 - 1) * (q - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) * z := h
      _ = (q ^ 3 - 1) * ((q ^ 2 - 1) * z) := by ring
  have h2 : q ^ 2 - 1 ≤ q - 1 := by
    rw [h1]
    exact Nat.le_mul_of_pos_right _ hz
  have h3 : q < q ^ 2 := by nlinarith
  omega

theorem le_card_sl3_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    16482816 ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have hq : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  generalize 2 ^ n = q at hq
  have h3 : 512 ≤ q ^ 3 := by
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 64 ≤ q ^ 2 := by
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  calc 16482816 = 512 * (63 * 511) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))


theorem natural_sl3_of_b42 {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (hB : B4Hyp G L) (hA : IsFFStarOffender G A)
    (hc : B42Conclusion G L A) {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) :
    ∃ m, 2 ≤ m ∧ BinaryNaturalSL L ⊤ ⊥ 3 m ∧ qOf G = ((1 / 2 : ℚ) : WithTop ℚ) := by
  classical
  set q := 2 ^ n with hqdef
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  set z := Nat.card (Subgroup.center ↥L) with hz
  set r := (q ^ 2 - 1) * (q ^ 3 - 1) with hr
  have hz1 : 1 ≤ z := hodd.pos
  have hrodd : Odd r := by
    have e2 : q ^ 2 = 2 ^ (2 * n) := by rw [hqdef, ← pow_mul, mul_comm]
    have e3 : q ^ 3 = 2 ^ (3 * n) := by rw [hqdef, ← pow_mul, mul_comm]
    rw [hr, e2, e3]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  have hLc : Nat.card ↥L = q ^ 3 * r * z := by
    rw [← hcard, hz]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hq3 : q ^ 3 = 2 ^ (n * 3) := by rw [hqdef, ← pow_mul]
  have hL2 : Nat.card ↥L = 2 ^ (n * 3) * (r * z) := by rw [hLc, hq3, mul_assoc]
  have hrz : Odd (r * z) := hrodd.mul hodd
  have hlow : 16482816 ≤ Nat.card ↥L := by
    have h1 := le_card_sl3_of_three_le hn
    rw [hLc]
    calc 16482816 ≤ q ^ 3 * r := by rw [hr, mul_assoc] at *; exact h1
      _ ≤ q ^ 3 * r * z := Nat.le_mul_of_pos_right _ hz1
  have small : ∀ {M : ℕ}, Nat.card ↥L ≤ M → M < 16482816 → False := fun h1 h2 => by omega
  have one_le : ∀ {K : Type} [Field K] [Finite K] {m : ℕ}, Nat.card K = 2 ^ m → 1 ≤ m := by
    intro K _ _ m hK
    by_contra h
    have h0 : m = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  have hLG : L ≤ G := hB.2.1 ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  rcases hc with ⟨-, ⟨m, hnat⟩, -, -⟩ | ⟨-, ⟨m, hnat⟩, hq⟩ | ⟨⟨m, hsp, hJ⟩, -⟩ |
      ⟨⟨m, hg2, -, hJ⟩, -⟩ | h5 | ⟨-, ⟨π, hR⟩, -⟩ | ⟨-, -, ⟨α, π, hR⟩, -⟩ |
      ⟨-, -, -, K, _, _, Γ₀, hK4, -, -, -, π, hR, -⟩ | ⟨-, m, hm, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩ |
      ⟨-, -, -, -, π, hR, -⟩
  ·
    exfalso
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1m := one_le hFc
    have h1 : Nat.card ↥L = 2 ^ m * (4 ^ m - 1) := by
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_two_pow hFc]
    have hodd' : Odd (4 ^ m - 1) := by
      rw [show (4 : ℕ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hL2)
    have h4 : q ^ 6 = 4 ^ m := by
      rw [hm3, hqdef, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    refine false_of_sl2_sl3_eq hq4 (z := z) ?_
    rw [h4, hodd2, hr]
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1m := one_le hFc
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · exfalso
      have hm1 : m = 1 := by omega
      subst hm1
      refine small (M := 168) (le_of_eq ?_) (by norm_num)
      rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL,
        Vol2.Ch10.SecA.card_SL_three_pow hFc]
      norm_num
    · exact ⟨m, h2, hnat, hq⟩
  ·
    exfalso
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hsp.exists_equiv
    have h1m := one_le hFc
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      have hLJ := Vol2.Ch10.SecA.le_ffJ_of_two_dvd hV hB (Vol2.Ch10.SecA.two_dvd_card_ffJ hA)
      refine small (M := 720) ?_ (by norm_num)
      calc Nat.card ↥L ≤ Nat.card ↥(ffJ G) := Subgroup.card_le_of_le hLJ
        _ = 720 := by
          rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_Sp4_pow hFc]
          norm_num
    · have hJL := hJ (by omega)
      rw [hJL] at e
      have h1 : Nat.card ↥L = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
        rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_Sp4_pow hFc]
      have hodd' : Odd ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) :=
        (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
      obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hL2)
      set s := 2 ^ m with hs
      have e2 : (2 : ℕ) ^ (2 * m) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
      have e4 : (2 : ℕ) ^ (4 * m) = s ^ 4 := by rw [hs, ← pow_mul, mul_comm]
      have hqs : s ^ 4 = q ^ 3 := by rw [hq3, ← e4, hm3]
      rw [e2, e4] at hodd2
      exact false_of_sp4_sl3_eq hq4 hz1 hqs hodd2
  ·
    exfalso
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := Bridge.TypeList.exists_equiv_of_g2Natural hg2
    have h1m := one_le hFc
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      have hLJ := Vol2.Ch10.SecA.le_ffJ_of_two_dvd hV hB (Vol2.Ch10.SecA.two_dvd_card_ffJ hA)
      refine small (M := 12096) ?_ (by norm_num)
      calc Nat.card ↥L ≤ Nat.card ↥(ffJ G) := Subgroup.card_le_of_le hLJ
        _ = 12096 := by
          rw [← Nat.card_congr e.toEquiv, U3.card_quasithinG2_two (by rw [hFc]; norm_num)]
    · have hJL := hJ (by omega)
      rw [hJL] at e
      set s := 2 ^ m with hs
      have h1 : Nat.card ↥L = 2 ^ (6 * m) * ((s ^ 6 - 1) * (s ^ 2 - 1)) := by
        rw [← Nat.card_congr e.toEquiv, card_quasithinG2_1527d hFc, hFc, hs, ← pow_mul,
          mul_comm m 6]
      have e6 : (2 : ℕ) ^ (6 * m) = s ^ 6 := by rw [hs, ← pow_mul, mul_comm]
      have e2 : (2 : ℕ) ^ (2 * m) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
      have hodd' : Odd ((s ^ 6 - 1) * (s ^ 2 - 1)) := by
        rw [← e6, ← e2]
        exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
      obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hL2)
      have hqs : s ^ 6 = q ^ 3 := by rw [hq3, ← e6, hm3]
      exact false_of_g2_sl3_eq hq4 hz1 hqs hodd2
  ·
    exfalso
    obtain ⟨k, hk, -, ⟨e⟩⟩ := InternalSec.alternatingNatural_of_b42Case5 hV hB h5
    refine small (M := 2520) ?_ (by norm_num)
    rw [Nat.card_congr e.toEquiv]
    rcases hk with rfl | rfl <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide
  ·
    exfalso
    refine small (M := 360) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 6)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 360 := by rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  ·
    exfalso
    refine small (M := 2520) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 7)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 2520 := by rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  ·
    exfalso
    refine small (M := 262144) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective _ hR.1
      _ ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 3) K) := Subgroup.card_le_card_group _
      _ ≤ Nat.card (Matrix (Fin 3) (Fin 3) K) :=
          Nat.card_le_card_of_injective (fun g => (g : Matrix (Fin 3) (Fin 3) K))
            (fun a b h => Units.ext h)
      _ = 262144 := by
          show Nat.card (Fin 3 → Fin 3 → K) = 262144
          rw [Nat.card_fun, Nat.card_fun, hK4, Nat.card_fin]
          norm_num
  ·
    exfalso
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    refine small (M := 9999360) ?_ (by norm_num)
    rw [← Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_statedSL]
    rcases hm with rfl | rfl
    · rw [Vol2.Ch10.SecA.card_SL_four_of_two hF2]; norm_num
    · rw [Vol2.Ch10.SecA.card_SL_five_of_two hF2]
  ·
    exfalso
    refine small (M := 20160) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 20160 := by
        rw [Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_four_of_two (by simp)]
  ·
    exfalso
    refine small (M := 9999360) ?_ (by norm_num)
    calc Nat.card ↥L ≤ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) :=
          Nat.card_le_card_of_surjective _ hR.1
      _ = 9999360 := by
        rw [Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_five_of_two (by simp)]

theorem exists_mem_normalizer_fpf_sl3 {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (P : Sylow 2 (SpecialLinearGroup (Fin 3) F)) :
    ∃ d : SpecialLinearGroup (Fin 3) F, d ∈ Subgroup.normalizer
      ((P : Subgroup (SpecialLinearGroup (Fin 3) F)) : Set (SpecialLinearGroup (Fin 3) F)) ∧
      ∀ v : Fin 3 → F, (d : Matrix (Fin 3) (Fin 3) F).mulVec v = v → v = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, Set.ncard_pair (zero_ne_one)] at h1
    omega
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hl2 : l ^ 2 ≠ 1 := by
    intro h
    apply hl1
    have h3 : (l + 1) * (l + 1) = 0 := by linear_combination h + l * h2 + h2
    have h4 : l + 1 = 0 := mul_self_eq_zero.mp h3
    linear_combination h4 - h2
  have hl2' : (l ^ 2)⁻¹ ≠ 1 := fun h => hl2 (inv_eq_one.mp h)
  set a : Fin 3 → F := ![l, l, (l ^ 2)⁻¹] with ha
  set b : Fin 3 → F := ![l⁻¹, l⁻¹, l ^ 2] with hb
  have hab : ∀ i, a i * b i = 1 := by
    intro i
    fin_cases i <;> simp [ha, hb, hl0]
  have hdet : (diagonal a).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp [ha]
    field_simp
  have hdet' : (diagonal b).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three]
    simp [hb]
    field_simp
  let d₀ : SpecialLinearGroup (Fin 3) F := ⟨diagonal a, hdet⟩
  let e₀ : SpecialLinearGroup (Fin 3) F := ⟨diagonal b, hdet'⟩
  have hde : d₀ * e₀ = 1 := by
    ext i j
    change (diagonal a * diagonal b) i j = (1 : Matrix (Fin 3) (Fin 3) F) i j
    rw [diagonal_mul_diagonal]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, one_apply_eq, hab]
    · rw [diagonal_apply_ne _ hij, one_apply_ne hij]
  have he : d₀⁻¹ = e₀ := (eq_inv_of_mul_eq_one_right hde).symm
  have hconjU : ∀ u ∈ unitriangular 3 F, d₀ * u * d₀⁻¹ ∈ unitriangular 3 F := by
    intro u hu
    obtain ⟨hlow, hdiag⟩ := hu
    have hprod : ((d₀ * u * d₀⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal a * (u : Matrix (Fin 3) (Fin 3) F) * diagonal b := by
      rw [he]
      rfl
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hprod, mul_diagonal, diagonal_mul, hlow i j hij]
      ring
    · rw [hprod, mul_diagonal, diagonal_mul, hdiag i, mul_one, hab]
  have hfix₀ : ∀ v : Fin 3 → F, (d₀ : Matrix (Fin 3) (Fin 3) F).mulVec v = v → v = 0 := by
    intro v hv
    have hv' : ∀ i, a i * v i = v i := by
      intro i
      have := congrFun hv i
      simpa [d₀, mulVec_diagonal] using this
    funext i
    have h1 := hv' i
    have h3 : (a i - 1) * v i = 0 := by linear_combination h1
    have hai : a i - 1 ≠ 0 := by
      fin_cases i
      · simpa [ha, sub_eq_zero] using hl1
      · simpa [ha, sub_eq_zero] using hl1
      · simpa [ha, sub_eq_zero] using hl2'
    simpa using (mul_eq_zero.mp h3).resolve_left hai
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) P₀ P
  have hmem : ∀ x, x ∈ (P : Subgroup (SpecialLinearGroup (Fin 3) F)) ↔
      h⁻¹ * x * h ∈ unitriangular 3 F := by
    intro x
    rw [← hh, Sylow.coe_subgroup_smul, ← hP₀, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e1 : h⁻¹ * ((MulAut.conj h) • y) * h = y := by
        rw [MulAut.smul_def, MulAut.conj_apply]; group
      rw [e1]; exact hy
    · intro hx
      refine ⟨h⁻¹ * x * h, hx, ?_⟩
      rw [MulAut.smul_def, MulAut.conj_apply]; group
  refine ⟨h * d₀ * h⁻¹, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe] at hx ⊢
    rw [hmem] at hx ⊢
    have e : h⁻¹ * (h * d₀ * h⁻¹ * x * (h * d₀ * h⁻¹)⁻¹) * h = d₀ * (h⁻¹ * x * h) * d₀⁻¹ := by
      group
    rw [e]
    exact hconjU _ hx
  · intro v hv
    have h1 : (d₀ : Matrix (Fin 3) (Fin 3) F).mulVec
        (((h⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        ((h⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v := by
      have e : (d₀ : Matrix (Fin 3) (Fin 3) F) *
          ((h⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          ((h⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            ((h * d₀ * h⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        have e' : (h⁻¹ * (h * d₀ * h⁻¹) : SpecialLinearGroup (Fin 3) F) = d₀ * h⁻¹ := by group
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, e']
      rw [mulVec_mulVec, e, ← mulVec_mulVec, hv]
    have h2 := hfix₀ _ h1
    have h3 : v = ((h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (((h⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) := by
      rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, one_mulVec]
    rw [h3, h2, mulVec_zero]

theorem exists_fpf_of_natural_sl3 {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {m : ℕ} (hnat : BinaryNaturalSL L U Z 3 m) (hm : 2 ≤ m) {X : Type} [Group X]
    [Finite X]
    (κ : X →* ↥L) (hκ : Function.Surjective κ) {T₀ : Subgroup X} (hsyl : IsSylowTwoOf T₀ ⊤)
    (hker : ∀ x ∈ κ.ker, x ∈ Subgroup.normalizer (T₀ : Set X)) :
    ∃ k ∈ Subgroup.normalizer (T₀ : Set X), ∀ u ∈ U, ((κ k : ↥L) : MulAut W) u * u⁻¹ ∈ Z →
      u ∈ Z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, hFfin, hFc, hR⟩ := hnat
  obtain ⟨π, hπ⟩ : ∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) →* ↥L,
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).RealizesVia L U Z π := hR
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hFc])
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFc]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨ε, hε⟩ := exists_sec_equiv_nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F) hπ
  have hπinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  set eπ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≃* ↥L :=
    MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩ with heπ
  set eS := specialLinearGroupEquivStatedSL 3 F with heS
  set θ : X →* Matrix.SpecialLinearGroup (Fin 3) F :=
    (eS.symm.toMonoidHom.comp eπ.symm.toMonoidHom).comp κ with hθ
  have hθs : Function.Surjective θ := fun y => by
    obtain ⟨x, hx⟩ := hκ (eπ (eS y))
    exact ⟨x, by simp [hθ, hx]⟩
  have hθker : ∀ x, θ x = 1 → x ∈ κ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have h1 : eS.symm (eπ.symm (κ x)) = 1 := hx
    have h2 : eπ.symm (κ x) = 1 := by
      have := congrArg eS h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have := congrArg eπ h2
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have hP2 : IsPGroup 2 ↥(T₀.map θ) := hsyl.2.1.map θ
  have hPidx : ¬ 2 ∣ (T₀.map θ).index := by
    intro hd
    apply hsyl.2.2
    have h2 : (T₀.subgroupOf ⊤).index = T₀.index := Subgroup.relIndex_top_right _
    rw [h2]
    exact hd.trans (Subgroup.index_map_dvd T₀ hθs)
  obtain ⟨d, hdN, hdfix⟩ := exists_mem_normalizer_fpf_sl3 hF4 (hP2.toSylow hPidx)
  obtain ⟨k, hk⟩ := hθs d
  refine ⟨k, ?_, ?_⟩
  ·
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    rw [SetLike.mem_coe] at ht ⊢
    set x := k * t * k⁻¹ with hx
    have hθx : θ x ∈ T₀.map θ := by
      have h1 : θ x = d * θ t * d⁻¹ := by rw [hx, map_mul, map_mul, map_inv, hk]
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp hdN (θ t)).mp ⟨t, ht, rfl⟩
    obtain ⟨t', ht', htx⟩ := hθx
    have hyk : t'⁻¹ * x ∈ κ.ker := hθker _ (by rw [map_mul, map_inv, htx, inv_mul_cancel])
    have hxN : x ∈ Subgroup.normalizer (T₀ : Set X) := by
      have e : x = t' * (t'⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer ht') (hker _ hyk)
    obtain ⟨e₂, he₂⟩ := hsyl.2.1 ⟨t, ht⟩
    have hx2 : x ^ 2 ^ e₂ = 1 := by
      have h1 : t ^ 2 ^ e₂ = 1 := by
        have := congrArg Subtype.val he₂
        simpa using this
      rw [hx, conj_pow, h1, mul_one, mul_inv_cancel]
    have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
      rintro ⟨g, hg⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨e₂, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx2,
        _root_.one_zpow]
    have hPx : IsPGroup 2 ↥(T₀ ⊔ Subgroup.zpowers x) :=
      IsPGroup.to_sup_of_normal_left' hsyl.2.1 hzp (by rw [Subgroup.zpowers_le]; exact hxN)
    have heq := hsyl.eq_of_le le_sup_left le_top hPx
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  ·
    intro u hu huZ
    set γ := eπ.symm (κ k) with hγ
    have hπγ : π γ = κ k := by
      have := MulEquiv.apply_symm_apply eπ (κ k)
      rw [← hγ] at this
      exact this
    have hγd : eS.symm γ = d := hk
    have hUinv : ((π γ : ↥L) : MulAut W) u ∈ U := hπ.2.2.2.1 (π γ) u hu
    have h1 := hε γ ⟨u, hu⟩ hUinv
    have hq : (QuotientGroup.mk (⟨((π γ : ↥L) : MulAut W) u, hUinv⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U) =
        QuotientGroup.mk ⟨u, hu⟩ := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h2 : ((π γ : ↥L) : MulAut W) u * u⁻¹ ∈ Z := by rw [hπγ]; exact huZ
      have h3 := Z.inv_mem h2
      have e : (((⟨((π γ : ↥L) : MulAut W) u, hUinv⟩ : ↥U)⁻¹ * ⟨u, hu⟩ : ↥U) : W) =
          (((π γ : ↥L) : MulAut W) u * u⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [_root_.mul_inv_rev, inv_inv, mul_comm]
      rw [e]
      exact h3
    rw [hq] at h1
    set v : Fin 3 → F := Multiplicative.toAdd (ε (QuotientGroup.mk ⟨u, hu⟩)) with hv
    have hγv : (((γ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).mulVec v =
        v := by
      have h2 := congrArg Multiplicative.toAdd h1
      rw [natAct] at h2
      simp only [toAdd_ofAdd] at h2
      exact h2.symm
    have hdm : ((d : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((γ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← hγd]
      have := specialLinearGroupEquivStatedSL_coe 3 F (eS.symm γ)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hv0 : v = 0 := hdfix v (by rw [hdm]; exact hγv)
    have h2 : ε (QuotientGroup.mk ⟨u, hu⟩) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hv, hv0]
      rfl
    rw [map_eq_one_iff _ ε.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2

end CFSG.Quasithin.H13.A6.A6S20
