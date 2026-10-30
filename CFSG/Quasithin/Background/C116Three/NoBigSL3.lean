module

public import CFSG.Quasithin.Background.C116Three.GroupDefs
import CFSG.Models.PGLSimple
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.C116Three.ModuleDefs
public import CFSG.Quasithin.Background.C1GNA7Base
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.J1
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem odd_even_pow_sub_one {x k : ℕ} (hx : Even x) (hx0 : 0 < x) (hk : 1 ≤ k) :
    Odd (x ^ k - 1) := by
  have h1 : 1 ≤ x ^ k := Nat.one_le_pow _ _ hx0
  have h2 : x ^ k % 2 = 0 := Nat.even_iff.1 ((Nat.even_pow).2 ⟨hx, by omega⟩)
  exact Nat.odd_iff.2 (by omega)

theorem even_two_pow {m : ℕ} (hm : 1 ≤ m) : Even (2 ^ m) :=
  (Nat.even_pow).2 ⟨even_two, by omega⟩

theorem sl3_ne_psl2_two_pow {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro h
  have hx0 : 0 < 2 ^ m := by positivity
  have hxE : Even (2 ^ m) := even_two_pow hm
  have hy0 : 0 < 2 ^ n := by positivity
  have hyE : Even (2 ^ n) := even_two_pow hn
  have hA : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    (odd_even_pow_sub_one hxE hx0 (by norm_num)).mul (odd_even_pow_sub_one hxE hx0 (by norm_num))
  have hB : Odd ((2 ^ n) ^ 2 - 1) := odd_even_pow_sub_one hyE hy0 (by norm_num)
  have hS : (2 ^ m) ^ 3 = 2 ^ (3 * m) := by rw [← pow_mul, mul_comm]
  have h' : 2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← hS]
    exact h
  have hdA : 2 ^ n ∣ 2 ^ (3 * m) := Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hA)) ⟨_, h'⟩
  have hdB : 2 ^ (3 * m) ∣ 2 ^ n := Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left (3 * m) (Nat.coprime_two_left.2 hB)) ⟨_, h'.symm⟩
  have hn1 : n ≤ 3 * m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdA
  have hn2 : 3 * m ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdB
  obtain rfl : n = 3 * m := by omega
  have hAB := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (3 * m)) h'
  rw [← hS] at hAB
  have hx2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  set x := 2 ^ m with hx
  have hle : (x ^ 2 - 1) * (x ^ 3 - 1) ≤ x ^ 5 := by
    calc (x ^ 2 - 1) * (x ^ 3 - 1) ≤ x ^ 2 * x ^ 3 :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = x ^ 5 := by ring
  have h6 : 2 * x ^ 5 ≤ (x ^ 3) ^ 2 := by
    have : (x ^ 3) ^ 2 = x * x ^ 5 := by ring
    rw [this]
    exact Nat.mul_le_mul hx2 (le_refl _)
  have h5 : 2 ≤ x ^ 5 := le_trans hx2 (Nat.le_self_pow (by norm_num) x)
  omega

theorem two_pow_dvd_pm_one {p f : ℕ} (hp : Odd p) (hd : 2 ^ (f + 2) ∣ p ^ 2 - 1) :
    2 ^ (f + 1) ∣ p - 1 ∨ 2 ^ (f + 1) ∣ p + 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h2 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  have h4 : 2 ^ (f + 2) = 4 * 2 ^ f := by ring
  rw [h2, h4] at hd
  have hk : 2 ^ f ∣ k * (k + 1) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  have hsplit : 2 ^ f ∣ k ∨ 2 ^ f ∣ k + 1 := by
    rcases Nat.even_or_odd k with he | ho
    · exact Or.inl (Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.pow_left f (Nat.coprime_two_left.2 he.add_one)) hk)
    · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left
        (Nat.Coprime.pow_left f (Nat.coprime_two_left.2 ho)) hk)
  have h2f : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
  rcases hsplit with h | h
  · left
    rw [h2f, show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.mul_dvd_mul_left 2 h
  · right
    rw [h2f, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
    exact Nat.mul_dvd_mul_left 2 h

theorem sl3_ne_psl2_prime {m p : ℕ} (hm : 3 ≤ m) (hp : Odd p) (hp5 : 5 ≤ p) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ p * (p ^ 2 - 1) / 2 := by
  intro h
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ m := ⟨_, rfl⟩
  rw [← hq] at h
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq3 : 2 ^ (3 * m) = q ^ 3 := by rw [hq]; ring
  have hq3ge : 512 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq8 3)
  have hp2 : p ^ 2 % 2 = 1 := Nat.odd_iff.1 hp.pow
  have h2d : 2 ∣ p * (p ^ 2 - 1) := Dvd.dvd.mul_left (by omega) p
  have hE : p * (p ^ 2 - 1) = 2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) := by
    rw [h, Nat.mul_div_cancel' h2d]
  obtain ⟨f, hf⟩ : ∃ f, 3 * m = f + 1 := ⟨3 * m - 1, by omega⟩
  have h2pow : 2 ^ (3 * m + 1) = 2 * q ^ 3 := by rw [pow_succ, hq3]; ring
  have hd1 : 2 ^ (3 * m + 1) ∣ p * (p ^ 2 - 1) := by
    rw [hE, h2pow]
    exact mul_dvd_mul_left 2 (dvd_mul_right _ _)
  have hd2 : 2 ^ (3 * m + 1) ∣ p ^ 2 - 1 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hp)) hd1
  have hd3 : 2 ^ (f + 2) ∣ p ^ 2 - 1 := by
    rw [show f + 2 = 3 * m + 1 by omega]
    exact hd2
  have hdis := two_pow_dvd_pm_one hp hd3
  rw [← hf] at hdis
  have hsize : p + 1 < 2 ^ (3 * m) := by
    rw [hq3]
    by_contra hcon
    push Not at hcon
    have h8p : 7 * q ^ 3 ≤ 8 * p := by omega
    have hA5 : (q ^ 2 - 1) * (q ^ 3 - 1) ≤ q ^ 5 := by
      calc (q ^ 2 - 1) * (q ^ 3 - 1) ≤ q ^ 2 * q ^ 3 :=
            Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
        _ = q ^ 5 := by ring
    have hAq : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ q ^ 8 := by
      calc q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ q ^ 3 * q ^ 5 :=
            Nat.mul_le_mul (le_refl _) hA5
        _ = q ^ 8 := by ring
    have hp25 : 25 ≤ p ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hp5 2)
    have hp3 : p ^ 3 ≤ 2 * (p * (p ^ 2 - 1)) := by
      have h1 : p ^ 2 ≤ 2 * (p ^ 2 - 1) := by omega
      calc p ^ 3 = p * p ^ 2 := by ring
        _ ≤ p * (2 * (p ^ 2 - 1)) := Nat.mul_le_mul (le_refl _) h1
        _ = 2 * (p * (p ^ 2 - 1)) := by ring
    have hpq : p ^ 3 ≤ 4 * q ^ 8 := by omega
    have h3 := Nat.pow_le_pow_left h8p 3
    have e1 : (7 * q ^ 3) ^ 3 = 343 * q ^ 9 := by ring
    have e2 : (8 * p) ^ 3 = 512 * p ^ 3 := by ring
    rw [e1, e2] at h3
    have h9 : 343 * q ^ 9 ≤ 2048 * q ^ 8 := by omega
    have h10 : q ^ 8 * (343 * q) ≤ q ^ 8 * 2048 := by
      calc q ^ 8 * (343 * q) = 343 * q ^ 9 := by ring
        _ ≤ 2048 * q ^ 8 := h9
        _ = q ^ 8 * 2048 := by ring
    have h11 := Nat.le_of_mul_le_mul_left h10 (pow_pos (by omega : 0 < q) 8)
    omega
  rcases hdis with hd | hd
  · have := Nat.le_of_dvd (by omega) hd
    omega
  · have := Nat.le_of_dvd (by omega) hd
    omega

theorem sl3_card_ge {m : ℕ} (hm : 3 ≤ m) :
    16482816 ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  generalize 2 ^ m = x at h8 ⊢
  have h1 : 512 ≤ x ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left h8 3)
  have h2 : 64 ≤ x ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h8 2)
  have h3 : 63 ≤ x ^ 2 - 1 := by omega
  have h4 : 511 ≤ x ^ 3 - 1 := by omega
  calc 16482816 = 512 * (63 * 511) := by norm_num
    _ ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)

theorem card_psl2_two_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) : Nat.card (StatedProj (StatedSL 2 K)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 2) (by norm_num), hK]
  have hodd : Odd (2 ^ n - 1) := odd_even_pow_sub_one even_two (by norm_num) hn
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd)
  rw [hg, Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem card_psl2_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hK : Nat.card K = p)
    (hp : Odd p) : Nat.card (StatedProj (StatedSL 2 K)) = p * (p ^ 2 - 1) / 2 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (n := 2) (by norm_num), hK]
  obtain ⟨k, hk⟩ := hp
  have h2 : 2 ∣ p - 1 := ⟨k, by omega⟩
  rw [Nat.gcd_eq_left h2, Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem sl3_ne_sz {m f : ℕ} (hmo : Odd m) (hm : 1 ≤ m) (hf : 1 ≤ f) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠
      (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
  intro h
  have hxE : Even (2 ^ m) := even_two_pow hm
  have hx0 : 0 < 2 ^ m := by positivity
  have hyE : Even (2 ^ f) := even_two_pow hf
  have hA : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    (odd_even_pow_sub_one hxE hx0 (by norm_num)).mul (odd_even_pow_sub_one hxE hx0 (by norm_num))
  have hB : Odd ((2 ^ f - 1) * ((2 ^ f) ^ 2 + 1)) :=
    (odd_even_pow_sub_one even_two (by norm_num) hf).mul
      (Even.add_one (Nat.even_pow.2 ⟨hyE, by norm_num⟩))
  have hS : (2 ^ m) ^ 3 = 2 ^ (3 * m) := by rw [← pow_mul, mul_comm]
  have hb : (2 ^ f) ^ 2 = 2 ^ (f * 2) := by rw [← pow_mul]
  have h2 : 2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) =
      2 ^ (f * 2) * ((2 ^ f - 1) * ((2 ^ f) ^ 2 + 1)) := by
    rw [← hS, ← hb, h]
    ring
  have hdA : 2 ^ (f * 2) ∣ 2 ^ (3 * m) := Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hA)) ⟨_, h2⟩
  have hdB : 2 ^ (3 * m) ∣ 2 ^ (f * 2) := Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hB)) ⟨_, h2.symm⟩
  have hn1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdA
  have hn2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdB
  obtain ⟨k, hk⟩ := hmo
  omega

theorem nb3_card_eq_of_simple {X Y : Type} [Group X] [Group Y] [IsSimpleGroup X] (f : X →* Y)
    (hf : Function.Surjective f) (hY : 1 < Nat.card Y) : Nat.card X = Nat.card Y := by
  rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with hk | hk
  · exact Nat.card_congr (MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).1 hk, hf⟩).toEquiv
  · exfalso
    have hsub : Subsingleton Y := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      have hx : x ∈ f.ker := by rw [hk]; exact Subgroup.mem_top x
      have hy : y ∈ f.ker := by rw [hk]; exact Subgroup.mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      rw [hx, hy]⟩
    have h1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    omega

theorem nb3_one_le_of_card_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [hK, h, pow_zero] at h1
    omega
  · omega

theorem nb3_psl2_two_false {X Y : Type} [Group X] [Group Y] [Finite X] {n : ℕ} (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n) (e : X ≃* StatedProj (StatedSL 2 K))
    (f : X →* Y) (hf : Function.Surjective f) {m : ℕ} (hm : 3 ≤ m)
    (hY : Nat.card Y = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) : False := by
  have hn : 1 ≤ n := nb3_one_le_of_card_two_pow hK
  have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact card_psl2_two_pow hK hn
  have hm1 : 1 ≤ m := by omega
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    have hle := Nat.card_le_card_of_surjective f hf
    rw [hX, hY] at hle
    have h6 : 2 ^ 1 * ((2 ^ 1) ^ 2 - 1) = 6 := by norm_num
    rw [h6] at hle
    exact absurd (le_trans (sl3_card_ge hm) hle) (by norm_num)
  · have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hsimp : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
      CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (le_refl 2)
        (Or.inr (by rw [hK]; omega)) (Or.inr (by rw [hK]; omega))
    haveI : IsSimpleGroup X := e.isSimpleGroup
    have hY1 : 1 < Nat.card Y := by
      rw [hY]
      have := sl3_card_ge hm
      omega
    have heq := nb3_card_eq_of_simple f hf hY1
    exact sl3_ne_psl2_two_pow hm1 hn (hY.symm.trans (heq.symm.trans hX))

theorem nb3_psl2_p_false {X Y : Type} [Group X] [Group Y] [Finite X] {p : ℕ} (K : Type) [Field K]
    [Finite K] (hp : p.Prime) (hp3 : 3 < p) (hK : Nat.card K = p)
    (e : X ≃* StatedProj (StatedSL 2 K)) (f : X →* Y) (hf : Function.Surjective f) {m : ℕ}
    (hm : 3 ≤ m) (hY : Nat.card Y = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) :
    False := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hX : Nat.card X = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_psl2_prime hK hodd
  have hsimp : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (le_refl 2)
      (Or.inr (by rw [hK]; omega)) (Or.inr (by rw [hK]; omega))
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have hY1 : 1 < Nat.card Y := by
    rw [hY]
    have := sl3_card_ge hm
    omega
  have heq := nb3_card_eq_of_simple f hf hY1
  exact sl3_ne_psl2_prime hm hodd hp5 (hY.symm.trans (heq.symm.trans hX))

theorem nb3_sz_false {X Y : Type} [Group X] [Group Y] [Finite X]
    {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : X ≃* ↥(CFSG.Blueprint.suzukiGroup a K)) (f : X →* Y) (hf : Function.Surjective f)
    {m : ℕ} (hm : 3 ≤ m) (hmo : Odd m)
    (hY : Nat.card Y = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) : False := by
  obtain ⟨-, -, hsimp⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have hX : Nat.card X =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LieType.Ree.suzuki_order hK
  have hY1 : 1 < Nat.card Y := by
    rw [hY]
    have := sl3_card_ge hm
    omega
  have heq := nb3_card_eq_of_simple f hf hY1
  exact sl3_ne_sz (f := 2 * a + 1) hmo (by omega) (by omega)
    (hY.symm.trans (heq.symm.trans hX))

theorem nb3_j1_false {X Y : Type} [Group X] [Group Y] [Finite X]
    (e : X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) (f : X →* Y) (hf : Function.Surjective f)
    {m : ℕ} (hm : 3 ≤ m)
    (hY : Nat.card Y = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) : False := by
  have hX : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have hle := Nat.card_le_card_of_surjective f hf
  rw [hX, hY] at hle
  exact absurd (le_trans (sl3_card_ge hm) hle) (by norm_num)

theorem nb3_false_of_A38Types
    {X Y : Type} [Group X] [Group Y] [Finite X] (hX : A38Types X) (f : X →* Y)
    (hf : Function.Surjective f) {m : ℕ} (hm : 3 ≤ m) (hmo : Odd m)
    (hY : Nat.card Y = (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))) : False := by
  rcases hX with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hpX⟩
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hn
    exact nb3_psl2_two_false K hK e f hf hm hY
  · obtain ⟨-, a, ha, K, hKf, hKfin, hna, hK, ⟨e⟩⟩ := hn
    subst hna
    exact nb3_sz_false ha K hK e f hf hm hmo hY
  · obtain ⟨e⟩ := hJ
    exact nb3_j1_false e f hf hm hY
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hpX
    rw [pow_one] at hK
    exact nb3_psl2_p_false K hp hp3 hK e f hf hm hY

variable {G : Type} [Group G] [Finite G]

theorem nb3_A38_image (h38 : A38ForSQTK) {H T L : Subgroup G} {t : G} (hT : IsSylowTwoOf T H)
    (hSQ : IsSQTKTC H) (hL : L ∈ cComp H) (P : GroupPair H T L t) :
    A38Types ↥(modO2Image H L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hTH : T ≤ H := hT.1
  have hLb := modO2Image_mem_cComp hL
  have hQ : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) :=
    SQTKHyp.of_sqtkGroup ↥H (C1GN.isSQTKTC_iff_sqtkGroup.1 hSQ)
  have hnot : ¬ (modO2Image H L).Normal := fun hnorm => by
    have hn : (L.subgroupOf H).Normal :=
      normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H)
        (subgroupOf_mem_cComp hL) hnorm
    exact P.tN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).1 hn (hTH P.tT))
  obtain ⟨hL1, -⟩ := h38 _ hQ _ hLb
  rcases hL1 with hnL | ⟨hA, -⟩
  · exact absurd hnL hnot
  · exact hA

theorem nb3_surj {V H L : Subgroup G} (hVred : IsTwoReducedIn H V) (hL : L ≤ H) :
    ∃ f : ↥(modO2Image H L) →* ↥(autI hVred.2.2.1 L), Function.Surjective f := by
  have hNn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hVred.2.1
  have hker : CFSG.pCore 2 ↥H ≤ (convHom hVred.2.2.1 H hHN).ker := by
    intro n hn
    rw [ker_convHom]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨n.2,
      CFSG.Quasithin.pCoreOf_le_centralizer_of_isTwoReducedIn hVred
        ((CFSG.mem_openPCoreOf_iff n).2 hn)⟩)
  let ψ : ↥H ⧸ CFSG.pCore 2 ↥H →* MulAut (IntMod V hVred.2.2.1) :=
    QuotientGroup.lift _ (convHom hVred.2.2.1 H hHN) hker
  refine ⟨(ψ.comp (modO2Image H L).subtype).codRestrict (autI hVred.2.2.1 L) ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact convI_mem_autI hVred.2.2.1 (Subgroup.mem_subgroupOf.1 hy) (hHN y.2)
  · rintro ⟨z, hz⟩
    obtain ⟨g, hgL, rfl⟩ := (mem_autI hVred.2.2.1).1 hz
    have hgH : (g : G) ∈ H := hL hgL
    refine ⟨⟨QuotientGroup.mk' _ ⟨(g : G), hgH⟩,
      Subgroup.mem_map.2 ⟨⟨(g : G), hgH⟩, Subgroup.mem_subgroupOf.2 hgL, rfl⟩⟩, ?_⟩
    rfl

theorem nb3_autI_of_certs
    (h38 : A38ForSQTK) {H T V L : Subgroup G} {t : G} (hH : CharTwo H)
    (hVred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) (hSQ : IsSQTKTC H) (hL : L ∈ cComp H)
    (hq : QuasiData V L) (P : GroupPair H T L t) : NoBigSL3 (autI hVred.2.2.1 L) := by
  unfold NoBigSL3
  rintro ⟨m, K, hKf, hKfin, hm, hmo, hK, ⟨e⟩⟩
  have hY : Nat.card ↥(autI hVred.2.2.1 L) =
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hK]
  obtain ⟨f, hf⟩ := nb3_surj hVred (le_of_mem_cComp hL)
  exact nb3_false_of_A38Types (nb3_A38_image h38 hT hSQ hL P) f hf hm hmo hY

theorem noBigSL3_autI
    (h38 : A38ForSQTK) {H T V L : Subgroup G} {t : G} (hH : CharTwo H)
    (hVred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) (hSQ : IsSQTKTC H) (hL : L ∈ cComp H)
    (hq : QuasiData V L) (P : GroupPair H T L t) : NoBigSL3 (autI hVred.2.2.1 L) :=
  nb3_autI_of_certs h38 hH hVred hT hSQ hL hq P

end CFSG.Quasithin.C116Three
