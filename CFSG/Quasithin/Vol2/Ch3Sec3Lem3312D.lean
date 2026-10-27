module

public import CFSG.Quasithin.Background.GoldschmidtS146RArith
public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

namespace L3312

theorem modO2_equiv_of_surjective {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hk : IsPGroup 2 ↥f.ker) :
    Nonempty ((B ⧸ CFSG.pCore 2 B) ≃* (A ⧸ CFSG.pCore 2 A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 B).Normal := CFSG.pCore_normal
  have : (CFSG.pCore 2 A).Normal := CFSG.pCore_normal
  let g : A →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : g.ker = CFSG.pCore 2 A := by
    have hcomap : g.ker = (CFSG.pCore 2 B).comap f := by
      ext a
      simp [g, QuotientGroup.eq_one_iff]
    apply le_antisymm
    ·
      rw [hcomap]
      refine le_sSup ⟨Subgroup.Normal.comap inferInstance f, ?_⟩
      intro a
      obtain ⟨k, hk1⟩ := (CFSG.pCore_isPGroup (p := 2) (G := B)) ⟨f a, a.2⟩
      have h1 : f ((a : A) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk1
      obtain ⟨m, hm⟩ := hk ⟨_, h1⟩
      refine ⟨k + m, Subtype.ext ?_⟩
      have h2 : ((a : A) ^ 2 ^ k) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [pow_add, pow_mul, h2]
    ·
      intro a ha
      rw [hcomap, Subgroup.mem_comap]
      have hmap : (CFSG.pCore 2 A).map f ≤ CFSG.pCore 2 B :=
        le_sSup ⟨Subgroup.Normal.map inferInstance f hf,
          (CFSG.pCore_isPGroup (p := 2) (G := A)).map f⟩
      exact hmap ⟨a, ha, rfl⟩
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker))⟩

@[expose] def Type3312R (W : Type) [Group W] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n W) ∨ IsPSL 3 2 1 W ∨ IsPSL 4 2 1 W

namespace Type3312R

variable {W : Type} [Group W]

theorem of_equiv {W' : Type} [Group W'] (e : W ≃* W') (h : Type3312R W') : Type3312R W := by
  have hpsl : ∀ {n p f : ℕ}, IsPSL n p f W' → IsPSL n p f W := fun {n p f} h' => by
    obtain ⟨hv, K, hK1, hK2, hK3, ⟨f'⟩⟩ := h'
    exact ⟨hv, K, hK1, hK2, hK3, ⟨e.trans f'⟩⟩
  rcases h with ⟨n, hn, h⟩ | h | h
  · exact Or.inl ⟨n, hn, hpsl h⟩
  · exact Or.inr (Or.inl (hpsl h))
  · exact Or.inr (Or.inr (hpsl h))

theorem isSimpleGroup (h : Type3312R W) : IsSimpleGroup W := by
  rcases h with ⟨n, -, h⟩ | h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity W 2 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity W 3 2 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity W 4 2 1 h).2

theorem card (h : Type3312R W) :
    (∃ n : ℕ, 2 ≤ n ∧ Nat.card W = 2 ^ n * ((2 ^ n) ^ 2 - 1)) ∨ Nat.card W = 168 ∨
      Nat.card W = 20160 := by
  rcases h with ⟨n, hn, h⟩ | h | h
  · exact Or.inl ⟨n, hn, GoldS146R.card_isPSL_two_two h⟩
  · exact Or.inr (Or.inl (SBc11.card_of_isPSL_three_two h))
  · exact Or.inr (Or.inr (Ch1Four.card_of_isPSL_four_two h))

theorem three_le_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem le_sq_sub_one {a m : ℕ} (hm : a ≤ m) : a ^ 2 - 1 ≤ m ^ 2 - 1 :=
  Nat.sub_le_sub_right (Nat.pow_le_pow_left hm 2) 1

theorem three_dvd_card (h : Type3312R W) : 3 ∣ Nat.card W := by
  rcases h.card with ⟨n, hn, hc⟩ | hc | hc
  · rw [hc]
    refine Dvd.dvd.mul_left ?_ _
    have h1 : (2 ^ n) ^ 2 % 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num [Nat.pow_mod]
    have h4 := three_le_pow hn
    have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · rw [hc]; norm_num
  · rw [hc]; norm_num

theorem not_comm (h : Type3312R W) : ∃ a b : W, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have hs := h.isSimpleGroup
  have : IsMulCommutative W := ⟨⟨hc⟩⟩
  have hp := (Group.is_simple_iff_prime_card.mp hs)
  have h3 := h.three_dvd_card
  have h3' : Nat.card W = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
  rcases h.card with ⟨n, hn, hc'⟩ | hc' | hc' <;> rw [hc'] at h3'
  · have h4 := three_le_pow hn
    have h15 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := le_sq_sub_one h4
    have : 4 * 15 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h4 (by simpa using h15)
    omega
  · omega
  · omega

theorem false_of_two_pow_mul (h : Type3312R W) {k N : ℕ} (hN : N = 360 ∨ N = 1080)
    (hk : 2 ^ k * Nat.card W = N) : False := by
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rcases h.card with ⟨n, hn, hc⟩ | hc | hc <;> rw [hc] at hk
  · have h4 := three_le_pow hn
    have h15 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := le_sq_sub_one h4
    have hle : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≤ 1080 := by
      have := Nat.le_mul_of_pos_left (2 ^ n * ((2 ^ n) ^ 2 - 1)) (Nat.one_le_two_pow (n := k))
      rcases hN with rfl | rfl <;> omega
    have hn3 : n ≤ 3 := by
      by_contra hn4
      have h16 : 16 ≤ 2 ^ n :=
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h255 : 16 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := le_sq_sub_one h16
      have : 16 * 255 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h16 (by simpa using h255)
      omega
    have hk5 : k ≤ 5 := by
      by_contra hk6
      have h64 : 64 ≤ 2 ^ k :=
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 64 * 60 ≤ 2 ^ k * (2 ^ n * ((2 ^ n) ^ 2 - 1)) :=
        Nat.mul_le_mul h64 (Nat.mul_le_mul h4 (by simpa using h15))
      rcases hN with rfl | rfl <;> omega
    interval_cases n <;> interval_cases k <;> rcases hN with rfl | rfl <;> omega
  · have hk5 : k ≤ 3 := by
      by_contra hk4
      have h16 : 16 ≤ 2 ^ k :=
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rcases hN with rfl | rfl <;> omega
    interval_cases k <;> rcases hN with rfl | rfl <;> omega
  · rcases hN with rfl | rfl <;> omega

theorem isPSL_two_two_two_of_card (h : Type3312R W) (hc : Nat.card W = 60) : IsPSL 2 2 2 W := by
  rcases h with ⟨n, hn, h'⟩ | h' | h'
  · have h2 := GoldS146R.card_isPSL_two_two h'
    rw [hc] at h2
    have hn2 : n = 2 := by
      have h4 := three_le_pow hn
      by_contra hne
      have h8 : 8 ≤ 2 ^ n :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h63 : 8 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := le_sq_sub_one h8
      have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by simpa using h63)
      omega
    rwa [hn2] at h'
  · have := SBc11.card_of_isPSL_three_two h'
    omega
  · have := Ch1Four.card_of_isPSL_four_two h'
    omega

theorem not_isSz (h : Type3312R W) {f : ℕ} (hS : IsSz f W) :
    False := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := hS
  rw [hf] at hK
  have hc := CFSG.LieType.Ree.suzuki_order hK
  rw [← Nat.card_congr e.toEquiv] at hc
  have h3 := h.three_dvd_card
  rw [hc] at h3
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq h3
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  · omega

theorem not_isExt_elemAbelian {X : Type} [Group X] [Finite X]
    (h : Type3312R (X ⧸ CFSG.pCore 2 X)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hext : IsExt X (fun V _ => IsElemAbelianOfRank p 2 V) (fun Y _ => IsSL2 p Y)) : False := by
  obtain ⟨V, hVn, ⟨eV⟩, -⟩ := hext
  have : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hs := h.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have hVc : Nat.card V = p ^ 2 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hVO : ∀ v ∈ V, v ∈ CFSG.pCore 2 X → v = 1 := by
    intro v hv hvO
    have hvp : (⟨v, hv⟩ : V) ^ p ^ 2 = 1 := by
      rw [← hVc]
      exact pow_card_eq_one'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨v, hvO⟩
    have h1 : v ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : v ^ p ^ 2 = 1 := by simpa using congrArg Subtype.val hvp
    have hcop : Nat.Coprime (2 ^ k) (p ^ 2) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have h3 := (pow_gcd_eq_one (a := v)).mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at h3
  set Vb := V.map (QuotientGroup.mk' (CFSG.pCore 2 X)) with hVb
  have hVbn : Vb.Normal := hVn.map _ (QuotientGroup.mk'_surjective _)
  have hVb1 : Vb ≠ ⊥ := by
    intro hb
    have hV1 : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have : (QuotientGroup.mk' (CFSG.pCore 2 X) v) ∈ Vb := ⟨v, hv, rfl⟩
      rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact (Subgroup.mem_bot).mpr (hVO v hv this)
    rw [hV1, Subgroup.card_bot] at hVc
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  have hVbtop : Vb = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal Vb).resolve_left hVb1
  obtain ⟨a, b, hab⟩ := h.not_comm
  apply hab
  have ha : a ∈ Vb := hVbtop ▸ Subgroup.mem_top a
  have hb : b ∈ Vb := hVbtop ▸ Subgroup.mem_top b
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hb
  have hcomm : u * w = w * u := by
    have := congrArg Subtype.val (eV.injective (by
      rw [map_mul, map_mul, mul_comm] : eV (⟨u, hu⟩ * ⟨w, hw⟩) = eV (⟨w, hw⟩ * ⟨u, hu⟩)))
    simpa using this
  rw [← map_mul, ← map_mul, hcomm]

end Type3312R

end L3312

end CFSG.Quasithin.H13
