module

public import CFSG.Quasithin.Vol2.Ch1EightFourCore
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.CharacterTheory.Burnside
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.Ch1Four

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def NSof (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ N : Subgroup X, N.Normal ∧ N ≠ ⊤ ∧ Nat.card N = n

theorem NSof.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ} (h : NSof X n) :
    NSof Y n := by
  obtain ⟨N, hN, hne, hcard⟩ := h
  refine ⟨N.map e.toMonoidHom, hN.map _ e.surjective, fun htop => hne ?_, ?_⟩
  · rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective N, htop,
      Subgroup.comap_top]
  · rw [Subgroup.card_map_of_injective e.injective, hcard]

theorem InitNum.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : InitNum (Nat.card X) (NSof X)) : InitNum (Nat.card Y) (NSof Y) := by
  rw [← Nat.card_congr e.toEquiv]
  rcases h with h | h | h | ⟨p, k, n, hp, hp5, hn, hNS, hk⟩ | ⟨p, k, hp, hp5, hNS, hk⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, k, n, hp, hp5, hn, hNS.of_mulEquiv e, hk⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, k, hp, hp5, hNS.of_mulEquiv e, hk⟩)))

@[expose] def InitNum3 (m : ℕ) (NS : ℕ → Prop) : Prop :=
  (∃ c ∈ finOrders, ∃ k, m * 2 ^ k = c) ∨ (∃ n, 2 ≤ n ∧ m = 2 ^ n * (4 ^ n - 1)) ∨
    (∃ p k n : ℕ, p.Prime ∧ 5 ≤ p ∧ Odd n ∧ NS n ∧ m * 2 ^ k = n * (p * (p ^ 2 - 1))) ∨
    ∃ p k : ℕ, p.Prime ∧ 5 ≤ p ∧ NS (p ^ 2) ∧ m * 2 ^ k = p ^ 3 * (p ^ 2 - 1)

theorem InitNum3.initNum {m : ℕ} {NS : ℕ → Prop} (h : InitNum3 m NS) : InitNum m NS := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem InitNum3.three_dvd {m : ℕ} {NS : ℕ → Prop} (h : InitNum3 m NS) : 3 ∣ m := by
  have hc3 : ∀ k, Nat.Coprime 3 (2 ^ k) := fun k => Nat.Coprime.pow_right _ (by norm_num)
  rcases h with ⟨c, hc, k, hk⟩ | ⟨n, -, rfl⟩ | ⟨p, k, n, hp, hp5, -, -, hk⟩ |
    ⟨p, k, hp, hp5, -, hk⟩
  · have h3 : 3 ∣ c := by
      simp only [finOrders, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    exact (hc3 k).dvd_of_dvd_mul_right (hk ▸ h3)
  · have h4 : 3 ∣ 4 ^ n - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one 4 n
    exact h4.mul_left _
  · exact (hc3 k).dvd_of_dvd_mul_right
      (hk ▸ ((three_dvd_sq_sub_one_of_prime hp hp5).mul_left p).mul_left n)
  · exact (hc3 k).dvd_of_dvd_mul_right (hk ▸ (three_dvd_sq_sub_one_of_prime hp hp5).mul_left _)

variable {H : Type} [Group H] [Finite H]

theorem card_modO2_mul : ∃ j, Nat.card (H ⧸ CFSG.pCore 2 H) * 2 ^ j = Nat.card H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  exact ⟨j, by rw [← hj, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]⟩

theorem card_modO2_mul_of_le {V : Subgroup H} [V.Normal] (hV : IsPGroup 2 V) :
    ∃ t, Nat.card (H ⧸ CFSG.pCore 2 H) * 2 ^ t = Nat.card (H ⧸ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : V ≤ CFSG.pCore 2 H := le_sSup ⟨inferInstance, hV⟩
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hdvd : Nat.card V ∣ 2 ^ j := hj ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hij : i ≤ j := by
    have := Nat.le_of_dvd (by positivity) hdvd
    rw [hi] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  refine ⟨j - i, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 H)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [hj] at h1
  rw [hi] at h2
  have e : 2 ^ j = 2 ^ (j - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel hij]
  rw [e, ← mul_assoc] at h1
  have := h1.symm.trans h2
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

theorem exists_image_of_odd {V : Subgroup H} [V.Normal] (hV : Odd (Nat.card V)) :
    ∃ (N : Subgroup (H ⧸ CFSG.pCore 2 H)) (_ : N.Normal) (j : ℕ), Nat.card N = Nat.card V ∧
      Nat.card ((H ⧸ CFSG.pCore 2 H) ⧸ N) * 2 ^ j = Nat.card (H ⧸ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  set f := QuotientGroup.mk' (CFSG.pCore 2 H) with hf
  have hinf : V ⊓ CFSG.pCore 2 H = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hj]
    exact (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hV))
  have hcard : Nat.card (V.map f) = Nat.card V := by
    have hinj : Function.Injective (f.comp V.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      have : (x : H) ∈ V ⊓ CFSG.pCore 2 H := ⟨x.2, hx⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
    have hr : (f.comp V.subtype).range = V.map f := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  refine ⟨V.map f, Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _), j,
    hcard, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.map f)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 H)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [hcard] at h1
  rw [h1, hj] at h2
  have := h2.symm.trans h3
  have hV0 : 0 < Nat.card V := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hV0
  calc Nat.card ((H ⧸ CFSG.pCore 2 H) ⧸ V.map f) * 2 ^ j * Nat.card V
      = Nat.card ((H ⧸ CFSG.pCore 2 H) ⧸ V.map f) * Nat.card V * 2 ^ j := by ring
    _ = Nat.card (H ⧸ V) * Nat.card V := this


section Types

variable {Y : Type} [Group Y]

theorem card_of_isAlt' {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k Y) : Nat.card Y = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

theorem card_of_isHat' {S : Type} [Group S] (h : IsHat Y S) : Nat.card Y = Nat.card S * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center Y).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv]

theorem card_of_isPSL' {n p e : ℕ} (hn : 1 ≤ n) (h : IsPSL n p e Y) :
    Nat.card Y = (p ^ e) ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, ((p ^ e) ^ j - 1)) /
      Nat.gcd n (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hn h

theorem card_of_isPSL_three_two (h : IsPSL 3 2 1 Y) : Nat.card Y = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_of_isPSL_four_two (h : IsPSL 4 2 1 Y) : Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_of_isPSL_three_four (h : IsPSL 3 2 2 Y) : Nat.card Y = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem card_of_isPSL_two_two {n : ℕ} (h : IsPSL 2 2 n Y) :
    2 ≤ n ∧ Nat.card Y = 2 ^ n * (4 ^ n - 1) := by
  have hadm := h.1
  obtain ⟨-, hn1, -, h22, -⟩ := hadm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact h22 rfl
  refine ⟨hn2, ?_⟩
  rw [card_of_isPSL' (by norm_num) h]
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    refine Nat.coprime_two_left.mpr ?_
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hg, Nat.div_one, h4]
  simp

theorem card_of_isPSL_two_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 2 p 1 Y) :
    2 * Nat.card Y = p * (p ^ 2 - 1) := by
  rw [card_of_isPSL' (by norm_num) h]
  have hodd := hp.odd_of_ne_two hp2
  have hg : Nat.gcd 2 (p - 1) = 2 := by
    obtain ⟨a, rfl⟩ := hodd
    simp
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton]
  rw [hg]
  have : 2 ∣ p * (p ^ 2 - 1) := by
    obtain ⟨a, rfl⟩ := hodd
    exact Dvd.dvd.mul_left ⟨2 * a ^ 2 + 2 * a, by ring_nf; omega⟩ _
  exact Nat.mul_div_cancel' this

theorem card_of_isSL2' {p : ℕ} (hp : p.Prime) (h : IsSL2 p Y) : Nat.card Y = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear (ZMod p) 2 (by norm_num), Nat.card_zmod]
  simp

theorem card_of_isSporadic_M22' (h : IsSporadic .M22 Y) :
    Nat.card Y = 443520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M22

theorem card_of_isSporadic_M24' (h : IsSporadic .M24 Y) :
    Nat.card Y = 244823040 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M24

theorem not_three_dvd_card_of_isSz' {f : ℕ} (h : IsSz f Y) :
    ¬ 3 ∣ Nat.card Y := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK,
    show (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) =
      (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1) by ring]
  exact not_three_dvd_sz a

theorem isPGroup_of_isE2 {n : ℕ} (h : IsE2 n Y) : IsPGroup 2 Y := by
  obtain ⟨e⟩ := h
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin n → ZMod 2) = 2 ^ n
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem isPGroup_of_isExtraspecial2 {m : ℕ} (h : IsExtraspecial2 m Y) : IsPGroup 2 Y :=
  IsPGroup.of_card h.2

theorem isPGroup_of_isZ4Cubed (h : IsZ4Cubed Y) : IsPGroup 2 Y := by
  obtain ⟨e⟩ := h
  refine IsPGroup.of_card (n := 6) ?_
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → ZMod 4) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem isPGroup_of_isZ4StarExtra2 (h : IsZ4StarExtra2 Y) : IsPGroup 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ, -, hE, hZc, hZE, -⟩ := h
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]; exact hz⟩
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num)
  have hEp : IsPGroup 2 E := IsPGroup.of_card hE.2
  have h1 : IsPGroup 2 ↥(Z ⊔ E) := hZp.to_sup_of_normal_left hEp
  rw [hZE] at h1
  exact h1.of_equiv Subgroup.topEquiv

end Types


section Packs

variable {B : Type} [Group B] [Finite B]

theorem init3_of_card {c : ℕ} (hc : c ∈ finOrders) (h : Nat.card B = c) :
    InitNum3 (Nat.card (B ⧸ CFSG.pCore 2 B)) (NSof (B ⧸ CFSG.pCore 2 B)) := by
  obtain ⟨j, hj⟩ := card_modO2_mul (H := B)
  exact Or.inl ⟨c, hc, j, hj.trans h⟩

theorem init3_of_ext {c : ℕ} (hc : c ∈ finOrders) {V : Subgroup B} [V.Normal] (hV : IsPGroup 2 V)
    (h : Nat.card (B ⧸ V) = c) :
    InitNum3 (Nat.card (B ⧸ CFSG.pCore 2 B)) (NSof (B ⧸ CFSG.pCore 2 B)) := by
  obtain ⟨j, hj⟩ := card_modO2_mul_of_le hV
  exact Or.inl ⟨c, hc, j, hj.trans h⟩

omit [Finite B] in
theorem init3_of_modO2 {c : ℕ} (hc : c ∈ finOrders) (h : Nat.card (B ⧸ CFSG.pCore 2 B) = c) :
    InitNum3 (Nat.card (B ⧸ CFSG.pCore 2 B)) (NSof (B ⧸ CFSG.pCore 2 B)) :=
  Or.inl ⟨c, hc, 0, by rw [pow_zero, mul_one, h]⟩

theorem nontrivial_of_card_eq {X : Type} [Group X] [Finite X] {p A k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpA : p ∣ A) (h : Nat.card X * 2 ^ k = A * (p ^ 2 - 1)) : Nontrivial X := by
  rw [← Finite.one_lt_card_iff_nontrivial]
  by_contra hle
  push Not at hle
  have h1 : Nat.card X = 1 := le_antisymm hle Nat.card_pos
  rw [h1, one_mul] at h
  exact prime_not_dvd_two_pow hp hp2 k (h ▸ hpA.mul_right _)

theorem init3_of_card_p {p i : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : Nat.card B * 2 ^ i = p * (p ^ 2 - 1)) :
    InitNum3 (Nat.card (B ⧸ CFSG.pCore 2 B)) (NSof (B ⧸ CFSG.pCore 2 B)) := by
  obtain ⟨j, hj⟩ := card_modO2_mul (H := B)
  have e : Nat.card (B ⧸ CFSG.pCore 2 B) * 2 ^ (j + i) = 1 * (p * (p ^ 2 - 1)) := by
    rw [pow_add, ← mul_assoc, hj, h, one_mul]
  have : Nontrivial (B ⧸ CFSG.pCore 2 B) :=
    nontrivial_of_card_eq hp (by omega) (dvd_refl p) (by rw [e, one_mul])
  exact Or.inr (Or.inr (Or.inl ⟨p, j + i, 1, hp, hp5, odd_one, ⟨⊥, inferInstance,
    bot_ne_top, Subgroup.card_bot⟩, e⟩))

theorem init_of_odd_ext {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {V : Subgroup B} [V.Normal]
    (hV : Odd (Nat.card V)) (h : Nat.card (B ⧸ V) = p * (p ^ 2 - 1)) :
    ∃ k, NSof (B ⧸ CFSG.pCore 2 B) (Nat.card V) ∧
      Nat.card (B ⧸ CFSG.pCore 2 B) * 2 ^ k = Nat.card V * (p * (p ^ 2 - 1)) := by
  obtain ⟨N, hN, j, hcard, hj⟩ := exists_image_of_odd hV
  refine ⟨j, ⟨N, hN, fun htop => ?_, hcard⟩, ?_⟩
  · have : Nat.card ((B ⧸ CFSG.pCore 2 B) ⧸ N) = 1 := by
      rw [← Subgroup.index, htop, Subgroup.index_top]
    rw [this, one_mul, h] at hj
    exact prime_not_dvd_two_pow hp (by omega) j (hj ▸ dvd_mul_right p _)
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcard, ← h, ← hj]
    ring

end Packs


section Cases

variable {B : Type} [Group B] [Finite B]

theorem init3_of_isExt {PV PY : ∀ (V : Type) [Group V], Prop} {c : ℕ} (hc : c ∈ finOrders)
    (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V)
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = c) (h : IsExt B PV PY) :
    InitNum3 (Nat.card (B ⧸ CFSG.pCore 2 B)) (NSof (B ⧸ CFSG.pCore 2 B)) := by
  obtain ⟨V, hVn, hPV, hPY⟩ := h
  exact init3_of_ext hc (hV _ hPV) (hY _ hPY)

theorem card_alt5 {Y : Type} [Group Y] (h : IsAlt 5 Y) : Nat.card Y = 60 := by
  rw [card_of_isAlt' (by norm_num) h]
  decide

theorem card_alt6 {Y : Type} [Group Y] (h : IsAlt 6 Y) : Nat.card Y = 360 := by
  rw [card_of_isAlt' (by norm_num) h]
  decide

theorem card_alt7 {Y : Type} [Group Y] (h : IsAlt 7 Y) : Nat.card Y = 2520 := by
  rw [card_of_isAlt' (by norm_num) h]
  decide

theorem card_hat6 {Y : Type} [Group Y] (h : IsHat Y (alternatingGroup (Fin 6))) :
    Nat.card Y = 1080 := by
  rw [card_of_isHat' h, card_alt6 ⟨MulEquiv.refl _⟩]

theorem card_hatM22 {Y : Type} [Group Y]
    (h : IsHat Y (CFSG.Blueprint.NativeSporadic.Carrier .M22)) : Nat.card Y = 1330560 := by
  rw [card_of_isHat' h, card_of_isSporadic_M22' ⟨MulEquiv.refl _⟩]

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have : p = 4 := by omega
  subst this
  norm_num at hp

theorem init3_of_a312Case
    {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} (h : A312Case B L) :
    A312C3 B L ∨ InitNum3 (Nat.card (ModO2 B)) (NSof (ModO2 B)) := by
  have hE2 : ∀ k, ∀ (V : Type) [Group V], IsE2 k V → IsPGroup 2 V := fun k V _ h =>
    isPGroup_of_isE2 h
  have hX2 : ∀ k, ∀ (V : Type) [Group V], IsExtraspecial2 k V → IsPGroup 2 V := fun k V _ h =>
    isPGroup_of_isExtraspecial2 h
  have hA5 : ∀ (Y : Type) [Group Y], IsAlt 5 Y → Nat.card Y = 60 := fun Y _ h => card_alt5 h
  have hA6 : ∀ (Y : Type) [Group Y], IsAlt 6 Y → Nat.card Y = 360 := fun Y _ h => card_alt6 h
  have hA7 : ∀ (Y : Type) [Group Y], IsAlt 7 Y → Nat.card Y = 2520 := fun Y _ h => card_alt7 h
  have hH6 : ∀ (Y : Type) [Group Y], IsHat Y (alternatingGroup (Fin 6)) → Nat.card Y = 1080 :=
    fun Y _ h => card_hat6 h
  have hL32 : ∀ (Y : Type) [Group Y], IsPSL 3 2 1 Y → Nat.card Y = 168 := fun Y _ h =>
    card_of_isPSL_three_two h
  have hL42 : ∀ (Y : Type) [Group Y], IsPSL 4 2 1 Y → Nat.card Y = 20160 := fun Y _ h =>
    card_of_isPSL_four_two h
  have m60 : (60 : ℕ) ∈ finOrders := by decide
  have m168 : (168 : ℕ) ∈ finOrders := by decide
  have m360 : (360 : ℕ) ∈ finOrders := by decide
  have m1080 : (1080 : ℕ) ∈ finOrders := by decide
  have m2520 : (2520 : ℕ) ∈ finOrders := by decide
  have m20160 : (20160 : ℕ) ∈ finOrders := by decide
  have m443520 : (443520 : ℕ) ∈ finOrders := by decide
  have m1330560 : (1330560 : ℕ) ∈ finOrders := by decide
  have m244823040 : (244823040 : ℕ) ∈ finOrders := by decide
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨n, hn⟩, -, -⟩ := h
    obtain ⟨h2, hc⟩ := card_of_isPSL_two_two hn
    exact Or.inr (Or.inr (Or.inl ⟨n, h2, hc⟩))
  ·
    exact Or.inl h
  ·
    exact Or.inr (init3_of_modO2 m168 (hL32 _ h.1))
  ·
    exact Or.inr (init3_of_modO2 m20160 (hL42 _ h.1))
  ·
    rcases h.1 with h | h
    · exact Or.inr (init3_of_card m60 (hA5 _ h))
    · exact Or.inr (init3_of_card m168 (hL32 _ h))
  ·
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr (init3_of_card m360 (hA6 _ h))
    · exact Or.inr (init3_of_card m1080 (hH6 _ h))
  ·
    rcases h with ⟨p, hp, hp3, hB, -⟩ | ⟨h, -⟩
    · have hp5 := five_le_of_prime hp hp3
      exact Or.inr (init3_of_card_p hp hp5 (i := 1)
        (by rw [pow_one, mul_comm]; exact card_of_isPSL_two_odd hp (by omega) hB))
    · exact Or.inr (init3_of_card m60 (hA5 _ h))
  ·
    rcases h with ⟨s, p, hp, hp3, hB, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr (init3_of_card_p hp (five_le_of_prime hp hp3) (i := 0)
        (by rw [pow_zero, mul_one]; exact card_of_isSL2' hp hB))
    · exact Or.inr (init3_of_card m360 (hA6 _ h))
    · exact Or.inr (init3_of_card m1080 (hH6 _ h))
  ·
    obtain ⟨p, hp, hp3, ⟨V, hVn, hV, hY⟩, -⟩ := h
    have hp5 := five_le_of_prime hp hp3
    have hV2 : Nat.card V = p ^ 2 := by
      obtain ⟨e⟩ := hV
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      have : NeZero p := ⟨hp.ne_zero⟩
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hVodd : Odd (Nat.card V) := by
      rw [hV2]
      exact (hp.odd_of_ne_two (by omega)).pow
    obtain ⟨k, hNS, hk⟩ := init_of_odd_ext hp (by omega) hVodd (card_of_isSL2' hp hY)
    rw [hV2] at hNS hk
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, k, hp, by omega, hNS, by rw [hk]; ring⟩)))
  ·
    exact Or.inr (init3_of_card m360 (hA6 _ h.1))
  ·
    rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩
    · exact Or.inr (init3_of_isExt m60 (hE2 4) hA5 h)
    · exact Or.inr (init3_of_isExt m360 (hE2 4) hA6 h)
    · exact Or.inr (init3_of_isExt m60 (hE2 4) hA5 h)
    · exact Or.inr (init3_of_isExt m1080 (hE2 4) hH6 h)
  ·
    rcases h.1 with h | h | h | h | h | h | h
    · exact Or.inr (init3_of_card m443520 (card_of_isSporadic_M22' h))
    · exact Or.inr (init3_of_card m20160 (card_of_isPSL_three_four h))
    · exact Or.inr (init3_of_isExt m2520 (hE2 4) hA7 h)
    · exact Or.inr (init3_of_isExt m168 (hE2 4) hL32 h)
    · exact Or.inr (init3_of_isExt m168 (hE2 3) hL32 h)
    · exact Or.inr (init3_of_isExt m360 (hE2 4) hA6 h)
    · exact Or.inr (init3_of_isExt m60 (hE2 4) hA5 h)
  ·
    rcases h.1 with h | h | h | h
    · exact Or.inr (init3_of_isExt m20160 (hE2 4) hL42 h)
    · exact Or.inr (init3_of_isExt m168 (hE2 6) hL32 h)
    · exact Or.inr (init3_of_isExt m168 (hX2 3) hL32 h)
    · exact Or.inr (init3_of_isExt m1080 (hE2 6) hH6 h)
  ·
    exact Or.inr (init3_of_card m60 (hA5 _ h.1))
  ·
    exact Or.inr (init3_of_isExt m60 (hX2 2) hA5 h.1)
  ·
    rcases h.2 with h | h | h | h | h | h
    · exact Or.inr (init3_of_isExt m1330560 (hX2 6) (fun Y _ h => card_hatM22 h) h)
    · exact Or.inr (init3_of_isExt m244823040 (hE2 11)
        (fun Y _ h => card_of_isSporadic_M24' h) h)
    · exact Or.inr (init3_of_modO2 m60 (hA5 _ h))
    · exact Or.inr (init3_of_modO2 m1080 (hH6 _ h))
    · exact Or.inr (init3_of_modO2 m20160 (hL42 _ h))
    · exact Or.inr (init3_of_modO2 m168 (hL32 _ h))
  ·
    rcases h.1 with h | h
    · exact Or.inr (init3_of_isExt m60 (fun V _ h => isPGroup_of_isZ4StarExtra2 h) hA5 h)
    · exact Or.inr (init3_of_isExt m168 (fun V _ h => isPGroup_of_isZ4Cubed h) hL32 h)
  ·
    rcases h.1 with h | h
    · exact Or.inr (init3_of_isExt m168 (hX2 3) hL32 h)
    · exact Or.inr (init3_of_isExt m1080 (hE2 6) hH6 h)
  ·
    rcases h.1 with h | h
    · exact Or.inr (init3_of_modO2 m60 (hA5 _ h))
    · exact Or.inr (init3_of_modO2 m168 (hL32 _ h))

theorem init_of_a312Case
    {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}
    (h : A312Case B L) : InitNum (Nat.card (ModO2 B)) (NSof (ModO2 B)) := by
  rcases init3_of_a312Case h with h | h
  · obtain ⟨f, hf, -, -⟩ := h
    exact Or.inr (Or.inr (Or.inl (not_three_dvd_card_of_isSz' hf)))
  · exact h.initNum

end Cases


section Nonquasi

theorem false_of_perfect_card_24 {Y : Type} [Group Y] [Finite Y] (hY : Group.IsPerfect Y)
    (hc : Nat.card Y = 24) : False := by
  have := Fintype.ofFinite Y
  have hs : Group.IsSolvable Y :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hc]; norm_num)
  have hnt : Nontrivial Y := by
    rw [← Finite.one_lt_card_iff_nontrivial, hc]
    norm_num
  exact Group.IsPerfect.not_isSolvable Y hs

theorem init3_of_a312Nonquasi {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} (hBL : B ≤ L)
    (hperf : Group.IsPerfect ↥B) (h : A312Nonquasi B L) :
    InitNum3 (Nat.card (ModO2 B)) (NSof (ModO2 B)) := by
  set OL : Subgroup Q := (CFSG.oddCore ↥L).map L.subtype with hOL
  have hsub : OL.subgroupOf L = CFSG.oddCore ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hLO : L ≤ Subgroup.normalizer (OL : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
    rw [hsub]
    infer_instance
  have hBO : B ≤ Subgroup.normalizer (OL : Set Q) := hBL.trans hLO
  have : (OL.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBO
  set V := OL.subgroupOf B with hV
  have hVodd : Odd (Nat.card V) := by
    have h1 : Nat.card V = Nat.card ↥(OL ⊓ B) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective B.subtype_injective]
    have h2 : Nat.card ↥(OL ⊓ B) ∣ Nat.card OL := Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card OL = Nat.card (CFSG.oddCore ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h1]
    exact (h3 ▸ A312.odd_card_oddCore ↥L).of_dvd_nat h2
  have : (OL.subgroupOf (B ⊔ OL)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBO
  have hφ : Nat.card (↥B ⧸ V) = (OL.subgroupOf (B ⊔ OL)).index :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B OL hBO).toEquiv
  obtain ⟨p, hp, hp5, hcard⟩ : ∃ p, p.Prime ∧ 5 ≤ p ∧ Nat.card (↥B ⧸ V) = p * (p ^ 2 - 1) := by
    have hpq : Group.IsPerfect (↥B ⧸ V) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' V) (QuotientGroup.mk'_surjective _)
    unfold A312Nonquasi at h
    dsimp only at h
    rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, rfl, hSL⟩
    · have hc : Nat.card (↥B ⧸ V) = p * (p ^ 2 - 1) := by
        rw [hφ, ← hLB, hsub]
        exact card_of_isSL2' hp hSL
      have hp5 : 5 ≤ p := by
        by_contra hlt
        have hp3 : p = 3 := by
          have := hp.two_le
          interval_cases p <;> first | rfl | exact absurd rfl hp2 | exact absurd hp (by decide)
        subst hp3
        exact false_of_perfect_card_24 hpq (hc.trans (by norm_num))
      exact ⟨p, hp, hp5, hc⟩
    · refine ⟨5, by norm_num, le_rfl, ?_⟩
      rw [hφ]
      exact card_of_isSL2' (by norm_num) hSL
  obtain ⟨k, hNS, hk⟩ := init_of_odd_ext hp hp5 hVodd hcard
  exact Or.inr (Or.inr (Or.inl ⟨p, k, Nat.card V, hp, hp5, hVodd, hNS, hk⟩))

theorem init_of_a312Nonquasi {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} (hBL : B ≤ L)
    (hperf : Group.IsPerfect ↥B) (h : A312Nonquasi B L) :
    InitNum (Nat.card (ModO2 B)) (NSof (ModO2 B)) :=
  (init3_of_a312Nonquasi hBL hperf h).initNum

end Nonquasi

end CFSG.Quasithin.Ch1Four
