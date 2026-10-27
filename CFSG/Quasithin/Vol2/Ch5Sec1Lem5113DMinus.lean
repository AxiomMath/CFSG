module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Orth
public import CFSG.Quasithin.Vol2.Ch5Sec1Hall

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)

section Frob

theorem pow_two_pow_gcd_eq_self {M : Type*} [Monoid M] {x : M} {j e : ℕ} (hj : x ^ 2 ^ j = x)
    (he : x ^ 2 ^ e = x) : x ^ 2 ^ Nat.gcd j e = x := by
  rcases Nat.lt_or_ge (Nat.gcd j e) e with h | h
  · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_gcd h
    have h3 : j * a = e * (j * a / e) + Nat.gcd j e := by
      have := Nat.div_add_mod (j * a) e
      omega
    have h4 : x ^ 2 ^ (j * a) = (x ^ 2 ^ (e * (j * a / e))) ^ 2 ^ Nat.gcd j e := by
      rw [← pow_mul, ← pow_add, ← h3]
    rw [iter_two_pow_eq_self hj a, iter_two_pow_eq_self he (j * a / e)] at h4
    exact h4.symm
  · rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0
      rw [Nat.gcd_zero_right]
      exact hj
    · rw [le_antisymm (Nat.le_of_dvd h0 (Nat.gcd_dvd_right j e)) h]
      exact he

theorem odd_of_pow_two_pow_eq_sq {M : Type*} [Monoid M] {ω : M} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {j : ℕ} (h : ω ^ 2 ^ j = ω ^ 2) : Odd j := by
  by_contra hj
  rw [Nat.not_odd_iff_even] at hj
  rw [pow_two_pow_eq_self_of_even hω hj] at h
  apply hω1
  calc ω = ω ^ 2 := h
    _ = ω * ω := pow_two ω
    _ = ω ^ 2 * ω := by rw [← h]
    _ = ω ^ 3 := (pow_succ ω 2).symm
    _ = 1 := hω

variable {F : Type} [Field F]

theorem eq_one_of_pow_add_one [Finite F] [CharP F 2] {m j : ℕ} (hcard : Nat.card F = 2 ^ (2 * m))
    (hj : Odd j) {x : F} (hx : x ^ (2 ^ m + 1) = 1) (hxj : x ^ 2 ^ j = x) : x = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h2m : x ^ 2 ^ (2 * m) = x := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hg := pow_two_pow_gcd_eq_self hxj h2m
  have hgm : Nat.gcd j (2 * m) ∣ m := by
    have hodd : Odd (Nat.gcd j (2 * m)) := hj.of_dvd_nat (Nat.gcd_dvd_left j (2 * m))
    have hcop : Nat.Coprime (Nat.gcd j (2 * m)) 2 := Nat.coprime_two_right.mpr hodd
    exact (Nat.Coprime.dvd_mul_left hcop).mp (Nat.gcd_dvd_right j (2 * m))
  obtain ⟨q, hq⟩ := hgm
  have hm : x ^ 2 ^ m = x := by
    rw [hq]
    exact iter_two_pow_eq_self hg q
  have hx2 : x ^ 2 ^ 1 = 1 := by
    have e : x ^ (2 ^ m + 1) = x ^ 2 ^ 1 := by
      rw [pow_succ x (2 ^ m), hm, pow_one (2 : ℕ), pow_two x]
    rw [← e]
    exact hx
  exact eq_one_of_pow_two_pow_eq_one hx2

end Frob

variable {G : Type} [Group G]

section Char

variable {L T W : Subgroup G} {F : Type} [Field F]

theorem borel_upper (hLW : L ≤ Subgroup.normalizer (W : Set G)) (ψ : ↥(autOn L W) ≃* SL(2, F))
    (hP : ∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn (T ⊓ L) W ↔ ∃ b : F, ψ x = unipSL b)
    {b : G} (hb : b ∈ borelL T L) :
    (ψ (autHom hLW ⟨b, hb.1⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
  upper_of_mem_normalizer ψ hP _ (conjAct_mem_normalizer_autOn ⟨b, hLW hb.1⟩ hb.2)

@[expose] noncomputable def borelChar (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (ψ : ↥(autOn L W) ≃* SL(2, F))
    (hP : ∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn (T ⊓ L) W ↔ ∃ b : F, ψ x = unipSL b) :
    ↥(borelL T L) →* Fˣ where
  toFun b := Units.mk0 ((ψ (autHom hLW ⟨b, b.2.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0)
    (left_ne_zero_of_mul_eq_one (upper_det (borel_upper hLW ψ hP b.2)))
  map_one' := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_one]
    rw [show (⟨((1 : ↥(borelL T L)) : G), (1 : ↥(borelL T L)).2.1⟩ : ↥L) = 1 from rfl, map_one,
      map_one]
    simp
  map_mul' a b := by
    apply Units.ext
    rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0]
    rw [show (⟨((a * b : ↥(borelL T L)) : G), (a * b).2.1⟩ : ↥L) = ⟨a, a.2.1⟩ * ⟨b, b.2.1⟩ from
      rfl, map_mul, map_mul]
    exact (upper_mul (borel_upper hLW ψ hP a.2) (borel_upper hLW ψ hP b.2)).2

variable (hLW : L ≤ Subgroup.normalizer (W : Set G)) (ψ : ↥(autOn L W) ≃* SL(2, F))
  (hP : ∀ x : ↥(autOn L W), (x : MulAut ↥W) ∈ autOn (T ⊓ L) W ↔ ∃ b : F, ψ x = unipSL b)

theorem coe_borelChar (b : ↥(borelL T L)) :
    (borelChar hLW ψ hP b : F) = (ψ (autHom hLW ⟨b, b.2.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
  rfl

theorem borelChar_eq_one {s : G} (hs : s ∈ T ⊓ L) (hsB : s ∈ borelL T L) :
    borelChar hLW ψ hP ⟨s, hsB⟩ = 1 := by
  apply Units.ext
  rw [coe_borelChar, Units.val_one]
  have hsS : ((autHom hLW ⟨s, hsB.1⟩ : ↥(autOn L W)) : MulAut ↥W) ∈ autOn (T ⊓ L) W :=
    mem_autOn_iff.mpr ⟨⟨s, hLW hsB.1⟩, hs, rfl⟩
  obtain ⟨b, hb⟩ := (hP _).mp hsS
  rw [hb, coe_unipSL]
  simp

theorem eq_one_of_borelChar [Finite G] (hC : L ⊓ Subgroup.centralizer (W : Set G) ≤ T)
    (hS : IsPGroup 2 ↥(T ⊓ L)) {D : Subgroup G} (hD : Odd (Nat.card D)) {δ : G} (hδ : δ ∈ D)
    (hδB : δ ∈ borelL T L) (h1 : borelChar hLW ψ hP ⟨δ, hδB⟩ = 1) : δ = 1 := by
  have h00 : (ψ (autHom hLW ⟨δ, hδB.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := congrArg Units.val h1
    rwa [coe_borelChar, Units.val_one] at this
  have hu := eq_unipSL_of_upper (borel_upper hLW ψ hP hδB) h00
  have hmem : ((autHom hLW ⟨δ, hδB.1⟩ : ↥(autOn L W)) : MulAut ↥W) ∈ autOn (T ⊓ L) W :=
    (hP _).mpr ⟨_, hu⟩
  obtain ⟨p, hp, hpc⟩ := mem_autOn_iff.mp hmem
  have hcent := inv_mul_mem_centralizer (W := W) (p := p) (c := ⟨δ, hLW hδB.1⟩) hpc
  have hpδL : ((p⁻¹ * ⟨δ, hLW hδB.1⟩ : Subgroup.normalizer (W : Set G)) : G) ∈ L := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact L.mul_mem (L.inv_mem hp.2) hδB.1
  have hT : ((p⁻¹ * ⟨δ, hLW hδB.1⟩ : Subgroup.normalizer (W : Set G)) : G) ∈ T :=
    hC ⟨hpδL, hcent⟩
  have hδT : δ ∈ T ⊓ L := by
    refine ⟨?_, hδB.1⟩
    have e : δ = (p : G) * ((p⁻¹ * ⟨δ, hLW hδB.1⟩ : Subgroup.normalizer (W : Set G)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact T.mul_mem hp.1 hT
  have hmem' : δ ∈ (T ⊓ L) ⊓ D := ⟨hδT, hδ⟩
  rw [inf_eq_bot_of_odd_of_isPGroup hS hD] at hmem'
  exact (Subgroup.mem_bot).mp hmem'

theorem exists_borelChar_conj [Finite F] {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTW : T ≤ Subgroup.normalizer (W : Set G))
    {t : G} (ht : t ∈ T) :
    ∃ σ : RingAut F, ∀ (b : G) (hb : b ∈ borelL T L) (hb' : t * b * t⁻¹ ∈ borelL T L),
      (borelChar hLW ψ hP ⟨t * b * t⁻¹, hb'⟩ : F) = σ (borelChar hLW ψ hP ⟨b, hb⟩ : F) := by
  set τ : Subgroup.normalizer ((autOn L W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    ⟨conjAct W ⟨t, hTW ht⟩, conjAct_mem_normalizer_autOn ⟨t, hTW ht⟩ (hTL ht)⟩ with hτ
  have hτP : (τ : MulAut ↥W) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) W : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    conjAct_mem_normalizer_autOn ⟨t, hTW ht⟩
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTL ht⟩)
  obtain ⟨h, σ, hh, hασ, -⟩ := exists_upper_of_normalizes hn hcard ψ hP τ hτP
  refine ⟨σ, fun b hb hb' => ?_⟩
  have hy : autHom hLW ⟨t * b * t⁻¹, hb'.1⟩ =
      (autOn L W).normalizerMonoidHom τ (autHom hLW ⟨b, hb.1⟩) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change conjAct W ⟨t * b * t⁻¹, _⟩ = conjAct W ⟨t, hTW ht⟩ * conjAct W ⟨b, _⟩ *
      (conjAct W ⟨t, hTW ht⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  show (ψ (autHom hLW ⟨t * b * t⁻¹, hb'.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 =
    σ ((ψ (autHom hLW ⟨b, hb.1⟩) : Matrix (Fin 2) (Fin 2) F) 0 0)
  rw [hy, hασ]
  exact (upper_conj_map σ hh (borel_upper hLW ψ hP hb)).2

include hLW ψ hP in
theorem card_le_inf_of_inverts [Finite G] [Finite F] [CharP F 2] {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    {D K Dm : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hDm : Dm ≤ D)
    (hDme : ∀ x ∈ Dm, x ^ (2 ^ m + 1) = 1) {t d : G} (ht : t ∈ T) (hd : d ∈ D) (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1) (htd : t * d * t⁻¹ = d⁻¹) (htK : t ∈ K)
    (hDmK : Dm ≤ Subgroup.normalizer (K : Set G))
    (hSK : T ⊓ L ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card Dm ≤ Nat.card ↥(D ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCL : L ⊓ Subgroup.centralizer (W : Set G) ≤ T := fun x hx =>
    hC ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  set B := borelL T L with hBdef
  set P := T ⊓ L with hPdef
  have hPB : P ≤ B := Hyp5_0_1.inf_le_borel T L
  have hBN : B ≤ Subgroup.normalizer (P : Set G) := inf_le_right
  have hSB : IsSylowTwoOf P B := A4.isSylowTwoOf_mono hS hPB inf_le_left
  have hP2 : IsPGroup 2 P := hS.2.1
  have hDodd : Odd (Nat.card D) := hD.2.1
  have hDB : D ≤ B := hD.1
  have hBodd : Odd (P.relIndex B) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSB.2.2)
  have hBDP : P ⊔ D = B := by
    rw [sup_comm]
    exact sup_eq_of_isHall_isSylow hD hSB
  have hPt : t ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTL ht⟩
  have hconjB : ∀ b ∈ B, t * b * t⁻¹ ∈ B := fun b hb =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hTL ht) b).mp hb.1, Subgroup.mul_mem _
      (Subgroup.mul_mem _ hPt hb.2) (Subgroup.inv_mem _ hPt)⟩
  have hn : 1 ≤ 2 * m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have := Finite.one_lt_card (α := F)
      rw [hcard] at this
      norm_num at this
    · omega
  obtain ⟨σ, hσ⟩ := exists_borelChar_conj hLW ψ hP hn hcard hTL hTW ht
  obtain ⟨j, hj⟩ := exists_eq_pow_two_pow hcard σ
  have hσc : ∀ (b : G) (hb : b ∈ B) (hb' : t * b * t⁻¹ ∈ B),
      borelChar hLW ψ hP ⟨t * b * t⁻¹, hb'⟩ = borelChar hLW ψ hP ⟨b, hb⟩ ^ 2 ^ j :=
    fun b hb hb' => by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hσ b hb hb', hj]
  have hχ1 : ∀ (s : G) (hs : s ∈ P) (hsB : s ∈ B), borelChar hLW ψ hP ⟨s, hsB⟩ = 1 :=
    fun s hs hsB => borelChar_eq_one hLW ψ hP hs hsB
  have hχinj : ∀ δ ∈ D, ∀ (hδB : δ ∈ B), borelChar hLW ψ hP ⟨δ, hδB⟩ = 1 → δ = 1 :=
    fun δ hδ hδB h1 => eq_one_of_borelChar hLW ψ hP hCL hP2 hDodd hδ hδB h1
  set χ := borelChar hLW ψ hP with hχ
  have hdB : d ∈ B := hDB hd
  have hjodd : Odd j := by
    have hc1 : χ ⟨d, hdB⟩ ≠ 1 := fun h1 => hd1 (hχinj d hd hdB h1)
    have hc3 : χ ⟨d, hdB⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have e : (⟨d, hdB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [e, map_one]
    have hcinv : χ ⟨t * d * t⁻¹, hconjB d hdB⟩ = χ ⟨d, hdB⟩ ^ 2 := by
      have e : (⟨t * d * t⁻¹, hconjB d hdB⟩ : ↥B) = (⟨d, hdB⟩ : ↥B)⁻¹ := Subtype.ext htd
      rw [e, map_inv]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hc3)
    have h1 := hσc d hdB (hconjB d hdB)
    rw [hcinv] at h1
    exact odd_of_pow_two_pow_eq_sq hc3 hc1 h1.symm
  set Q := K ⊓ B with hQdef
  have hQB : Q ≤ B := inf_le_right
  have hQK : Q ≤ K := inf_le_left
  set P' := P ⊓ Q with hP'def
  have hP'Q : P' ≤ Q := inf_le_right
  have hQN : Q ≤ Subgroup.normalizer (P' : Set G) := fun _ hq =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hBN (hQB hq), Subgroup.le_normalizer hq⟩
  have hPQodd : Odd (P.relIndex Q) := by
    have h1 : P.relIndex (Q ⊔ P) = P.relIndex Q := by
      have hA := hQB.trans hBN
      have := Subgroup.normal_subgroupOf_of_le_normalizer hA
      have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
      exact Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient Q P hA).toEquiv.symm
    have h2 := Subgroup.relIndex_mul_relIndex P (Q ⊔ P) B le_sup_right (sup_le hQB hPB)
    rw [← h1]
    exact hBodd.of_dvd_nat (Dvd.intro _ h2)
  have hP'relQ : P'.relIndex Q = P.relIndex Q := Subgroup.inf_relIndex_right P Q
  have hcop : Nat.Coprime (Nat.card P') (P'.relIndex Q) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hP2.to_le (inf_le_left : P' ≤ P))
    rw [hk, hP'relQ]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hPQodd)
  obtain ⟨E, hEQ, -, hP'E, hEcard, -⟩ := exists_complement_of_coprime hP'Q hQN hcop
  have hEodd : Odd (Nat.card E) := by
    rw [hEcard, hP'relQ]
    exact hPQodd
  set Y₀ := P ⊔ E with hY₀
  have hEB : E ≤ B := hEQ.trans hQB
  have hY₀B : Y₀ ≤ B := sup_le hPB hEB
  have hY₀odd : Odd (P.relIndex Y₀) := by
    have h2 := Subgroup.relIndex_mul_relIndex P Y₀ B le_sup_left hY₀B
    exact hBodd.of_dvd_nat (Dvd.intro _ h2)
  have hPE : P ⊓ E = ⊥ := inf_eq_bot_of_odd_of_isPGroup hP2 hEodd
  have hPD1 : P ⊓ (D ⊓ Y₀) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [← inf_eq_bot_of_odd_of_isPGroup hP2 hDodd]
    exact ⟨hy.1, hy.2.1⟩
  have hPD2 : P ⊔ (D ⊓ Y₀) = Y₀ := by
    apply le_antisymm (sup_le le_sup_left inf_le_right)
    have h1 := inf_sup_le_sup_inf (le_sup_left : P ≤ Y₀) (hDB.trans hBN)
    rw [hBDP, inf_eq_left.mpr hY₀B] at h1
    rw [inf_comm]
    exact h1
  obtain ⟨x, hxP, hEx⟩ := exists_mem_conj_of_complements (le_sup_left : P ≤ Y₀) (hY₀B.trans hBN)
    hP2 hY₀odd inf_le_right hPD1 hPD2 (le_sup_right : E ≤ Y₀) hPE rfl
  have hE1K : D ⊓ Y₀ ≤ D ⊓ K := by
    intro e he
    refine ⟨he.1, ?_⟩
    have hxe : x * e * x⁻¹ ∈ E := by
      rw [hEx]
      exact ⟨e, he, rfl⟩
    have h2 : x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hSK (P.inv_mem hxP)) _).mp (hQK (hEQ hxe))
    have e2 : x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ = e := by group
    rwa [e2] at h2
  have hDmB : ∀ z ∈ Dm, z ∈ B := fun z hz => hDB (hDm hz)
  have hkey : ∀ z : ↥Dm, ∃ e : ↥(D ⊓ K), χ ⟨e, hDB e.2.1⟩ =
      χ ⟨z, hDmB z z.2⟩ ^ 2 ^ j * (χ ⟨z, hDmB z z.2⟩)⁻¹ := by
    rintro ⟨z, hz⟩
    have hzB := hDmB z hz
    have hkB : t * z * t⁻¹ * z⁻¹ ∈ B := B.mul_mem (hconjB z hzB) (B.inv_mem hzB)
    have hkK : t * z * t⁻¹ * z⁻¹ ∈ K := by
      have h1 : z * t⁻¹ * z⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hDmK hz) _).mp (K.inv_mem htK)
      have e : t * z * t⁻¹ * z⁻¹ = t * (z * t⁻¹ * z⁻¹) := by group
      rw [e]
      exact K.mul_mem htK h1
    have hχk : χ ⟨t * z * t⁻¹ * z⁻¹, hkB⟩ = χ ⟨z, hzB⟩ ^ 2 ^ j * (χ ⟨z, hzB⟩)⁻¹ := by
      have e : (⟨t * z * t⁻¹ * z⁻¹, hkB⟩ : ↥B) =
          ⟨t * z * t⁻¹, hconjB z hzB⟩ * (⟨z, hzB⟩ : ↥B)⁻¹ := rfl
      rw [e, map_mul, map_inv, hσc z hzB (hconjB z hzB)]
    have hk' : t * z * t⁻¹ * z⁻¹ ∈ ((P' ⊔ E : Subgroup G) : Set G) := by
      rw [hP'E]
      exact ⟨hkK, hkB⟩
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P' E (hEQ.trans hQN)] at hk'
    obtain ⟨p, hp, e', he', hpe⟩ := hk'
    rw [hEx] at he'
    obtain ⟨e, he, hee⟩ := he'
    refine ⟨⟨e, hE1K he⟩, ?_⟩
    show χ ⟨e, hDB (hE1K he).1⟩ = χ ⟨z, hzB⟩ ^ 2 ^ j * (χ ⟨z, hzB⟩)⁻¹
    rw [← hχk]
    have hpB : p ∈ B := hPB hp.1
    have hxB : x ∈ B := hPB hxP
    have heB : e ∈ B := hDB he.1
    have e2 : (⟨t * z * t⁻¹ * z⁻¹, hkB⟩ : ↥B) =
        ⟨p, hpB⟩ * (⟨x, hxB⟩ * ⟨e, heB⟩ * (⟨x, hxB⟩ : ↥B)⁻¹) := by
      apply Subtype.ext
      show t * z * t⁻¹ * z⁻¹ = p * (x * e * x⁻¹)
      rw [← hpe, ← hee]
      simp [MulAut.conj_apply]
    rw [e2, map_mul, map_mul, map_mul, map_inv, hχ1 p hp.1 hpB, hχ1 x hxP hxB]
    simp
  choose f hf using hkey
  refine Nat.card_le_card_of_injective f fun z z' hzz' => ?_
  have hzz : χ ⟨z, hDmB z z.2⟩ ^ 2 ^ j * (χ ⟨z, hDmB z z.2⟩)⁻¹ =
      χ ⟨z', hDmB z' z'.2⟩ ^ 2 ^ j * (χ ⟨z', hDmB z' z'.2⟩)⁻¹ := by
    rw [← hf z, ← hf z', hzz']
  have hwDm : (z : G) * (z' : G)⁻¹ ∈ Dm := Dm.mul_mem z.2 (Dm.inv_mem z'.2)
  have hwB := hDmB _ hwDm
  have hχw : χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ = χ ⟨z, hDmB z z.2⟩ * (χ ⟨z', hDmB z' z'.2⟩)⁻¹ := by
    have e : (⟨(z : G) * (z' : G)⁻¹, hwB⟩ : ↥B) =
        ⟨z, hDmB z z.2⟩ * (⟨z', hDmB z' z'.2⟩ : ↥B)⁻¹ := rfl
    rw [e, map_mul, map_inv]
  have hfix : χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ ^ 2 ^ j = χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ := by
    rw [hχw, ← div_eq_mul_inv, div_pow, div_eq_div_iff_mul_eq_mul]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at hzz
    rw [hzz, mul_comm]
  have hw1 : (χ ⟨(z : G) * (z' : G)⁻¹, hwB⟩ : F) = 1 := by
    refine eq_one_of_pow_add_one hcard hjodd ?_ ?_
    · rw [← Units.val_pow_eq_pow_val, ← map_pow]
      have e : (⟨(z : G) * (z' : G)⁻¹, hwB⟩ : ↥B) ^ (2 ^ m + 1) = 1 :=
        Subtype.ext (by simpa using hDme _ hwDm)
      rw [e, map_one, Units.val_one]
    · rw [← Units.val_pow_eq_pow_val, hfix]
  have hw : (z : G) * (z' : G)⁻¹ = 1 :=
    hχinj _ (hDm hwDm) hwB (Units.ext (by rw [hw1, Units.val_one]))
  exact Subtype.ext (mul_inv_eq_one.mp hw)

include hLW ψ hP in
theorem card_hall_eq_card_units [Finite G] [Finite F]
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    Nat.card D = Nat.card Fˣ := by
  have hCL : L ⊓ Subgroup.centralizer (W : Set G) ≤ T := fun x hx =>
    hC ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  refine Nat.card_eq_of_bijective ((borelChar hLW ψ hP).comp (Subgroup.inclusion hD.1))
    ⟨?_, fun u => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (eq_one_of_borelChar hLW ψ hP hCL hS.2.1 hD.2.1 y.2 (hD.1 y.2) hy)
  · obtain ⟨δ, hδ, hδu⟩ := exists_mem_D_of_sylow hLW ψ hP hC hS hD u.ne_zero
    exact ⟨⟨δ, hδ⟩, Units.ext hδu⟩

include hLW ψ hP in
theorem exists_dMinus [Finite G] [Finite F] [CharP F 2] {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m)) (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T)
    (hS : IsSylowTwoOf (T ⊓ L) L) {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    ∃ Dm : Subgroup G, Dm ≤ D ∧ Nat.card Dm = 2 ^ m + 1 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have := Finite.one_lt_card (α := F)
      rw [hcard] at this
      norm_num at this
    · exact h0
  have h2m : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hcardU : Nat.card Fˣ = (2 ^ m - 1) * (2 ^ m + 1) := by
    rw [Nat.card_units, hcard, two_mul, pow_add]
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ m = r + 1 := ⟨2 ^ m - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel]
    have e : (r + 1) * (r + 1) = r * (r + 1 + 1) + 1 := by ring
    rw [e, Nat.add_sub_cancel]
  obtain ⟨g, hg⟩ : ∃ g : Fˣ, orderOf g = Nat.card Fˣ := IsCyclic.exists_ofOrder_eq_natCard
  have hu : orderOf (g ^ (2 ^ m - 1)) = 2 ^ m + 1 := by
    rw [orderOf_pow_of_dvd (by omega) (by rw [hg, hcardU]; exact Dvd.intro _ rfl), hg, hcardU]
    exact Nat.mul_div_cancel_left _ (by omega)
  obtain ⟨δ, hδ, hδu⟩ := exists_mem_D_of_sylow hLW ψ hP hC hS hD (g ^ (2 ^ m - 1)).ne_zero
  have hCL : L ⊓ Subgroup.centralizer (W : Set G) ≤ T := fun x hx =>
    hC ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have hinj : Function.Injective ((borelChar hLW ψ hP).comp (Subgroup.inclusion hD.1)) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (eq_one_of_borelChar hLW ψ hP hCL hS.2.1 hD.2.1 y.2 (hD.1 y.2) hy)
  have hχδ : (borelChar hLW ψ hP).comp (Subgroup.inclusion hD.1) ⟨δ, hδ⟩ = g ^ (2 ^ m - 1) :=
    Units.ext hδu
  have hord : orderOf δ = 2 ^ m + 1 := by
    have h1 := orderOf_injective _ hinj ⟨δ, hδ⟩
    rw [hχδ, hu, Subgroup.orderOf_mk] at h1
    exact h1.symm
  refine ⟨Subgroup.zpowers δ, (Subgroup.zpowers_le).mpr hδ, ?_⟩
  rw [Nat.card_zpowers, hord]

include hLW ψ hP in
theorem le_one_of_dMinus [Finite G] [Finite F] [CharP F 2] {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hC : (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T) (hS : IsSylowTwoOf (T ⊓ L) L)
    {D K Dm D₃ : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hDm : Dm ≤ D)
    (hDmc : Nat.card Dm = 2 ^ m + 1) {t d : G} (ht : t ∈ T) (hd : d ∈ D) (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1) (htd : t * d * t⁻¹ = d⁻¹) (htK : t ∈ K)
    (hDmK : Dm ≤ Subgroup.normalizer (K : Set G))
    (hSK : T ⊓ L ≤ Subgroup.normalizer (K : Set G)) (hDK : D ⊓ K ≤ D₃)
    (hD₃ : Nat.card D₃ = 3) : m ≤ 1 := by
  have hDme : ∀ x ∈ Dm, x ^ (2 ^ m + 1) = 1 := fun x hx => by
    have h1 : (⟨x, hx⟩ : ↥Dm) ^ Nat.card Dm = 1 := pow_card_eq_one'
    rw [hDmc] at h1
    simpa using congrArg Subtype.val h1
  have h1 := card_le_inf_of_inverts hLW ψ hP hcard hTL hTW hC hS hD hDm hDme ht hd hd1 hd3 htd
    htK hDmK hSK
  have h2 := Subgroup.card_le_of_le hDK
  rw [hDmc] at h1
  rw [hD₃] at h2
  have h3 : 2 ^ m + 1 ≤ 3 := h1.trans h2
  by_contra hm
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Char

end CFSG.Quasithin.H13
