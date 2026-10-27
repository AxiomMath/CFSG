module

public import CFSG.RankThree.PartOne.SEITZ2.G2F2Rad
public import CFSG.RankThree.PartOne.SEITZ6.G2Tor

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
open scoped commutatorElement Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem ordProd_commute_x7 (c : ℕ → K) (d : K) : Commute (ordProd c) (xp 7 d) := by
  unfold ordProd
  exact (((((commute_07 _ d).mul_left (commute_17 _ d)).mul_left (commute_47 _ d)).mul_left
    (commute_87 _ d)).mul_left (commute_37 _ d)).mul_left (commute_xp_same 7 _ d)

theorem conj_x8 (c : ℕ → K) (d : K) :
    ordProd c * xp 8 d * (ordProd c)⁻¹ =
      xp 8 d * (xp 3 (c 1 * d) * xp 7 ((c 4 + c 0 * c 1) * d)) := by
  rw [ordProd_inv]
  unfold ordProd
  g2coll
  have e4 : c 1 * c 0 + (c 4 + (c 1 * c 0 + c 4)) = 0 := by char2
  rw [e4, xp_zero, one_mul]
  congr 1
  · congr 1; char2
  · congr 1
    · congr 1; char2
    · congr 1; char2

omit [CharP K 2] in
theorem rf_e1_8 : reflect .G2 e1 (rt 8) = rt 4 := by decide +kernel

omit [CharP K 2] in
theorem rf_e1_7 : reflect .G2 e1 (rt 7) = rt 7 := by decide +kernel

omit [CharP K 2] in
theorem rf_e1_10 : reflect .G2 e1 (rt 10) = rt 10 := by decide +kernel

omit [CharP K 2] in
theorem rf_e1_6 : reflect .G2 e1 (rt 6) = rt 2 := by decide +kernel

omit [CharP K 2] in
theorem rf_e0_2 : reflect .G2 e0 (rt 2) = rt 0 := by decide +kernel

theorem n1_conj_ordProd (c : ℕ → K) (hc1 : c 1 = 0) :
    weylElement .G2 K e1 * ordProd c * (weylElement .G2 K e1)⁻¹ =
      ordProd (mk6 (c 3) 0 (c 8) (c 4) (c 0) (c 7 + c 4 * c 8 + c 0 * c 3)) := by
  have h0 : reflect .G2 e1 (rt 0) = rt 3 := reflect_0'
  have h4 : reflect .G2 e1 (rt 4) = rt 8 := reflect_4
  have h8 : reflect .G2 e1 (rt 8) = rt 4 := rf_e1_8
  have h3 : reflect .G2 e1 (rt 3) = rt 0 := reflect_3
  have h7 : reflect .G2 e1 (rt 7) = rt 7 := rf_e1_7
  have e : ordProd c = xp 0 (c 0) * xp 4 (c 4) * xp 8 (c 8) * xp 3 (c 3) * xp 7 (c 7) := by
    simp only [ordProd, hc1, xp_zero, mul_one]
  rw [e]
  simp only [conj_mul_eq, weylElement_conj_xp e1 (by norm_num) h0,
    weylElement_conj_xp e1 (by norm_num) h4, weylElement_conj_xp e1 (by norm_num) h8,
    weylElement_conj_xp e1 (by norm_num) h3, weylElement_conj_xp e1 (by norm_num) h7]
  rw [ordProd_mk6]
  g2coll
  rw [show c 3 * c 0 + c 8 * c 4 + c 7 = c 7 + c 4 * c 8 + c 0 * c 3 by ring]

theorem ordProd_split (c : ℕ → K) :
    ordProd c = ordProd (mk6 (c 0) 0 (c 4) (c 8) (c 3 + c 1 ^ 2 * c 4 + c 1 * c 8)
      (c 7 + c 1 * c 4 ^ 2)) * xp 1 (c 1) := by
  rw [ordProd_mk6]
  unfold ordProd
  g2coll
  have e3 : c 1 ^ 2 * c 4 + (c 1 * c 8 + (c 3 + c 1 ^ 2 * c 4 + c 1 * c 8)) = c 3 := by char2
  have e7 : c 1 * c 4 ^ 2 + (c 7 + c 1 * c 4 ^ 2) = c 7 := by char2
  rw [e3, e7]

omit [CharP K 2] in
theorem torus_conj_ordProd {t : adjointGroup .G2 K} (ht : t ∈ Tg K) :
    ∃ m0 m1 m4 m8 m3 m7 : K, ∀ c : ℕ → K, t * ordProd c * t⁻¹ =
      ordProd (mk6 (m0 * c 0) (m1 * c 1) (m4 * c 4) (m8 * c 8) (m3 * c 3) (m7 * c 7)) := by
  obtain ⟨m0, -, h0⟩ := Tg_conj_xp ht (p := 0) (by norm_num)
  obtain ⟨m1, -, h1⟩ := Tg_conj_xp ht (p := 1) (by norm_num)
  obtain ⟨m4, -, h4⟩ := Tg_conj_xp ht (p := 4) (by norm_num)
  obtain ⟨m8, -, h8⟩ := Tg_conj_xp ht (p := 8) (by norm_num)
  obtain ⟨m3, -, h3⟩ := Tg_conj_xp ht (p := 3) (by norm_num)
  obtain ⟨m7, -, h7⟩ := Tg_conj_xp ht (p := 7) (by norm_num)
  refine ⟨m0, m1, m4, m8, m3, m7, fun c => ?_⟩
  rw [ordProd_mk6]
  unfold ordProd
  simp only [conj_mul_eq, h0, h1, h4, h8, h3, h7]

omit [CharP K 2] in
theorem torus_conj_xp10 (a b : Kˣ) (c : K) :
    (torusElement .G2 K e0 a * torusElement .G2 K e1 b) * xp 10 c *
      (torusElement .G2 K e0 a * torusElement .G2 K e1 b)⁻¹ =
        xp 10 (((a⁻¹ : Kˣ) : K) * c) := by
  rw [show torusElement .G2 K e0 a * torusElement .G2 K e1 b * xp 10 c *
      (torusElement .G2 K e0 a * torusElement .G2 K e1 b)⁻¹ =
      torusElement .G2 K e0 a * (torusElement .G2 K e1 b * xp 10 c *
        (torusElement .G2 K e1 b)⁻¹) * (torusElement .G2 K e0 a)⁻¹ by group,
    torusElement_conj_xp e1 (by norm_num), torusElement_conj_xp e0 (by norm_num)]
  have h0 : (∑ j, (Tag.G2).cartan e0 j * (rt 10) j) = -1 := by decide +kernel
  have h1 : (∑ j, (Tag.G2).cartan e1 j * (rt 10) j) = 0 := by decide +kernel
  rw [h0, h1]
  simp

theorem mem_of_conj_weyl {H : Subgroup (adjointGroup .G2 K)} (i : Fin (Tag.rank .G2)) {p q : ℕ}
    (hp : p < 12) (h : reflect .G2 i (rt p) = rt q) (hw : weylElement .G2 K i ∈ H) {c : K}
    (hc : xp p c ∈ H) : xp q c ∈ H := by
  have := H.mul_mem (H.mul_mem hw hc) (H.inv_mem hw)
  rwa [weylElement_conj_xp i hp h] at this

theorem comm_xp_6_7 (s t : K) : ⁅xp 6 s, xp 7 t⁆ = xp 0 (s * t) := by
  have h : RootOps.repCheck .G2 6 7 [(1, 1, 0, -1)] = true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  simp only [cast_neg_one_eq, one_mul] at this
  show _ = _
  rw [this]
  simp only [pow_one]

theorem x6_conj_x7 (c : K) : xp 6 1 * xp 7 c * (xp 6 1)⁻¹ = xp 0 c * xp 7 c := by
  have h := comm_xp_6_7 (K := K) 1 c
  rw [one_mul] at h
  rw [← h, commutatorElement_def]
  group

theorem commute_6_10 (x y : K) : Commute (xp 6 x) (xp 10 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

end CFSG.RankThree.PartOne.SEITZ2
