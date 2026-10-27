module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81Tools
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofE81U43Data
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res4.U43

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434RemU43

theorem toMat_conj_eq {g x : SUg} {cg cx cy : List ℕ} (hg : toMat g = dec4 cg)
    (hx : toMat x = dec4 cx) (h : mul4 cy cg = mul4 cg cx) : toMat (g * x * g⁻¹) = dec4 cy := by
  have h1 : toMat (g * x * g⁻¹) * toMat g = dec4 cy * toMat g := by
    rw [← map_mul, inv_mul_cancel_right, map_mul, hg, hx, ← dec4_mul4, ← h, dec4_mul4]
  have h2 : toMat g * toMat g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc toMat (g * x * g⁻¹) = toMat (g * x * g⁻¹) * (toMat g * toMat g⁻¹) := by
        rw [h2, mul_one]
    _ = (toMat (g * x * g⁻¹) * toMat g) * toMat g⁻¹ := (mul_assoc _ _ _).symm
    _ = (dec4 cy * toMat g) * toMat g⁻¹ := by rw [h1]
    _ = dec4 cy := by rw [mul_assoc, h2, mul_one]

theorem mul_ne_of_commutes4 {g x : SUg} {cg cx : List ℕ} (hg : toMat g = dec4 cg)
    (hx : toMat x = dec4 cx) (h : commutes4 cx cg = false) : x * g ≠ g * x := by
  intro hxg
  have h1 : dec4 (mul4 cx cg) = dec4 (mul4 cg cx) := by
    rw [dec4_mul4, dec4_mul4, ← hg, ← hx, ← map_mul, ← map_mul, hxg]
  have h2 := dec4_injective (canon4_mul4 _ _) (canon4_mul4 _ _) h1
  simp [commutes4, h2] at h

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {q q' r r' x : G} (h : q * r = q' * r')
    (hc : (r * r'⁻¹) * x = x * (r * r'⁻¹)) : q * x * q⁻¹ = q' * x * q'⁻¹ := by
  have hq : q' = q * (r * r'⁻¹) := by
    calc q' = q' * r' * r'⁻¹ := by group
      _ = q * r * r'⁻¹ := by rw [h]
      _ = q * (r * r'⁻¹) := by group
  rw [hq]
  calc q * x * q⁻¹ = q * (x * (r * r'⁻¹)) * (r * r'⁻¹)⁻¹ * q⁻¹ := by group
    _ = q * ((r * r'⁻¹) * x) * (r * r'⁻¹)⁻¹ * q⁻¹ := by rw [hc]
    _ = q * (r * r'⁻¹) * x * (q * (r * r'⁻¹))⁻¹ := by group

structure Data where
  x0 : SUg
  x1 : SUg
  x2 : SUg
  x3 : SUg
  g1 : SUg
  g2 : SUg
  t : SUg
  hx0 : toMat x0 = dec4 (cX 0)
  hx1 : toMat x1 = dec4 (cX 1)
  hx2 : toMat x2 = dec4 (cX 2)
  hx3 : toMat x3 = dec4 (cX 3)
  hg1 : toMat g1 = dec4 codeG1
  hg2 : toMat g2 = dec4 codeG2
  ht : toMat t = dec4 codeT
  hg1S : g1 ∈ sylS
  hg2S : g2 ∈ sylS
  hRS : Subgroup.closure ({x0, x1, x2, x3} : Set SUg) ≤ sylS
  hRe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({x0, x1, x2, x3} : Set SUg))
  hR81 : 81 ≤ Nat.card (Subgroup.closure ({x0, x1, x2, x3} : Set SUg))

namespace Data

variable (d : Data)

noncomputable def x (k : ℕ) : SUg := [d.x0, d.x1, d.x2, d.x3].getD k 1

theorem hx : ∀ k < 4, toMat (d.x k) = dec4 (cX k) := by
  intro k hk
  interval_cases k
  · exact d.hx0
  · exact d.hx1
  · exact d.hx2
  · exact d.hx3

noncomputable abbrev R : Subgroup SUg := Subgroup.closure ({d.x0, d.x1, d.x2, d.x3} : Set SUg)

theorem x_mem {k : ℕ} (hk : k < 4) : d.x k ∈ d.R := by
  apply Subgroup.subset_closure
  interval_cases k <;> simp [x]

theorem R_comm {a b : SUg} (ha : a ∈ d.R) (hb : b ∈ d.R) : a * b = b * a :=
  congrArg Subtype.val (d.hRe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem x_cube {k : ℕ} (hk : k < 4) : d.x k ^ 3 = 1 := d.hRe.2 _ (d.x_mem hk)

theorem card_R : Nat.card d.R = 81 := le_antisymm (card_closure_four_le d.hRe) d.hR81

noncomputable def xp (e : ℕ) : SUg :=
  d.x 0 ^ (e % 3) * d.x 1 ^ (e / 3 % 3) * d.x 2 ^ (e / 9 % 3) * d.x 3 ^ (e / 27 % 3)

theorem xp_mem (e : ℕ) : d.xp e ∈ d.R :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (d.x_mem (by norm_num)) _) (Subgroup.pow_mem _ (d.x_mem (by norm_num)) _))
    (Subgroup.pow_mem _ (d.x_mem (by norm_num)) _)) (Subgroup.pow_mem _ (d.x_mem (by norm_num)) _)

theorem toMat_xp (e : ℕ) : toMat (d.xp e) = dec4 (rtProdL e) := by
  rw [xp, rtProdL, map_mul, map_mul, map_mul,
    toMat_pow4 (d.hx 0 (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    toMat_pow4 (d.hx 1 (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    toMat_pow4 (d.hx 2 (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    toMat_pow4 (d.hx 3 (by norm_num)) (Nat.mod_lt _ (by norm_num)), dec4_mul4, dec4_mul4,
    dec4_mul4]

noncomputable def Q (a b : ℕ) : SUg := d.g1 ^ a * d.g2 ^ b

theorem toMat_Q {a b : ℕ} (ha : a < 3) (hb : b < 3) : toMat (d.Q a b) = dec4 (codeQ a b) := by
  rw [Q, map_mul, toMat_pow4 d.hg1 ha, toMat_pow4 d.hg2 hb, ← dec4_mul4]
  rfl

theorem Q_mem (a b : ℕ) : d.Q a b ∈ sylS :=
  sylS.mul_mem (sylS.pow_mem d.hg1S a) (sylS.pow_mem d.hg2S b)

theorem Q_zero : d.Q 0 0 = 1 := by simp [Q]

theorem toMat_conj_Q {a b : ℕ} (ha : a < 3) (hb : b < 3) :
    toMat (d.Q a b * d.x 0 * (d.Q a b)⁻¹) = dec4 (sig a b) :=
  toMat_conj_eq (d.toMat_Q ha hb) (d.hx 0 (by norm_num)) (sig_check a ha b hb)

theorem exists_coset (hsyl : uSylCheck = true) {t : SUg} (ht : t ∈ sylS) :
    ∃ a < 3, ∃ b < 3, ∃ r ∈ d.R, t = d.Q a b * r := by
  let f : Fin 3 × Fin 3 × d.R → sylS := fun p =>
    ⟨d.Q p.1 p.2.1 * p.2.2, sylS.mul_mem (d.Q_mem _ _) (d.hRS p.2.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b, r⟩ ⟨a', b', r'⟩ h
    have h' : d.Q a b * r = d.Q a' b' * r' := congrArg Subtype.val h
    have hs : (r : SUg) * (r' : SUg)⁻¹ ∈ d.R := d.R.mul_mem r.2 (d.R.inv_mem r'.2)
    have hconj : d.Q a b * d.x 0 * (d.Q a b)⁻¹ = d.Q a' b' * d.x 0 * (d.Q a' b')⁻¹ :=
      conj_eq_of_mul_eq h' (d.R_comm hs (d.x_mem (k := 0) (by norm_num)))
    have hsig : sig a b = sig a' b' := by
      refine dec4_injective (sig_canon a a.2 b b.2) (sig_canon a' a'.2 b' b'.2) ?_
      rw [← d.toMat_conj_Q a.2 b.2, ← d.toMat_conj_Q a'.2 b'.2, hconj]
    obtain ⟨haa, hbb⟩ := sig_inj a.2 b.2 a'.2 b'.2 hsig
    have ha : a = a' := Fin.ext haa
    have hb : b = b' := Fin.ext hbb
    subst ha hb
    have hr : (r : SUg) = r' := mul_left_cancel h'
    rw [Subtype.ext hr]
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    rw [Nat.card_prod, Nat.card_prod, Nat.card_fin, d.card_R, card_sylS hsyl]
  obtain ⟨⟨a, b, r⟩, hp⟩ := hbij.2 ⟨t, ht⟩
  exact ⟨a, a.2, b, b.2, r, r.2, (congrArg Subtype.val hp).symm⟩

theorem card_centralizer_Q_le {a b : ℕ} (ha : a < 3) (hb : b < 3) (hab : ¬ (a = 0 ∧ b = 0)) :
    Nat.card (d.R ⊓ Subgroup.centralizer ({d.Q a b} : Set SUg) : Subgroup SUg) ≤ 9 := by
  obtain ⟨m, hm⟩ : ∃ m, m = wIdx a b := ⟨_, rfl⟩
  have hm23 : m = 2 ∨ m = 3 := by
    rw [hm, wIdx]
    split_ifs <;> simp
  have hm4 : m < 4 := by rcases hm23 with h | h <;> omega
  obtain ⟨N, hN⟩ : ∃ N : Subgroup SUg, N = Subgroup.zpowers (d.x 0) ⊔ Subgroup.zpowers (d.x m) :=
    ⟨_, rfl⟩
  have hcm : d.x 0 * d.x m = d.x m * d.x 0 := d.R_comm (d.x_mem (by norm_num)) (d.x_mem hm4)
  have hNR : N ≤ d.R := hN ▸ sup_le (Subgroup.zpowers_le.mpr (d.x_mem (by norm_num)))
    (Subgroup.zpowers_le.mpr (d.x_mem hm4))
  have hcode : ∀ i < 3, ∀ j < 3,
      toMat (d.x 0 ^ i * d.x m ^ j) = dec4 (mul4 (pow4 (cX 0) i) (pow4 (cX m) j)) := by
    intro i hi j hj
    rw [map_mul, toMat_pow4 (d.hx 0 (by norm_num)) hi, toMat_pow4 (d.hx m hm4) hj, dec4_mul4]
  have hCN : (d.R ⊓ Subgroup.centralizer ({d.Q a b} : Set SUg)) ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨hn1, hnN⟩ := Subgroup.mem_inf.mp hn
    have hnc := (Subgroup.mem_inf.mp hn1).2
    rw [hN] at hnN
    rw [Subgroup.mem_bot]
    obtain ⟨i, hi, j, hj, rfl⟩ := exists_pow_of_mem_sup (d.x_cube (k := 0) (by norm_num))
      (d.x_cube hm4) hcm hnN
    by_contra hne
    have hij : ¬ (i = 0 ∧ j = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hne (by simp)
    have hwc : commutes4 (mul4 (pow4 (cX 0) i) (pow4 (cX m) j)) (codeQ a b) = false := by
      rw [hm]
      exact w_check ha hb hab hi hj hij
    exact mul_ne_of_commutes4 (d.toMat_Q ha hb) (hcode i hi j hj) hwc
      (Subgroup.mem_centralizer_singleton_iff.mp hnc)
  have hN9 : 9 ≤ Nat.card N := by
    have hmemN : ∀ p : Fin 3 × Fin 3, d.x 0 ^ (p.1 : ℕ) * d.x m ^ (p.2 : ℕ) ∈ N := by
      intro p
      rw [hN]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers _)) _) (Subgroup.pow_mem _ (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers _)) _)
    let f : Fin 3 × Fin 3 → N := fun p => ⟨d.x 0 ^ (p.1 : ℕ) * d.x m ^ (p.2 : ℕ), hmemN p⟩
    have hf : Function.Injective f := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h' : d.x 0 ^ (i : ℕ) * d.x m ^ (j : ℕ) = d.x 0 ^ (i' : ℕ) * d.x m ^ (j' : ℕ) :=
        congrArg Subtype.val h
      have hc : mul4 (pow4 (cX 0) i) (pow4 (cX m) j) = mul4 (pow4 (cX 0) i') (pow4 (cX m) j') :=
        dec4_injective (canon4_mul4 _ _) (canon4_mul4 _ _)
          (by rw [← hcode i i.2 j j.2, ← hcode i' i'.2 j' j'.2, h'])
      obtain ⟨hi, hj⟩ := dist2 hm23 i.2 j.2 i'.2 j'.2 hc
      rw [Fin.ext hi, Fin.ext hj]
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_fin] at this
  have hle : Nat.card (d.R ⊓ Subgroup.centralizer ({d.Q a b} : Set SUg) : Subgroup SUg) *
      Nat.card N ≤ Nat.card d.R := card_mul_card_le inf_le_left hNR hCN
  rw [d.card_R] at hle
  by_contra hgt
  push Not at hgt
  have := Nat.mul_le_mul hgt hN9
  omega

theorem card_centralizer_le (hsyl : uSylCheck = true) {t : SUg} (ht : t ∈ sylS) (htR : t ∉ d.R) :
    Nat.card (d.R ⊓ Subgroup.centralizer ({t} : Set SUg) : Subgroup SUg) ≤ 9 := by
  obtain ⟨a, ha, b, hb, r, hr, rfl⟩ := d.exists_coset hsyl ht
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    apply htR
    rw [d.Q_zero, one_mul]
    exact hr
  have heq : d.R ⊓ Subgroup.centralizer ({d.Q a b * r} : Set SUg) =
      d.R ⊓ Subgroup.centralizer ({d.Q a b} : Set SUg) := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hy, hyc⟩
      refine ⟨hy, ?_⟩
      have hry := d.R_comm hr hy
      calc y * d.Q a b = y * (d.Q a b * r) * r⁻¹ := by group
        _ = d.Q a b * r * y * r⁻¹ := by rw [hyc]
        _ = d.Q a b * (r * y) * r⁻¹ := by group
        _ = d.Q a b * (y * r) * r⁻¹ := by rw [hry]
        _ = d.Q a b * y := by group
    · rintro ⟨hy, hyc⟩
      refine ⟨hy, ?_⟩
      have hry := d.R_comm hr hy
      calc y * (d.Q a b * r) = d.Q a b * y * r := by rw [← mul_assoc, hyc]
        _ = d.Q a b * (y * r) := by group
        _ = d.Q a b * (r * y) := by rw [hry]
        _ = d.Q a b * r * y := by group
  rw [heq]
  exact d.card_centralizer_Q_le ha hb hab

include d in
theorem card_center_le (hsyl : uSylCheck = true) :
    Nat.card (sylS ⊓ Subgroup.centralizer (sylS : Set SUg) : Subgroup SUg) ≤ 3 := by
  obtain ⟨C, hC⟩ : ∃ C : Subgroup SUg, C = d.R ⊓ Subgroup.centralizer ({d.Q 1 0} : Set SUg) ⊓
      Subgroup.centralizer ({d.Q 0 1} : Set SUg) := ⟨_, rfl⟩
  have hZC : sylS ⊓ Subgroup.centralizer (sylS : Set SUg) ≤ C := by
    intro z hz
    obtain ⟨hzS, hzc⟩ := Subgroup.mem_inf.mp hz
    have hzR : z ∈ d.R := by
      by_contra hzR
      have hle := d.card_centralizer_le hsyl hzS hzR
      have hRle : d.R ≤ d.R ⊓ Subgroup.centralizer ({z} : Set SUg) := by
        refine le_inf le_rfl fun r hr => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hzc r (d.hRS hr)
      have := Subgroup.card_le_of_le hRle
      rw [d.card_R] at this
      omega
    rw [hC]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzR, ?_⟩, ?_⟩ <;>
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (Subgroup.mem_centralizer_iff.mp hzc _ (d.Q_mem 1 0)).symm
    · exact (Subgroup.mem_centralizer_iff.mp hzc _ (d.Q_mem 0 1)).symm
  obtain ⟨N, hN⟩ : ∃ N : Subgroup SUg,
      N = Subgroup.zpowers (d.x 0) ⊔ Subgroup.zpowers (d.x 2) ⊔ Subgroup.zpowers (d.x 3) :=
    ⟨_, rfl⟩
  have hNR : N ≤ d.R := hN ▸ sup_le (sup_le (Subgroup.zpowers_le.mpr (d.x_mem (by norm_num)))
    (Subgroup.zpowers_le.mpr (d.x_mem (by norm_num)))) (Subgroup.zpowers_le.mpr
      (d.x_mem (by norm_num)))
  have hcode : ∀ i < 3, ∀ j < 3, ∀ k < 3, toMat (d.x 0 ^ i * d.x 2 ^ j * d.x 3 ^ k) =
      dec4 (mul4 (mul4 (pow4 (cX 0) i) (pow4 (cX 2) j)) (pow4 (cX 3) k)) := by
    intro i hi j hj k hk
    rw [map_mul, map_mul, toMat_pow4 (d.hx 0 (by norm_num)) hi,
      toMat_pow4 (d.hx 2 (by norm_num)) hj, toMat_pow4 (d.hx 3 (by norm_num)) hk, dec4_mul4,
      dec4_mul4]
  have hc02 := d.R_comm (d.x_mem (k := 0) (by norm_num)) (d.x_mem (k := 2) (by norm_num))
  have hc03 := d.R_comm (d.x_mem (k := 0) (by norm_num)) (d.x_mem (k := 3) (by norm_num))
  have hc23 := d.R_comm (d.x_mem (k := 2) (by norm_num)) (d.x_mem (k := 3) (by norm_num))
  have hCN : C ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨hnC, hnN⟩ := Subgroup.mem_inf.mp hn
    rw [hC] at hnC
    obtain ⟨hnC', hn2⟩ := Subgroup.mem_inf.mp hnC
    have hn1 := (Subgroup.mem_inf.mp hnC').2
    rw [hN] at hnN
    rw [Subgroup.mem_bot]
    obtain ⟨i, hi, j, hj, k, hk, rfl⟩ := exists_pow_of_mem_sup3
      (d.x_cube (k := 0) (by norm_num)) (d.x_cube (k := 2) (by norm_num))
      (d.x_cube (k := 3) (by norm_num)) hc02 hc03 hc23 hnN
    by_contra hne
    have hijk : ¬ (i = 0 ∧ j = 0 ∧ k = 0) := by
      rintro ⟨rfl, rfl, rfl⟩
      exact hne (by simp)
    have hz := z_check i hi j hj k hk hijk
    rw [Bool.and_eq_false_iff] at hz
    rcases hz with hz | hz
    · exact mul_ne_of_commutes4 (d.toMat_Q (by norm_num) (by norm_num)) (hcode i hi j hj k hk) hz
        (Subgroup.mem_centralizer_singleton_iff.mp hn1)
    · exact mul_ne_of_commutes4 (d.toMat_Q (by norm_num) (by norm_num)) (hcode i hi j hj k hk) hz
        (Subgroup.mem_centralizer_singleton_iff.mp hn2)
  have hN27 : 27 ≤ Nat.card N := by
    have hmemN : ∀ p : Fin 3 × Fin 3 × Fin 3,
        d.x 0 ^ (p.1 : ℕ) * d.x 2 ^ (p.2.1 : ℕ) * d.x 3 ^ (p.2.2 : ℕ) ∈ N := by
      intro p
      rw [hN]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
          (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left
            (Subgroup.mem_zpowers _))) _)
          (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
            (Subgroup.mem_zpowers _))) _))
          (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
    let f : Fin 3 × Fin 3 × Fin 3 → N := fun p =>
      ⟨d.x 0 ^ (p.1 : ℕ) * d.x 2 ^ (p.2.1 : ℕ) * d.x 3 ^ (p.2.2 : ℕ), hmemN p⟩
    have hf : Function.Injective f := by
      rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
      have h' : d.x 0 ^ (i : ℕ) * d.x 2 ^ (j : ℕ) * d.x 3 ^ (k : ℕ) =
          d.x 0 ^ (i' : ℕ) * d.x 2 ^ (j' : ℕ) * d.x 3 ^ (k' : ℕ) := congrArg Subtype.val h
      have hc : mul4 (mul4 (pow4 (cX 0) i) (pow4 (cX 2) j)) (pow4 (cX 3) k) =
          mul4 (mul4 (pow4 (cX 0) i') (pow4 (cX 2) j')) (pow4 (cX 3) k') :=
        dec4_injective (canon4_mul4 _ _) (canon4_mul4 _ _)
          (by rw [← hcode i i.2 j j.2 k k.2, ← hcode i' i'.2 j' j'.2 k' k'.2, h'])
      obtain ⟨hi, hj, hk⟩ := dist3 i.2 j.2 k.2 i'.2 j'.2 k'.2 hc
      rw [Fin.ext hi, Fin.ext hj, Fin.ext hk]
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_prod, Nat.card_fin] at this
  have hCR : C ≤ d.R := by
    rw [hC]
    exact inf_le_left.trans inf_le_left
  have hle : Nat.card C * Nat.card N ≤ Nat.card d.R := card_mul_card_le hCR hNR hCN
  rw [d.card_R] at hle
  have hC3 : Nat.card C ≤ 3 := by
    by_contra hgt
    push Not at hgt
    have := Nat.mul_le_mul hgt hN27
    omega
  exact (Subgroup.card_le_of_le hZC).trans hC3

theorem eq_R_of_le (hsyl : uSylCheck = true) {B : Subgroup SUg} (hBS : B ≤ sylS)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h81 : 81 ≤ Nat.card B) : B = d.R := by
  have hle := le_of_abelian_card_ge d.hRS (fun x hx y hy => d.R_comm hx hy) (card_sylS hsyl)
    d.card_R (fun t ht htR => d.card_centralizer_le hsyl ht htR) (d.card_center_le hsyl) hBS hBc
    h81
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_R]; exact h81)

theorem t_mem_normalizer : d.t ∈ Subgroup.normalizer (d.R : Set SUg) := by
  refine mem_normalizer_closure_of_conj_mem ?_
  have key : ∀ k < 4, d.t * d.x k * d.t⁻¹ ∈ d.R := by
    intro k hk
    have h := toMat_conj_eq d.ht (d.hx k hk) (img_check k hk)
    rw [← d.toMat_xp] at h
    rw [toMat_injective h]
    exact d.xp_mem _
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact key 0 (by norm_num)
  · exact key 1 (by norm_num)
  · exact key 2 (by norm_num)
  · exact key 3 (by norm_num)

noncomputable def eD : Fin 4 → SUg := ![d.xp 27, d.xp 13, d.xp 39, d.xp 46]

theorem closure_eD : Subgroup.closure (Set.range d.eD) = d.R := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> exact d.xp_mem _
  · rw [Subgroup.closure_le]
    have hm0 : d.xp 27 ∈ Subgroup.closure (Set.range d.eD) := Subgroup.subset_closure ⟨0, rfl⟩
    have hm1 : d.xp 13 ∈ Subgroup.closure (Set.range d.eD) := Subgroup.subset_closure ⟨1, rfl⟩
    have hm2 : d.xp 39 ∈ Subgroup.closure (Set.range d.eD) := Subgroup.subset_closure ⟨2, rfl⟩
    have hm3 : d.xp 46 ∈ Subgroup.closure (Set.range d.eD) := Subgroup.subset_closure ⟨3, rfl⟩
    have key : ∀ k < 4, d.x k ∈ Subgroup.closure (Set.range d.eD) := by
      intro k hk
      have hlt : ∀ i, xCoeff k i < 3 := by
        intro i
        interval_cases k <;> simp only [xCoeff] <;> rcases i with _ | _ | _ | _ | i <;> simp
      have hxk : d.x k = d.xp 27 ^ xCoeff k 0 * d.xp 13 ^ xCoeff k 1 * d.xp 39 ^ xCoeff k 2 *
          d.xp 46 ^ xCoeff k 3 := by
        have hb := basis_check k hk
        change cX k = mul4 (mul4 (mul4 (pow4 (rtProdL 27) (xCoeff k 0))
          (pow4 (rtProdL 13) (xCoeff k 1))) (pow4 (rtProdL 39) (xCoeff k 2)))
          (pow4 (rtProdL 46) (xCoeff k 3)) at hb
        apply toMat_injective
        rw [d.hx k hk, map_mul, map_mul, map_mul,
          toMat_pow4 (d.toMat_xp _) (hlt 0), toMat_pow4 (d.toMat_xp _) (hlt 1),
          toMat_pow4 (d.toMat_xp _) (hlt 2), toMat_pow4 (d.toMat_xp _) (hlt 3), ← dec4_mul4,
          ← dec4_mul4, ← dec4_mul4, ← hb]
      rw [hxk]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ hm0 _) (Subgroup.pow_mem _ hm1 _))
        (Subgroup.pow_mem _ hm2 _)) (Subgroup.pow_mem _ hm3 _)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact key 0 (by norm_num)
    · exact key 1 (by norm_num)
    · exact key 2 (by norm_num)
    · exact key 3 (by norm_num)

theorem conj_t_fix {e : ℕ} (h : mul4 (rtProdL e) codeT = mul4 codeT (rtProdL e)) :
    d.t * d.xp e * d.t⁻¹ = d.xp e := by
  have h' := toMat_conj_eq d.ht (d.toMat_xp e) h
  exact toMat_injective (by rw [h', d.toMat_xp])

theorem conj_t_inv {e : ℕ} (h : mul4 (sq4 (rtProdL e)) codeT = mul4 codeT (rtProdL e)) :
    d.t * d.xp e * d.t⁻¹ = (d.xp e)⁻¹ := by
  have h' := toMat_conj_eq d.ht (d.toMat_xp e) h
  have he3 : d.xp e ^ 3 = 1 := d.hRe.2 _ (d.xp_mem _)
  have hsq : (d.xp e)⁻¹ = d.xp e ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', he3]
  rw [hsq]
  apply toMat_injective
  rw [h', toMat_pow4 (d.toMat_xp e) (by norm_num : 2 < 3)]
  rfl

theorem card_R_inf_centralizer_t :
    Nat.card (d.R ⊓ Subgroup.centralizer ({d.t} : Set SUg) : Subgroup SUg) = 9 := by
  have h0 : d.t * d.eD 0 * d.t⁻¹ = d.eD 0 := d.conj_t_fix (diag_fix 0 (by norm_num))
  have h1 : d.t * d.eD 1 * d.t⁻¹ = d.eD 1 := d.conj_t_fix (diag_fix 1 (by norm_num))
  have h2 : d.t * d.eD 2 * d.t⁻¹ = (d.eD 2)⁻¹ := d.conj_t_inv (diag_inv 0 (by norm_num))
  have h3 : d.t * d.eD 3 * d.t⁻¹ = (d.eD 3)⁻¹ := d.conj_t_inv (diag_inv 1 (by norm_num))
  have hDe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure (Set.range d.eD)) := by
    rw [d.closure_eD]
    exact d.hRe
  have h81 : 81 ≤ Nat.card (Subgroup.closure (Set.range d.eD)) := by
    rw [d.closure_eD]
    exact d.hR81
  have := card_inf_centralizer_eq_nine hDe h81 h0 h1 h2 h3
  rwa [d.closure_eD] at this

theorem piU_t_sq : piU d.t ^ 2 = 1 := by
  rw [← map_pow, piU_eq_one_iff]
  refine ⟨-1, ?_⟩
  apply Units.ext
  have h : toMat (d.t ^ 2) = dec4 codeNegOne := by
    rw [pow_two, map_mul, d.ht, ← dec4_mul4, codeT_sq]
  rw [toMat_apply] at h
  rw [h, Matrix.GeneralLinearGroup.coe_scalar, dec4_negOne, Units.val_neg, Units.val_one]

theorem piU_t_ne_one : piU d.t ≠ 1 := by
  rw [Ne, piU_eq_one_iff]
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL (Fin 4) CFSG.LieType.Multipliers.U43.F9 =>
    (g : Matrix (Fin 4) (Fin 4) CFSG.LieType.Multipliers.U43.F9) 0 1) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at h
  have h2 : ((d.t : GL (Fin 4) CFSG.LieType.Multipliers.U43.F9) :
      Matrix (Fin 4) (Fin 4) CFSG.LieType.Multipliers.U43.F9) 0 1 = dec4 codeT 0 1 := by
    rw [← toMat_apply, d.ht]
  rw [← h, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at h2
  exact dec4_codeT_01 h2.symm

include d in
theorem e81InvAt_UX (hsyl : uSylCheck = true) : E81InvAt UX := by
  obtain ⟨D, hD⟩ : ∃ D : Subgroup UX, D = d.R.map piU := ⟨_, rfl⟩
  have hinj : ∀ x ∈ d.R, ∀ y ∈ d.R, piU x = piU y → x = y := fun x hx y hy h =>
    piU_injOn_sylS hsyl (d.hRS hx) (d.hRS hy) h
  have htN : piU d.t ∈ Subgroup.normalizer (D : Set UX) :=
    hD ▸ Subgroup.le_normalizer_map piU ⟨d.t, d.t_mem_normalizer, rfl⟩
  have htC : Nat.card (D ⊓ Subgroup.centralizer {piU d.t} : Subgroup UX) = 9 := by
    have heq : D ⊓ Subgroup.centralizer {piU d.t} =
        (d.R ⊓ Subgroup.centralizer ({d.t} : Set SUg)).map piU := by
      apply le_antisymm
      · intro y hy
        obtain ⟨hyD, hyc⟩ := Subgroup.mem_inf.mp hy
        rw [hD] at hyD
        obtain ⟨r, hr, rfl⟩ := hyD
        refine ⟨r, Subgroup.mem_inf.mpr ⟨hr, ?_⟩, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
        have hTr : d.t⁻¹ * r * d.t ∈ d.R := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ d.t_mem_normalizer) r).mp hr
          simpa using this
        have hpi : piU (d.t⁻¹ * r * d.t) = piU r := by
          rw [map_mul, map_mul, map_inv]
          calc (piU d.t)⁻¹ * piU r * piU d.t = (piU d.t)⁻¹ * (piU r * piU d.t) := by group
            _ = (piU d.t)⁻¹ * (piU d.t * piU r) := by rw [hyc]
            _ = piU r := by group
        have h3 : d.t⁻¹ * r * d.t = r := hinj _ hTr _ hr hpi
        calc r * d.t = d.t * (d.t⁻¹ * r * d.t) := by group
          _ = d.t * r := by rw [h3]
      · rintro _ ⟨r, hr', rfl⟩
        obtain ⟨hr, hrc⟩ := Subgroup.mem_inf.mp hr'
        refine Subgroup.mem_inf.mpr ⟨hD ▸ ⟨r, hr, rfl⟩, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hrc ⊢
        rw [← map_mul, ← map_mul, hrc]
    rw [heq, card_map_piU_of_le hsyl ((inf_le_left).trans d.hRS), d.card_R_inf_centralizer_t]
  intro B hB h81
  obtain ⟨g, Pt, hPt, hPte, hPtn, hmap⟩ := exists_conj_elemAbelian hsyl hB rfl
  have hPtR : Pt = d.R := d.eq_R_of_le hsyl hPt
    (fun x hx y hy => congrArg Subtype.val (hPte.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (hPtn ▸ h81)
  rw [hPtR, ← hD] at hmap
  have hBeq : B = D.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hmap, Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hBeq]
  exact exists_inv_of_map_conj g⁻¹ htN d.piU_t_ne_one d.piU_t_sq htC

end Data

noncomputable def hLift (j : ℕ) : SUg := wordElem (uLiftG.getD j [])

noncomputable def data (hsyl : uSylCheck = true) (hrt : uRtCheck = true) : Data where
  x0 := sAt (uLiftBasis.getD 0 0)
  x1 := sAt (uLiftBasis.getD 1 0)
  x2 := sAt (uLiftBasis.getD 2 0)
  x3 := sAt (uLiftBasis.getD 3 0)
  g1 := wordElem (uGenWords.getD 1 [])
  g2 := wordElem (uGenWords.getD 2 [])
  t := hLift 0 * hLift 1 * hLift 1 * hLift 0 * hLift 1 * hLift 1
  hx0 := by rw [toMat_xS hsyl hrt (by norm_num : 0 < 4), uAt_basis 0 (by norm_num)]
  hx1 := by rw [toMat_xS hsyl hrt (by norm_num : 1 < 4), uAt_basis 1 (by norm_num)]
  hx2 := by rw [toMat_xS hsyl hrt (by norm_num : 2 < 4), uAt_basis 2 (by norm_num)]
  hx3 := by rw [toMat_xS hsyl hrt (by norm_num : 3 < 4), uAt_basis 3 (by norm_num)]
  hg1 := by rw [toMat_apply, coe_wordElem _ gen_words_ok.1, wordCode_gen.1]
  hg2 := by rw [toMat_apply, coe_wordElem _ gen_words_ok.2, wordCode_gen.2]
  ht := by
    have h0 : toMat (hLift 0) = dec4 codeH0 := by
      rw [hLift, toMat_apply, coe_wordElem _ lift_words_ok.1, wordCode_lift.1]
    have h1 : toMat (hLift 1) = dec4 codeH1 := by
      rw [hLift, toMat_apply, coe_wordElem _ lift_words_ok.2, wordCode_lift.2]
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, h0, h1, ← dec4_mul4, ← dec4_mul4,
      ← dec4_mul4, ← dec4_mul4, ← dec4_mul4, codeT_eq]
  hg1S := by
    apply Subgroup.subset_closure
    refine ⟨uGenWords.getD 1 [], ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ (by simp [uGenWords])]
    exact List.getElem_mem _
  hg2S := by
    apply Subgroup.subset_closure
    refine ⟨uGenWords.getD 2 [], ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ (by simp [uGenWords])]
    exact List.getElem_mem _
  hRS := rtS_le_sylS hsyl hrt
  hRe := rtS_isElemAbelian hsyl hrt
  hR81 := card_rtS hsyl hrt

theorem e81InvAt_of_mulEquiv_u43
    {X : Type*} [Group X] (φ : X ≃* CFSG.Assembly.RankThreeEven.projSU 4 3 1) : E81InvAt X :=
  e81InvAt_of_mulEquiv (φ.trans projSUEquivUX)
    ((data uSylCheck_true (uClassCheck_parts uClassCheck_true).1).e81InvAt_UX uSylCheck_true)

end CFSG.RankThree.PartTwo.Sec6.Res611Res4.U43
