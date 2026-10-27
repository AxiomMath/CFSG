module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth77_of_steps (h76 : Stroth76Statement) (h71 : Stroth71Statement)
    (h73c : Stroth73cStatement) (hZ : Sec7CentreMpStatement) (h1 : Step77OneStatement)
    (h2 : Step77TwoStatement) (hE : Step77EndStatement) : Stroth77Statement := by
  intro G _ _ M Q Z B hc n t hs
  by_contra hno
  have hom : OmegaMinusNat hc t 2 := h76 G M Q Z B hc n t hs hno
  rcases h71 G M Q Z B hc n t hs with h | he
  · exact hno h
  obtain ⟨-, ⟨x, ⟨hxM, g, hg, hQ⟩, hxt, w, hw, hxw⟩, -⟩ := he
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc hs.toSec5.mem
  have hxZ : x ∉ Z0 := by
    intro hxZ0
    exact hxw (sec39_Z_le_Vt ((hZ G M Q Z B hc n t hs Z0 hZ0 x hxZ0).2 w hw))
  obtain ⟨hsc1, hsc2⟩ := (h73c G M Q Z B hc n t hs hno Z0 hZ0).2 hom
  exact hE G M Q Z B hc n t hs hno hom Z0 hZ0 hsc1 hsc2 g hg x hQ hxt hxZ
    (h1 G M Q Z B hc n t hs hno hom Z0 hZ0 g hg x hQ hxt hxZ)
    (h2 G M Q Z B hc n t hs hno hom Z0 hZ0 g hg x hQ hxt hxZ)

theorem sec78_two_pow_gt_plus (m : ℕ) (hm : 7 ≤ m) : 8 * m - 16 < 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : 2 ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
      ring
    rw [e]
    omega

theorem sec78_two_pow_gt_minus (m : ℕ) (hm : 5 ≤ m) : 8 * m - 16 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem card_N_of_order (hc : Ctx M Q Z B) {n m k : ℕ} {N : Subgroup G}
    (hw : Nat.card Q = Nat.card Z ^ (2 * n + 1))
    (hN : Nat.card N * Nat.card Z ^ (4 * m) = Nat.card Q ^ 2) (hk : 2 * n + 1 = 4 * m + k) :
    Nat.card N = Nat.card Q * Nat.card Z ^ k := by
  have hq : 0 < Nat.card Z ^ (4 * m) := pow_pos (by have := two_le_card_Z_of_ctx hc; omega) _
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [hN, mul_assoc, ← pow_add, hw, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem stroth78_of_inputs (h77 : Stroth77Statement) (hN : Sec7NOrderStatement)
    (hW : Sec7WVOrderStatement) (hI : Step78IneqStatement) (hG : Sec7WVGeStatement) :
    Stroth78Statement := by
  intro G _ _ M Q Z B hc n t h5 hlarge hnp m hm htype
  have hs : Sec7Hyp hc n t := ⟨h5, hnp, ⟨m, hm, htype⟩, hlarge⟩
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := h5.width
  have hNo := hN G M Q Z B hc n t hs m hm htype
  have key : ∀ k, 2 * n + 1 = 4 * m + k → Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ k :=
    fun k hk => card_N_of_order hc hw hNo hk
  have hm_of_plus : ∀ m' : ℕ, 1 ≤ m' → OmegaPlusNat hc t m' → m = m' := by
    intro m' hm' hp'
    rcases htype with hp | hmn
    · exact hp.eq_of_plus hp'
    · exact omegaPlusNat_eq_omegaMinusNat (by omega) hp' hmn |>.symm
  have hm_of_minus : ∀ m' : ℕ, 1 ≤ m' → OmegaMinusNat hc t m' → m = m' := by
    intro m' hm' hp'
    rcases htype with hp | hmn
    · exact omegaPlusNat_eq_omegaMinusNat (by omega) hp hp'
    · exact OmegaMinusNat.eq_of_minus (by omega) hm' hmn hp'
  rcases h77 G M Q Z B hc n t hs with ha | ⟨hb, hn⟩ | ⟨hb, hn⟩ | ⟨hb, hn⟩
  ·
    have hIneq := hI G M Q Z B hc n t hs ha m hm htype
    rcases htype with hp | hmn
    · have hm3 : 3 ≤ m := by
        by_contra hlt
        have : m = 2 := by omega
        subst this
        exact hnp hp
      obtain ⟨y, hy, hn⟩ := (hW G M Q Z B hc n t hs m hm).2 hp hm3
      have hm6 : m ≤ 6 := by
        by_contra hgt
        have := sec78_two_pow_gt_plus m (by omega)
        have h2 : 2 ^ (m - 1) ≤ y * 2 ^ (m - 1) := Nat.le_mul_of_pos_left _ hy
        omega
      interval_cases m
      · have h10 := hG G M Q Z B hc n t hs hp
        have hn' : n = 10 := by norm_num at hn; omega
        subst hn'
        exact Or.inl ⟨rfl, rfl, key 9 (by norm_num)⟩
      · have hy2 : y ≤ 2 := by norm_num at hn hIneq; omega
        have : y = 1 ∨ y = 2 := by omega
        rcases this with rfl | rfl
        · have hn' : n = 12 := by norm_num at hn; omega
          subst hn'
          exact Or.inr (Or.inr (Or.inl ⟨rfl, hp, rfl, key 9 (by norm_num)⟩))
        · have hn' : n = 16 := by norm_num at hn; omega
          subst hn'
          exact Or.inr (Or.inl ⟨rfl, rfl, key 17 (by norm_num)⟩)
      · have hy1 : y = 1 := by norm_num at hn hIneq; omega
        subst hy1
        have hn' : n = 18 := by norm_num at hn; omega
        subst hn'
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp, rfl, key 17 (by norm_num)⟩)))
      · have hy1 : y = 1 := by norm_num at hn hIneq; omega
        subst hy1
        have hn' : n = 28 := by norm_num at hn; omega
        subst hn'
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hp, rfl, key 33 (by norm_num)⟩)))
    · obtain ⟨y, hy, hn⟩ := (hW G M Q Z B hc n t hs m hm).1 hmn
      have hm4 : m ≤ 4 := by
        by_contra hgt
        have := sec78_two_pow_gt_minus m (by omega)
        have h2 : 2 ^ m ≤ y * 2 ^ m := Nat.le_mul_of_pos_left _ hy
        omega
      interval_cases m
      · norm_num at hn hIneq
        omega
      · have hy1 : y = 1 := by norm_num at hn hIneq; omega
        subst hy1
        have hn' : n = 10 := by norm_num at hn; omega
        subst hn'
        exact Or.inl ⟨rfl, rfl, key 9 (by norm_num)⟩
      · have hy1 : y = 1 := by norm_num at hn hIneq; omega
        subst hy1
        have hn' : n = 16 := by norm_num at hn; omega
        subst hn'
        exact Or.inr (Or.inl ⟨rfl, rfl, key 17 (by norm_num)⟩)
  · have hm3 : m = 3 := hm_of_minus 3 (by norm_num) hb
    subst hm3
    subst hn
    exact Or.inl ⟨rfl, rfl, key 9 (by norm_num)⟩
  · have hm3 : m = 3 := hm_of_plus 3 (by norm_num) hb
    subst hm3
    subst hn
    exact Or.inl ⟨rfl, rfl, key 9 (by norm_num)⟩
  · have hm4 : m = 4 := hm_of_plus 4 (by norm_num) hb
    subst hm4
    subst hn
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hb, rfl, key 9 (by norm_num)⟩))

end CFSG.RankThree.GF2n.Stroth80
