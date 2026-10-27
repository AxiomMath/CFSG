module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAut
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem width_eq_three (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) : n = 3 := by
  have hle := card_bar_LB_le_sq_mul_x hc hw hn hx hZ hLm2 hcenter
  have hge := hc.card_bar_LB_ge hw (by omega)
  rw [hZ] at hle hge
  have hq : x < 2 ^ x := Nat.lt_two_pow_self
  rcases Nat.lt_or_ge n 4 with h | h
  · omega
  · exfalso
    have h3 : (2 ^ x) ^ 3 ≤ (2 ^ x) ^ (n - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hlt : (2 ^ x) ^ 2 * x < (2 ^ x) ^ 3 := by
      rw [show (2 ^ x) ^ 3 = (2 ^ x) ^ 2 * 2 ^ x by ring]
      exact (Nat.mul_lt_mul_left (by positivity : 0 < (2 ^ x) ^ 2)).mpr hq
    omega

theorem card_bar_LB_mul_card_inf_QB (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) :
    Nat.card (bar M Q (LB M Q B)) * Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (2 * n) := by
  have h1 := hc.card_LB_mul hw
  have h2 : Nat.card (bar M Q (LB M Q B)) * Nat.card Q = Nat.card (LB M Q B) :=
    bar_card_mul_card_of_le (M := M) (S := LB M Q B) le_sup_left hc.LB_le_M
  have key : Nat.card (bar M Q (LB M Q B)) * Nat.card ↥(Q ⊓ QB B) * Nat.card Q =
      Nat.card Z ^ (2 * n) * Nat.card Q := by
    calc Nat.card (bar M Q (LB M Q B)) * Nat.card ↥(Q ⊓ QB B) * Nat.card Q
        = (Nat.card (bar M Q (LB M Q B)) * Nat.card Q) * Nat.card ↥(Q ⊓ QB B) := by
          ring
      _ = Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) := by rw [h2]
      _ = Nat.card Q * Nat.card Z ^ (2 * n) := h1
      _ = Nat.card Z ^ (2 * n) * Nat.card Q := by ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos key

theorem card_bar_LB_eq_sq_iff (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 ≤ n) :
    Nat.card (bar M Q (LB M Q B)) = Nat.card Z ^ 2 ↔
      Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (2 * n - 2) := by
  have h := card_bar_LB_mul_card_inf_QB hc hw
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hpow : Nat.card Z ^ (2 * n) = Nat.card Z ^ 2 * Nat.card Z ^ (2 * n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  constructor
  · intro hL
    rw [hL, hpow] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hq 2) h
  · intro hD
    rw [hD, hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hq (2 * n - 2)) h

theorem card_bar_LB_eq_sq (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    Nat.card (bar M Q (LB M Q B)) = (Nat.card Z) ^ 2 := by
  classical
  have hx0 : x ≠ 0 := by omega
  have hIsL2 : CFSG.LocalAnalysis.WeakClosure81.IsL2Gp (Xbar M Q Z B) x := by
    obtain ⟨e⟩ := nonempty_xbar_mulEquiv_psl2GF hLm2 hcenter
    exact ⟨GaloisField 2 x, inferInstance, inferInstance, GaloisField.card 2 x hx0,
      ⟨e.trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 x))⟩⟩
  let f : ↥(bar M Q (LB M Q B)) →* MulAut (Xbar M Q Z B) := barLBConjAct hc
  have hA : CFSG.Open.IsElemAbelian 2 f.range := by
    have h1 : CFSG.Open.IsElemAbelian 2
        (⊤ : Subgroup ↥(bar M Q (LB M Q B))) := by
      have h2 := (hc.isElemAbelian_bar_LB).subgroupOf (bar M Q (LB M Q B))
      rwa [Subgroup.subgroupOf_self] at h2
    have h3 := h1.map f
    have h4 : Subgroup.map f ⊤ = f.range := (MonoidHom.range_eq_map f).symm
    rwa [h4] at h3
  have hrange : Nat.card ↥(f.range) ≤ 2 ^ x :=
    CFSG.LocalAnalysis.WeakClosure81.card_le_two_pow_of_isL2Gp hIsL2 hA
  have ha2 := exists_isA2_of_lieModel hc hx hLm2 hcenter
  have hC := card_inf_centralizer_Xbar_le hc hw hn hx hZ ha2
  have hker : Nat.card ↥(f.ker) ≤ Nat.card Z := by
    rw [show f.ker = (bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B)) from barLBConjAct_ker hc]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans_le hC
  have hcard : Nat.card (bar M Q (LB M Q B)) =
      Nat.card ↥(f.range) * Nat.card ↥(f.ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  refine le_antisymm ?_ (hc.card_bar_LB_ge_two hw hn)
  calc Nat.card (bar M Q (LB M Q B)) = Nat.card ↥(f.range) * Nat.card ↥(f.ker) := hcard
    _ ≤ 2 ^ x * Nat.card Z := Nat.mul_le_mul hrange hker
    _ = (Nat.card Z) ^ 2 := by rw [hZ]; ring

end CFSG.RankThree.GF2n.Stroth80
