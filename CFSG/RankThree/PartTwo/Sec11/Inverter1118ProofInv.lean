module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.Steps
import CFSG.RankThree.PartTwo.Sec11.Final1128Item1129
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Inverter1118Proof

theorem three_pow_dvd_add_one_of_dvd {n e : ℕ} {k : ℤ} (hk : k % 3 = 2)
    (h : (3 : ℤ) ^ n ∣ k ^ 2 ^ e - 1) : (3 : ℤ) ^ n ∣ k + 1 := by
  have hc1 : IsCoprime (3 : ℤ) (k - 1) :=
    (Prime.coprime_iff_not_dvd Int.prime_three).mpr (by omega)
  rcases e with _ | e
  · refine (hc1.pow_left (m := n)).dvd_of_dvd_mul_right ?_
    simpa using (dvd_mul_of_dvd_right h (k + 1))
  · set S := ∑ i ∈ Finset.range (2 ^ e), (k ^ 2) ^ i with hS
    have hfac : k ^ 2 ^ (e + 1) - 1 = (k + 1) * ((k - 1) * S) := by
      have h1 := geom_sum_mul (k ^ 2) (2 ^ e)
      rw [← hS] at h1
      rw [pow_succ', pow_mul, ← h1]
      ring
    have hcS : IsCoprime (3 : ℤ) S := by
      refine (Prime.coprime_iff_not_dvd Int.prime_three).mpr ?_
      intro h3
      have h0 : (S : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd S 3).mpr h3
      have hk' : (k : ZMod 3) = 2 := by
        have hk3 : k % ((3 : ℕ) : ℤ) = 2 := by exact_mod_cast hk
        rw [← ZMod.intCast_mod k 3, hk3]
        simp
      have hk2 : ((k : ZMod 3)) ^ 2 = 1 := by rw [hk']; decide
      rw [hS] at h0
      push_cast at h0
      rw [hk2] at h0
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0
      have h2 : ((2 ^ e : ℕ) : ZMod 3) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at h2
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
    rw [hfac] at h
    exact ((hc1.mul_right hcS).pow_left (m := n)).dvd_of_dvd_mul_right h

section Group

variable {G : Type*} [Group G]

theorem conj_eq_inv_of_two_element {j y : G} {V : Subgroup G} (hy : ∃ n : ℕ, y ^ 3 ^ n = 1)
    (hj : ∃ e : ℕ, j ^ 2 ^ e = 1) (hjy : j ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hyV : y ∉ V) (hinv : j * y * j⁻¹ * y ∈ V) : j * y * j⁻¹ = y⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (Item1119Proof.conj_mem_zpowers_of_mem_normalizer hjy)
  have hk1 : y ^ (k + 1) ∈ V := by
    rw [zpow_add_one, hk]
    exact hinv
  have h3 : (3 : ℤ) ∣ k + 1 := by
    by_contra h3
    exact hyV (Subgroup.zpowers_le.mpr hk1 (Item1116Proof.mem_zpowers_zpow_of_not_dvd hy h3))
  have hk2 : k % 3 = 2 := by omega
  obtain ⟨e, he⟩ := hj
  obtain ⟨m, hm⟩ := Item1119Proof.exists_orderOf_eq_three_pow' hy
  have h1 := Item1119Proof.pow_conj_eq_zpow_pow hk.symm (2 ^ e)
  rw [he, one_mul, inv_one, mul_one] at h1
  have h2 : y ^ (k ^ 2 ^ e - 1) = 1 := by
    rw [zpow_sub_one, ← h1, mul_inv_cancel]
  have h4 : ((orderOf y : ℕ) : ℤ) ∣ k ^ 2 ^ e - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hm] at h4
  push_cast at h4
  have h5 := three_pow_dvd_add_one_of_dvd hk2 h4
  have h6 : y ^ (k + 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hm]
    push_cast
    exact h5
  rw [← hk]
  calc y ^ k = y ^ (k + 1) * y⁻¹ := by rw [zpow_add_one]; group
    _ = y⁻¹ := by rw [h6, one_mul]

theorem conj_inv_or_conj {n y : G} {V : Subgroup G}
    (hny : n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hnV : n ∈ Subgroup.normalizer (V : Set G)) (hy3 : y ^ 3 ∈ V) (hyV : y ∉ V) :
    n * y * n⁻¹ * y⁻¹ ∈ V ∨ n * y * n⁻¹ * y ∈ V := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (Item1119Proof.conj_mem_zpowers_of_mem_normalizer hny)
  have hle : Subgroup.zpowers (y ^ 3) ≤ V := Subgroup.zpowers_le.mpr hy3
  have hmem : ∀ t : ℤ, (3 : ℤ) ∣ t → y ^ t ∈ V := by
    rintro t ⟨u, rfl⟩
    refine hle ?_
    have e : y ^ ((3 : ℤ) * u) = (y ^ 3) ^ u := by
      rw [zpow_mul]
      norm_cast
    rw [e]
    exact Subgroup.zpow_mem_zpowers _ u
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · exfalso
    apply hyV
    have h := hmem k (Int.dvd_of_emod_eq_zero h0)
    rw [hk] at h
    have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnV) _).mp h
    have e : n⁻¹ * (n * y * n⁻¹) * n⁻¹⁻¹ = y := by group
    rwa [e] at h'
  · left
    have h := hmem (k - 1) (by omega)
    rwa [zpow_sub_one, hk] at h
  · right
    have h := hmem (k + 1) (by omega)
    rwa [zpow_add_one, hk] at h

theorem conj_inv_mul_conj {n n' y : G} {V : Subgroup G}
    (hnV : n ∈ Subgroup.normalizer (V : Set G)) (hn : n * y * n⁻¹ * y ∈ V)
    (hn' : n' * y * n'⁻¹ * y⁻¹ ∈ V) : (n * n') * y * (n * n')⁻¹ * y ∈ V := by
  have h1 := (Subgroup.mem_normalizer_iff.mp hnV _).mp hn'
  have e : (n * n') * y * (n * n')⁻¹ * y =
      (n * (n' * y * n'⁻¹ * y⁻¹) * n⁻¹) * (n * y * n⁻¹ * y) := by group
  rw [e]
  exact V.mul_mem h1 hn

theorem conj_mul_conj_inv {n n' y : G} {V : Subgroup G}
    (hnV : n ∈ Subgroup.normalizer (V : Set G)) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hn : n * y * n⁻¹ * y⁻¹ ∈ V) (hn' : n' * y * n'⁻¹ * y ∈ V) :
    (n * n') * y * (n * n')⁻¹ * y ∈ V := by
  have h1 := (Subgroup.mem_normalizer_iff.mp hnV _).mp hn'
  have h2 : y⁻¹ * (n * y * n⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyV) _).mp (V.inv_mem hn)
  have e : (n * n') * y * (n * n')⁻¹ * y =
      (n * (n' * y * n'⁻¹ * y) * n⁻¹) * (y⁻¹ * (n * y * n⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹) := by group
  rw [e]
  exact V.mul_mem h1 h2

theorem conj_inv_mul_conj_inv {n n' y : G} {V : Subgroup G}
    (hnV : n ∈ Subgroup.normalizer (V : Set G)) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hn : n * y * n⁻¹ * y ∈ V) (hn' : n' * y * n'⁻¹ * y ∈ V) :
    (n * n') * y * (n * n')⁻¹ * y⁻¹ ∈ V := by
  have h1 := (Subgroup.mem_normalizer_iff.mp hnV _).mp hn'
  have h2 : y * (n * y * n⁻¹ * y)⁻¹ * y⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hyV _).mp (V.inv_mem hn)
  have e : (n * n') * y * (n * n')⁻¹ * y⁻¹ =
      (n * (n' * y * n'⁻¹ * y) * n⁻¹) * (y * (n * y * n⁻¹ * y)⁻¹ * y⁻¹) := by group
  rw [e]
  exact V.mul_mem h1 h2

theorem conj_pow_odd_inv {n y : G} {V : Subgroup G} (hnV : n ∈ Subgroup.normalizer (V : Set G))
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hn : n * y * n⁻¹ * y ∈ V) (m : ℕ) :
    n ^ (2 * m + 1) * y * (n ^ (2 * m + 1))⁻¹ * y ∈ V := by
  induction m with
  | zero => simpa using hn
  | succ m ih =>
    have hpow : n ^ (2 * m + 1) ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hnV _
    have h1 := conj_inv_mul_conj_inv hpow hyV ih hn
    have h2 := conj_mul_conj_inv (Subgroup.mul_mem _ hpow hnV) hyV h1 hn
    rwa [← pow_succ, ← pow_succ, show 2 * m + 1 + 1 + 1 = 2 * (m + 1) + 1 by ring] at h2

end Group

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem normalizer_x_s (h45 : Sec4.Item4_5) (h113 : Item113)
    (h : Sec11Data G A c L a R Y d x s r g) {n : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G)) :
    n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) ∧
      n ∈ Subgroup.normalizer (Subgroup.zpowers s : Set G) := by
  have hnL := h.toSec11Std.normalizer_le_normalizer_L h45 hn.1
  have hnR : n ∈ Subgroup.normalizer (R : Set G) := by
    have h1 := Subgroup.inf_normalizer_le_normalizer_inf ⟨hn.2, Subgroup.le_normalizer hnL⟩
    rwa [h.inf_normalizer_L h45 h113] at h1
  constructor
  · have hN := Subgroup.inf_normalizer_le_normalizer_inf ⟨hnR, hnL⟩
    rwa [h.inf_L_eq] at hN
  · have hN := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hnR, Sec6.normalizer_le_normalizer_thetaQuotCentralizer L hnL⟩
    rwa [h.inf_centralizer_eq] at hN

theorem commutator_le_centralizer_a (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1115 : Item1115) (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    ⁅sec11P R g, sec11P R g⁆ ≤ Subgroup.centralizer {a} := by
  set P := sec11P R g with hPdef
  have hR := Item1116NoFifteen.R_eq_of_closure_eq h hrs
  have hsa : s * a = a * s := h1115 G A c L a R Y d x s r g h
  have hag : a * g = g * a := (Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
  have hgP := Item1119Proof.g_mem_P R g
  have hRP := Item1119Proof.R_le_P R g
  have hPS : P ≤ Subgroup.closure ({a, x, s, g} : Set G) := by
    refine sup_le ?_ ?_
    · rw [hR, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hSP : Subgroup.closure ({a, x, s, g} : Set G) ≤ P := by
    rw [Subgroup.closure_le]
    have hmem : ∀ y ∈ ({a, x, s} : Set G), y ∈ P := fun y hy => hRP (by
      rw [hR]
      exact Subgroup.subset_closure hy)
    rintro y (rfl | rfl | rfl | rfl)
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hmem _ (by simp)
    · exact hgP
  have hSd : Subgroup.closure ({a, x, s, g} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    hSP.trans (Item1119Proof.P_le_normalizer_d h113 h117 h)
  have hφ : ∀ w ∈ P, a * w * a⁻¹ * w⁻¹ ∈ Subgroup.zpowers d := by
    intro w hw
    refine Item1119Proof.commutator_mem_of_mem_closure hSd ?_ (hPS hw)
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy <;> rw [hy]
    · rw [show a * a * a⁻¹ * a⁻¹ = 1 by group]
      exact Subgroup.one_mem _
    · have e : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ (Item1119Proof.commutator_x_a_facts h45 h).1
    · rw [show a * s * a⁻¹ * s⁻¹ = 1 by rw [← hsa]; group]
      exact Subgroup.one_mem _
    · rw [show a * g * a⁻¹ * g⁻¹ = 1 by rw [hag]; group]
      exact Subgroup.one_mem _
  rw [Subgroup.commutator_le]
  intro p hp q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcen : ∀ z ∈ Subgroup.zpowers d, ∀ w ∈ P, w * z = z * w := fun z hz w hw =>
    Item1119Proof.commute_of_mem_zpowers_d h113 h117 h hz hw
  set φp := a * p * a⁻¹ * p⁻¹ with hφp
  set φq := a * q * a⁻¹ * q⁻¹ with hφq
  have hp' : a * p * a⁻¹ = φp * p := by rw [hφp]; group
  have hq' : a * q * a⁻¹ = φq * q := by rw [hφq]; group
  have h1 := hcen φp (hφ p hp)
  have h2 := hcen φq (hφ q hq)
  have hφpq : φp * φq = φq * φp := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hφ p hp)
    obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp (hφ q hq)
    have e1 : φp = d ^ m := by rw [hm]
    have e2 : φq = d ^ m' := by rw [hm']
    rw [e1, e2, ← zpow_add, ← zpow_add, add_comm]
  have key : a * ⁅p, q⁆ * a⁻¹ = ⁅p, q⁆ := by
    have e : a * ⁅p, q⁆ * a⁻¹ = ⁅a * p * a⁻¹, a * q * a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hp', hq']
    simp only [commutatorElement_def]
    have hpq2 := h2 p hp
    have hp1 := h1 p hp
    have hqp : q * p⁻¹ * φp⁻¹ = φp⁻¹ * (q * p⁻¹) := by
      have h3 : (q * p⁻¹) * φp = φp * (q * p⁻¹) :=
        h1 _ (Subgroup.mul_mem _ hq (Subgroup.inv_mem _ hp))
      calc q * p⁻¹ * φp⁻¹ = φp⁻¹ * (φp * (q * p⁻¹)) * φp⁻¹ := by group
        _ = φp⁻¹ * ((q * p⁻¹) * φp) * φp⁻¹ := by rw [h3]
        _ = φp⁻¹ * (q * p⁻¹) := by group
    have hpφ : p * φp⁻¹ = φp⁻¹ * p := by
      calc p * φp⁻¹ = φp⁻¹ * (φp * p) * φp⁻¹ := by group
        _ = φp⁻¹ * (p * φp) * φp⁻¹ := by rw [hp1]
        _ = φp⁻¹ * p := by group
    calc φp * p * (φq * q) * (φp * p)⁻¹ * (φq * q)⁻¹
        = φp * (p * φq) * q * p⁻¹ * φp⁻¹ * q⁻¹ * φq⁻¹ := by group
      _ = φp * (φq * p) * q * p⁻¹ * φp⁻¹ * q⁻¹ * φq⁻¹ := by rw [hpq2]
      _ = φp * φq * p * (q * p⁻¹ * φp⁻¹) * q⁻¹ * φq⁻¹ := by group
      _ = φp * φq * p * (φp⁻¹ * (q * p⁻¹)) * q⁻¹ * φq⁻¹ := by rw [hqp]
      _ = φp * φq * (p * φp⁻¹) * q * p⁻¹ * q⁻¹ * φq⁻¹ := by group
      _ = φp * φq * (φp⁻¹ * p) * q * p⁻¹ * q⁻¹ * φq⁻¹ := by rw [hpφ]
      _ = (φp * φq * φp⁻¹) * (p * q * p⁻¹ * q⁻¹) * φq⁻¹ := by group
      _ = φq * (p * q * p⁻¹ * q⁻¹) * φq⁻¹ := by
          rw [hφpq]
          group
      _ = p * q * p⁻¹ * q⁻¹ := by
          have h4 : (p * q * p⁻¹ * q⁻¹) * φq = φq * (p * q * p⁻¹ * q⁻¹) :=
            h2 _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hp hq)
              (Subgroup.inv_mem _ hp)) (Subgroup.inv_mem _ hq))
          rw [← h4]
          group
  calc ⁅p, q⁆ * a = (a * ⁅p, q⁆ * a⁻¹) * a := by rw [key]
    _ = a * ⁅p, q⁆ := by group

theorem exists_inverter (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1115 : Item1115) (hbig : Sec11Big G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hW : ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33))
    (hsV : s ∉ ⁅sec11P R g, sec11P R g⁆ ⊔ Subgroup.closure {x ^ 3, s ^ 3}) :
    ∃ j : G, (∃ k : ℕ, j ^ 2 ^ k = 1) ∧
      j ∈ Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ∧
      j * x * j⁻¹ = x⁻¹ ∧ j * s * j⁻¹ = s⁻¹ := by
  have h := hbig.toSec11Data
  set P := sec11P R g with hPdef
  set V := ⁅P, P⁆ ⊔ Subgroup.closure ({x ^ 3, s ^ 3} : Set G) with hVdef
  set NH := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (P : Set G) with hNH
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hRP := Item1119Proof.R_le_P R g
  have hxP : x ∈ P := hRP hxR
  have hsP : s ∈ P := hRP hsR
  have hx := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  have hs := Item1116Proof.exists_pow_eq_one_of_mem h hsR
  have hx3V : x ^ 3 ∈ V := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hs3V : s ^ 3 ∈ V := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hPP : ⁅P, P⁆ ≤ V := le_sup_left
  have hcPP : ⁅P, P⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hp hq) (P.inv_mem hp)) (P.inv_mem hq)
  have hVP : V ≤ P := by
    refine sup_le hcPP ?_
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [P.pow_mem hxP 3, P.pow_mem hsP 3]
  have hPV : ∀ p ∈ P, p ∈ Subgroup.normalizer (V : Set G) := by
    intro p hp
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have e : p * v * p⁻¹ = ⁅p, v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem (hPP (Subgroup.commutator_mem_commutator hp (hVP hv))) hv
  have hNHV : NH ≤ Subgroup.normalizer (V : Set G) := by
    intro n hn
    obtain ⟨hnx, hns⟩ := normalizer_x_s h45 h113 h hn
    refine Item1119Proof.mem_normalizer_sup (Item1129Proof.mem_normalizer_commutator hn.2) ?_
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have hle : Subgroup.closure ({x ^ 3, s ^ 3} : Set G) ≤
        (Subgroup.closure ({x ^ 3, s ^ 3} : Set G)).comap (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      change n * y * n⁻¹ ∈ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy <;> rw [hy]
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
          (Item1119Proof.conj_mem_zpowers_of_mem_normalizer hnx)
        have e : n * x ^ 3 * n⁻¹ = (x ^ 3) ^ k := by
          rw [← conj_pow, ← hk]
          group
        rw [e]
        exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
          (Item1119Proof.conj_mem_zpowers_of_mem_normalizer hns)
        have e : n * s ^ 3 * n⁻¹ = (s ^ 3) ^ k := by
          rw [← conj_pow, ← hk]
          group
        rw [e]
        exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k
    exact hle hv
  have hxV : x ∉ V := by
    have hVa : V ≤ Subgroup.centralizer {a} := by
      refine sup_le (commutator_le_centralizer_a h45 h113 h117 h1115 h hrs) ?_
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have h1 := (Item1119Proof.a_x_facts h45 h).1
        calc x ^ 3 * a = a * x ^ 3 * a⁻¹ * a := by rw [h1]
          _ = a * x ^ 3 := by group
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (Commute.pow_left (h1115 G A c L a R Y d x s r g h : Commute s a) 3).eq
    intro hxV
    exact Item1115Proof.not_commute_a_x h (Subgroup.mem_centralizer_singleton_iff.mp (hVa hxV)).symm
  have htrans := h.htrans hcdN hNd
  have hexists : ∀ y ∈ P, y ∉ V → y ^ 3 ∈ V →
      (∀ n ∈ NH, n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G)) →
      ∃ n ∈ NH, n * y * n⁻¹ * y ∈ V := by
    intro y hyP hyV hy3 hNy
    by_contra hcon
    push Not at hcon
    apply hyV
    refine rank3II_11_22_mem h hcdN hNd htrans hW hVP hPP hNHV hyP fun n hn => ?_
    rcases conj_inv_or_conj (hNy n hn) (hNHV hn) hy3 hyV with h1 | h1
    · exact h1
    · exact absurd h1 (hcon n hn)
  obtain ⟨n₁, hn₁, hn₁x⟩ := hexists x hxP hxV hx3V fun n hn => (normalizer_x_s h45 h113 h hn).1
  obtain ⟨n₂, hn₂, hn₂s⟩ := hexists s hsP hsV hs3V fun n hn => (normalizer_x_s h45 h113 h hn).2
  obtain ⟨n, hn, hnx, hns⟩ : ∃ n ∈ NH, n * x * n⁻¹ * x ∈ V ∧ n * s * n⁻¹ * s ∈ V := by
    rcases conj_inv_or_conj (normalizer_x_s h45 h113 h hn₁).2 (hNHV hn₁) hs3V hsV with h1 | h1
    · rcases conj_inv_or_conj (normalizer_x_s h45 h113 h hn₂).1 (hNHV hn₂) hx3V hxV with
        h2 | h2
      · exact ⟨n₁ * n₂, NH.mul_mem hn₁ hn₂, conj_inv_mul_conj (hNHV hn₁) hn₁x h2,
          conj_mul_conj_inv (hNHV hn₁) (hPV s hsP) h1 hn₂s⟩
      · exact ⟨n₂, hn₂, h2, hn₂s⟩
    · exact ⟨n₁, hn₁, hn₁x, h1⟩
  obtain ⟨e, o, ho, hno⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf n)
    (orderOf_pos n).ne'
  obtain ⟨m, rfl⟩ := ho
  set j := n ^ (2 * m + 1) with hj
  have hjNH : j ∈ NH := NH.pow_mem hn _
  have hj2 : ∃ k : ℕ, j ^ 2 ^ k = 1 := by
    refine ⟨e, ?_⟩
    rw [hj, ← pow_mul, mul_comm, ← hno, pow_orderOf_eq_one]
  have hjx := conj_pow_odd_inv (hNHV hn) (hPV x hxP) hnx m
  have hjs := conj_pow_odd_inv (hNHV hn) (hPV s hsP) hns m
  refine ⟨j, hj2, hjNH.2, ?_, ?_⟩
  · exact conj_eq_inv_of_two_element hx hj2 (normalizer_x_s h45 h113 h hjNH).1 hxV hjx
  · exact conj_eq_inv_of_two_element hs hj2 (normalizer_x_s h45 h113 h hjNH).2 hsV hjs

end Data

end Inverter1118Proof

end CFSG.RankThree.PartTwo.Sec11
