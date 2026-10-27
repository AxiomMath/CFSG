module

public import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofSAlt
import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofSAlt
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofBasic
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofCenter
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofInv
import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.DataExistsAct

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1117Res4Proof

section Generic

variable {G : Type*} [Group G]

theorem three_dvd_of_zpow_mem {D : Subgroup G} {s : G} (hs3 : s ^ 3 ∈ D) (hs : s ∉ D)
    {m : ℤ} (hm : s ^ m ∈ D) : (3 : ℤ) ∣ m := by
  by_contra h3
  apply hs
  have hcop : IsCoprime m 3 :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by
      have hg : Int.gcd m 3 ∣ 3 := by
        have := Int.gcd_dvd_right (a := m) (b := 3)
        exact Int.ofNat_dvd.mp (by simpa using this)
      rcases (Nat.dvd_prime Nat.prime_three).mp hg with h1 | h1
      · exact h1
      · exfalso
        apply h3
        have := Int.gcd_dvd_left (a := m) (b := 3)
        rw [h1] at this
        exact_mod_cast this))
  obtain ⟨α, β, hαβ⟩ := hcop
  have hs3' : s ^ (3 : ℤ) ∈ D := by exact_mod_cast hs3
  have e : s = (s ^ m) ^ α * (s ^ (3 : ℤ)) ^ β := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm m α, mul_comm (3 : ℤ) β, hαβ, zpow_one]
  rw [e]
  exact D.mul_mem (D.zpow_mem hm α) (D.zpow_mem hs3' β)

theorem zpow_pow_three_comm (y : G) (i : ℤ) : (y ^ i) ^ 3 = (y ^ 3) ^ i := by
  rw [← zpow_natCast (y ^ i), ← zpow_mul, ← zpow_natCast y, ← zpow_mul, mul_comm]

theorem three_dvd_sub_one_of_dvd_one_sub_pow {u : ℤ} {K : ℕ}
    (h : (3 : ℤ) ∣ 1 - u ^ 3 ^ K) : (3 : ℤ) ∣ u - 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ n : ℕ, ((u : ZMod 3)) ^ 3 ^ n = (u : ZMod 3) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  have h1 : ((1 - u ^ 3 ^ K : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  push_cast at h1
  rw [hpow K] at h1
  have h2 : ((u - 1 : ℤ) : ZMod 3) = 0 := by
    push_cast
    linear_combination -h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h2

theorem three_dvd_sub_one_of_conj_mem {D : Subgroup G} {g s : G} (hg : ∃ K : ℕ, g ^ 3 ^ K = 1)
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hsD : ∀ δ ∈ D, s * δ = δ * s)
    (hs3 : s ^ 3 ∈ D) (hs : s ∉ D) {u : ℤ} (hu : s ^ (-u) * (g * s * g⁻¹) ∈ D) :
    (3 : ℤ) ∣ u - 1 := by
  obtain ⟨K, hK⟩ := hg
  set δ₀ := s ^ (-u) * (g * s * g⁻¹) with hδ₀
  have hgs : g * s * g⁻¹ = s ^ u * δ₀ := by
    rw [hδ₀, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have hconj : ∀ δ ∈ D, g * δ * g⁻¹ ∈ D := fun δ hδ =>
    (Subgroup.mem_normalizer_iff.mp hgD δ).mp hδ
  have key : ∀ n : ℕ, ∃ δ ∈ D, g ^ n * s * (g ^ n)⁻¹ = s ^ (u ^ n) * δ := by
    intro n
    induction n with
    | zero => exact ⟨1, D.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨δ, hδD, hδ⟩ := ih
      have hcomm : Commute s δ₀ := hsD δ₀ hu
      refine ⟨δ₀ ^ (u ^ n) * (g * δ * g⁻¹), D.mul_mem (D.zpow_mem hu _) (hconj δ hδD), ?_⟩
      calc g ^ (n + 1) * s * (g ^ (n + 1))⁻¹ = g * (g ^ n * s * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (s ^ (u ^ n) * δ) * g⁻¹ := by rw [hδ]
        _ = (g * s * g⁻¹) ^ (u ^ n) * (g * δ * g⁻¹) := by rw [conj_zpow]; group
        _ = (s ^ u * δ₀) ^ (u ^ n) * (g * δ * g⁻¹) := by rw [hgs]
        _ = s ^ (u ^ (n + 1)) * (δ₀ ^ (u ^ n) * (g * δ * g⁻¹)) := by
            rw [(hcomm.zpow_left u).mul_zpow, ← zpow_mul, ← pow_succ', mul_assoc]
  obtain ⟨δ, hδD, hδ⟩ := key (3 ^ K)
  rw [hK, one_mul, inv_one, mul_one] at hδ
  have hmem : s ^ (1 - u ^ 3 ^ K) ∈ D := by
    have e : s ^ (1 - u ^ 3 ^ K) = δ := by
      rw [zpow_sub, zpow_one]
      calc s * (s ^ (u ^ 3 ^ K))⁻¹ = s ^ (u ^ 3 ^ K) * δ * (s ^ (u ^ 3 ^ K))⁻¹ := by rw [← hδ]
        _ = δ := by
            rw [mul_inv_eq_iff_eq_mul]
            exact ((show Commute s δ from hsD δ hδD).zpow_left _).eq
    rw [e]
    exact hδD
  exact three_dvd_sub_one_of_dvd_one_sub_pow (three_dvd_of_zpow_mem hs3 hs hmem)

end Generic

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem commutator_x_cube_eq (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsa : s * a = a * s) {k m n : ℤ}
    (hxg : x * g * x⁻¹ * g⁻¹ = a ^ k * x ^ (3 * m) * s ^ n) :
    x ^ 3 * g * (x ^ 3)⁻¹ * g⁻¹ = (x ^ (3 * m) * s ^ n) ^ 3 := by
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hxs : s * x = x * s := h.commute_s_x
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g hxR
  have hsP : s ∈ sec11P R g := Item1119Proof.R_le_P R g hsR
  have hdA := Item1117Proof.d_mem_A h
  set e₀ := x * a * x⁻¹ * a⁻¹ with he₀
  have he₀d : e₀ ∈ Subgroup.zpowers d := (Item1119Proof.commutator_x_a_facts h45 h).1
  have he₀A : e₀ ∈ A := Subgroup.zpowers_le.mpr hdA he₀d
  have hxa : x * a * x⁻¹ = e₀ * a := by rw [he₀]; group
  have he₀x : Commute e₀ x :=
    (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h he₀d hxP).symm
  have he₀s : Commute e₀ s :=
    (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h he₀d hsP).symm
  have he₀a : Commute e₀ a := Item1117Proof.commute_of_mem_A h he₀A h.a_mem
  have he₀3 : e₀ ^ 3 = 1 := h.mem_partTwoF.1.2 e₀ he₀A
  have hax3 : Commute (x ^ 3) a := by
    have h1 := (Item1119Proof.a_x_facts h45 h).1
    show x ^ 3 * a = a * x ^ 3
    calc x ^ 3 * a = (a * x ^ 3 * a⁻¹) * a := by rw [h1]
      _ = a * x ^ 3 := by group
  have hx3m : ∀ j : ℤ, x ^ (3 * j) = (x ^ 3) ^ j := fun j => by rw [zpow_mul]; norm_cast
  have hsa' : Commute s a := hsa
  have hsx' : Commute s x := hxs
  set w := x ^ (3 * m) * s ^ n with hw
  have hwx : Commute w x :=
    ((Commute.refl x).zpow_left (3 * m)).mul_left (hsx'.zpow_left n)
  have hwa : Commute w a := by
    rw [hw, hx3m]
    exact (hax3.zpow_left m).mul_left (hsa'.zpow_left n)
  have hwe : Commute w e₀ :=
    ((he₀x.zpow_right (3 * m)).symm).mul_left ((he₀s.zpow_right n).symm)
  have hxg' : x * g * x⁻¹ * g⁻¹ = a ^ k * w := by rw [hxg, hw, mul_assoc]
  exact Item1117ResProof.pow_three_commutator_eq hxg' hxa he₀x he₀a hwx hwa hwe he₀3 ha3

theorem three_dvd_exp_s (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h : Sec11Data G A c L a R Y d x s r g) (hsa : s * a = a * s) {k m n k' m' n' : ℤ}
    (hxg : x * g * x⁻¹ * g⁻¹ = a ^ k * x ^ (3 * m) * s ^ n)
    (hsg : s * g * s⁻¹ * g⁻¹ = a ^ k' * x ^ (3 * m') * s ^ n') : (3 : ℤ) ∣ n' := by
  have hxs : s * x = x * s := h.commute_s_x
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hax : a * x ^ 3 * a⁻¹ = x ^ 3 := (Item1119Proof.a_x_facts h45 h).1
  have hax3 : Commute (x ^ 3) a := by
    show x ^ 3 * a = a * x ^ 3
    calc x ^ 3 * a = (a * x ^ 3 * a⁻¹) * a := by rw [hax]
      _ = a * x ^ 3 := by group
  have hx3m : ∀ j : ℤ, x ^ (3 * j) = (x ^ 3) ^ j := fun j => by rw [zpow_mul]; norm_cast
  have hs3m : ∀ j : ℤ, s ^ (3 * j) = (s ^ 3) ^ j := fun j => by rw [zpow_mul]; norm_cast
  have hsa' : Commute s a := hsa
  have hsx' : Commute s x := hxs
  have hga : g * a = a * g := (Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1))
  set D := Subgroup.closure ({x ^ 3, a, s ^ 3} : Set G) with hD
  have hx3D : x ^ 3 ∈ D := Subgroup.subset_closure (by simp)
  have haD : a ∈ D := Subgroup.subset_closure (by simp)
  have hs3D : s ^ 3 ∈ D := Subgroup.subset_closure (by simp)
  have hsD : s ∉ D := by
    have h1 := Item1118StepsProof.not_mem_closure h hsa hax 0
    rwa [zpow_zero, mul_one] at h1
  have hsDc : ∀ δ ∈ D, s * δ = δ * s := by
    intro δ hδ
    refine Item1118StepsProof.commute_of_mem_closure ?_ hδ
    rintro y (rfl | rfl | rfl)
    · exact (hsx'.pow_right 3).eq
    · exact hsa
    · exact ((Commute.refl s).pow_right 3).eq
  have hcx3 : Commute (x ^ 3) (s ^ 3) := (hsx'.pow_pow 3 3).symm
  have hgD : g ∈ Subgroup.normalizer (D : Set G) := by
    refine Item1118StepsProof.mem_normalizer_closure_of_forall ?_
    rintro y (rfl | rfl | rfl)
    ·
      have hc := commutator_x_cube_eq h45 h113 h117 h hsa hxg
      have e : g * x ^ 3 * g⁻¹ = (x ^ 3 * g * (x ^ 3)⁻¹ * g⁻¹)⁻¹ * x ^ 3 := by group
      rw [e, hc]
      have hxms : Commute (x ^ (3 * m)) (s ^ n) := (hsx'.zpow_zpow n (3 * m)).symm
      have hw3 : (x ^ (3 * m) * s ^ n) ^ 3 = (x ^ 3) ^ (3 * m) * (s ^ 3) ^ n := by
        rw [hxms.mul_pow, zpow_pow_three_comm, zpow_pow_three_comm]
      rw [hw3]
      exact D.mul_mem (D.inv_mem (D.mul_mem (D.zpow_mem hx3D _) (D.zpow_mem hs3D _))) hx3D
    · rw [hga, mul_inv_cancel_right]
      exact haD
    ·
      have e : g * s ^ 3 * g⁻¹ = ((s * g * s⁻¹ * g⁻¹)⁻¹ * s) ^ 3 := by
        rw [← conj_pow]; congr 1; group
      rw [e, hsg]
      have hws : Commute (a ^ k' * x ^ (3 * m') * s ^ n') s :=
        ((hsa'.symm.zpow_left k').mul_left (hsx'.symm.zpow_left (3 * m'))).mul_left
          ((Commute.refl s).zpow_left n')
      rw [hws.inv_left.mul_pow, inv_pow]
      refine D.mul_mem (D.inv_mem ?_) hs3D
      have hc1 : Commute (a ^ k') (x ^ (3 * m')) := by
        rw [hx3m]; exact hax3.symm.zpow_zpow k' m'
      have hc2 : Commute (a ^ k' * x ^ (3 * m')) (s ^ n') :=
        ((hsa'.symm.zpow_zpow k' n')).mul_left ((hsx'.symm.zpow_zpow (3 * m') n'))
      rw [hc2.mul_pow, hc1.mul_pow, zpow_pow_three_comm, zpow_pow_three_comm,
        zpow_pow_three_comm, ha3, one_zpow, one_mul]
      exact D.mul_mem (D.zpow_mem hx3D _) (D.zpow_mem hs3D _)
  set v := a ^ k' * x ^ (3 * m') with hv
  have hvD : v ∈ D := by
    rw [hv, hx3m]
    exact D.mul_mem (D.zpow_mem haD _) (D.zpow_mem hx3D _)
  have hvs : Commute v s :=
    (hsa'.symm.zpow_left k').mul_left (hsx'.symm.zpow_left (3 * m'))
  have hu : s ^ (-(1 - n')) * (g * s * g⁻¹) ∈ D := by
    have e : s ^ (-(1 - n')) * (g * s * g⁻¹) = v⁻¹ := by
      have hgs : g * s * g⁻¹ = (v * s ^ n')⁻¹ * s := by
        rw [show g * s * g⁻¹ = (s * g * s⁻¹ * g⁻¹)⁻¹ * s by group, hsg, hv]
      rw [hgs, mul_inv_rev]
      have hvs' : Commute v⁻¹ s := hvs.inv_left
      calc s ^ (-(1 - n')) * ((s ^ n')⁻¹ * v⁻¹ * s)
          = s ^ (-(1 - n')) * ((s ^ n')⁻¹ * (v⁻¹ * s)) := by group
        _ = s ^ (-(1 - n')) * ((s ^ n')⁻¹ * (s * v⁻¹)) := by rw [hvs'.eq]
        _ = (s ^ (-(1 - n')) * (s ^ n')⁻¹ * s) * v⁻¹ := by group
        _ = v⁻¹ := by
            rw [← zpow_neg, ← zpow_add, ← zpow_add_one]
            ring_nf
            rw [zpow_zero, one_mul]
    rw [e]
    exact D.inv_mem hvD
  have h3 := three_dvd_sub_one_of_conj_mem h.pow_eq_one hgD hsDc hs3D hsD hu
  have e : 1 - n' - 1 = -n' := by ring
  rw [e] at h3
  exact (Int.dvd_neg).mp h3

theorem alt_of_big (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    s * g * s⁻¹ * g⁻¹ ∈ Subgroup.closure {x ^ 3, s ^ 3} ∨
      x * g * x⁻¹ * g⁻¹ ∈ Subgroup.closure {a, x ^ 3, s ^ 3} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hbig.toSec11Data
  have h1115 := item1115_of_mhoV h45 h113 h117
  have hsa : s * a = a * s := h1115 G A c L a R Y d x s r g h
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hgR : g ∈ Subgroup.normalizer (R : Set G) := h.g_mem_normalizer
  have hxs : s * x = x * s := h.commute_s_x
  have hgY : g ∈ Y := h.g_mem.1
  have hx3Y : x ^ 3 ∈ Y := Item1119Proof.x_cube_mem_Y h45 h
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hPPa := Inverter1118Proof.commutator_le_centralizer_a h45 h113 h117 h1115 h hrs
  have hgP := Item1119Proof.g_mem_P R g
  have hcomm_R : ∀ y ∈ R, y * g * y⁻¹ * g⁻¹ ∈ R := fun y hy => by
    have e : y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) := by group
    rw [e]
    exact R.mul_mem hy ((Subgroup.mem_normalizer_iff.mp hgR _).mp (R.inv_mem hy))
  have hcomm_a : ∀ y ∈ R, y * g * y⁻¹ * g⁻¹ * a = a * (y * g * y⁻¹ * g⁻¹) := fun y hy => by
    have hmem : ⁅y, g⁆ ∈ ⁅sec11P R g, sec11P R g⁆ :=
      Subgroup.commutator_mem_commutator (Item1119Proof.R_le_P R g hy) hgP
    rw [commutatorElement_def] at hmem
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hPPa hmem))
  obtain ⟨k, m, n, hkmn⟩ := Item1118StepsProof.exists_eq_of_mem_centralizer h45 h113 h117 h hrs
    hsa (hcomm_R x hxR) (hcomm_a x hxR)
  obtain ⟨k', m', n', hkmn'⟩ := Item1118StepsProof.exists_eq_of_mem_centralizer h45 h113 h117 h
    hrs hsa (hcomm_R s hsR) (hcomm_a s hsR)
  have hsY : s ∈ Subgroup.normalizer (Y : Set G) := by
    obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
    have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
    have hK1 : sec11K L a ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
    exact h.toSec11Std.mem_normalizer_Y hK1
      ((Item1116Proof.le_centralizer_and_normalizer h45 h).2 hsR) hsa
  have hsgY : s * g * s⁻¹ * g⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hsY g).mp hgY) (Y.inv_mem hgY)
  have hn' : (3 : ℤ) ∣ n' :=
    three_dvd_exp_s h45 h113 h117 h hsa hkmn hkmn'
  obtain ⟨q', hq'⟩ := hn'
  have hx3m : ∀ j : ℤ, x ^ (3 * j) = (x ^ 3) ^ j := fun j => by rw [zpow_mul]; norm_cast
  have hs3m : ∀ j : ℤ, s ^ (3 * j) = (s ^ 3) ^ j := fun j => by rw [zpow_mul]; norm_cast
  by_cases hn : (3 : ℤ) ∣ n
  ·
    right
    obtain ⟨q, hq⟩ := hn
    set T := Subgroup.closure ({a, x ^ 3, s ^ 3} : Set G) with hT
    have haT : a ∈ T := Subgroup.subset_closure (by simp)
    have hx3T : x ^ 3 ∈ T := Subgroup.subset_closure (by simp)
    have hs3T : s ^ 3 ∈ T := Subgroup.subset_closure (by simp)
    rw [hkmn, hq, hx3m, hs3m]
    exact T.mul_mem (T.mul_mem (T.zpow_mem haT k) (T.zpow_mem hx3T m)) (T.zpow_mem hs3T q)
  ·
    left
    obtain ⟨-, -, hd3⟩ := Item1115Proof.d_mem h
    have hdA := Item1117Proof.d_mem_A h
    have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g hxR
    have hsP : s ∈ sec11P R g := Item1119Proof.R_le_P R g hsR
    set e₀ := x * a * x⁻¹ * a⁻¹ with he₀
    have he₀d : e₀ ∈ Subgroup.zpowers d := (Item1119Proof.commutator_x_a_facts h45 h).1
    have he₀A : e₀ ∈ A := Subgroup.zpowers_le.mpr hdA he₀d
    have hxa : x * a * x⁻¹ = e₀ * a := by rw [he₀]; group
    have he₀x : Commute e₀ x :=
      (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h he₀d hxP).symm
    have he₀s : Commute e₀ s :=
      (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h he₀d hsP).symm
    have he₀a : Commute e₀ a := Item1117Proof.commute_of_mem_A h he₀A h.a_mem
    have he₀3 : e₀ ^ 3 = 1 := h.mem_partTwoF.1.2 e₀ he₀A
    have hax3 : Commute (x ^ 3) a := by
      have h1 := (Item1119Proof.a_x_facts h45 h).1
      show x ^ 3 * a = a * x ^ 3
      calc x ^ 3 * a = (a * x ^ 3 * a⁻¹) * a := by rw [h1]
        _ = a * x ^ 3 := by group
    have hsa' : Commute s a := hsa
    have hsx' : Commute s x := hxs
    set w := x ^ (3 * m) * s ^ n with hw
    have hwx : Commute w x :=
      ((Commute.refl x).zpow_left (3 * m)).mul_left (hsx'.zpow_left n)
    have hwa : Commute w a := by
      rw [hw, hx3m]
      exact (hax3.zpow_left m).mul_left (hsa'.zpow_left n)
    have hwe : Commute w e₀ :=
      ((he₀x.zpow_right (3 * m)).symm).mul_left ((he₀s.zpow_right n).symm)
    have hxg : x * g * x⁻¹ * g⁻¹ = a ^ k * w := by rw [hkmn, hw, mul_assoc]
    have hcube := Item1117ResProof.pow_three_commutator_eq hxg hxa he₀x he₀a hwx hwa hwe he₀3 ha3
    have hcY : x ^ 3 * g * (x ^ 3)⁻¹ * g⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem hx3Y hgY) (Y.inv_mem hx3Y)) (Y.inv_mem hgY)
    rw [hcube] at hcY
    have hxms : Commute (x ^ (3 * m)) (s ^ n) :=
      (hsx'.zpow_zpow n (3 * m)).symm
    have hw3 : w ^ 3 = (x ^ (3 * m)) ^ 3 * (s ^ n) ^ 3 := by rw [hw, hxms.mul_pow]
    have hxY : (x ^ (3 * m)) ^ 3 ∈ Y := by
      rw [hx3m]
      exact Y.pow_mem (Y.zpow_mem hx3Y m) 3
    have hsnY : (s ^ 3) ^ n ∈ Y := by
      have h1 : (s ^ n) ^ 3 ∈ Y := by
        have e : (s ^ n) ^ 3 = ((x ^ (3 * m)) ^ 3)⁻¹ * w ^ 3 := by rw [hw3]; group
        rw [e]
        exact Y.mul_mem (Y.inv_mem hxY) hcY
      have e : (s ^ 3) ^ n = (s ^ n) ^ 3 := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [e]
      exact h1
    have hs3 : ∃ j : ℕ, (s ^ 3) ^ 3 ^ j = 1 := by
      obtain ⟨j, hj⟩ := Item1116Proof.exists_pow_eq_one_of_mem h hsR
      exact ⟨j, by rw [← pow_mul, mul_comm, pow_mul, hj, one_pow]⟩
    have hs3Y : s ^ 3 ∈ Y :=
      Subgroup.zpowers_le.mpr hsnY (Item1116Proof.mem_zpowers_zpow_of_not_dvd hs3 hn)
    have hsn'Y : s ^ n' ∈ Y := by
      rw [hq', hs3m]
      exact Y.zpow_mem hs3Y q'
    have hx3m'Y : x ^ (3 * m') ∈ Y := by
      rw [hx3m]
      exact Y.zpow_mem hx3Y m'
    have hakY : a ^ k' ∈ Y := by
      have e : a ^ k' = (s * g * s⁻¹ * g⁻¹) * (s ^ n')⁻¹ * (x ^ (3 * m'))⁻¹ := by
        rw [hkmn']; group
      rw [e]
      exact Y.mul_mem (Y.mul_mem hsgY (Y.inv_mem hsn'Y)) (Y.inv_mem hx3m'Y)
    have hk' : (3 : ℤ) ∣ k' := by
      by_contra hk'
      apply hbig.a_not_mem_Y
      exact Subgroup.zpowers_le.mpr hakY
        (Item1116Proof.mem_zpowers_zpow_of_not_dvd ⟨1, by rw [pow_one]; exact ha3⟩ hk')
    rw [hkmn', ActOnA.zpow_eq_one_of_dvd ha3 hk', one_mul, hq', hx3m, hs3m]
    set T := Subgroup.closure ({x ^ 3, s ^ 3} : Set G) with hT
    exact T.mul_mem (T.zpow_mem (Subgroup.subset_closure (by simp)) m')
      (T.zpow_mem (Subgroup.subset_closure (by simp)) q')

theorem comm_of_big (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hW : ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33))
 :
    ∃ i : ℤ, x * g * x⁻¹ * g⁻¹ ∈ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3} ∧
      s * g * s⁻¹ * g⁻¹ ∈ Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hbig.toSec11Data
  have hsa : s * a = a * s := item1115_of_mhoV h45 h113 h117 G A c L a R Y d x s r g h
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hgR : g ∈ Subgroup.normalizer (R : Set G) := h.g_mem_normalizer
  have hxs : s * x = x * s := h.commute_s_x
  have hxsc : Commute s x := hxs
  have hsac : Commute s a := hsa
  have hax : a * x ^ 3 * a⁻¹ = x ^ 3 := (Item1119Proof.a_x_facts h45 h).1
  have hax3 : Commute a (x ^ 3) := by
    show a * x ^ 3 = x ^ 3 * a
    calc a * x ^ 3 = a * x ^ 3 * a⁻¹ * a := by group
      _ = x ^ 3 * a := by rw [hax]
  have hPPa := Inverter1118Proof.commutator_le_centralizer_a h45 h113 h117
    (item1115_of_mhoV h45 h113 h117) h hrs
  have hgP := Item1119Proof.g_mem_P R g
  have hcomm_R : ∀ y ∈ R, y * g * y⁻¹ * g⁻¹ ∈ R := fun y hy => by
    have e : y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) := by group
    rw [e]
    exact R.mul_mem hy ((Subgroup.mem_normalizer_iff.mp hgR _).mp (R.inv_mem hy))
  have hcomm_a : ∀ y ∈ R, y * g * y⁻¹ * g⁻¹ * a = a * (y * g * y⁻¹ * g⁻¹) := fun y hy => by
    have hmem : ⁅y, g⁆ ∈ ⁅sec11P R g, sec11P R g⁆ :=
      Subgroup.commutator_mem_commutator (Item1119Proof.R_le_P R g hy) hgP
    rw [commutatorElement_def] at hmem
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hPPa hmem))
  obtain ⟨k, m, n, hkmn⟩ := Item1118StepsProof.exists_eq_of_mem_centralizer h45 h113 h117 h hrs
    hsa (hcomm_R x hxR) (hcomm_a x hxR)
  obtain ⟨k', m', n', hkmn'⟩ := Item1118StepsProof.exists_eq_of_mem_centralizer h45 h113 h117 h
    hrs hsa (hcomm_R s hsR) (hcomm_a s hsR)
  have hsY : s ∈ Subgroup.normalizer (Y : Set G) := by
    obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
    have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
    have hK1 : sec11K L a ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
    exact h.toSec11Std.mem_normalizer_Y hK1
      ((Item1116Proof.le_centralizer_and_normalizer h45 h).2 hsR) hsa
  have hsgY : s * g * s⁻¹ * g⁻¹ ∈ Y := by
    have e : s * g * s⁻¹ * g⁻¹ = (s * g * s⁻¹) * g⁻¹ := rfl
    rw [e]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hsY g).mp h.g_mem.1) (Y.inv_mem h.g_mem.1)
  have hn' : (3 : ℤ) ∣ n' :=
    three_dvd_exp_s h45 h113 h117 h hsa hkmn hkmn'
  have hmemT : ∀ i k₀ m₀ q : ℤ, a ^ k₀ * x ^ (3 * m₀) * s ^ (i * k₀ + 3 * q) ∈
      Subgroup.closure {x ^ 3, a * s ^ i, s ^ 3} := by
    intro i k₀ m₀ q
    set T := Subgroup.closure ({x ^ 3, a * s ^ i, s ^ 3} : Set G)
    have hx3T : x ^ 3 ∈ T := Subgroup.subset_closure (by simp)
    have huT : a * s ^ i ∈ T := Subgroup.subset_closure (by simp)
    have hs3T : s ^ 3 ∈ T := Subgroup.subset_closure (by simp)
    have e : a ^ k₀ * x ^ (3 * m₀) * s ^ (i * k₀ + 3 * q) =
        (a * s ^ i) ^ k₀ * (x ^ 3) ^ m₀ * (s ^ 3) ^ q := by
      have h1 : (a * s ^ i) ^ k₀ = a ^ k₀ * s ^ (i * k₀) := by
        rw [(Commute.zpow_right hsac.symm i).mul_zpow, ← zpow_mul]
      have h2 : (x ^ 3) ^ m₀ = x ^ (3 * m₀) := by
        rw [zpow_mul]
        norm_cast
      have h3 : (s ^ 3) ^ q = s ^ (3 * q) := by
        rw [zpow_mul]
        norm_cast
      calc a ^ k₀ * x ^ (3 * m₀) * s ^ (i * k₀ + 3 * q)
          = a ^ k₀ * (x ^ (3 * m₀) * s ^ (i * k₀)) * s ^ (3 * q) := by rw [zpow_add]; group
        _ = a ^ k₀ * (s ^ (i * k₀) * x ^ (3 * m₀)) * s ^ (3 * q) := by
            rw [(hxsc.zpow_zpow (i * k₀) (3 * m₀)).eq]
        _ = (a * s ^ i) ^ k₀ * (x ^ 3) ^ m₀ * (s ^ 3) ^ q := by rw [h1, h2, h3]; group
    rw [e]
    exact T.mul_mem (T.mul_mem (T.zpow_mem huT k₀) (T.zpow_mem hx3T m₀)) (T.zpow_mem hs3T q)
  rcases alt_of_big h45 h113 h117 hbig hrs with hL | hR
  ·
    have hk : ¬ (3 : ℤ) ∣ k := by
      intro hk3
      set D := Subgroup.closure ({x, s} : Set G) with hD
      have hxD : x ∈ D := Subgroup.subset_closure (by simp)
      have hsD : s ∈ D := Subgroup.subset_closure (by simp)
      have hxgD : x * g * x⁻¹ * g⁻¹ ∈ D := by
        rw [hkmn, ActOnA.zpow_eq_one_of_dvd (h.mem_partTwoF.1.2 a h.a_mem) hk3, one_mul]
        exact D.mul_mem (D.zpow_mem hxD _) (D.zpow_mem hsD _)
      have hsgD : s * g * s⁻¹ * g⁻¹ ∈ D := by
        refine (Subgroup.closure_le _).mpr ?_ hL
        rintro z (rfl | rfl)
        · exact D.pow_mem hxD 3
        · exact D.pow_mem hsD 3
      have hPP := Item1118StepsProof.commutator_le_closure_xs h45 h hrs hsa hxgD hsgD
      have hVP : D ≤ sec11P R g := by
        rw [hD, Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact Item1119Proof.R_le_P R g hxR
        · exact Item1119Proof.R_le_P R g hsR
      have hNV : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
          Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
            Subgroup.normalizer (D : Set G) := by
        intro n hn
        obtain ⟨hnx, hns⟩ := Inverter1118Proof.normalizer_x_s h45 h113 h hn
        refine Item1118StepsProof.mem_normalizer_closure_of_forall ?_
        rintro z (rfl | rfl)
        · exact Subgroup.zpowers_le.mpr hxD
            (Item1119Proof.conj_mem_zpowers_of_mem_normalizer hnx)
        · exact Subgroup.zpowers_le.mpr hsD
            (Item1119Proof.conj_mem_zpowers_of_mem_normalizer hns)
      have haP : a ∈ sec11P R g :=
        Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 h.a_mem)
      have hcen : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
          Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G),
            n * a * n⁻¹ * a⁻¹ ∈ D := by
        intro n hn
        have h1 := h.commutator_mem_V h45 h113 outAbelian1016
          (Item1115Proof.A_le_R h.toHyp91 h.a_mem) n hn
        rwa [Set.pair_comm] at h1
      have haV : a ∉ D := by
        intro haD
        apply h.toSec11Std.a_not_mem_innerPreimage
        have hle : D ≤ innerPreimage L := by
          rw [hD, Set.pair_comm, ← h.inf_innerPreimage_eq]
          exact inf_le_right
        exact hle haD
      exact rank3II_11_27_of h hcdN hNd (h.htrans hcdN hNd) hW hVP hNV haP hcen haV hPP
    refine ⟨k * n, ?_, ?_⟩
    · have hq : (3 : ℤ) ∣ n - k * n * k := by
        have hkk : (3 : ℤ) ∣ k * k - 1 := by
          have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
          rcases hk' with h1 | h1
          · exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, Int.mul_emod, h1]; norm_num)
          · exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, Int.mul_emod, h1]; norm_num)
        have e : n - k * n * k = -(n * (k * k - 1)) := by ring
        rw [e]
        exact (dvd_mul_of_dvd_right hkk n).neg_right
      obtain ⟨q, hq⟩ := hq
      have e : s ^ n = s ^ (k * n * k + 3 * q) := by
        rw [show k * n * k + 3 * q = n by linarith]
      rw [hkmn, e]
      exact hmemT (k * n) k m q
    · refine (Subgroup.closure_le _).mpr ?_ hL
      rintro z (rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
  ·
    refine ⟨0, ?_, ?_⟩
    · refine (Subgroup.closure_le _).mpr ?_ hR
      rintro z (rfl | rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · obtain ⟨q, hq⟩ := hn'
      have e : s ^ n' = s ^ ((0 : ℤ) * k' + 3 * q) := by rw [hq, zero_mul, zero_add]
      rw [hkmn', e]
      exact hmemT 0 k' m' q

end Data

end Item1117Res4Proof

section Main

theorem step1118SComm_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) :
    Step1118SComm := by
  intro G _ _ A c L a R Y d x s r g hbig hcdN hNd hrs hW
  exact Item1117Res4Proof.comm_of_big h45 h113 h117 hbig hcdN hNd hrs hW

theorem step1118S_holds (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) :
    Step1118S :=
  step1118S_of h45 h113 h117 (step1118SComm_holds h45 h113 h117)

end Main

end CFSG.RankThree.PartTwo.Sec11
