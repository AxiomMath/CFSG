module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReePhi6Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReePhi6Sub
import CFSG.Walter.ReeOrder.WardLocal.Four
import CFSG.Walter.ReeOrder.JT.Section2
import CFSG.Monster.B.GSide.HInnerFusion
import CFSG.GroupTheory.CentralizerMap
import CFSG.ClassicalInvolution.Orders.Ree
import CFSG.Blueprint.Catalog
import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped MatrixGroups

private lemma three_pow_odd_mod_seven (k : ℕ) :
    3 ^ (2 * k + 1) % 7 = 3 ∨ 3 ^ (2 * k + 1) % 7 = 5 ∨
      3 ^ (2 * k + 1) % 7 = 6 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [h, pow_add]
    have hmod : 3 ^ (2 * k + 1) * 3 ^ 2 % 7 =
        (3 ^ (2 * k + 1) % 7) * (3 ^ 2 % 7) % 7 := Nat.mul_mod _ _ _
    rw [hmod]
    rcases ih with h | h | h <;> rw [h] <;> norm_num

private lemma ree_q_pos (k : ℕ) : 1 ≤ 3 ^ (2 * k + 1) := by
  have := pow_pos (by norm_num : 0 < 3) (2 * k + 1)
  omega

private lemma ree_q_ge (k : ℕ) (hk : 1 ≤ k) : 27 ≤ 3 ^ (2 * k + 1) := by
  have h : 3 ^ 3 ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h
  exact h

private lemma ree_q_pow_three_add_one (q : ℕ) (hq : 2 ≤ q) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have h1 : q ≤ q ^ 2 := by nlinarith
  zify [h1, hq]
  ring

private lemma three_mul_pow_eq (k : ℕ) : 3 * 3 ^ k = 3 ^ (k + 1) := (pow_succ' 3 k).symm

private lemma three_pow_succ_le_q (k : ℕ) (hk : 1 ≤ k) : 3 * 3 ^ k ≤ 3 ^ (2 * k + 1) + 1 := by
  rw [three_mul_pow_eq]
  have h : 3 ^ (k + 1) ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem ree_exists_hall_torus
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X) {k : ℕ} (hk : 1 ≤ k)
    (hmod : CFSG.Blueprint.LieModel X .twistedG2 0 3 (2 * k + 1))
    (h7 : ¬ 7 ∣ 3 ^ (2 * k + 1) + 1) {B : Subgroup X} (hB7 : Nat.card B = 7) :
    ∃ H : Subgroup X, B ≤ H ∧ (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧
      (∀ x ∈ H, x ≠ 1 → centralizer ({x} : Set X) = H) ∧
      (Nat.card H = 3 ^ (2 * k + 1) + 1 + 3 ^ (k + 1) ∨
        Nat.card H + 3 ^ (k + 1) = 3 ^ (2 * k + 1) + 1) ∧
      ∃ u : X, orderOf u = 2 ∧ ∀ h ∈ H, u * h * u⁻¹ = h⁻¹ := by
  classical
  have hree : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * k + 1) :=
    (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
  obtain ⟨-, ⟨⟨x₀, hx₀⟩, -⟩, -⟩ :=
    CFSG.ComponentClassification.LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
      k hk X hree
  obtain ⟨J₀, hJ₀p, hJ₀f, -⟩ := ree_exists_jtHyp hXs hmod hx₀
  obtain ⟨W, hWp, hWf, -, -⟩ := exists_reeTypeHyp_of_jtHyp J₀ hJ₀p
  have hWq : W.q = 3 ^ (2 * k + 1) := by
    rw [show W.q = W.p ^ W.f from rfl, hWp, hWf, hJ₀p, hJ₀f]
  obtain ⟨hqf, hM⟩ := CFSG.Walter.WardLocal.ward_four W hWq
  have h7X : 7 ∣ Nat.card X := by
    have h := Subgroup.card_subgroup_dvd_card B
    rwa [hB7] at h
  have hcardX : Nat.card X = (3 ^ (2 * k + 1)) ^ 3 * ((3 ^ (2 * k + 1)) ^ 3 + 1) *
      (3 ^ (2 * k + 1) - 1) := by
    obtain ⟨-, -, -, -, hcard⟩ :=
      CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hree
    rw [hcard]
    simp [CFSG.Open.ordRee]
  have h7q : ¬ 7 ∣ 3 ^ (2 * k + 1) := by
    intro h
    have h' := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
    norm_num at h'
  have h7q1 : ¬ 7 ∣ 3 ^ (2 * k + 1) - 1 := by
    intro h
    obtain ⟨t, ht⟩ := h
    have hq1 : 1 ≤ 3 ^ (2 * k + 1) := ree_q_pos k
    have hqeq : 3 ^ (2 * k + 1) = 7 * t + 1 := by omega
    have hmodq : 3 ^ (2 * k + 1) % 7 = 1 := by
      rw [hqeq, Nat.add_mod]
      norm_num
    rcases three_pow_odd_mod_seven k with h | h | h <;> omega
  have h7prod : 7 ∣ (3 ^ (2 * k + 1)) ^ 3 * ((3 ^ (2 * k + 1)) ^ 3 + 1) *
      (3 ^ (2 * k + 1) - 1) := hcardX ▸ h7X
  have h7a : 7 ∣ (3 ^ (2 * k + 1)) ^ 3 * ((3 ^ (2 * k + 1)) ^ 3 + 1) := by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7prod with h | h
    · exact h
    · exact absurd h h7q1
  have h7b : 7 ∣ (3 ^ (2 * k + 1)) ^ 3 + 1 := by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7a with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h) h7q
    · exact h
  have hq2 : 2 ≤ 3 ^ (2 * k + 1) := by
    have := ree_q_ge k hk
    omega
  have h7phi : 7 ∣ (3 ^ (2 * k + 1)) ^ 2 - 3 ^ (2 * k + 1) + 1 := by
    rw [ree_q_pow_three_add_one _ hq2] at h7b
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7b with h | h
    · exact absurd h h7
    · exact h
  have h7prod2 : 7 ∣ (3 ^ (2 * k + 1) + 1 + 3 * 3 ^ k) *
      (3 ^ (2 * k + 1) + 1 - 3 * 3 ^ k) := by
    have h := h7phi
    rw [← hWq] at h
    rw [hqf] at h
    rwa [hWq] at h
  obtain ⟨s, hs7⟩ : ∃ s : Bool, 7 ∣ (if s then 3 ^ (2 * k + 1) + 1 + 3 * 3 ^ k
      else 3 ^ (2 * k + 1) + 1 - 3 * 3 ^ k) := by
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7prod2 with h | h
    · exact ⟨true, by simpa using h⟩
    · exact ⟨false, by simpa using h⟩
  obtain ⟨M, W', hMcomm, hMcard, hMcop, hMcen, -, hWcyc, hW6, hMW, hNM, hfpf⟩ := hM s
  have hMcomm' : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hMcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h7M : 7 ∣ Nat.card M := by
    rw [hMcard, hWq]
    exact hs7
  have hidxM : ¬ 7 ∣ M.index := by
    intro h7i
    have hg7 : 7 ∣ Nat.gcd (Nat.card M) M.index := Nat.dvd_gcd h7M h7i
    rw [hMcop] at hg7
    norm_num at hg7
  have hBpg : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by rw [hB7, pow_one])
  obtain ⟨g, hg⟩ := CFSG.Monster.B.GSide.exists_conj_mem_of_not_dvd_index M hidxM hBpg
  let H : Subgroup X := M.map (MulAut.conj g⁻¹).toMonoidHom
  have hBH : B ≤ H := by
    intro b hb
    have hbM : g * b * g⁻¹ ∈ M := hg b hb
    have hmem : (MulAut.conj g⁻¹) (g * b * g⁻¹) ∈ H := Subgroup.mem_map_of_mem _ hbM
    have heq : (MulAut.conj g⁻¹) (g * b * g⁻¹) = b := by
      rw [MulAut.conj_apply]
      group
    rwa [heq] at hmem
  have hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨n, hnM, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hMcomm' m hmM n hnM]
  have hHC : ∀ x ∈ H, x ≠ 1 → centralizer ({x} : Set X) = H := by
    intro x hx hx1
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hx
    have hm1 : m ≠ 1 := by
      intro h1
      apply hx1
      rw [h1, map_one]
    have hcen : centralizer ({m} : Set X) = M := hMcen m hmM hm1
    have := CFSG.centralizer_singleton_map (MulAut.conj g⁻¹) m
    rw [hcen] at this
    exact this.symm
  have hHcard : Nat.card H = Nat.card M :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hHcardiff : Nat.card H = 3 ^ (2 * k + 1) + 1 + 3 ^ (k + 1) ∨
      Nat.card H + 3 ^ (k + 1) = 3 ^ (2 * k + 1) + 1 := by
    rw [hHcard, hMcard, hWq]
    have hp3 : 3 ^ (k + 1) = 3 * 3 ^ k := (three_mul_pow_eq k).symm
    cases s with
    | false =>
      right
      rw [hp3]
      simp only [Bool.false_eq_true, if_false]
      rw [Nat.sub_add_cancel (three_pow_succ_le_q k hk)]
    | true =>
      left
      rw [hp3]
      simp
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥W') 2 (by rw [hW6]; norm_num)
  have hw2 : ((w : W') : X) * ((w : W') : X) = 1 := by
    have h : (w : W') ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    have := congrArg (fun z : ↥W' => (z : X)) h
    simpa [pow_two] using this
  have hwN : ((w : W') : X) ∈ normalizer (M : Set X) := by
    rw [hNM]
    exact Subgroup.mem_sup_right w.2
  let φ : MulAut ↥M := M.normalizerMonoidHom ⟨((w : W') : X), hwN⟩
  have hφinv : Function.Involutive φ := by
    intro y
    apply Subtype.ext
    have hw2' : ((w : W') : X) * ((w : W') : X) = 1 := hw2
    have hinv : ((w : W') : X)⁻¹ = ((w : W') : X) := inv_eq_of_mul_eq_one_right hw2'
    simp only [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [hinv]
    calc ((w : W') : X) * (((w : W') : X) * (y : X) * ((w : W') : X)) * ((w : W') : X)
        = (((w : W') : X) * ((w : W') : X)) * (y : X) *
            (((w : W') : X) * ((w : W') : X)) := by group
      _ = (y : X) := by rw [hw2']; simp
  have hφfpf : MonoidHom.FixedPointFree φ := by
    intro y hy
    apply Subtype.ext
    have hyeq : ((w : W') : X) * (y : X) * ((w : W') : X)⁻¹ = (y : X) := by
      have := congrArg Subtype.val hy
      simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    have hyC : (y : X) ∈ centralizer ({((w : W') : X)} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg (fun z => z * ((w : W') : X)) hyeq
      simpa [mul_assoc] using this.symm
    have hbot : (y : X) ∈ (⊥ : Subgroup X) := by
      rw [← hfpf ((w : W') : X) w.2 (by
        intro h1
        have h1' : (w : W') = 1 := Subtype.ext h1
        rw [h1', orderOf_one] at hw
        omega)]
      exact ⟨y.2, hyC⟩
    simpa using hbot
  have hcoe := hφfpf.coe_eq_inv_of_involutive hφinv
  have hinvM : ∀ m ∈ M, ((w : W') : X) * m * ((w : W') : X)⁻¹ = m⁻¹ := by
    intro m hm
    have h := congrFun hcoe ⟨m, hm⟩
    have := congrArg Subtype.val h
    simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  refine ⟨H, hBH, hHab, hHC, hHcardiff, (MulAut.conj g⁻¹) ((w : W') : X), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    rw [Subgroup.orderOf_coe, hw]
  · intro h hh
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hh
    have hmaps : ((MulAut.conj g⁻¹) : MulAut X).toMonoidHom (w : W') =
        (MulAut.conj g⁻¹) ((w : W') : X) := rfl
    rw [show (MulAut.conj g⁻¹).toMonoidHom m = (MulAut.conj g⁻¹) m from rfl]
    rw [show ((MulAut.conj g⁻¹) ((w : W') : X))⁻¹ =
        (MulAut.conj g⁻¹) ((w : W') : X)⁻¹ from (map_inv _ _).symm]
    rw [← map_mul, ← map_mul]
    rw [hinvM m hmM]
    exact map_inv _ _

theorem ree_centralizer_inf_cases
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X) {k : ℕ}
    (hmod : CFSG.Blueprint.LieModel X .twistedG2 0 3 (2 * k + 1)) {T M : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTM : T ≤ M) (hNM : normalizer (T : Set X) ≤ M)
    (hidx : ∀ N : Subgroup ↥M, N.index ≠ 2) {j : X} (hjM : j ∈ M) (hj : orderOf j = 2) :
    (∃ P : Sylow 2 X, j ∈ (P : Subgroup X) ∧ (P : Subgroup X) ≤ M ∧
      Nat.card ↥(centralizer ({j} : Set X) ⊓ M) = 24 ∧
      centralizer ({j} : Set X) ⊓ M ≤ normalizer ((P : Subgroup X) : Set X)) ∨
    ∃ m : ℕ, 3 ≤ m ∧ m ∣ 2 * k + 1 ∧
      Nat.card M = (3 ^ m) ^ 3 * ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1) := by
  classical
  obtain ⟨P, hjP, hPM, hNPM⟩ := exists_sylow_two_normalizer_le hT hTM hNM hjM hj
  obtain ⟨J, hJp, hJf, hJt⟩ := ree_exists_jtHyp hXs hmod hj
  have hp : J.p ≠ 2 := by rw [hJp]; norm_num
  have hjP' : J.t ∈ (P : Subgroup X) := by rw [hJt]; exact hjP
  let V : Subgroup X := (P : Subgroup X) ⊓ J.F
  have hVF : V ≤ J.F := inf_le_right
  have hV : IsKleinFour V := J.isKleinFour_inf_F hp P hjP'
  have hJmod : J.p ^ J.f % 8 = 3 ∨ J.p ^ J.f % 8 = 5 := by
    simpa only [CFSG.Walter.JT.JTHyp.q_eq] using J.mod_eight hp
  let N₀ : Subgroup X := J.F ⊓ normalizer (V : Set X)
  have hN₀card : Nat.card N₀ = 12 := by
    simpa [N₀, V] using (J.facts hp).card_inf_normalizer hJmod hVF hV
  have hN₀M : N₀ ≤ M := by
    intro y hy
    exact hNPM (J.mem_normalizer_sylow_of_mem_F P hjP' hy.1 hy.2)
  have hN₀MF : N₀ ≤ M ⊓ J.F := fun y hy => ⟨hN₀M hy, hy.1⟩
  have hcard_sub : Nat.card ↥(M.subgroupOf J.F) = Nat.card ↥(M ⊓ J.F) := by
    have h := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := M ⊓ J.F) (K := J.F) inf_le_right).toEquiv
    rwa [Subgroup.inf_subgroupOf_right] at h
  let R : Subgroup (PSL(2, GaloisField J.p J.f)) := (M.subgroupOf J.F).map J.iso.toMonoidHom
  have hRcardMF : Nat.card R = Nat.card ↥(M ⊓ J.F) := by
    rw [show Nat.card R = Nat.card ↥((M.subgroupOf J.F).map J.iso.toMonoidHom) from rfl,
      Subgroup.card_map_of_injective J.iso.injective, hcard_sub]
  have h12 : 12 ∣ Nat.card R := by
    rw [hRcardMF, ← hN₀card]
    exact Subgroup.card_dvd_of_le hN₀MF
  have hfodd : Odd J.f := by
    rw [hJf]
    exact ⟨k, by ring⟩
  rcases psl2_three_subgroup_cases (p := J.p) hJp hfodd R h12 with hR12 | ⟨m, hm3, hmdvd, ⟨eR⟩⟩
  · left
    have hMFcard : Nat.card ↥(M ⊓ J.F) = 12 := by rw [← hRcardMF]; exact hR12
    have hMFN₀ : M ⊓ J.F = N₀ :=
      (Subgroup.eq_of_le_of_card_ge hN₀MF (by rw [hMFcard, hN₀card])).symm
    have hj2 : j * j = 1 := by rw [← pow_two, ← hj, pow_orderOf_eq_one]
    have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj2
    have hCj : centralizer ({j} : Set X) ⊓ M = Subgroup.zpowers j ⊔ (J.F ⊓ M) := by
      have hce : centralizer ({j} : Set X) = Subgroup.zpowers j ⊔ J.F := by
        rw [← hJt]
        exact J.centralizer_eq
      rw [hce]
      have hcomm : ∀ a ∈ Subgroup.zpowers j, ∀ b ∈ J.F, a * b = b * a := by
        intro a ha b hb
        have hjc : j ∈ Subgroup.centralizer (J.F : Set X) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have h := J.commute_of_mem_F hy
          rwa [hJt] at h
        have hale : a ∈ Subgroup.centralizer (J.F : Set X) :=
          Subgroup.zpowers_le.mpr hjc ha
        exact (Subgroup.mem_centralizer_iff.mp hale b hb).symm
      apply le_antisymm
      · intro x hx
        obtain ⟨hxsup, hxM⟩ := hx
        obtain ⟨a, ha, b, hb, hab⟩ :=
          CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
            (A := Subgroup.zpowers j) (B := J.F) hcomm hxsup
        have haM : a ∈ M := Subgroup.zpowers_le.mpr hjM ha
        have hbM : b ∈ M := by
          have h : a⁻¹ * (a * b) ∈ M := M.mul_mem (M.inv_mem haM) (hab ▸ hxM)
          simpa using h
        rw [← hab]
        exact Subgroup.mul_mem_sup ha ⟨hb, hbM⟩
      · intro x hx
        obtain ⟨a, ha, b, hb, hab⟩ :=
          CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
            (A := Subgroup.zpowers j) (B := J.F ⊓ M)
            (fun a ha b hb => hcomm a ha b hb.1) hx
        rw [← hab]
        exact ⟨Subgroup.mul_mem_sup ha hb.1,
          M.mul_mem (Subgroup.zpowers_le.mpr hjM ha) hb.2⟩
    have hcardK : Nat.card ↥(J.F ⊓ M) = 12 := by
      rw [inf_comm, hMFN₀, hN₀card]
    have hdisj : Disjoint (Subgroup.zpowers j) (J.F ⊓ M) := by
      rw [disjoint_iff]
      have hdvd : Nat.card ↥(Subgroup.zpowers j ⊓ (J.F ⊓ M)) ∣ 2 := by
        have h := Subgroup.card_dvd_of_le
          (H := Subgroup.zpowers j ⊓ (J.F ⊓ M)) (K := Subgroup.zpowers j) inf_le_left
        rwa [Nat.card_zpowers, hj] at h
      have hle : Nat.card ↥(Subgroup.zpowers j ⊓ (J.F ⊓ M)) ≤ 2 :=
        Nat.le_of_dvd (by norm_num) hdvd
      have hne : Nat.card ↥(Subgroup.zpowers j ⊓ (J.F ⊓ M)) ≠ 2 := by
        intro h2
        have heq : Subgroup.zpowers j ⊓ (J.F ⊓ M) = Subgroup.zpowers j :=
          Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers j ⊓ (J.F ⊓ M))
            (K := Subgroup.zpowers j) inf_le_left (by rw [h2, Nat.card_zpowers, hj])
        have hmem : j ∈ Subgroup.zpowers j ⊓ (J.F ⊓ M) := by
          rw [heq]
          exact Subgroup.mem_zpowers j
        have : J.t ∈ J.F := by rw [hJt]; exact hmem.2.1
        exact J.t_not_mem this
      have hpos : 0 < Nat.card ↥(Subgroup.zpowers j ⊓ (J.F ⊓ M)) := Nat.card_pos
      have h1 : Nat.card ↥(Subgroup.zpowers j ⊓ (J.F ⊓ M)) = 1 := by omega
      exact Subgroup.card_eq_one.mp h1
    have hnorm : Subgroup.zpowers j ≤ Subgroup.normalizer ((J.F ⊓ M) : Set X) := by
      refine Subgroup.zpowers_le.mpr
        (CFSG.Walter.JT.mem_normalizer_of_conj_mem (H := J.F ⊓ M) ?_)
      intro x hx
      refine ⟨?_, M.mul_mem (M.mul_mem hjM hx.2) (M.inv_mem hjM)⟩
      have hmem : j * x * j⁻¹ = x := by
        have hc : x * j = j * x := by
          have h := J.commute_of_mem_F hx.1
          rwa [hJt] at h
        calc j * x * j⁻¹ = x * j * j⁻¹ := by rw [hc]
          _ = x := by rw [mul_inv_cancel_right]
      rw [hmem]
      exact hx.1
    have hcard24 : Nat.card ↥(centralizer ({j} : Set X) ⊓ M) = 24 := by
      rw [hCj]
      rw [CFSG.Walter.JT.card_sup_eq_mul_of_disjoint (H := Subgroup.zpowers j) (K := J.F ⊓ M)
        hnorm hdisj]
      rw [Nat.card_zpowers, hj, hcardK]
    have hle : centralizer ({j} : Set X) ⊓ M ≤ normalizer ((P : Subgroup X) : Set X) := by
      rw [hCj]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.le_normalizer hjP
      · intro y hy
        have hyN₀ : y ∈ N₀ := by
          rw [← hMFN₀, inf_comm]
          exact hy
        exact J.mem_normalizer_sylow_of_mem_F P hjP' hyN₀.1 hyN₀.2
    exact ⟨P, hjP, hPM, hcard24, hle⟩
  · right
    let e : ↥(M.subgroupOf J.F) ≃* PSL(2, GaloisField J.p m) :=
      (Subgroup.equivMapOfInjective (M.subgroupOf J.F) J.iso.toMonoidHom J.iso.injective).trans eR
    have hm5 : 5 < J.p ^ m := by
      rw [hJp]
      calc 5 < 3 ^ 3 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    obtain ⟨JM, hJMp, hJMf, -⟩ :=
      exists_jtHyp_subgroup J M (by rw [hJt]; exact hjM) hidx hm5 e
    refine ⟨m, hm3, ?_, ?_⟩
    · rw [← hJf]
      exact hmdvd
    · have hcard := jtHyp_card_eq_of_three JM (hJMp.trans hJp)
      have hJMq : JM.q = 3 ^ m := by
        rw [show JM.q = JM.p ^ JM.f from rfl, hJMp, hJp, hJMf]
      rw [hJMq] at hcard
      exact hcard

theorem uc2_10_7OddReeSevenInnerPhi6_holds :
    UC2_10_7OddReeSevenInnerPhi6 := by
  intro X _ _ hXs f hmod h7 T B M hT hBT hB7 hTM hBM hstar
  obtain ⟨-, -, -, -, ⟨k, rfl⟩, hf3⟩ := CFSG.Blueprint.LieModel.admissible hmod
  have hk : 1 ≤ k := by omega
  obtain ⟨hT8, hCT, hidx21⟩ := ree_sylow_two_facts hXs hmod hT
  have hBC : ¬ B ≤ centralizer (T : Set X) := by
    intro h
    have h78 := Subgroup.card_dvd_of_le (hCT ▸ h)
    rw [hB7, hT8] at h78
    norm_num at h78
  have hNM : normalizer (T : Set X) ≤ M :=
    normalizer_le_of_index_eq_twentyOne hT8 hidx21 hBT hB7 hTM hBM hstar
  have hN168 : Nat.card (normalizer (T : Set X)) = 168 := by
    have h := Subgroup.index_mul_card (H := T.subgroupOf (normalizer (T : Set X)))
    have hcard : Nat.card ↥(T.subgroupOf (normalizer (T : Set X))) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (K := normalizer (T : Set X))
        Subgroup.le_normalizer).toEquiv, hT8]
    rw [hidx21, hcard] at h
    omega
  have hidxM : ∀ N : Subgroup ↥M, N.index ≠ 2 :=
    index_ne_two_of_fpf hT hT8 hBT hB7 hBC hTM hBM
  have hTe : ∀ x ∈ T, x * x = 1 := by
    have hdvd : ¬ 2 ∣ T.index := by
      have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
      rwa [Subgroup.relIndex_top_right] at h
    let S : Sylow 2 X := hT.isPGroup.toSylow hdvd
    have hSco : (S : Subgroup X) = T := IsPGroup.toSylow_coe hT.isPGroup hdvd
    have hgen := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_ReeSylowGeneration_holds
      X (3 ^ (2 * k + 1)) k ⟨k, rfl, hmod⟩ rfl hk
    intro x hx
    have hx' : x ∈ (S : Subgroup X) := hSco ▸ hx
    have hE : CFSG.Open.IsElemAbelian 2 (S : Subgroup X) := (hgen.2.2 S).1
    have hpow : x ^ 2 = 1 := hE.2 x hx'
    simpa [pow_two] using hpow
  obtain ⟨H, hBH, hHab, hHC, hHcard, u, hu, huinv⟩ :=
    ree_exists_hall_torus hXs hk hmod h7 hB7
  have hCB : centralizer (B : Set X) = H := by
    obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr h
      rw [hbot, Subgroup.card_bot] at hB7
      omega
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ centralizer ({b₀} : Set X) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hx b₀ hb₀B).symm
      rwa [hHC b₀ (hBH hb₀B) hb₀1] at hxC
    · intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      exact (hHab x hx b (hBH hb)).symm
  have hHM : H ≤ M := by
    intro h hh
    apply hstar h
    intro b hb
    have hbh : h * b = b * h := hHab h hh b (hBH hb)
    have hb' : h⁻¹ * b * h = b := by
      calc h⁻¹ * b * h = h⁻¹ * (b * h) := by rw [mul_assoc]
        _ = h⁻¹ * (h * b) := by rw [hbh]
        _ = b := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [hb']
    exact hBM hb
  have huM : u ∈ M := by
    have huinv' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by
      rw [← pow_two, ← hu, pow_orderOf_eq_one])
    apply hstar u
    intro b hb
    have h1 : u⁻¹ * b * u = b⁻¹ := by
      simpa [huinv'] using huinv b (hBH hb)
    rw [h1]
    exact hBM (B.inv_mem hb)
  have hHodd : Odd (Nat.card H) := by
    have hqodd : Odd (3 ^ (2 * k + 1)) := Odd.pow (n := 2 * k + 1) (by norm_num : Odd 3)
    have hpodd : Odd (3 ^ (k + 1)) := Odd.pow (n := k + 1) (by norm_num : Odd 3)
    rcases hHcard with h | h
    · rw [h]
      exact (hqodd.add_odd odd_one).add_odd hpodd
    · have hle : 3 ^ (k + 1) ≤ 3 ^ (2 * k + 1) + 1 := by
        have h2 : 3 ^ (k + 1) ≤ 3 ^ (2 * k + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hq1even : Even (3 ^ (2 * k + 1) + 1) := hqodd.add_odd odd_one
      have hH : Nat.card H = 3 ^ (2 * k + 1) + 1 - 3 ^ (k + 1) := by omega
      rw [hH]
      exact Nat.Even.sub_odd hle hq1even hpodd
  by_contra hMtop
  have hcases : ∀ j ∈ M, orderOf j = 2 → ∃ P : Sylow 2 X, j ∈ (P : Subgroup X) ∧
      (P : Subgroup X) ≤ M ∧ Nat.card ↥(centralizer ({j} : Set X) ⊓ M) = 24 ∧
      centralizer ({j} : Set X) ⊓ M ≤ normalizer ((P : Subgroup X) : Set X) := by
    intro j hjM hj
    rcases ree_centralizer_inf_cases hXs hmod hT hTM hNM hidxM hjM hj with
      h | ⟨m, hm3, hmdvd, hMcard⟩
    · exact h
    · exfalso
      have hdvdHM : Nat.card H ∣ Nat.card M := Subgroup.card_dvd_of_le hHM
      have hdvd : Nat.card H ∣ (3 ^ m) ^ 3 * ((3 ^ m) ^ 3 + 1) * (3 ^ m - 1) := by
        rwa [hMcard] at hdvdHM
      have hm : m = 2 * k + 1 := phi6_torus_eq_of_dvd hk hm3 hmdvd hHcard hdvd
      have hcardX : Nat.card X = (3 ^ (2 * k + 1)) ^ 3 * ((3 ^ (2 * k + 1)) ^ 3 + 1) *
          (3 ^ (2 * k + 1) - 1) := by
        have hree : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * k + 1) :=
          (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
        obtain ⟨-, -, -, -, hcard⟩ :=
          CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hree
        rw [hcard]
        simp [CFSG.Open.ordRee]
      have hcardM : Nat.card M = Nat.card X := by
        rw [hMcard, hm, hcardX]
      exact hMtop (Subgroup.card_eq_iff_eq_top M |>.mp hcardM)
  obtain ⟨S, hS, hTI⟩ := tiCountHyp_subgroup hT hT8 hTe hTM hN168 hNM hcases
  have hX7 : Nat.card (B.subgroupOf M) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, hB7]
  have hXN : B.subgroupOf M ≤ normalizer ((S : Subgroup ↥M) : Set ↥M) := by
    rw [hS]
    intro x hx
    refine CFSG.Walter.JT.mem_normalizer_of_conj_mem (H := T.subgroupOf M) ?_
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hb : (x : X) ∈ normalizer (T : Set X) := hBT hx
    have h := (Subgroup.mem_normalizer_iff.mp hb (y : X)).mp hy
    simpa using h
  have hCMcard : Nat.card (centralizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M)) =
      Nat.card H := by
    rw [card_centralizer_subgroupOf hBM, hCB, inf_eq_left.mpr hHM]
  have hCXo : Odd (Nat.card (centralizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M))) := by
    rw [hCMcard]
    exact hHodd
  have hu' : ∃ u' : ↥M, orderOf u' = 2 ∧
      ∀ c ∈ centralizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M),
        u' * c * u'⁻¹ = c⁻¹ := by
    refine ⟨⟨u, huM⟩, ?_, ?_⟩
    · rw [← Subgroup.orderOf_coe (⟨u, huM⟩ : ↥M)]
      exact hu
    · intro c hc
      apply Subtype.ext
      have hcH : (c : X) ∈ H := by
        have hc' : (c : X) ∈ centralizer (B : Set X) := by
          refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
          have hbM : b ∈ M := hBM hb
          have hx : (⟨b, hbM⟩ : ↥M) ∈ B.subgroupOf M := Subgroup.mem_subgroupOf.mpr hb
          have h := Subgroup.mem_centralizer_iff.mp hc ⟨b, hbM⟩ hx
          simpa using congrArg (fun z : ↥M => (z : X)) h
        rwa [hCB] at hc'
      have h := huinv (c : X) hcH
      simpa using h
  have hres := card_centralizer_dvd_of_ti hTI hX7 hXN hCXo hu'
  rw [hCMcard] at hres
  exact phi6_torus_not_dvd hk hHcard hres

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
