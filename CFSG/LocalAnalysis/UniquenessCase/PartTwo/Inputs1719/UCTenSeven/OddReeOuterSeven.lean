module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReePhi6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup

private lemma centralizer_zpowers_eq_subgroup {G : Type} [Group G] (a : G) :
    Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx a (Subgroup.mem_zpowers a)).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hxa : a ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
    have hbx := Subgroup.zpowers_le.mpr hxa hb
    rwa [Subgroup.mem_centralizer_singleton_iff] at hbx

private lemma inverts_of_le_centralizer {G : Type} [Group G] {H B : Subgroup G} {y u : G}
    (hBH : B ≤ H) (hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hCB : Subgroup.centralizer (B : Set G) = H)
    (hinvB : ∀ x ∈ B, y * x * y⁻¹ = x⁻¹)
    (hu : u⁻¹ = u) (huinvH : ∀ h ∈ H, u * h * u⁻¹ = h⁻¹) :
    ∀ h ∈ H, y * h * y⁻¹ = h⁻¹ := by
  have hyu : y * u ∈ H := by
    rw [← hCB]
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : y * b * y⁻¹ = b⁻¹ := hinvB b hb
    have h2 : u * b * u⁻¹ = b⁻¹ := huinvH b (hBH hb)
    have hconj : (y * u) * b * (y * u)⁻¹ = b := by
      calc (y * u) * b * (y * u)⁻¹ = y * (u * b * u⁻¹) * y⁻¹ := by group
        _ = y * b⁻¹ * y⁻¹ := by rw [h2]
        _ = (y * b * y⁻¹)⁻¹ := by group
        _ = b := by rw [h1, inv_inv]
    have hxb : (y * u) * b = b * (y * u) := by
      have h := congrArg (fun t => t * (y * u)) hconj
      simpa [mul_assoc] using h
    exact hxb.symm
  intro h hh
  have h3 : u⁻¹ * h * u = h⁻¹ := by
    rw [hu]
    simpa [hu] using huinvH h hh
  calc y * h * y⁻¹ = (y * u) * (u⁻¹ * h * u) * (y * u)⁻¹ := by group
    _ = (y * u) * h⁻¹ * (y * u)⁻¹ := by rw [h3]
    _ = h⁻¹ := by
        have hc : (y * u) * h⁻¹ = h⁻¹ * (y * u) := hHab (y * u) hyu h⁻¹ (H.inv_mem hh)
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]

private lemma inverts_centralizer_subgroupOf {G : Type} [Group G] {M B H : Subgroup G} {u : G}
    (hBM : B ≤ M) (hBH : B ≤ H)
    (hHab : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hCB : Subgroup.centralizer (B : Set G) = H)
    (hu : u⁻¹ = u) (huinvH : ∀ h ∈ H, u * h * u⁻¹ = h⁻¹)
    {y' : ↥M} (hinvB : ∀ x ∈ B.subgroupOf M, y' * x * y'⁻¹ = x⁻¹) :
    ∀ c ∈ Subgroup.centralizer ((B.subgroupOf M : Subgroup ↥M) : Set ↥M),
      y' * c * y'⁻¹ = c⁻¹ := by
  have hinvX : ∀ x ∈ B, (y' : G) * x * (y' : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hxm : x ∈ M := hBM hx
    have hx' : (⟨x, hxm⟩ : ↥M) ∈ B.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
    have h := congrArg (fun t : ↥M => (t : G)) (hinvB ⟨x, hxm⟩ hx')
    simpa using h
  have hHinv := inverts_of_le_centralizer hBH hHab hCB hinvX hu huinvH
  intro c hc
  apply Subtype.ext
  have hcH : (c : G) ∈ H := by
    rw [← hCB]
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbm : b ∈ M := hBM hb
    have hb' : (⟨b, hbm⟩ : ↥M) ∈ B.subgroupOf M := Subgroup.mem_subgroupOf.mpr hb
    exact congrArg (fun t : ↥M => (t : G))
      (Subgroup.mem_centralizer_iff.mp hc ⟨b, hbm⟩ hb')
  have h := hHinv (c : G) hcH
  simpa using h

private lemma not_343_dvd_card_ree :
    ¬ 7 ^ 3 ∣ (3 ^ 7) ^ 3 * ((3 ^ 7) ^ 3 + 1) * (3 ^ 7 - 1) := by
  norm_num

private lemma sylow_seven_commutative {X : Type} [Group X] [Finite X] {M : Subgroup X}
    (hcardX : Nat.card X = (3 ^ 7) ^ 3 * ((3 ^ 7) ^ 3 + 1) * (3 ^ 7 - 1))
    {Q : Sylow 7 ↥M} (h49 : 49 ∣ Nat.card ↥Q) :
    Nat.card ↥Q = 49 ∧ ∀ a b : ↥Q, a * b = b * a := by
  have h7cubed : ¬ 7 ^ 3 ∣ Nat.card X := by
    rw [hcardX]
    exact not_343_dvd_card_ree
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥Q = 7 ^ k := (Sylow.isPGroup' Q).exists_card_eq
  have hQX : Nat.card ↥Q ∣ Nat.card X :=
    (Subgroup.card_subgroup_dvd_card (Q : Subgroup ↥M)).trans (Subgroup.card_subgroup_dvd_card M)
  have h2k : 2 ≤ k := by
    rw [hk] at h49
    have hle : 49 ≤ 7 ^ k := Nat.le_of_dvd (by positivity) (by simpa using h49)
    by_contra h
    have hk1 : k ≤ 1 := by omega
    have hlittle : 7 ^ k ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    norm_num at hlittle
    omega
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ k := by omega
    have hdvd3 : 7 ^ 3 ∣ 7 ^ k := Nat.pow_dvd_pow 7 h3
    exact h7cubed (dvd_trans hdvd3 (hk ▸ hQX))
  have hQcard : Nat.card ↥Q = 49 := by
    have hk2' : k = 2 := by omega
    rw [hk, hk2']
    norm_num
  refine ⟨hQcard, fun a b => ?_⟩
  exact IsPGroup.commutative_of_card_eq_prime_sq (G := ↥Q) (p := 7)
    (by rw [hQcard]; norm_num) a b

theorem ree_seven_eq_top_of_sq_dvd
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X)
    (hmod : CFSG.Blueprint.LieModel X .twistedG2 0 3 7) {T M : Subgroup X}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTM : T ≤ M)
    (hNM : normalizer (T : Set X) ≤ M) (hidx : ∀ N : Subgroup ↥M, N.index ≠ 2)
    (h49 : 49 ∣ Nat.card M) : M = ⊤ := by
  classical
  obtain ⟨hT8, hCT, hidx21⟩ := ree_sylow_two_facts hXs hmod hT
  have hN168 : Nat.card (normalizer (T : Set X)) = 168 := by
    have h := Subgroup.index_mul_card (H := T.subgroupOf (normalizer (T : Set X)))
    have hcard : Nat.card ↥(T.subgroupOf (normalizer (T : Set X))) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (K := normalizer (T : Set X))
        Subgroup.le_normalizer).toEquiv, hT8]
    rw [hidx21, hcard] at h
    omega
  have hTe : ∀ x ∈ T, x * x = 1 := by
    have hdvd : ¬ 2 ∣ T.index := by
      have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
      rwa [Subgroup.relIndex_top_right] at h
    let S : Sylow 2 X := hT.isPGroup.toSylow hdvd
    have hSco : (S : Subgroup X) = T := IsPGroup.toSylow_coe hT.isPGroup hdvd
    have hgen := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_ReeSylowGeneration_holds
      X (3 ^ 7) 3 ⟨3, by norm_num, hmod⟩ (by norm_num) (by norm_num)
    intro x hx
    have hx' : x ∈ (S : Subgroup X) := hSco ▸ hx
    have hE : CFSG.Open.IsElemAbelian 2 (S : Subgroup X) := (hgen.2.2 S).1
    have hpow : x ^ 2 = 1 := hE.2 x hx'
    simpa [pow_two] using hpow
  have hcardX : Nat.card X = (3 ^ 7) ^ 3 * ((3 ^ 7) ^ 3 + 1) * (3 ^ 7 - 1) := by
    have hree : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 7 :=
      (hmod.reeTitsModel (by simp [CFSG.Blueprint.reeTitsTags])).2
    obtain ⟨-, -, -, -, hcard⟩ :=
      CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hree
    rw [hcard]
    simp [CFSG.Open.ordRee]
  by_contra hMtop
  have hcases : ∀ j ∈ M, orderOf j = 2 → ∃ P : Sylow 2 X, j ∈ (P : Subgroup X) ∧
      (P : Subgroup X) ≤ M ∧ Nat.card ↥(centralizer ({j} : Set X) ⊓ M) = 24 ∧
      centralizer ({j} : Set X) ⊓ M ≤ normalizer ((P : Subgroup X) : Set X) := by
    intro j hjM hj
    rcases ree_centralizer_inf_cases (k := 3) hXs hmod hT hTM hNM hidx hjM hj with
      h | ⟨m, hm3, hmdvd, hMcard⟩
    · exact h
    · exfalso
      have hm : m = 7 := by
        have h1 : m ∣ 7 := by simpa using hmdvd
        rcases (Nat.dvd_prime Nat.prime_seven).mp h1 with h2 | h2
        · omega
        · exact h2
      have hcardM : Nat.card M = Nat.card X := by
        rw [hMcard, hm, hcardX]
      exact hMtop (Subgroup.card_eq_iff_eq_top M |>.mp hcardM)
  obtain ⟨S, hS, hTI⟩ := tiCountHyp_subgroup hT hT8 hTe hTM hN168 hNM hcases
  have h7N : 7 ∣ Nat.card ↥(normalizer (T : Set X)) := by
    rw [hN168]; norm_num
  have hfact : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨x7, hx7ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(normalizer (T : Set X))) 7 h7N
  set X7 : Subgroup X := Subgroup.zpowers (x7 : X) with hX7def
  have hX7card : Nat.card X7 = 7 := by
    rw [hX7def, Nat.card_zpowers, Subgroup.orderOf_coe, hx7ord]
  have hX7N : X7 ≤ normalizer (T : Set X) := by
    rw [hX7def, Subgroup.zpowers_le]
    exact x7.2
  have hX7M : X7 ≤ M := hX7N.trans hNM
  have hX7'card : Nat.card (X7.subgroupOf M) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX7M).toEquiv, hX7card]
  have hX7'N : X7.subgroupOf M ≤ normalizer ((S : Subgroup ↥M) : Set ↥M) := by
    rw [hS]
    intro x hx
    refine CFSG.Walter.JT.mem_normalizer_of_conj_mem (H := T.subgroupOf M) ?_
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hb : (x : X) ∈ normalizer (T : Set X) := hX7N hx
    have h := (Subgroup.mem_normalizer_iff.mp hb (y : X)).mp hy
    simpa using h
  obtain ⟨H, hX7H, hHab, hHC, hHcard, u, hu2, huinv⟩ :=
    ree_exists_hall_torus (k := 3) hXs (by norm_num) hmod (by norm_num) (B := X7) hX7card
  have hx7H : (x7 : X) ∈ H := by
    apply hX7H
    rw [hX7def]
    exact Subgroup.mem_zpowers _
  have hx7ne : (x7 : X) ≠ 1 := by
    intro h1
    have h2 : orderOf ((x7 : X)) = 1 := by rw [h1, orderOf_one]
    rw [Subgroup.orderOf_coe, hx7ord] at h2
    norm_num at h2
  have hCX7 : centralizer (X7 : Set X) = H := by
    rw [hX7def, centralizer_zpowers_eq_subgroup]
    exact hHC (x7 : X) hx7H hx7ne
  have hHodd : Odd (Nat.card H) := by
    rcases hHcard with h | h
    · rw [h]; norm_num
    · have h2 : Nat.card H = 2107 := by
        have h' := h
        norm_num at h'
        omega
      rw [h2]; norm_num
  have hCXo : Odd (Nat.card (centralizer ((X7.subgroupOf M : Subgroup ↥M) : Set ↥M))) := by
    rw [card_centralizer_subgroupOf hX7M]
    refine Odd.of_dvd_nat hHodd (Subgroup.card_dvd_of_le ?_)
    rw [hCX7]
    exact inf_le_left
  have hYcard := hTI.card_inv_outside
  have hpos : Set.ncard {y : ↥M | orderOf y = 2 ∧
      y ∉ normalizer ((S : Subgroup ↥M) : Set ↥M)} ≠ 0 := by
    intro h0
    rw [h0] at hYcard
    have h168 : Nat.card ↥M = 168 := by
      have h := hYcard
      omega
    have h49' : 49 ∣ (168 : ℕ) := by rw [← h168]; exact h49
    norm_num at h49'
  obtain ⟨y, hy2, hyN⟩ := Set.nonempty_of_ncard_ne_zero hpos
  obtain ⟨g, hgN, hginv⟩ := exists_conj_inverts_of_ti hTI hX7'card hX7'N hCXo hy2 hyN
  set y' : ↥M := g⁻¹ * y * g with hy'def
  have hy'2 : orderOf y' = 2 := by
    rw [hy'def]
    have hconj : g⁻¹ * y * g = MulAut.conj g⁻¹ y := by rw [MulAut.conj_apply, inv_inv]
    rw [hconj, MulEquiv.orderOf_eq, hy2]
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, ← hu2, pow_orderOf_eq_one])
  have hYinv : ∀ c ∈ centralizer ((X7.subgroupOf M : Subgroup ↥M) : Set ↥M),
      y' * c * y'⁻¹ = c⁻¹ :=
    inverts_centralizer_subgroupOf hX7M hX7H hHab hCX7 hu huinv
      (fun x hx => by rw [hy'def]; exact hginv x hx)
  have hres : Nat.card (centralizer ((X7.subgroupOf M : Subgroup ↥M) : Set ↥M)) ∣ 168 :=
    card_centralizer_dvd_of_ti hTI hX7'card hX7'N hCXo ⟨y', hy'2, hYinv⟩
  have hX7'P : IsPGroup 7 (X7.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [hX7'card, pow_one])
  obtain ⟨Q, hX7'Q⟩ := IsPGroup.exists_le_sylow hX7'P
  have h49Q : 49 ∣ Nat.card ↥Q := by
    have h : 7 ^ 2 ∣ Nat.card ↥Q := Sylow.pow_dvd_card_of_pow_dvd_card Q (by simpa using h49)
    simpa using h
  obtain ⟨hQcard, hQcomm⟩ := sylow_seven_commutative hcardX h49Q
  have hQle : (Q : Subgroup ↥M) ≤ centralizer ((X7.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcomm := congrArg (fun t : ↥Q => (t : ↥M)) (hQcomm ⟨x, hX7'Q hx⟩ ⟨q, hq⟩)
    simpa using hcomm
  have h49dvd : 49 ∣ Nat.card (centralizer ((X7.subgroupOf M : Subgroup ↥M) : Set ↥M)) :=
    hQcard ▸ Subgroup.card_dvd_of_le hQle
  have hbad : 49 ∣ 168 := dvd_trans h49dvd hres
  norm_num at hbad

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
