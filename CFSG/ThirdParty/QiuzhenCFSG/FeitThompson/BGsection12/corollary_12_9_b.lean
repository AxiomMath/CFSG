module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_9_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- In a finite cyclic group, any two subgroups of the same prime order are equal. -/
public lemma CFSG.unique_subgroup_of_prime_order_in_cyclic_pre
    {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} [Fact p.Prime] (H K : Subgroup G)
    (hH : Nat.card H = p) (hK : Nat.card K = p) : H = K := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := Nat.Prime.pos hp_prime
  have hp_dvd_cardG : p ∣ Nat.card G := by
    rw [← hH]; exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := G)
  have hg_order : orderOf g = Nat.card G := by
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x; have hx := hg x
    rcases ((Submonoid.mem_powers_iff _ _).mp hx) with ⟨k, hk⟩
    rw [← hk]; exact ⟨(k : ℤ), by simp⟩
  set d := Nat.card G / p with hd_def
  have hd_mul : d * p = Nat.card G := Nat.div_mul_cancel hp_dvd_cardG
  have hd_dvd : d ∣ Nat.card G := by rw [← hd_mul]; exact ⟨p, rfl⟩
  have hd_pos : 0 < d := by
    by_contra hd0; have hd0' : d = 0 := Nat.eq_zero_of_not_pos hd0
    rw [hd0', zero_mul] at hd_mul
    have hcard_pos : 0 < Nat.card G := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    omega
  set g0 := g ^ d with hg0_def
  have hg0_order : orderOf g0 = p := by
    rw [hg0_def, orderOf_pow, hg_order]
    have h_gcd : Nat.gcd (Nat.card G) d = d := Nat.gcd_eq_right hd_dvd
    rw [h_gcd]; exact Nat.div_eq_of_eq_mul_right hd_pos hd_mul.symm
  let G0 : Subgroup G := Subgroup.zpowers g0
  have hG0_card : Nat.card G0 = p := by rw [Nat.card_zpowers, hg0_order]
  have h_eq_G0 (L : Subgroup G) (hL : Nat.card L = p) : L = G0 := by
    have hL_ne_bot : L ≠ ⊥ := by
      intro hbot
      have hcard1 : Nat.card L = 1 := by
        simp [hbot]
      rw [hL] at hcard1; exact hp_prime.ne_one hcard1
    haveI : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL_ne_bot
    obtain ⟨h, hh⟩ := IsCyclic.exists_monoid_generator (α := L)
    have hh_order_L : orderOf (h : L) = p := by
      have h_eq : orderOf (h : L) = Nat.card L :=
        orderOf_eq_card_of_forall_mem_zpowers (by
          intro x; have hx := hh x
          rcases ((Submonoid.mem_powers_iff _ _).mp hx) with ⟨n, hn⟩
          rw [← hn]; exact ⟨(n : ℤ), by simp⟩)
      rw [hL] at h_eq; exact h_eq
    have hh_order_G : orderOf (h : G) = p := by
      rw [Subgroup.orderOf_coe (h : L), hh_order_L]
    have hh_mem : (h : G) ∈ Submonoid.powers g := hg (h : G)
    rcases ((Submonoid.mem_powers_iff _ _).mp hh_mem) with ⟨k, hk⟩
    rw [← hk] at hh_order_G; rw [orderOf_pow, hg_order] at hh_order_G
    set gk := Nat.gcd (Nat.card G) k with hgk_def
    have hgk_dvd_N : gk ∣ Nat.card G := Nat.gcd_dvd_left _ _
    have hN_eq_gk_mul_p : Nat.card G = gk * p := by
      calc
        Nat.card G = gk * (Nat.card G / gk) := (Nat.mul_div_cancel' hgk_dvd_N).symm
        _ = gk * p := by rw [hh_order_G]
    have hgk_eq_d : gk = d := by
      have h_eq : gk * p = d * p := by rw [← hN_eq_gk_mul_p, hd_mul]
      apply Nat.eq_of_mul_eq_mul_right hp_pos
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq
    have hd_dvd_k : d ∣ k := by rw [← hgk_eq_d]; exact Nat.gcd_dvd_right _ _
    rcases hd_dvd_k with ⟨m, hm⟩
    have h_mem_G0 : (h : G) ∈ G0 := by
      rw [← hk, hm, pow_mul, ← hg0_def]
      exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by simp⟩
    have hL_le_G0 : L ≤ G0 := by
      intro x hx
      have hx_mem : (⟨x, hx⟩ : L) ∈ Submonoid.powers (h : L) := hh ⟨x, hx⟩
      rcases ((Submonoid.mem_powers_iff _ _).mp hx_mem) with ⟨n, hn⟩
      have hx_eq : x = (h : G) ^ n := by simpa using congrArg Subtype.val hn.symm
      rw [hx_eq]; exact Subgroup.pow_mem G0 h_mem_G0 n
    apply Subgroup.eq_of_le_of_card_ge hL_le_G0
    rw [hG0_card, hL]
  exact (h_eq_G0 H hH).trans (h_eq_G0 K hK).symm

/-- Corollary 12.9(b). -/
public theorem CFSG.corollary_12_9_b
    {M E E₁₂ E₁ E₂ E₃ A Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hq : q ∈ section12Tau1Primes M)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hCQ : subgroupCentralizerIn (section10Msigma M) Q = ⊥)
    (hcomm : ⁅A, Q⁆ ≠ ⊥) :
    section12NotConjugate ⁅A, Q⁆ (subgroupCentralizerIn A Q) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  haveI : Fact q.val.Prime := ⟨q.2⟩
  have h_a := corollary_12_9_a hM hE hp hA hq hQ hCQ hcomm
  rcases h_a with ⟨hA0_prime, hA0_eq_CMsigma, hA0_norm_M⟩
  let A0 : Subgroup G := ⁅A, Q⁆
  have hA0_card : Nat.card A0 = p.val := by rcases hA0_prime with ⟨_, h⟩; simpa [A0] using h
  have hA0_le_M : A0 ≤ M := by rcases hA0_norm_M with ⟨h, _⟩; exact h
  have hA0_ne_bot : A0 ≠ ⊥ := by simpa [A0] using hcomm
  have hA0_subnorm_M : (A0.subgroupOf M).Normal := by rcases hA0_norm_M with ⟨_, h⟩; exact h
  -- Extract hcomp without destroying hE
  have hcomp : section12ComplementToMsigma M E := hE.1
  have hEM : E ≤ M := hcomp.2.1
  rcases hQ with ⟨hQE, hQ_card⟩
  have hQM : Q ≤ M := hQE.trans hEM
  have hp_ne_q : p ≠ q := by
    intro h; subst h
    have hr1 : primeRank p.val M = 1 := hq.2.2
    have hr2 : primeRank p.val M = 2 := hp.2; rw [hr1] at hr2; omega
  have hp_ne_q_val : p.val ≠ q.val := by intro h; apply hp_ne_q; exact Subtype.ext h
  -- Step 1: N_G(A0) = M
  have hM8 : M ∈ section8MaximalSubgroups G := by
    simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hM
  have hN_A0_eq_M : Subgroup.normalizer (A0 : Set G) = M :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal hM8 hA0_le_M hA0_ne_bot
      hA0_subnorm_M
  have hCG_A0_le_M : Subgroup.centralizer (A0 : Set G) ≤ M :=
    (centralizer_le_normalizer A0).trans (by rw [hN_A0_eq_M])
  -- For m ∈ M, A0^m = A0
  have hA0_conj_eq (m : G) (hm : m ∈ M) : A0.conjBy m = A0 := by
    have hm_norm : m ∈ Subgroup.normalizer (A0 : Set G) := by
      rw [hN_A0_eq_M]; exact hm
    have hm_norm_iff : ∀ n, n ∈ (A0 : Set G) ↔ m * n * m⁻¹ ∈ (A0 : Set G) := by
      intro n
      exact ((Subgroup.mem_normalizer_iff (H := A0) (g := m)).mp hm_norm n)
    ext x
    constructor
    · intro hx
      dsimp [Subgroup.conjBy] at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : m * y * m⁻¹ ∈ A0 := ((hm_norm_iff y).mp hy)
      simpa
    · intro hx
      have hm_inv_norm : m⁻¹ ∈ Subgroup.normalizer (A0 : Set G) := by
        rw [hN_A0_eq_M]; exact Subgroup.inv_mem M hm
      have hm_inv_norm_iff : ∀ n, n ∈ (A0 : Set G) ↔ m⁻¹ * n * m ∈ (A0 : Set G) := by
        intro n
        have h := ((Subgroup.mem_normalizer_iff (H := A0) (g := m⁻¹)).mp hm_inv_norm n)
        simpa [inv_inv] using h
      have hmem : m⁻¹ * x * m ∈ A0 := ((hm_inv_norm_iff x).mp hx)
      dsimp [Subgroup.conjBy]
      refine Subgroup.mem_map.mpr ⟨m⁻¹ * x * m, hmem, ?_⟩
      simp [mul_assoc]
  -- Centralizer conjugation lemma: C_G(S^g) = C_G(S)^g
  have h_centralizer_conj (S : Subgroup G) (g : G) :
      Subgroup.centralizer ((S.conjBy g) : Set G) =
        (Subgroup.centralizer (S : Set G)).conjBy g := by
    have h_S_conj : S.conjBy g = S.map ((MulAut.conj g).toMonoidHom) := rfl
    have h_CS_conj : (Subgroup.centralizer (S : Set G)).conjBy g =
        (Subgroup.centralizer (S : Set G)).map ((MulAut.conj g).toMonoidHom) := rfl
    rw [h_S_conj, h_CS_conj]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx
      have hc : g⁻¹ * x * g ∈ Subgroup.centralizer (S : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hmem : g * s * g⁻¹ ∈ S.map ((MulAut.conj g).toMonoidHom) := by
          refine Subgroup.mem_map.mpr ⟨s, hs, ?_⟩
          simp [MulAut.conj_apply]
        have hcomm := hx (g * s * g⁻¹) hmem
        -- hcomm: (g*s*g⁻¹) * x = x * (g*s*g⁻¹)
        -- Need: s * (g⁻¹*x*g) = (g⁻¹*x*g) * s
        calc
          s * (g⁻¹ * x * g) = (s * g⁻¹) * x * g := by simp [mul_assoc]
          _ = (g⁻¹ * g * s * g⁻¹) * x * g := by simp
          _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by simp [mul_assoc]
          _ = g⁻¹ * (x * (g * s * g⁻¹)) * g := by rw [hcomm]
          _ = (g⁻¹ * x * g) * s := by
            calc
              g⁻¹ * (x * (g * s * g⁻¹)) * g = (g⁻¹ * x) * (g * s * g⁻¹ * g) := by group
              _ = (g⁻¹ * x) * (g * s) := by simp
              _ = (g⁻¹ * x * g) * s := by group
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hc, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨c, hc, hc_eq⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨s, hs, hy_eq⟩
      -- hc_eq: ((MulAut.conj g).toMonoidHom) c = x  →  g*c*g⁻¹ = x
      -- hy_eq: ((MulAut.conj g).toMonoidHom) s = y  →  g*s*g⁻¹ = y
      have hx_eq : x = g * c * g⁻¹ := by
        simpa [MulAut.conj_apply] using congrArg id hc_eq.symm
      have hy_eq' : y = g * s * g⁻¹ := by
        simpa [MulAut.conj_apply] using congrArg id hy_eq.symm
      have hc_comm := (Subgroup.mem_centralizer_iff.mp hc) s hs
      -- hc_comm: s * c = c * s
      -- Goal: y * x = x * y (from Subgroup.mem_centralizer_iff)
      calc
        y * x = (g * s * g⁻¹) * (g * c * g⁻¹) := by rw [hx_eq, hy_eq']
        _ = g * s * (g⁻¹ * g) * c * g⁻¹ := by simp [mul_assoc]
        _ = g * s * c * g⁻¹ := by simp
        _ = g * (s * c) * g⁻¹ := by simp [mul_assoc]
        _ = g * (c * s) * g⁻¹ := by rw [hc_comm]
        _ = g * c * s * g⁻¹ := by simp [mul_assoc]
        _ = g * c * (g⁻¹ * g) * s * g⁻¹ := by simp
        _ = (g * c * g⁻¹) * (g * s * g⁻¹) := by simp [mul_assoc]
        _ = x * y := by rw [hx_eq, hy_eq']
  -- M-invariance of C_G(A0)
  have hCG_A0_M_inv (m : G) (hm : m ∈ M) :
      (Subgroup.centralizer (A0 : Set G)).conjBy m = Subgroup.centralizer (A0 : Set G) := by
    calc
      (Subgroup.centralizer (A0 : Set G)).conjBy m
          = Subgroup.centralizer ((A0.conjBy m) : Set G) :=
        (h_centralizer_conj A0 m).symm
      _ = Subgroup.centralizer (A0 : Set G) := by rw [hA0_conj_eq m hm]
  -- Step 2: Q does NOT centralize A0
  have hQ_not_cent_A0 : ¬ (Q ≤ Subgroup.centralizer (A0 : Set G)) := by
    intro hQ_cent_A0
    have hA_elem : IsElementaryAbelian p.val A := by
      rcases section12_rankTwo_elementary hA with ⟨_, hAelem⟩; exact hAelem
    haveI : IsElementaryAbelian p.val A := hA_elem
    have hA_exp_p : ∀ a : A, a ^ p.val = 1 := by
      intro a
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p.val A) a
    haveI : IsCyclic Q := isCyclic_of_prime_card hQ_card
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
    let gG := (g : Q).val
    have hgG_mem_Q : gG ∈ Q := (g : Q).property
    have hgG_order : orderOf gG = q.val := by
      have h_order_Q : orderOf (g : Q) = Nat.card Q :=
        orderOf_eq_card_of_forall_mem_zpowers (fun x => hg x)
      have h_order_gG : orderOf gG = orderOf (g : Q) := by
        simp [gG]
      rw [h_order_gG, h_order_Q, hQ_card]
    have hAnormE : section10NormalIn A E :=
      section12_rankTwo_normalIn_complement_of_tau2_pre hM hE hp hA
    rcases hAnormE with ⟨hAE_le, hAnorm⟩
    have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) := by
      have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hAE_le).mp hAnorm
      exact hQE.trans hE_norm_A
    have hQ_cent_A0_comm : ∀ (g' : G), g' ∈ Q → ∀ (a0 : G), a0 ∈ A0 → g' * a0 = a0 * g' := by
      intro g' hg'Q a0 ha0
      have hg'_cent : g' ∈ Subgroup.centralizer (A0 : Set G) := hQ_cent_A0 hg'Q
      exact ((Subgroup.mem_centralizer_iff.mp hg'_cent) a0 ha0).symm
    have h_varphi_in_A0 : ∀ a : A, ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ∈ A0 := by
      intro a
      have ha_inv_mem : (a⁻¹ : G) ∈ A := by
        simp
      have hmem := Subgroup.commutator_mem_commutator
        (g₁ := (a : G)⁻¹) (g₂ := gG) (H₁ := A) (H₂ := Q) ha_inv_mem hgG_mem_Q
      simpa [A0, commutatorElement_def] using hmem
    have h_conj_eq : ∀ a : A, gG * (a : G) * gG⁻¹ = (a : G) *
        ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) := by
      intro a; group
    have h_gG_fixes_varphi : ∀ a : A,
        gG * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) * gG⁻¹ =
          ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) := by
      intro a
      have hcomm := hQ_cent_A0_comm gG hgG_mem_Q ((a : G)⁻¹ * gG * (a : G) * gG⁻¹)
        (h_varphi_in_A0 a)
      -- hcomm: gG * X = X * gG
      calc
        gG * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) * gG⁻¹
            = (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) * gG) * gG⁻¹ := by rw [hcomm]
        _ = ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) := by group
    have h_pow_conj : ∀ (a : A) (k : ℕ),
        (gG ^ k) * (a : G) * (gG ^ k)⁻¹ =
          (a : G) * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k) := by
      intro a k
      induction k with
      | zero => simp
      | succ k ih =>
        calc
          (gG ^ (k+1)) * (a : G) * (gG ^ (k+1))⁻¹
              = gG * ((gG ^ k) * (a : G) * (gG ^ k)⁻¹) * gG⁻¹ := by
            calc
              (gG ^ (k+1)) * (a : G) * (gG ^ (k+1))⁻¹
                  = (gG ^ k * gG) * (a : G) * ((gG ^ k * gG)⁻¹) := by rw [pow_succ]
              _ = (gG * (gG ^ k)) * (a : G) * (gG⁻¹ * (gG ^ k)⁻¹) := by group
              _ = gG * ((gG ^ k) * (a : G) * (gG ^ k)⁻¹) * gG⁻¹ := by group
          _ = gG * ((a : G) * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k)) * gG⁻¹ := by rw [ih]
          _ = (gG * (a : G) * gG⁻¹) *
                (gG * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k) * gG⁻¹) := by group
          _ = ((a : G) * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) *
                (gG * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k) * gG⁻¹) := by rw [h_conj_eq a]
          _ = ((a : G) * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) *
                ((gG * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) * gG⁻¹) ^ k) := by rw [← conj_pow]
          _ = ((a : G) * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) *
                (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k) := by rw [h_gG_fixes_varphi a]
          _ = (a : G) * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ (k+1)) := by
            calc
              ((a : G) * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) *
                  (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k)
                = (a : G) * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) *
                    (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k)) := by
                  simp [mul_assoc]
              _ = (a : G) * ((((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ k) *
                    ((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) := by
                  apply congrArg (fun t => (a : G) * t)
                  exact (Commute.self_pow ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) k).eq
              _ = (a : G) * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ (k+1)) := by
                simp [pow_succ]
    have h_gG_pow_q : gG ^ q.val = 1 := by
      rw [← hgG_order, pow_orderOf_eq_one]
    have h_varphi_pow_q : ∀ a : A,
        (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ q.val) = 1 := by
      intro a
      have h_eq := h_pow_conj a q.val
      have h_left : (gG ^ q.val) * (a : G) * (gG ^ q.val)⁻¹ = (a : G) := by
        simp [h_gG_pow_q]
      rw [h_left] at h_eq
      -- h_eq : (a : G) = (a : G) * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ q.val)
      -- So (a : G) * X = (a : G) = (a : G) * 1, cancel (a : G) to get X = 1
      have htemp : (a : G) * (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ q.val) = (a : G) * 1 := by
        rw [← h_eq, mul_one]
      exact mul_left_cancel htemp
    have h_varphi_pow_p : ∀ a : A,
        (((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ^ p.val) = 1 := by
      intro a
      have hA0_le_A : A0 ≤ A := by rcases hA0_prime with ⟨hle, _⟩; exact hle
      have h_mem : ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) ∈ A :=
        hA0_le_A (h_varphi_in_A0 a)
      set phi_a : A := ⟨((a : G)⁻¹ * gG * (a : G) * gG⁻¹), h_mem⟩
      have h_pow : phi_a ^ p.val = 1 := hA_exp_p phi_a
      simpa using congrArg Subtype.val h_pow
    have h_cop : Nat.Coprime p.val q.val :=
      (Nat.coprime_primes p.2 q.2).mpr hp_ne_q_val
    have h_varphi_one : ∀ a : A, ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) = 1 := by
      intro a
      have h_order_dvd_p : orderOf (((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) ∣ p.val :=
        orderOf_dvd_of_pow_eq_one (h_varphi_pow_p a)
      have h_order_dvd_q : orderOf (((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) ∣ q.val :=
        orderOf_dvd_of_pow_eq_one (h_varphi_pow_q a)
      have hgcd : orderOf (((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) ∣ Nat.gcd p.val q.val :=
        Nat.dvd_gcd h_order_dvd_p h_order_dvd_q
      rw [h_cop] at hgcd
      have h_order_one : orderOf (((a : G)⁻¹ * gG * (a : G) * gG⁻¹)) = 1 :=
        Nat.eq_one_of_dvd_one hgcd
      exact orderOf_eq_one_iff.mp h_order_one
    have h_gG_centralizes_A : ∀ a : A, gG * (a : G) * gG⁻¹ = (a : G) := by
      intro a
      have h_phi_one := h_varphi_one a
      calc
        gG * (a : G) * gG⁻¹ = (a : G) * ((a : G)⁻¹ * gG * (a : G) * gG⁻¹) := h_conj_eq a
        _ = (a : G) * 1 := by rw [h_phi_one]
        _ = (a : G) := by simp
    have hgG_cent : gG ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := h_gG_centralizes_A ⟨a, ha⟩
      -- h: gG * (⟨a, ha⟩ : G) * gG⁻¹ = (⟨a, ha⟩ : G)
      have h' : gG * a * gG⁻¹ = a := by simpa using h
      -- need to show a * gG = gG * a
      have htemp : gG * a = a * gG := by
        calc
          gG * a = (gG * a) * 1 := by simp
          _ = (gG * a) * (gG⁻¹ * gG) := by simp
          _ = (gG * a * gG⁻¹) * gG := by group
          _ = a * gG := by rw [h']
      exact htemp.symm
    have hQ_centralizes_A : Q ≤ Subgroup.centralizer (A : Set G) := by
      intro x hxQ
      rcases hg ⟨x, hxQ⟩ with ⟨k, hk⟩
      have hk_val : gG ^ k = x := by
        simpa [gG, Subgroup.coe_zpow] using congrArg Subtype.val hk
      rw [← hk_val]
      exact Subgroup.zpow_mem (Subgroup.centralizer (A : Set G)) hgG_cent k
    have h_comm_bot : A0 = ⊥ := by
      dsimp [A0]
      rw [Subgroup.commutator_comm A Q, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hQ_centralizes_A
    have h_comm_bot' : ⁅A, Q⁆ = ⊥ := by simpa [A0] using h_comm_bot
    exact hcomm h_comm_bot'
  -- Step 3: Final contradiction assuming A0 and A1 are conjugate
  dsimp [section12NotConjugate]
  intro g hconj
  -- hconj: A0.conjBy g = subgroupCentralizerIn A Q
  -- Q centralizes A1 = C_A(Q), so Q ≤ C_G(A1) = C_G(A0^g) = C_G(A0)^g
  have hQ_cent_A1 : Q ≤ Subgroup.centralizer ((subgroupCentralizerIn A Q) : Set G) := by
    intro x hxQ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨hyA, hyC⟩
    exact ((Subgroup.mem_centralizer_iff.mp hyC) x hxQ).symm
  have hQ_cent_A0g : Q ≤ Subgroup.centralizer ((A0.conjBy g) : Set G) := by
    -- hconj: A0.conjBy g = subgroupCentralizerIn A Q
    -- hQ_cent_A1: Q ≤ C(subgroupCentralizerIn A Q)
    rw [hconj]
    exact hQ_cent_A1
  -- C_G(A0^g) = C_G(A0)^g
  have hC_A0g_eq : Subgroup.centralizer ((A0.conjBy g) : Set G) =
      (Subgroup.centralizer (A0 : Set G)).conjBy g :=
    h_centralizer_conj A0 g
  have hQ_le_CA0g : Q ≤ (Subgroup.centralizer (A0 : Set G)).conjBy g := by
    rw [← hC_A0g_eq]; exact hQ_cent_A0g
  -- Therefore Q^(g⁻¹) ≤ C_G(A0)
  -- Let X = Q^(g⁻¹)
  let X : Subgroup G := Q.conjBy (g⁻¹)
  have hX_le_CA0 : X ≤ Subgroup.centralizer (A0 : Set G) := by
    intro x hx
    simp [X, Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨q, hqQ, rfl⟩
    -- Need to show g⁻¹ * q * g ∈ C_G(A0)
    have hq_mem : q ∈ (Subgroup.centralizer (A0 : Set G)).conjBy g := hQ_le_CA0g hqQ
    have hq_mem_map : q ∈ ((Subgroup.centralizer (A0 : Set G)).map ((MulAut.conj g).toMonoidHom)) := by
      simpa [Subgroup.conjBy] using hq_mem
    rcases Subgroup.mem_map.mp hq_mem_map with ⟨c, hc, hqc⟩
    -- hqc: (MulAut.conj g).toMonoidHom c = q, i.e., g * c * g⁻¹ = q, so g⁻¹ * q * g = c
    have h_eq : g⁻¹ * q * g = c := by
      calc
        g⁻¹ * q * g = g⁻¹ * ((MulAut.conj g).toMonoidHom c) * g := by rw [hqc]
        _ = g⁻¹ * (g * c * g⁻¹) * g := rfl
        _ = c := by group
    rw [h_eq]
    exact hc
  have hX_le_M : X ≤ M := hX_le_CA0.trans hCG_A0_le_M
  have hX_card : Nat.card X = q.val := by
    have e : X ≃* Q := by
      -- X = Q.conjBy(g⁻¹) ≅ Q
      refine (Subgroup.equivMapOfInjective
        (f := (MulAut.conj (g⁻¹)).toMonoidHom) Q
        ((MulAut.conj (g⁻¹)).injective)).symm
    exact (Nat.card_congr e.toEquiv).trans hQ_card
  have hX_ne_bot : X ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card X = 1 := by
      simp [hbot]
    rw [hX_card] at hcard1
    have hq_ne_one : q.val ≠ 1 := Nat.Prime.ne_one q.2
    exact hq_ne_one hcard1
  -- Now we have Q ≤ M and X ≤ M, both of order q
  -- Embed into M
  let Qsub : Subgroup M := Q.subgroupOf M
  let Xsub : Subgroup M := X.subgroupOf M
  have hQsub_card : Nat.card Qsub = q.val := by
    -- Qsub ≅ Q since Q ≤ M
    have e : Qsub ≃* Q := (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M) hQM)
    exact (Nat.card_congr e.toEquiv).trans hQ_card
  have hXsub_card : Nat.card Xsub = q.val := by
    have e : Xsub ≃* X := (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hX_le_M)
    exact (Nat.card_congr e.toEquiv).trans hX_card
  -- They are q-groups
  have hQsub_p : IsPGroup q.val Qsub :=
    (IsPGroup.of_card (n := 1) (by simpa [pow_one] using hQ_card)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M) hQM).symm
  have hXsub_p : IsPGroup q.val Xsub :=
    (IsPGroup.of_card (n := 1) (by simpa [pow_one] using hX_card)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hX_le_M).symm
  -- Sylow q-subgroups of M are cyclic
  have hpG_dvd_q : q.val ∣ Nat.card G := by
    have hqM : q.val ∣ Nat.card M := by
      have h_card_dvd : Nat.card Q ∣ Nat.card M := by
        have h_card_eq : Nat.card (Q.subgroupOf M) = Nat.card Q :=
          natCard_subgroupOf_eq Q M hQM
        have h_dvd : Nat.card (Q.subgroupOf M) ∣ Nat.card M :=
          Subgroup.card_subgroup_dvd_card (Q.subgroupOf M)
        rwa [h_card_eq] at h_dvd
      simpa [hQ_card] using h_card_dvd
    exact hqM.trans (Subgroup.card_subgroup_dvd_card M)
  have h_q_odd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG_dvd_q
  have h_q_rank : primeRank q.val M = 1 := hq.2.2
  have h_sylow_cyclic : ∀ P : Sylow q.val M, IsCyclic (P : Subgroup M) :=
    section12_sylow_cyclic_of_primeRank_le_one h_q_odd
      (le_of_eq h_q_rank)
  -- Get Sylow q-subgroups
  obtain ⟨SQ, hQsub_le_SQ⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := q.val) hQsub_p
  obtain ⟨SX, hXsub_le_SX⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := q.val) hXsub_p
  -- They are conjugate in M
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M SQ SX
  -- Conjugate Qsub by m to get into SX
  have h_Qsub_m_le_SX : (MulAut.conj (m : M)) • Qsub ≤ (SX : Subgroup M) := by
    calc
      (MulAut.conj (m : M)) • Qsub ≤ (MulAut.conj (m : M)) • (SQ : Subgroup M) := by
        intro x hx
        rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨y, hQsub_le_SQ hy, rfl⟩
      _ = ((m • SQ : Sylow q.val M) : Subgroup M) := by
        -- Sylow.coe_subgroup_smul gives this equality
        rw [← Sylow.coe_subgroup_smul (g := m) (P := SQ)]
      _ = (SX : Subgroup M) := by
        simp [hm]
  let Qsub_m : Subgroup M := (MulAut.conj (m : M)) • Qsub
  have hQsub_m_card : Nat.card Qsub_m = q.val := by
    -- Conjugation is an automorphism, so card is preserved
    have h_card_eq : Nat.card Qsub_m = Nat.card Qsub := by
      dsimp [Qsub_m]
      let e : Qsub ≃* ((MulAut.conj (m : M)) • Qsub : Subgroup M) :=
        Subgroup.equivSMul (a := MulAut.conj (m : M)) (H := Qsub)
      exact (Nat.card_congr e.symm.toEquiv)
    rw [h_card_eq, hQsub_card]
  have hQsub_m_le_SX : Qsub_m ≤ (SX : Subgroup M) := h_Qsub_m_le_SX
  -- SX is cyclic, apply unique subgroup lemma
  haveI hSX_cyc : IsCyclic (SX : Subgroup M) := h_sylow_cyclic SX
  have h_eq_in_SX : Qsub_m.subgroupOf (SX : Subgroup M) = Xsub.subgroupOf (SX : Subgroup M) :=
    unique_subgroup_of_prime_order_in_cyclic_pre
      (H := Qsub_m.subgroupOf (SX : Subgroup M))
      (K := Xsub.subgroupOf (SX : Subgroup M))
      (hH := by
        have e : Qsub_m.subgroupOf (SX : Subgroup M) ≃* Qsub_m :=
          (Subgroup.subgroupOfEquivOfLe (H := Qsub_m) (K := (SX : Subgroup M)) hQsub_m_le_SX)
        exact (Nat.card_congr e.toEquiv).trans hQsub_m_card)
      (hK := by
        have e : Xsub.subgroupOf (SX : Subgroup M) ≃* Xsub :=
          (Subgroup.subgroupOfEquivOfLe (H := Xsub) (K := (SX : Subgroup M)) hXsub_le_SX)
        exact (Nat.card_congr e.toEquiv).trans hXsub_card)
  -- Lift to equality in M
  have hQsub_m_eq_Xsub : Qsub_m = Xsub := by
    calc
      Qsub_m = (Qsub_m.subgroupOf (SX : Subgroup M)).map (SX : Subgroup M).subtype := by
        rw [Subgroup.subgroupOf_map_subtype Qsub_m (SX : Subgroup M)]
        -- Goal: Qsub_m = Qsub_m ⊓ SX
        -- inf_eq_left.mpr gives Qsub_m ⊓ SX = Qsub_m, so we need .symm
        exact (inf_eq_left.mpr hQsub_m_le_SX).symm
      _ = (Xsub.subgroupOf (SX : Subgroup M)).map (SX : Subgroup M).subtype := by
        rw [h_eq_in_SX]
      _ = Xsub := by
        rw [Subgroup.subgroupOf_map_subtype Xsub (SX : Subgroup M)]
        -- Goal: Xsub ⊓ SX = Xsub
        -- inf_eq_left.mpr gives exactly this
        exact inf_eq_left.mpr hXsub_le_SX
  -- Lift to G: map both sides by M.subtype
  have h_map_Qsub_m : Qsub_m.map M.subtype = (MulAut.conj (m : G)) • Q := by
    -- Qsub_m = (conj m) Qsub, and Qsub.map M.subtype = Q
    have hQsub_map : Qsub.map M.subtype = Q := by
      -- Qsub = Q.subgroupOf M, and (Q.subgroupOf M).map M.subtype = Q
      calc
        Qsub.map M.subtype = (Q.subgroupOf M).map M.subtype := rfl
        _ = Q := by
          apply le_antisymm
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            -- hy : y ∈ Q.subgroupOf M
            have hyQ : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hy
            exact hyQ
          · intro x hx
            refine Subgroup.mem_map.mpr ⟨⟨x, hQM hx⟩, hx, rfl⟩
    calc
      Qsub_m.map M.subtype = ((MulAut.conj (m : M)) • Qsub).map M.subtype := rfl
      _ = (MulAut.conj (m : G)) • (Qsub.map M.subtype) := by
        apply le_antisymm
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Set.mem_smul_set.mp hy with ⟨z, hz, rfl⟩
          refine Set.mem_smul_set.mpr
            ⟨M.subtype z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
        · intro x hx
          rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          refine Subgroup.mem_map.mpr
            ⟨(MulAut.conj (m : M)) z, Set.mem_smul_set.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
      _ = (MulAut.conj (m : G)) • Q := by rw [hQsub_map]
  have h_map_Xsub : Xsub.map M.subtype = X := by
    calc
      Xsub.map M.subtype = (X.subgroupOf M).map M.subtype := rfl
      _ = X := by
        apply le_antisymm
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          -- hy : y ∈ Xsub = X.subgroupOf M
          have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
          exact hyX
        · intro x hx
          refine Subgroup.mem_map.mpr ⟨⟨x, hX_le_M hx⟩, hx, rfl⟩
  -- Therefore (conj m) Q = X = Q^(g⁻¹) ≤ C_G(A0)
  have h_conj_eq : (MulAut.conj (m : G)) • Q = X := by
    calc
      (MulAut.conj (m : G)) • Q = Qsub_m.map M.subtype := by rw [h_map_Qsub_m]
      _ = Xsub.map M.subtype := by rw [hQsub_m_eq_Xsub]
      _ = X := by rw [h_map_Xsub]
  have h_Qm_le_CA0 : (MulAut.conj (m : G)) • Q ≤ Subgroup.centralizer (A0 : Set G) := by
    rw [h_conj_eq]
    exact hX_le_CA0
  -- By M-invariance of C_G(A0), Q ≤ C_G(A0)
  -- Since (conj m) Q ≤ C_G(A0) and C_G(A0)^(m⁻¹) = C_G(A0)
  have hm_M : (m : G) ∈ M := (m : M).property
  have hm_inv_M : (m : G)⁻¹ ∈ M := Subgroup.inv_mem M hm_M
  have h_map_CA0_inv : (Subgroup.centralizer (A0 : Set G)).conjBy ((m : G)⁻¹) =
      Subgroup.centralizer (A0 : Set G) := by
    simpa using hCG_A0_M_inv (m⁻¹) hm_inv_M
  have hQ_le_CA0 : Q ≤ Subgroup.centralizer (A0 : Set G) := by
    -- (conj m) Q ≤ C → conj(m⁻¹)(conj(m) Q) ≤ conj(m⁻¹) C = C
    -- i.e., Q ≤ C
    calc
      Q = (MulAut.conj (m⁻¹ : G)) • ((MulAut.conj (m : G)) • Q) := by
        simp
      _ ≤ (MulAut.conj (m⁻¹ : G)) • (Subgroup.centralizer (A0 : Set G)) := by
        intro x hx
        rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
        apply Set.mem_smul_set.mpr
        refine ⟨y, h_Qm_le_CA0 hy, ?_⟩
        simp
      _ = (Subgroup.centralizer (A0 : Set G)).conjBy ((m : G)⁻¹) := rfl
      _ = Subgroup.centralizer (A0 : Set G) := h_map_CA0_inv
  exact hQ_not_cent_A0 hQ_le_CA0



end Section12
