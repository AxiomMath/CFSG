module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Sporadic.Recognition.JankoWongOddCore
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup

section Orbit

variable {G : Type*} [Group G]

theorem card_modEq_card_inf_centralizer_of_pow_five {Q : Subgroup G} [Finite Q] {r : G}
    (hr : r ^ 5 = 1) (hQ : ∀ q ∈ Q, r * q * r⁻¹ ∈ Q) :
    Nat.card Q ≡ Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) [MOD 5] := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : Function.End Q := fun q => ⟨r * q * r⁻¹, hQ q q.2⟩
  have hpow : ∀ (n : ℕ) (q : Q), (((f ^ n) q : Q) : G) = r ^ n * q * (r ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro q; simp; rfl
    | succ n ih =>
      intro q
      rw [pow_succ']
      change r * (((f ^ n) q : Q) : G) * r⁻¹ = _
      rw [ih]
      simp only [pow_succ']
      group
  have hf : f ^ 5 ^ 1 = 1 := by
    funext q
    apply Subtype.ext
    rw [pow_one, hpow]
    show _ = (q : G)
    rw [hr]
    group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf
  have hfix : Fintype.card ↑(Function.fixedPoints f) =
      Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun q => ⟨(q.1 : G), q.1.2, ?_⟩
        invFun := fun q => ⟨⟨(q : G), q.2.1⟩, ?_⟩
        left_inv := fun q => by apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := fun q => by apply Subtype.ext; rfl }
    · have h := congrArg Subtype.val q.2
      change r * (q.1 : G) * r⁻¹ = q.1 at h
      show (q.1 : G) ∈ centralizer ({r} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (q.1 : G) * r = (r * (q.1 : G) * r⁻¹) * r := by rw [h]
        _ = r * (q.1 : G) := by group
    · have h := Subgroup.mem_centralizer_singleton_iff.mp q.2.2
      apply Subtype.ext
      change r * (q : G) * r⁻¹ = q
      calc r * (q : G) * r⁻¹ = ((q : G) * r) * r⁻¹ := by rw [h]
        _ = q := by group
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  exact hmod

theorem commute_of_card_le_twentySeven {Q : Subgroup G} [Finite Q] (hQ3 : IsPGroup 3 Q)
    (hQ27 : Nat.card Q ≤ 27) {r : G} (hr : r ^ 5 = 1) (hQ : ∀ q ∈ Q, r * q * r⁻¹ ∈ Q) :
    ∀ q ∈ Q, q * r = r * q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp hQ3
  have hmod := card_modEq_card_inf_centralizer_of_pow_five hr hQ
  have hdvd : Nat.card ↥(Q ⊓ centralizer ({r} : Set G)) ∣ 3 ^ i := by
    rw [← hi]; exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hji, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hi3 : i ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hij : i = j := by
    rw [hi, hj] at hmod
    unfold Nat.ModEq at hmod
    interval_cases i <;> interval_cases j <;> simp_all
  have hQC : Q ⊓ centralizer ({r} : Set G) = Q := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hi, hj, hij]
  intro q hq
  have : q ∈ Q ⊓ centralizer ({r} : Set G) := by rw [hQC]; exact hq
  exact Subgroup.mem_centralizer_singleton_iff.mp this.2

theorem eq_bot_of_inverted_card_le_twentySeven {Q : Subgroup G} [Finite Q] (hQ3 : IsPGroup 3 Q)
    (hQ27 : Nat.card Q ≤ 27) {r₁ r₂ : G} (hr₁ : r₁ ^ 5 = 1) (hr₂ : r₂ ^ 5 = 1)
    (h₁ : ∀ q ∈ Q, r₁ * q * r₁⁻¹ ∈ Q) (h₂ : ∀ q ∈ Q, r₂ * q * r₂⁻¹ ∈ Q)
    (hinv : ∀ q ∈ Q, (r₁ * r₂) ^ 2 * q * ((r₁ * r₂) ^ 2)⁻¹ = q⁻¹) : Q = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c₁ := commute_of_card_le_twentySeven hQ3 hQ27 hr₁ h₁
  have c₂ := commute_of_card_le_twentySeven hQ3 hQ27 hr₂ h₂
  rw [eq_bot_iff]
  intro q hq
  have hc : (r₁ * r₂) * q = q * (r₁ * r₂) := by
    calc r₁ * r₂ * q = r₁ * (r₂ * q) := mul_assoc _ _ _
      _ = r₁ * (q * r₂) := by rw [c₂ q hq]
      _ = (r₁ * q) * r₂ := (mul_assoc _ _ _).symm
      _ = (q * r₁) * r₂ := by rw [c₁ q hq]
      _ = q * (r₁ * r₂) := mul_assoc _ _ _
  have hc2 : (r₁ * r₂) ^ 2 * q = q * (r₁ * r₂) ^ 2 :=
    (Commute.pow_left (show Commute (r₁ * r₂) q from hc) 2).eq
  have hq1 : q = q⁻¹ := by
    have h := hinv q hq
    rw [hc2] at h
    rwa [mul_inv_cancel_right] at h
  have hq2 : q ^ 2 = 1 := by
    rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr hq1
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ3 ⟨q, hq⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : 3 ^ k ∣ 2 := hk ▸ orderOf_dvd_of_pow_eq_one hq2
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    simpa using hk
  · exfalso
    have : 3 ∣ 2 := (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd
    omega

theorem three_pow_four_dvd_of_inverted [Finite G] {A : Subgroup G} [A.Normal]
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {r₁ r₂ : G} (hr₁ : r₁ ^ 5 = 1) (hr₂ : r₂ ^ 5 = 1)
    (hinv : ∀ x ∈ A, (r₁ * r₂) ^ 2 * x * ((r₁ * r₂) ^ 2)⁻¹ = x⁻¹) (h3 : 3 ∣ Nat.card A) :
    3 ^ 4 ∣ Nat.card A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h4
  obtain ⟨P⟩ : Nonempty (Sylow 3 A) := inferInstance
  have hPn : (P : Subgroup A).Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := Subtype.ext (by
      show (g : G) * n * (g : G)⁻¹ = n
      rw [hcomm g g.2 n n.2]; group)
    rw [this]; exact hn⟩
  have hPchar := Subgroup.characteristic_iff_le_comap.mp (P.characteristic_of_normal hPn)
  let Q : Subgroup G := (P : Subgroup A).map A.subtype
  have hQn : ∀ g : G, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    rintro g _ ⟨p, hp, rfl⟩
    exact ⟨_, hPchar (MulAut.conjNormal g) hp, MulAut.conjNormal_apply g p⟩
  have hQcard : Nat.card Q = 3 ^ (Nat.card A).factorization 3 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, P.card_eq_multiplicity]
  have hne : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hv1 : 1 ≤ (Nat.card A).factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization hne).mp h3
  have hv4 : (Nat.card A).factorization 3 < 4 := by
    by_contra h
    exact h4 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mpr (by omega))
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card hQcard
  have hQ27 : Nat.card Q ≤ 27 := by
    rw [hQcard]
    calc 3 ^ (Nat.card A).factorization 3 ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 27 := by norm_num
  have hQA : ∀ q ∈ Q, q ∈ A := by
    rintro _ ⟨p, _, rfl⟩
    exact p.2
  have hbot := eq_bot_of_inverted_card_le_twentySeven hQ3 hQ27 hr₁ hr₂ (fun q hq => hQn r₁ q hq)
    (fun q hq => hQn r₂ q hq) (fun q hq => hinv q (hQA q hq))
  have h1 : Nat.card Q = 1 := by rw [hbot]; simp
  rw [hQcard] at h1
  have : (Nat.card A).factorization 3 = 0 := by
    rcases Nat.pow_eq_one.mp h1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  omega

end Orbit

section Reduction

variable {K : Type*} [Group K]

theorem exists_mem_centralizer_of_central_mod {M : Subgroup K} [M.Normal] [Finite K]
    (hModd : Odd (Nat.card M)) {z : K} (hz2 : z ^ 2 = 1)
    (hBS : (QuotientGroup.mk z : K ⧸ M) ∈ center (K ⧸ M)) (k : K) :
    ∃ m ∈ M, m⁻¹ * k ∈ centralizer ({z} : Set K) := by
  obtain ⟨z', hz'⟩ : ∃ z' : K, z' = k * z * k⁻¹ := ⟨_, rfl⟩
  have hzz : z * z = 1 := by rwa [← pow_two]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hz'z' : z' * z' = 1 := by
    calc z' * z' = k * (z * z) * k⁻¹ := by rw [hz']; group
      _ = 1 := by rw [hzz]; group
  have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'z'
  obtain ⟨u, hu⟩ : ∃ u : K, u = z * z' := ⟨_, rfl⟩
  have huM : u ∈ M := by
    rw [← QuotientGroup.eq_one_iff]
    have hc := Subgroup.mem_center_iff.mp hBS (k : K ⧸ M)
    have h1 : (z' : K ⧸ M) = (z : K ⧸ M) := by
      calc (z' : K ⧸ M) = (k : K ⧸ M) * (z : K ⧸ M) * (k : K ⧸ M)⁻¹ := by
            rw [hz', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        _ = (z : K ⧸ M) * (k : K ⧸ M) * (k : K ⧸ M)⁻¹ := by rw [hc]
        _ = (z : K ⧸ M) := by group
    rw [hu, QuotientGroup.mk_mul, h1, ← QuotientGroup.mk_mul, hzz, QuotientGroup.mk_one]
  have hord : Odd (orderOf u) := by
    have h1 : orderOf (⟨u, huM⟩ : M) ∣ Nat.card M := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hModd h1
  obtain ⟨s, hs⟩ := hord
  have hu1 : u ^ (2 * s + 1) = 1 := by rw [← hs]; exact pow_orderOf_eq_one u
  have hu2 : u ^ (2 * s) = u⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hu1)
  have hzu : z * u * z⁻¹ = u⁻¹ := by
    rw [hu, mul_inv_rev, hzi, hz'i]
    calc z * (z * z') * z = (z * z) * z' * z := by group
      _ = z' * z := by rw [hzz, one_mul]
  have hpow : z * u ^ s * z⁻¹ = (u⁻¹) ^ s := by rw [← conj_pow, hzu]
  have huz : u⁻¹ * z = z' := by
    rw [hu, mul_inv_rev, hz'i, hzi]
    calc z' * z * z = z' * (z * z) := by group
      _ = z' := by rw [hzz, mul_one]
  have hmain : u ^ s * z * (u ^ s)⁻¹ = z' := by
    calc u ^ s * z * (u ^ s)⁻¹ = u ^ s * (z * (u ^ s)⁻¹ * z⁻¹) * z := by group
      _ = u ^ s * (z * u ^ s * z⁻¹)⁻¹ * z := by group
      _ = u ^ s * ((u⁻¹) ^ s)⁻¹ * z := by rw [hpow]
      _ = u ^ (2 * s) * z := by group
      _ = z' := by rw [hu2, huz]
  refine ⟨u ^ s, M.pow_mem huM s, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (u ^ s)⁻¹ * k * z = (u ^ s)⁻¹ * (k * z * k⁻¹) * k := by group
    _ = (u ^ s)⁻¹ * (u ^ s * z * (u ^ s)⁻¹) * k := by rw [← hz', ← hmain]
    _ = z * ((u ^ s)⁻¹ * k) := by group

theorem card_mul_card_inf_of_exists_mem {M T : Subgroup K} [M.Normal]
    (h : ∀ k : K, ∃ m ∈ M, m⁻¹ * k ∈ T) :
    Nat.card K * Nat.card ↥(M ⊓ T) = Nat.card M * Nat.card T := by
  let ψ : ↥T →* K ⧸ M := (QuotientGroup.mk' M).comp T.subtype
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨m, hm, hmk⟩ := h k
    refine ⟨⟨m⁻¹ * k, hmk⟩, ?_⟩
    show (QuotientGroup.mk (m⁻¹ * k) : K ⧸ M) = QuotientGroup.mk k
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff m).mpr hm, inv_one,
      one_mul]
  have hker : ψ.ker = M.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (t : K)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv, hker,
    ← Subgroup.inf_subgroupOf_right M T,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ T ≤ T)).toEquiv] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
  calc Nat.card K * Nat.card ↥(M ⊓ T) = (Nat.card (K ⧸ M) * Nat.card M) * Nat.card ↥(M ⊓ T) := by
        rw [← h2]
    _ = Nat.card M * (Nat.card (K ⧸ M) * Nat.card ↥(M ⊓ T)) := by ring
    _ = Nat.card M * Nat.card T := by rw [← h1]

theorem card_eq_card_map_mk'_mul_card {M Z : Subgroup K} [Z.Normal] (hZM : Z ≤ M) :
    Nat.card M = Nat.card ↥(M.map (QuotientGroup.mk' Z)) * Nat.card Z := by
  let π' : ↥M →* K ⧸ Z := (QuotientGroup.mk' Z).domRestrict M
  have hrange : π'.range = M.map (QuotientGroup.mk' Z) := MonoidHom.domRestrict_range M _
  have hker : π'.ker = Z.subgroupOf M := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π').toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv] at h1
  exact h1

theorem commute_of_commute_mod_central {Z : Subgroup K} [Z.Normal] (hZ3 : ∀ c ∈ Z, c ^ 3 = 1)
    (hZc : ∀ c ∈ Z, ∀ g : K, g * c = c * g) {z m : K} (hz2 : z ^ 2 = 1)
    (h : (QuotientGroup.mk z : K ⧸ Z) * QuotientGroup.mk m =
      QuotientGroup.mk m * QuotientGroup.mk z) : z * m = m * z := by
  have hzz : z * z = 1 := by rwa [← pow_two]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hc : (z * m)⁻¹ * (m * z) ∈ Z := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact h
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = (z * m)⁻¹ * (m * z) := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hzc : z * c = c * z := hZc c hc z
  have hc3 := hZ3 c hc
  have hzz' : z⁻¹ * z⁻¹ = 1 := by rw [hzi, hzz]
  have hinv : z * c * z⁻¹ = c⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc z * c * z⁻¹ * c = z * m⁻¹ * (z⁻¹ * z⁻¹) * m * z := by rw [hcdef]; group
      _ = z * m⁻¹ * m * z := by rw [hzz', mul_one]
      _ = z * z := by group
      _ = 1 := hzz
  have hcc : z * c * z⁻¹ = c := by
    calc z * c * z⁻¹ = c * z * z⁻¹ := by rw [hzc]
      _ = c := by group
  have hc2 : c * c = 1 := mul_eq_one_iff_eq_inv.mpr (by rw [← hinv]; exact hcc.symm)
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; simp
  rw [hc1] at hcdef
  exact inv_mul_eq_one.mp hcdef.symm

theorem eq_one_of_commute_map {Z M : Subgroup K} [Z.Normal] (hZ3 : ∀ c ∈ Z, c ^ 3 = 1)
    (hZc : ∀ c ∈ Z, ∀ g : K, g * c = c * g) {z : K} (hz2 : z ^ 2 = 1)
    (hW : ∀ m ∈ M, z * m = m * z → m ∈ Z) {y : K ⧸ Z} (hy : y ∈ M.map (QuotientGroup.mk' Z))
    (hyz : (QuotientGroup.mk z : K ⧸ Z) * y = y * QuotientGroup.mk z) : y = 1 := by
  obtain ⟨m, hm, rfl⟩ := hy
  have hyz' : (QuotientGroup.mk z : K ⧸ Z) * QuotientGroup.mk m =
      QuotientGroup.mk m * QuotientGroup.mk z := hyz
  exact (QuotientGroup.eq_one_iff m).mpr (hW m hm (commute_of_commute_mod_central hZ3 hZc hz2 hyz'))

theorem commutative_of_inverted {Y : Subgroup K} {u : K} (hinv : ∀ y ∈ Y, u * y * u⁻¹ = y⁻¹) :
    ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
  intro x hx y hy
  have h1 := hinv (x * y) (Y.mul_mem hx hy)
  have h2 := hinv x hx
  have h3 := hinv y hy
  have h4 : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
    calc x⁻¹ * y⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by rw [h2, h3]
      _ = u * (x * y) * u⁻¹ := by group
      _ = (x * y)⁻¹ := h1
      _ = y⁻¹ * x⁻¹ := by group
  calc x * y = (y⁻¹ * x⁻¹)⁻¹ := by group
    _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [h4]
    _ = y * x := by group

end Reduction

theorem three_pow_six_dvd_of_brauerSuzuki
    {K : Type*} [Group K] [Finite K] {a z r₁ r₂ : K}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (haK : ∀ k : K, k * a = a * k) (hz2 : z ^ 2 = 1)
    (hBS : (QuotientGroup.mk z : K ⧸ CFSG.oddCore K) ∈ Subgroup.center (K ⧸ CFSG.oddCore K))
    (hT : Nat.card ↥(Subgroup.centralizer ({z} : Set K)) = 360)
    (hodd : ∀ W : Subgroup K, W ≤ Subgroup.centralizer ({z} : Set K) →
      (∀ t ∈ Subgroup.centralizer ({z} : Set K), ∀ w ∈ W, t * w * t⁻¹ ∈ W) →
      Odd (Nat.card W) → W ≤ Subgroup.zpowers a)
    (hr₁ : orderOf r₁ = 5) (hr₂ : orderOf r₂ = 5) (hr₁₂ : (r₁ * r₂) ^ 2 = z)
    (h27 : 27 ∣ Nat.card K) :
    3 ^ 6 ∣ Nat.card K := by
  have hMn : (CFSG.oddCore K).Normal := CFSG.oddCore_normal K
  have hModd : Odd (Nat.card (CFSG.oddCore K)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have haorder : orderOf a = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime ha3 ha1
  have hZcard : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, haorder]
  have hZle : zpowers a ≤ center K := (Subgroup.zpowers_le).mpr (Subgroup.mem_center_iff.mpr haK)
  have hZn : (zpowers a).Normal := Subgroup.normal_of_le_center hZle
  have hZc : ∀ c ∈ zpowers a, ∀ g : K, g * c = c * g := fun c hc g =>
    Subgroup.mem_center_iff.mp (hZle hc) g
  have hZ3 : ∀ c ∈ zpowers a, c ^ 3 = 1 := by
    intro c hc
    have := pow_card_eq_one' (G := zpowers a) (x := ⟨c, hc⟩)
    rw [hZcard] at this
    exact congrArg Subtype.val this
  have hZM : zpowers a ≤ CFSG.oddCore K :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _ hZn
      (by rw [hZcard]; exact ⟨1, rfl⟩)
  have hKMT := fun k : K => exists_mem_centralizer_of_central_mod hModd hz2 hBS k
  have hW : CFSG.oddCore K ⊓ centralizer ({z} : Set K) = zpowers a := by
    have hle : CFSG.oddCore K ⊓ centralizer ({z} : Set K) ≤ zpowers a := by
      refine hodd _ inf_le_right (fun t ht w hw => ⟨hMn.conj_mem w hw.1 t, ?_⟩) ?_
      · exact (centralizer ({z} : Set K)).mul_mem
          ((centralizer ({z} : Set K)).mul_mem ht hw.2) ((centralizer ({z} : Set K)).inv_mem ht)
      · exact Odd.of_dvd_nat hModd (Subgroup.card_dvd_of_le inf_le_left)
    refine le_antisymm hle (le_inf hZM ?_)
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hZc c hc z).symm
  have hcardMT : Nat.card K * 3 = Nat.card (CFSG.oddCore K) * 360 := by
    have := card_mul_card_inf_of_exists_mem hKMT
    rwa [hW, hZcard, hT] at this
  have hMbn : ((CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a))).Normal :=
    hMn.map _ (QuotientGroup.mk'_surjective _)
  have hcardM : Nat.card (CFSG.oddCore K) =
      Nat.card ↥((CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a))) * 3 := by
    rw [card_eq_card_map_mk'_mul_card hZM, hZcard]
  have hfpf : ∀ y ∈ (CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a)),
      QuotientGroup.mk' (zpowers a) z * y = y * QuotientGroup.mk' (zpowers a) z → y = 1 := by
    intro y hy hyz
    refine eq_one_of_commute_map hZ3 hZc hz2 ?_ hy hyz
    intro m hm hmz
    rw [← hW]
    exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr hmz.symm⟩
  have hz2b : QuotientGroup.mk' (zpowers a) z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hinv := inverts_of_fpf hz2b (fun y hy => hMbn.conj_mem y hy _) hfpf
  have hcomm := commutative_of_inverted hinv
  have hr₁5 : QuotientGroup.mk' (zpowers a) r₁ ^ 5 = 1 := by
    rw [← map_pow, ← hr₁, pow_orderOf_eq_one, map_one]
  have hr₂5 : QuotientGroup.mk' (zpowers a) r₂ ^ 5 = 1 := by
    rw [← map_pow, ← hr₂, pow_orderOf_eq_one, map_one]
  have hzb : (QuotientGroup.mk' (zpowers a) r₁ * QuotientGroup.mk' (zpowers a) r₂) ^ 2 =
      QuotientGroup.mk' (zpowers a) z := by
    rw [← map_mul, ← map_pow, hr₁₂]
  have h3 : 3 ∣ Nat.card ↥((CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a))) := by
    omega
  obtain ⟨c, hc⟩ := three_pow_four_dvd_of_inverted hcomm hr₁5 hr₂5 (by rwa [hzb]) h3
  exact ⟨40 * c, by omega⟩

end CFSG.Sporadic.Recognition.JankoWong
