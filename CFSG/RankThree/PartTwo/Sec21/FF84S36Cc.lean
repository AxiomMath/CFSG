module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36Gen
public import CFSG.RankThree.PartTwo.Sec21.FF84S3M1
public import CFSG.RankThree.PartTwo.Sec21.FF84S3BCoprime
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHHolds
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem S36_op2_sup_zpowers {t c' : G} {M K : Subgroup G}
    (ht : orderOf t = 2) (hc3 : orderOf c' = 3)
    (hM : Subgroup.zpowers c' ⊔ K = M) (hK : Nat.card K = 60) (hKs : IsSimpleGroup K)
    (htM : ∀ m ∈ M, t * m = m * t) (hcM : ∀ m ∈ M, c' * m = m * c')
    (hKM : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) :
    Op 2 (Subgroup.zpowers t ⊔ M) = Subgroup.zpowers t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM' : K ≤ M := hM ▸ le_sup_right
  have hMH : M ≤ Subgroup.zpowers t ⊔ M := le_sup_right
  have hc'M : c' ∈ M := hM ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c')
  have htC : t ∈ Subgroup.centralizer (M : Set G) :=
    Subgroup.mem_centralizer_iff.2 (fun m hm => (htM m hm).symm)
  have htN : Subgroup.zpowers t ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ htC)
  have hMnK : M ≤ Subgroup.normalizer (K : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk; exact hKM m hm k hk
    · intro hk
      have h := hKM m⁻¹ (M.inv_mem hm) _ hk
      have e : m⁻¹ * (m * k * m⁻¹) * m⁻¹⁻¹ = k := by group
      rwa [e] at h
  have hdecM : ∀ m ∈ M, ∃ i : ℤ, ∃ k ∈ K, m = c' ^ i * k := by
    intro m hm
    have hset : (↑(Subgroup.zpowers c' ⊔ K) : Set G) =
        (Subgroup.zpowers c' : Set G) * (K : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((Subgroup.zpowers_le.2 hc'M).trans hMnK)
    rw [hM] at hset
    have hm' : m ∈ (M : Set G) := hm
    rw [hset, Set.mem_mul] at hm'
    obtain ⟨y, hy, k, hk, hyk⟩ := hm'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨i, k, hk, hyk.symm⟩
  have hdecH : ∀ h ∈ Subgroup.zpowers t ⊔ M, ∃ j : ℤ, ∃ m ∈ M, h = t ^ j * m := by
    intro h hh
    have hset : (↑(Subgroup.zpowers t ⊔ M) : Set G) =
        (Subgroup.zpowers t : Set G) * (M : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ htN
    have hh' : h ∈ (↑(Subgroup.zpowers t ⊔ M) : Set G) := hh
    rw [hset, Set.mem_mul] at hh'
    obtain ⟨y, hy, m, hm, hym⟩ := hh'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨j, m, hm, hym.symm⟩
  have hcomm_t : ∀ (j : ℤ) (m : G), m ∈ M → t ^ j * m = m * t ^ j := fun j m hm =>
    (Commute.zpow_left (show Commute t m from htM m hm) j).eq
  have hcomm_c : ∀ (i : ℤ) (m : G), m ∈ M → c' ^ i * m = m * c' ^ i := fun i m hm =>
    (Commute.zpow_left (show Commute c' m from hcM m hm) i).eq
  have hKH : ∀ h ∈ Subgroup.zpowers t ⊔ M, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    obtain ⟨j, m, hm, rfl⟩ := hdecH _ hh
    have hmk : m * k * m⁻¹ ∈ K := hKM m hm k hk
    have e : t ^ j * m * k * (t ^ j * m)⁻¹ = t ^ j * (m * k * m⁻¹) * (t ^ j)⁻¹ := by group
    rw [e, hcomm_t j _ (hKM' hmk), mul_inv_cancel_right]
    exact hmk
  have hinf : ∀ y ∈ Op 2 (Subgroup.zpowers t ⊔ M) ⊓ K, y = 1 := by
    have hN' : ((Op 2 (Subgroup.zpowers t ⊔ M) ⊓ K).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
      have hgH : (g : G) ∈ Subgroup.zpowers t ⊔ M := hMH (hKM' g.2)
      have e : ((g * n * g⁻¹ : K) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by simp
      rw [e]
      exact Subgroup.mem_inf.2
        ⟨S36_op2_conj hgH hn1, K.mul_mem (K.mul_mem g.2 hn2) (K.inv_mem g.2)⟩
    haveI := hN'
    intro y hy
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Op 2 (Subgroup.zpowers t ⊔ M) ⊓ K).subgroupOf K) with h | h
    · have hy' : (⟨y, (Subgroup.mem_inf.1 hy).2⟩ : ↥K) ∈
          (Op 2 (Subgroup.zpowers t ⊔ M) ⊓ K).subgroupOf K :=
        Subgroup.mem_subgroupOf.2 hy
      rw [h] at hy'
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hy')
    · exfalso
      letI : Fintype K := Fintype.ofFinite K
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3
        (show 3 ∣ Fintype.card K by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
      have hxO : (x : G) ∈ Op 2 (Subgroup.zpowers t ⊔ M) := by
        have hmem : x ∈ (Op 2 (Subgroup.zpowers t ⊔ M) ⊓ K).subgroupOf K := by
          rw [h]; exact Subgroup.mem_top x
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).1
      obtain ⟨n, hn⟩ := S36_op2_isPGroup (Subgroup.zpowers t ⊔ M) ⟨(x : G), hxO⟩
      have hn' : (x : G) ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have hx3 : orderOf (x : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
      rw [Subgroup.orderOf_coe, hx] at hx3
      have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hx3
      omega
  have hRsub : Op 2 (Subgroup.zpowers t ⊔ M) ≤ Subgroup.zpowers t := by
    intro x hx
    have hxH : x ∈ Subgroup.zpowers t ⊔ M := S36_op2_le _ hx
    have hxK : ∀ k ∈ K, x * k = k * x := by
      intro k hk
      have hkH : k ∈ Subgroup.zpowers t ⊔ M := hMH (hKM' hk)
      have hw : k * x⁻¹ * k⁻¹ ∈ Op 2 (Subgroup.zpowers t ⊔ M) :=
        S36_op2_conj hkH (Subgroup.inv_mem _ hx)
      have hxw : x * (k * x⁻¹ * k⁻¹) ∈ Op 2 (Subgroup.zpowers t ⊔ M) := mul_mem hx hw
      have hK' : x * (k * x⁻¹ * k⁻¹) ∈ K := by
        have e : x * (k * x⁻¹ * k⁻¹) = (x * k * x⁻¹) * k⁻¹ := by group
        rw [e]
        exact K.mul_mem (hKH x hxH k hk) (K.inv_mem hk)
      have h1 : x * (k * x⁻¹ * k⁻¹) = 1 := hinf _ (Subgroup.mem_inf.2 ⟨hxw, hK'⟩)
      calc x * k = (x * (k * x⁻¹ * k⁻¹)) * k * x := by group
        _ = k * x := by rw [h1]; group
    obtain ⟨j, m, hm, hxm⟩ := hdecH x hxH
    obtain ⟨i, k0, hk0, hmk⟩ := hdecM m hm
    have hxy : x = (t ^ j * c' ^ i) * k0 := by rw [hxm, hmk, mul_assoc]
    have hyK : ∀ k ∈ K, (t ^ j * c' ^ i) * k = k * (t ^ j * c' ^ i) := by
      intro k hk
      have hkM : k ∈ M := hKM' hk
      calc (t ^ j * c' ^ i) * k = t ^ j * (c' ^ i * k) := mul_assoc _ _ _
        _ = t ^ j * (k * c' ^ i) := by rw [hcomm_c i k hkM]
        _ = (t ^ j * k) * c' ^ i := (mul_assoc _ _ _).symm
        _ = (k * t ^ j) * c' ^ i := by rw [hcomm_t j k hkM]
        _ = k * (t ^ j * c' ^ i) := mul_assoc _ _ _
    have hk0eq : k0 = (t ^ j * c' ^ i)⁻¹ * x := by rw [hxy]; group
    have hk0c : ∀ k ∈ K, k0 * k = k * k0 := by
      intro k hk
      have hyinv : (t ^ j * c' ^ i)⁻¹ * k = k * (t ^ j * c' ^ i)⁻¹ :=
        (Commute.inv_left (show Commute (t ^ j * c' ^ i) k from hyK k hk)).eq
      calc k0 * k = (t ^ j * c' ^ i)⁻¹ * x * k := by rw [hk0eq]
        _ = (t ^ j * c' ^ i)⁻¹ * (x * k) := by group
        _ = (t ^ j * c' ^ i)⁻¹ * (k * x) := by rw [hxK k hk]
        _ = ((t ^ j * c' ^ i)⁻¹ * k) * x := by group
        _ = (k * (t ^ j * c' ^ i)⁻¹) * x := by rw [hyinv]
        _ = k * k0 := by rw [hk0eq]; group
    have hk0one : k0 = 1 := S36_centre_trivial hK hKs hk0 hk0c
    rw [hk0one, mul_one] at hxy
    obtain ⟨n, hn⟩ := S36_op2_isPGroup (Subgroup.zpowers t ⊔ M) ⟨x, hx⟩
    have hxn : x ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [hxy] at hxn
    have hcomm : Commute (t ^ j) (c' ^ i) :=
      ((show Commute t c' from htM c' hc'M).zpow_left j).zpow_right i
    rw [hcomm.mul_pow] at hxn
    have hzt : (t ^ j) ^ 2 ^ n ∈ Subgroup.zpowers t :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩) _
    have hw : (c' ^ i) ^ 2 ^ n = ((t ^ j) ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hxn
    have hw2 : ((c' ^ i) ^ 2 ^ n) ^ 2 = 1 := by
      rw [hw]
      exact S36_sq_zpowers ht (Subgroup.inv_mem _ hzt)
    have h3' : c' ^ ((3 : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast]
      have h := pow_orderOf_eq_one c'
      rwa [hc3] at h
    have ha3 : (c' ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, h3', one_zpow]
    have h2n : (c' ^ i) ^ 2 ^ (n + 1) = 1 := by
      rw [pow_succ, pow_mul]
      exact hw2
    have hgcd : (c' ^ i) ^ Nat.gcd (2 ^ (n + 1)) 3 = 1 := pow_gcd_eq_one.2 ⟨h2n, ha3⟩
    have hcop : Nat.gcd (2 ^ (n + 1)) 3 = 1 := by
      apply Nat.Coprime.gcd_eq_one
      exact Nat.Coprime.pow_left _ (by norm_num)
    rw [hcop, pow_one] at hgcd
    rw [hxy, hgcd, mul_one]
    exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩
  have hgcomm : ∀ g ∈ Subgroup.zpowers t ⊔ M, Commute g t := by
    intro g hg
    obtain ⟨j, m, hm, rfl⟩ := hdecH g hg
    exact Commute.mul_left ((Commute.refl t).zpow_left j) (show Commute m t from (htM m hm).symm)
  have hRsup : Subgroup.zpowers t ≤ Op 2 (Subgroup.zpowers t ⊔ M) :=
    S36_zpowers_op2 ht (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)) hgcomm
  exact le_antisymm hRsub hRsup

theorem S36_part {b t c' : G} {L K : Subgroup G} (hb3 : orderOf b = 3) (ht : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (hbL : ∀ l ∈ L, b * l = l * b) (htL : ∀ l ∈ L, t * l = l * t)
    (hN : Subgroup.closure ({b, t} : Set G) ⊔ L = Nor (Subgroup.zpowers b)) (hcL : c' ∈ L)
    (hC : Cen c' ≤ Nor (Subgroup.zpowers b)) (hc3 : orderOf c' = 3)
    (hK : Nat.card K = 60) (hKs : IsSimpleGroup K) (hM : Subgroup.zpowers c' ⊔ K = L ⊓ Cen c')
    (hKn : ∀ m ∈ L ⊓ Cen c', conjBy m K = K) :
    Op 2 (Cen t ⊓ Cen c') = Subgroup.zpowers t ∧
      Cen t ⊓ Cen c' = Subgroup.zpowers t ⊔ Subgroup.zpowers c' ⊔ L ⊓ Cen c' := by
  have hcen := S36_cen_eq hb3 ht htb hbL htL hN hcL hC
  have hKM : ∀ m ∈ L ⊓ Cen c', ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    have h : m * k * m⁻¹ ∈ conjBy m K := Subgroup.mem_map.2 ⟨k, hk, rfl⟩
    rw [hKn m hm] at h
    exact h
  have hcM : ∀ m ∈ L ⊓ Cen c', c' * m = m * c' := fun m hm =>
    S36_comm_of_cen (Subgroup.mem_inf.1 hm).2
  have htM : ∀ m ∈ L ⊓ Cen c', t * m = m * t := fun m hm =>
    htL m (Subgroup.mem_inf.1 hm).1
  have hcl := S36_op2_sup_zpowers ht hc3 hM hK hKs htM hcM hKM
  have hcz : Subgroup.zpowers c' ≤ L ⊓ Cen c' :=
    Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hcL, S36_mem_cen_of rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [hcen]
    exact hcl
  · rw [hcen]
    apply le_antisymm
    · exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
    · exact sup_le (sup_le le_sup_left (hcz.trans le_sup_right)) le_sup_right

theorem S36_conj_mem_cen {c g x : G} (hg : g ∈ Cen c) (hx : x ∈ Cen c) :
    g * x * g⁻¹ ∈ Cen c := by
  have hgc : c * g = g * c := S36_comm_of_cen hg
  have hxc : c * x = x * c := S36_comm_of_cen hx
  have hg' : g * c * g⁻¹ = c := by rw [← hgc]; group
  refine S36_mem_cen_of ?_
  calc c * (g * x * g⁻¹) = (c * g) * x * g⁻¹ := by group
    _ = (g * c) * x * g⁻¹ := by rw [hgc]
    _ = g * (c * x) * g⁻¹ := by group
    _ = g * (x * c) * g⁻¹ := by rw [hxc]
    _ = (g * x * g⁻¹) * (g * c * g⁻¹) := by group
    _ = (g * x * g⁻¹) * c := by rw [hg']

theorem S36_CT_of {t c : G} (ht : orderOf t = 2) (htc : t ∈ Cen c)
    (hH : Op 2 (Cen t ⊓ Cen c) = Subgroup.zpowers t) :
    Op 2 (Cen t) ⊓ Cen c = Subgroup.zpowers t := by
  have htCen : t ∈ Cen t := S36_mem_cen_of rfl
  apply le_antisymm
  · have hsub : Op 2 (Cen t) ⊓ Cen c ≤ Op 2 (Cen t ⊓ Cen c) := by
      refine S36_op2_of_normal (fun x hx => Subgroup.mem_inf.2
        ⟨S36_op2_le _ (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩) ?_
        (S36_isPGroup_mono (S36_op2_isPGroup _) inf_le_left)
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
      have e : ((g * n * g⁻¹ : ↥(Cen t ⊓ Cen c)) : G) = (g : G) * (n : G) * (g : G)⁻¹ := by
        simp
      rw [e]
      have hg := Subgroup.mem_inf.1 g.2
      exact Subgroup.mem_inf.2 ⟨S36_op2_conj hg.1 hn1, S36_conj_mem_cen hg.2 hn2⟩
    rw [hH] at hsub
    exact hsub
  · refine le_inf ?_ (Subgroup.zpowers_le.2 htc)
    exact S36_zpowers_op2 ht htCen (fun g hg => (S36_comm_of_cen hg).symm)

theorem S36_c_case {b t b₁ b₂ : G} {L B : Subgroup G} (sec : FF84Sec3 b L B b₁ b₂)
    (h31 : FF84_3_1) (h33 : FF84_3_3) (ht : orderOf t = 2) (htL : t ∈ CenS L)
    (htb : t * b * t⁻¹ = b⁻¹)
    (hN : Subgroup.closure ({b, t} : Set G) ⊔ L = Nor (Subgroup.zpowers b)) :
    Op 2 (Cen t ⊓ Cen (b₁ * b₂)) = Subgroup.zpowers t ∧
      Cen t ⊓ Cen (b₁ * b₂) = Subgroup.zpowers t ⊔ Subgroup.zpowers (b₁ * b₂) ⊔ L ⊓ Cen (b₁ * b₂) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : orderOf b = 3 := sec.hyp.ord
  have hZ : Subgroup.center L = ⊥ := (h31 G b L B b₁ b₂ sec).2
  obtain ⟨K, -, hK60, hKs, -, -, hM, hKc⟩ := M1_K sec hZ
  have hb1B : b₁ ∈ B := (Subgroup.mem_inf.1 sec.hb₁).1
  have hb2B : b₂ ∈ B := (Subgroup.mem_inf.1 sec.hb₂).1
  have hcL : b₁ * b₂ ∈ L :=
    mul_mem (Subgroup.mem_inf.1 sec.hb₁).2 (Subgroup.mem_inf.1 sec.hb₂).2
  have hc3 : orderOf (b₁ * b₂) = 3 := by
    apply orderOf_eq_prime
    · rw [(comm_of_mem_B sec hb1B hb2B).mul_pow, pow3_of_mem_B sec hb1B,
        pow3_of_mem_B sec hb2B, one_mul]
    · exact b₁b₂_ne_one sec
  have hbL : ∀ l ∈ L, b * l = l * b := fun l hl => S36_comm_of_cen (sec.hyp.hLC hl)
  have htL' : ∀ l ∈ L, t * l = l * t := fun l hl =>
    (Subgroup.mem_centralizer_iff.1 htL l hl).symm
  have hC : Cen (b₁ * b₂) ≤ Nor (Subgroup.zpowers b) := fun x hx =>
    (h33 G b L B b₁ b₂ sec).2.1 (S36_cen_le_nor _ hx)
  have hKn : ∀ m ∈ L ⊓ Cen (b₁ * b₂), conjBy m K = K := fun m hm =>
    hKc m (Subgroup.mem_inf.2 ⟨sec.hyp.hLC (Subgroup.mem_inf.1 hm).1, (Subgroup.mem_inf.1 hm).2⟩)
  exact S36_part hb3 ht htb hbL htL' hN hcL hC hc3 hK60 hKs hM hKn

theorem F6_Cc {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) :
    Op 2 (Cen t ⊓ Cen (b₁ * b₂)) = Subgroup.zpowers t ∧
    Op 2 (Cen t ⊓ Cen (b₁ * b₂ ^ 2)) = Subgroup.zpowers t ∧
    Cen t ⊓ Cen (b₁ * b₂) = Subgroup.zpowers t ⊔ Subgroup.zpowers (b₁ * b₂) ⊔ L ⊓ Cen (b₁ * b₂) := by
  obtain ⟨h1, h3⟩ := S36_c_case d.sec h31 h33 d.ht d.htL d.htb d.hN
  refine ⟨h1, ?_, h3⟩
  have hb2B : b₂ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₂).1
  have hsq : b₂ ^ 2 = b₂⁻¹ := S36_sq_eq_inv (pow3_of_mem_B d.sec hb2B)
  rw [hsq]
  exact (S36_c_case (P_inv₂ d.sec) h31 h33 d.ht d.htL d.htb d.hN).1

theorem F6_CT_c {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) :
    Op 2 (Cen t) ⊓ Cen (b₁ * b₂) = Subgroup.zpowers t ∧
      Op 2 (Cen t) ⊓ Cen (b₁ * b₂ ^ 2) = Subgroup.zpowers t := by
  obtain ⟨h1, h2, -⟩ := F6_Cc d h31 h33
  have htC : ∀ x ∈ L, t ∈ Cen x := fun x hx =>
    S36_mem_cen_of (Subgroup.mem_centralizer_iff.1 d.htL x hx)
  have hcL : b₁ * b₂ ∈ L :=
    mul_mem (Subgroup.mem_inf.1 d.sec.hb₁).2 (Subgroup.mem_inf.1 d.sec.hb₂).2
  have hdL : b₁ * b₂ ^ 2 ∈ L :=
    mul_mem (Subgroup.mem_inf.1 d.sec.hb₁).2 (pow_mem (Subgroup.mem_inf.1 d.sec.hb₂).2 2)
  exact ⟨S36_CT_of d.ht (htC _ hcL) h1, S36_CT_of d.ht (htC _ hdL) h2⟩

theorem S36_not_three_dvd {X : Subgroup G} (hX : IsPGroup 2 X) : ¬ 3 ∣ Nat.card X := by
  classical
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨y, hy⟩ : ∃ y : X, orderOf y = 3 :=
    exists_prime_orderOf_dvd_card 3 (by rwa [← Nat.card_eq_fintype_card])
  obtain ⟨k, hk⟩ := hX y
  have h2 : (y : G) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hd : orderOf (y : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  rw [Subgroup.orderOf_coe, hy] at hd
  have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  omega

theorem S36_nor_op2 {H : Subgroup G} {g : G} (hg : g ∈ H) : g ∈ Nor (Op 2 H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact fun hn => S36_op2_conj hg hn
  · intro hn
    have h := S36_op2_conj (Subgroup.inv_mem H hg) hn
    have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
    rwa [e] at h

theorem S36_nor_zpowers_le {t : G} (ht : orderOf t = 2) : Nor (Subgroup.zpowers t) ≤ Cen t := by
  intro x hx
  have hs : x * t * x⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.1 hx t).1 (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hs
  have ht1 : t ≠ 1 := by
    intro h
    have h' := ht
    rw [h, orderOf_one] at h'
    norm_num at h'
  have h2 : t ^ (k % 2) = t ^ k := by
    have := zpow_mod_orderOf t k
    rwa [ht] at this
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at h2
    have h3 : x * t * x⁻¹ = 1 := by rw [← hk, ← h2]
    exact absurd (by
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = 1 := by rw [h3]; group) ht1
  · rw [h, zpow_one] at h2
    have h3 : x * t * x⁻¹ = t := by rw [← hk, ← h2]
    have hxt : x * t = t * x := by
      calc x * t = x * t * x⁻¹ * x := by group
        _ = t * x := by rw [h3]
    exact S36_mem_cen_of hxt.symm

theorem S36_c_order {b b₁ b₂ : G} {L B : Subgroup G} (sec : FF84Sec3 b L B b₁ b₂) :
    orderOf (b₁ * b₂) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1B : b₁ ∈ B := (Subgroup.mem_inf.1 sec.hb₁).1
  have hb2B : b₂ ∈ B := (Subgroup.mem_inf.1 sec.hb₂).1
  apply orderOf_eq_prime
  · rw [(comm_of_mem_B sec hb1B hb2B).mul_pow, pow3_of_mem_B sec hb1B,
      pow3_of_mem_B sec hb2B, one_mul]
  · exact b₁b₂_ne_one sec

theorem F6_r_pos {b t b₁ b₂ : G} {L B : Subgroup G} (hchar : CFSG.Assembly.IsCharTwoType G)
    (d : F6Data b L B b₁ b₂ t) : Op 2 (Cen t) ≠ Subgroup.zpowers t := by
  intro hT
  have hNor : Nor (Subgroup.zpowers t) = Cen t :=
    le_antisymm (S36_nor_zpowers_le d.ht) (S36_cen_le_nor t)
  have hTQ : Op 2 (Nor (Subgroup.zpowers t)) = Subgroup.zpowers t := by
    rw [hNor]; exact hT
  have hQne : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    have ht1 : t = 1 := Subgroup.zpowers_eq_bot.1 h
    have h' := d.ht
    rw [ht1, orderOf_one] at h'
    norm_num at h'
  have hB := B_charTwo hchar (Subgroup.zpowers t) hQne (S36_isPGroup_zpowers d.ht)
  rw [hTQ] at hB
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  have hcenle : Cen t ≤ Subgroup.zpowers t := by
    intro x hx
    have hxt : t * x = x * t := S36_comm_of_cen hx
    have hxC : x ∈ CenS (Subgroup.zpowers t) := by
      refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
      have hh' : h ∈ Subgroup.zpowers t := hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh'
      exact ((show Commute t x from hxt).zpow_left k).eq
    have hxN : x ∈ Nor (Subgroup.zpowers t) := by rw [hNor]; exact hx
    exact hB (Subgroup.mem_inf.2 ⟨hxN, hxC⟩)
  have hcL : b₁ * b₂ ∈ L :=
    mul_mem (Subgroup.mem_inf.1 d.sec.hb₁).2 (Subgroup.mem_inf.1 d.sec.hb₂).2
  have hc_zt : b₁ * b₂ ∈ Subgroup.zpowers t := hcenle (S36_mem_cen_of (htc' _ hcL))
  have h2 : orderOf (b₁ * b₂) ∣ 2 := orderOf_dvd_of_pow_eq_one (S36_sq_zpowers d.ht hc_zt)
  rw [S36_c_order d.sec] at h2
  norm_num at h2

theorem F6_H {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) :
    (∀ u ∈ Op 2 (Cen t), ∀ v ∈ Op 2 (Cen t), u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers t) ∧
    (∀ u ∈ Op 2 (Cen t), u ^ 2 ∈ Subgroup.zpowers t) ∧
    ∃ r : ℕ, Nat.card (Op 2 (Cen t)) = 2 * 16 ^ r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1B : b₁ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₁).1
  have hb2B : b₂ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₂).1
  have hb1L : b₁ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₁).2
  have hb2L : b₂ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₂).2
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  have htCen : t ∈ Cen t := S36_mem_cen_of rfl
  have hCT := (F6_CT_c d h31 h33).2
  obtain ⟨K, hKle, hK60, hKs, hdK, -, -, -⟩ := M1_K d.sec (h31 G b L B b₁ b₂ d.sec).2
  have hKC : K ≤ Cen t := fun k hk =>
    S36_mem_cen_of (htc' k (Subgroup.mem_inf.1 (hKle hk)).1)
  have hdCt : b₁ * b₂ ^ 2 ∈ Cen t := hKC hdK
  have hKT : K ≤ Nor (Op 2 (Cen t)) := fun k hk => S36_nor_op2 (hKC hk)
  have hKN : K ≤ Nor (Subgroup.zpowers t) := fun k hk => S36_cen_le_nor t (hKC hk)
  have hNT : Subgroup.zpowers t ≤ Op 2 (Cen t) :=
    S36_zpowers_op2 d.ht htCen (fun g hg => (S36_comm_of_cen hg).symm)
  have hNnorm : ((Subgroup.zpowers t).subgroupOf (Op 2 (Cen t))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hgt : (g : G) * t = t * (g : G) :=
      (S36_comm_of_cen (S36_op2_le _ g.2)).symm
    have hc : (g : G) * t ^ k = t ^ k * (g : G) :=
      ((show Commute (g : G) t from hgt).zpow_right k).eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hk, hc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  have hT3 : ¬ 3 ∣ Nat.card (Op 2 (Cen t)) := S36_not_three_dvd (S36_op2_isPGroup _)
  have hsq : b₂ ^ 2 = b₂⁻¹ := S36_sq_eq_inv (pow3_of_mem_B d.sec hb2B)
  have hd3 : orderOf (b₁ * b₂ ^ 2) = 3 := by
    apply orderOf_eq_prime
    · have hcm : Commute b₁ (b₂ ^ 2) := (comm_of_mem_B d.sec hb1B hb2B).pow_right 2
      have h6 : (b₂ ^ 2) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, pow3_of_mem_B d.sec hb2B, one_pow]
      rw [hcm.mul_pow, pow3_of_mem_B d.sec hb1B, h6, one_mul]
    · rw [hsq]
      exact b₁b₂inv_ne_one d.sec
  have hfpf : ∀ u ∈ Op 2 (Cen t), (∃ n ∈ Subgroup.zpowers t,
      b₁ * b₂ ^ 2 * u * (b₁ * b₂ ^ 2)⁻¹ = u * n) → u ∈ Subgroup.zpowers t := by
    rintro u hu ⟨n, hn, hconj⟩
    obtain ⟨q, hq, n', hn', hqu⟩ := B_coprime_quot 2 (Op 2 (Cen t)) (Subgroup.zpowers t)
      (b₁ * b₂ ^ 2) (S36_op2_isPGroup _) hNT hNnorm (S36_nor_op2 hdCt)
      (S36_cen_le_nor t hdCt) (by rw [hd3]; norm_num) u hu ⟨n, hn, hconj⟩
    have hq' : q ∈ Subgroup.zpowers t := by
      rw [← hCT]; exact hq
    rw [hqu]
    exact mul_mem hq' hn'
  obtain ⟨h1, h2, r, hr⟩ := lemmaH_holds G K (Op 2 (Cen t)) (Subgroup.zpowers t)
    (b₁ * b₂ ^ 2) hK60 hKs hT3 hKT hNT hKN hNnorm hdK hd3 hfpf
  refine ⟨h1, h2, r, ?_⟩
  rw [hr, Nat.card_zpowers, d.ht]

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
