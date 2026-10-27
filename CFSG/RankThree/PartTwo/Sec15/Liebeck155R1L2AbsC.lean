module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2AbsA
import CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open scoped Pointwise

theorem res1L2C_exists_odd_pow_isPGroup_two {G : Type*} [Group G] [Finite G] (g : G) :
    ∃ m : ℕ, Odd m ∧ IsPGroup 2 (Subgroup.zpowers (g ^ m)) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨m, hm, IsPGroup.of_card (n := k) ?_⟩
  rw [Nat.card_zpowers, orderOf_pow_of_dvd hm.pos.ne' ⟨2 ^ k, by rw [hkm, mul_comm]⟩, hkm]
  exact Nat.mul_div_cancel _ hm.pos

theorem res1L2C_pow_conj_eq_self {G : Type*} [Group G] {g x : G} (h : g * x * g⁻¹ = x) (m : ℕ) :
    g ^ m * x * (g ^ m)⁻¹ = x := by
  have hc : Commute g x := mul_inv_eq_iff_eq_mul.mp h
  exact mul_inv_eq_iff_eq_mul.mpr ((hc.pow_left m).eq)

theorem res1L2C_pow_odd_conj_eq_inv {G : Type*} [Group G] {g x : G} (h : g * x * g⁻¹ = x⁻¹) {m : ℕ}
    (hm : Odd m) : g ^ m * x * (g ^ m)⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : g * x⁻¹ * g⁻¹ = x := by
    calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      _ = x := by rw [h, inv_inv]
  induction k with
  | zero => simpa using h
  | succ k ih =>
    calc g ^ (2 * (k + 1) + 1) * x * (g ^ (2 * (k + 1) + 1))⁻¹
        = g * (g * (g ^ (2 * k + 1) * x * (g ^ (2 * k + 1))⁻¹) * g⁻¹) * g⁻¹ := by group
      _ = x⁻¹ := by rw [ih, h2, h]

theorem res1L2C_exists_pGroup_containing_conj {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (B T₁ T₂ : Subgroup G) (h₁ : T₁ ≤ B) (h₂ : T₂ ≤ B) (hT₁ : IsPGroup p T₁)
    (hT₂ : IsPGroup p T₂) :
    ∃ S : Subgroup G, IsPGroup p S ∧ T₁ ≤ S ∧ ∃ b ∈ B, ∀ t ∈ T₂, b * t * b⁻¹ ∈ S := by
  obtain ⟨Q₁, hQ₁⟩ := (hT₁.comap_subtype (K := B)).exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := (hT₂.comap_subtype (K := B)).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B Q₂ Q₁
  refine ⟨(Q₁ : Subgroup B).map B.subtype, Q₁.isPGroup'.map _, fun t ht => ?_, b, b.2,
    fun t ht => ?_⟩
  · exact ⟨⟨t, h₁ ht⟩, hQ₁ ht, rfl⟩
  · have h1 : (⟨t, h₂ ht⟩ : B) ∈ (Q₂ : Subgroup B) := hQ₂ ht
    have h2 : MulAut.conj b • (⟨t, h₂ ht⟩ : B) ∈ MulAut.conj b • (Q₂ : Subgroup B) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← Sylow.coe_subgroup_smul, hb] at h2
    exact ⟨_, h2, rfl⟩

theorem res1L2C_conj_eq_of_unipotent {G : Type*} [Group G] {p N : ℕ} {ℓ : Subgroup G}
    (hℓp : ∀ y ∈ ℓ, y ^ p = 1) (hN : Nat.Coprime N p) {γ x : G} (hγN : γ ^ N = 1)
    (hγℓ : ∀ y ∈ ℓ, γ * y * γ⁻¹ = y) (hd : γ * x * γ⁻¹ * x⁻¹ ∈ ℓ) :
    γ * x * γ⁻¹ = x := by
  obtain ⟨d, hd_def⟩ : ∃ d, d = γ * x * γ⁻¹ * x⁻¹ := ⟨_, rfl⟩
  rw [← hd_def] at hd
  have hdx : γ * x * γ⁻¹ = d * x := by rw [hd_def]; group
  have hit : ∀ n : ℕ, γ ^ n * x * (γ ^ n)⁻¹ = d ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc γ ^ (n + 1) * x * (γ ^ (n + 1))⁻¹
          = γ * (γ ^ n * x * (γ ^ n)⁻¹) * γ⁻¹ := by group
        _ = γ * (d ^ n * x) * γ⁻¹ := by rw [ih]
        _ = (γ * d * γ⁻¹) ^ n * (γ * x * γ⁻¹) := by
            rw [conj_pow]; group
        _ = d ^ (n + 1) * x := by rw [hγℓ d hd, hdx, pow_succ, mul_assoc]
  have hdN : d ^ N = 1 := by
    have h := hit N
    rw [hγN, inv_one, one_mul, mul_one] at h
    exact (mul_eq_right.mp h.symm)
  have hdp : d ^ p = 1 := hℓp d hd
  have hord : orderOf d = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hdN) hN)
      (orderOf_dvd_of_pow_eq_one hdp)
  rw [hdx, orderOf_eq_one_iff.mp hord, one_mul]

theorem res1L2C_isElemAbelian_of_forall {p : ℕ} {G : Type*} [Group G] (E : Subgroup G)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : ∀ x ∈ E, x ^ p = 1) :
    CFSG.Open.IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, hp⟩

theorem res1L2C_isElemAbelian_sup_of_commute {p : ℕ} {G : Type*} [Group G] [Finite G]
    {E F : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) (hF : CFSG.Open.IsElemAbelian p F)
    (hc : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a) : CFSG.Open.IsElemAbelian p (E ⊔ F) := by
  have hEc : ∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hFc : ∀ b ∈ F, ∀ b' ∈ F, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hLE : E ≤ Subgroup.normalizer (F : Set G) := by
    intro a ha
    apply Subgroup.mem_normalizer_fintype
    intro b hb
    have : a * b * a⁻¹ = b := mul_inv_eq_iff_eq_mul.mpr (hc a ha b hb)
    rw [this]
    exact hb
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right E F hLE
  have hdecomp : ∀ x ∈ E ⊔ F, ∃ a ∈ E, ∃ b ∈ F, x = a * b := by
    intro x hx
    have hx' : x ∈ (↑(E ⊔ F) : Set G) := hx
    rw [hcoe] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  refine res1L2C_isElemAbelian_of_forall _ ?_ ?_
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hdecomp y hy
    exact (Commute.mul_left (Commute.mul_right (hEc a ha a' ha') (hc a ha b' hb'))
      (Commute.mul_right (hc a' ha' b hb).symm (hFc b hb b' hb'))).eq
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp x hx
    rw [(show Commute a b from hc a ha b hb).mul_pow, hE.2 a ha, hF.2 b hb, one_mul]

theorem Res1L2Abs.isCyclic_of_rank {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y]
    {p : ℕ} (D : Res1L2Abs P Y p) (R : Subgroup P) (hR : IsPGroup p R) (hRΘ : R ≤ D.Θ)
    (hRc : R ≤ Subgroup.centralizer ({D.j} : Set P)) : IsCyclic R := by
  have := Fact.mk D.hp
  by_contra hnc
  obtain ⟨B, hB, hBcard⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (D.hp.odd_of_ne_two (by have := D.hp5; omega)) hR hnc
  have := hB
  let E : Subgroup P := B.map R.subtype
  have hEcard : Nat.card E = p ^ 2 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact hBcard
  have hER : E ≤ R := Subgroup.map_subtype_le B
  have hEM : E ≤ D.M := hER.trans (hRc.trans D.hCM)
  have hEel : CFSG.Open.IsElemAbelian p E := by
    refine res1L2C_isElemAbelian_of_forall _ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have h := hB.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      have h2 := congrArg (fun x : B => ((x : R) : P)) h
      simpa using h2
    · rintro _ ⟨a, ha, rfl⟩
      have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := B) a ha
      have h2 := congrArg R.subtype h
      simpa using h2
  have hjE : D.j ∉ E := fun h =>
    D.hρj (MonoidHom.mem_ker.mp (D.hΘker (hRΘ (hER h))))
  have hzel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers D.j) := by
    refine res1L2C_isElemAbelian_of_forall _ ?_ ?_
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      show D.j ^ m * D.j ^ n = D.j ^ n * D.j ^ m
      rw [← zpow_add, ← zpow_add, add_comm]
    · rintro _ ⟨m, rfl⟩
      show (D.j ^ m) ^ p = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, D.hj, one_zpow]
  have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers D.j, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute a D.j := Subgroup.mem_centralizer_singleton_iff.mp (hRc (hER ha))
    exact (hc.zpow_right k).eq
  have hE'el := res1L2C_isElemAbelian_sup_of_commute hEel hzel hcomm
  have hE'M : E ⊔ Subgroup.zpowers D.j ≤ D.M :=
    sup_le hEM (Subgroup.zpowers_le.mpr D.hjM)
  have hlt : E < E ⊔ Subgroup.zpowers D.j :=
    lt_of_le_of_ne le_sup_left fun h =>
      hjE (by rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hcard := Subgroup.card_lt_of_lt hlt
  have := D.hrank _ hE'M hE'el
  rw [hEcard] at hcard
  omega

theorem res1L2C_exists_orderOf_eq_prime_of_ne_bot {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (R : Subgroup G) (hR : IsPGroup p R) (hne : R ≠ ⊥) : ∃ f ∈ R, orderOf f = p := by
  have hdvd : p ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq R (by simpa using hk)) hne
    · rw [hk]
      exact dvd_pow_self p (Nat.succ_ne_zero k)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) p hdvd
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem res1L2C_mem_zpowers_of_pow_eq_one_of_cyclic {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (R : Subgroup G) [IsCyclic R] (hR : IsPGroup p R) {f : G} (hfR : f ∈ R)
    (hf : orderOf f = p) {x : G} (hxR : x ∈ R) (hx : x ^ p = 1) : x ∈ Subgroup.zpowers f := by
  rcases CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC.mem_zpowers_or_mem_zpowers_of_isCyclic
    R hR f x hfR hxR with h | h
  · exact h
  · by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have hxo : orderOf x = p := orderOf_eq_prime hx hx1
      have heq : Subgroup.zpowers f = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hf, hxo])
      rw [heq]
      exact Subgroup.mem_zpowers x

theorem Res1L2Abs.exists_zeta {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y] {p : ℕ}
    (D : Res1L2Abs P Y p) (R : Subgroup P) (hRΘ : R ≤ D.Θ) (hR : IsPGroup p R)
    (hRmax : ∀ X : Subgroup P, X ≤ D.Θ → IsPGroup p X → R ≤ X → X = R)
    (hRc : R ≤ Subgroup.centralizer ({D.j} : Set P)) {f : P} (hfR : f ∈ R)
    (hf : orderOf f = p) (hfz : ∀ x ∈ R, x ^ p = 1 → x ∈ Subgroup.zpowers f) :
    ∃ ζ : P, ζ * f * ζ⁻¹ = f ∧ ζ * D.j * ζ⁻¹ = D.j⁻¹ := by
  have := Fact.mk D.hp
  have hfΘ : f ∈ D.Θ := hRΘ hfR
  by_cases hfC : f ∈ D.Cc
  · exact ⟨D.z, D.hCT f (Subgroup.mem_inf.mpr ⟨hfC, hfΘ⟩), D.hzj⟩
  have hzj' : D.z * D.j⁻¹ * D.z⁻¹ = D.j := by
    calc D.z * D.j⁻¹ * D.z⁻¹ = (D.z * D.j * D.z⁻¹)⁻¹ := by group
      _ = D.j := by rw [D.hzj, inv_inv]
  have hjC : ∀ x ∈ D.Cc ⊓ D.Θ, D.j * x * D.j⁻¹ = x := by
    intro x hx
    have hxC := (Subgroup.mem_inf.mp hx).1
    have hxΘ := (Subgroup.mem_inf.mp hx).2
    have hx' : D.j⁻¹ * x * D.j ∈ D.Cc ⊓ D.Θ := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · simpa using D.hCcM D.j⁻¹ (D.M.inv_mem D.hjM) x hxC
      · simpa using D.hΘn.conj_mem x hxΘ D.j⁻¹
    have h1 := D.hCT _ hx'
    have h2 := D.hCT _ hx
    have h3 : D.z * (D.j⁻¹ * x * D.j) * D.z⁻¹ = D.j * x * D.j⁻¹ := by
      calc D.z * (D.j⁻¹ * x * D.j) * D.z⁻¹
          = (D.z * D.j⁻¹ * D.z⁻¹) * (D.z * x * D.z⁻¹) * (D.z * D.j * D.z⁻¹) := by group
        _ = D.j * x * D.j⁻¹ := by rw [h2, D.hzj, hzj']
    have h4 : D.j * x * D.j⁻¹ = D.j⁻¹ * x * D.j := h3.symm.trans h1
    have h5 : (D.j * D.j) * x = x * (D.j * D.j) := by
      calc D.j * D.j * x = D.j * (D.j * x * D.j⁻¹) * D.j := by group
        _ = D.j * (D.j⁻¹ * x * D.j) * D.j := by rw [h4]
        _ = x * (D.j * D.j) := by group
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (D.hp.odd_of_ne_two (by have := D.hp5; omega))
    have hjk : (D.j * D.j) ^ ((p + 1) / 2) = D.j := by
      rw [← pow_two, ← pow_mul, show 2 * ((p + 1) / 2) = p + 1 by omega, pow_succ, D.hj, one_mul]
    have h6 : Commute (D.j * D.j) x := h5
    have h7 := (h6.pow_left ((p + 1) / 2)).eq
    rw [hjk] at h7
    exact mul_inv_eq_iff_eq_mul.mpr h7
  have hno : ∀ c ∈ D.Cc ⊓ D.Θ, orderOf c ≠ p := by
    intro c hc hcp
    have hcC := (Subgroup.mem_inf.mp hc).1
    have hcΘ := (Subgroup.mem_inf.mp hc).2
    have hcj : c ∈ Subgroup.centralizer ({D.j} : Set P) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hjC c hc)).symm
    have hcB : c ∈ D.Θ ⊓ Subgroup.centralizer ({D.j} : Set P) := Subgroup.mem_inf.mpr ⟨hcΘ, hcj⟩
    have hRB : R ≤ D.Θ ⊓ Subgroup.centralizer ({D.j} : Set P) := le_inf hRΘ hRc
    have hmaxB : ∀ X : Subgroup P, X ≤ D.Θ ⊓ Subgroup.centralizer ({D.j} : Set P) →
        IsPGroup p X → R ≤ X → X = R :=
      fun X hX hXp hRX => hRmax X (hX.trans inf_le_left) hXp hRX
    have hTp : IsPGroup p (Subgroup.zpowers c) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hcp, pow_one])
    obtain ⟨b, hbB, hb⟩ := res1L2A_exists_conj_mem_of_maximal _ R (Subgroup.zpowers c) hRB
      (Subgroup.zpowers_le.mpr hcB) hR hTp hmaxB
    have hy : b * c * b⁻¹ ∈ R := hb c (Subgroup.mem_zpowers c)
    have hbM : b ∈ D.M := D.hCM (Subgroup.mem_inf.mp hbB).2
    have hyC : b * c * b⁻¹ ∈ D.Cc := D.hCcM b hbM c hcC
    have hc1 : c ≠ 1 := by
      rintro rfl
      simp at hcp
      exact D.hp.one_lt.ne hcp
    have hy1 : b * c * b⁻¹ ≠ 1 := by
      intro h
      apply hc1
      calc c = b⁻¹ * (b * c * b⁻¹) * b := by group
        _ = 1 := by rw [h]; group
    have hcpow : c ^ p = 1 := by rw [← hcp]; exact pow_orderOf_eq_one c
    have hyp : (b * c * b⁻¹) ^ p = 1 := by rw [conj_pow, hcpow]; group
    have hyo : orderOf (b * c * b⁻¹) = p := orderOf_eq_prime hyp hy1
    have hyf : b * c * b⁻¹ ∈ Subgroup.zpowers f := hfz _ hy hyp
    have heq : Subgroup.zpowers (b * c * b⁻¹) = Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyf)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hf, hyo])
    apply hfC
    have : f ∈ Subgroup.zpowers (b * c * b⁻¹) := by rw [heq]; exact Subgroup.mem_zpowers f
    exact (Subgroup.zpowers_le.mpr hyC) this
  have hRN : R ≤ Subgroup.normalizer ((D.Cc ⊓ D.Θ : Subgroup P) : Set P) := by
    intro r hr
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hrM : r ∈ D.M := D.hCM (hRc hr)
    exact Subgroup.mem_inf.mpr ⟨D.hCcM r hrM x (Subgroup.mem_inf.mp hx).1,
      D.hΘn.conj_mem x (Subgroup.mem_inf.mp hx).2 r⟩
  have hpelt : ∀ c ∈ D.Cc ⊓ D.Θ, ∀ k : ℕ, orderOf c = p ^ k → c = 1 := by
    intro c hc k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hk
    · exfalso
      refine hno (c ^ (orderOf c / p)) ((D.Cc ⊓ D.Θ).pow_mem hc _) ?_
      rw [orderOf_pow_orderOf_div (orderOf_pos c).ne'
        (by rw [hk]; exact dvd_pow_self p hkpos.ne')]
  have hcoeQ := Subgroup.coe_mul_of_left_le_normalizer_right R (D.Cc ⊓ D.Θ) hRN
  have hRQ : R ≤ R ⊔ (D.Cc ⊓ D.Θ) := le_sup_left
  have hQmax : ∀ X : Subgroup P, X ≤ R ⊔ (D.Cc ⊓ D.Θ) → IsPGroup p X → R ≤ X → X = R := by
    intro X hXQ hXp hRX
    refine le_antisymm (fun x hx => ?_) hRX
    have hx' : x ∈ (↑(R ⊔ (D.Cc ⊓ D.Θ)) : Set P) := hXQ hx
    rw [hcoeQ] at hx'
    obtain ⟨r, hr, c, hc, rfl⟩ := hx'
    have hcX : c ∈ X := by
      have := X.mul_mem (X.inv_mem (hRX hr)) hx
      simpa using this
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hXp ⟨c, hcX⟩
    have hc1 := hpelt c hc k (by rw [← hk, Subgroup.orderOf_mk])
    subst hc1
    simpa using hr
  have hcommmem : ∀ r ∈ R, D.z * r * D.z⁻¹ * r⁻¹ ∈ D.Cc ⊓ D.Θ := by
    intro r hr
    have hrM : r ∈ D.M := D.hCM (hRc hr)
    have h1 : r * D.z * r⁻¹ ∈ D.Cc := D.hCcM r hrM D.z D.hzCc
    have h2 : r * D.z * r⁻¹ * D.z⁻¹ ∈ D.Cc := D.Cc.mul_mem h1 (D.Cc.inv_mem D.hzCc)
    have e : (r * D.z * r⁻¹ * D.z⁻¹)⁻¹ = D.z * r * D.z⁻¹ * r⁻¹ := by group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← e]
      exact D.Cc.inv_mem h2
    · exact D.Θ.mul_mem (D.hΘn.conj_mem r (hRΘ hr) D.z) (D.Θ.inv_mem (hRΘ hr))
  have hTQ : R.map (MulAut.conj D.z).toMonoidHom ≤ R ⊔ (D.Cc ⊓ D.Θ) := by
    rintro _ ⟨r, hr, rfl⟩
    have h := Subgroup.mul_mem _ (le_sup_right (a := R) (hcommmem r hr))
      (le_sup_left (b := D.Cc ⊓ D.Θ) hr)
    simpa [MulAut.conj_apply] using h
  obtain ⟨b, hbQ, hb⟩ := res1L2A_exists_conj_mem_of_maximal _ R _ hRQ hTQ hR (hR.map _) hQmax
  have hbQ' : b ∈ (↑(R ⊔ (D.Cc ⊓ D.Θ)) : Set P) := hbQ
  rw [hcoeQ] at hbQ'
  obtain ⟨r', hr', c, hc, rfl⟩ := hbQ'
  have hnorm : ∀ s ∈ R, c * D.z * s * (c * D.z)⁻¹ ∈ R := by
    intro s hs
    have h := hb (D.z * s * D.z⁻¹) ⟨s, hs, rfl⟩
    have h2 := R.mul_mem (R.mul_mem (R.inv_mem hr') h) hr'
    have e : r'⁻¹ * (r' * c * (D.z * s * D.z⁻¹) * (r' * c)⁻¹) * r' = c * D.z * s * (c * D.z)⁻¹ := by
      group
    rw [← e]
    simpa [MulAut.conj_apply] using h2
  have hcent : ∀ s ∈ R, c * D.z * s * (c * D.z)⁻¹ = s := by
    intro s hs
    have hsN := hRN hs
    have hc₀ := hcommmem s hs
    have hd : c * D.z * s * (c * D.z)⁻¹ * s⁻¹ ∈ D.Cc ⊓ D.Θ := by
      have h1 : (c * (D.z * s * D.z⁻¹ * s⁻¹)) * (s * c⁻¹ * s⁻¹) ∈ D.Cc ⊓ D.Θ :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hc₀)
          ((Subgroup.mem_normalizer_iff.mp hsN _).mp ((D.Cc ⊓ D.Θ).inv_mem hc))
      have e : (c * (D.z * s * D.z⁻¹ * s⁻¹)) * (s * c⁻¹ * s⁻¹) =
          c * D.z * s * (c * D.z)⁻¹ * s⁻¹ := by group
      rwa [e] at h1
    have hdR : c * D.z * s * (c * D.z)⁻¹ * s⁻¹ ∈ R := R.mul_mem (hnorm s hs) (R.inv_mem hs)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨_, hdR⟩
    have h1 := hpelt _ hd k (by rw [← hk, Subgroup.orderOf_mk])
    exact mul_inv_eq_one.mp h1
  refine ⟨c * D.z, hcent f hfR, ?_⟩
  have hcj : c * D.j = D.j * c := (mul_inv_eq_iff_eq_mul.mp (hjC c hc)).symm
  calc c * D.z * D.j * (c * D.z)⁻¹ = c * (D.z * D.j * D.z⁻¹) * c⁻¹ := by group
    _ = c * D.j⁻¹ * c⁻¹ := by rw [D.hzj]
    _ = D.j⁻¹ := mul_inv_eq_iff_eq_mul.mpr
        (show Commute c D.j⁻¹ from (show Commute c D.j from hcj).inv_right).eq

theorem res1L2C_exists_decomp_sup_zpowers {G : Type*} [Group G] [Finite G] {f j : G}
    (h : Commute f j) {x : G} (hx : x ∈ Subgroup.zpowers f ⊔ Subgroup.zpowers j) :
    ∃ a b : ℤ, x = f ^ a * j ^ b := by
  have hℓn : Subgroup.zpowers f ≤ Subgroup.normalizer (Subgroup.zpowers j : Set G) := by
    intro a ha
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h2 : f ^ m * j ^ k * (f ^ m)⁻¹ = j ^ k :=
      mul_inv_eq_iff_eq_mul.mpr (h.zpow_zpow m k).eq
    rw [h2]
    exact Subgroup.zpow_mem_zpowers _ _
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers f)
    (Subgroup.zpowers j) hℓn
  have hx' : x ∈ (↑(Subgroup.zpowers f ⊔ Subgroup.zpowers j) : Set G) := hx
  rw [hcoe] at hx'
  obtain ⟨u', hu', v, hv, rfl⟩ := hx'
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact ⟨a, b, rfl⟩

theorem res1L2C_mul_zpow_mem_sup_zpowers {G : Type*} [Group G] (f j : G) (a b : ℤ) :
    f ^ a * j ^ b ∈ Subgroup.zpowers f ⊔ Subgroup.zpowers j :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ _))
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

theorem res1L2C_mulAut_mul_conj_mul_inv {Y : Type*} [Group Y] (α : MulAut Y) (y : Y) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext x
  simp [MulAut.conj_apply]

theorem res1L2C_inv_conj_of_conj_eq_inv {G : Type*} [Group G] {g t : G} (h : g * t * g⁻¹ = t⁻¹) :
    g⁻¹ * t * g = t⁻¹ := by
  have h3 : g⁻¹ * t⁻¹ * g = t := by
    calc g⁻¹ * t⁻¹ * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
      _ = t := by group
  calc g⁻¹ * t * g = (g⁻¹ * t⁻¹ * g)⁻¹ := by group
    _ = t⁻¹ := by rw [h3]

theorem Res1L2Abs.false_of_commuting_two {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y]
    {p : ℕ} (D : Res1L2Abs P Y p) (R : Subgroup P) (hRΘ : R ≤ D.Θ)
    (hRc : R ≤ Subgroup.centralizer ({D.j} : Set P)) {f : P} (hfR : f ∈ R)
    (hf : orderOf f = p) (S : Subgroup P) (hS : IsPGroup 2 S) {ζ u : P} (hζS : ζ ∈ S)
    (huS : u ∈ S)
    (hζE : ζ ∈ Subgroup.normalizer ((Subgroup.zpowers f ⊔ Subgroup.zpowers D.j : Subgroup P) :
      Set P))
    (huE : u ∈ Subgroup.normalizer ((Subgroup.zpowers f ⊔ Subgroup.zpowers D.j : Subgroup P) :
      Set P))
    (hζf : ζ * f * ζ⁻¹ = f) (hζj : ζ * D.j * ζ⁻¹ = D.j⁻¹)
    (huinn : ∃ y : Y, D.ρ u = MulAut.conj y)
    (huinv : D.ρ u * D.ρ D.j * (D.ρ u)⁻¹ = (D.ρ D.j)⁻¹) : False := by
  have := Fact.mk D.hp
  have hfΘ : f ∈ D.Θ := hRΘ hfR
  have hfker : D.ρ f = 1 := MonoidHom.mem_ker.mp (D.hΘker hfΘ)
  have hfj : Commute f D.j := Subgroup.mem_centralizer_singleton_iff.mp (hRc hfR)
  have hfp : f ^ p = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  obtain ⟨E, hE⟩ : ∃ E : Subgroup P, E = Subgroup.zpowers f ⊔ Subgroup.zpowers D.j := ⟨_, rfl⟩
  rw [← hE] at hζE huE
  have hEdec : ∀ x ∈ E, ∃ a b : ℤ, x = f ^ a * D.j ^ b := fun x hx => by
    rw [hE] at hx
    exact res1L2C_exists_decomp_sup_zpowers hfj hx
  have hEmem : ∀ a b : ℤ, f ^ a * D.j ^ b ∈ E := fun a b => by
    rw [hE]
    exact res1L2C_mul_zpow_mem_sup_zpowers _ _ a b
  have hρE : ∀ a b : ℤ, D.ρ (f ^ a * D.j ^ b) = D.ρ D.j ^ b := by
    intro a b
    rw [map_mul, map_zpow, map_zpow, hfker, one_zpow, one_mul]
  have hEker : ∀ x ∈ E, D.ρ x = 1 → x ∈ Subgroup.zpowers f := by
    intro x hx h1
    obtain ⟨a, b, rfl⟩ := hEdec x hx
    rw [hρE, ← map_zpow] at h1
    have hjb : D.j ^ b = 1 := D.eq_one_of_mem_zpowers (Subgroup.zpow_mem_zpowers _ _) h1
    rw [hjb, mul_one]
    exact Subgroup.zpow_mem_zpowers _ _
  have hjE : D.j ∈ E := by
    rw [hE]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hfE : f ∈ E := by
    rw [hE]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hnf : ∀ g ∈ Subgroup.normalizer (E : Set P), g * f * g⁻¹ ∈ Subgroup.zpowers f := by
    intro g hg
    have h1 : g * f * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hg f).mp hfE
    have h2 : g * f * g⁻¹ ∈ D.Θ := D.hΘn.conj_mem f hfΘ g
    exact hEker _ h1 (MonoidHom.mem_ker.mp (D.hΘker h2))
  have hζℓ : ∀ y ∈ Subgroup.zpowers f, ζ * y * ζ⁻¹ = y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hζf]
  obtain ⟨γ, hγ⟩ : ∃ γ : P, γ = ζ⁻¹ * u⁻¹ * ζ * u := ⟨_, rfl⟩
  have hγinv : γ⁻¹ = u⁻¹ * ζ⁻¹ * u * ζ := by rw [hγ]; group
  have hγS : γ ∈ S := by
    rw [hγ]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem hζS) (S.inv_mem huS)) hζS) huS
  have hγE : γ ∈ Subgroup.normalizer (E : Set P) := by
    rw [hγ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hζE)
      (Subgroup.inv_mem _ huE)) hζE) huE
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS ⟨γ, hγS⟩
  rw [Subgroup.orderOf_mk] at hk
  have hγN : γ ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one γ
  have hN : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two D.hp).mpr (by have := D.hp5; omega))
  have hγf : γ * f * γ⁻¹ = f := by
    have h1 : ζ * (u * f * u⁻¹) * ζ⁻¹ = u * f * u⁻¹ := hζℓ _ (hnf u huE)
    have h2 : ζ⁻¹ * f * ζ = f := by
      calc ζ⁻¹ * f * ζ = ζ⁻¹ * (ζ * f * ζ⁻¹) * ζ := by rw [hζf]
        _ = f := by group
    calc γ * f * γ⁻¹ = ζ⁻¹ * u⁻¹ * (ζ * (u * f * u⁻¹) * ζ⁻¹) * u * ζ := by rw [hγinv, hγ]; group
      _ = ζ⁻¹ * u⁻¹ * (u * f * u⁻¹) * u * ζ := by rw [h1]
      _ = ζ⁻¹ * f * ζ := by group
      _ = f := h2
  have hγℓ : ∀ y ∈ Subgroup.zpowers f, γ * y * γ⁻¹ = y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hγf]
  have hℓp : ∀ y ∈ Subgroup.zpowers f, y ^ p = 1 := by
    intro y hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hfp, one_zpow]
  have hat : D.ρ ζ * D.ρ D.j * (D.ρ ζ)⁻¹ = (D.ρ D.j)⁻¹ := by
    have := congrArg D.ρ hζj
    simpa using this
  have hat' := res1L2C_inv_conj_of_conj_eq_inv hat
  have hbt' := res1L2C_inv_conj_of_conj_eq_inv huinv
  have hρd : D.ρ (γ * D.j * γ⁻¹ * D.j⁻¹) = 1 := by
    have h1 : D.ρ γ * D.ρ D.j * (D.ρ γ)⁻¹ = D.ρ D.j := by
      have e1 : D.ρ ζ * (D.ρ D.j)⁻¹ * (D.ρ ζ)⁻¹ = D.ρ D.j := by
        calc D.ρ ζ * (D.ρ D.j)⁻¹ * (D.ρ ζ)⁻¹ = (D.ρ ζ * D.ρ D.j * (D.ρ ζ)⁻¹)⁻¹ := by group
          _ = D.ρ D.j := by rw [hat, inv_inv]
      have e2 : (D.ρ ζ)⁻¹ * (D.ρ D.j)⁻¹ * D.ρ ζ = D.ρ D.j := by
        calc (D.ρ ζ)⁻¹ * (D.ρ D.j)⁻¹ * D.ρ ζ = ((D.ρ ζ)⁻¹ * D.ρ D.j * D.ρ ζ)⁻¹ := by group
          _ = D.ρ D.j := by rw [hat', inv_inv]
      calc D.ρ γ * D.ρ D.j * (D.ρ γ)⁻¹
          = (D.ρ ζ)⁻¹ * (D.ρ u)⁻¹ * D.ρ ζ * (D.ρ u * D.ρ D.j * (D.ρ u)⁻¹) * (D.ρ ζ)⁻¹ * D.ρ u *
              D.ρ ζ := by rw [hγ]; simp only [map_mul, map_inv]; group
        _ = (D.ρ ζ)⁻¹ * (D.ρ u)⁻¹ * (D.ρ ζ * (D.ρ D.j)⁻¹ * (D.ρ ζ)⁻¹) * D.ρ u * D.ρ ζ := by
            rw [huinv]; group
        _ = (D.ρ ζ)⁻¹ * ((D.ρ u)⁻¹ * D.ρ D.j * D.ρ u) * D.ρ ζ := by rw [e1]; group
        _ = (D.ρ ζ)⁻¹ * (D.ρ D.j)⁻¹ * D.ρ ζ := by rw [hbt']
        _ = D.ρ D.j := e2
    simp only [map_mul, map_inv]
    rw [h1]
    exact mul_inv_cancel _
  have hd : γ * D.j * γ⁻¹ * D.j⁻¹ ∈ Subgroup.zpowers f := by
    refine hEker _ (Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hγE _).mp hjE)
      (Subgroup.inv_mem _ hjE)) hρd
  have hγj : γ * D.j * γ⁻¹ = D.j := res1L2C_conj_eq_of_unipotent hℓp hN hγN hγℓ hd
  have hy : ζ * (u * D.j * u⁻¹) * ζ⁻¹ = (u * D.j * u⁻¹)⁻¹ := by
    have e : ζ⁻¹ * u⁻¹ * ζ * u * D.j * (u⁻¹ * ζ⁻¹ * u * ζ) = D.j := by
      rw [← hγinv, ← hγ]
      exact hγj
    calc ζ * (u * D.j * u⁻¹) * ζ⁻¹
        = u * (ζ * (ζ⁻¹ * u⁻¹ * ζ * u * D.j * (u⁻¹ * ζ⁻¹ * u * ζ)) * ζ⁻¹) * u⁻¹ := by group
      _ = u * (ζ * D.j * ζ⁻¹) * u⁻¹ := by rw [e]
      _ = (u * D.j * u⁻¹)⁻¹ := by rw [hζj]; group
  have hyE : u * D.j * u⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp huE _).mp hjE
  obtain ⟨a, b, hab⟩ := hEdec _ hyE
  have hjc : Commute (f ^ a) (D.j ^ b) := hfj.zpow_zpow a b
  have hζy : ζ * (f ^ a * D.j ^ b) * ζ⁻¹ = f ^ a * (D.j ^ b)⁻¹ := by
    calc ζ * (f ^ a * D.j ^ b) * ζ⁻¹ = (ζ * f ^ a * ζ⁻¹) * (ζ * D.j ^ b * ζ⁻¹) := by group
      _ = f ^ a * (D.j ^ b)⁻¹ := by rw [← conj_zpow, ← conj_zpow, hζf, hζj, inv_zpow]
  rw [hab, hζy] at hy
  have hfa : f ^ a * f ^ a = 1 := by
    have h1 : f ^ a * (D.j ^ b)⁻¹ = (f ^ a)⁻¹ * (D.j ^ b)⁻¹ := by
      rw [hy, mul_inv_rev]
      exact hjc.inv_inv.eq.symm
    have h2 : f ^ a = (f ^ a)⁻¹ := mul_right_cancel h1
    calc f ^ a * f ^ a = f ^ a * (f ^ a)⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel _
  have hfa1 : f ^ a = 1 := by
    have h2 : (f ^ a) ^ 2 = 1 := by rw [pow_two]; exact hfa
    have h3 : (f ^ a) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hfp, one_zpow]
    have h4 : orderOf (f ^ a) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h2)
          ((Nat.coprime_primes Nat.prime_two D.hp).mpr (by have := D.hp5; omega)))
        (orderOf_dvd_of_pow_eq_one h3)
    exact orderOf_eq_one_iff.mp h4
  have hmem : u * D.j * u⁻¹ ∈ Subgroup.zpowers D.j := by
    rw [hab, hfa1, one_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  exact D.false_of_inner_inverter (D.conj_eq_inv hmem huinv) huinn

theorem Res1L2Abs.false_of_zeta_inverter {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y]
    {p : ℕ} (D : Res1L2Abs P Y p) (R : Subgroup P) (hRΘ : R ≤ D.Θ)
    (hRc : R ≤ Subgroup.centralizer ({D.j} : Set P)) {f : P} (hfR : f ∈ R)
    (hf : orderOf f = p) (hfz : ∀ x ∈ R, x ^ p = 1 → x ∈ Subgroup.zpowers f) {ζ : P}
    (hζf : ζ * f * ζ⁻¹ = f) (hζj : ζ * D.j * ζ⁻¹ = D.j⁻¹) {w : P}
    (hwS : ∀ s ∈ R ⊔ Subgroup.zpowers D.j, w * s * w⁻¹ ∈ R ⊔ Subgroup.zpowers D.j)
    (hwinn : ∃ y : Y, D.ρ w = MulAut.conj y)
    (hwinv : D.ρ w * D.ρ D.j * (D.ρ w)⁻¹ = (D.ρ D.j)⁻¹) : False := by
  have := Fact.mk D.hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfΘ : f ∈ D.Θ := hRΘ hfR
  have hfker : D.ρ f = 1 := MonoidHom.mem_ker.mp (D.hΘker hfΘ)
  have hfj : Commute f D.j := Subgroup.mem_centralizer_singleton_iff.mp (hRc hfR)
  have hfp : f ^ p = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  obtain ⟨E, hE⟩ : ∃ E : Subgroup P, E = Subgroup.zpowers f ⊔ Subgroup.zpowers D.j := ⟨_, rfl⟩
  have hEdec : ∀ x ∈ E, ∃ a b : ℤ, x = f ^ a * D.j ^ b := fun x hx => by
    rw [hE] at hx
    exact res1L2C_exists_decomp_sup_zpowers hfj hx
  have hEmem : ∀ a b : ℤ, f ^ a * D.j ^ b ∈ E := fun a b => by
    rw [hE]
    exact res1L2C_mul_zpow_mem_sup_zpowers _ _ a b
  have hjE : D.j ∈ E := by rw [hE]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hjbp : ∀ b : ℤ, (D.j ^ b) ^ p = 1 := fun b => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, D.hj, one_zpow]
  have hfap : ∀ a : ℤ, (f ^ a) ^ p = 1 := fun a => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hfp, one_zpow]
  have hEpow : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := hEdec x hx
    rw [(hfj.zpow_zpow a b).mul_pow, hfap, hjbp, mul_one]
  have hEρ : ∀ x ∈ E, D.ρ x ∈ Subgroup.zpowers (D.ρ D.j) := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := hEdec x hx
    rw [map_mul, map_zpow, map_zpow, hfker, one_zpow, one_mul]
    exact Subgroup.zpow_mem_zpowers _ _
  have hEP : E ≤ R ⊔ Subgroup.zpowers D.j := by
    rw [hE]
    exact sup_le_sup_right (Subgroup.zpowers_le.mpr hfR) _
  have hLE : R ≤ Subgroup.normalizer (Subgroup.zpowers D.j : Set P) := by
    intro r hr
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute r D.j := Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)
    have : r * D.j ^ k * r⁻¹ = D.j ^ k := by
      rw [(hc.zpow_right k).eq]
      group
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _
  have hEchar : ∀ x ∈ R ⊔ Subgroup.zpowers D.j, x ^ p = 1 → x ∈ E := by
    intro x hx hxp
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right R (Subgroup.zpowers D.j) hLE
    have hx' : x ∈ (↑(R ⊔ Subgroup.zpowers D.j) : Set P) := hx
    rw [hcoe] at hx'
    obtain ⟨r, hr, v, hv, rfl⟩ := hx'
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hc : Commute r (D.j ^ b) :=
      (show Commute r D.j from Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)).zpow_right b
    have hrp : r ^ p = 1 := by
      have h1 : (r * D.j ^ b) ^ p = r ^ p * (D.j ^ b) ^ p := hc.mul_pow p
      rw [h1, hjbp, mul_one] at hxp
      exact hxp
    have hrf := hfz r hr hrp
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hrf
    exact hEmem a b
  have hwE : w ∈ Subgroup.normalizer (E : Set P) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have h1 := hwS x (hEP hx)
    have h2 : (w * x * w⁻¹) ^ p = 1 := by rw [conj_pow, hEpow x hx]; group
    exact hEchar _ h1 h2
  have hζE : ζ ∈ Subgroup.normalizer (E : Set P) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨a, b, rfl⟩ := hEdec x hx
    have : ζ * (f ^ a * D.j ^ b) * ζ⁻¹ = f ^ a * (D.j ^ b)⁻¹ := by
      calc ζ * (f ^ a * D.j ^ b) * ζ⁻¹ = (ζ * f ^ a * ζ⁻¹) * (ζ * D.j ^ b * ζ⁻¹) := by group
        _ = f ^ a * (D.j ^ b)⁻¹ := by rw [← conj_zpow, ← conj_zpow, hζf, hζj, inv_zpow]
    rw [this, ← zpow_neg]
    exact hEmem a (-b)
  obtain ⟨mw, hmw, hw2⟩ := res1L2C_exists_odd_pow_isPGroup_two w
  obtain ⟨mz, hmz, hz2⟩ := res1L2C_exists_odd_pow_isPGroup_two ζ
  have hw₂E : w ^ mw ∈ Subgroup.normalizer (E : Set P) := Subgroup.pow_mem _ hwE mw
  have hζ₂E : ζ ^ mz ∈ Subgroup.normalizer (E : Set P) := Subgroup.pow_mem _ hζE mz
  have hζ₂f : ζ ^ mz * f * (ζ ^ mz)⁻¹ = f := res1L2C_pow_conj_eq_self hζf mz
  have hζ₂j : ζ ^ mz * D.j * (ζ ^ mz)⁻¹ = D.j⁻¹ := res1L2C_pow_odd_conj_eq_inv hζj hmz
  obtain ⟨y₂, hy₂⟩ := hwinn
  have hw₂inv : D.ρ (w ^ mw) * D.ρ D.j * (D.ρ (w ^ mw))⁻¹ = (D.ρ D.j)⁻¹ := by
    rw [map_pow]
    exact res1L2C_pow_odd_conj_eq_inv hwinv hmw
  obtain ⟨S, hS, hζS, h, hhN, hh⟩ := res1L2C_exists_pGroup_containing_conj (p := 2)
    (Subgroup.normalizer (E : Set P)) (Subgroup.zpowers (ζ ^ mz)) (Subgroup.zpowers (w ^ mw))
    (Subgroup.zpowers_le.mpr hζ₂E) (Subgroup.zpowers_le.mpr hw₂E) hz2 hw2
  have huS : h * w ^ mw * h⁻¹ ∈ S := hh _ (Subgroup.mem_zpowers _)
  have huE : h * w ^ mw * h⁻¹ ∈ Subgroup.normalizer (E : Set P) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hw₂E) (Subgroup.inv_mem _ hhN)
  have huinn : ∃ y : Y, D.ρ (h * w ^ mw * h⁻¹) = MulAut.conj y := by
    refine ⟨D.ρ h (y₂ ^ mw), ?_⟩
    rw [← res1L2C_mulAut_mul_conj_mul_inv, map_mul, map_mul, map_inv, map_pow, hy₂, map_pow]
  have huinv : D.ρ (h * w ^ mw * h⁻¹) * D.ρ D.j * (D.ρ (h * w ^ mw * h⁻¹))⁻¹ =
      (D.ρ D.j)⁻¹ := by
    have hβT : ∀ t ∈ Subgroup.zpowers (D.ρ D.j),
        D.ρ (w ^ mw) * t * (D.ρ (w ^ mw))⁻¹ = t⁻¹ := by
      intro t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      rw [← conj_zpow, hw₂inv, inv_zpow]
    have ht' : (D.ρ h)⁻¹ * D.ρ D.j * D.ρ h ∈ Subgroup.zpowers (D.ρ D.j) := by
      have h1 : h⁻¹ * D.j * h ∈ E := (Subgroup.mem_normalizer_iff''.mp hhN D.j).mp hjE
      have := hEρ _ h1
      simpa using this
    have hβt' := hβT _ ht'
    calc D.ρ (h * w ^ mw * h⁻¹) * D.ρ D.j * (D.ρ (h * w ^ mw * h⁻¹))⁻¹
        = D.ρ h * (D.ρ (w ^ mw) * ((D.ρ h)⁻¹ * D.ρ D.j * D.ρ h) * (D.ρ (w ^ mw))⁻¹) *
            (D.ρ h)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = D.ρ h * ((D.ρ h)⁻¹ * D.ρ D.j * D.ρ h)⁻¹ * (D.ρ h)⁻¹ := by rw [hβt']
      _ = (D.ρ D.j)⁻¹ := by group
  exact D.false_of_commuting_two R hRΘ hRc hfR hf S hS (hζS (Subgroup.mem_zpowers _)) huS
    (hE ▸ hζ₂E) (hE ▸ huE) hζ₂f hζ₂j huinn huinv

theorem Res1L2Abs.false_of_sylow_central {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y]
    {p : ℕ} (D : Res1L2Abs P Y p) (R : Subgroup P) (hRΘ : R ≤ D.Θ)
    (hR : IsPGroup p R) (hRmax : ∀ X : Subgroup P, X ≤ D.Θ → IsPGroup p X → R ≤ X → X = R)
    (hRne : R ≠ ⊥) (hRc : R ≤ Subgroup.centralizer ({D.j} : Set P)) : False := by
  have := Fact.mk D.hp
  have := D.isCyclic_of_rank R hR hRΘ hRc
  obtain ⟨f, hfR, hf⟩ := res1L2C_exists_orderOf_eq_prime_of_ne_bot R hR hRne
  have hfz : ∀ x ∈ R, x ^ p = 1 → x ∈ Subgroup.zpowers f := fun x hx hxp =>
    res1L2C_mem_zpowers_of_pow_eq_one_of_cyclic R hR hfR hf hx hxp
  obtain ⟨ζ, hζf, hζj⟩ := D.exists_zeta R hRΘ hR hRmax hRc hfR hf hfz
  obtain ⟨w, hwS, hwinn, hwinv⟩ := D.exists_inverter R hRΘ hR hRmax hRc
  exact D.false_of_zeta_inverter R hRΘ hRc hfR hf hfz hζf hζj hwS hwinn hwinv

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
