module

public import CFSG.RankThree.PartOne.S12.PerfectOddPrime
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.H13.Ch4.T425

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_fixed {X B : Subgroup G} {p : ℕ} [Fact p.Prime] (hX : IsPGroup p X)
    (hB : ¬ p ∣ Nat.card B) (hXB : X ≤ Subgroup.normalizer (B : Set G)) {a : G}
    (ha : ∀ x ∈ X, a⁻¹ * (x * a * x⁻¹) ∈ B) :
    ∃ b ∈ B, ∀ x ∈ X, x * (a * b) * x⁻¹ = a * b := by
  have hmem : ∀ (x : ↥X) (b : ↥B), a⁻¹ * ((x : G) * (a * b) * (x : G)⁻¹) ∈ B := by
    intro x b
    have h2 : (x : G) * b * (x : G)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hXB x.2) b).mp b.2
    have e : a⁻¹ * ((x : G) * (a * b) * (x : G)⁻¹) =
        (a⁻¹ * ((x : G) * a * (x : G)⁻¹)) * ((x : G) * b * (x : G)⁻¹) := by group
    rw [e]
    exact B.mul_mem (ha x x.2) h2
  let _ : MulAction ↥X ↥B :=
    { smul := fun x b => ⟨a⁻¹ * ((x : G) * (a * b) * (x : G)⁻¹), hmem x b⟩
      one_smul := fun b => Subtype.ext (by
        show a⁻¹ * (((1 : ↥X) : G) * (a * b) * ((1 : ↥X) : G)⁻¹) = b
        simp)
      mul_smul := fun x y b => Subtype.ext (by
        show a⁻¹ * (((x * y : ↥X) : G) * (a * b) * ((x * y : ↥X) : G)⁻¹) =
          a⁻¹ * ((x : G) * (a * (a⁻¹ * ((y : G) * (a * b) * (y : G)⁻¹))) * (x : G)⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  obtain ⟨b, hb⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card ↥B hB
  refine ⟨b, b.2, fun x hx => ?_⟩
  have h2 : a⁻¹ * (x * (a * (b : G)) * x⁻¹) = b := congrArg Subtype.val (hb ⟨x, hx⟩)
  calc x * (a * (b : G)) * x⁻¹ = a * (a⁻¹ * (x * (a * (b : G)) * x⁻¹)) := by group
    _ = a * b := by rw [h2]

theorem not_dvd_card_pCoreOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (L : Subgroup G) :
    ¬ p ∣ Nat.card (pCoreOf 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L).exists_card_eq
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem exists_mul_mem_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L X : Subgroup G}
    (hX : IsPGroup p X) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) {l : G} (hl : l ∈ L) :
    ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.centralizer (X : Set G) := by
  have hXB : X ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun x hx =>
    normalizer_le_normalizer_pCoreOf 2 L (hXL hx)
  have hO : (pCoreOf 2 L).subgroupOf L |>.Normal := normal_pCoreOf_subgroupOf L
  obtain ⟨b, hb, hfix⟩ := exists_mul_fixed hX (not_dvd_card_pCoreOf Fact.out hp2 L) hXB (a := l)
    fun x hx => by
      have h1 := hcomm x hx l hl
      have hlO : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ ∈ pCoreOf 2 L := by
        have := hO.conj_mem ⟨_, pCoreOf_le 2 L h1⟩ (Subgroup.mem_subgroupOf.mpr h1) ⟨l, hl⟩⁻¹
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      have e : l⁻¹ * (x * l * x⁻¹) = l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ := by group
      rw [e]
      exact hlO
  refine ⟨b, hb, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have := hfix x hx
  calc x * (l * b) = x * (l * b) * x⁻¹ * x := by group
    _ = l * b * x := by rw [this]

theorem exists_noncentral {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2) {L X : Subgroup G}
    (hLp : ⁅L, L⁆ = L) (hpL : p ∣ Nat.card L) (hX : IsPGroup p X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∃ z ∈ L, orderOf z = p ∧ z ∈ Subgroup.centralizer (X : Set G) ∧
      ∃ l ∈ L, z * l * z⁻¹ * l⁻¹ ∉ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 ↥L with hNdef
  have hN2 : IsPGroup 2 ↥N := by
    rw [hNdef]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hpQ : p ∣ Nat.card (↥L ⧸ N) := by
    have h1 := N.card_eq_card_quotient_mul_card_subgroup
    rw [h1] at hpL
    rcases (Nat.Prime.dvd_mul hpf.out).mp hpL with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hN2.exists_card_eq
      rw [hk] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpf.out Nat.prime_two).mp (hpf.out.dvd_of_dvd_pow h))
  obtain ⟨e, he, heZ⟩ :=
    CFSG.RankThree.PartOne.exists_pow_eq_one_not_mem_center_of_isPerfect hp2 inferInstance hpQ
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective e
  obtain ⟨b, hb, hlb⟩ := exists_mul_mem_centralizer hp2 hX hXL hcomm l₀.2
  have hbL : b ∈ L := pCoreOf_le 2 L hb
  set y : ↥L := l₀ * ⟨b, hbL⟩ with hydef
  have hyb : (QuotientGroup.mk y : ↥L ⧸ N) = QuotientGroup.mk l₀ := by
    rw [QuotientGroup.eq]
    have : y⁻¹ * l₀ = (⟨b, hbL⟩ : ↥L)⁻¹ := by rw [hydef]; group
    rw [this]
    exact N.inv_mem (C2Six.mem_pCore_two_iff.mpr hb)
  have hyp : y ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hyb]
    exact he
  obtain ⟨k, hk⟩ := hN2 ⟨y ^ p, hyp⟩
  have hk' : (y ^ p) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set z : ↥L := y ^ 2 ^ k with hzdef
  have hzp : z ^ p = 1 := by rw [hzdef, ← pow_mul, mul_comm, pow_mul, hk']
  have hzZ : (QuotientGroup.mk z : ↥L ⧸ N) ∉ Subgroup.center (↥L ⧸ N) := by
    intro hzc
    apply heZ
    have he1 : (QuotientGroup.mk l₀ : ↥L ⧸ N) ≠ 1 := fun h1 => heZ (h1 ▸ Subgroup.one_mem _)
    have ho : orderOf (QuotientGroup.mk l₀ : ↥L ⧸ N) = p :=
      (hpf.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one he)).resolve_left
        (fun h => he1 (orderOf_eq_one_iff.mp h))
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hpf.out).mpr (Ne.symm hp2))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpf.out.one_lt
    have hmz : (QuotientGroup.mk z : ↥L ⧸ N) ^ m = QuotientGroup.mk l₀ := by
      rw [hzdef, QuotientGroup.mk_pow, hyb, ← pow_mul, ← pow_mod_orderOf, ho, hm, pow_one]
    rw [← hmz]
    exact Subgroup.pow_mem _ hzc m
  have hz1 : z ≠ 1 := fun h => hzZ (by rw [h, QuotientGroup.mk_one]; exact Subgroup.one_mem _)
  refine ⟨z, z.2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact (hpf.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hzp)).resolve_left
      (fun h => hz1 (orderOf_eq_one_iff.mp h))
  · have hyC : ((y : ↥L) : G) ∈ Subgroup.centralizer (X : Set G) := hlb
    exact Subgroup.pow_mem _ hyC _
  · rw [Subgroup.mem_center_iff] at hzZ
    push Not at hzZ
    obtain ⟨q, hq⟩ := hzZ
    obtain ⟨l₁, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨l₁, l₁.2, fun hc => hq ?_⟩
    have hc' : z * l₁ * z⁻¹ * l₁⁻¹ ∈ N := C2Six.mem_pCore_two_iff.mpr hc
    rw [← QuotientGroup.eq_one_iff] at hc'
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hc'
    have e1 := mul_inv_eq_one.mp hc'
    rw [mul_inv_eq_iff_eq_mul] at e1
    exact e1.symm

theorem succ_le_pRank {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L E Y : Subgroup G}
    (hLp : ⁅L, L⁆ = L) (hpL : p ∣ Nat.card L) (hE : IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ x ∈ E, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) (hEY : E ≤ Y) (hLY : L ≤ Y) :
    k + 1 ≤ CFSG.Open.pRank p Y := by
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨z, hzL, hzo, hzC, l, hl, hzl⟩ := exists_noncentral hp2 hLp hpL hEp hEL hcomm
  have hzE : z ∉ E := fun hz => hzl (hcomm z hz l hl)
  obtain ⟨hE', hcard⟩ := exists_elemAbelian_sup_zpowers hE hzo
    (fun x hx => Subgroup.mem_centralizer_iff.mp hzC x hx) hzE
  refine le_pRank Fact.out (sup_le hEY (Subgroup.zpowers_le.mpr (hLY hzL))) hE' ?_
  rw [hcard, hk, pow_succ]

end CFSG.Quasithin.H13.Ch4.T425
