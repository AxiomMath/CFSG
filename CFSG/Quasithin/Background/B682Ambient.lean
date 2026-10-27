module

public import CFSG.Quasithin.Background.E2Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

theorem mem_of_pows_mem_of_coprime {Y : Type*} [Group Y] {N : Subgroup Y} {x : Y} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : x ^ m ∈ N) (hn : x ^ n ∈ N) : x ∈ N := by
  have h := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one, Nat.cast_one] at h
  have e : x = (x ^ m) ^ (Nat.gcdA m n) * (x ^ n) ^ (Nat.gcdB m n) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact N.mul_mem (N.zpow_mem hm _) (N.zpow_mem hn _)

theorem card_eq_card_map_mul_inf_ker {Y Y' : Type*} [Group Y] [Group Y'] (f : Y →* Y')
    (H : Subgroup Y) : Nat.card ↥H = Nat.card ↥(H.map f) * Nat.card ↥(H ⊓ f.ker) := by
  have h := Subgroup.card_mul_index (f.domRestrict H).ker
  rw [Subgroup.index_ker] at h
  have h1 : (f.domRestrict H).range = H.map f := by
    ext b
    simp [Subgroup.mem_map]
  have h3 : Nat.card ↥(f.domRestrict H).ker = Nat.card ↥(H ⊓ f.ker) := by
    rw [MonoidHom.ker_domRestrict, ← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [h1, h3] at h
  rw [← h, mul_comm]

theorem isCyclic_of_pRank_le_one {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {H P : Subgroup Y} (hPH : P ≤ H) (hP : IsPGroup p ↥P)
    (hr : CFSG.Open.pRank p H ≤ 1) : IsCyclic ↥P := by
  by_contra hnc
  have : Fact (IsPGroup p ↥P) := ⟨hP⟩
  obtain ⟨S, -, hcard, hel⟩ := CFSG.lemma_4_5_a hp2 hnc
  set E := S.map P.subtype
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', hae⟩ := a.2
      obtain ⟨b', hb', hbe⟩ := b.2
      apply Subtype.ext
      show (a : Y) * b = b * a
      rw [← hae, ← hbe]
      have hc : (⟨a', ha'⟩ : ↥S) * ⟨b', hb'⟩ = ⟨b', hb'⟩ * ⟨a', ha'⟩ := hel.is_comm.comm _ _
      have := congrArg (fun s : ↥S => ((s : ↥P) : Y)) hc
      simpa using this
    · obtain ⟨s, hs, rfl⟩ := hx
      have h1 := congrArg Subtype.val (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := S)
        s hs)
      simpa using h1
  have hEc : Nat.card ↥E = p ^ 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hcard]
  have hbdd : BddAbove {k | ∃ E : Subgroup Y, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card ↥E = p ^ k} := by
    refine ⟨Nat.card Y, fun k hk => ?_⟩
    obtain ⟨E', -, -, hE'⟩ := hk
    have h1 : p ^ k ≤ Nat.card Y := hE' ▸ Subgroup.card_le_card_group E'
    have h2 : k < p ^ k := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    omega
  have h2 : 2 ≤ CFSG.Open.pRank p H :=
    le_csSup hbdd ⟨E, (Subgroup.map_subtype_le S).trans hPH, hE, hEc⟩
  omega

namespace MinParabolic

variable {X : Type*} [Group X] [Finite X] {T M : Subgroup X}

theorem sylow_map_eq_pCore (h : MinParabolic (⊤ : Subgroup X) T M) (hsolv : Group.IsSolvable X)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) {P : Subgroup X}
    (hP : IsPGroup p ↥P) (hPs : Nat.card ↥P = p ^ (Nat.card X).factorization p) :
    P.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) =
        CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X) ∧
      (kerIn M ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) =
        (frattini (CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X))).map
          (CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X)).subtype ∧
      ∀ y : X ⧸ CFSG.Open.pCore 2 X, ∃ k : ℕ,
        y ^ 2 ^ k ∈ CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p', hp', hp'2, hO2p2, hJbar, hne, -⟩ := h.solvable_structure hsolv
  obtain ⟨p₀, -, -, hq⟩ := h.exists_odd_prime_of_solvable hsolv
  have hp'X : p' ∣ Nat.card X := by
    have : Fact p'.Prime := ⟨hp'⟩
    have h1 := (CFSG.LieType.BorelTits.pCore_isPGroup p' (G := X ⧸ kerIn M ⊤)).card_eq_or_dvd
    rcases h1 with h1 | h1
    · exact absurd (Subgroup.card_eq_one.1 h1) hne
    · exact h1.trans ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.index_dvd_card _))
  have hpp' : p = p' := by
    rcases hq p hp hpX with h1 | h1
    · exact absurd h1 hp2
    rcases hq p' hp' hp'X with h2 | h2
    · exact absurd h2 hp'2
    rw [h1, h2]
  subst hpp'
  have : Fact p.Prime := ⟨hp⟩
  set Q := CFSG.Open.pCore 2 X with hQ
  set φ := QuotientGroup.mk' Q with hφ
  set Op := CFSG.Open.pCore p (X ⧸ Q) with hOp
  have h2P : ∀ y : X, ∃ k : ℕ, φ y ^ 2 ^ k ∈ Op := by
    intro y
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p X p)).mp hO2p2 y
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_comap.mp hk⟩
  refine ⟨?_, hJbar, fun y => ?_⟩
  swap
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q y
    exact h2P x
  have hle : P.map φ ≤ Op := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := h2P y
    obtain ⟨a, ha⟩ := hP ⟨y, hy⟩
    have ha' : y ^ p ^ a = 1 := congrArg Subtype.val ha
    refine mem_of_pows_mem_of_coprime (m := 2 ^ k) (n := p ^ a)
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))) hk ?_
    rw [← map_pow, ha', map_one]
    exact Op.one_mem
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥φ.ker) := by
    rw [hφ, QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).1 hP
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 hQ2
    rw [hn, hm]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hcP : Nat.card ↥(P.map φ) = Nat.card ↥P := by
    have h1 := card_eq_card_map_mul_inf_ker φ P
    rw [(Subgroup.disjoint_of_coprime_natCard hcop).eq_bot, Subgroup.card_bot, mul_one] at h1
    exact h1.symm
  have hcOp : Nat.card ↥Op ≤ Nat.card ↥(P.map φ) := by
    rw [hcP, hPs]
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p)).1
      (CFSG.LieType.BorelTits.pCore_isPGroup p (G := X ⧸ Q))
    rw [hb]
    have h1 : p ^ b ∣ Nat.card X := by
      rw [← hb]
      exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.index_dvd_card _)
    have h2 := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1
    exact Nat.pow_le_pow_right hp.pos h2
  exact Subgroup.eq_of_le_of_card_ge hle hcOp

end MinParabolic

namespace MinParabolic

variable {G : Type*} [Group G] [Finite G] {H T M : Subgroup G}

theorem exists_odd_prime_ambient (h : MinParabolic H T M) (hsolv : Group.IsSolvable ↥H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥H ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥H → q = 2 ∨ q = p := by
  obtain ⟨p, hp, hp2, hq⟩ := h.subgroupOf.exists_odd_prime_of_solvable hsolv
  refine ⟨p, hp, hp2, ?_, hq⟩
  by_contra hpH
  have hX : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have hpow : Nat.card ↥H = 2 ^ (Nat.card ↥H).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hX fun {d} hd hdX =>
      (hq d hd hdX).resolve_right fun e => hpH (e ▸ hdX)
  apply h.subgroupOf.not_isPGroup_top
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := (Nat.card ↥H).primeFactorsList.length) ?_
  rw [Subgroup.card_top]
  exact hpow

theorem isCyclic_twoResidual_ambient (h : MinParabolic H T M) (hsolv : Group.IsSolvable ↥H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpH : p ∣ Nat.card ↥H)
    (hr : CFSG.Open.pRank p H ≤ 1) :
    IsCyclic ↥(twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H))) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p ↥H) := inferInstance
  have hPs := P.card_eq_multiplicity
  obtain ⟨h1, -, h2P⟩ := h.subgroupOf.sylow_map_eq_pCore hsolv hp hp2 hpH P.isPGroup' hPs
  have hPc : IsCyclic ↥(P : Subgroup ↥H) := by
    have h2 := isCyclic_of_pRank_le_one hp2 (Subgroup.map_subtype_le (P : Subgroup ↥H))
      (P.isPGroup'.map H.subtype) hr
    have := h2
    exact isCyclic_of_surjective
      (((P : Subgroup ↥H).equivMapOfInjective _ H.subtype_injective).symm.toMonoidHom)
      (MulEquiv.surjective _)
  rw [E2.twoResidual_eq_pCore hp hp2 h2P, ← h1]
  exact isCyclic_of_surjective ((QuotientGroup.mk' _).subgroupMap (P : Subgroup ↥H))
    (MonoidHom.subgroupMap_surjective _ _)

theorem e2_1_ambient (h : MinParabolic H T M)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2) (hsolv : Group.IsSolvable ↥H)
    (hR : ¬ pCoreOf 2 (M.subgroupOf H) ≤ CFSG.Open.pCore 2 ↥H ∨
      ∃ t ∈ T.subgroupOf H, (∀ j ∈ kerIn (M.subgroupOf H) ⊤,
        t * j * t⁻¹ * j⁻¹ ∈ pCoreOf 2 (kerIn (M.subgroupOf H) ⊤)) ∧ t ∉ CFSG.Open.pCore 2 ↥H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (Nonempty (twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)) ≃*
          Multiplicative (ZMod p)) ∨
        IsElemAbelianOfRank p 2 (twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H))) ∨
        IsPOnePlusTwo p (twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)))) := by
  refine E2_1 h.subgroupOf (fun p hp hp2 => ?_) hsolv hR
  have : Fact p.Prime := ⟨hp⟩
  rw [pRank_top_subtype]
  exact hSQT p hp hp2

end MinParabolic

end CFSG.Quasithin
