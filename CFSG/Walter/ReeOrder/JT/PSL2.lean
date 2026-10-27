module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups

section Transport

variable {X P : Type*} [Group X] [Group P] (ι : P →* X)

theorem map_centralizer_of_injective (hι : Function.Injective ι) (H : Subgroup P) :
    (Subgroup.centralizer (H : Set P)).map ι =
      ι.range ⊓ Subgroup.centralizer ((H.map ι : Subgroup X) : Set X) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hx h hh]
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, fun h hh => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hx (ι h) ⟨h, hh, rfl⟩

theorem map_normalizer_of_injective (hι : Function.Injective ι) (H : Subgroup P) :
    (Subgroup.normalizer (H : Set P)).map ι =
      ι.range ⊓ Subgroup.normalizer ((H.map ι : Subgroup X) : Set X) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := H.map ι) (f := ι)
    (Subgroup.map_le_range ι H)
  rw [Subgroup.comap_map_eq_self_of_injective hι] at h
  rw [← h, Subgroup.map_comap_eq, inf_comm]

theorem map_centralizer_singleton_of_injective (hι : Function.Injective ι) (x : P) :
    (Subgroup.centralizer ({x} : Set P)).map ι =
      ι.range ⊓ Subgroup.centralizer ({ι x} : Set X) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, rfl⟩, by rw [← map_mul, ← map_mul, hz]⟩
  · rintro ⟨⟨z, rfl⟩, hz⟩
    exact ⟨z, hι (by rw [map_mul, map_mul, hz]), rfl⟩

end Transport

structure TorusData {X : Type*} [Group X] (L U : Subgroup X) (w : X) : Prop where
  le : U ≤ L
  cyclic : IsCyclic U
  w_mem : w ∈ L
  w_not_mem : w ∉ U
  w_mul_self : w * w = 1
  inv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹
  normalizer : ∀ R : Subgroup X, R ≤ U → R ≠ ⊥ →
    L ⊓ Subgroup.normalizer (R : Set X) = U ⊔ Subgroup.zpowers w

theorem TorusData.map {X P : Type*} [Group X] [Group P] (ι : P →* X)
    (hι : Function.Injective ι) {U : Subgroup P} {w : P}
    (hU : TorusData (⊤ : Subgroup P) U w) : TorusData ι.range (U.map ι) (ι w) where
  le := Subgroup.map_le_range ι U
  cyclic := by
    have := hU.cyclic
    exact isCyclic_of_surjective (U.equivMapOfInjective ι hι) (MulEquiv.surjective _)
  w_mem := ⟨w, rfl⟩
  w_not_mem := by
    rintro ⟨x, hx, hxw⟩
    exact hU.w_not_mem (hι hxw ▸ hx)
  w_mul_self := by rw [← map_mul, hU.w_mul_self, map_one]
  inv := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_inv, ← map_mul, hU.inv x hx, map_inv]
  normalizer := by
    intro R hRU hR
    have hRr : R ≤ ι.range := hRU.trans (Subgroup.map_le_range ι U)
    have hR0 : R.comap ι ≤ U := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hRU hx
      exact hι hyx ▸ hy
    have hR0ne : R.comap ι ≠ ⊥ := by
      intro h0
      apply hR
      rw [← Subgroup.map_comap_eq_self hRr, h0, Subgroup.map_bot]
    have h := hU.normalizer (R.comap ι) hR0 hR0ne
    rw [top_inf_eq] at h
    have h2 := map_normalizer_of_injective ι hι (R.comap ι)
    rw [Subgroup.map_comap_eq_self hRr, h, Subgroup.map_sup, MonoidHom.map_zpowers] at h2
    exact h2.symm

theorem mem_zpowers_of_orderOf_eq_two {X : Type*} [Group X] {v x : X} (hv : orderOf v = 2) :
    x ∈ Subgroup.zpowers v ↔ x = 1 ∨ x = v := by
  have h2 : v ^ (2 : ℤ) = 1 := by
    have := pow_orderOf_eq_one v
    rw [hv] at this
    rw [zpow_ofNat, this]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change v ^ k = 1
      rw [← Int.ediv_mul_add_emod k 2, hk, add_zero, mul_comm, zpow_mul, h2, one_zpow]
    · right
      change v ^ k = v
      rw [← Int.ediv_mul_add_emod k 2, hk, zpow_add, mul_comm, zpow_mul, h2, one_zpow,
        one_mul, zpow_one]
  · rintro (h | h) <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers v

theorem normalizer_zpowers_of_orderOf_eq_two {X : Type*} [Group X] {v : X}
    (hv : orderOf v = 2) :
    Subgroup.normalizer ((Subgroup.zpowers v : Subgroup X) : Set X) =
      Subgroup.centralizer ({v} : Set X) := by
  have hv1 : v ≠ 1 := by
    rintro rfl
    simp at hv
  have hconj : ∀ g x y : X, g * x * g⁻¹ = y → x = g⁻¹ * y * g := by
    rintro g x y rfl
    group
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rcases (mem_zpowers_of_orderOf_eq_two hv).mp ((h v).mp (Subgroup.mem_zpowers v)) with h1 | h1
    · exact absurd (by simpa using hconj _ _ _ h1) hv1
    · calc g * v = (g * v * g⁻¹) * g := by group
        _ = v * g := by rw [h1]
  · intro h x
    have hc : g * v * g⁻¹ = v := by rw [h, mul_inv_cancel_right]
    rw [mem_zpowers_of_orderOf_eq_two hv, mem_zpowers_of_orderOf_eq_two hv]
    constructor
    · rintro (h1 | h1) <;> rw [h1]
      · left; group
      · right; exact hc
    · rintro (h1 | h1)
      · left
        simpa using hconj _ _ _ h1
      · right
        rw [hconj _ _ _ h1, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem TorusData.centralizer_eq {X : Type*} [Group X] {L U : Subgroup X} {w : X}
    (hU : TorusData L U w) {v : X} (hvU : v ∈ U) (hv : orderOf v = 2) :
    L ⊓ Subgroup.centralizer ({v} : Set X) = U ⊔ Subgroup.zpowers w := by
  have hR : Subgroup.zpowers v ≤ U := (Subgroup.zpowers_le).mpr hvU
  have hRne : Subgroup.zpowers v ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    rintro rfl
    simp at hv
  rw [← normalizer_zpowers_of_orderOf_eq_two hv]
  exact hU.normalizer _ hR hRne

section PSL2

variable {K : Type*} [Field K] [Finite K]

theorem mod_four_eq_two_of_factorization_two_eq_one {n : ℕ} (hn : n ≠ 0)
    (h : n.factorization 2 = 1) : n % 4 = 2 := by
  have h2 : 2 ∣ n := (Nat.prime_two.pow_dvd_iff_le_factorization hn (k := 1)).mpr (by omega)
  have h4 : ¬ 4 ∣ n := fun h4 =>
    absurd ((Nat.prime_two.pow_dvd_iff_le_factorization hn (k := 2)).mp (by simpa using h4))
      (by omega)
  omega

theorem factorization_two_psl2_card_eq_two_iff {q : ℕ} (hq : Odd q) (hq1 : 1 < q) :
    (q * (q ^ 2 - 1) / 2).factorization 2 = 2 ↔ q % 8 = 3 ∨ q % 8 = 5 := by
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp hq
  rcases Nat.even_or_odd ((q - 1) / 2) with he | ho
  · rw [GorensteinWalter.psl2_order_two_factorization_split hq hq1 he]
    have hne : (q - 1) / 2 ≠ 0 := by omega
    constructor
    · intro h
      have := mod_four_eq_two_of_factorization_two_eq_one hne (by omega)
      omega
    · intro h
      have h8 : q % 8 = 5 := by
        rcases h with h | h
        · exfalso
          have := Nat.even_iff.mp he
          omega
        · exact h
      have : (q - 1) / 2 = 2 * ((q - 1) / 4) := by omega
      rw [this, Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by omega)]
  · rw [GorensteinWalter.psl2_order_two_factorization_nonsplit hq hq1 ho]
    have hne : (q + 1) / 2 ≠ 0 := by omega
    constructor
    · intro h
      have := mod_four_eq_two_of_factorization_two_eq_one hne (by omega)
      omega
    · intro h
      have h8 : q % 8 = 3 := by
        rcases h with h | h
        · exact h
        · exfalso
          have := Nat.odd_iff.mp ho
          omega
      have : (q + 1) / 2 = 2 * ((q + 1) / 4) := by omega
      rw [this, Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by omega)]

theorem psl2_mod_eight_of_isMulCommutative
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K)) (P : Sylow 2 PSL(2, K))
    (hP : IsMulCommutative (P : Subgroup PSL(2, K))) :
    Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5 := by
  obtain ⟨m, hm, ⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hK P
  have hcomm : IsMulCommutative (DihedralGroup (2 ^ m)) :=
    ⟨⟨fun a b => e.symm.injective (by
      rw [map_mul, map_mul]
      exact hP.is_comm.comm _ _)⟩⟩
  have hm1 : m = 1 := by
    by_contra hne
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact DihedralGroup.not_commutative (by omega) (by omega) hcomm
  have hPcard : Nat.card (P : Subgroup PSL(2, K)) = 4 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm1]
    norm_num
  have hmult := Sylow.card_eq_multiplicity P
  rw [hPcard, GorensteinWalter.psl2_card_formula K hK] at hmult
  obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hK
  have hqodd : Odd (Nat.card K) := hcard ▸ hpodd.pow
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  refine (factorization_two_psl2_card_eq_two_iff hqodd hq1).mp ?_
  have : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [this] at hmult
  exact (Nat.pow_right_injective le_rfl hmult).symm

theorem gcd_sub_one_two_of_odd {q : ℕ} (hq : Odd q) : Nat.gcd (q - 1) 2 = 2 :=
  Nat.gcd_eq_right (by obtain ⟨k, rfl⟩ := hq; exact ⟨k, by omega⟩)

theorem psl2_even_torus {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (hq : Odd (Nat.card K)) :
    ∃ U : Subgroup PSL(2, K), ∃ w : PSL(2, K), TorusData ⊤ U w ∧ Even (Nat.card U) ∧
      (Nat.card K % 4 = 3 ∧ 2 * Nat.card U = Nat.card K + 1 ∨
        Nat.card K % 4 = 1 ∧ 2 * Nat.card U + 1 = Nat.card K) := by
  have hgcd := gcd_sub_one_two_of_odd hq
  have hq2 : Nat.card K % 2 = 1 := Nat.odd_iff.mp hq
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with he | ho
  · obtain ⟨U, w, hUc, hUcard, -, hwU, hwsq, hwinv, -, hnorm⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data (F := K) hKcard
    rw [hgcd] at hUcard
    refine ⟨U, w, ⟨le_top, hUc, Subgroup.mem_top w, hwU, hwsq, hwinv, fun R hR hR1 => by
      rw [top_inf_eq]; exact hnorm R hR hR1⟩, hUcard ▸ he, Or.inr ⟨?_, ?_⟩⟩
    · have := Nat.even_iff.mp he
      omega
    · rw [hUcard]
      have := Nat.even_iff.mp he
      omega
  · obtain ⟨U, w, hUc, hUcard, -, hwU, hwsq, hwinv, -, hnorm⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data (F := K) hKcard
    rw [hgcd] at hUcard
    have ho' := Nat.odd_iff.mp ho
    refine ⟨U, w, ⟨le_top, hUc, Subgroup.mem_top w, hwU, hwsq, hwinv, fun R hR hR1 => by
      rw [top_inf_eq]; exact hnorm R hR hR1⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [hUcard, Nat.even_iff]
      omega
    · omega
    · rw [hUcard]
      omega

theorem psl2_odd_torus {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (hq : Odd (Nat.card K)) :
    ∃ U : Subgroup PSL(2, K), ∃ w : PSL(2, K), TorusData ⊤ U w ∧ Odd (Nat.card U) ∧
      (Nat.card K % 4 = 3 ∧ 2 * Nat.card U + 1 = Nat.card K ∨
        Nat.card K % 4 = 1 ∧ 2 * Nat.card U = Nat.card K + 1) := by
  have hgcd := gcd_sub_one_two_of_odd hq
  have hq2 : Nat.card K % 2 = 1 := Nat.odd_iff.mp hq
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with he | ho
  · obtain ⟨U, w, hUc, hUcard, -, hwU, hwsq, hwinv, -, hnorm⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data (F := K) hKcard
    rw [hgcd] at hUcard
    have he' := Nat.even_iff.mp he
    refine ⟨U, w, ⟨le_top, hUc, Subgroup.mem_top w, hwU, hwsq, hwinv, fun R hR hR1 => by
      rw [top_inf_eq]; exact hnorm R hR hR1⟩, ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [hUcard, Nat.odd_iff]
      omega
    · omega
    · rw [hUcard]
      omega
  · obtain ⟨U, w, hUc, hUcard, -, hwU, hwsq, hwinv, -, hnorm⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data (F := K) hKcard
    rw [hgcd] at hUcard
    have ho' := Nat.odd_iff.mp ho
    refine ⟨U, w, ⟨le_top, hUc, Subgroup.mem_top w, hwU, hwsq, hwinv, fun R hR hR1 => by
      rw [top_inf_eq]; exact hnorm R hR hR1⟩, hUcard ▸ ho, Or.inl ⟨?_, ?_⟩⟩
    · omega
    · rw [hUcard]
      omega

end PSL2

structure PSL2Facts {G : Type*} [Group G] (F : Subgroup G) (p f : ℕ) : Prop where
  prime : p.Prime
  odd_p : Odd p
  pos : 0 < f
  seven_le : 7 ≤ p ^ f
  card : Nat.card F = p ^ f * ((p ^ f) ^ 2 - 1) / 2
  simple : IsSimpleGroup F
  isConj : ∀ x ∈ F, ∀ y ∈ F, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ F, g * x * g⁻¹ = y
  kleinFour : ∀ V : Subgroup G, V ≤ F → IsKleinFour V →
    F ⊓ Subgroup.centralizer (V : Set G) = V
  mod_eight : (∀ P : Subgroup G, P ≤ F → IsPGroup 2 P → IsMulCommutative P) →
    p ^ f % 8 = 3 ∨ p ^ f % 8 = 5
  even_torus : ∀ v ∈ F, orderOf v = 2 → ∃ U : Subgroup G, ∃ w : G, TorusData F U w ∧ v ∈ U ∧
    (p ^ f % 4 = 3 ∧ 2 * Nat.card U = p ^ f + 1 ∨ p ^ f % 4 = 1 ∧ 2 * Nat.card U + 1 = p ^ f)
  odd_torus : ∃ U : Subgroup G, ∃ w : G, TorusData F U w ∧
    (p ^ f % 4 = 3 ∧ 2 * Nat.card U + 1 = p ^ f ∨ p ^ f % 4 = 1 ∧ 2 * Nat.card U = p ^ f + 1)
  cyclic : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ P : Subgroup G, P ≤ F → IsPGroup r P →
    IsCyclic P

theorem psl2Facts {G : Type*} [Group G]
    {p f : ℕ} [Fact p.Prime] (F : Subgroup G)
    (e : F ≃* PSL(2, GaloisField p f)) (hp : p ≠ 2) (hq : 5 < p ^ f) : PSL2Facts F p f := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  set K := GaloisField p f
  have hKcard : Nat.card K = p ^ f := GaloisField.card p f hf
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hK : GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, Fact.out, hpodd, Nat.one_le_iff_ne_zero.mpr hf, hKcard⟩
  have hq7 : 7 ≤ p ^ f := by
    have := Nat.odd_iff.mp hqodd
    omega
  let ι : PSL(2, K) →* G := F.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := F.subtype_injective.comp e.symm.injective
  have hιe : ∀ x : F, ι (e x) = x := fun x => by simp [ι]
  have hrange : ι.range = F := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, hιe ⟨x, hx⟩⟩
  have hmapcomap : ∀ X : Subgroup G, X ≤ F → (X.comap ι).map ι = X := fun X hX =>
    Subgroup.map_comap_eq_self (hrange ▸ hX)
  have hinvI : ∀ y : PSL(2, K), orderOf y = 2 → BenderSuzuki.PFAppendixIII.IsInvolution y := by
    intro y hy
    refine ⟨fun h1 => ?_, ?_⟩
    · rw [h1, orderOf_one] at hy
      omega
    · have := pow_orderOf_eq_one y
      rwa [hy] at this
  have hinvol : ∀ x (hx : x ∈ F), orderOf x = 2 →
      BenderSuzuki.PFAppendixIII.IsInvolution (e ⟨x, hx⟩) := by
    intro x hx hx2
    apply hinvI
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2]
  refine ⟨Fact.out, hpodd, Nat.pos_of_ne_zero hf, hq7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula K hK, hKcard]
  ·
    have : IsSimpleGroup PSL(2, K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact e.isSimpleGroup
  ·
    intro x hx y hy hx2 hy2
    obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power K hK _ _
      (hinvol x hx hx2) (hinvol y hy hy2)
    refine ⟨ι g, hrange ▸ ⟨g, rfl⟩, ?_⟩
    have := congrArg ι hg
    rwa [map_mul, map_mul, map_inv, hιe, hιe] at this
  ·
    intro V hVF hV
    set V₀ := V.comap ι
    have hV₀ : V₀.map ι = V := hmapcomap V hVF
    have eV : V₀ ≃* V := (V₀.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hV₀)
    have hV₀4 : IsKleinFour V₀ :=
      ⟨by rw [Nat.card_congr eV.toEquiv, hV.card_four],
        by rw [Monoid.exponent_eq_of_mulEquiv eV, hV.exponent_two]⟩
    have h := GorensteinWalter.psl2_kleinFour_centralizer_eq_self K hK V₀ hV₀4
    have h2 := map_centralizer_of_injective ι hι V₀
    rw [h, hV₀, hrange] at h2
    exact h2.symm
  ·
    intro hab
    let P₀ : Sylow 2 PSL(2, K) := default
    have hPF : (P₀ : Subgroup PSL(2, K)).map ι ≤ F := hrange ▸ Subgroup.map_le_range ι _
    have hP := hab _ hPF (P₀.isPGroup'.map ι)
    have eP := (P₀ : Subgroup PSL(2, K)).equivMapOfInjective ι hι
    have hP₀ : IsMulCommutative (P₀ : Subgroup PSL(2, K)) :=
      ⟨⟨fun a b => eP.injective (by rw [map_mul, map_mul]; exact hP.is_comm.comm _ _)⟩⟩
    have := psl2_mod_eight_of_isMulCommutative hK P₀ hP₀
    rwa [hKcard] at this
  ·
    intro v hv hv2
    obtain ⟨U₀, w₀, hU₀, hU₀even, hU₀card⟩ := psl2_even_torus hKcard (hKcard ▸ hqodd)
    obtain ⟨v₀, hv₀⟩ := exists_prime_orderOf_dvd_card' (G := U₀) 2 hU₀even.two_dvd
    have hv₀2 : orderOf (v₀ : PSL(2, K)) = 2 := by rw [Subgroup.orderOf_coe, hv₀]
    have hv₀I : BenderSuzuki.PFAppendixIII.IsInvolution (v₀ : PSL(2, K)) := hinvI _ hv₀2
    obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power K hK _ _
      hv₀I (hinvol v hv hv2)
    let ι' : PSL(2, K) →* G := ι.comp (MulAut.conj g).toMonoidHom
    have hι' : Function.Injective ι' := hι.comp (MulAut.conj g).injective
    have hrange' : ι'.range = F := by
      rw [← hrange]
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨(MulAut.conj g).symm y, by simp [ι']; group⟩
    have hT := hU₀.map ι' hι'
    rw [hrange'] at hT
    refine ⟨U₀.map ι', ι' w₀, hT, ⟨v₀, v₀.2, ?_⟩, ?_⟩
    · change ι (g * v₀ * g⁻¹) = v
      rw [hg, hιe]
    · rw [Subgroup.card_map_of_injective hι', ← hKcard]
      exact hU₀card
  ·
    obtain ⟨U₀, w₀, hU₀, -, hU₀card⟩ := psl2_odd_torus hKcard (hKcard ▸ hqodd)
    have hT := hU₀.map ι hι
    rw [hrange] at hT
    refine ⟨U₀.map ι, ι w₀, hT, ?_⟩
    rw [Subgroup.card_map_of_injective hι, ← hKcard]
    exact hU₀card
  ·
    intro r hr hr2 hrp P hPF hPr
    have : Fact r.Prime := ⟨hr⟩
    set P₀ := P.comap ι
    have hP₀ : P₀.map ι = P := hmapcomap P hPF
    have eP : P₀ ≃* P := (P₀.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hP₀)
    have hP₀r : IsPGroup r P₀ := hPr.of_equiv eP.symm
    obtain ⟨R, hR⟩ := hP₀r.exists_le_sylow
    have hRc : IsCyclic (R : Subgroup PSL(2, K)) :=
      GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hKcard (hKcard ▸ hq7) r
        hr2 (by
          rw [hKcard]
          exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Fact.out).mpr hrp)) R
    have : IsCyclic P₀ := Subgroup.isCyclic_of_le hR
    exact isCyclic_of_surjective eP eP.surjective

end CFSG.Walter.JT
