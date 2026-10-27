module

public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.Quasithin.Background.A1cA131
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem opq1_exists_cover_of_le {G : Type*} [Group G] {X K : Subgroup G} (hKX : K ≤ X)
    (hX : IsQuotientOfSQTKTC ↥X) :
    ∃ (S : Type) (_ : Group S) (_ : Finite S),
      (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2) ∧
        ∃ φ : S →* ↥K, Function.Surjective φ := by
  obtain ⟨S, _, _, hSQT, -, φ, hφ⟩ := hX
  let K' : Subgroup ↥X := K.subgroupOf X
  refine ⟨↥(K'.comap φ), inferInstance, inferInstance, ?_, ?_⟩
  · intro p hp hp2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (K'.comap φ).subtype
      (K'.comap φ).subtype_injective).trans (hSQT p hp hp2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom.comp (φ.subgroupComap K'), ?_⟩
    exact (Subgroup.subgroupOfEquivOfLe hKX).surjective.comp
      (MonoidHom.subgroupComap_surjective φ K' hφ)

theorem opq1_mem_sup_of_le_centralizer {G : Type*} [Group G] {N R : Subgroup G}
    (h : R ≤ Subgroup.centralizer (N : Set G)) :
    ∀ x ∈ N ⊔ R, ∃ n ∈ N, ∃ r ∈ R, x = n * r := by
  intro x hx
  have hx' : x ∈ (↑(N ⊔ R) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N R
    (h.trans (Subgroup.centralizer_le_normalizer _)), Set.mem_mul] at hx'
  obtain ⟨n, hn, r, hr, rfl⟩ := hx'
  exact ⟨n, hn, r, hr, rfl⟩

theorem opq1_isPGroup_sup {G : Type*} [Group G] {p : ℕ} {N R : Subgroup G}
    (hN : IsPGroup p N) (hR : IsPGroup p R) (h : R ≤ Subgroup.centralizer (N : Set G)) :
    IsPGroup p ↥(N ⊔ R) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, hn, r, hr, rfl⟩ := opq1_mem_sup_of_le_centralizer h x hx
  obtain ⟨a, ha⟩ := hN ⟨n, hn⟩
  obtain ⟨b, hb⟩ := hR ⟨r, hr⟩
  have ha' : n ^ p ^ a = 1 := congrArg Subtype.val ha
  have hb' : r ^ p ^ b = 1 := congrArg Subtype.val hb
  have hc : Commute n r := Subgroup.mem_centralizer_iff.1 (h hr) n hn
  refine ⟨a + b, Subtype.ext ?_⟩
  change (n * r) ^ p ^ (a + b) = 1
  rw [hc.mul_pow, pow_add, pow_mul, ha', one_pow, mul_comm (p ^ a), pow_mul, hb', one_pow,
    mul_one]

theorem opq1_mem_sup_zpowers {G : Type*} [Group G] {P : Subgroup G} {τ : G} (hτ : τ * τ = 1)
    (hτn : τ ∈ Subgroup.normalizer (P : Set G)) :
    ∀ x ∈ P ⊔ Subgroup.zpowers τ, ∃ a ∈ P, x = a ∨ x = a * τ := by
  intro x hx
  have hnorm : Subgroup.zpowers τ ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.2 hτn
  have hx' : x ∈ (↑(P ⊔ Subgroup.zpowers τ) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P _ hnorm, Set.mem_mul] at hx'
  obtain ⟨a, ha, s, hs, rfl⟩ := hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  refine ⟨a, ha, ?_⟩
  have hT2 : τ ^ (2 : ℤ) = 1 := by rw [zpow_two, hτ]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [zpow_eq_zpow_emod k hT2, hk]
    simp
  · right
    rw [zpow_eq_zpow_emod k hT2, hk]
    simp

theorem opq1_subgroupOf_le_pCore {G : Type*} [Group G] {p : ℕ} {P K : Subgroup G}
    (hPp : IsPGroup p P) (hPK : P ≤ K) (hKn : K ≤ Subgroup.normalizer (P : Set G)) :
    P.subgroupOf K ≤ CFSG.Open.pCore p ↥K := by
  have hnormal : (P.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKn
  have hpK : IsPGroup p ↥(P.subgroupOf K) := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  exact CFSG.LieType.BorelTits.le_pCore p hnormal hpK

theorem opq1_cyclic_aux {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hS : IsQuotientOfSQTKTC ↥M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup G}
    (hPp : IsPGroup p P) (hPM : P ≤ M) {τ y : G} (hτM : τ ∈ M) (hτ : τ * τ = 1)
    (hτn : τ ∈ Subgroup.normalizer (P : Set G)) (hyP : y ∈ P) (hPy : ∀ a ∈ P, a * y = y * a)
    (hnc : ¬ τ * y = y * τ) {R : Subgroup G} (hRP : R ≤ P) (hRτ : ∀ r ∈ R, r * τ = τ * r) :
    IsCyclic ↥R := by
  have hp : p.Prime := Fact.out
  set Q : Subgroup G := P ⊔ Subgroup.zpowers τ
  have hPQ : P ≤ Q := le_sup_left
  have hτQ : τ ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
  have hyQ : y ∈ Q := hPQ hyP
  have hQn : Q ≤ Subgroup.normalizer (P : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hτn)
  have hQM : Q ≤ M := sup_le hPM (Subgroup.zpowers_le.2 hτM)
  have hle : P.subgroupOf Q ≤ CFSG.Open.pCore p ↥Q := opq1_subgroupOf_le_pCore hPp hPQ hQn
  have hdecomp := opq1_mem_sup_zpowers hτ hτn
  have hF : Subgroup.centralizer (CFSG.Open.pCore p ↥Q : Set ↥Q) ≤ CFSG.Open.pCore p ↥Q := by
    intro g hg
    have hy' : (⟨y, hyQ⟩ : ↥Q) ∈ CFSG.Open.pCore p ↥Q := hle (Subgroup.mem_subgroupOf.2 hyP)
    have hgy : y * (g : G) = (g : G) * y :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg _ hy')
    obtain ⟨a, haP, hcase⟩ := hdecomp (g : G) g.2
    rcases hcase with h | h
    · exact hle (Subgroup.mem_subgroupOf.2 (h ▸ haP))
    · exfalso
      rw [h] at hgy
      apply hnc
      have h1 : a * (τ * y) = a * (y * τ) := by
        calc a * (τ * y) = a * τ * y := (mul_assoc _ _ _).symm
          _ = y * (a * τ) := hgy.symm
          _ = (y * a) * τ := (mul_assoc _ _ _).symm
          _ = (a * y) * τ := by rw [hPy a haP]
          _ = a * (y * τ) := mul_assoc _ _ _
      exact mul_left_cancel h1
  obtain ⟨S, _, _, hSrk, φ, hφ⟩ := opq1_exists_cover_of_le hQM hS
  have hconcl := A1c.A131Concl_of_surjective hp2 hF _ S φ hφ rfl (hSrk p hp hp2)
  let τ' : ↥Q := ⟨τ, hτQ⟩
  have hτ'2 : τ' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hτ)
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers τ') := A1c.isPGroup_two_zpowers hτ'2
  have hT1 : Subgroup.zpowers τ' ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    apply hnc
    have h1 : τ = 1 := congrArg Subtype.val h
    rw [h1, one_mul, mul_one]
  have hcyc := hconcl.1 (Subgroup.zpowers τ') hT2 hT1
  have hsub : R.subgroupOf Q ≤ CFSG.Open.pCore p ↥Q ⊓
      Subgroup.centralizer ((Subgroup.zpowers τ' : Subgroup ↥Q) : Set ↥Q) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    refine ⟨hle (Subgroup.mem_subgroupOf.2 (hRP hz)), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute τ' z := Subtype.ext (hRτ z hz).symm
    exact (hc.zpow_left k).eq
  have hc1 : IsCyclic ↥(R.subgroupOf Q) :=
    isCyclic_of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective hsub)
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (hRP.trans hPQ)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (hRP.trans hPQ)).surjective

set_option linter.unusedVariables false in
theorem opq_cyclic_of_inverting {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hS : IsQuotientOfSQTKTC ↥M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {y τ : G}
    (hyM : y ∈ M) (hτM : τ ∈ M) (hy : orderOf y = p) (hτ : τ * τ = 1) (hτy : τ * y * τ⁻¹ = y⁻¹)
    {R : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup p R) (hRy : ∀ r ∈ R, r * y = y * r)
    (hRτ : ∀ r ∈ R, r * τ = τ * r) (hRdisj : ∀ r ∈ R, r ∈ Subgroup.zpowers y → r = 1) :
    IsCyclic ↥R := by
  have hp : p.Prime := Fact.out
  have hnc : ¬ τ * y = y * τ := by
    intro h
    have h1 : y = y⁻¹ := by
      rw [← hτy, h, mul_inv_cancel_right]
    have h2 : y ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel y
    have h3 : p ∣ 2 := hy ▸ orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)
  have hRc : R ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    exact (Commute.zpow_left (show Commute y r from (hRy r hr).symm) k).eq
  have hNp : IsPGroup p ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hPp : IsPGroup p ↥(Subgroup.zpowers y ⊔ R) := opq1_isPGroup_sup hNp hR hRc
  have hyP : y ∈ Subgroup.zpowers y ⊔ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hRP : R ≤ Subgroup.zpowers y ⊔ R := le_sup_right
  have hPM : Subgroup.zpowers y ⊔ R ≤ M := sup_le (Subgroup.zpowers_le.2 hyM) hRM
  have hPy : ∀ a ∈ Subgroup.zpowers y ⊔ R, a * y = y * a := by
    have hle : Subgroup.zpowers y ⊔ R ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      · intro r hr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hRy r hr
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle ha)
  have hτn : τ ∈ Subgroup.normalizer ((Subgroup.zpowers y ⊔ R : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    have hle : Subgroup.zpowers y ⊔ R ≤
        (Subgroup.zpowers y ⊔ R).comap (MulAut.conj τ).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
        change τ * y * τ⁻¹ ∈ _
        rw [hτy]
        exact Subgroup.inv_mem _ hyP
      · intro r hr
        rw [Subgroup.mem_comap]
        change τ * r * τ⁻¹ ∈ _
        rw [← hRτ r hr, mul_inv_cancel_right]
        exact hRP hr
    exact hle hn
  exact opq1_cyclic_aux hS hp2 hPp hPM hτM hτ hτn hyP hPy hnc hRP hRτ

end CFSG.Quasithin
