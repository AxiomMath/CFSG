module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion

public section

namespace CFSG.Walter

open scoped MatrixGroups
open CFSG.GorensteinWalter

universe u

theorem factorization_two_two_mul_odd {m : ℕ} (hm : Odd m) : (2 * m).factorization 2 = 1 := by
  rw [Nat.factorization_mul (by norm_num) (by rintro rfl; simp at hm),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))]

theorem psl2_order_factorization_two_of_mod_eight {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    (q * (q ^ 2 - 1) / 2).factorization 2 = 2 := by
  have hqodd : Odd q := by
    rcases hq with h | h <;> exact Nat.odd_iff.mpr (by omega)
  have hq1 : 1 < q := by rcases hq with h | h <;> omega
  rcases hq with h | h
  · have hodd : Odd ((q - 1) / 2) := Nat.odd_iff.mpr (by omega)
    rw [psl2_order_two_factorization_nonsplit hqodd hq1 hodd]
    have : (q + 1) / 2 = 2 * ((q + 1) / 4) := by omega
    rw [this, factorization_two_two_mul_odd (Nat.odd_iff.mpr (by omega))]
  · have heven : Even ((q - 1) / 2) := Nat.even_iff.mpr (by omega)
    rw [psl2_order_two_factorization_split hqodd hq1 heven]
    have : (q - 1) / 2 = 2 * ((q - 1) / 4) := by omega
    rw [this, factorization_two_two_mul_odd (Nat.odd_iff.mpr (by omega))]

theorem sq_mod_eight_of_odd {x : ℕ} (hx : Odd x) : x ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ := hx
  have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [this]
  have h2 : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
  obtain ⟨m, hm⟩ := h2
  rw [hm]
  omega

theorem odd_of_pow_mod_eight {p f : ℕ} (hp : Odd p) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) :
    Odd f := by
  by_contra hf
  obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp hf
  have : p ^ (k + k) = (p ^ k) ^ 2 := by ring
  rw [this, sq_mod_eight_of_odd hp.pow] at h8
  omega

theorem nonempty_sup_zpowers_mulEquiv_dihedralGroup {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) [IsCyclic U] (w : G) (hwU : w ∉ U) (hw : w * w = 1)
    (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) :
    Nonempty (↥(U ⊔ Subgroup.zpowers w) ≃* DihedralGroup (Nat.card U)) := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  set D := U ⊔ Subgroup.zpowers w with hD
  have hUD : U ≤ D := le_sup_left
  have hwD : w ∈ D := le_sup_right (a := U) (Subgroup.mem_zpowers w)
  let ρ : D := ⟨u, hUD u.2⟩
  let σ : D := ⟨w, hwD⟩
  have hUeq : U = Subgroup.zpowers (u : G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := hu ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨k, rfl⟩
      exact U.zpow_mem u.2 k
  have hgen : (⊤ : Subgroup D) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    change D = Subgroup.zpowers (u : G) ⊔ Subgroup.zpowers w
    rw [hD, ← hUeq]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simp [σ, pow_two, hw])
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simp [σ, ρ, hinv u u.2])
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    rintro ⟨k, hk⟩
    apply hwU
    have h := congrArg Subtype.val hk
    simp only [Subgroup.coe_zpow, ρ, σ] at h
    rw [← h]
    exact U.zpow_mem u.2 k
  obtain ⟨e⟩ := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = Nat.card U := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu]
  rw [hord] at e
  exact ⟨e⟩

theorem centralizer_eq_sup_zpowers_of_torus {G : Type*} [Group G] (U : Subgroup G) [IsCyclic U]
    (w : G) (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ R : Subgroup G, R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = U ⊔ Subgroup.zpowers w)
    {s : G} (hsU : s ∈ U) (hs : orderOf s = 2) :
    Subgroup.centralizer ({s} : Set G) = U ⊔ Subgroup.zpowers w := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  apply le_antisymm
  · rw [← hnormalizer (Subgroup.zpowers s) (Subgroup.zpowers_le.mpr hsU)
      (by rwa [ne_eq, Subgroup.zpowers_eq_bot])]
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hfix : ∀ k : ℤ, g * s ^ k * g⁻¹ = s ^ k := fun k => by
      rw [(Commute.zpow_right hg k).eq, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hfix k).symm⟩
    · rintro ⟨k, hk⟩
      simp only at hk
      refine ⟨k, ?_⟩
      calc s ^ k = g⁻¹ * (g * s ^ k * g⁻¹) * g := by group
        _ = g⁻¹ * s ^ k * g := by rw [hfix k]
        _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [hk]
        _ = h := by group
  · refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : U) ⟨s, hsU⟩)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hinv s hsU
      rw [inv_eq_of_mul_eq_one_right hs2, mul_inv_eq_iff_eq_mul] at h
      exact h

theorem isOddPrimePower_of_card {K : Type*} {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f)
    (hp : Odd p) (hf : 0 < f) : IsOddPrimePower (Nat.card K) :=
  ⟨p, f, Fact.out, hp, hf, hK⟩

section Field

variable (K : Type u) [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem psl2_sylow_two_card_eq_four (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (P : Sylow 2 PSL(2, K)) :
    Nat.card (P : Subgroup PSL(2, K)) = 4 := by
  rw [P.card_eq_multiplicity, psl2_card_formula K (isOddPrimePower_of_card hK hp hf), hK,
    psl2_order_factorization_two_of_mod_eight h8]
  norm_num

theorem psl2_sylow_two_isKleinFour (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (P : Sylow 2 PSL(2, K)) :
    IsKleinFour (P : Subgroup PSL(2, K)) := by
  obtain ⟨m, _hm, ⟨e⟩⟩ :=
    psl2_odd_hasDihedralSylowTwo_model K (isOddPrimePower_of_card hK hp hf) P
  have hcard := psl2_sylow_two_card_eq_four K hK hp hf h8 P
  have h2m : 2 ^ m = 2 := by
    have h : 4 = 2 * 2 ^ m :=
      hcard.symm.trans ((Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card)
    omega
  rw [h2m] at e
  exact ⟨hcard, (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩

theorem psl2_isConj_of_orderOf_eq_two (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    {x y : PSL(2, K)} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hinv : ∀ z : PSL(2, K), orderOf z = 2 → BenderSuzuki.PFAppendixIII.IsInvolution z :=
    fun z hz => ⟨fun h => by simp [h] at hz, by simpa [hz] using pow_orderOf_eq_one z⟩
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power K
    (isOddPrimePower_of_card hK hp hf) x y (hinv x hx) (hinv y hy)
  exact isConj_iff.mpr ⟨g, hg⟩

omit [Finite K] [Fact p.Prime] in
theorem centralizer_conj_eq_map {G : Type*} [Group G] (g s : G) :
    Subgroup.centralizer ({g * s * g⁻¹} : Set G) =
      (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [h]
      _ = s * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * s * g⁻¹) = g * ((g⁻¹ * x * g) * s) * g⁻¹ := by group
      _ = g * (s * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * s * g⁻¹ * x := by group

theorem psl2_centralizer_involution_of_torus (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (U : Subgroup PSL(2, K)) (w : PSL(2, K)) (hUc : IsCyclic U) (hwU : w ∉ U)
    (hw : w * w = 1) (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hcard : Nat.card (U ⊔ Subgroup.zpowers w : Subgroup PSL(2, K)) = 2 * Nat.card U)
    (hnormalizer : ∀ R : Subgroup PSL(2, K), R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set PSL(2, K)) = U ⊔ Subgroup.zpowers w)
    (heven : Even (Nat.card U)) {t : PSL(2, K)} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) = 2 * Nat.card U ∧
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, K)) ≃* DihedralGroup (Nat.card U)) := by
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 heven.two_dvd
  have hs' : orderOf (s : PSL(2, K)) = 2 := by rw [Subgroup.orderOf_coe, hs]
  have hCs := centralizer_eq_sup_zpowers_of_torus U w hinv hnormalizer s.2 hs'
  obtain ⟨g, hg⟩ := isConj_iff.mp (psl2_isConj_of_orderOf_eq_two K hK hp hf hs' ht)
  have hCt : Subgroup.centralizer ({t} : Set PSL(2, K)) =
      (U ⊔ Subgroup.zpowers w).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, centralizer_conj_eq_map, hCs]
  let e : Subgroup.centralizer ({t} : Set PSL(2, K)) ≃* ↥(U ⊔ Subgroup.zpowers w) :=
    (MulEquiv.subgroupCongr hCt).trans ((MulAut.conj g).subgroupMap _).symm
  obtain ⟨d⟩ := nonempty_sup_zpowers_mulEquiv_dihedralGroup U w hwU hw hinv
  exact ⟨(Nat.card_congr e.toEquiv).trans hcard, ⟨e.trans d⟩⟩

theorem psl2_centralizer_involution (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    {t : PSL(2, K)} (ht : orderOf t = 2) :
    (p ^ f % 4 = 1 → Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) = p ^ f - 1 ∧
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, K)) ≃*
        DihedralGroup ((p ^ f - 1) / 2))) ∧
    (p ^ f % 4 = 3 → Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) = p ^ f + 1 ∧
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, K)) ≃*
        DihedralGroup ((p ^ f + 1) / 2))) := by
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    rw [hK]
    obtain ⟨k, hk⟩ := hp.pow (n := f)
    exact ⟨k, by omega⟩
  constructor
  · intro h4
    obtain ⟨U, w, hUc, hUcard, _, hwU, hw, hinv, hcard, hnormalizer⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data (F := K) hK
    rw [hgcd, hK] at hUcard
    have heven : Even (Nat.card U) := by rw [hUcard]; exact Nat.even_iff.mpr (by omega)
    obtain ⟨h1, h2⟩ := psl2_centralizer_involution_of_torus K hK hp hf U w hUc hwU hw hinv hcard
      hnormalizer heven ht
    rw [hUcard] at h1 h2
    exact ⟨h1.trans (by omega), h2⟩
  · intro h4
    obtain ⟨U, w, hUc, hUcard, _, hwU, hw, hinv, hcard, hnormalizer⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data (F := K) hK
    rw [hgcd, hK] at hUcard
    have heven : Even (Nat.card U) := by rw [hUcard]; exact Nat.even_iff.mpr (by omega)
    obtain ⟨h1, h2⟩ := psl2_centralizer_involution_of_torus K hK hp hf U w hUc hwU hw hinv hcard
      hnormalizer heven ht
    rw [hUcard] at h1 h2
    exact ⟨h1.trans (by omega), h2⟩

theorem psl2_centralizer_involution_dihedral (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (h7 : 7 ≤ p ^ f) {t : PSL(2, K)} (ht : orderOf t = 2) :
    ∃ n : ℕ, 4 ≤ n ∧ Even n ∧ 2 * n = Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) ∧
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, K)) ≃* DihedralGroup n) := by
  obtain ⟨h1, h3⟩ := psl2_centralizer_involution K hK hp hf ht
  have hq : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have := Nat.odd_iff.mp (hp.pow (n := f))
    omega
  rcases hq with hq | hq
  · obtain ⟨hc, he⟩ := h1 hq
    exact ⟨(p ^ f - 1) / 2, by omega, Nat.even_iff.mpr (by omega), by omega, he⟩
  · obtain ⟨hc, he⟩ := h3 hq
    exact ⟨(p ^ f + 1) / 2, by omega, Nat.even_iff.mpr (by omega), by omega, he⟩

omit [Field K] [Finite K] [Fact p.Prime] in
theorem card_center_dihedralGroup {n : ℕ} (hn : 4 ≤ n) (heven : Even n) :
    Nat.card (Subgroup.center (DihedralGroup n)) = 2 := by
  have : NeZero n := ⟨by omega⟩
  rw [DihedralGroup.center_eq_closure_of_even_ne_two heven (by omega), Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [DihedralGroup.r_pow, DihedralGroup.one_def]
    congr 1
    obtain ⟨m, rfl⟩ := heven
    rw [show (m + m) / 2 = m by omega, ← Nat.cast_mul, show m * 2 = m + m by ring,
      ZMod.natCast_self]
  · rw [DihedralGroup.one_def, ne_eq, DihedralGroup.r.injEq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega

theorem psl2_center_centralizer_involution (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (h7 : 7 ≤ p ^ f) {t : PSL(2, K)} (ht : orderOf t = 2) :
    (Subgroup.center (Subgroup.centralizer ({t} : Set PSL(2, K)))).map
      (Subgroup.centralizer ({t} : Set PSL(2, K))).subtype = Subgroup.zpowers t := by
  set C := Subgroup.centralizer ({t} : Set PSL(2, K)) with hC
  obtain ⟨n, hn4, hneven, -, ⟨e⟩⟩ := psl2_centralizer_involution_dihedral K hK hp hf h7 ht
  have hcenter : Nat.card (Subgroup.center C) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans (card_center_dihedralGroup hn4 hneven)
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htZ : (⟨t, htC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have heq : Subgroup.zpowers (⟨t, htC⟩ : C) = Subgroup.center C :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htZ)
      (by rw [hcenter, Nat.card_zpowers, Subgroup.orderOf_mk, ht])
  rw [← heq, MonoidHom.map_zpowers]
  rfl

end Field

section GaloisField

variable {p f : ℕ} [Fact p.Prime]

theorem psl2_odd_sylow_two_isKleinFour (hp : Odd p) (hf : 0 < f)
    (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (P : Sylow 2 PSL(2, GaloisField p f)) :
    IsKleinFour (P : Subgroup PSL(2, GaloisField p f)) :=
  psl2_sylow_two_isKleinFour _ (GaloisField.card p f hf.ne') hp hf h8 P

theorem psl2_odd_isConj_of_orderOf_eq_two (hp : Odd p) (hf : 0 < f)
    {x y : PSL(2, GaloisField p f)} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  psl2_isConj_of_orderOf_eq_two _ (GaloisField.card p f hf.ne') hp hf hx hy

theorem psl2_odd_centralizer_involution (hp : Odd p) (hf : 0 < f)
    {t : PSL(2, GaloisField p f)} (ht : orderOf t = 2) :
    (p ^ f % 4 = 1 →
      Nat.card (Subgroup.centralizer ({t} : Set PSL(2, GaloisField p f))) = p ^ f - 1 ∧
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, GaloisField p f)) ≃*
        DihedralGroup ((p ^ f - 1) / 2))) ∧
    (p ^ f % 4 = 3 →
      Nat.card (Subgroup.centralizer ({t} : Set PSL(2, GaloisField p f))) = p ^ f + 1 ∧
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, GaloisField p f)) ≃*
        DihedralGroup ((p ^ f + 1) / 2))) :=
  psl2_centralizer_involution _ (GaloisField.card p f hf.ne') hp hf ht

theorem psl2_odd_center_centralizer_involution (hp : Odd p) (hf : 0 < f) (h7 : 7 ≤ p ^ f)
    {t : PSL(2, GaloisField p f)} (ht : orderOf t = 2) :
    (Subgroup.center (Subgroup.centralizer ({t} : Set PSL(2, GaloisField p f)))).map
      (Subgroup.centralizer ({t} : Set PSL(2, GaloisField p f))).subtype = Subgroup.zpowers t :=
  psl2_center_centralizer_involution _ (GaloisField.card p f hf.ne') hp hf h7 ht

end GaloisField

end CFSG.Walter
