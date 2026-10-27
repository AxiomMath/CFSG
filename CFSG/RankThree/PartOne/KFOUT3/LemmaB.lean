module

public import CFSG.RankThree.PartOne.N143.JDiag
public import CFSG.RankThree.PartOne.KFOUT3.CycCent
public import CFSG.RankThree.PartOne.KFOUT3.CycMono
public import CFSG.RankThree.PartOne.KFOUT3.SLCard

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143 CFSG.Assembly.LowTwoRank

section Field

variable {K : Type} [Field K]

theorem eq_one_of_pow_three [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) {r : K} (hr : r ^ 3 = 1) :
    r = 1 := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  let u : Kˣ := Units.mk0 r hr0
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hr)
  by_contra hne
  have hu1 : u ≠ 1 := fun h => hne (congrArg Units.val h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  rw [Nat.card_units, hord] at hdvd
  exact h3 hdvd

theorem units_eq_one_of_pow_three [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) {u : Kˣ}
    (hu : u ^ 3 = 1) : u = 1 :=
  Units.ext (eq_one_of_pow_three h3 (by simpa using congrArg Units.val hu))

theorem SL3_center_eq_one [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1) {z : SL3 K}
    (hz : z ∈ Subgroup.center (SL3 K)) : z = 1 := by
  obtain ⟨r, hr, hzr⟩ := exists_scalar_of_mem_center hz
  have hr1 : r = 1 := eq_one_of_pow_three h3 hr
  apply Subtype.ext
  rw [hzr, hr1, map_one]
  rfl

end Field

section Cover

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [Finite K] {ρ : SL3 K →* G}

omit [Finite G] in
theorem cover_injective_of_not_dvd (hρ : IsPSL3Cover p A J ρ) (h3 : ¬ 3 ∣ Nat.card K - 1) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro z hz
  exact SL3_center_eq_one h3 (hρ.ker_central (MonoidHom.mem_ker.2 hz))

theorem not_dvd_card_D (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) (h3 : ¬ 3 ∣ Nat.card K - 1) :
    ¬ 3 ∣ Nat.card (J ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(J ⊓ Subgroup.centralizer (A : Set G))) 3 hdvd
  have hinj := cover_injective_of_not_dvd hρ h3
  obtain ⟨m, hm, hmd⟩ := (hρ.mem_inf_centralizer_iff hp h).1 d.2
  obtain ⟨v, hv, rfl⟩ := exists_diagSL_of_mem_CenTor hζ hm
  have hd3 : (d : G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one d
    rw [hd] at this
    exact congrArg Subtype.val this
  have hm3 : diagSL v hv ^ 3 = 1 := hinj (by rw [map_pow, hmd, map_one]; exact hd3)
  have hv3 : ∀ i, v i ^ 3 = 1 := by
    intro i
    rw [diagSL_pow] at hm3
    have := congrArg (fun y : SL3 K => ent y i i) hm3
    simp only [diagSL_apply, Pi.pow_apply, ite_true, ent, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at this
    apply Units.ext
    simpa using this
  have hv1 : v = 1 := funext fun i => units_eq_one_of_pow_three h3 (hv3 i)
  have hdiag : diagSL v hv = 1 := by
    subst hv1
    exact diagSL_one'
  have hd1 : d = 1 := by
    apply Subtype.ext
    rw [← hmd, hdiag, map_one]
    rfl
  rw [hd1, orderOf_one] at hd
  omega

omit [Finite K] in
theorem units_eq_one_of_pow_three_pow (h3 : ¬ 3 ∣ Nat.card K - 1) {u : Kˣ} {n : ℕ}
    (hu : u ^ (3 ^ n) = 1) : u = 1 := by
  have hdvd1 : orderOf u ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hu
  have hdvd2 : orderOf u ∣ Nat.card K - 1 := by
    have := orderOf_dvd_natCard u
    rwa [Nat.card_units] at this
  have hcop : Nat.Coprime (3 ^ n) (Nat.card K - 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  have : orderOf u ∣ Nat.gcd (3 ^ n) (Nat.card K - 1) := Nat.dvd_gcd hdvd1 hdvd2
  rw [hcop] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

omit [Finite K] in
theorem ent_eq_zero_of_actsBy {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K} {σ : Equiv.Perm (Fin 3)}
    (hm : ActsBy p m σ) (i k : Fin 3) (hk : k ≠ σ i) : ent m k i = 0 := by
  have hij : i ≠ σ⁻¹ k := fun h => hk (Equiv.Perm.inv_eq_iff_eq.1 h.symm)
  have hw1 : ∏ l, tSep ζ i (σ⁻¹ k) l = 1 := KFU.prod_torusElt i (σ⁻¹ k) ζ
  have hwp : ∀ l, tSep ζ i (σ⁻¹ k) l ^ p = 1 := fun l =>
    (KFU.torusElt_mem hij hζ.pow : KFU.torusElt i (σ⁻¹ k) ζ ∈ KFU.torusVec p 3 K).1 l
  have h1 := hm _ hw1 hwp
  rw [mul_inv_eq_iff_eq_mul] at h1
  have h2 : ent (m * diagSL (tSep ζ i (σ⁻¹ k)) hw1) k i =
      ent (diagSL (permVec σ (tSep ζ i (σ⁻¹ k))) (prod_permVec σ hw1) * m) k i := by rw [h1]
  rw [ent_mul_diagSL, ent_diagSL_mul] at h2
  have h3 : ent m k i * (tSep ζ i (σ⁻¹ k) i : K) =
      (tSep ζ i (σ⁻¹ k) (σ⁻¹ k) : K) * ent m k i := h2
  have hne : (tSep ζ i (σ⁻¹ k) i : K) ≠ (tSep ζ i (σ⁻¹ k) (σ⁻¹ k) : K) := fun h =>
    tSep_ne hζ hij (Units.ext h)
  have h4 : ent m k i * ((tSep ζ i (σ⁻¹ k) i : K) - (tSep ζ i (σ⁻¹ k) (σ⁻¹ k) : K)) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.1 h4 with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0) hne

theorem exists_threeElts_centralizer [CharP K 2] (hp : p.Prime) (h : JGood p A c J)
    (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ} (hζ : IsZeta p ζ) (hq : Nat.card K % 3 = 2) {x : G}
    (hx : x ∈ J ⊓ torusNormalizer A) (hx3 : x ^ 3 = 1) (hmove : ∃ a ∈ A, x * a * x⁻¹ ≠ a) :
    ∃ U : Subgroup G, (∀ u : G, u ∈ U ↔
        u ∈ J ⊓ Subgroup.centralizer ({x} : Set G) ∧ ∃ n : ℕ, u ^ (3 ^ n) = 1) ∧
      IsCyclic ↥U ∧ Nat.card U = 3 ^ (Nat.card (SL3 K)).factorization 3 := by
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by omega
  have hinj := cover_injective_of_not_dvd hρ h3
  obtain ⟨m, hm, rfl⟩ := (hρ.mem_inf_normalizer_iff hp h).1 hx
  have hm3 : m ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hx3)
  obtain ⟨σ, hσ⟩ := exists_actsBy hζ hm
  have hv0 : ∏ k, tSep ζ 0 1 k = 1 := KFU.prod_torusElt 0 1 ζ
  have hσ3 : σ ^ 3 = 1 := ActsBy.perm_pow_eq_one hp hρ hζ hσ hv0 3 (by rw [hm3]; simp)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    obtain ⟨a, haA, hne⟩ := hmove
    exact hne (by simpa using IsPSL3Cover.act_trivial h hρ hσ (n := 1) (by simp) a haA)
  have hmono := ent_eq_zero_of_actsBy hζ hσ
  have hdet : IsUnit (m : Matrix (Fin 3) (Fin 3) K).det := by
    rw [m.det_coe]
    exact isUnit_one
  have he := isUnit_det_krylov_of_monomial hσ3 hσ1 (fun i k hk => hmono i k hk) hdet
  let M : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL m
  have hM3 : M ^ 3 = 1 := by rw [← map_pow, hm3, map_one]
  have hMm : (M : Matrix (Fin 3) (Fin 3) K) = m := Matrix.SpecialLinearGroup.coe_GL_coe_matrix m
  obtain ⟨-, U₀, hU₀, hU₀cyc, hU₀card⟩ :=
    exists_cyc_threeElts h3 hM3 (e := Pi.single 0 1) (by rw [hMm]; exact he)
  have hdet1 : ∀ c' ∈ U₀, ∃ s : SL3 K, Matrix.SpecialLinearGroup.toGL s = c' := by
    intro c' hc'
    obtain ⟨-, n, hn⟩ := (hU₀ c').1 hc'
    have hdn : (Matrix.GeneralLinearGroup.det c') ^ (3 ^ n) = 1 := by
      rw [← map_pow, hn, map_one]
    have hd1 : Matrix.GeneralLinearGroup.det c' = 1 := units_eq_one_of_pow_three_pow h3 hdn
    refine ⟨⟨(c' : Matrix (Fin 3) (Fin 3) K), ?_⟩, Units.ext rfl⟩
    have := congrArg Units.val hd1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  let Usl : Subgroup (SL3 K) := U₀.comap Matrix.SpecialLinearGroup.toGL
  let ψ : Usl →* U₀ :=
    (Matrix.SpecialLinearGroup.toGL.comp Usl.subtype).codRestrict U₀ (fun s => s.2)
  have hψinj : Function.Injective ψ := fun s t hst =>
    Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val hst))
  have hψsurj : Function.Surjective ψ := by
    intro c'
    obtain ⟨s, hs⟩ := hdet1 c' c'.2
    exact ⟨⟨s, by show Matrix.SpecialLinearGroup.toGL s ∈ U₀; rw [hs]; exact c'.2⟩,
      Subtype.ext hs⟩
  have hUsl_cyc : IsCyclic Usl := isCyclic_of_injective ψ hψinj
  have hequiv := Subgroup.equivMapOfInjective Usl ρ hinj
  refine ⟨Usl.map ρ, fun u => ⟨?_, ?_⟩, isCyclic_of_surjective hequiv hequiv.surjective, ?_⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hcomm', n, hn⟩ := (hU₀ _).1 hs
    have hsm : s * m = m * s := Matrix.SpecialLinearGroup.toGL_injective (by
      rw [map_mul, map_mul]
      exact hcomm')
    have hsn : s ^ (3 ^ n) = 1 := Matrix.SpecialLinearGroup.toGL_injective (by
      rw [map_pow, hn, map_one])
    refine ⟨Subgroup.mem_inf.2 ⟨hρ.range_eq ▸ ⟨s, rfl⟩, ?_⟩, n, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hsm]
    · rw [← map_pow, hsn, map_one]
  · rintro ⟨hu, n, hn⟩
    obtain ⟨hJ, hcent⟩ := Subgroup.mem_inf.1 hu
    obtain ⟨s, rfl⟩ : u ∈ ρ.range := hρ.range_eq ▸ hJ
    have hsm : s * m = m * s := hinj (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hcent)
    have hsn : s ^ (3 ^ n) = 1 := hinj (by rw [map_pow, hn, map_one])
    have hs : s ∈ Usl := by
      show Matrix.SpecialLinearGroup.toGL s ∈ U₀
      refine (hU₀ _).2 ⟨?_, n, ?_⟩
      · rw [← map_mul, ← map_mul, hsm]
      · rw [← map_pow, hsn, map_one]
    exact ⟨s, hs, rfl⟩
  · rw [← Nat.card_congr hequiv.toEquiv, Nat.card_congr (Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩),
      hU₀card, factorization_card_SL3 hq]

end Cover

theorem jLemmaB_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    JLemmaB := by
  intro G _ _ p A c J h f hpf hmodel h2mod
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA h hpf hmodel
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hchar : CharP K 2 := charP_two_of_card hK
  obtain ⟨ζ, hζ⟩ := exists_isZeta hp h5 (by rw [hK]; exact hpf)
  have hq : Nat.card K % 3 = 2 := by rw [hK]; exact h2mod
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by omega
  refine ⟨not_dvd_card_D hp h hρ hζ h3, fun x hx hx3 hmove => ?_⟩
  obtain ⟨U, hU, hUcyc, hUcard⟩ := exists_threeElts_centralizer hp h hρ hζ hq hx hx3 hmove
  refine ⟨U, hU, hUcyc, ?_⟩
  have hJcard : Nat.card J = Nat.card (SL3 K) := by
    rw [← hρ.range_eq]
    exact (Nat.card_congr (MonoidHom.ofInjective (cover_injective_of_not_dvd hρ h3)).toEquiv).symm
  rw [hUcard, hJcard]

end CFSG.RankThree.PartOne.KFOUT3
