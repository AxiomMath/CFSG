module

public import CFSG.RankThree.PartOne.KF.F132Row6Types
public import CFSG.RankThree.PartOne.KF.R6Su2
public import CFSG.RankThree.PartOne.KF.F132Row4Types

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

@[expose] def KFK0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (E : Subgroup G) (t : MulAut E) (f : ℕ),
    p.Prime → 5 ≤ p → IsElementaryAbelian p E → autMovedInG E t ≠ ⊥ →
    kExceptional p (kZero p E t) f → ∀ K K' : Subgroup G, K ≤ kZero p E t → K' ≤ kZero p E t →
      StatedClassicalModel ↥K .PSL 2 2 f → StatedClassicalModel ↥K' .PSL 2 2 f →
      autMovedInG E t ≤ K → autMovedInG E t ≤ K' → K = K'

theorem eq_of_two_pow_mul_odd {a b O O' : ℕ} (hO : Odd O) (hO' : Odd O')
    (h : 2 ^ a * O = 2 ^ b * O') : a = b := by
  have hc₁ : Nat.Coprime (2 ^ a) O' := (Nat.coprime_two_left.2 hO').pow_left _
  have hc₂ : Nat.Coprime (2 ^ b) O := (Nat.coprime_two_left.2 hO).pow_left _
  have h1 : a ≤ b := by
    have hdvd : 2 ^ a ∣ 2 ^ b * O' := ⟨O, h.symm⟩
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc₁.dvd_of_dvd_mul_right hdvd)
  have h2 : b ≤ a := by
    have hdvd : 2 ^ b ∣ 2 ^ a * O := ⟨O', h⟩
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc₂.dvd_of_dvd_mul_right hdvd)
  exact le_antisymm h1 h2

theorem odd_cofactor_psu3 {f : ℕ} (hf : 1 ≤ f) :
    Odd (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
  have hq'ev : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  refine Odd.mul ?_ ?_
  · have h4 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have hev : Even ((2 ^ f) ^ 2) := (Nat.even_pow.2 ⟨hq'ev, by norm_num⟩)
    rcases hev with ⟨r, hr⟩
    exact ⟨r - 1, by omega⟩
  · have hev : Even ((2 ^ f) ^ 3) := (Nat.even_pow.2 ⟨hq'ev, by norm_num⟩)
    rcases hev with ⟨r, hr⟩
    exact ⟨r, by omega⟩

theorem psu_three_degree_unique {X : Type} [Group X] {f f' : ℕ}
    (h : StatedClassicalModel X .PSU 3 2 f) (h' : StatedClassicalModel X .PSU 3 2 f') : f = f' := by
  obtain ⟨hadm, F, hFf, hFfin, hF, ⟨e⟩⟩ := h
  obtain ⟨hadm', F', hFf', hFfin', hF', ⟨e'⟩⟩ := h'
  have hf : 1 ≤ f := hadm.2.1
  have hf' : 1 ≤ f' := hadm'.2.1
  have hcard : Nat.card (StatedProj (StatedSU 3 (2 ^ f) F)) =
      Nat.card (StatedProj (StatedSU 3 (2 ^ f') F')) :=
    Nat.card_congr (e.symm.trans e').toEquiv
  have h1 := card_psu3_mul_gcd hf hF
  have h2 := card_psu3_mul_gcd hf' hF'
  set N := Nat.card (StatedProj (StatedSU 3 (2 ^ f) F)) with hN
  rw [← hcard] at h2
  set O := ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) with hOdef
  set O' := ((2 ^ f') ^ 2 - 1) * ((2 ^ f') ^ 3 + 1) with hO'def
  have hOodd : Odd O := odd_cofactor_psu3 hf
  have hO'odd : Odd O' := odd_cofactor_psu3 hf'
  obtain ⟨k, m, hm, hNe⟩ := Nat.exists_eq_two_pow_mul_odd (n := N) (by
    intro h0
    rw [h0, mul_zero] at h1
    have : (2 ^ f) ^ 3 * O ≠ 0 := Nat.mul_ne_zero (by positivity) hOodd.pos.ne'
    exact this h1.symm)
  have hd : ∀ g : ℕ, Odd (Nat.gcd 3 (2 ^ g + 1)) := by
    intro g
    rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (2 ^ g + 1)) with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact ⟨1, rfl⟩
  have hpow : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, mul_comm]
  have hpow' : (2 ^ f') ^ 3 = 2 ^ (3 * f') := by rw [← pow_mul, mul_comm]
  have e1 : 2 ^ k * (Nat.gcd 3 (2 ^ f + 1) * m) = 2 ^ (3 * f) * O := by
    calc 2 ^ k * (Nat.gcd 3 (2 ^ f + 1) * m) = Nat.gcd 3 (2 ^ f + 1) * (2 ^ k * m) := by ring
      _ = Nat.gcd 3 (2 ^ f + 1) * N := by rw [← hNe]
      _ = (2 ^ f) ^ 3 * O := h1
      _ = 2 ^ (3 * f) * O := congrArg (· * O) hpow
  have e2 : 2 ^ k * (Nat.gcd 3 (2 ^ f' + 1) * m) = 2 ^ (3 * f') * O' := by
    calc 2 ^ k * (Nat.gcd 3 (2 ^ f' + 1) * m) = Nat.gcd 3 (2 ^ f' + 1) * (2 ^ k * m) := by ring
      _ = Nat.gcd 3 (2 ^ f' + 1) * N := by rw [← hNe]
      _ = (2 ^ f') ^ 3 * O' := h2
      _ = 2 ^ (3 * f') * O' := congrArg (· * O') hpow'
  have hk1 := eq_of_two_pow_mul_odd ((hd f).mul hm) hOodd e1
  have hk2 := eq_of_two_pow_mul_odd ((hd f').mul hm) hO'odd e2
  omega

section Kt

variable {G : Type} [Group G]

theorem kfKt_of_data [Finite G] (hK0 : KFK0) {p f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {E : Subgroup G}
    (hEel : IsElementaryAbelian p E) {t : MulAut E} (hmovne : autMovedInG E t ≠ ⊥)
    (hex : kExceptional p (kZero p E t) f) {K : Subgroup G} (hKle : K ≤ kZero p E t)
    (hmod : StatedClassicalModel ↥K .PSL 2 2 f) (hmov : autMovedInG E t ≤ K)
    (hcent : E ⊓ Subgroup.centralizer (K : Set G) = autFixedInG E t)
    (hlift : ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
      k ∈ K ∧ E.normalizerMonoidHom ⟨k, hk⟩ = t) : KFKt p E f t K := by
  have hIsKt : ∀ K' : Subgroup G, K' ≤ kZero p E t → StatedClassicalModel ↥K' .PSL 2 2 f →
      autMovedInG E t ≤ K' → IsKt p E t K' := by
    intro K' hle hm hmv
    refine ⟨fun f' hf' => ?_, fun hne => absurd ⟨f, hex⟩ hne⟩
    have hff : f = f' := psu_three_degree_unique hex.2.2 hf'.2.2
    subst hff
    exact ⟨hle, hm, hmv⟩
  refine ⟨hIsKt K hKle hmod hmov, fun K' hK' => ?_, hmod, hcent, hmov, hlift⟩
  obtain ⟨hle', hm', hmv'⟩ := hK'.1 f hex
  exact hK0 G p E t f hp h5 hEel hmovne hex K' K hle' hKle hm' hmod hmv' hmov

theorem kfKt_conj {p f : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G} (h : KFKt p E f t K)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    KFKt p E f (conjAut E w hw * t * (conjAut E w hw)⁻¹) (conjBy w K) := by
  obtain ⟨hIsKt, hU, hmod, hcent, hmov, k, hk, hkK, hkt⟩ := h
  refine ⟨isKt_conj hIsKt hw, fun K'' hK'' => ?_,
    (Equivariance.statedClassicalModel_conjBy_iff w K).2 hmod, ?_, ?_, ?_⟩
  · have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
    have h2 := isKt_conj hK'' hw'
    rw [Equivariance.conjAut_inv hw] at h2
    have h3 : (conjAut E w hw)⁻¹ * (conjAut E w hw * t * (conjAut E w hw)⁻¹) *
        ((conjAut E w hw)⁻¹)⁻¹ = t := by group
    rw [h3] at h2
    have h4 := hU _ h2
    rw [← h4, Equivariance.conjBy_conjBy_inv]
  · have hE : conjBy w E = E := Equivariance.conjBy_eq_of_mem_normalizer hw
    rw [Equivariance.centralizer_conjBy, Equivariance.autFixedInG_conj t hw, ← hcent]
    have h1 : conjBy w (E ⊓ Subgroup.centralizer (K : Set G)) =
        conjBy w E ⊓ conjBy w (Subgroup.centralizer (K : Set G)) := by
      unfold conjBy
      exact Subgroup.map_inf _ _ _ (MulAut.conj w).injective
    rw [h1, hE]
  · rw [Equivariance.autMovedInG_conj t hw]
    exact Subgroup.map_mono hmov
  · refine ⟨w * k * w⁻¹, (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem hw hk)
      ((Subgroup.normalizer (E : Set G)).inv_mem hw), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
    · have h2 := Equivariance.conj_conjAut_normalizerMonoidHom hw ⟨k, hk⟩
      rw [hkt, MulAut.conj_apply] at h2
      exact h2.symm

end Kt

section Cover

theorem perfectResidual_eq_top_of_perfect {H : Type*} [Group H] (h : Group.IsPerfect H) :
    perfectResidual H = ⊤ := by
  have hD : ∀ n, derivedSeries H n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero H
    | succ n ih =>
      rw [derivedSeries_succ, ih, ← _root_.commutator_def]
      exact h.commutator_eq_top
  simp only [perfectResidual, hD, iInf_top]

variable {E' P : Type} [Group E'] [Finite E'] [Group P] [Finite P] {p : ℕ} {ε : E' →* P}

theorem exists_perfect_cover_sub (hε : IsCentralPQuot p ε) {X : Subgroup E'} {Q : Subgroup P}
    (hQX : Q ≤ X.map ε) (hQ : Group.IsPerfect ↥Q) :
    ∃ Kc : Subgroup E', Kc ≤ X ∧ Kc.map ε = Q ∧ Group.IsPerfect ↥Kc ∧
      (ε.subgroupMap Kc).ker ≤ Subgroup.center ↥Kc := by
  set Y : Subgroup E' := X ⊓ Q.comap ε with hY
  have hYQ : Y.map ε = Q := by
    ext y
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hxX, hx⟩ := hQX hy
      exact ⟨x, ⟨hxX, by simpa [hx] using hy⟩, hx⟩
  refine ⟨inSubgroup perfectResidual Y, (Subgroup.map_subtype_le _).trans inf_le_left, ?_,
    isPerfect_inSubgroup_perfectResidual Y, ker_subgroupMap_le_center hε _⟩
  rw [map_inSubgroup_perfectResidual, hYQ]
  unfold inSubgroup
  rw [perfectResidual_eq_top_of_perfect hQ, Subgroup.map_top, Subgroup.range_subtype]

end Cover

section Exc

open CFSG.RankThree.PartOne.KFOUT3 CFSG.RankThree.PartOne.Torsion37 CFSG.RankThree.PerfectCover
  CFSG.RankThree.GroupTheory CFSG.LocalCores

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {P : Type} [Group P] [Finite P]

theorem exists_exc_K
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hf3 : 3 ≤ f)
    {t : MulAut E} {K₀ : Subgroup G} (hK₀L : K₀ ≤ L)
    (hK₀c : K₀ ≤ Subgroup.centralizer (autFixedInG E t : Set G))
    {z : G} (hzE : z ∈ E) (hzK₀ : z ∈ K₀) (hzord : orderOf z = p)
    (hEK₀ : E ⊓ K₀ = Subgroup.zpowers z)
    (htz : ((t ⟨z, hzE⟩ : E) : G) = z⁻¹) (hEeq : E = autFixedInG E t ⊔ Subgroup.zpowers z)
    (hmov₀ : autMovedInG E t ≤ K₀)
    (ε : ↥L →* P) (hε : IsCentralPQuot p ε) {Q : Subgroup P} (hQperf : Group.IsPerfect ↥Q)
    (hQqs : IsQuasisimple ↥Q)
    (hQmodel : StatedClassicalModel (↥Q ⧸ Subgroup.center ↥Q) .PSL 2 2 f)
    (hQK : Q ≤ (K₀.subgroupOf L).map ε) (hzQ : ε ⟨z, hK₀L hzK₀⟩ ∈ Q) {n : P} (hnQ : n ∈ Q)
    (hn : n * ε ⟨z, hK₀L hzK₀⟩ * n⁻¹ = (ε ⟨z, hK₀L hzK₀⟩)⁻¹) :
    ∃ K : Subgroup G, K ≤ K₀ ∧ StatedClassicalModel ↥K .PSL 2 2 f ∧ autMovedInG E t ≤ K ∧
      E ⊓ Subgroup.centralizer (K : Set G) = autFixedInG E t ∧
      ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
        k ∈ K ∧ E.normalizerMonoidHom ⟨k, hk⟩ = t := by
  classical
  subst hEA
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have := h.A_elem
  obtain ⟨Kc, hKcY, hKcmap, hKcperf, hKcker⟩ := exists_perfect_cover_sub hε hQK hQperf
  have hKcK₀ : Kc.map L.subtype ≤ K₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKcY hx
  set K : Subgroup G := Kc.map L.subtype with hK
  have hsurj := ε.subgroupMap_surjective Kc
  have hQ' : IsQuasisimple ↥(Kc.map ε) := by
    rw [hKcmap]
    exact hQqs
  have hKcqs : IsQuasisimple ↥Kc :=
    (isQuasisimple_iff_of_surjective hKcperf (ε.subgroupMap Kc) hsurj hKcker).2 hQ'
  obtain ⟨e₁⟩ := centerQuotientEquiv_of_surjective hKcperf (ε.subgroupMap Kc) hsurj hKcker
  obtain ⟨e₂⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKcmap)
  have hKcmodel : StatedClassicalModel (↥Kc ⧸ Subgroup.center ↥Kc) .PSL 2 2 f :=
    Equivariance.statedClassicalModel_of_mulEquiv (e₁.trans e₂).symm hQmodel
  have hZKc : Subgroup.center ↥Kc = ⊥ := psl2EvenCenterTrivial_of_multipliers hGA hf3 hKcqs hKcmodel
  have hKmodel : StatedClassicalModel ↥K .PSL 2 2 f := by
    let eK : ↥Kc ≃* ↥K := Kc.equivMapOfInjective L.subtype L.subtype_injective
    exact Equivariance.statedClassicalModel_of_mulEquiv eK
      (Equivariance.statedClassicalModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZKc).trans QuotientGroup.quotientBot) hKcmodel)
  set zL : ↥L := ⟨z, hK₀L hzK₀⟩ with hzL
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hzLp : zL ^ p = 1 := Subtype.ext (by simpa using hzp)
  have hεzp : (ε zL) ^ p = 1 := by rw [← map_pow, hzLp, map_one]
  have hzKc : zL ∈ Kc := by
    have hxK : ε zL ∈ Kc.map ε := by rw [hKcmap]; exact hzQ
    obtain ⟨y, hyK, hyε, hyp⟩ := hε.exists_lift_mem hxK hεzp
    have : y = zL := hε.eq_of_map_eq hyp hzLp hyε
    rw [← this]
    exact hyK
  have hzK : z ∈ K := ⟨zL, hzKc, rfl⟩
  have hEKle : E ⊓ K₀ ≤ K := by
    rw [hEK₀]
    exact Subgroup.zpowers_le.2 hzK
  have hCleE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hmovE : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hmovK : autMovedInG E t ≤ K := fun x hx => hEKle ⟨hmovE hx, hmov₀ hx⟩
  obtain ⟨kL, hkLc, hkLε⟩ : ∃ kL ∈ Kc, ε kL = n := by
    have : n ∈ Kc.map ε := by rw [hKcmap]; exact hnQ
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨y, hy, rfl⟩
  set k : G := (kL : G) with hk
  have hkK : k ∈ K := ⟨kL, hkLc, rfl⟩
  have hkK₀ : k ∈ K₀ := hKcK₀ hkK
  have hkz : k * z * k⁻¹ = z⁻¹ := by
    have h1 : kL * zL * kL⁻¹ = zL⁻¹ := by
      refine hε.eq_of_map_eq ?_ ?_ ?_
      · rw [conj_pow, hzLp, mul_one, mul_inv_cancel]
      · rw [inv_pow, hzLp, inv_one]
      · rw [map_mul, map_mul, map_inv, map_inv, hkLε]
        exact hn
    have := congrArg Subtype.val h1
    simpa using this
  have hkz' : k⁻¹ * z * (k⁻¹)⁻¹ = z⁻¹ := by
    have h1 : k * z = z⁻¹ * k := by
      rw [mul_inv_eq_iff_eq_mul] at hkz
      exact hkz
    have hz' : z = k⁻¹ * z⁻¹ * k := by
      calc z = k⁻¹ * (k * z) := by group
        _ = k⁻¹ * (z⁻¹ * k) := by rw [h1]
        _ = k⁻¹ * z⁻¹ * k := by group
    calc k⁻¹ * z * (k⁻¹)⁻¹ = (k⁻¹ * z⁻¹ * k)⁻¹ := by group
      _ = z⁻¹ := by rw [← hz']
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.E_elem.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hzcomm : ∀ y ∈ autFixedInG E t, ∀ y' ∈ Subgroup.zpowers z, y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
    exact (Commute.zpow_right (show Commute y z from hEcomm y (hCleE hy) z hzE) i).eq
  have hdec : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * z ^ i := by
    intro e he
    rw [hEeq] at he
    obtain ⟨u, hu, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hzcomm he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨u, hu, i, rfl⟩
  have hconj : ∀ v ∈ K₀, v * z * v⁻¹ = z⁻¹ → ∀ (e : G) (he : e ∈ E),
      v * e * v⁻¹ = ((t ⟨e, he⟩ : E) : G) := by
    intro v hv hvz e he
    obtain ⟨u, hu, i, hei⟩ := hdec e he
    have huE : u ∈ E := hCleE hu
    have hteq : (⟨e, he⟩ : E) = ⟨u, huE⟩ * ⟨z, hzE⟩ ^ i := by
      apply Subtype.ext
      simp [hei]
    have h1 : ((t ⟨e, he⟩ : E) : G) = u * (z⁻¹) ^ i := by
      rw [hteq, map_mul, map_zpow]
      obtain ⟨huE', hu'⟩ := mem_autFixedInG_iff.1 hu
      have h3 : t ⟨u, huE⟩ = ⟨u, huE⟩ := hu'
      have h4 : t ⟨z, hzE⟩ = ⟨z⁻¹, E.inv_mem hzE⟩ := Subtype.ext htz
      rw [h3, h4]
      simp
    have hvu : v * u * v⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.mp (hK₀c hv) u hu
      rw [← this, mul_inv_cancel_right]
    rw [h1, hei]
    calc v * (u * z ^ i) * v⁻¹ = (v * u * v⁻¹) * (v * z * v⁻¹) ^ i := by rw [conj_zpow]; group
      _ = u * (z⁻¹) ^ i := by rw [hvu, hvz]
  have hkNorm : k ∈ Subgroup.normalizer (E : Set G) := by
    refine mem_normalizer_of_conj_mem (fun e he => ?_) (fun e he => ?_)
    · rw [hconj k hkK₀ hkz e he]
      exact (t ⟨e, he⟩).2
    · have h3 := hconj k⁻¹ (K₀.inv_mem hkK₀) hkz' e he
      rw [inv_inv] at h3
      rw [h3]
      exact (t ⟨e, he⟩).2
  have hlift : E.normalizerMonoidHom ⟨k, hkNorm⟩ = t := by
    refine DFunLike.ext _ _ fun e => Subtype.ext ?_
    show k * (e : G) * k⁻¹ = ((t e : E) : G)
    exact hconj k hkK₀ hkz (e : G) e.2
  have hcent : E ⊓ Subgroup.centralizer (K : Set G) = autFixedInG E t := by
    apply le_antisymm
    · rintro e ⟨heE, heC⟩
      refine mem_autFixedInG_iff.2 ⟨heE, ?_⟩
      have h1 := hconj k hkK₀ hkz e heE
      have h2 : k * e * k⁻¹ = e := by
        have := Subgroup.mem_centralizer_iff.mp heC k hkK
        rw [this, mul_inv_cancel_right]
      exact Subtype.ext (by rw [← h1, h2])
    · intro u hu
      refine ⟨hCleE hu, ?_⟩
      exact Subgroup.mem_centralizer_iff.2 fun x hxK =>
        (Subgroup.mem_centralizer_iff.mp (hK₀c (hKcK₀ hxK)) u hu).symm
  exact ⟨K, hKcK₀, hKmodel, hmovK, hcent, k, hkNorm, hkK, hlift⟩

end Exc

section Block

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem su2_block_facts (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 3 ≤ f) {P : Type} [Group P] [Finite P]
    {p : ℕ} {q : ↥(SU (unitaryInvolution K 2 f) 5) →* P} (hq : IsCentralPQuot p q) :
    Group.IsPerfect ↥((su2Emb (unitaryInvolution K 2 f)).range.map q) ∧
      IsQuasisimple ↥((su2Emb (unitaryInvolution K 2 f)).range.map q) ∧
      StatedClassicalModel (↥((su2Emb (unitaryInvolution K 2 f)).range.map q) ⧸
        Subgroup.center ↥((su2Emb (unitaryInvolution K 2 f)).range.map q)) .PSL 2 2 f := by
  have hFq : Nat.card (fixF (unitaryInvolution K 2 f)) = 2 ^ f := card_fixedSubfield hK
  have hk4 : 4 ≤ Nat.card ↥(fixF (unitaryInvolution K 2 f)) := by
    rw [hFq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hSLqs := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le
    (k := ↥(fixF (unitaryInvolution K 2 f))) (m := 2) le_rfl hk4
  set B := (su2Emb (unitaryInvolution K 2 f)).range with hB
  have hBqs : IsQuasisimple ↥B :=
    LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (su2Emb_injective (unitaryInvolution K 2 f))) hSLqs
  have hBnot : ¬ B ≤ q.ker := fun hle =>
    not_le_center_of_isQuasisimple' hBqs (fun x hx => hq.central (hle hx))
  have hQqs : IsQuasisimple ↥(B.map q) := LocalCores.isQuasisimple_map hBqs q hBnot
  refine ⟨hQqs.1, hQqs, ?_⟩
  obtain ⟨e₁⟩ := centerQuotientEquiv_of_surjective hBqs.1 (q.subgroupMap B)
    (q.subgroupMap_surjective B) (ker_subgroupMap_le_center hq B)
  exact statedModel_psl_two_of_layer hFq (by omega) (su2Emb_injective (unitaryInvolution K 2 f))
    (hB.symm ▸ rfl) e₁.symm

end Block

section Centralizer

variable {G : Type} [Group G]

theorem kZero_le_centralizer_fixed (p : ℕ) (E : Subgroup G) (t : MulAut E) :
    kZero p E t ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
  unfold kZero pElementSubgroup
  rw [Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  exact (Subgroup.map_subtype_le _) hx

end Centralizer

section Row6

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem row6_exc_kfKt (hGA : CFSG.Open.GriessAllModelsStatement)
    (hK0 : KFK0) (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hf3 : 3 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2)
    (hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u)
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    (ε : ↥L →* StatedProj (StatedSU 5 (2 ^ f) K)) (hε : IsCentralPQuot p ε)
    (hq : IsCentralPQuot p (suQ 5 hK))
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus6 (unitaryInvolution K 2 f) p).map (suQ 5 hK))
    (S : D8Ctx p K L (E ⊓ L))
    (hS : ∀ (d : D8Mod p K) (m : ↥(SU (unitaryInvolution K 2 f) 5)),
      (m : GL (Fin 5) K) = diagU (d8Vec 5 d) →
        ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) = suQ 5 hK m) :
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → kExceptional p (kZero p E s) f →
      ∃ Kt : Subgroup G, KFKt p E f s Kt := by
  classical
  obtain ⟨-, r₀, r₁, hr₀s, hr₀L, hr₁s, hr₁L, hord, hex₀, hKF₁, himg₀, himg₁, hpairs, hexcconj,
    hK₀L, hmov₀, z, hzE, hzK₀, hzord, hEK₀, htz, hEeq⟩ :=
    row6_main_ext hGA h hF13 hEA hG hf3 hpq hK hfix hζ ε hε hq hAT S hS
  subst hEA
  have hp := h.prime
  set σ : K ≃+* K := unitaryInvolution K 2 f with hσ
  obtain ⟨hQperf, hQqs, hQmodel⟩ := su2_block_facts hK hf3 hq
  set Q := (su2Emb σ).range.map (suQ 5 hK) with hQ
  have hQK : Q ≤ ((kZero p E r₀).subgroupOf L).map ε := by
    rw [himg₀]
    exact Subgroup.map_mono (by
      rintro _ ⟨X, rfl⟩
      exact su2Emb_mem_range_su3Emb σ X)
  have hzL : z ∈ L := hK₀L hzK₀
  set zL : ↥L := ⟨z, hzL⟩ with hzLdef
  have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hzLp : zL ^ p = 1 := Subtype.ext (by simpa using hzp)
  have hεzp : (ε zL) ^ p = 1 := by rw [← map_pow, hzLp, map_one]
  have hεT : ε zL ∈ (torus6 σ p).map (suQ 5 hK) := by
    rw [← hAT]
    exact ⟨zL, Subgroup.mem_subgroupOf.2 ⟨hzE, hzL⟩, rfl⟩
  have hεD : ε zL ∈ (su3Emb σ).range.map (suQ 5 hK) := by
    rw [← himg₀]
    exact ⟨zL, Subgroup.mem_subgroupOf.2 hzK₀, rfl⟩
  obtain ⟨τ, hτT, hτ⟩ := hεT
  obtain ⟨y, hyD, hyq, hyp⟩ := hq.exists_lift_mem hεD hεzp
  have hτy : τ = y := hq.eq_of_map_eq (torus6_pow_eq_one hτT) hyp (hτ.trans hyq.symm)
  have hy : y ∈ torus6 σ p ⊓ (su3Emb σ).range := ⟨hτy ▸ hτT, hyD⟩
  rw [torus6_inf_range_su3_eq hfix] at hy
  obtain ⟨u, rfl⟩ := hy
  have hyB : rhoSU3 hfix u ∈ (su2Emb σ).range := rhoSU3_mem_range_su2Emb σ hfix u
  have hzQ : ε zL ∈ Q := ⟨_, hyB, hyq⟩
  have hnQ : suQ 5 hK (su2Emb σ (wSL (fixF σ))) ∈ Q := ⟨_, ⟨wSL (fixF σ), rfl⟩, rfl⟩
  have hn : suQ 5 hK (su2Emb σ (wSL (fixF σ))) * ε zL * (suQ 5 hK (su2Emb σ (wSL (fixF σ))))⁻¹ =
      (ε zL)⁻¹ := by
    rw [← hyq, ← map_inv, ← map_mul, ← map_mul, su2Emb_weyl_conj σ hfix u, map_inv]
    exact map_inv _ _
  obtain ⟨Kt, hKtle, hKtmod, hKtmov, hKtcent, hKtlift⟩ := exists_exc_K hGA h rfl hf3 hK₀L
    (kZero_le_centralizer_fixed p E r₀) hzE hzK₀ hzord hEK₀ htz hEeq hmov₀ ε hε hQperf hQqs
    hQmodel hQK hzQ hnQ hn
  have hmovne : autMovedInG E r₀ ≠ ⊥ := by
    intro hbot
    have hcard := (hF13.reflection r₀ hr₀s).2.2
    rw [hbot, Subgroup.card_bot] at hcard
    exact hp.one_lt.ne hcard
  have hKFKt₀ : KFKt p E f r₀ Kt := kfKt_of_data hK0 hp (Sec12Three.five_le h) h.E_elem hmovne hex₀
    hKtle hKtmod hKtmov hKtcent hKtlift
  intro s hs hsL hexc
  obtain ⟨x, hxL, hxE, hx⟩ := hexcconj s hs hsL hexc
  exact ⟨conjBy x Kt, hx ▸ kfKt_conj hKFKt₀ hxE⟩

theorem kf132Row6_kfKt (hGA : CFSG.Open.GriessAllModelsStatement)
    (hK0 : KFK0) (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f) :
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → kExceptional p (kZero p E s) f →
      ∃ Kt : Subgroup G, KFKt p E f s Kt := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_row6 hGA hF hpq hmod
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hchar, hK, ⟨ζ₀, hζ₀⟩, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame_of (n := 5) (Or.inr rfl) d8Comb_five hcore hf1 hpq hmod
  have hq : IsCentralPQuot p (suQ 5 hK) := isCentralPQuot_suQ hp hp2 (by norm_num) hpq hf1 hK
  have hfix : ∀ u : Kˣ, u ^ p = 1 → unitaryInvolution K 2 f (u : K) = u := by
    intro u hu
    have h2 : u ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, hu, one_pow]
    rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : u ^ 2 ^ f = u := by
      calc u ^ 2 ^ f = u ^ (2 ^ f - 1) * u := by rw [← pow_succ, Nat.sub_add_cancel hq1]
        _ = u := by rw [h2, one_mul]
    rw [this]
  have hAT : ((A ⊓ L).subgroupOf L).map ε =
      (torus6 (unitaryInvolution K 2 f) p).map (suQ 5 hK) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  obtain ⟨S, hS⟩ := rowSU_S (n := 5) (Or.inr rfl) d8Comb_five d8Comb2_five hp hp2 hK hf1 hpq
    ⟨ζ₀, hζ₀⟩ ε hε hcore.F_le hcore.F_exp hFT₁ hFT₂
  exact row6_exc_kfKt hGA hK0 h hF13 hEA hG hf3 hpq hK hfix hζ₀ ε hε hq hAT S hS

end Row6

end CFSG.RankThree.PartOne.KF132
