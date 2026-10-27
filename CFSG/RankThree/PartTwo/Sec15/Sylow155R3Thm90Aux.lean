module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

structure J2Facts (J : Type) [Group J] : Prop where
  simple : IsSimpleGroup J
  perfect : Group.IsPerfect J
  center : Subgroup.center J = ⊥
  card_aut : Nat.card (MulAut J) = 1209600
  finite : Finite J

namespace J2Facts

variable {J : Type} [Group J]

theorem eq_bot_of_normal_isSolvable (hJ : J2Facts J) (N : Subgroup J) [N.Normal]
    (hN : Group.IsSolvable N) : N = ⊥ := by
  haveI := hJ.simple
  haveI := hJ.perfect
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    haveI : Group.IsSolvable J :=
      solvable_of_surjective (f := (Subgroup.topEquiv (G := J)).toMonoidHom)
        (Subgroup.topEquiv (G := J)).surjective
    exact Group.IsPerfect.not_isSolvable J inferInstance

theorem le_ker_of_solvable (hJ : J2Facts J) {H : Type*} [Group H] (φ : H →* J)
    (hφ : Function.Surjective φ) (K : Subgroup H) [K.Normal] (hK : Group.IsSolvable K) :
    K ≤ φ.ker := by
  haveI := hK
  haveI : (K.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  haveI : Group.IsSolvable (K.map φ) := solvable_of_surjective (f := φ.subgroupMap K)
    (MonoidHom.subgroupMap_surjective φ K)
  have h := hJ.eq_bot_of_normal_isSolvable (K.map φ) inferInstance
  rwa [Subgroup.map_eq_bot_iff] at h

theorem not_dvd_card_aut {p : ℕ} (hp : p.Prime) (hp7 : ¬ (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7)) :
    ¬ p ∣ 1209600 := by
  intro h
  have e : (1209600 : ℕ) = 2 ^ 8 * 3 ^ 3 * 5 ^ 2 * 7 := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact hp7 (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow h)))
      · exact hp7 (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h))))
    · exact hp7 (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
        (hp.dvd_of_dvd_pow h)))))
  · exact hp7 (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))))

theorem not_dvd_card (hJ : J2Facts J) {p : ℕ} (hp : p.Prime)
    (hp7 : ¬ (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7)) : ¬ p ∣ Nat.card J := by
  intro h
  have hinj : Function.Injective (MulAut.conj : J →* MulAut J) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hz : g ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut J => f y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    rw [hJ.center] at hz
    exact hz
  have := Subgroup.card_dvd_of_injective _ hinj
  rw [hJ.card_aut] at this
  exact not_dvd_card_aut hp hp7 (h.trans this)

theorem eq_one_of_pow_prime (hJ : J2Facts J) {X : Type*} [Group X] (e : X ≃* J) {p : ℕ}
    (hp : p.Prime) (hp7 : ¬ (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7)) {σ : MulAut X}
    (hσ : σ ^ p = 1) : σ = 1 := by
  obtain ⟨τ, hτdef⟩ : ∃ τ : MulAut J, τ = MulAut.congr e σ := ⟨_, rfl⟩
  have hτ : τ ^ p = 1 := by rw [hτdef, ← map_pow, hσ, map_one]
  have h1 : orderOf τ ∣ p := orderOf_dvd_of_pow_eq_one hτ
  have h2 : orderOf τ ∣ 1209600 := by
    have := orderOf_dvd_natCard τ
    rwa [hJ.card_aut] at this
  have hord : orderOf τ = 1 := by
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (not_dvd_card_aut hp hp7)
  have hτ1 : τ = 1 := orderOf_eq_one_iff.mp hord
  exact (MulAut.congr e).injective (by rw [← hτdef, hτ1, map_one])

theorem le_ker_of_normalizes (hJ : J2Facts J) {W : Type*} [Group W] (M K : Subgroup W)
    (hK : Group.IsSolvable K) (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (φ : M →* J)
    (hφ : Function.Surjective φ) : K.subgroupOf M ≤ φ.ker := by
  haveI := hK
  haveI : (K.subgroupOf M).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hMK g g.2 n hn⟩
  haveI : Group.IsSolvable (K.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective
      (f := ((M.subtype.comp (K.subgroupOf M).subtype).codRestrict K fun x => x.2))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : K => (x : W)) hab)))
  exact hJ.le_ker_of_solvable φ hφ _ inferInstance

theorem eq_one_of_commutators_mem (hJ : J2Facts J) {W : Type*} [Group W] (M K : Subgroup W)
    (hK : Group.IsSolvable K) (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (φ : M →* J)
    (hφ : Function.Surjective φ) (d : M)
    (hd : ∀ m : M, (d : W) * m * (d : W)⁻¹ * (m : W)⁻¹ ∈ K) : φ d = 1 := by
  have hz : φ d ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := hφ y
    have h1 : d * m * d⁻¹ * m⁻¹ ∈ φ.ker := hJ.le_ker_of_normalizes M K hK hMK φ hφ (hd m)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  rw [hJ.center] at hz
  exact hz

end J2Facts

theorem exists_mul_fixed {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] (τ : MulAut H)
    (hτ : τ ^ p = 1) (N : Subgroup H) (hN : ∀ n ∈ N, τ n ∈ N) (hp : ¬ p ∣ Nat.card N) (l : H)
    (hl : l⁻¹ * τ l ∈ N) : ∃ n ∈ N, τ (l * n) = l * n := by
  classical
  have hmem : ∀ g : {g : H // l⁻¹ * g ∈ N}, l⁻¹ * τ g.1 ∈ N := fun g => by
    have h1 : l⁻¹ * τ g.1 = (l⁻¹ * τ l) * τ (l⁻¹ * g.1) := by
      simp only [map_mul, map_inv]; group
    rw [h1]
    exact N.mul_mem hl (hN _ g.2)
  let f : {g : H // l⁻¹ * g ∈ N} → {g : H // l⁻¹ * g ∈ N} := fun g => ⟨τ g.1, hmem g⟩
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (τ.injective (congrArg Subtype.val hab))
  let σ : Equiv.Perm {g : H // l⁻¹ * g ∈ N} :=
    Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ (n : ℕ) (g : {g : H // l⁻¹ * g ∈ N}), ((σ ^ n) g).1 = (τ ^ n) g.1 := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hσp : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext g
    rw [hσ, hτ]
    rfl
  haveI : Fintype {g : H // l⁻¹ * g ∈ N} := Fintype.ofFinite _
  have hcard : Nat.card {g : H // l⁻¹ * g ∈ N} = Nat.card N :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft l⁻¹) (fun g => Iff.rfl))
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := p) (n := 1) (σ := σ)
    (by rw [Fintype.card_eq_nat_card, hcard]; exact hp) hσp
  refine ⟨l⁻¹ * a.1, a.2, ?_⟩
  have h2 : τ a.1 = a.1 := congrArg Subtype.val ha
  rw [mul_inv_cancel_left]
  exact h2

theorem fix_of_mem_zpowers {X : Type*} [Group X] (σ : MulAut X) (hσ : σ ^ 3 = 1) {a : X}
    (ha : a ^ 3 = 1) (h : σ a ∈ Subgroup.zpowers a) : σ a = a := by
  by_cases ha1 : a = 1
  · rw [ha1, map_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hord : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hkm : a ^ (k % 3) = σ a := by
    have := zpow_mod_orderOf a k
    rw [hord] at this
    rw [← hk, ← this]
    norm_cast
  have h3 : σ (σ (σ a)) = a := by
    have := congrArg (fun f : MulAut X => f a) hσ
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at hkm
    exfalso
    apply ha1
    apply σ.injective
    rw [← hkm, zpow_zero, map_one]
  · rw [h1, zpow_one] at hkm
    exact hkm.symm
  · rw [h2] at hkm
    have hsa : σ a = a ^ 2 := by rw [← hkm]; norm_cast
    have hσσ : σ (σ a) = a := by
      rw [hsa, map_pow, hsa, ← pow_mul]
      calc a ^ (2 * 2) = a ^ 3 * a := by rw [← pow_succ]
        _ = a := by rw [ha, one_mul]
    rw [hσσ] at h3
    exfalso
    rw [hsa] at h3
    apply ha1
    calc a = a ^ 2 * a⁻¹ := by group
      _ = a * a⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel a

theorem eq_one_of_pow_three_of_not_dvd {G : Type*} [Group G] {H : Subgroup G}
    (hH : ¬ 3 ∣ Nat.card H) {g : G} (hg : g ∈ H) (h3 : g ^ 3 = 1) : g = 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ H.orderOf_dvd_natCard hg) hH

theorem not_dvd_card_theta {J : Type} [Group J] {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X))
    (e : X ⧸ aschbacherSolvableCore 3 X ≃* J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpJ : ¬ p ∣ Nat.card J) : ¬ p ∣ Nat.card (aschbacherSolvableCore 3 X) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hθsol, hθchar, -, -, -, -, hRθ⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hRθ' : CFSG.pCore 2 X ≤ aschbacherSolvableCore 3 X := hRθ 2 Nat.prime_two (by norm_num)
  haveI := hθchar
  haveI := hθsol
  haveI hNbn : ((aschbacherSolvableCore 3 X).map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hNbsol : Group.IsSolvable
      ((aschbacherSolvableCore 3 X).map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    solvable_of_surjective
      (f := (QuotientGroup.mk' (CFSG.pCore 2 X)).subgroupMap (aschbacherSolvableCore 3 X))
      (MonoidHom.subgroupMap_surjective _ _)
  have hQperf : Group.IsPerfect (X ⧸ CFSG.pCore 2 X) := hq.1
  haveI := hQperf
  have hQnt : Nontrivial (X ⧸ CFSG.pCore 2 X) := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine nontrivial_of_ne a' b' ?_
    rintro rfl
    exact hab rfl
  have hcent : (aschbacherSolvableCore 3 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤
      Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNbn with h | h
    · exfalso
      rw [h] at hNbsol
      haveI := hNbsol
      haveI : Group.IsSolvable (X ⧸ CFSG.pCore 2 X) :=
        solvable_of_surjective
          (f := (Subgroup.topEquiv (G := X ⧸ CFSG.pCore 2 X)).toMonoidHom)
          Subgroup.topEquiv.surjective
      exact Group.IsPerfect.not_isSolvable (X ⧸ CFSG.pCore 2 X) inferInstance
    · exact h
  have hidx : ((aschbacherSolvableCore 3 X).map (QuotientGroup.mk' (CFSG.pCore 2 X))).index =
      Nat.card J := by
    have e1 := QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 X)
      (aschbacherSolvableCore 3 X) hRθ'
    rw [Subgroup.index, Nat.card_congr (e1.trans e).toEquiv]
  have hNbcomm : ∀ a b : ((aschbacherSolvableCore 3 X).map
      (QuotientGroup.mk' (CFSG.pCore 2 X))), a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hcent b.2) a)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := aschbacherSolvableCore 3 X) p hdvd
  have hz : QuotientGroup.mk' (CFSG.pCore 2 X) (y : X) ∈
      (aschbacherSolvableCore 3 X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
    Subgroup.mem_map_of_mem _ y.2
  have hpow := CFSG.RankThree.PartTwo.KFacts.KS14.pow_index_eq_one_of_isPerfect
    ((aschbacherSolvableCore 3 X).map (QuotientGroup.mk' (CFSG.pCore 2 X))) hNbcomm (hcent hz)
  rw [hidx, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hpow
  have hyo : orderOf (y : X) = p := by rw [Subgroup.orderOf_coe]; exact hy
  have hcop : Nat.Coprime (Nat.card J) (orderOf (y : X)) := by
    rw [hyo]; exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpJ).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hyR : (y : X) ∈ CFSG.pCore 2 X := by
    rw [← hm]; exact Subgroup.pow_mem _ hpow m
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨(y : X), hyR⟩
  have hk' : (y : X) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h1 : p ∣ 2 ^ k := hyo ▸ orderOf_dvd_of_pow_eq_one hk'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))

section Subnormal

variable {G : Type*} [Group G] {G' : Type*} [Group G']

abbrev SubnormalIn (H K : Subgroup G) : Prop := (H.subgroupOf K).IsSubnormal

theorem SubnormalIn.subgroupOf {H K : Subgroup G} (J : Subgroup G) (hKJ : K ≤ J)
    (h : SubnormalIn H K) : SubnormalIn (H.subgroupOf J) (K.subgroupOf J) := by
  have h1 := Subgroup.IsSubnormal.comap (Subgroup.subgroupOfEquivOfLe hKJ).toMonoidHom h
  convert h1 using 1
  ext x
  exact Iff.rfl

theorem SubnormalIn.trans {H K J : Subgroup G} (hHK : H ≤ K) (hKJ : K ≤ J)
    (h1 : SubnormalIn H K) (h2 : SubnormalIn K J) : SubnormalIn H J :=
  Subgroup.IsSubnormal.trans (H := H.subgroupOf J) (K := K.subgroupOf J)
    (fun x hx => hHK hx) (SubnormalIn.subgroupOf J hKJ h1) h2

theorem SubnormalIn.inf {H K : Subgroup G} (J : Subgroup G) (h : SubnormalIn H K) :
    SubnormalIn (H ⊓ J) (K ⊓ J) := by
  have h1 := Subgroup.IsSubnormal.comap (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K)) h
  convert h1 using 1
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2.2⟩⟩

theorem SubnormalIn.map {H K : Subgroup G} (hHK : H ≤ K) (f : G →* G') (h : SubnormalIn H K) :
    SubnormalIn (H.map f) (K.map f) := by
  have h1 := Subgroup.IsSubnormal.map (MonoidHom.subgroupMap_surjective f K) h
  convert h1 using 1
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    exact ⟨⟨u, hHK hu⟩, hu, Subtype.ext hux⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : G), hy, rfl⟩

end Subnormal

theorem thetaComponentsAt_facts {Y : Type*} [Group Y] {c : Y} {M : Subgroup Y}
    (hM : M ∈ thetaComponentsAt 3 c) :
    M ≤ Subgroup.centralizer ({c} : Set Y) ∧
      (M.subgroupOf (Subgroup.centralizer ({c} : Set Y))).IsSubnormal ∧ Group.IsPerfect M := by
  obtain ⟨M₀, hM₀, rfl⟩ := hM
  refine ⟨Subgroup.map_subtype_le M₀, ?_, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.centralizer ({c} : Set Y)).subtype_injective]
    exact hM₀.2.1
  · haveI := hM₀.1
    exact Group.IsPerfect.map (Subgroup.centralizer ({c} : Set Y)).subtype

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
