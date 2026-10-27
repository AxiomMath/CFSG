module

public import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldSuzuki
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CompThree
public import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent

public section

section

open CFSG Subgroup
open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szPrimeHom)
open CFSG.Open (signalizerFixedSubgroup)

namespace CFSG.RankThree.PartTwo.Sec11



section SuzukiAut

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem sz_exists_order_five (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x : suzukiGroup a K, orderOf x = 5 ∧ ∀ τ : RingAut K, szFieldAut a K τ x = x := by
  haveI : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 2 * a + 1) hK
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (suzukiGroup 0 (ZMod 2)) = 20 :=
    CFSG.RankThree.PartTwo.KFacts.KP7.card_suzukiGroup_two
  haveI : Finite (suzukiGroup 0 (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := suzukiGroup 0 (ZMod 2)) 5
    (by rw [hcard]; norm_num)
  refine ⟨szPrimeHom a K x₀, ?_, fun τ => ?_⟩
  · rw [orderOf_injective (szPrimeHom a K)
      CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szPrimeHom_injective x₀]
    exact hx₀
  · have hfix : ∀ y : ZMod 2,
        τ (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.primeEmb K y) =
          CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.primeEmb K y := by
      intro y
      rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) y with rfl | rfl <;> simp
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    simp only [CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.coe_szFieldAut,
      CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.coe_szPrimeHom, Matrix.map_apply]
    exact hfix _

end SuzukiAut



end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szPrimeHom)
open CFSG.Open (signalizerFixedSubgroup)

namespace CFSG.RankThree.PartTwo.Sec11



section SuzukiAut

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem sz_five_not_normalizes_sylow (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : suzukiGroup a K} (hx : orderOf x = 5)
    (Q : Sylow 2 (suzukiGroup a K)) :
    ¬ ∀ y ∈ (Q : Subgroup (suzukiGroup a K)), x * y * x⁻¹ ∈ (Q : Subgroup (suzukiGroup a K)) := by
  intro hnorm
  have := CFSG.LieType.Ree.finite_suzukiGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx5 : x ^ 5 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hpow : ∀ n : ℕ, ∀ y ∈ (Q : Subgroup (suzukiGroup a K)),
      x ^ n * y * (x ^ n)⁻¹ ∈ (Q : Subgroup (suzukiGroup a K)) := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simpa using hy
    | succ m ih =>
      intro y hy
      have e : x ^ (m + 1) * y * (x ^ (m + 1))⁻¹ = x * (x ^ m * y * (x ^ m)⁻¹) * x⁻¹ := by
        simp only [pow_succ', mul_inv_rev, mul_assoc]
      rw [e]
      exact hnorm _ (ih y hy)
  have hxN : x ∈ Subgroup.normalizer (Q : Subgroup (suzukiGroup a K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm h hh, fun hxh => ?_⟩
    have h4 := hpow 4 _ hxh
    have e' : x ^ 4 * (x * h * x⁻¹) * (x ^ 4)⁻¹ = x ^ 5 * h * (x ^ 5)⁻¹ := by
      group
    have e : x ^ 4 * (x * h * x⁻¹) * (x ^ 4)⁻¹ = h := by
      rw [e', hx5]
      simp
    rw [e] at h4
    exact h4
  have hN : ∀ g : Subgroup.zpowers x,
      g.1 ∈ Subgroup.normalizer (Q : Subgroup (suzukiGroup a K)) :=
    fun g => Subgroup.zpowers_le.2 hxN g.2
  have hmemQ : ∀ (g : Subgroup.zpowers x) (u : suzukiGroup a K),
      u ∈ (Q : Subgroup (suzukiGroup a K)) →
        g.1 * u * g.1⁻¹ ∈ (Q : Subgroup (suzukiGroup a K)) :=
    fun g u hu => (Subgroup.mem_normalizer_iff.1 (hN g) u).1 hu
  have hord : ∀ y g : suzukiGroup a K, orderOf (y * g * y⁻¹) = orderOf g := fun y g => by
    have h := (MulAut.conj y).orderOf_eq g
    rwa [MulAut.conj_apply] at h
  let _ : MulAction (Subgroup.zpowers x)
      {g : suzukiGroup a K // g ∈ (Q : Subgroup (suzukiGroup a K)) ∧ orderOf g = 2} :=
    { smul := fun g u => ⟨g.1 * u.1 * g.1⁻¹, hmemQ g u.1 u.2.1, by rw [hord, u.2.2]⟩
      one_smul := fun u => Subtype.ext (by
        show (1 : suzukiGroup a K) * u.1 * (1 : suzukiGroup a K)⁻¹ = u.1
        simp)
      mul_smul := fun g h u => Subtype.ext (by
        show g.1 * h.1 * u.1 * (g.1 * h.1)⁻¹ = g.1 * (h.1 * u.1 * h.1⁻¹) * g.1⁻¹
        simp [mul_assoc]) }
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPp : IsPGroup 5 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hcard := hPp.card_modEq_card_fixedPoints
    {g : suzukiGroup a K // g ∈ (Q : Subgroup (suzukiGroup a K)) ∧ orderOf g = 2}
  rw [CFSG.RankThree.PartTwo.KFacts.KP7.card_involutions_sylow hK Q] at hcard
  have hfix : IsEmpty (MulAction.fixedPoints (Subgroup.zpowers x)
      {g : suzukiGroup a K // g ∈ (Q : Subgroup (suzukiGroup a K)) ∧ orderOf g = 2}) := by
    refine ⟨fun w => ?_⟩
    obtain ⟨u, hu⟩ := w
    have hu' : ∀ g : Subgroup.zpowers x, g • u = u := hu
    have hxu' := congrArg Subtype.val (hu' ⟨x, Subgroup.mem_zpowers x⟩)
    have hxu : x * u.1 * x⁻¹ = u.1 := hxu'
    have hcent : x ∈ Subgroup.centralizer {u.1} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.1 hxu
    obtain ⟨P, -, hPC, hPuniq⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).1 u.1 u.2.2
    have hQP : Q = P := hPuniq Q u.2.1
    have hC : Subgroup.centralizer {u.1} = (Q : Subgroup (suzukiGroup a K)) := by
      rw [hPC, hQP]
    have hxQ : x ∈ (Q : Subgroup (suzukiGroup a K)) := by
      rw [← hC]
      exact hcent
    have hdvd : orderOf x ∣ 2 ^ (Nat.card (suzukiGroup a K)).factorization 2 := by
      rw [← Sylow.card_eq_multiplicity Q, ← Subgroup.orderOf_mk x hxQ]
      exact orderOf_dvd_natCard _
    rw [hx] at hdvd
    have h5 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    omega
  have hempty : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x)
      {g : suzukiGroup a K // g ∈ (Q : Subgroup (suzukiGroup a K)) ∧ orderOf g = 2}) = 0 :=
    Nat.card_of_isEmpty
  rw [hempty] at hcard
  unfold Nat.ModEq at hcard
  have hmod : ∀ n : ℕ, 2 ^ (2 * n + 1) % 5 = 2 ∨ 2 ^ (2 * n + 1) % 5 = 3 := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ih =>
      have e : 2 ^ (2 * (m + 1) + 1) = 2 ^ (2 * m + 1) * 4 := by ring
      rw [e]
      omega
  have := hmod a
  omega

end SuzukiAut



end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szPrimeHom)
open CFSG.Open (signalizerFixedSubgroup)

namespace CFSG.RankThree.PartTwo.Sec11



section SuzukiAut

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem sz_O2_fixed_eq_bot (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (τ : RingAut K) (N : Subgroup (suzukiGroup a K))
    (hN : IsPGroup 2 N) (hfix : ∀ n ∈ N, szFieldAut a K τ n = n)
    (hnorm : ∀ f : suzukiGroup a K, szFieldAut a K τ f = f → ∀ n ∈ N, f * n * f⁻¹ ∈ N) :
    N = ⊥ := by
  by_contra hne
  haveI : Finite (suzukiGroup a K) := CFSG.LieType.Ree.finite_suzukiGroup hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hne
  obtain ⟨x, hx5, hxfix⟩ := sz_exists_order_five hK
  have hxinvφ : szFieldAut a K τ x⁻¹ = x⁻¹ := by
    rw [map_inv, hxfix τ]
  have hxinvN : ∀ n ∈ N, x⁻¹ * n * x⁻¹⁻¹ ∈ N := hnorm x⁻¹ hxinvφ
  have hconj_ord : ∀ g w : suzukiGroup a K, orderOf (g * w * g⁻¹) = orderOf w := by
    intro g w
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective w
    simpa using h
  obtain ⟨z, hzN, hz2⟩ : ∃ z ∈ N, orderOf z = 2 := by
    obtain ⟨n₀, hn₀, hcard⟩ := (hN.nontrivial_iff_card).1 hNnt
    have h2dvd : 2 ∣ Nat.card N := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2dvd
    exact ⟨(z₀ : suzukiGroup a K), z₀.2, by rw [Subgroup.orderOf_coe]; exact hz₀⟩
  have hz₁N : x⁻¹ * z * x ∈ N := by
    have h := hxinvN z hzN
    rwa [inv_inv] at h
  have hz₁2 : orderOf (x⁻¹ * z * x) = 2 := by
    have h := hconj_ord x⁻¹ z
    rwa [inv_inv, hz2] at h
  obtain ⟨Q, hNQ⟩ := IsPGroup.exists_le_sylow (P := N) hN
  have hCz : Subgroup.centralizer ({z} : Set (suzukiGroup a K)) =
      (Q : Subgroup (suzukiGroup a K)) := by
    obtain ⟨P, -, hCP, hPuniq⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).1 z hz2
    have hQP : Q = P := hPuniq Q (hNQ hzN)
    rw [hQP]
    exact hCP
  have hCz₁ : Subgroup.centralizer ({x⁻¹ * z * x} : Set (suzukiGroup a K)) =
      (Q : Subgroup (suzukiGroup a K)) := by
    obtain ⟨P, -, hCP, hPuniq⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).1
        (x⁻¹ * z * x) hz₁2
    have hQP : Q = P := hPuniq Q (hNQ hz₁N)
    rw [hQP]
    exact hCP
  refine sz_five_not_normalizes_sylow ha hK hx5 Q ?_
  intro y hy
  have hy₁ : y ∈ Subgroup.centralizer ({x⁻¹ * z * x} : Set (suzukiGroup a K)) := by
    rw [hCz₁]
    exact hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy₁
  have hmem : x * y * x⁻¹ ∈ Subgroup.centralizer ({z} : Set (suzukiGroup a K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * y * x⁻¹ * z = x * (y * (x⁻¹ * z * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * z * x) * y) * x⁻¹ := by rw [hy₁]
      _ = z * (x * y * x⁻¹) := by group
  rw [hCz] at hmem
  exact hmem

end SuzukiAut



end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open CFSG.Blueprint
open CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szPrimeHom szFieldAut_S)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (exists_eq_conj_mul_szFieldAut
  suzukiSElt_mem_signalizerFixedSubgroup suzukiSElt_zero_one_involution
  orderOf_suzukiSElt_zero_one exists_conj_suzukiSElt_of_mem_suzukiU
  mem_fixedSubgroup_iff_forall_mem_zpowers)
open CFSG.Open (signalizerFixedSubgroup)

namespace CFSG.RankThree.PartTwo.Sec11



section SuzukiAut

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem szCentralizerFixed_eq_bot'
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : RingAut K}
    (hn2 : ¬ IsPGroup 2 (signalizerFixedSubgroup (szFieldAut a K σ))) :
    Subgroup.centralizer
      (signalizerFixedSubgroup (szFieldAut a K σ) : Set (suzukiGroup a K)) = ⊥ := by
  have hinv := (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).1
  set C := signalizerFixedSubgroup (szFieldAut a K σ)
  have hzC : suzukiSElt a K 0 1 ∈ C :=
    suzukiSElt_mem_signalizerFixedSubgroup (map_zero σ) (map_one σ)
  obtain ⟨P₀, -, hP₀, -⟩ := hinv _ (orderOf_suzukiSElt_zero_one hK)
  have hDP : Subgroup.centralizer (C : Set (suzukiGroup a K)) ≤
      (P₀ : Subgroup (suzukiGroup a K)) := by
    intro d hd
    rw [← hP₀, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hd _ hzC).symm
  have hDp : IsPGroup 2 (Subgroup.centralizer (C : Set (suzukiGroup a K))) :=
    P₀.isPGroup'.to_le hDP
  by_contra hne
  have h2dvd : 2 ∣ Nat.card (Subgroup.centralizer (C : Set (suzukiGroup a K))) :=
    hDp.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hd2 : orderOf (d : suzukiGroup a K) = 2 := by rw [Subgroup.orderOf_coe, hd]
  obtain ⟨P₁, -, hP₁, -⟩ := hinv _ hd2
  have hCP : C ≤ (P₁ : Subgroup (suzukiGroup a K)) := by
    intro c hc
    rw [← hP₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 d.2 c hc
  have hCp : IsPGroup 2 C := P₁.isPGroup'.to_le hCP
  exact hn2 hCp

theorem szMem_zpowers_of_fixes' (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : RingAut K}
    (hn2 : ¬ IsPGroup 2 (signalizerFixedSubgroup (szFieldAut a K σ)))
    {g : MulAut (suzukiGroup a K)}
    (hg : ∀ x ∈ signalizerFixedSubgroup (szFieldAut a K σ), g x = x) :
    g ∈ Subgroup.zpowers (szFieldAut a K σ) := by
  obtain ⟨x, τ, rfl⟩ := exists_eq_conj_mul_szFieldAut ha hK g
  obtain ⟨hzU, hz2, hz1⟩ := suzukiSElt_zero_one_involution (a := a) (K := K) hK
  have hxU : x ∈ suzukiU a K := by
    have h1 := hg _ (suzukiSElt_mem_signalizerFixedSubgroup (a := a) (σ := σ) (map_zero σ)
      (map_one σ))
    rw [MulAut.mul_apply, szFieldAut_S, map_zero, map_one, MulAut.conj_apply] at h1
    rw [← CFSG.RankThree.centralizer_eq_suzukiU hK hzU hz2 hz1,
      Subgroup.mem_centralizer_singleton_iff]
    calc x * suzukiSElt a K 0 1 = x * suzukiSElt a K 0 1 * x⁻¹ * x := by group
      _ = suzukiSElt a K 0 1 * x := by rw [h1]
  have hτ : ∀ u : K, σ u = u → τ u = u := by
    intro u hu
    have h1 := hg _ (suzukiSElt_mem_signalizerFixedSubgroup (a := a) (σ := σ) (u := u) (v := 0)
      hu (map_zero σ))
    rw [MulAut.mul_apply, szFieldAut_S, map_zero, MulAut.conj_apply] at h1
    obtain ⟨w, hw⟩ := exists_conj_suzukiSElt_of_mem_suzukiU hK hxU (τ u) 0
    rw [hw] at h1
    exact (suzukiSElt_inj.1 h1).1
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1
    (CFSG.RankThree.LinearTwo.mem_zpowers_of_forall_fixed Nat.prime_two (n := 2 * a + 1)
      (by omega) hK σ τ hτ)
  have hxD : x ∈ Subgroup.centralizer
      (signalizerFixedSubgroup (szFieldAut a K σ) : Set (suzukiGroup a K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 := hg c hc
    have h2 : szFieldAut a K (σ ^ j) c = c := by
      rw [map_zpow]
      exact (mem_fixedSubgroup_iff_forall_mem_zpowers _ c).1 hc _ (Subgroup.zpow_mem_zpowers _ _)
    rw [MulAut.mul_apply, h2, MulAut.conj_apply] at h1
    calc c * x = x * c * x⁻¹ * x := by rw [h1]
      _ = x * c := by group
  rw [szCentralizerFixed_eq_bot' ha hK hn2, Subgroup.mem_bot] at hxD
  subst hxD
  rw [map_one, one_mul, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

theorem sz_mem_zpowers_of_fixes (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : RingAut K) {g : MulAut (suzukiGroup a K)}
    (hg : ∀ x : suzukiGroup a K, szFieldAut a K σ x = x → g x = x) :
    g ∈ Subgroup.zpowers (szFieldAut a K σ) := by
  obtain ⟨x, hxo, hxf⟩ := sz_exists_order_five hK
  have hxC : x ∈ signalizerFixedSubgroup (szFieldAut a K σ) := hxf σ
  have hn2 : ¬ IsPGroup 2 (signalizerFixedSubgroup (szFieldAut a K σ)) := by
    intro hP
    obtain ⟨k, hk⟩ := hP ⟨x, hxC⟩
    have hdvd := orderOf_dvd_of_pow_eq_one hk
    rw [Subgroup.orderOf_mk, hxo] at hdvd
    have h52 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    exact absurd h52 (by decide)
  exact szMem_zpowers_of_fixes' ha hK hn2 fun y hy => hg y hy

end SuzukiAut



end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szPrimeHom)
open CFSG.Open (signalizerFixedSubgroup)

namespace CFSG.RankThree.PartTwo.Sec11



section SuzukiAut

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem sz_aut_order_three_facts (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : MulAut (suzukiGroup a K)) (hσ : σ ^ 3 = 1) :
    (∃ t : suzukiGroup a K, t ≠ 1 ∧ σ t = t) ∧
    (∀ N : Subgroup (suzukiGroup a K), IsPGroup 2 N → (∀ n ∈ N, σ n = n) →
      (∀ f : suzukiGroup a K, σ f = f → ∀ n ∈ N, f * n * f⁻¹ ∈ N) → N = ⊥) ∧
    (∀ α : MulAut (suzukiGroup a K), (∃ k : ℕ, α ^ 2 ^ k = 1) →
      (∀ f : suzukiGroup a K, σ f = f → α f = f) → α = 1) := by
  have h3 : ∀ x ∈ Subgroup.zpowers σ, x ^ 3 = 1 := fun x hx =>
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_pow_eq_one hσ))
  have hred : ∃ (γ : MulAut (suzukiGroup a K)) (τ : RingAut K),
      szFieldAut a K τ ^ 3 = 1 ∧ σ = γ * szFieldAut a K τ * γ⁻¹ := by
    by_cases hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut σ
    ·
      have hmodel : SuzukiModel (suzukiGroup a K) 2 (2 * a + 1) :=
        ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
      have hP : IsPGroup 3 (Subgroup.zpowers σ) := fun x =>
        ⟨1, by rw [pow_one]; exact Subtype.ext (h3 x x.2)⟩
      have hinf := CFSG.RankThree.PartTwo.KFacts.KP7.inf_inner_eq_bot hmodel hP
      have hmem : σ ∈ Subgroup.zpowers σ ⊓
          CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
        Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers σ, hin⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact ⟨1, 1, by simp, by simp [hmem]⟩
    ·
      obtain ⟨φ, hφ, -, d, hd, hσeq⟩ :=
        CFSG.RankThree.PartTwo.KFacts.isField_sz_of_pow_three_eq_one ha hK hσ hin
      obtain ⟨τ, rfl⟩ : φ ∈ (szFieldAut a K).range := hφ
      obtain ⟨g, rfl⟩ : d ∈ (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range := hd
      refine ⟨MulAut.conj g, τ, ?_, hσeq⟩
      have h := hσ
      rw [hσeq, conj_pow] at h
      calc szFieldAut a K τ ^ 3
          = (MulAut.conj g)⁻¹ * (MulAut.conj g * szFieldAut a K τ ^ 3 * (MulAut.conj g)⁻¹) *
              MulAut.conj g := by group
        _ = 1 := by rw [h]; group
  obtain ⟨γ, τ, hφ3, hσeq⟩ := hred
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨t, ht2, hfixt⟩ :=
      CFSG.RankThree.PartTwo.KFacts.KP7.exists_involution_fixed ha hK (Subgroup.zpowers σ) h3
    refine ⟨t, ?_, hfixt σ (Subgroup.mem_zpowers σ)⟩
    rintro rfl
    rw [orderOf_one] at ht2
    norm_num at ht2
  ·
    intro N hN hfixN hnormN
    have hN' : IsPGroup 2 (N.comap γ.toMonoidHom) :=
      hN.comap_of_injective γ.toMonoidHom γ.injective
    have hfix' : ∀ x ∈ N.comap γ.toMonoidHom, szFieldAut a K τ x = x := by
      intro x hx
      have hγx : σ (γ x) = γ x := hfixN (γ x) (Subgroup.mem_comap.1 hx)
      have h1 : σ (γ x) = γ (szFieldAut a K τ x) := by
        rw [hσeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      exact γ.injective (h1.symm.trans hγx)
    have hnorm' : ∀ f : suzukiGroup a K, szFieldAut a K τ f = f →
        ∀ x ∈ N.comap γ.toMonoidHom, f * x * f⁻¹ ∈ N.comap γ.toMonoidHom := by
      intro f hf x hx
      have hF : σ (γ f) = γ f := by
        rw [hσeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hf]
      have key := hnormN (γ f) hF (γ x) (Subgroup.mem_comap.1 hx)
      show γ (f * x * f⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact key
    have hbot := sz_O2_fixed_eq_bot ha hK τ (N.comap γ.toMonoidHom) hN' hfix' hnorm'
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hmem : γ⁻¹ n ∈ N.comap γ.toMonoidHom := by
      rw [Subgroup.mem_comap]
      show γ (γ⁻¹ n) ∈ N
      rw [MulAut.apply_inv_self]
      exact hn
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : γ (γ⁻¹ n) = γ 1 := congrArg γ hmem
    rwa [MulAut.apply_inv_self, map_one] at h1
  ·
    rintro α ⟨k, hk⟩ hfixα
    have hconj : (γ⁻¹ * α * γ) ^ 2 ^ k = 1 := by
      rw [show γ⁻¹ * α * γ = γ⁻¹ * α * (γ⁻¹)⁻¹ by group, conj_pow, hk]
      group
    have hfix' : ∀ x : suzukiGroup a K, szFieldAut a K τ x = x → (γ⁻¹ * α * γ) x = x := by
      intro x hx
      have hγx : σ (γ x) = γ x := by
        rw [hσeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx]
      have hα : α (γ x) = γ x := hfixα (γ x) hγx
      rw [MulAut.mul_apply, MulAut.mul_apply, hα, MulAut.inv_apply_self]
    have hmemz := sz_mem_zpowers_of_fixes ha hK τ (g := γ⁻¹ * α * γ) hfix'
    have h3' : (γ⁻¹ * α * γ) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1
        ((orderOf_dvd_of_mem_zpowers hmemz).trans (orderOf_dvd_of_pow_eq_one hφ3))
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have hone : orderOf (γ⁻¹ * α * γ) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3')
        (orderOf_dvd_of_pow_eq_one hconj)
    have hα1 : γ⁻¹ * α * γ = 1 := orderOf_eq_one_iff.1 hone
    calc α = γ * (γ⁻¹ * α * γ) * γ⁻¹ := by group
      _ = 1 := by simp [hα1]

end SuzukiAut



end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank Subgroup
open CFSG.Blueprint

namespace CFSG.RankThree.PartTwo.Sec11



@[expose] def szT_conj {X : Type} [Group X] (J : Subgroup X) (g : X)
    (hg : g ∈ Subgroup.normalizer (J : Set X)) : MulAut ↥J :=
  J.normalizerMonoidHom ⟨g, hg⟩

theorem szT_conj_apply {X : Type} [Group X] (J : Subgroup X) (g : X)
    (hg : g ∈ Subgroup.normalizer (J : Set X)) (j : ↥J) :
    ((szT_conj J g hg j : ↥J) : X) = g * (j : X) * g⁻¹ :=
  rfl

theorem szT_conj_fix_iff {X : Type} [Group X] (J : Subgroup X) (g : X)
    (hg : g ∈ Subgroup.normalizer (J : Set X)) (j : ↥J) :
    szT_conj J g hg j = j ↔ g * (j : X) = (j : X) * g := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [szT_conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  · intro h
    apply Subtype.ext
    rw [szT_conj_apply]
    exact mul_inv_eq_iff_eq_mul.mpr h

theorem szT_conj_pow_eq_one {X : Type} [Group X] (J : Subgroup X) (g : X)
    (hg : g ∈ Subgroup.normalizer (J : Set X)) (n : ℕ)
    (hn : g ^ n ∈ Subgroup.centralizer (J : Set X)) :
    szT_conj J g hg ^ n = 1 := by
  have hm : (⟨g, hg⟩ : Subgroup.normalizer (J : Set X)) ^ n ∈ J.normalizerMonoidHom.ker := by
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact hn
  unfold szT_conj
  rw [← map_pow]
  exact MonoidHom.mem_ker.mp hm

theorem szT_congr_apply {G H : Type} [Group G] [Group H] (e : G ≃* H) (τ : MulAut G)
    (s : H) : MulAut.congr e τ s = e (τ (e.symm s)) :=
  rfl

theorem szT_congr_fix {G H : Type} [Group G] [Group H] (e : G ≃* H) (τ : MulAut G) (s : H) :
    MulAut.congr e τ s = s ↔ τ (e.symm s) = e.symm s := by
  rw [szT_congr_apply]
  constructor
  · intro h
    have h1 := congrArg e.symm h
    rw [MulEquiv.symm_apply_apply] at h1
    exact h1
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem suzukiAutFacts_of_kpSz (hK2 : KFacts.KPSz) :
    SuzukiAutFacts := by
  intro X _ _ hX J hJs hJp h3 y hy hy3
  have hnab : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hcen : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcomm g z
    have hbot : commutator ↥J = ⊥ := (commutator_eq_bot_iff_center_eq_top (G := ↥J)).mpr hcen
    have htop : commutator ↥J = ⊤ := Group.IsPerfect.commutator_eq_top (G := ↥J)
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥J)
    have hmem : a ∈ commutator ↥J := by
      rw [htop]
      exact Subgroup.mem_top a
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ha hmem
  have hcat : CFSG.Assembly.InCatalog ↥J :=
    CFSG.KCore.KGroupAllSimple.catalogue_self CFSG.Assembly.inCatalog_isoInvariant
      (CFSG.IsKGroup.subgroup hX J)
  obtain ⟨f, hf⟩ := hK2 ↥J hnab hcat h3
  obtain ⟨-, a, ha, K, hKF, hKfin, rfl, hK, ⟨iso⟩⟩ := hf
  have hσ3 : (MulAut.congr iso (szT_conj J y hy)) ^ 3 = 1 := by
    rw [← map_pow, szT_conj_pow_eq_one J y hy 3 hy3, map_one]
  obtain ⟨hA, hB, hC⟩ :=
    sz_aut_order_three_facts ha hK (MulAut.congr iso (szT_conj J y hy)) hσ3
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨t, ht1, hσt⟩ := hA
    have h1 : iso (szT_conj J y hy (iso.symm t)) = t := hσt
    have hfix : szT_conj J y hy (iso.symm t) = iso.symm t := by
      calc szT_conj J y hy (iso.symm t)
          = iso.symm (iso (szT_conj J y hy (iso.symm t))) :=
            (MulEquiv.symm_apply_apply iso _).symm
        _ = iso.symm t := by rw [h1]
    refine ⟨((iso.symm t : ↥J) : X), (iso.symm t).2, ?_, ?_⟩
    · intro h2
      apply ht1
      have h4 : iso.symm t = 1 := Subtype.ext h2
      rw [← MulEquiv.apply_symm_apply iso t, h4, map_one]
    · exact (szT_conj_fix_iff J y hy (iso.symm t)).mp hfix
  ·
    intro N hNJ hN hNcomm hNnorm
    have hNJp : IsPGroup 2 (N.subgroupOf J) :=
      hN.comap_of_injective J.subtype (Subgroup.subtype_injective J)
    have hNSp : IsPGroup 2 ((N.subgroupOf J).map iso.toMonoidHom) :=
      hNJp.map iso.toMonoidHom
    have hNSfix : ∀ n ∈ (N.subgroupOf J).map iso.toMonoidHom,
        MulAut.congr iso (szT_conj J y hy) n = n := by
      intro n hn
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hn
      have hjN : (j : X) ∈ N := Subgroup.mem_subgroupOf.mp hj
      have hσj : szT_conj J y hy j = j :=
        (szT_conj_fix_iff J y hy j).mpr (hNcomm _ hjN)
      show iso (szT_conj J y hy (iso.symm (iso j))) = iso j
      rw [MulEquiv.symm_apply_apply, hσj]
    have hNSnorm : ∀ f : suzukiGroup a K, MulAut.congr iso (szT_conj J y hy) f = f →
        ∀ n ∈ (N.subgroupOf J).map iso.toMonoidHom,
          f * n * f⁻¹ ∈ (N.subgroupOf J).map iso.toMonoidHom := by
      intro f hf n hn
      obtain ⟨f', rfl⟩ := iso.surjective f
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hn
      have hf' : szT_conj J y hy f' = f' := by
        have h1 := (szT_congr_fix iso (szT_conj J y hy) (iso f')).mp hf
        rwa [MulEquiv.symm_apply_apply] at h1
      have hyf' : y * (f' : X) = (f' : X) * y := (szT_conj_fix_iff J y hy f').mp hf'
      have hmemN : (f' : X) * (j : X) * (f' : X)⁻¹ ∈ N :=
        hNnorm _ f'.2 hyf' _ (Subgroup.mem_subgroupOf.mp hj)
      have hmemJ : f' * j * f'⁻¹ ∈ N.subgroupOf J := Subgroup.mem_subgroupOf.mpr hmemN
      have heq : iso f' * iso.toMonoidHom j * (iso f')⁻¹ = iso.toMonoidHom (f' * j * f'⁻¹) := by
        simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rw [heq]
      exact Subgroup.mem_map_of_mem _ hmemJ
    have hNSbot := hB _ hNSp hNSfix hNSnorm
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxJ : x ∈ J := hNJ hx
    have hmem : (⟨x, hxJ⟩ : ↥J) ∈ N.subgroupOf J := Subgroup.mem_subgroupOf.mpr hx
    have hmemS : iso.toMonoidHom ⟨x, hxJ⟩ ∈ (N.subgroupOf J).map iso.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hmem
    rw [hNSbot, Subgroup.mem_bot] at hmemS
    have hmemS' : iso ⟨x, hxJ⟩ = 1 := hmemS
    have h1 : (⟨x, hxJ⟩ : ↥J) = 1 := iso.injective (hmemS'.trans (map_one iso).symm)
    exact congrArg Subtype.val h1
  ·
    intro x hx _ hkx hcomm' j hj
    obtain ⟨k, hk⟩ := hkx
    have hxpow : szT_conj J x hx ^ 2 ^ k = 1 :=
      szT_conj_pow_eq_one J x hx (2 ^ k) (by rw [hk]; exact Subgroup.one_mem _)
    have hαpow : (MulAut.congr iso (szT_conj J x hx)) ^ 2 ^ k = 1 := by
      rw [← map_pow, hxpow, map_one]
    have hαfix : ∀ s : suzukiGroup a K, MulAut.congr iso (szT_conj J y hy) s = s →
        MulAut.congr iso (szT_conj J x hx) s = s := by
      intro s hs
      obtain ⟨s', rfl⟩ := iso.surjective s
      have hσs : szT_conj J y hy s' = s' := by
        have h1 := (szT_congr_fix iso (szT_conj J y hy) (iso s')).mp hs
        rwa [MulEquiv.symm_apply_apply] at h1
      have hxs : szT_conj J x hx s' = s' :=
        (szT_conj_fix_iff J x hx s').mpr
          (hcomm' _ s'.2 ((szT_conj_fix_iff J y hy s').mp hσs))
      apply (szT_congr_fix iso (szT_conj J x hx) (iso s')).mpr
      rw [MulEquiv.symm_apply_apply]
      exact hxs
    have hα1 : MulAut.congr iso (szT_conj J x hx) = 1 := hC _ ⟨k, hαpow⟩ hαfix
    have hαj : szT_conj J x hx ⟨j, hj⟩ = ⟨j, hj⟩ := by
      have h1 : MulAut.congr iso (szT_conj J x hx) (iso ⟨j, hj⟩) = iso ⟨j, hj⟩ := by
        rw [hα1, MulAut.one_apply]
      have h2 := (szT_congr_fix iso (szT_conj J x hx) (iso ⟨j, hj⟩)).mp h1
      rwa [MulEquiv.symm_apply_apply] at h2
    exact (szT_conj_fix_iff J x hx ⟨j, hj⟩).mp hαj



end CFSG.RankThree.PartTwo.Sec11

end
