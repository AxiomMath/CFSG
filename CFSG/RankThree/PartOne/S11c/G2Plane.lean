module

public import CFSG.RankThree.PartOne.S11c.G2Pgl
public import CFSG.RankThree.GroupTheory.SteinbergBMMovingPlaneTwoSubgroupObstruction
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.S11c.G2Transport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.GroupTheory.SteinbergBM

variable {K : Type} [Field K]

theorem isElementaryAbelian_of_mulEquiv' {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsElementaryAbelian p G) : IsElementaryAbelian p H :=
  CFSG.IsElementaryAbelian.of_mulEquiv e h

theorem g2_elementary_two [Finite K] (hK : Odd (Nat.card K)) {R : Subgroup (ModGL .G2 K)}
    (hR : R ≤ adjointGroup .G2 K) [Finite R] [IsElementaryAbelian 2 R] :
    Nat.card R ≤ 8 ∧ (Nat.card R = 8 → ∀ z ∈ adjointGroup .G2 K,
      (∀ r ∈ R, z * r = r * z) → Odd (orderOf z) → z = 1) := by
  classical
  by_cases hR1 : ∀ r ∈ R, r = 1
  · have hcard : Nat.card R = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext (by rw [hR1 x x.2, hR1 y y.2])⟩, ⟨1⟩⟩
    exact ⟨by omega, fun h8 => absurd h8 (by omega)⟩
  push Not at hR1
  obtain ⟨t, htR, ht1⟩ := hR1
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) t htR
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative R).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRle : R ≤ adjointGroup .G2 K ⊓ Subgroup.centralizer {t} := fun r hr =>
    ⟨hR hr, Subgroup.mem_centralizer_singleton_iff.2 (hcomm r hr t htR)⟩
  obtain ⟨b, L, _, ψ, ι, hb, hb1, hψ, hι, himg, -⟩ :=
    exists_involution_transport hK (hR htR) ht2 ht1
  have hK2 := ringChar_ne_two_of_odd_card hK
  obtain ⟨α, β, h, hS⟩ := exists_g2_pair hK hb hb1
  obtain ⟨R₀, hR₀X, hR₀, ⟨eR⟩⟩ := exists_corresponding_subgroup hψ hι himg hRle
  have : Finite R₀ := Finite.of_equiv R eR.toEquiv
  have : IsElementaryAbelian 2 R₀ := isElementaryAbelian_of_mulEquiv' eR inferInstance
  have hcard : Nat.card R₀ = Nat.card R := (Nat.card_congr eR.toEquiv).symm
  obtain ⟨hle, hcen⟩ := g2_toral_elementary_two hK2 hb h hS hR₀X
  refine ⟨hcard ▸ hle, fun h8 z hz hzc hodd => ?_⟩
  have hzt : z ∈ adjointGroup .G2 K ⊓ Subgroup.centralizer {t} :=
    ⟨hz, Subgroup.mem_centralizer_singleton_iff.2 (hzc t htR)⟩
  have hψz : ψ z ∈ (toralCentralizer .G2 K b).map ι := by
    rw [← himg]
    exact Subgroup.mem_map_of_mem ψ hzt
  obtain ⟨z₀, hz₀, hz₀e⟩ := hψz
  have hz₀R : ∀ r₀ ∈ R₀, z₀ * r₀ = r₀ * z₀ := fun r₀ hr₀ => by
    have : ι r₀ ∈ R.map ψ := hR₀ ▸ Subgroup.mem_map_of_mem ι hr₀
    obtain ⟨r, hr, hre⟩ := this
    apply hι
    rw [map_mul, map_mul, hz₀e, ← hre, ← map_mul, ← map_mul, hzc r hr]
  have hord : orderOf z₀ = orderOf z := by
    rw [← orderOf_injective ι hι z₀, hz₀e, orderOf_injective ψ hψ z]
  have h1 := hcen (hcard ▸ h8) z₀ hz₀ hz₀R (hord ▸ hodd)
  apply hψ
  rw [← hz₀e, h1, map_one, map_one]

theorem g2_plane_centralizes [Finite K] (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {E U : Subgroup (ModGL .G2 K)} (hE : E ≤ adjointGroup .G2 K)
    (hU : U ≤ adjointGroup .G2 K) [IsElementaryAbelian p E] (hEcard : Nat.card E = p ^ 2)
    [Finite U] (hU2 : IsPGroup 2 U) (hEU : ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U) :
    ∀ e ∈ E, ∀ u ∈ U, e * u = u * e := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; positivity)
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  by_contra hcon
  push Not at hcon
  obtain ⟨e₀, he₀, u₀, hu₀, hne⟩ := hcon
  obtain ⟨W, hWmem⟩ : ∃ W : Subgroup (ModGL .G2 K), ∀ z, z ∈ W ↔
      z ∈ U ∧ (∀ u ∈ U, u * z = z * u) ∧ z * z = 1 :=
    ⟨{ carrier := {z | z ∈ U ∧ (∀ u ∈ U, u * z = z * u) ∧ z * z = 1}
       one_mem' := ⟨U.one_mem, fun u _ => by simp, by simp⟩
       mul_mem' := fun {x y} hx hy => by
         have hxy : x * y = y * x := (hx.2.1 y hy.1).symm
         refine ⟨U.mul_mem hx.1 hy.1, fun u hu => ?_, ?_⟩
         · rw [← mul_assoc, hx.2.1 u hu, mul_assoc, hy.2.1 u hu, mul_assoc]
         · calc x * y * (x * y) = x * (y * x) * y := by group
             _ = x * (x * y) * y := by rw [← hxy]
             _ = (x * x) * (y * y) := by group
             _ = 1 := by rw [hx.2.2, hy.2.2, one_mul]
       inv_mem' := fun {x} hx => by
         have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx.2.2
         rw [hinv]
         exact hx }, fun z => Iff.rfl⟩
  have hWU : W ≤ U := fun z hz => ((hWmem z).1 hz).1
  have hWE : ∀ e ∈ E, ∀ w ∈ W, e * w * e⁻¹ ∈ W := by
    intro e he w hw
    have hw' := (hWmem w).1 hw
    refine (hWmem _).2 ⟨hEU e he w hw'.1, fun u hu => ?_, ?_⟩
    · have h1 : e⁻¹ * u * e ∈ U := by simpa using hEU e⁻¹ (E.inv_mem he) u hu
      have h2 := hw'.2.1 _ h1
      calc u * (e * w * e⁻¹) = e * ((e⁻¹ * u * e) * w) * e⁻¹ := by group
        _ = e * (w * (e⁻¹ * u * e)) * e⁻¹ := by rw [h2]
        _ = e * w * e⁻¹ * u := by group
    · calc e * w * e⁻¹ * (e * w * e⁻¹) = e * (w * w) * e⁻¹ := by group
        _ = 1 := by rw [hw'.2.2]; group
  by_cases hcent : ∀ e ∈ E, ∀ w ∈ W, e * w = w * e
  ·
    have hu₀1 : u₀ ≠ 1 := fun h => hne (by rw [h]; simp)
    have : Nontrivial U := ⟨⟨u₀, hu₀⟩, 1, fun h => hu₀1 (congrArg Subtype.val h)⟩
    have hZ : Nontrivial (Subgroup.center U) := hU2.center_nontrivial
    have hc2 : IsPGroup 2 (Subgroup.center U) := hU2.to_subgroup _
    have hdvd : 2 ∣ Nat.card (Subgroup.center U) := by
      have h1 : 1 < Nat.card (Subgroup.center U) := Finite.one_lt_card_iff_nontrivial.2 hZ
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hc2
      rw [hn] at h1 ⊢
      rcases n with _ | n
      · simp at h1
      · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
    obtain ⟨tc, htc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have htU : ((tc : U) : ModGL .G2 K) ∈ U := (tc : U).2
    have hcen : ∀ u ∈ U, u * ((tc : U) : ModGL .G2 K) = ((tc : U) : ModGL .G2 K) * u :=
      fun u hu => congrArg Subtype.val (Subgroup.mem_center_iff.1 tc.2 ⟨u, hu⟩)
    have hsq : tc ^ 2 = 1 := by rw [← htc]; exact pow_orderOf_eq_one tc
    have h2 : ((tc : U) : ModGL .G2 K) * ((tc : U) : ModGL .G2 K) = 1 := by
      have := congrArg (fun x : Subgroup.center U => ((x : U) : ModGL .G2 K)) hsq
      simpa [sq] using this
    have ht1 : ((tc : U) : ModGL .G2 K) ≠ 1 := fun h => by
      have : tc = 1 := Subtype.ext (Subtype.ext h)
      rw [this, orderOf_one] at htc
      omega
    have hxt : ∀ x ∈ E, x * ((tc : U) : ModGL .G2 K) = ((tc : U) : ModGL .G2 K) * x :=
      fun x hx => hcent x hx _ ((hWmem _).2 ⟨htU, hcen, h2⟩)
    have := g2_involution_largePrime hK (hU htU) (by rw [sq]; exact h2) ht1 hp hp3 (P := E)
      (U := U) (fun x hx => ⟨hE hx, Subgroup.mem_centralizer_singleton_iff.2 (hxt x hx)⟩)
      (fun u hu => ⟨hU hu, Subgroup.mem_centralizer_singleton_iff.2 (hcen u hu)⟩) hEp hU2 hEU
    exact hne (this e₀ he₀ u₀ hu₀)
  · push Not at hcent
    obtain ⟨e₁, he₁, w₁, hw₁, hne₁⟩ := hcent
    have hEW : E ≤ Subgroup.normalizer (W : Set (ModGL .G2 K)) := fun e he => by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        exact hWE e he w hw
      · intro hw
        have h1 := hWE e⁻¹ (E.inv_mem he) _ hw
        have h2 : e⁻¹ * (e * w * e⁻¹) * e⁻¹⁻¹ = w := by group
        rwa [h2] at h1
    have _hf : Fact (E ≤ Subgroup.normalizer (W : Set (ModGL .G2 K))) := ⟨hEW⟩
    have : Finite W := Finite.of_injective (Subgroup.inclusion hWU)
      (Subgroup.inclusion_injective hWU)
    have hW2 : IsPGroup 2 W :=
      hU2.of_injective (Subgroup.inclusion hWU) (Subgroup.inclusion_injective hWU)
    have hUE : commutatorAction E W ≠ ⊥ := by
      intro h0
      apply hne₁
      have hmem : (⟨w₁, hw₁⟩ : W)⁻¹ * ((⟨e₁, he₁⟩ : E) • (⟨w₁, hw₁⟩ : W)) ∈
          commutatorAction E W := by
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨⟨e₁, he₁⟩, ⟨w₁, hw₁⟩, rfl⟩
      rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have h2 := congrArg Subtype.val hmem.symm
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h2
      change e₁ * w₁ * e₁⁻¹ = w₁ at h2
      calc e₁ * w₁ = e₁ * w₁ * e₁⁻¹ * e₁ := by group
        _ = w₁ * e₁ := by rw [h2]
    obtain ⟨R, hR, D, hDcard, -, hR1, -, -, ⟨d, hd⟩, hGL, -, -, -, -, hDtriv, -⟩ :=
      moving_large_prime_plane_two_subgroup_fixed_line_and_small_order_obstruction
        (E := E) (U := W) hp hp2 hEcard hW2 hUE
    set R' : Subgroup (ModGL .G2 K) := R.map W.subtype with hR'
    have hR'W : ∀ x ∈ R', x ∈ W := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hR'C : R' ≤ adjointGroup .G2 K := fun x hx => hU (hWU (hR'W x hx))
    have : Finite R' :=
      Finite.of_equiv R (Subgroup.equivMapOfInjective R W.subtype W.subtype_injective).toEquiv
    have : IsElementaryAbelian 2 R' := by
      refine { is_comm := ⟨fun x y => ?_⟩, exponent_dvd_p := ?_ }
      · obtain ⟨x, hx⟩ := x
        obtain ⟨y, hy⟩ := y
        apply Subtype.ext
        change x * y = y * x
        exact (((hWmem x).1 (hR'W x hx)).2.1 y (hWU (hR'W y hy))).symm
      · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
        obtain ⟨x, hx⟩ := x
        apply Subtype.ext
        change x ^ 2 = 1
        rw [sq]
        exact ((hWmem x).1 (hR'W x hx)).2.2
    have hcardR' : Nat.card R' = Nat.card R := Subgroup.card_map_of_injective W.subtype_injective
    obtain ⟨hle8, hcen8⟩ := g2_elementary_two hK hR'C
    have hfr : Nat.card (R ⧸ frattini R) ≤ Nat.card R :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    have hd3 : d ≤ 3 := by
      by_contra hd4
      have : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨k, hk1, hkd, hk⟩ :=
      exists_dvd_two_pow_sub_one_of_dvd_card_GL_two hp hp2 (hGL d hd)
    have hk3 : k = 3 := by
      have hk' : k ≤ 3 := by omega
      interval_cases k
      · exact absurd (Nat.le_of_dvd (by norm_num) hk) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) hk) (by omega)
      · rfl
    have hd3' : d = 3 := by omega
    have hR8 : Nat.card R' = 8 := by
      have : 2 ^ d ≤ Nat.card R := hd ▸ hfr
      rw [hd3'] at this
      omega
    have : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; exact hp.ne_zero)
    have hDnt : Nontrivial D :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [hDcard]; exact hp.one_lt)
    obtain ⟨z, hz1⟩ := exists_ne (1 : D)
    have hz1' : (z : E) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzfix := hDtriv (z : E) z.2 hz1'
    have hzp : (z : E) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) _
    have hzpM : ((z : E) : ModGL .G2 K) ^ p = 1 := by
      have := congrArg (fun x : E => (x : ModGL .G2 K)) hzp
      simpa using this
    have hzne : ((z : E) : ModGL .G2 K) ≠ 1 := fun h => hz1' (Subtype.ext h)
    have hzord : orderOf ((z : E) : ModGL .G2 K) = p :=
      ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hzpM)).resolve_left
        (fun h => hzne (orderOf_eq_one_iff.1 h))
    have hzc : ∀ r ∈ R', ((z : E) : ModGL .G2 K) * r = r * ((z : E) : ModGL .G2 K) := by
      rintro _ ⟨w, hw, rfl⟩
      have h1 := congrArg Subtype.val (hzfix w hw)
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h1
      change ((z : E) : ModGL .G2 K) * w = w * ((z : E) : ModGL .G2 K)
      calc ((z : E) : ModGL .G2 K) * w
          = ((z : E) : ModGL .G2 K) * w * ((z : E) : ModGL .G2 K)⁻¹ * ((z : E) : ModGL .G2 K) := by
            group
        _ = w * ((z : E) : ModGL .G2 K) := by rw [h1]
    have := hcen8 hR8 _ (hE (z : E).2) hzc (hzord ▸ hp.odd_of_ne_two hp2)
    exact hzne this

end CFSG.RankThree.PartOne
