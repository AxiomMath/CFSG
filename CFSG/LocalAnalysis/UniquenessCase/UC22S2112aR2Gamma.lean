module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Card
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Field
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Beta
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.UCK47
import CFSG.LocalAnalysis.UniquenessCase.UC6G.S28
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r2_exists_lift {L : Subgroup G} (hsol : IsPGroup 2 (CFSG.solvableRadical ↥L))
    {b : G} (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : orderOf b = r) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {A : Type} [Group A]
    (hA : IsPGroup p A) (ι : A →* BarInf L) (hι : Function.Injective ι) (κ : A →* A)
    (hκ : ∀ a, inducedBarInfAutHom L ⟨b, hb⟩ (ι a) = ι (κ a)) :
    ∃ ψ : A →* G, Function.Injective ψ ∧ (∀ a, ψ a ∈ L) ∧ ∀ a, b * ψ a * b⁻¹ = ψ (κ a) := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* BarInf L := QuotientGroup.mk' (CFSG.solvableRadical ↥L)
  let U : Subgroup (BarInf L) := ι.range
  have hUp : IsPGroup p ↥U := hA.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  let E : Subgroup G := (U.comap π).map L.subtype
  have hEL : E ≤ L := Subgroup.map_subtype_le _
  have hbE : b ∈ normalizer (E : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := hx
    refine ⟨L.normalizerMonoidHom ⟨b, hb⟩ x, ⟨κ a, ?_⟩, rfl⟩
    change ι (κ a) = inducedBarInfAutHom L ⟨b, hb⟩ (π x)
    rw [← hκ, ha]
  have hB : IsPGroup r ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, hbr])
  have hBE : zpowers b ≤ normalizer (E : Set G) := Subgroup.zpowers_le.2 hbE
  have hfE : ∀ x : ↥E, π (Subgroup.inclusion hEL x) ∈ U := by
    rintro ⟨_, y, hy, rfl⟩
    exact hy
  let f : ↥E →* ↥U := (π.comp (Subgroup.inclusion hEL)).codRestrict U hfE
  have hf : Function.Surjective f := by
    rintro ⟨u, hu⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) u
    exact ⟨⟨x, x, hu, rfl⟩, rfl⟩
  have hker : IsPGroup 2 f.ker := by
    have hkerEq : f.ker = (CFSG.solvableRadical ↥L).comap (Subgroup.inclusion hEL) := by
      ext x
      show f x = 1 ↔ Subgroup.inclusion hEL x ∈ CFSG.solvableRadical ↥L
      rw [← QuotientGroup.eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hkerEq]
    exact IsPGroup.comap_of_injective hsol _ (Subgroup.inclusion_injective hEL)
  have hnd : ¬ r ∣ Nat.card (Sylow p ↥E) := by
    obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥E))
    have h1 : Nat.card (Sylow p ↥E) ∣ Nat.card ↥E :=
      (Sylow.card_dvd_index P₀).trans (Subgroup.index_dvd_card _)
    rw [← Subgroup.card_ker_mul_card_of_surjective hf] at h1
    obtain ⟨a, ha⟩ := hker.exists_card_eq
    obtain ⟨k, hk⟩ := hUp.exists_card_eq
    rw [ha, hk] at h1
    have hcop : Nat.Coprime (Nat.card (Sylow p ↥E)) (p ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_sylow p ↥E)))
    have h2 := hcop.dvd_of_dvd_mul_right h1
    intro hr'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow (hr'.trans h2)))
  let φ : ↥(zpowers b) →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hBE)
  let : MulDistribMulAction ↥(zpowers b) ↥E := MulDistribMulAction.compHom ↥E φ
  obtain ⟨P, hP⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥E) hnd
  have hPb : ∀ x ∈ (P : Subgroup ↥E), E.normalizerMonoidHom ⟨b, hbE⟩ x ∈ (P : Subgroup ↥E) := by
    intro x hx
    have h := congrArg (fun Q : Sylow p ↥E => (Q : Subgroup ↥E))
      (MulAction.mem_fixedPoints.mp hP (⟨b, mem_zpowers b⟩ : ↥(zpowers b)))
    rw [Sylow.pointwise_smul_def] at h
    rw [← h]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, rfl⟩
  have hdisj : Disjoint (P : Subgroup ↥E) f.ker :=
    IsPGroup.disjoint_of_ne p 2 hp2 _ _ P.isPGroup' hker
  have hinj : ∀ x ∈ (P : Subgroup ↥E), ∀ y ∈ (P : Subgroup ↥E), f x = f y → x = y := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * y ∈ (P : Subgroup ↥E) ⊓ f.ker :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx) hy,
        MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hxy'
    exact inv_mul_eq_one.1 hxy'
  have hsurj : ∀ u : ↥U, ∃ x ∈ (P : Subgroup ↥E), f x = u := by
    intro u
    have hS : ((P.mapSurjective hf : Sylow p ↥U) : Subgroup ↥U) = ⊤ :=
      ((P.mapSurjective hf).is_maximal' (hUp.to_subgroup ⊤) le_top).symm
    have hu : u ∈ ((P.mapSurjective hf : Sylow p ↥U) : Subgroup ↥U) := by
      rw [hS]
      exact Subgroup.mem_top u
    rw [Sylow.coe_mapSurjective] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    exact ⟨x, hx, hxu⟩
  let ρ : ↥(P : Subgroup ↥E) →* ↥U := f.comp (P : Subgroup ↥E).subtype
  have hρ : Function.Bijective ρ := by
    refine ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy), fun u => ?_⟩
    obtain ⟨x, hx, hxu⟩ := hsurj u
    exact ⟨⟨x, hx⟩, hxu⟩
  let e : ↥(P : Subgroup ↥E) ≃* ↥U := MulEquiv.ofBijective ρ hρ
  let j : A →* ↥(P : Subgroup ↥E) := e.symm.toMonoidHom.comp ι.rangeRestrict
  have hj : ∀ a, f (j a : ↥E) = ι.rangeRestrict a := fun a => e.apply_symm_apply _
  refine ⟨E.subtype.comp ((P : Subgroup ↥E).subtype.comp j), ?_, fun a => hEL (j a : ↥E).2,
    fun a => ?_⟩
  · intro a a' h
    have h1 : (j a : ↥E) = j a' := Subtype.ext h
    have h2 : ι.rangeRestrict a = ι.rangeRestrict a' := by rw [← hj, ← hj, h1]
    exact hι (congrArg Subtype.val h2)
  ·
    have hy : E.normalizerMonoidHom ⟨b, hbE⟩ (j a : ↥E) ∈ (P : Subgroup ↥E) := hPb _ (j a).2
    have hfy : f (E.normalizerMonoidHom ⟨b, hbE⟩ (j a : ↥E)) = f (j (κ a) : ↥E) := by
      rw [hj]
      apply Subtype.ext
      change π (L.normalizerMonoidHom ⟨b, hb⟩ (Subgroup.inclusion hEL (j a : ↥E))) = ι (κ a)
      rw [← hκ]
      change inducedBarInfAutHom L ⟨b, hb⟩ (π (Subgroup.inclusion hEL (j a : ↥E))) = _
      congr 1
      exact congrArg Subtype.val (hj a)
    exact congrArg Subtype.val (hinj _ hy _ (j (κ a)).2 hfy)

theorem uc22s2112r2_two_lt_card_of_ne (hK : UCK.K47) {Mg : Type} [Group Mg] [Finite Mg]
    (hMg : CFSG.Open.IsKGroup Mg) (Q₀ : Subgroup Mg) [Q₀.Normal] (hQ₀ : IsPGroup 2 Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {p f r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hr : r.Prime) (hr2 : r ≠ 2) (hpr : p ≠ r) (hrf : r ∣ f) (hf1 : 1 ≤ f)
    (τ : GaloisField p f ≃+* GaloisField p f) (hτr : orderOf τ = r)
    (hcard : Nat.card {t : GaloisField p f // τ t = t} = p ^ (f / r))
    (ψ : Multiplicative (GaloisField p f) →* Mg) (hψ : Function.Injective ψ) {b : Mg}
    (hbr : orderOf b = r)
    (hbψ : ∀ t, b * ψ (Multiplicative.ofAdd t) * b⁻¹ = ψ (Multiplicative.ofAdd (τ t))) :
    2 < Nat.card ↥(Q₀ ⊓ centralizer ((zpowers b : Subgroup Mg) : Set Mg)) := by
  classical
  have hp : p.Prime := Fact.out
  rw [← not_le]
  intro hfix
  let N : Multiplicative (GaloisField p f) →* Multiplicative (GaloisField p f) :=
    AddMonoidHom.toMultiplicative (τ.toAddMonoidHom - AddMonoidHom.id _)
  let Q : Subgroup Mg := (ψ.comp N).range
  have hQmem : ∀ t, ψ (Multiplicative.ofAdd (τ t - t)) ∈ Q := fun t =>
    ⟨Multiplicative.ofAdd t, rfl⟩
  have hQcases : ∀ g ∈ Q, ∃ t, ψ (Multiplicative.ofAdd (τ t - t)) = g := by
    rintro g ⟨a, rfl⟩
    exact ⟨Multiplicative.toAdd a, rfl⟩
  have hpow : ∀ a : Multiplicative (GaloisField p f), a ^ p = 1 := fun a =>
    Multiplicative.toAdd.injective (by
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul])
  have hQexp : ∀ g : ↥Q, g ^ p = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    change (ψ.comp N) a ^ p = 1
    rw [← map_pow, hpow, map_one]
  have hQp : IsPGroup p ↥Q := fun g => ⟨1, by rw [pow_one]; exact hQexp g⟩
  have hbQ : b ∈ normalizer (Q : Set Mg) := by
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨t, rfl⟩ := hQcases g hg
    rw [hbψ, map_sub]
    exact hQmem (τ t)
  have hDQ : zpowers b ≤ normalizer (Q : Set Mg) := Subgroup.zpowers_le.2 hbQ
  have hτp : τ ^ r = 1 := hτr ▸ pow_orderOf_eq_one τ
  have hrF : (r : GaloisField p f) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (GaloisField p f) p]
    exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 h)
  have hcomm : ⁅zpowers b, Q⁆ = Q := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro d hd g hg
      rw [commutatorElement_def]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.1 (hDQ hd) g).1 hg) (Q.inv_mem hg)
    · intro g hg
      obtain ⟨t, rfl⟩ := hQcases g hg
      obtain ⟨u, ⟨s, hs⟩, hu⟩ := uc22s2112r2_sub_one_onto τ hτp hrF ⟨t, rfl⟩
      have hg' : ψ (Multiplicative.ofAdd (τ t - t)) = ⁅b, ψ (Multiplicative.ofAdd u)⁆ := by
        rw [← hu, commutatorElement_def, hbψ, ofAdd_sub, map_div, div_eq_mul_inv]
      rw [hg']
      exact Subgroup.commutator_mem_commutator (mem_zpowers b) (hs ▸ hQmem s)
  have hcyc : IsCyclic ↥Q := UC6.k47_transport_two_uc6 hK hMg Q₀ hQ₀ hchar hp hr hp2 hr2 hpr
    (zpowers b) (by rw [Nat.card_zpowers, hbr]) hfix Q hQp inferInstance hDQ hcomm
  have hle : Nat.card ↥Q ≤ p := by
    refine Nat.le_of_dvd hp.pos ?_
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd.2 fun g => orderOf_dvd_of_pow_eq_one (hQexp g)
  have hker : Nat.card N.ker = p ^ (f / r) := by
    rw [← hcard]
    refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun a => ?_)
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (τ (Multiplicative.toAdd a) - Multiplicative.toAdd a) = 1 ↔ _
    rw [ofAdd_eq_one, sub_eq_zero]
  have hFcard : Nat.card (Multiplicative (GaloisField p f)) = p ^ f :=
    (Nat.card_congr Multiplicative.toAdd).trans (GaloisField.card p f (by omega))
  have hNr : Nat.card N.range = p ^ (f - f / r) := by
    have h1 := Subgroup.card_ker_mul_card_range N
    rw [hker, hFcard] at h1
    have h2 : p ^ f = p ^ (f / r) * p ^ (f - f / r) := by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.div_le_self f r)]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h1
  have hQcard : Nat.card ↥Q = p ^ (f - f / r) := by
    rw [← hNr]
    change Nat.card ↥(ψ.comp N).range = _
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hψ]
  have h2 : 2 ≤ f - f / r := by
    obtain ⟨k, hk⟩ := hrf
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h => by
      rw [h, mul_zero] at hk
      omega
    have hfr : f / r = k := by rw [hk, Nat.mul_div_cancel_left k hr.pos]
    have h3 : 3 * k ≤ r * k := Nat.mul_le_mul_right k (by have := hr.two_le; omega)
    omega
  have hp1 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at hp1
  have hle' : p ^ (f - f / r) ≤ p := hQcard ▸ hle
  exact absurd hle' (not_le.2 (hp1.trans_le (Nat.pow_le_pow_right hp.pos h2)))

theorem uc22s2112r2_two_lt_card_of_eq (hK : UCK.K47) {Mg : Type} [Group Mg] [Finite Mg]
    (hMg : CFSG.Open.IsKGroup Mg) (Q₀ : Subgroup Mg) [Q₀.Normal] (hQ₀ : IsPGroup 2 Q₀)
    (hchar : centralizer (Q₀ : Set Mg) ≤ Q₀) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (τ : GaloisField p f ≃+* GaloisField p f) (hτp : orderOf τ = p)
    (ψ : Multiplicative (GaloisField p f) →* Mg) (hψ : Function.Injective ψ) {b : Mg}
    (hbp : orderOf b = p)
    (hbψ : ∀ t, b * ψ (Multiplicative.ofAdd t) * b⁻¹ = ψ (Multiplicative.ofAdd (τ t))) :
    2 < Nat.card ↥(Q₀ ⊓ centralizer ((zpowers b : Subgroup Mg) : Set Mg)) := by
  classical
  have hp : p.Prime := Fact.out
  rw [← not_le]
  intro hfix
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτp
    exact hp.one_lt.ne hτp
  obtain ⟨t₀, ht₀, hfix₀⟩ :=
    uc22s2112r2_exists_sub_one_sq τ (hτp ▸ pow_orderOf_eq_one τ) hτ1
  have hpow : ∀ a : Multiplicative (GaloisField p f), a ^ p = 1 := fun a =>
    Multiplicative.toAdd.injective (by
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul])
  have hby : b * ψ (Multiplicative.ofAdd t₀) * b⁻¹ =
      ψ (Multiplicative.ofAdd t₀) * ψ (Multiplicative.ofAdd (τ t₀ - t₀)) := by
    rw [hbψ, ← map_mul, ← ofAdd_add]
    congr 2
    ring
  have hbc : b * ψ (Multiplicative.ofAdd (τ t₀ - t₀)) * b⁻¹ =
      ψ (Multiplicative.ofAdd (τ t₀ - t₀)) := by
    rw [hbψ, hfix₀]
  set y := ψ (Multiplicative.ofAdd t₀) with hy
  set c := ψ (Multiplicative.ofAdd (τ t₀ - t₀)) with hc
  have hbcC : Commute b c := mul_inv_eq_iff_eq_mul.1 hbc
  have hRcomm : ∀ x ∈ ψ.range, ∀ z ∈ ψ.range, x * z = z * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [← map_mul, mul_comm, map_mul]
  have hbR : b ∈ normalizer (ψ.range : Set Mg) := by
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨a, rfl⟩ := hg
    exact ⟨Multiplicative.ofAdd (τ (Multiplicative.toAdd a)), (hbψ (Multiplicative.toAdd a)).symm⟩
  have hXR : zpowers b ≤ normalizer (ψ.range : Set Mg) := Subgroup.zpowers_le.2 hbR
  have hRp : IsPGroup p ↥ψ.range := by
    rintro ⟨_, a, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    change ψ a ^ p = 1
    rw [← map_pow, hpow, map_one]
  have hXp : IsPGroup p ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, hbp])
  have hP : IsPGroup p ↥(ψ.range ⊔ zpowers b) := IsPGroup.to_sup_of_normal_left' hRp hXp hXR
  have hyR : y ∈ ψ.range := ⟨Multiplicative.ofAdd t₀, hy.symm⟩
  have hyc : ∀ x ∈ zpowers b, ∀ w ∈ ψ.range ⊔ zpowers b,
      (y * x * y⁻¹ * x⁻¹) * w = w * (y * x * y⁻¹ * x⁻¹) := by
    intro x hx w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hcx : c * b ^ k = b ^ k * c := ((hbcC.zpow_left k).eq).symm
    have hzR : y * b ^ k * y⁻¹ * (b ^ k)⁻¹ ∈ ψ.range := by
      have h1 : b ^ k * y⁻¹ * (b ^ k)⁻¹ ∈ ψ.range :=
        (Subgroup.mem_normalizer_iff.1 (hXR hx) y⁻¹).1 (ψ.range.inv_mem hyR)
      have h2 : y * b ^ k * y⁻¹ * (b ^ k)⁻¹ = y * (b ^ k * y⁻¹ * (b ^ k)⁻¹) := by group
      rw [h2]
      exact ψ.range.mul_mem hyR h1
    have hzb : b * (y * b ^ k * y⁻¹ * (b ^ k)⁻¹) * b⁻¹ = y * b ^ k * y⁻¹ * (b ^ k)⁻¹ := by
      have e1 : b * (y * b ^ k * y⁻¹ * (b ^ k)⁻¹) * b⁻¹ =
          (b * y * b⁻¹) * (b * b ^ k * b⁻¹) * (b * y * b⁻¹)⁻¹ * (b * b ^ k * b⁻¹)⁻¹ := by
        group
      have e2 : b * b ^ k * b⁻¹ = b ^ k := by group
      rw [e1, e2, hby]
      calc y * c * b ^ k * (y * c)⁻¹ * (b ^ k)⁻¹
          = y * (c * b ^ k) * c⁻¹ * y⁻¹ * (b ^ k)⁻¹ := by group
        _ = y * (b ^ k * c) * c⁻¹ * y⁻¹ * (b ^ k)⁻¹ := by rw [hcx]
        _ = y * b ^ k * y⁻¹ * (b ^ k)⁻¹ := by group
    have hPC : ψ.range ⊔ zpowers b ≤
        centralizer ({y * b ^ k * y⁻¹ * (b ^ k)⁻¹} : Set Mg) := by
      refine sup_le (fun v hv => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hRcomm v hv _ hzR
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.1 hzb
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hPC hw)).symm
  have hk := UC6.k47_transport_uc6 hK hMg Q₀ hQ₀ hchar hp hp2 (zpowers b)
    (by rw [Nat.card_zpowers, hbp]) hfix (ψ.range ⊔ zpowers b) hP le_sup_right y
    (le_sup_left (a := ψ.range) hyR) hyc b (mem_zpowers b)
  have hc1 : c = 1 := by
    have h1 : b * y * b⁻¹ = y := by rw [← hk, mul_inv_cancel_right]
    rw [hby] at h1
    exact mul_eq_left.1 h1
  apply ht₀
  have h2 : Multiplicative.ofAdd (τ t₀ - t₀) = 1 := hψ (by rw [map_one, ← hc]; exact hc1)
  exact sub_eq_zero.1 (ofAdd_eq_one.1 h2)

theorem uc22s2112r2_two_lt_card (hGA : GriessAllModelsStatement) {D : Data G}
    {L : Subgroup G} (hL : L ∈ calC D.M) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hX : LieModel (BarInf L) .PSL 2 p f) {b : G} (hbM : b ∈ D.M)
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    2 < Nat.card ↥(F07.Q7 D ⊓ centralizer ({b} : Set G)) := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  set θ := inducedBarInfAutHom L ⟨b, hb⟩ with hθdef
  have hbpow : (⟨b, hb⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := by
    rw [← hbr, ← Subgroup.orderOf_mk b hb]
    exact pow_orderOf_eq_one _
  have hθr : orderOf θ = r := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hθdef, ← map_pow, hbpow, map_one]
    · intro h1
      exact hθ (h1 ▸ Subgroup.one_mem _)
  obtain ⟨w, τ, hw, hτr, hrf, hcard, hθw⟩ := uc22s2112r2_exists_rootParam hp2 hX hr hr2 hθr hθ
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hrf' : r ≤ f := Nat.le_of_dvd (by omega) hrf
  have hZ : center (Bar2 L) = ⊥ :=
    uc22s2112r2_center_bar2_eq_bot hGA hL hp2 (fun _ => by omega) hX
  have hsol : IsPGroup 2 (CFSG.solvableRadical ↥L) := by
    rw [solvableRadical_eq_pCore_of_center_bar2_eq_bot hL.2.2 hZ]
    exact CFSG.pCore_isPGroup
  have hA : IsPGroup p (Multiplicative (GaloisField p f)) := fun a =>
    ⟨1, Multiplicative.toAdd.injective (by
      rw [pow_one, toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul])⟩
  obtain ⟨ψ, hψ, hψL, hbψ⟩ := uc22s2112r2_exists_lift hsol hb hr hr2 hbr hp2 hA w hw
    (AddMonoidHom.toMultiplicative τ.toAddMonoidHom) fun a => hθw (Multiplicative.toAdd a)
  have hLM : L ≤ D.M := hL.1.le
  let ψM : Multiplicative (GaloisField p f) →* ↥D.M := ψ.codRestrict D.M fun a => hLM (hψL a)
  have hψM : Function.Injective ψM := fun a a' h => hψ (congrArg Subtype.val h)
  have hbMr : orderOf (⟨b, hbM⟩ : ↥D.M) = r := by
    rw [Subgroup.orderOf_mk]
    exact hbr
  have hbψM : ∀ t, (⟨b, hbM⟩ : ↥D.M) * ψM (Multiplicative.ofAdd t) * (⟨b, hbM⟩ : ↥D.M)⁻¹ =
      ψM (Multiplicative.ofAdd (τ t)) := fun t => Subtype.ext (hbψ (Multiplicative.ofAdd t))
  obtain ⟨hMg, hQ₀, hchar⟩ := UC6G.moduleData_uc6 D
  have key : 2 < Nat.card ↥(CFSG.pCore 2 ↥D.M ⊓
      centralizer ((zpowers (⟨b, hbM⟩ : ↥D.M) : Subgroup ↥D.M) : Set ↥D.M)) := by
    rcases eq_or_ne p r with hpr | hpr
    · subst hpr
      exact uc22s2112r2_two_lt_card_of_eq UCK.k47 hMg _ hQ₀ hchar hp2 τ hτr ψM hψM hbMr hbψM
    · exact uc22s2112r2_two_lt_card_of_ne UCK.k47 hMg _ hQ₀ hchar hp2 hr hr2 hpr hrf hf1 τ hτr
        hcard ψM hψM hbMr hbψM
  refine key.trans_le ?_
  have hle : (CFSG.pCore 2 ↥D.M ⊓
      centralizer ((zpowers (⟨b, hbM⟩ : ↥D.M) : Subgroup ↥D.M) : Set ↥D.M)).map D.M.subtype ≤
      F07.Q7 D ⊓ centralizer ({b} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨x, hxQ, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxC _ (mem_zpowers _)).symm)⟩
  have h := Subgroup.card_le_of_le hle
  rwa [Subgroup.card_map_of_injective D.M.subtype_injective] at h

theorem uc22s2112r2_false_of_r74Card (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (h74 : F07.R74Card D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hMs : IsStronglyPEmbedded p D.M) (hX : LieModel (BarInf L) .PSL 2 p f) {b : G}
    (hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hbr : orderOf b = r)
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    False := by
  have h1 := h74 p _ (uc22s2112r2_sec7Hyp hGA hH c hL hp2 hMs hX hbB hb hr hr2 hbr hθ)
  have h2 := uc22s2112r2_two_lt_card hGA hL hp2 hX (c.hBM hbB) hb hr hr2 hbr hθ
  obtain ⟨-, -, hCN, -⟩ := uc22s2112r2_normalizer hH c hL.1.le hbB (hbr ▸ hr)
  have h3 := Subgroup.card_le_of_le (inf_le_inf_left (F07.Q7 D) hCN)
  omega

theorem s21_12aFR2g_of_r74Card (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (h74 : F07.R74Card D) : S21_12aFR2g D Ch := by
  rintro hH c L hL p hp35 hpσ f hf hf2 hX - ⟨b, hbB, hb, hbf, hθ⟩
  have : Fact p.Prime := ⟨by rcases hp35 with rfl | rfl <;> norm_num⟩
  exact (uc22s2112r2_false_of_r74Card hGA h74 hH c hL (by omega)
    (UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ) hX hbB hb hf hf2 hbf
    hθ).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
