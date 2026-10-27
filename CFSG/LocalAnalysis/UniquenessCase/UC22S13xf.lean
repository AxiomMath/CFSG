module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible
import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small
import CFSG.LieType.ChevTwo.OppositeFixedExcTits
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

theorem uc22s13xf_mem_cartan_of_conj {K : Type*} [Group K] {P : Subgroup K} {t q x : K}
    (hq : q ∈ borel P) (hx : q * x * q⁻¹ ∈ cartan P t) : x ∈ cartan P (q⁻¹ * t * q) := by
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conjugate_iff_mul_inv] at hx2
  have hqi : q⁻¹ ∈ borel P := (borel P).inv_mem hq
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 := (borel P).mul_mem ((borel P).mul_mem hqi hx1) hq
    rwa [show q⁻¹ * (q * x * q⁻¹) * q = x by group] at h1
  · rw [mem_conjugate_iff_mul_inv]
    have h1 := (borel P).mul_mem ((borel P).mul_mem hqi hx2) hq
    rwa [show q⁻¹ * (t * (q * x * q⁻¹) * t⁻¹) * q = q⁻¹ * t * q * x * (q⁻¹ * t * q)⁻¹ by group]
      at h1

theorem uc22s13xf_exists_cartan_of_le_borel {K : Type} [Group K]
    [Finite K] {n i e : ℕ} (hK : BenderType K n i e) (Q : Sylow 2 K) {A : Subgroup K}
    (hAM : A ≤ borel (Q : Subgroup K)) (hA : Odd (Nat.card A)) :
    ∃ t : K, t * t = 1 ∧ t ∉ borel (Q : Subgroup K) ∧ A ≤ cartan (Q : Subgroup K) t := by
  obtain ⟨t₀, h₀⟩ := hK.exists_benderCore Q
  obtain ⟨q, hq, hqA⟩ := h₀.exists_conj_cartan_of_odd Q.isPGroup' hAM hA
  have hqM : q ∈ borel (Q : Subgroup K) := le_borel _ hq
  refine ⟨q⁻¹ * t₀ * q, ?_, ?_, fun a ha => uc22s13xf_mem_cartan_of_conj hqM (hqA a ha)⟩
  · calc q⁻¹ * t₀ * q * (q⁻¹ * t₀ * q) = q⁻¹ * (t₀ * t₀) * q := by group
      _ = 1 := by rw [h₀.sq_eq_one]; group
  · intro hmem
    apply h₀.not_mem
    have h1 := (borel (Q : Subgroup K)).mul_mem ((borel (Q : Subgroup K)).mul_mem hqM hmem)
      ((borel (Q : Subgroup K)).inv_mem hqM)
    rwa [show q * (q⁻¹ * t₀ * q) * q⁻¹ = t₀ by group] at h1

theorem uc22s13xf_le_borel_of_odd {K : Type} [Group K] [Finite K]
    {n i e : ℕ} (hK : BenderType K n i e) (Q : Sylow 2 K) {A : Subgroup K}
    (hA : Odd (Nat.card A)) (hAQ : (A : Set K) * Q = Q * A) : A ≤ borel (Q : Subgroup K) := by
  classical
  haveI := hK.isSimple
  obtain ⟨t₀, h₀⟩ := hK.exists_benderCore Q
  by_cases hX : A ⊔ (Q : Subgroup K) = ⊤
  swap
  · exact le_sup_left.trans (h₀.le_borel_of_le le_sup_right hX)
  exfalso
  set P : Subgroup K := (Q : Subgroup K)
  have hAP : (A : Set K) * (P : Set K) = (P : Set K) * A := hAQ
  have hset : ((A ⊔ P : Subgroup K) : Set K) = (A : Set K) * P :=
    CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hAP
  have hfac : ∀ g : K, ∃ a ∈ A, ∃ u ∈ P, a * u = g := by
    intro g
    have hg : g ∈ ((A ⊔ P : Subgroup K) : Set K) := by
      rw [hX]
      exact Subgroup.mem_top g
    rw [hset] at hg
    exact Set.mem_mul.mp hg
  have hA₀ : Odd (Nat.card ↥(A ⊓ borel P)) := hA.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨t, ht, htM, hA₀D⟩ := uc22s13xf_exists_cartan_of_le_borel hK Q inf_le_right hA₀
  have h := h₀.of_involution ht htM
  have hti : t⁻¹ = t := inv_eq_of_mul_self ht
  have hDA : ∀ d ∈ cartan P t, d ∈ A := by
    intro d hd
    obtain ⟨a, ha, u, hu, rfl⟩ := hfac d
    have haM : a ∈ borel P := by
      have h1 := (borel P).mul_mem (cartan_le_borel P t hd) ((borel P).inv_mem (le_borel P hu))
      rwa [mul_inv_cancel_right] at h1
    have haD : a ∈ cartan P t := hA₀D (Subgroup.mem_inf.mpr ⟨ha, haM⟩)
    have huD : u ∈ cartan P t := by
      have h1 := (cartan P t).mul_mem ((cartan P t).inv_mem haD) hd
      rwa [inv_mul_cancel_left] at h1
    have hu1 : u ∈ P ⊓ cartan P t := Subgroup.mem_inf.mpr ⟨hu, huD⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hu1
    rw [hu1, mul_one]
    exact ha
  obtain ⟨a, ha, u, hu, hau⟩ := hfac t
  have haD : ∀ d ∈ cartan P t, a⁻¹ * d * a ∈ cartan P t := by
    intro d hd
    refine hA₀D (Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem (A.inv_mem ha) (hDA d hd)) ha, ?_⟩)
    have h1 : a⁻¹ * d * a = u * (t⁻¹ * d * t) * u⁻¹ := by
      rw [← hau]
      group
    rw [h1, hti]
    exact (borel P).mul_mem ((borel P).mul_mem (le_borel P hu)
      (cartan_le_borel P t (h.cartan_mul_mul hd))) ((borel P).inv_mem (le_borel P hu))
  have hcomm : ∀ d ∈ cartan P t, u * d = d * u := by
    intro d hd
    have h1 : u * d * u⁻¹ ∈ cartan P t := by
      have h2 : u * d * u⁻¹ = a⁻¹ * (t * d * t⁻¹) * a := by
        rw [← hau]
        group
      rw [h2, hti]
      exact haD _ (h.cartan_mul_mul hd)
    have h2 : u * d * u⁻¹ * d⁻¹ ∈ P := by
      have hdP : d * u⁻¹ * d⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (cartan_le_borel P t hd) u⁻¹).mp (P.inv_mem hu)
      have h3 := P.mul_mem hu hdP
      rwa [show u * (d * u⁻¹ * d⁻¹) = u * d * u⁻¹ * d⁻¹ by group] at h3
    have h3 : u * d * u⁻¹ * d⁻¹ ∈ P ⊓ cartan P t :=
      Subgroup.mem_inf.mpr ⟨h2, (cartan P t).mul_mem h1 ((cartan P t).inv_mem hd)⟩
    rw [h.inf_eq, Subgroup.mem_bot] at h3
    calc u * d = u * d * u⁻¹ * d⁻¹ * (d * u) := by group
      _ = d * u := by rw [h3, one_mul]
  have hn2 : 2 ≤ n := hK.two_le.2
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hDcard : Nat.card (cartan P t) = (2 ^ n - 1) * e := h.card_cartan
  have hDpos : 0 < Nat.card (cartan P t) := Nat.card_pos
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he0 | he0
    · rw [he0, mul_zero] at hDcard
      omega
    · exact he0
  have h3e : 3 * e ≤ Nat.card (cartan P t) := by
    rw [hDcard]
    exact Nat.mul_le_mul_right e (by omega)
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ cartan P t, d ≠ 1 := by
    rcases (cartan P t).bot_or_exists_ne_one with hbot | hex
    · rw [hbot, Subgroup.card_bot] at h3e
      omega
    · exact hex
  have hu1 : u = 1 := by
    rcases hK.cases' with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨rfl, -, -⟩
    · exact h.eq_one_of_commute_cartan Q.isPGroup' hd hd1 hu (hcomm d hd)
    · exact h.eq_one_of_commute_cartan Q.isPGroup' hd hd1 hu (hcomm d hd)
    · by_contra hu1
      have hdu : d * u * d⁻¹ * u⁻¹ ∈ rootCenter P := by
        rw [← hcomm d hd, mul_inv_cancel_right, mul_inv_cancel]
        exact (rootCenter P).one_mem
      have hz := hK.fixedPointFree_unitary Q ht htM hd hd1 hu hdu
      have hcard := h.card_cartan_inf_centralizer hz hu1
      have hle : cartan P t ≤ centralizer ({u} : Set K) := fun x hx =>
        Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff.mp hy]
          exact hcomm x hx
      rw [inf_eq_left.mpr hle] at hcard
      omega
  have htA : t ∈ A := by
    rw [← hau, hu1, mul_one]
    exact ha
  have ht1 : t ≠ 1 := fun h1 => htM (by rw [h1]; exact (borel P).one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) ht1
  have hdvd := Subgroup.orderOf_dvd_natCard A htA
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr hdvd)

theorem uc22s13xf_le_cartan_of_odd {K : Type} [Group K] [Finite K]
    {n i e : ℕ} (hK : BenderType K n i e) (hOut : IsPGroup 2 (Outer K))
    {A T : Subgroup (MulAut K)} (hA : Odd (Nat.card A)) (hT : IsPGroup 2 T) (Q : Sylow 2 K)
    (hQ : (Q : Subgroup K).map MulAut.conj ≤ T) (hAT : (A : Set (MulAut K)) * T = T * A) :
    ∃ t : K, t * t = 1 ∧ t ∉ borel (Q : Subgroup K) ∧
      A ≤ (cartan (Q : Subgroup K) t).map MulAut.conj := by
  classical
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : g ∈ center K := Subgroup.mem_center_iff.mpr fun x => by
      have h1 := congrArg (fun α : MulAut K => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rw [hK.center_eq_bot] at hgZ
    exact Subgroup.mem_bot.mp hgZ
  have hArange : A ≤ (MulAut.conj : K →* MulAut K).range := fun α hα =>
    CFSG.LieType.ChevTwo.inner_of_odd_orderOf_of_outer hOut α
      (hA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A hα))
  have hAinn : ∀ α ∈ A, ∃ y : K, MulAut.conj y = α := fun α hα =>
    MonoidHom.mem_range.mp (hArange hα)
  have hA'odd : Odd (Nat.card (A.comap (MulAut.conj : K →* MulAut K))) := by
    rw [← Subgroup.card_map_of_injective (K := A.comap (MulAut.conj : K →* MulAut K)) hinj,
      Subgroup.map_comap_eq_self hArange]
    exact hA
  have hQT : (Q : Subgroup K) ≤ T.comap (MulAut.conj : K →* MulAut K) :=
    Subgroup.map_le_iff_le_comap.mp hQ
  have hTQ : T.comap (MulAut.conj : K →* MulAut K) = Q :=
    Q.is_maximal' (hT.comap_of_injective _ hinj) hQT
  have hmemQ : ∀ k : K, MulAut.conj k ∈ T → k ∈ (Q : Subgroup K) := fun k hk => by
    rw [← hTQ]
    exact hk
  have hperm : ((A.comap (MulAut.conj : K →* MulAut K) : Subgroup K) : Set K) * Q =
      Q * (A.comap (MulAut.conj : K →* MulAut K) : Subgroup K) := by
    ext x
    simp only [Set.mem_mul, SetLike.mem_coe, Subgroup.mem_comap]
    constructor
    · rintro ⟨a, ha, q, hq, rfl⟩
      have hmem : MulAut.conj a * MulAut.conj q ∈ (A : Set (MulAut K)) * T :=
        Set.mul_mem_mul ha (hQ (Subgroup.mem_map_of_mem _ hq))
      rw [hAT] at hmem
      obtain ⟨τ, hτ, α, hα, hτα⟩ := Set.mem_mul.mp hmem
      obtain ⟨b, rfl⟩ := hAinn α hα
      refine ⟨a * q * b⁻¹, hmemQ _ ?_, b, hα, by group⟩
      rw [map_mul, map_mul, map_inv, ← hτα, mul_inv_cancel_right]
      exact hτ
    · rintro ⟨q, hq, a, ha, rfl⟩
      have hmem : MulAut.conj q * MulAut.conj a ∈ (T : Set (MulAut K)) * A :=
        Set.mul_mem_mul (hQ (Subgroup.mem_map_of_mem _ hq)) ha
      rw [← hAT] at hmem
      obtain ⟨α, hα, τ, hτ, hατ⟩ := Set.mem_mul.mp hmem
      obtain ⟨b, rfl⟩ := hAinn α hα
      refine ⟨b, hα, b⁻¹ * q * a, hmemQ _ ?_, by group⟩
      rw [map_mul, map_mul, map_inv, mul_assoc, ← hατ, inv_mul_cancel_left]
      exact hτ
  have hle : A.comap (MulAut.conj : K →* MulAut K) ≤ borel (Q : Subgroup K) :=
    uc22s13xf_le_borel_of_odd hK Q hA'odd hperm
  obtain ⟨t, ht, htM, hD⟩ := uc22s13xf_exists_cartan_of_le_borel hK Q hle hA'odd
  refine ⟨t, ht, htM, fun α hα => ?_⟩
  obtain ⟨y, rfl⟩ := hAinn α hα
  exact Subgroup.mem_map_of_mem _ (hD (Subgroup.mem_comap.mpr hα))

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xf_map_permutes {H : Type*} [Group H] {N B T : Subgroup G} (hBN : B ≤ N)
    (hTN : T ≤ N) (hBT : Permutes B T) (f : ↥N →* H) :
    ((B.subgroupOf N).map f : Set H) * (T.subgroupOf N).map f =
      (T.subgroupOf N).map f * (B.subgroupOf N).map f := by
  have key : ∀ {X Y : Subgroup G}, X ≤ N → Y ≤ N → (X : Set G) * Y = Y * X →
      ((X.subgroupOf N).map f : Set H) * (Y.subgroupOf N).map f ⊆
        (Y.subgroupOf N).map f * (X.subgroupOf N).map f := by
    intro X Y hXN hYN hXY z hz
    obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    have hmem : (x : G) * y ∈ (X : Set G) * Y :=
      Set.mul_mem_mul (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)
    rw [hXY] at hmem
    obtain ⟨y', hy', x', hx', heq⟩ := Set.mem_mul.mp hmem
    refine Set.mem_mul.mpr ⟨f ⟨y', hYN hy'⟩, ⟨⟨y', hYN hy'⟩, hy', rfl⟩, f ⟨x', hXN hx'⟩,
      ⟨⟨x', hXN hx'⟩, hx', rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext heq)
  have hBT' : (B : Set G) * T = T * B := hBT
  exact Set.Subset.antisymm (key hBN hTN hBT') (key hTN hBN hBT'.symm)

theorem uc22s13xf_cartan {M L T B : Subgroup G} (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hBN : B ≤ normalizer (L : Set G)) (hB : Odd (Nat.card B)) (hBT : Permutes B T) {n : ℕ}
    (hn : IsPowTwo n) (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) :
    ∃ (Q : Sylow 2 (Bar2 L)) (t : Bar2 L), t * t = 1 ∧ t ∉ borel (Q : Subgroup (Bar2 L)) ∧
      IsCyclic (cartan (Q : Subgroup (Bar2 L)) t) ∧
      (IsL2 (Bar2 L) n → Nat.card (cartan (Q : Subgroup (Bar2 L)) t) = 2 ^ n - 1) ∧
      (IsU3 (Bar2 L) n → Nat.card (cartan (Q : Subgroup (Bar2 L)) t) = 2 ^ (2 * n) - 1) ∧
      ∀ b : ↥(normalizer (L : Set G)), (b : G) ∈ B →
        UC6S846.rhoL L b ∈ (cartan (Q : Subgroup (Bar2 L)) t).map MulAut.conj := by
  classical
  have hn2 : 2 ≤ n := by
    have h1 : 1 ≤ n ∧ 2 ^ n ≠ 2 := by
      rcases hX with h | h
      · have hadm := CFSG.Blueprint.LieModel.admissible h
        exact ⟨hadm.2.1, fun h2 => hadm.2.2.2.1 (by rw [h2])⟩
      · have hadm := CFSG.Blueprint.LieModel.admissible h
        exact ⟨hadm.2.1, fun h2 => hadm.2.2.2 (by rw [h2])⟩
    rcases Nat.lt_or_ge n 2 with h | h
    · exfalso
      have hn1 : n = 1 := by omega
      exact h1.2 (by rw [hn1]; norm_num)
    · exact h
  obtain ⟨k, hk⟩ := hn
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hk
      omega
    · exact h0
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
    have hev : n = 2 * 2 ^ (k - 1) := by
      rw [hk, ← pow_succ']
      congr 1
      omega
    have h4 : 2 ^ n = 4 ^ 2 ^ (k - 1) := by
      rw [hev, pow_mul]
      norm_num
    have h41 : 4 ^ 2 ^ (k - 1) % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have hnd : ¬ 3 ∣ 2 ^ n + 1 := by
      rw [h4]
      omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
  obtain ⟨i, e, hK, hOut⟩ :
      ∃ i e : ℕ, BenderType (Bar2 L) n i e ∧ IsPGroup 2 (Outer (Bar2 L)) := by
    rcases hX with h | h
    · obtain ⟨φ⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2Model_of_lieModel h
      have hK : BenderType (Bar2 L) n 1 1 := .linear n hn2 φ
      exact ⟨1, 1, hK, IsPGroup.of_card (n := k) (hK.outer_linear.2.trans hk)⟩
    · obtain ⟨e, hK⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_psu3 hn2 h
      obtain ⟨Dd, hDn, -, hDcard, -, hQcard⟩ := hK.outer_unitary
      refine ⟨3, e, hK, IsPGroup.of_card (n := k + 1) ?_⟩
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Dd, hQcard, hDcard, hgcd, mul_one, hk]
      ring
  have hMN : M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hTN : T ≤ normalizer (L : Set G) := hT.le.trans hMN
  have hAodd : Odd (Nat.card ((B.subgroupOf (normalizer (L : Set G))).map (UC6S846.rhoL L))) :=
    hB.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans
      (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv)))
  have hTA : IsPGroup 2 ((T.subgroupOf (normalizer (L : Set G))).map (UC6S846.rhoL L)) :=
    (hT.isPGroup.of_injective (Subgroup.subgroupOfEquivOfLe hTN).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTN).injective).map _
  have hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L := hT.inf_of_le_normalizer hLM hMN
  obtain ⟨S, hS⟩ := hTL.exists_sylow_eq_subgroupOf
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hQ : ((S.mapSurjective hπ : Sylow 2 (Bar2 L)) : Subgroup (Bar2 L)).map MulAut.conj ≤
      (T.subgroupOf (normalizer (L : Set G))).map (UC6S846.rhoL L) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Sylow.coe_mapSurjective] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hsT : (s : G) ∈ T := by
      have h1 : s ∈ (T ⊓ L).subgroupOf L := by
        rw [← hS]
        exact hs
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).1
    refine ⟨⟨(s : G), Subgroup.le_normalizer s.2⟩, hsT, ?_⟩
    rw [UC6S846.rhoL_inner L (s : G) s.2]
    rfl
  obtain ⟨t, ht, htM, hAD⟩ := uc22s13xf_le_cartan_of_odd hK hOut hAodd hTA (S.mapSurjective hπ) hQ
    (uc22s13xf_map_permutes hBN hTN hBT (UC6S846.rhoL L))
  have hcore := hK.benderCore (S.mapSurjective hπ) ht htM
  refine ⟨S.mapSurjective hπ, t, ht, htM, hcore.isCyclic, ?_, ?_, ?_⟩
  · intro h2
    obtain ⟨φ⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2Model_of_lieModel h2
    obtain ⟨-, rfl, rfl⟩ := hK.unique (BenderType.linear n hn2 φ)
    rw [hcore.card_cartan, mul_one]
  · intro h3
    obtain ⟨e', hK'⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_psu3 hn2 h3
    obtain ⟨-, rfl, rfl⟩ := hK.unique hK'
    rw [hcore.card_cartan]
    rcases hK'.cases' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, he, -⟩
    · omega
    · omega
    · rw [he, hgcd, Nat.div_one]
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      obtain ⟨y, hy⟩ : ∃ y, 2 ^ n = y + 1 := ⟨2 ^ n - 1, by omega⟩
      rw [show 2 * n = n + n by ring, pow_add, hy, Nat.add_sub_cancel]
      symm
      apply Nat.sub_eq_of_eq_add
      ring
  · intro b hb
    exact hAD (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb))

theorem uc22s13xf_fix_cartan {M L T B : Subgroup G} (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hBN : B ≤ normalizer (L : Set G)) (hB : Odd (Nat.card B)) (hBT : Permutes B T) {n : ℕ}
    (hn : IsPowTwo n) (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) :
    ∃ (Q : Sylow 2 (Bar2 L)) (t : Bar2 L), t * t = 1 ∧ t ∉ borel (Q : Subgroup (Bar2 L)) ∧
      IsCyclic (cartan (Q : Subgroup (Bar2 L)) t) ∧
      (IsL2 (Bar2 L) n → Nat.card (cartan (Q : Subgroup (Bar2 L)) t) = 2 ^ n - 1) ∧
      (IsU3 (Bar2 L) n → Nat.card (cartan (Q : Subgroup (Bar2 L)) t) = 2 ^ (2 * n) - 1) ∧
      (∀ b : ↥(normalizer (L : Set G)), (b : G) ∈ B →
        UC6S846.rhoL L b ∈ (cartan (Q : Subgroup (Bar2 L)) t).map MulAut.conj) ∧
      ∀ b : ↥(normalizer (L : Set G)), (b : G) ∈ B → ∀ d ∈ cartan (Q : Subgroup (Bar2 L)) t,
        UC6S846.rhoL L b d = d := by
  obtain ⟨Q, t, ht, htM, hcyc, h2, h3, hmem⟩ := uc22s13xf_cartan hLM hLn hT hBN hB hBT hn hX
  refine ⟨Q, t, ht, htM, hcyc, h2, h3, hmem, fun b hb d hd => ?_⟩
  obtain ⟨c, hc, hcb⟩ := hmem b hb
  rw [← hcb, MulAut.conj_apply]
  have hcd : c * d = d * c := by
    have := hcyc
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(cartan (Q : Subgroup (Bar2 L)) t))).comm ⟨c, hc⟩ ⟨d, hd⟩)
  rw [hcd, mul_inv_cancel_right]

end CFSG.LocalAnalysis.UniquenessCase.UC22
