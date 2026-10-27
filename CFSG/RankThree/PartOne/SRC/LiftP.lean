module

public import Mathlib.GroupTheory.SchurZassenhaus
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup
open scoped Pointwise

theorem natCard_comap_of_surjective' {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (N : Subgroup H) :
    Nat.card ↥(N.comap f) = Nat.card ↥f.ker * Nat.card ↥N := by
  have : Finite H := Finite.of_surjective f hf
  have h1 := (N.comap f).card_mul_index
  have h2 := N.card_mul_index
  have h3 : (N.comap f).index = N.index := Subgroup.index_comap_of_surjective N hf
  have h4 : Nat.card G = Nat.card H * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  rw [h3] at h1
  have h5 : Nat.card ↥(N.comap f) * N.index = Nat.card ↥f.ker * Nat.card ↥N * N.index := by
    rw [h1, h4, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h5

theorem exists_lift_pGroup {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (R : Subgroup K) [R.Normal] (hR : Nat.Coprime (Nat.card R) p)
    (Ē : Subgroup (K ⧸ R)) (hĒ : IsPGroup p Ē) :
    ∃ E : Subgroup K, E ⊓ R = ⊥ ∧ E.map (QuotientGroup.mk' R) = Ē := by
  classical
  set G₁ : Subgroup K := Ē.comap (QuotientGroup.mk' R) with hG₁
  have hRG : R ≤ G₁ := fun x hx => by
    rw [hG₁, mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Ē.one_mem
  set N : Subgroup G₁ := R.subgroupOf G₁ with hN
  let f : G₁ →* Ē := ((QuotientGroup.mk' R).comp G₁.subtype).codRestrict Ē (fun x => x.2)
  have hfs : Function.Surjective f := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective R (e : K ⧸ R)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    rw [hG₁, mem_comap, hx]
    exact e.2
  have hfker : f.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hN, mem_subgroupOf]
    constructor
    · intro h
      have h' : QuotientGroup.mk' R (x : K) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff (x : K)).mp h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (x : K)).mpr h)
  have hNcard : Nat.card N = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv
  have hNindex : N.index = Nat.card Ē := by
    rw [← hfker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective f hfs, Subgroup.card_top]
  obtain ⟨n, hn⟩ := hĒ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hNindex, hn]
    exact Nat.Coprime.pow_right n hR
  have : N.Normal := by rw [hN]; infer_instance
  obtain ⟨H₁, hH₁⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨H₁.map G₁.subtype, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨y, hyG⟩, hyH, rfl⟩ := Subgroup.mem_map.mp hx.1
    have hyN : (⟨y, hyG⟩ : G₁) ∈ N := by
      rw [hN, mem_subgroupOf]
      exact hx.2
    have := hH₁.disjoint.le_bot ⟨hyN, hyH⟩
    rw [Subgroup.mem_bot] at this ⊢
    exact congrArg Subtype.val this
  · rw [Subgroup.map_map]
    ext e
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro he
      obtain ⟨x, hx⟩ := hfs ⟨e, he⟩
      have hxtop : x ∈ N ⊔ H₁ := by rw [hH₁.sup_eq_top]; exact mem_top x
      obtain ⟨a, ha, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxtop
      refine ⟨h, hh, ?_⟩
      have h1 : f (a * h) = f h := by
        have : f a = 1 := by rw [← MonoidHom.mem_ker, hfker]; exact ha
        rw [map_mul, this, one_mul]
      have h2 : f h = ⟨e, he⟩ := h1 ▸ hx
      exact congrArg Subtype.val h2

theorem exists_sylow_fixed {K : Type*} [Group K] [Finite K] {p : ℕ} (r : ℕ) [Fact p.Prime]
    [Fact r.Prime] {W E : Subgroup K} (hE : IsPGroup p E) (hEW : E ≤ normalizer (W : Set K))
    (hW : ¬ p ∣ Nat.card W) :
    ∃ T : Sylow r W, ∀ g ∈ E, ∀ y ∈ (T : Subgroup W).map W.subtype,
      g * y * g⁻¹ ∈ (T : Subgroup W).map W.subtype := by
  classical
  let φ : E →* MulAut W := (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hEW)
  let _inst : MulDistribMulAction E W := MulDistribMulAction.compHom W φ
  have hcard : ¬ p ∣ Nat.card (Sylow r W) := by
    intro h
    apply hW
    obtain P : Sylow r W := default
    exact h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _))
  obtain ⟨P, hP⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r W) hcard
  refine ⟨P, fun g hg y hy => ?_⟩
  obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hy
  have h1 : (⟨g, hg⟩ : E) • P = P := hP ⟨g, hg⟩
  have h2 : ((⟨g, hg⟩ : E) • x : W) ∈ ((⟨g, hg⟩ : E) • (P : Subgroup W)) :=
    Subgroup.smul_mem_pointwise_smul x _ _ hxP
  have h3 : ((⟨g, hg⟩ : E) • (P : Subgroup W)) = (P : Subgroup W) := by
    rw [← Sylow.pointwise_smul_def, h1]
  rw [h3] at h2
  exact ⟨_, h2, rfl⟩

theorem exists_lift_through_pPrime_kernel {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (R : Subgroup K) [R.Normal] (hR : Nat.Coprime (Nat.card R) p)
    {TB Ē : Subgroup (K ⧸ R)} (hT : TB ≠ ⊥) (hT2 : IsPGroup 2 TB)
    (hE : IsElementaryAbelian p Ē) (hnorm : Ē ≤ normalizer (TB : Set (K ⧸ R))) :
    ∃ T E : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ IsElementaryAbelian p E ∧
      Nat.card E = Nat.card Ē ∧ E ≤ normalizer (T : Set K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hĒp : IsPGroup p Ē := IsElementaryAbelian.isPGroup p Ē
  obtain ⟨E, hER, hEmap⟩ := exists_lift_pGroup R hR Ē hĒp
  set g : E →* K ⧸ R := (QuotientGroup.mk' R).comp E.subtype with hg
  have hgE : ∀ x : E, g x ∈ Ē := fun x => by
    rw [← hEmap]
    exact Subgroup.mem_map_of_mem _ x.2
  have hinj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxR : (x : K) ∈ R := (QuotientGroup.eq_one_iff (x : K)).mp hx
    have : (x : K) ∈ E ⊓ R := ⟨x.2, hxR⟩
    rw [hER, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hrange : g.range = Ē := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype, hEmap]
  have hEcard : Nat.card E = Nat.card Ē := by
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hEelem : IsElementaryAbelian p E := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply hinj
      rw [map_mul, map_mul]
      have := (IsMulCommutative.is_comm (M := Ē)).comm ⟨g a, hgE a⟩ ⟨g b, hgE b⟩
      exact congrArg Subtype.val this
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => ?_
      apply hinj
      rw [map_pow, map_one]
      have h1 : (⟨g a, hgE a⟩ : Ē) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p Ē) _
      exact congrArg Subtype.val h1
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  set W : Subgroup K := TB.comap (QuotientGroup.mk' R) with hW
  have hEW : E ≤ normalizer (W : Set K) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' : QuotientGroup.mk' R x ∈ normalizer (TB : Set (K ⧸ R)) :=
      hnorm (by rw [← hEmap]; exact Subgroup.mem_map_of_mem _ hx)
    have := (Subgroup.mem_normalizer_iff.mp hx') (QuotientGroup.mk' R y)
    simpa [hW] using this
  have hWcard : Nat.card W = Nat.card R * Nat.card TB := by
    rw [hW, natCard_comap_of_surjective' _ (QuotientGroup.mk'_surjective R), QuotientGroup.ker_mk']
  have hT2card : ∃ k : ℕ, Nat.card TB = 2 ^ k := hT2.exists_card_eq
  obtain ⟨k, hk⟩ := hT2card
  have hpW : ¬ p ∣ Nat.card W := by
    rw [hWcard, hk]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hR.symm h)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hT (Subgroup.eq_bot_of_card_eq _ (by rw [hk]; rfl))
  have h2W : 2 ∣ Nat.card W := by
    rw [hWcard, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk1) _
  obtain ⟨P, hP⟩ := exists_sylow_fixed 2 (p := p) hEp hEW hpW
  refine ⟨(P : Subgroup W).map W.subtype, E, ?_, ?_, hEelem, hEcard, ?_⟩
  · intro hbot
    have hP1 : (P : Subgroup W) = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp hbot
    have hc : Nat.card (P : Subgroup W) = 1 := by rw [hP1]; exact Subgroup.card_bot
    rw [P.card_eq_multiplicity] at hc
    have hfac : 0 < (Nat.card W).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2W
    have := Nat.one_lt_pow hfac.ne' Nat.one_lt_two
    omega
  · exact (P.isPGroup').map _
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hP x hx y hy
    · intro hy
      have := hP x⁻¹ (E.inv_mem hx) _ hy
      simpa [mul_assoc] using this

end CFSG.RankThree.PartOne.SRC
