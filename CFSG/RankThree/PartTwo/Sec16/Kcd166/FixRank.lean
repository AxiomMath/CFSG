module

public import CFSG.GroupTheory.CoprimeSectionStability
import CFSG.GroupTheory.SectionLemmas
public import CFSG.GroupTheory.SteinbergBWFrattini
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.RankThree.PartTwo.Sec11.SimsR1Blackburn
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank
public import CFSG.RankThree.PartTwo.KFacts.BlackburnScalar

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open Subgroup
open CFSG.RankThree.PartTwo
open scoped Pointwise commutatorElement

private lemma pow_commutatorElement_mem {G : Type*} [Group G] {N : Subgroup G} {s f : G}
    (hs : s ∈ Subgroup.normalizer (N : Set G)) (hf : ⁅s, f⁆ ∈ N) :
    ∀ k : ℕ, ⁅s ^ k, f⁆ ∈ N := by
  intro k
  induction k with
  | zero => simpa [commutatorElement_def] using N.one_mem
  | succ k ih =>
    have h1 : s * ⁅s ^ k, f⁆ * s⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hs _).mp ih
    have h2 : ⁅s ^ (k + 1), f⁆ = s * ⁅s ^ k, f⁆ * s⁻¹ * ⁅s, f⁆ := by
      rw [commutatorElement_def, pow_succ]
      group
    rw [h2]
    exact N.mul_mem h1 hf

private lemma zpow_commutatorElement_mem {G : Type*} [Group G] {N : Subgroup G} {s f : G}
    (hs : s ∈ Subgroup.normalizer (N : Set G)) (hf : ⁅s, f⁆ ∈ N) :
    ∀ k : ℤ, ⁅s ^ k, f⁆ ∈ N := by
  have hs' : s⁻¹ ∈ Subgroup.normalizer (N : Set G) := Subgroup.inv_mem _ hs
  have hf' : ⁅s⁻¹, f⁆ ∈ N := by
    have h1 : s⁻¹ * ⁅s, f⁆ * s ∈ N := by
      simpa using (Subgroup.mem_normalizer_iff.mp hs' ⁅s, f⁆).mp hf
    have h2 : ⁅s⁻¹, f⁆ = (s⁻¹ * ⁅s, f⁆ * s)⁻¹ := by
      rw [commutatorElement_def] at *
      group
    rw [h2]
    exact N.inv_mem h1
  intro k
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simpa using pow_commutatorElement_mem hs hf n
  · have h : (s : G) ^ (-(n : ℤ)) = (s⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [h]
    exact pow_commutatorElement_mem hs' hf' n

private lemma exists_gen_of_surjective {H K : Type*} [Group H] [Group K]
    (φ : H →* K) (hφ : Function.Surjective φ)
    (h : ∃ s : Finset H, s.card ≤ 3 ∧ Subgroup.closure (s : Set H) = ⊤) :
    ∃ t : Finset K, t.card ≤ 3 ∧ Subgroup.closure (t : Set K) = ⊤ := by
  classical
  obtain ⟨s, hsc, hstop⟩ := h
  refine ⟨s.image φ, Finset.card_image_le.trans hsc, ?_⟩
  have h1 : (Subgroup.closure (s : Set H)).map φ = Subgroup.closure (φ '' (s : Set H)) :=
    MonoidHom.map_closure φ _
  rw [hstop] at h1
  rw [Subgroup.map_top_of_surjective φ hφ] at h1
  have h3 : φ '' (s : Set H) = ((s.image φ : Finset K) : Set K) := by
    ext y
    simp [Finset.mem_image]
  rw [h3] at h1
  exact h1.symm

private lemma card_le_pow_three_of_group {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (h : ∃ s : Finset A, s.card ≤ 3 ∧
      Subgroup.closure (s : Set A) = ⊤) :
    Nat.card A ≤ p ^ 3 := by
  classical
  obtain ⟨s, hsc, htop⟩ := h
  haveI : Group.FG A := Group.fg_iff.mpr ⟨(s : Set A), htop, s.finite_toSet⟩
  have hgen3 : CFSG.generatorRank A ≤ 3 := by
    rw [CFSG.generatorRank_eq_group_rank]
    exact (Group.rank_le htop).trans hsc
  have hcard : Nat.card A = p ^ CFSG.generatorRank A :=
    CFSG.elementaryAbelian_card_eq_pow_generatorRank A
  exact hcard.trans_le (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hgen3)

private lemma pow_odd_mod_three {p : ℕ} (hp : p % 3 = 2) (k : ℕ) :
    p ^ (2 * k + 1) % 3 = 2 := by
  have hp2 : p ^ 2 % 3 = 1 := by
    rw [pow_two, Nat.mul_mod, hp]
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, Nat.mul_mod, ih, hp2]

private lemma mem_normalizer_of_commutator_mem {G : Type} [Group G] [Finite G]
    {F N : Subgroup G} {t : G} (hNF : N ≤ F)
    (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    t ∈ Subgroup.normalizer (F : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨f, hf, rfl⟩
    have h : t * f * t⁻¹ * f⁻¹ ∈ F := hNF (hFt f hf)
    have heq : t * f * t⁻¹ = (t * f * t⁻¹ * f⁻¹) * f := by group
    change t * f * t⁻¹ ∈ F
    rw [heq]
    exact F.mul_mem h hf
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]

private lemma conj_mem_zpowers_of_commute {G : Type} [Group G] {s t y : G}
    (h : s * t = t * s) (hy : y ∈ Subgroup.zpowers t) :
    s * y * s⁻¹ ∈ Subgroup.zpowers t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hst : s * t * s⁻¹ = t := by rw [h]; group
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [show s * t ^ k * s⁻¹ = (s * t * s⁻¹) ^ k by
        simpa using (conj_zpow (i := k) (a := s) (b := t)).symm, hst]

private lemma mem_normalizer_zpowers_of_commute {G : Type} [Group G] {s t : G}
    (h : s * t = t * s) : s ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_zpowers_of_commute h
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hs : s⁻¹ * t * s = t := by
      calc s⁻¹ * t * s = s⁻¹ * (t * s) := by group
        _ = s⁻¹ * (s * t) := by rw [← h]
        _ = t := by group
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc t ^ k = (s⁻¹ * t * s) ^ k := by rw [hs]
      _ = s⁻¹ * t ^ k * s := by
        simpa using (conj_zpow (i := k) (a := s⁻¹) (b := t))
      _ = s⁻¹ * (s * y * s⁻¹) * s := by rw [hk]
      _ = y := by group

private lemma mem_normalizer_centralizer_of_mem_normalizer {G : Type} [Group G] [Finite G]
    {T : Subgroup G} {σ : G} (hσ : σ ∈ Subgroup.normalizer (T : Set G)) :
    σ ∈ Subgroup.normalizer
      ((Subgroup.centralizer (T : Set G) : Subgroup G) : Set G) := by
  have hT : (MulAut.conj σ) '' (T : Set G) = (T : Set G) := by
    have hmap := congrArg (fun H : Subgroup G => (H : Set G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hσ)
    simpa [Subgroup.coe_map] using hmap
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · simpa [hT] using
      Subgroup.map_centralizer_le_centralizer_image (T : Set G) (MulAut.conj σ).toMonoidHom
  · rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective]

private lemma orderOf_mk_eq_prime {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {N F : Subgroup G} [hN : (N.subgroupOf F).Normal]
    [hEA : IsElementaryAbelian p (↥F ⧸ N.subgroupOf F)]
    {x : G} (hxF : x ∈ F) (hxN : x ∉ N) :
    orderOf (QuotientGroup.mk (⟨x, hxF⟩ : ↥F) : ↥F ⧸ N.subgroupOf F) = p := by
  rw [orderOf_eq_prime_iff]
  constructor
  · have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (↥F ⧸ N.subgroupOf F))
      (QuotientGroup.mk (⟨x, hxF⟩ : ↥F))
    simpa using hpow
  · intro h
    have hmem : (⟨x, hxF⟩ : ↥F) ∈ N.subgroupOf F :=
      (QuotientGroup.eq_one_iff (N := N.subgroupOf F) (x := ⟨x, hxF⟩)).mp h
    exact hxN (by simpa [Subgroup.mem_subgroupOf] using hmem)

private lemma pow_cube_of_scalar_iter {X : Type} [Group X] {ψ : X →* X} {w : ℕ} (x : X)
    (hψ : ∀ z, ψ z = z ^ w) (hψ3 : ∀ z, ψ (ψ (ψ z)) = z) :
    x ^ (w ^ 3) = x := by
  have h1 : ψ (ψ x) = (x ^ w) ^ w := by rw [hψ (ψ x), hψ x]
  have h2 : ψ (ψ (ψ x)) = ((x ^ w) ^ w) ^ w := by rw [hψ (ψ (ψ x)), h1]
  have h3 : ((x ^ w) ^ w) ^ w = x ^ (w ^ 3) := by
    rw [← pow_mul, ← pow_mul]
    ring_nf
  have h : ψ (ψ (ψ x)) = x ^ (w ^ 3) := h2.trans h3
  rw [hψ3] at h
  exact h.symm

private lemma zmod_cube_eq_one_of_pow_eq {p w : ℕ} [Fact p.Prime]
    {X : Type} [Group X] {x : X} (hxord : orderOf x = p) (hx : x ^ (w ^ 3) = x) :
    (w : ZMod p) ^ 3 = 1 := by
  have hmod : w ^ 3 ≡ 1 [MOD p] := by
    rw [← hxord]
    exact (pow_eq_pow_iff_modEq).mp (by simpa using hx)
  rw [← Nat.cast_pow]
  simpa using (ZMod.natCast_eq_natCast_iff (w ^ 3) 1 p).mpr hmod

private noncomputable def conjQuotientMap {G : Type} [Group G] {F N : Subgroup G}
    [hN : (N.subgroupOf F).Normal] {σ : G}
    (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) :
    (↥F ⧸ N.subgroupOf F) →* (↥F ⧸ N.subgroupOf F) :=
  QuotientGroup.map (N.subgroupOf F) (N.subgroupOf F)
    (F.normalizerMonoidHom ⟨σ, hσF⟩).toMonoidHom
    (by
      intro x hx
      change ((F.normalizerMonoidHom ⟨σ, hσF⟩) x) ∈ N.subgroupOf F
      rw [Subgroup.mem_subgroupOf, Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (Subgroup.mem_normalizer_iff.mp hσN (x : G)).mp
        (by simpa [Subgroup.mem_subgroupOf] using hx))

private lemma conjQuotientMap_mk {G : Type} [Group G] {F N : Subgroup G}
    [hN : (N.subgroupOf F).Normal] {σ : G}
    (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (x : ↥F) :
    conjQuotientMap hσF hσN (QuotientGroup.mk x) =
      QuotientGroup.mk ((F.normalizerMonoidHom ⟨σ, hσF⟩) x) :=
  QuotientGroup.map_mk (N.subgroupOf F) (N.subgroupOf F) _ _ x

private lemma conjQuotientMap_iterate {G : Type} [Group G] {F N : Subgroup G}
    [hN : (N.subgroupOf F).Normal] {σ : G}
    (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (hσ3 : σ ^ 3 = 1) :
    ∀ z, conjQuotientMap hσF hσN (conjQuotientMap hσF hσN
      (conjQuotientMap hσF hσN z)) = z := by
  intro z
  induction z using QuotientGroup.induction_on with
  | _ x =>
    rw [conjQuotientMap_mk, conjQuotientMap_mk, conjQuotientMap_mk]
    have hφ3 : (F.normalizerMonoidHom ⟨σ, hσF⟩)
        ((F.normalizerMonoidHom ⟨σ, hσF⟩) ((F.normalizerMonoidHom ⟨σ, hσF⟩) x)) = x := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hσ3' : σ * σ * σ = 1 := by
        simpa [pow_three'] using hσ3
      calc σ * (σ * (σ * (x : G) * σ⁻¹) * σ⁻¹) * σ⁻¹
          = (σ * σ * σ) * (x : G) * (σ * σ * σ)⁻¹ := by group
        _ = (x : G) := by rw [hσ3']; group
    rw [hφ3]

private lemma conjQuotientMap_pow {G : Type} [Group G] {F N : Subgroup G}
    [hN : (N.subgroupOf F).Normal] {σ : G}
    (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) {w : ℕ}
    (hsc : ∀ y ∈ F, σ * y * σ⁻¹ * (y ^ w)⁻¹ ∈ N) :
    ∀ z, conjQuotientMap hσF hσN z = z ^ w := by
  intro z
  induction z using QuotientGroup.induction_on with
  | _ x =>
    rw [conjQuotientMap_mk]
    change (QuotientGroup.mk' (N.subgroupOf F)) ((F.normalizerMonoidHom ⟨σ, hσF⟩) x) =
      ((QuotientGroup.mk' (N.subgroupOf F)) x) ^ w
    rw [← map_pow (QuotientGroup.mk' (N.subgroupOf F)) x w]
    change (((F.normalizerMonoidHom ⟨σ, hσF⟩) x : ↥F) : ↥F ⧸ N.subgroupOf F) =
      (((x ^ w : ↥F)) : ↥F ⧸ N.subgroupOf F)
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_pow] using
        hsc (x : G) x.2)

private lemma conjQuotientMap_fixed_eq_one {G : Type} [Group G] {M N F : Subgroup G}
    [hN : (N.subgroupOf F).Normal] {σ : G}
    (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (hFM : F ≤ M)
    (hfpf : ∀ m ∈ M, σ * m * σ⁻¹ * m⁻¹ ∈ N → m ∈ N) :
    ∀ z, conjQuotientMap hσF hσN z = z → z = 1 := by
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf F) z
  have hφx : (QuotientGroup.mk ((F.normalizerMonoidHom ⟨σ, hσF⟩) x) :
      ↥F ⧸ N.subgroupOf F) = QuotientGroup.mk x := by
    rw [← conjQuotientMap_mk hσF hσN x]
    simpa using hz
  have hmem : ((F.normalizerMonoidHom ⟨σ, hσF⟩) x : G) * (x : G)⁻¹ ∈ N := by
    have := (QuotientGroup.eq_iff_div_mem).mp hφx
    simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf] using this
  have hxN : (x : G) ∈ N :=
    hfpf (x : G) (hFM x.2)
      (by simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using hmem)
  exact (QuotientGroup.eq_one_iff (N := N.subgroupOf F) (x := x)).mpr
    (by simpa [Subgroup.mem_subgroupOf] using hxN)

private lemma scalar_cube_and_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M N F : Subgroup G} [hN : (N.subgroupOf F).Normal]
    [hEA : IsElementaryAbelian p (↥F ⧸ N.subgroupOf F)]
    {σ : G} (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (hσ3 : σ ^ 3 = 1)
    {w : ℕ} (hsc : ∀ m ∈ M, σ * m * σ⁻¹ * (m ^ w)⁻¹ ∈ N)
    (hFM : F ≤ M)
    (hfpf : ∀ m ∈ M, σ * m * σ⁻¹ * m⁻¹ ∈ N → m ∈ N)
    {x : G} (hxF : x ∈ F) (hxN : x ∉ N) :
    (w : ZMod p) ^ 3 = 1 ∧ (w : ZMod p) ≠ 1 := by
  have hscF : ∀ y ∈ F, σ * y * σ⁻¹ * (y ^ w)⁻¹ ∈ N := fun y hy => hsc y (hFM hy)
  have hψpow : ∀ z : ↥F ⧸ N.subgroupOf F, conjQuotientMap hσF hσN z = z ^ w :=
    conjQuotientMap_pow hσF hσN hscF
  have hψ3 : ∀ z : ↥F ⧸ N.subgroupOf F, conjQuotientMap hσF hσN
      (conjQuotientMap hσF hσN (conjQuotientMap hσF hσN z)) = z :=
    conjQuotientMap_iterate hσF hσN hσ3
  let xq : ↥F ⧸ N.subgroupOf F := QuotientGroup.mk (⟨x, hxF⟩ : ↥F)
  have hxq_ord : orderOf xq = p := orderOf_mk_eq_prime hxF hxN
  have hxq_pow : xq ^ (w ^ 3) = xq := pow_cube_of_scalar_iter xq hψpow hψ3
  constructor
  · exact zmod_cube_eq_one_of_pow_eq hxq_ord hxq_pow
  · intro hw1
    have hmod : w ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff w 1 p).mp (by simpa using hw1)
    have hwx : xq ^ w = xq := by
      simpa using (pow_eq_pow_iff_modEq (x := xq) (n := w) (m := 1)).mpr
        (by simpa [hxq_ord] using hmod)
    have h1 : σ * x * σ⁻¹ * (x ^ w)⁻¹ ∈ N := hsc x (hFM hxF)
    have h2 : x ^ w * x⁻¹ ∈ N := by
      have hxq_w : xq ^ w =
          QuotientGroup.mk (⟨x ^ w, F.pow_mem hxF w⟩ : ↥F) := by
        show (QuotientGroup.mk (⟨x, hxF⟩ : ↥F) : ↥F ⧸ N.subgroupOf F) ^ w = _
        exact (map_pow (QuotientGroup.mk' (N.subgroupOf F)) (⟨x, hxF⟩ : ↥F) w).symm
      have heq : (QuotientGroup.mk (⟨x ^ w, F.pow_mem hxF w⟩ : ↥F) :
          ↥F ⧸ N.subgroupOf F) = xq := hxq_w.symm.trans hwx
      have h2' : (⟨x ^ w, F.pow_mem hxF w⟩ : ↥F) / (⟨x, hxF⟩ : ↥F) ∈ N.subgroupOf F :=
        (QuotientGroup.eq_iff_div_mem).mp heq
      simpa [div_eq_mul_inv, Subgroup.mem_subgroupOf] using h2'
    have h3 : σ * x * σ⁻¹ * x⁻¹ ∈ N := by
      have := N.mul_mem h1 h2
      simpa [mul_assoc] using this
    exact hxN (hfpf x (hFM hxF) h3)


private lemma isPGroup_p_quotient {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {M N H : Subgroup G} [hC : (N.subgroupOf H).Normal]
    (hexp : ∀ x ∈ M, x ^ p ∈ N) :
    IsPGroup p (↥(M.subgroupOf H) ⧸ (N.subgroupOf H).subgroupOf (M.subgroupOf H)) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  refine ⟨1, ?_⟩
  rw [pow_one, ← map_pow (QuotientGroup.mk' _), QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  have hpow : (((x : ↥(M.subgroupOf H)) : ↥H) : G) ^ p ∈ N := hexp _ x.2
  simpa [Subgroup.mem_subgroupOf, Subgroup.coe_pow] using hpow

private lemma exists_sylow_subgroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M N H : Subgroup G} (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hMH : M ≤ H) (hHnormM : H ≤ Subgroup.normalizer (M : Set G))
    (hHnormN : H ≤ Subgroup.normalizer (N : Set G)) {t : G} (htH : t ∈ H) :
    ∃ R : Subgroup G, R ≤ M ∧ IsPGroup p R ∧ M = N ⊔ R ∧
      (⟨t, htH⟩ : ↥H) ∈ (N.subgroupOf H : Set ↥H) *
        (Subgroup.normalizer ((R.subgroupOf H) : Set ↥H) : Set ↥H) := by
  classical
  haveI hKnormal : (M.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMH).mpr hHnormM
  haveI hCnormal : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hNM.trans hMH)).mpr hHnormN
  have hCK : N.subgroupOf H ≤ M.subgroupOf H := fun x hx => hNM hx
  have hpquot : IsPGroup p (↥(M.subgroupOf H) ⧸
      (N.subgroupOf H).subgroupOf (M.subgroupOf H)) :=
    isPGroup_p_quotient (M := M) (N := N) (H := H) hexp
  let P : Sylow p ↥(M.subgroupOf H) := default
  haveI hPfin : Finite (Sylow p ↥(M.subgroupOf H)) := Sylow.finite_of_finiteIndex P
  obtain ⟨hprod, hfratt⟩ := CFSG.GroupTheory.ZJ.normal_p_quotient_frattini
    (G := ↥H) (C := N.subgroupOf H) (H := M.subgroupOf H) (p := p) hCK hpquot P
  set R' : Subgroup ↥H := (P : Subgroup (M.subgroupOf H)).map (M.subgroupOf H).subtype with hR'def
  set R : Subgroup G := R'.map H.subtype with hRdef
  have hR'M : R' ≤ M.subgroupOf H := Subgroup.map_subtype_le _
  have hRM : R ≤ M := by
    rw [hRdef]
    calc R'.map H.subtype ≤ (M.subgroupOf H).map H.subtype := Subgroup.map_mono hR'M
      _ = M := Subgroup.map_subgroupOf_eq_of_le hMH
  have hR2 : IsPGroup p R := by
    rw [hRdef, hR'def]
    exact (P.isPGroup'.map (M.subgroupOf H).subtype).map H.subtype
  have hK_eq : (M.subgroupOf H) = (N.subgroupOf H) ⊔ R' := by
    refine le_antisymm ?_ (sup_le hCK hR'M)
    intro x hx
    have hx' : x ∈ ((N.subgroupOf H : Subgroup ↥H) : Set ↥H) * (R' : Set ↥H) := by
      rw [← hprod]
      exact hx
    obtain ⟨c, hc, r, hr, rfl⟩ := hx'
    exact Subgroup.mul_mem_sup hc hr
  have hM_eq : M = N ⊔ R := by
    have h1 : (M.subgroupOf H).map H.subtype =
        (N.subgroupOf H).map H.subtype ⊔ R'.map H.subtype := by
      rw [hK_eq, Subgroup.map_sup]
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at h1
    rw [inf_eq_left.mpr hMH, inf_eq_left.mpr (hNM.trans hMH)] at h1
    exact h1
  refine ⟨R, hRM, hR2, hM_eq, ?_⟩
  have hsub : (R.subgroupOf H) = R' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective R'
  rw [hsub, hfratt]
  exact Set.mem_univ _

private lemma commutatorElement_inv_mul_mem {G : Type} [Group G] {M N F : Subgroup G} {t c : G}
    (hNM : N ≤ M) (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hcN : c ∈ N)
    (htM : t ∈ Subgroup.normalizer (M : Set G)) (hFM : F ≤ M)
    (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    ∀ f ∈ F, ⁅c⁻¹ * t, f⁆ ∈ N := by
  intro f hf
  have hcM : c ∈ M := hNM hcN
  have huM : t * f * t⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp htM f).mp (hFM hf)
  have h1 : c⁻¹ * (t * f * t⁻¹) * c * (t * f * t⁻¹)⁻¹ ∈ N := by
    simpa using hab c⁻¹ (M.inv_mem hcM) (t * f * t⁻¹) huM
  have h2 : t * f * t⁻¹ * f⁻¹ ∈ N := hFt f hf
  have h3 : ⁅c⁻¹ * t, f⁆ = (c⁻¹ * (t * f * t⁻¹) * c * (t * f * t⁻¹)⁻¹) *
      (t * f * t⁻¹ * f⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [h3]
  exact N.mul_mem h1 h2

private lemma exists_normalizing_elem {G : Type} [Group G] {M N R H : Subgroup G} {t : G}
    (htH : t ∈ H)
    (hfratt : (⟨t, htH⟩ : ↥H) ∈ (N.subgroupOf H : Set ↥H) *
      (Subgroup.normalizer ((R.subgroupOf H) : Set ↥H) : Set ↥H))
    (hRH : R ≤ H) (hNM : N ≤ M)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N)
    (htM : t ∈ Subgroup.normalizer (M : Set G))
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (htnM : t ∉ M)
    {F : Subgroup G} (hFM : F ≤ M) (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    ∃ s : G, s ∈ H ∧ s ∈ Subgroup.normalizer (M : Set G) ∧
      s ∈ Subgroup.normalizer (N : Set G) ∧ s ∈ Subgroup.normalizer (R : Set G) ∧
      s ∉ M ∧ (∀ f ∈ F, ⁅s, f⁆ ∈ N) := by
  classical
  rw [Set.mem_mul] at hfratt
  obtain ⟨c, hc, y, hy, hcy⟩ := hfratt
  set s : G := (y : G) with hsdef
  have hsH : s ∈ H := y.2
  have hst : (c : G) * s = t := by
    have h := congrArg (fun z : ↥H => (z : G)) hcy
    simpa [s, Subgroup.coe_mul] using h
  have hs_eq : s = (c : G)⁻¹ * t := by rw [← hst]; group
  have hcN : (c : G) ∈ N := hc
  have hsN : s ∈ Subgroup.normalizer (N : Set G) := by
    rw [hs_eq]
    exact (Subgroup.normalizer (N : Set G)).mul_mem
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hcN)) htN
  have hsM : s ∈ Subgroup.normalizer (M : Set G) := by
    rw [hs_eq]
    exact (Subgroup.normalizer (M : Set G)).mul_mem
      (Subgroup.inv_mem _ (Subgroup.le_normalizer (hNM hcN))) htM
  have hsR : s ∈ Subgroup.normalizer (R : Set G) := by
    have h2 : (Subgroup.normalizer (R : Set G)).subgroupOf H =
        Subgroup.normalizer ((R.subgroupOf H) : Set ↥H) :=
      Subgroup.subgroupOf_normalizer_eq (H := R) (N := H) hRH
    rw [← h2] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  have hs_notM : s ∉ M := by
    intro hsMmem
    have h := M.mul_mem (hNM hcN) hsMmem
    rw [hst] at h
    exact htnM h
  have hsf : ∀ f ∈ F, ⁅s, f⁆ ∈ N := by
    rw [hs_eq]
    exact commutatorElement_inv_mul_mem hNM hab hcN htM hFM hFt
  exact ⟨s, hsH, hsM, hsN, hsR, hs_notM, hsf⟩

private lemma isPGroup_two_quotient {G : Type} [Group G] {M H : Subgroup G}
    [hK : (M.subgroupOf H).Normal] {t : G}
    (htH : t ∈ H) (htM : t ∈ Subgroup.normalizer (M : Set G))
    (hHnormM : H ≤ Subgroup.normalizer (M : Set G))
    (hH_eq : H = M ⊔ Subgroup.zpowers t) (ht2 : IsPGroup 2 (Subgroup.zpowers t)) :
    IsPGroup 2 (↥H ⧸ M.subgroupOf H) := by
  let φ : ↥(Subgroup.zpowers t) →* (↥H ⧸ M.subgroupOf H) :=
    (QuotientGroup.mk' (M.subgroupOf H)).comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr htH))
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (M.subgroupOf H) z
    have hxH : (x : G) ∈ (M : Set G) * (Subgroup.zpowers t : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left M (Subgroup.zpowers t)
        (Subgroup.zpowers_le.mpr htM), ← hH_eq]
      exact x.2
    obtain ⟨a, ha, b, hb, hx⟩ := hxH
    have hbH : b ∈ H := Subgroup.zpowers_le.mpr htH hb
    refine ⟨⟨b, hb⟩, ?_⟩
    show (QuotientGroup.mk ⟨b, hbH⟩ : ↥H ⧸ M.subgroupOf H) =
      (QuotientGroup.mk x : ↥H ⧸ M.subgroupOf H)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (((⟨b, hbH⟩ : ↥H)⁻¹ * x : ↥H) : G) = (b : G)⁻¹ * (x : G) := by simp
    have hx' : (x : G) = (a : G) * (b : G) := hx.symm
    rw [h1, hx']
    have h2 : (b : G)⁻¹ * ((a : G) * (b : G)) = (b : G)⁻¹ * (a : G) * (b : G) := by
      group
    rw [h2]
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hHnormM hbH)) a).mp ha
  exact IsPGroup.of_surjective ht2 φ hφ

private lemma exists_two_part {G : Type} [Group G] [Finite G] {M N R H : Subgroup G}
    [hK : (M.subgroupOf H).Normal] {s : G} (hsH : s ∈ H)
    (hsN : s ∈ Subgroup.normalizer (N : Set G))
    (hsR : s ∈ Subgroup.normalizer (R : Set G)) (hs_notM : s ∉ M)
    (hHq2 : IsPGroup 2 (↥H ⧸ M.subgroupOf H)) {F : Subgroup G}
    (hsf : ∀ f ∈ F, ⁅s, f⁆ ∈ N) :
    ∃ (s2 : G) (k : ℕ), 1 ≤ k ∧ orderOf s2 = 2 ^ k ∧
      IsPGroup 2 (Subgroup.zpowers s2) ∧ s2 ≠ 1 ∧
      s2 ∈ Subgroup.normalizer (N : Set G) ∧ s2 ∈ Subgroup.normalizer (R : Set G) ∧
      (∀ f ∈ F, ⁅s2, f⁆ ∈ N) := by
  classical
  have hEven : ¬ Odd (orderOf s) := by
    intro hodd
    have hmem : (⟨s, hsH⟩ : ↥H) ∈ M.subgroupOf H :=
      CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_isPGroup_quotient (M.subgroupOf H) hHq2
        (by simpa using hodd)
    exact hs_notM hmem
  obtain ⟨k, m, hm_odd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact absurd (by rw [hord, hk, pow_zero, one_mul]; exact hm_odd) hEven
    · exact hk
  set s2 : G := s ^ m with hs2def
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hs2ord : orderOf s2 = 2 ^ k := by
    rw [hs2def, orderOf_pow, hord,
      Nat.gcd_eq_right (show m ∣ 2 ^ k * m from ⟨2 ^ k, by rw [mul_comm]⟩)]
    rw [Nat.mul_comm (2 ^ k) m]
    exact Nat.mul_div_cancel_left (2 ^ k) (Nat.pos_of_ne_zero hm0)
  have hs2_ne : s2 ≠ 1 := by
    intro h
    have h1 : orderOf s2 = 1 := by rw [h]; simp
    rw [hs2ord] at h1
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  have hs2P : IsPGroup 2 (Subgroup.zpowers s2) := by
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hs2ord]
  have hs2N : s2 ∈ Subgroup.normalizer (N : Set G) := by
    rw [hs2def]
    exact Subgroup.pow_mem _ hsN m
  have hs2R : s2 ∈ Subgroup.normalizer (R : Set G) := by
    rw [hs2def]
    exact Subgroup.pow_mem _ hsR m
  have hs2f : ∀ f ∈ F, ⁅s2, f⁆ ∈ N := by
    intro f hf
    rw [hs2def]
    exact pow_commutatorElement_mem hsN (hsf f hf) m
  exact ⟨s2, k, hk1, hs2ord, hs2P, hs2_ne, hs2N, hs2R, hs2f⟩

theorem le_inf_centralizer_sup_of_coprime {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M N R F : Subgroup G} {s2 : G} (hNM : N ≤ M)
    (hNn : (N.subgroupOf M).Normal) (hM_eq : M = N ⊔ R) (hR2 : IsPGroup p R)
    (hs2R : s2 ∈ Subgroup.normalizer (R : Set G))
    (hs2N : s2 ∈ Subgroup.normalizer (N : Set G))
    (hs2f : ∀ f ∈ F, ⁅s2, f⁆ ∈ N) (hFM : F ≤ M)
    (hcop : Nat.Coprime (Nat.card (Subgroup.zpowers s2)) (Nat.card R)) :
    F ≤ (R ⊓ Subgroup.centralizer (Subgroup.zpowers s2 : Set G)) ⊔ N := by
  have hRM : R ≤ M := by rw [hM_eq]; exact le_sup_right
  have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNn
  have hRnorm : R ≤ Subgroup.normalizer ((R ⊓ N) : Set G) := by
    intro r hr
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hr, hMnormN (hRM hr)⟩
  have hs2_inf : s2 ∈ Subgroup.normalizer ((R ⊓ N) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hs2R, hs2N⟩
  have hsolv : Group.IsSolvable ↥R := by
    haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
    infer_instance
  intro f hf
  have hfM : f ∈ M := hFM hf
  have hNnormR : R ≤ Subgroup.normalizer (N : Set G) := fun r hr => hMnormN (hRM hr)
  have hf' : f ∈ (N : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N R hNnormR, ← hM_eq]
    exact hfM
  obtain ⟨n, hn, r, hr, hrn⟩ := hf'
  have key : ⁅s2, r⁆ ∈ R ⊓ N := by
    have hA : s2 * n * s2⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hs2N n).mp hn
    have h2 : (s2 * n * s2⁻¹)⁻¹ * ⁅s2, f⁆ * n ∈ N :=
      N.mul_mem (N.mul_mem (N.inv_mem hA) (hs2f f hf)) hn
    have heq : ⁅s2, r⁆ = (s2 * n * s2⁻¹)⁻¹ * ⁅s2, f⁆ * n := by
      rw [commutatorElement_def] at *
      rw [← hrn]
      group
    refine ⟨?_, ?_⟩
    · exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp hs2R r).mp hr) (R.inv_mem hr)
    · rw [heq]
      exact h2
  have hfix : r ∈ (R ⊓ Subgroup.centralizer (Subgroup.zpowers s2 : Set G)) ⊔ (R ⊓ N) := by
    refine (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff (D := Subgroup.zpowers s2)
      (N := R) (M := R ⊓ N) inf_le_left hRnorm (Subgroup.zpowers_le.mpr hs2R)
      (Subgroup.zpowers_le.mpr hs2_inf) hcop hsolv hr).mp ?_
    intro d hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact zpow_commutatorElement_mem hs2_inf key j
  have hle : (R ⊓ Subgroup.centralizer (Subgroup.zpowers s2 : Set G)) ⊔ (R ⊓ N) ≤
      (R ⊓ Subgroup.centralizer (Subgroup.zpowers s2 : Set G)) ⊔ N :=
    sup_le le_sup_left (inf_le_right.trans le_sup_right)
  rw [← hrn]
  exact ((R ⊓ Subgroup.centralizer (Subgroup.zpowers s2 : Set G)) ⊔ N).mul_mem
    (Subgroup.mem_sup_right hn) (hle hfix)

private lemma elemAbelian_card_le_sq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {Q : Subgroup G} {s2 : G} (hs2P : IsPGroup 2 (Subgroup.zpowers s2)) (hs2_ne : s2 ≠ 1)
    (hQnorm : Q ≤ Subgroup.normalizer (Subgroup.zpowers s2 : Set G)) :
    ∀ E : Subgroup ↥Q, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2 := by
  intro E hE
  have hE' : CFSG.Open.IsElemAbelian p (E.map Q.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE Q.subtype
  have hcard : Nat.card (E.map Q.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective Q.subtype_injective
  rw [← hcard]
  exact hloc (Subgroup.zpowers s2) (E.map Q.subtype)
    (fun hbot => hs2_ne (Subgroup.zpowers_eq_bot.mp hbot)) hs2P
    (le_trans (Subgroup.map_subtype_le E) hQnorm) hE'.1 hE'.2

private lemma exists_three_generators {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {Q : Subgroup G} (hQp : IsPGroup p ↥Q) {s2 : G}
    (hs2P : IsPGroup 2 (Subgroup.zpowers s2)) (hs2_ne : s2 ≠ 1)
    (hQnorm : Q ≤ Subgroup.normalizer (Subgroup.zpowers s2 : Set G)) :
    ∃ s : Finset ↥Q, s.card ≤ 3 ∧ Subgroup.closure (s : Set ↥Q) = ⊤ :=
  (CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn.blackburnRankTwo_holds (p := p) hp5 ↥Q hQp
    (elemAbelian_card_le_sq hloc hs2P hs2_ne hQnorm)).1

private lemma isElementaryAbelian_map {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {M N Q : Subgroup G} [hN : (N.subgroupOf M).Normal]
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hQM : Q ≤ M) :
    IsElementaryAbelian p ↥((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) := by
  haveI hMbar : IsMulCommutative (↥M ⧸ N.subgroupOf M) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, _root_.commutator_def,
      Subgroup.commutator_le]
    rintro x - y -
    have h := hab (x : G) x.2 (y : G) y.2
    simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using h
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
    exact mul_comm' (a : ↥M ⧸ N.subgroupOf M) (b : ↥M ⧸ N.subgroupOf M)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun z => ?_
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp z.2
    refine Subtype.ext ?_
    show ((z : ↥M ⧸ N.subgroupOf M)) ^ p = 1
    have hz : (z : ↥M ⧸ N.subgroupOf M) = (QuotientGroup.mk' (N.subgroupOf M)) x := hxeq.symm
    rw [hz, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact hexp (x : G) x.2)

private lemma card_map_le_pow_three {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M N Q : Subgroup G} [hN : (N.subgroupOf M).Normal]
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hQM : Q ≤ M) (hgen : ∃ s : Finset ↥Q, s.card ≤ 3 ∧
      Subgroup.closure (s : Set ↥Q) = ⊤) :
    Nat.card ↥((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) ≤ p ^ 3 := by
  haveI hQea : IsElementaryAbelian p
      ↥((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) :=
    isElementaryAbelian_map hab hexp hQM
  let π : ↥Q →* (↥M ⧸ N.subgroupOf M) :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hQM)
  have hπ : ∀ z : ↥Q, π z ∈ (Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) := by
    intro z
    exact Subgroup.mem_map.mpr ⟨⟨(z : G), hQM z.2⟩, Subgroup.mem_subgroupOf.mpr z.2, rfl⟩
  let ψ : ↥Q →* ↥((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) :=
    π.codRestrict _ hπ
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp z.2
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    exact Subtype.ext (by
      show (QuotientGroup.mk' (N.subgroupOf M))
        (Subgroup.inclusion hQM ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩) = (z : _)
      have h1 : ((Subgroup.inclusion hQM ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩ : ↥M)) = x :=
        Subtype.ext rfl
      rw [h1]
      exact hxeq)
  obtain ⟨t, htc, htstop⟩ := exists_gen_of_surjective ψ hψ hgen
  exact card_le_pow_three_of_group ⟨t, htc, htstop⟩

private lemma map_subgroupOf_le_map_of_le_sup {G : Type} [Group G] {M N F Q : Subgroup G}
    [hN : (N.subgroupOf M).Normal] (hNM : N ≤ M) (hQM : Q ≤ M) (hFM : F ≤ M)
    (hFQN : F ≤ Q ⊔ N) :
    (F.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) ≤
      (Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) := by
  rintro y ⟨x, hx, rfl⟩
  have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.mp hx
  have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hN
  have hQnormN : Q ≤ Subgroup.normalizer (N : Set G) := fun q hq => hMnormN (hQM hq)
  have hqmem : (x : G) ∈ (Q : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Q N hQnormN]
    exact hFQN hxF
  obtain ⟨q, hq, n, hn, hqn⟩ := hqmem
  refine ⟨⟨(q : G), hQM hq⟩, Subgroup.mem_subgroupOf.mpr hq, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  have h1 : ((((⟨(q : G), hQM hq⟩ : ↥M))⁻¹ * x : ↥M) : G) = (q : G)⁻¹ * (x : G) := by
    simp
  rw [h1, ← hqn]
  simpa using hn

private lemma relIndex_le_pow_three_of_le_sup {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M N F Q : Subgroup G} (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hQM : Q ≤ M) (hFM : F ≤ M) (hFQN : F ≤ Q ⊔ N)
    (hgen : ∃ s : Finset ↥Q, s.card ≤ 3 ∧ Subgroup.closure (s : Set ↥Q) = ⊤) :
    N.relIndex F ≤ p ^ 3 := by
  haveI hN : (N.subgroupOf M).Normal := hNn
  have hAbound := card_map_le_pow_three (Q := Q) hab hexp hQM hgen
  have hle := map_subgroupOf_le_map_of_le_sup hNM hQM hFM hFQN
  rw [← Subgroup.relIndex_subgroupOf hFM]
  conv_lhs => rw [← QuotientGroup.ker_mk' (N.subgroupOf M)]
  rw [Subgroup.relIndex_ker]
  exact (Subgroup.card_le_of_le hle).trans hAbound

private lemma relIndex_le_pow_three_aux {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {M N : Subgroup G} (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    {t : G} (ht2 : IsPGroup 2 (Subgroup.zpowers t))
    (htM : t ∈ Subgroup.normalizer (M : Set G))
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (htnM : t ∉ M)
    {H : Subgroup G} (hMH : M ≤ H) (hH_eq : H = M ⊔ Subgroup.zpowers t)
    (hHnormM : H ≤ Subgroup.normalizer (M : Set G))
    (hHnormN : H ≤ Subgroup.normalizer (N : Set G)) (htH : t ∈ H)
    {F : Subgroup G} (hNF : N ≤ F) (hFM : F ≤ M) (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    N.relIndex F ≤ p ^ 3 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hKnormal : (M.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMH).mpr hHnormM
  obtain ⟨R, hRM, hR2, hM_eq, hfratt⟩ :=
    exists_sylow_subgroup hNM hNn hexp hMH hHnormM hHnormN htH
  obtain ⟨s, hsH, hsM, hsN, hsR, hs_notM, hsf⟩ :=
    exists_normalizing_elem htH hfratt (hRM.trans hMH) hNM hab htM htN htnM hFM hFt
  have hHq2 : IsPGroup 2 (↥H ⧸ M.subgroupOf H) :=
    isPGroup_two_quotient htH htM hHnormM hH_eq ht2
  obtain ⟨s2, k, hk1, hs2ord, hs2P, hs2_ne, hs2N, hs2R, hs2f⟩ :=
    exists_two_part hsH hsN hsR hs_notM hHq2 hsf
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers s2)) (Nat.card R) := by
    obtain ⟨b, hb⟩ := hR2.exists_card_eq
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    rw [Nat.card_zpowers, hs2ord, hb]
    exact Nat.Coprime.pow k b (Nat.coprime_two_left.mpr hpodd)
  set Q : Subgroup G := R ⊓ Subgroup.centralizer (Subgroup.zpowers s2 : Set G) with hQdef
  have hQM : Q ≤ M := inf_le_left.trans hRM
  have hQp : IsPGroup p ↥Q := hR2.to_le inf_le_left
  have hQnorm : Q ≤ Subgroup.normalizer (Subgroup.zpowers s2 : Set G) :=
    le_trans inf_le_right (Subgroup.centralizer_le_normalizer _)
  obtain ⟨u, huc, hustop⟩ := exists_three_generators hp5 hloc hQp hs2P hs2_ne hQnorm
  refine relIndex_le_pow_three_of_le_sup hNM hNn hab hexp hQM hFM ?_ ⟨u, huc, hustop⟩
  exact le_inf_centralizer_sup_of_coprime hNM hNn hM_eq hR2 hs2R hs2N hs2f hFM hcop

theorem relIndex_le_pow_three_of_not_mem {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {M N : Subgroup G} (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    {t : G} (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (htM : t ∈ Subgroup.normalizer (M : Set G))
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (htnM : t ∉ M)
    {F : Subgroup G} (hNF : N ≤ F) (hFM : F ≤ M) (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    N.relIndex F ≤ p ^ 3 := by
  classical
  have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNn
  exact relIndex_le_pow_three_aux hp5 hloc hNM hNn hab hexp ht2 htM htN htnM
    (H := M ⊔ Subgroup.zpowers t) le_sup_left rfl
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htM))
    (sup_le hMnormN (Subgroup.zpowers_le.mpr htN))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) hNF hFM hFt

theorem relIndex_le_pow_three {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {M N : Subgroup G} (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    {t : G} (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (htM : t ∈ Subgroup.normalizer (M : Set G))
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (htnt : ∃ m ∈ M, t * m * t⁻¹ * m⁻¹ ∉ N)
    {F : Subgroup G} (hNF : N ≤ F) (hFM : F ≤ M) (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    N.relIndex F ≤ p ^ 3 := by
  refine relIndex_le_pow_three_of_not_mem hp5 hloc hNM hNn hab hexp ht2 htM htN ?_ hNF hFM hFt
  intro htM'
  obtain ⟨m, hm, hnm⟩ := htnt
  exact hnm (hab t htM' m hm)

theorem card_le_sq_of_localRank_lt {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hrk : CFSG.Assembly.RankThreeEven.localRank p G < 3) :
    ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro S E hS hS2 hEN hEc hEp
  haveI hEea : IsElementaryAbelian p ↥E :=
    { toIsMulCommutative := hEc
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => by
        apply Subtype.ext
        simpa using hEp x x.2 }
  have hcard : Nat.card E = p ^ CFSG.generatorRank ↥E :=
    CFSG.elementaryAbelian_card_eq_pow_generatorRank ↥E
  have hle : CFSG.generatorRank ↥E ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
    CFSG.RankThree.PartOne.Sec9Excl.le_localRank_of_normalizes hp.one_lt hS hS2 hEc hEp hcard hEN
  have h2 : CFSG.generatorRank ↥E ≤ 2 := by omega
  calc Nat.card E = p ^ CFSG.generatorRank ↥E := hcard
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos h2

theorem card_le_sq_subgroup {G : Type} [Group G] {p : ℕ}
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2) (X : Subgroup G) :
    ∀ S E : Subgroup X, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set X) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2 := by
  intro S E hS hS2 hEN hEc hEp
  have hSmap : S.map X.subtype ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff] at h
    exact hS (le_bot_iff.mp (by simpa using h))
  have hEN' : E.map X.subtype ≤
      Subgroup.normalizer (S.map X.subtype : Set G) :=
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map (H := S) X.subtype)
  have hEc' : IsMulCommutative (E.map X.subtype) := Subgroup.map_isMulCommutative E X.subtype
  have hEp' : ∀ e ∈ E.map X.subtype, e ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    simp [hEp x hx]
  have hcard : Nat.card (E.map X.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [← hcard]
  exact hloc (S.map X.subtype) (E.map X.subtype) hSmap (hS2.map X.subtype) hEN' hEc' hEp'

private lemma index_subgroupOf_eq_pow_three {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M N F Q : Subgroup G} (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hQM : Q ≤ M) (hFM : F ≤ M) (hFQN : F ≤ Q ⊔ N)
    (hgen : ∃ s : Finset ↥Q, s.card ≤ 3 ∧ Subgroup.closure (s : Set ↥Q) = ⊤)
    (hrel3 : N.relIndex F = p ^ 3) :
    (N.subgroupOf Q).index = p ^ 3 := by
  haveI hN : (N.subgroupOf M).Normal := hNn
  have hcontain := map_subgroupOf_le_map_of_le_sup hNM hQM hFM hFQN
  have hupper : Nat.card ((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) ≤ p ^ 3 :=
    card_map_le_pow_three (Q := Q) hab hexp hQM hgen
  have hlower : p ^ 3 ≤
      Nat.card ((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) := by
    calc p ^ 3 = N.relIndex F := hrel3.symm
      _ = Nat.card ((F.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) := by
          rw [← Subgroup.relIndex_subgroupOf hFM]
          conv_lhs => rw [← QuotientGroup.ker_mk' (N.subgroupOf M)]
          rw [Subgroup.relIndex_ker]
      _ ≤ Nat.card ((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) :=
          Subgroup.card_le_of_le hcontain
  have hW : Nat.card ((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) = p ^ 3 :=
    le_antisymm hupper hlower
  change N.relIndex Q = p ^ 3
  rw [← Subgroup.relIndex_subgroupOf hQM]
  conv_lhs => rw [← QuotientGroup.ker_mk' (N.subgroupOf M)]
  rw [Subgroup.relIndex_ker]
  exact hW

private lemma frattini_eq_subgroupOf_of_card {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M N Q : Subgroup G} (hp5 : 5 ≤ p) (hNM : N ≤ M)
    (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    (hQp : IsPGroup p ↥Q) (hQM : Q ≤ M) (hKrel : (N.subgroupOf Q).index = p ^ 3)
    (hgen : ∃ s : Finset ↥Q, s.card ≤ 3 ∧ Subgroup.closure (s : Set ↥Q) = ⊤) :
    frattini ↥Q = N.subgroupOf Q := by
  haveI : Fact (IsPGroup p ↥Q) := ⟨hQp⟩
  haveI hKnormal : (N.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hQM.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNn))
  have hfr_le_K : frattini ↥Q ≤ N.subgroupOf Q := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
    refine (Subgroup.closure_le (N.subgroupOf Q)).mpr ?_
    rintro y (hy | hy)
    · have hcomm : _root_.commutator ↥Q ≤ N.subgroupOf Q := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        rintro x - z -
        rw [Subgroup.mem_subgroupOf]
        simpa [commutatorElement_def] using hab (x : G) (hQM x.2) (z : G) (hQM z.2)
      exact hcomm hy
    · obtain ⟨x, rfl⟩ := hy
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hexp (x : G) (hQM x.2))
  have hgenΦ : ∃ s : Finset (↥Q ⧸ frattini ↥Q), s.card ≤ 3 ∧
      Subgroup.closure (s : Set (↥Q ⧸ frattini ↥Q)) = ⊤ :=
    exists_gen_of_surjective (QuotientGroup.mk' (frattini ↥Q))
      (QuotientGroup.mk'_surjective _) hgen
  haveI hEAΦ : IsElementaryAbelian p (↥Q ⧸ frattini ↥Q) :=
    CFSG.isElementaryAbelian_quotient_frattini (R := ↥Q) (p := p)
  have hΦindex_le : (frattini ↥Q).index ≤ p ^ 3 := by
    have hcard := card_le_pow_three_of_group (p := p) hgenΦ
    simpa [Subgroup.index_eq_card] using hcard
  have hKleΦ : (N.subgroupOf Q).index ≤ (frattini ↥Q).index :=
    Subgroup.index_antitone hfr_le_K
  have hΦindex_eq : (frattini ↥Q).index = (N.subgroupOf Q).index :=
    le_antisymm (by rwa [hKrel]) hKleΦ
  haveI : (N.subgroupOf Q).FiniteIndex := Subgroup.finiteIndex_of_finite
  exact Subgroup.eq_of_index_dvd_index hfr_le_K (by rw [hΦindex_eq])

private lemma frattini_condition_of_scalar {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {M N Q : Subgroup G} [hNQ : (N.subgroupOf Q).Normal] (hQM : Q ≤ M) {σ : G}
    (hσQ : σ ∈ Subgroup.normalizer (Q : Set G)) {w : ℕ}
    (hsc : ∀ m ∈ M, σ * m * σ⁻¹ * (m ^ w)⁻¹ ∈ N)
    (hΦeqK : frattini ↥Q = N.subgroupOf Q) :
    ∀ x : ↥Q, (Q.normalizerMonoidHom ⟨σ, hσQ⟩ x)⁻¹ * x ^ w ∈ frattini ↥Q := by
  intro x
  have huQ : σ * (x : G) * σ⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hσQ (x : G)).mp x.2
  have hvQ : (x : G) ^ w ∈ Q := Q.pow_mem x.2 w
  have h1 : σ * (x : G) * σ⁻¹ * ((x : G) ^ w)⁻¹ ∈ N := hsc (x : G) (hQM x.2)
  have hk : (⟨σ * (x : G) * σ⁻¹, huQ⟩ : ↥Q) *
      (⟨(x : G) ^ w, hvQ⟩ : ↥Q)⁻¹ ∈ N.subgroupOf Q :=
    Subgroup.mem_subgroupOf.mpr (by simpa using h1)
  have hconj : (⟨σ * (x : G) * σ⁻¹, huQ⟩ : ↥Q)⁻¹ *
      ⟨(x : G) ^ w, hvQ⟩ ∈ N.subgroupOf Q := by
    have h := hNQ.conj_mem
      ((⟨σ * (x : G) * σ⁻¹, huQ⟩ : ↥Q) * (⟨(x : G) ^ w, hvQ⟩ : ↥Q)⁻¹)⁻¹
      (Subgroup.inv_mem _ hk) (⟨σ * (x : G) * σ⁻¹, huQ⟩ : ↥Q)⁻¹
    convert h using 1
    group
  rw [hΦeqK]
  have hx1 : Q.normalizerMonoidHom ⟨σ, hσQ⟩ x = ⟨σ * (x : G) * σ⁻¹, huQ⟩ :=
    Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨σ, hσQ⟩ x)
  have hx2 : x ^ w = (⟨(x : G) ^ w, hvQ⟩ : ↥Q) := rfl
  rw [hx1, hx2]
  exact hconj

private lemma relIndex_ne_pow_three_of_mod_two {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p % 3 = 2) {M N F : Subgroup G}
    [hN : (N.subgroupOf F).Normal] {σ : G}
    (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (hσ3 : σ ^ 3 = 1) (hFM : F ≤ M)
    (hfpf : ∀ m ∈ M, σ * m * σ⁻¹ * m⁻¹ ∈ N → m ∈ N)
    (hrel3 : N.relIndex F = p ^ 3) : False := by
  classical
  let X := ↥F ⧸ N.subgroupOf F
  haveI : Fintype X := Fintype.ofFinite X
  let ψ : X →* X := conjQuotientMap hσF hσN
  let f : Function.End X := fun z => ψ z
  haveI : Fintype (Function.fixedPoints f) := Fintype.ofFinite _
  have hf3 : f ^ 3 = 1 := by
    funext z
    change ψ (ψ (ψ z)) = z
    exact conjQuotientMap_iterate hσF hσN hσ3 z
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · change f 1 = 1
      simp [f, ψ]
    · rintro ⟨z, hz⟩
      apply Subtype.ext
      have hz' : (conjQuotientMap hσF hσN) z = z := Function.IsFixedPt.eq hz
      exact conjQuotientMap_fixed_eq_one hσF hσN hFM hfpf z hz'
  have hcardX : Fintype.card X = p ^ 3 := by
    change Fintype.card (↥F ⧸ N.subgroupOf F) = p ^ 3
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card (N.subgroupOf F)]
    exact hrel3
  have hfixFilter :
      (Finset.filter (fun z => z ∈ Function.fixedPoints f) Finset.univ).card = 1 := by
    rw [← Fintype.card_subtype]
    exact hfix
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := f) hf3
  have hmodFilter : Fintype.card X ≡
      (Finset.filter (fun z => z ∈ Function.fixedPoints f) Finset.univ).card [MOD 3] := by
    simpa using hmod
  rw [hfixFilter] at hmodFilter
  have hmod2 : p ^ 3 ≡ 1 [MOD 3] := by
    simpa [hcardX] using hmodFilter
  have h3 : p ^ 3 % 3 = 2 := by simpa using pow_odd_mod_three hp3 1
  have hmod3 : p ^ 3 % 3 = 1 % 3 := hmod2
  rw [h3] at hmod3
  norm_num at hmod3


private lemma exists_Q_data {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {M N : Subgroup G} (hMp : IsPGroup p M) (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    {t : G} (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (N : Set G))
    {F : Subgroup G} (hNF : N ≤ F) (hFM : F ≤ M)
    (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    ∃ Q : Subgroup G, Q = F ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) ∧
      Q ≤ M ∧ IsPGroup p ↥Q ∧
      Q ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) ∧
      (∃ s : Finset ↥Q, s.card ≤ 3 ∧ Subgroup.closure (s : Set ↥Q) = ⊤) ∧
      F ≤ Q ⊔ N := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNn
  have hNnF : (N.subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hFM.trans hMnormN)
  haveI hNnF' : (N.subgroupOf F).Normal := hNnF
  let Q : Subgroup G := F ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)
  have hQM : Q ≤ M := inf_le_left.trans hFM
  have hQp : IsPGroup p ↥Q := hMp.to_le hQM
  have hQnorm : Q ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) :=
    le_trans inf_le_right (Subgroup.centralizer_le_normalizer _)
  obtain ⟨u, huc, hustop⟩ := exists_three_generators hp5 hloc hQp ht2 ht1 hQnorm
  have htF : t ∈ Subgroup.normalizer (F : Set G) :=
    mem_normalizer_of_commutator_mem hNF hFt
  have hFp : IsPGroup p F := hMp.to_le hFM
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card F) := by
    obtain ⟨a, ha⟩ := ht2.exists_card_eq
    obtain ⟨b, hb⟩ := hFp.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b (Nat.coprime_two_left.mpr hpodd)
  have hFQN : F ≤ Q ⊔ N := by
    have h := le_inf_centralizer_sup_of_coprime hNF hNnF (sup_eq_right.mpr hNF).symm hFp
      htF htN hFt le_rfl hcop
    simpa [Q] using h
  exact ⟨Q, rfl, hQM, hQp, hQnorm, ⟨u, huc, hustop⟩, hFQN⟩

private lemma relIndex_eq_pow_three_of_not_le {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M N F : Subgroup G} (hMp : IsPGroup p M)
    (hNn : (N.subgroupOf F).Normal) (hFM : F ≤ M)
    (hrel_le : N.relIndex F ≤ p ^ 3) (hnot : ¬ N.relIndex F ≤ p ^ 2) :
    N.relIndex F = p ^ 3 := by
  have hp : p.Prime := Fact.out
  haveI : (N.subgroupOf F).Normal := hNn
  have hquot : IsPGroup p (↥F ⧸ N.subgroupOf F) := (hMp.to_le hFM).to_quotient _
  obtain ⟨k, hk⟩ := hquot.exists_card_eq
  have hk' : N.relIndex F = p ^ k := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hk
  have hrel_gt : p ^ 2 < N.relIndex F := Nat.lt_of_not_ge hnot
  have h2k : 2 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by simpa [hk'] using hrel_gt)
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by simpa [hk'] using hrel_le)
  have hk_eq : k = 3 := by omega
  exact hk'.trans (by rw [hk_eq])

private lemma scalar_data_of_relIndex_eq_pow_three {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {M N F : Subgroup G} [hNnF : (N.subgroupOf F).Normal]
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    {σ : G} (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hσN : σ ∈ Subgroup.normalizer (N : Set G)) (hσ3 : σ ^ 3 = 1)
    {w : ℕ} (hw : ∀ m ∈ M, σ * m * σ⁻¹ * (m ^ w)⁻¹ ∈ N) (hFM : F ≤ M)
    (hfpf : ∀ m ∈ M, σ * m * σ⁻¹ * m⁻¹ ∈ N → m ∈ N)
    (hNF : N ≤ F) (hrel3 : N.relIndex F = p ^ 3) :
    (w : ZMod p) ^ 3 = 1 ∧ (w : ZMod p) ≠ 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hFN_ne : F ≠ N := by
    intro h
    have h1 : N.relIndex F = 1 := by rw [h, Subgroup.relIndex_self]
    have hp3one : p ^ 3 = 1 := by rw [← hrel3]; exact h1
    have hlt : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hex : ∃ x ∈ F, x ∉ N := by
    by_contra h
    push Not at h
    exact hFN_ne (le_antisymm h hNF)
  obtain ⟨x, hxF, hxN⟩ := hex
  haveI hEA : IsElementaryAbelian p (↥F ⧸ N.subgroupOf F) :=
    CFSG.GroupTheory.isElementaryAbelian_quotient_of_commutator_pow (p := p) hab hexp hFM
  exact scalar_cube_and_ne_one (p := p) hσF hσN hσ3 hw hFM hfpf hxF hxN

private lemma case_mod_one_contradiction (hK1 : KFacts.BlackburnScalarAut)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {M N : Subgroup G} (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    {t σ : G} (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (ht1 : t ≠ 1)
    (hσ3 : σ ^ 3 = 1) (hσN : σ ∈ Subgroup.normalizer (N : Set G))
    (hfpf : ∀ m ∈ M, σ * m * σ⁻¹ * m⁻¹ ∈ N → m ∈ N)
    {w : ℕ} (hw : ∀ m ∈ M, σ * m * σ⁻¹ * (m ^ w)⁻¹ ∈ N)
    {F : Subgroup G} (hNF : N ≤ F) (hFM : F ≤ M)
    (hσF : σ ∈ Subgroup.normalizer (F : Set G)) (hrel3 : N.relIndex F = p ^ 3)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQp : IsPGroup p ↥Q)
    (hQnorm : Q ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G))
    (hgen : ∃ s : Finset ↥Q, s.card ≤ 3 ∧ Subgroup.closure (s : Set ↥Q) = ⊤)
    (hFQN : F ≤ Q ⊔ N) (hσQ : σ ∈ Subgroup.normalizer (Q : Set G)) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNn
  have hNnF : (N.subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hFM.trans hMnormN)
  haveI hNnF' : (N.subgroupOf F).Normal := hNnF
  obtain ⟨hw3, hwne⟩ :=
    scalar_data_of_relIndex_eq_pow_three (p := p) hab hexp hσF hσN hσ3 hw hFM hfpf hNF hrel3
  have hKindex : (N.subgroupOf Q).index = p ^ 3 :=
    index_subgroupOf_eq_pow_three hNM hNn hab hexp hQM hFM hFQN hgen hrel3
  have hΦeqK : frattini ↥Q = N.subgroupOf Q :=
    frattini_eq_subgroupOf_of_card hp5 hNM hNn hab hexp hQp hQM hKindex hgen
  haveI hNQ : (N.subgroupOf Q).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hQM.trans hMnormN)
  let σQ : MulAut ↥Q := Q.normalizerMonoidHom ⟨σ, hσQ⟩
  have hfr_cond : ∀ y : ↥Q, (σQ y)⁻¹ * y ^ w ∈ frattini ↥Q :=
    frattini_condition_of_scalar (p := p) hQM hσQ hw hΦeqK
  have hindex_le : (frattini ↥Q).index ≤ p ^ 2 :=
    hK1 p hp5 ↥Q hQp (elemAbelian_card_le_sq hloc ht2 ht1 hQnorm) w hw3 hwne σQ hfr_cond
  have h3le2 : p ^ 3 ≤ p ^ 2 := by
    calc p ^ 3 = (N.subgroupOf Q).index := hKindex.symm
      _ = (frattini ↥Q).index := by rw [hΦeqK]
      _ ≤ p ^ 2 := hindex_le
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem relIndex_le_sq_of_order_three (hK1 : KFacts.BlackburnScalarAut)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hloc : ∀ S E : Subgroup G, S ≠ ⊥ → IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set G) →
      IsMulCommutative E → (∀ e ∈ E, e ^ p = 1) → Nat.card E ≤ p ^ 2)
    {M N : Subgroup G} (hMp : IsPGroup p M) (hNM : N ≤ M) (hNn : (N.subgroupOf M).Normal)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x ∈ M, x ^ p ∈ N)
    {t : G} (ht2 : IsPGroup 2 (Subgroup.zpowers t)) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (N : Set G))
    {σ : G} (hσ3 : σ ^ 3 = 1) (hσt : σ * t = t * σ) (hσN : σ ∈ Subgroup.normalizer (N : Set G))
    (hfpf : ∀ m ∈ M, σ * m * σ⁻¹ * m⁻¹ ∈ N → m ∈ N)
    (hsc : p % 3 = 1 → ∃ w : ℕ, ∀ m ∈ M, σ * m * σ⁻¹ * (m ^ w)⁻¹ ∈ N)
    {F : Subgroup G} (hNF : N ≤ F) (hFM : F ≤ M) (hσF : σ ∈ Subgroup.normalizer (F : Set G))
    (hFt : ∀ f ∈ F, t * f * t⁻¹ * f⁻¹ ∈ N) :
    N.relIndex F ≤ p ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNn
  have hNnF : (N.subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hFM.trans hMnormN)
  haveI hNnF' : (N.subgroupOf F).Normal := hNnF
  obtain ⟨Q, hQeq, hQM, hQp, hQnorm, ⟨u, huc, hustop⟩, hFQN⟩ :=
    exists_Q_data hp5 hloc hMp hNM hNn ht2 ht1 htN hNF hFM hFt
  have hrel_le : N.relIndex F ≤ p ^ 3 :=
    relIndex_le_pow_three_of_le_sup hNM hNn hab hexp hQM hFM hFQN ⟨u, huc, hustop⟩
  by_contra hle
  have hrel3 : N.relIndex F = p ^ 3 :=
    relIndex_eq_pow_three_of_not_le hMp hNnF hFM hrel_le hle
  have hσzt : σ ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) :=
    mem_normalizer_zpowers_of_commute hσt
  have hσC : σ ∈ Subgroup.normalizer
      ((Subgroup.centralizer (Subgroup.zpowers t : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_centralizer_of_mem_normalizer hσzt
  have hσQ : σ ∈ Subgroup.normalizer (Q : Set G) := by
    rw [hQeq]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hσF, hσC⟩
  by_cases hp1 : p % 3 = 1
  · obtain ⟨w, hw⟩ := hsc hp1
    exact case_mod_one_contradiction hK1 hp5 hloc hNM hNn hab hexp ht2 ht1 hσ3 hσN hfpf hw
      hNF hFM hσF hrel3 hQM hQp hQnorm ⟨u, huc, hustop⟩ hFQN hσQ
  · have hp3 : p % 3 = 2 := by
      have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
      have hne : p % 3 ≠ 0 := by
        intro h0
        have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        have hpeq : 3 = p :=
          (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd).resolve_left (by norm_num)
        omega
      omega
    exact relIndex_ne_pow_three_of_mod_two hp3 hσF hσN hσ3 hFM hfpf hrel3

end CFSG.RankThree.PartTwo.Sec16.Kcd166
