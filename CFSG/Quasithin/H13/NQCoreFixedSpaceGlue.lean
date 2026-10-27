module

public import CFSG.Quasithin.SteinbergCDSingleNoncentralChiefFactor
public import CFSG.Quasithin.H13.NQCoreFixedSpaceTransport

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup Module CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCD (glFixedSpace mem_glFixedSpace)
open CFSG.QuasithinUnique.Setup.Campbell (elemThompsonIn)
open scoped IsMulCommutative

section Binary

variable {G : Type} [Group G] {F : Subgroup G} (V : Subgroup ↥F) [V.Normal] [IsMulCommutative ↥V]
  [Module (ZMod 2) (Additive ↥V)] {T : Subgroup G} (hTF : T ≤ F)
  {P : Type} [Group P] (ι : P →* G) (hι : Function.Injective ι) (K : Subgroup P)
  (hK : K.map ι = V.map F.subtype)

include hTF hι hK in
theorem card_pow_mul_card_fixedPoints_lt (k : ℕ)
    (hGL : ∀ A ≤ (T.subgroupOf F).map (conjGL V), A ≠ ⊥ → IsElementaryAbelian 2 ↥A →
      Nat.card A ^ k * Nat.card (glFixedSpace A) < Nat.card (Additive ↥V))
    {E : Subgroup (MulAut ↥K)} (hE : ∀ σ ∈ E, ∃ t ∈ T, ∀ x : ↥K, ι (σ x) = t * ι x * t⁻¹)
    (hE1 : E ≠ ⊥) (hEe : IsElementaryAbelian 2 ↥E) :
    Nat.card E ^ k * Nat.card (FixedPoints.subgroup ↥E ↥K) < Nat.card ↥K := by
  set ψ := isoOfMap V ι hι K hK with hψ
  have hA : E.map (congrGL V ψ) ≤ (T.subgroupOf F).map (conjGL V) := by
    refine map_congrGL_le_of_conj V ψ hTF fun σ hσ => ?_
    obtain ⟨t, ht, hσt⟩ := hE σ hσ
    refine ⟨t, ht, fun y => ?_⟩
    rw [isoOfMap_coe, isoOfMap_coe, hσt]
  have h := hGL _ hA (map_congrGL_ne_bot V ψ hE1) (isElementaryAbelian_map_congrGL V ψ hEe)
  rwa [card_map_congrGL, card_glFixedSpace_map_congrGL, card_additive_eq V ψ] at h

include hTF hι hK in
theorem card_mul_card_invariant_hom_lt
    (hGL : ∀ A ≤ (T.subgroupOf F).map (conjGL V), A ≠ ⊥ → IsElementaryAbelian 2 ↥A →
      Nat.card A * Nat.card {f : Module.Dual (ZMod 2) (Additive ↥V) //
        ∀ a ∈ A, ∀ w, f ((a : Additive ↥V →ₗ[ZMod 2] Additive ↥V) w) = f w} <
          Nat.card (Module.Dual (ZMod 2) (Additive ↥V)))
    {E : Subgroup (MulAut ↥K)} (hE : ∀ σ ∈ E, ∃ t ∈ T, ∀ x : ↥K, ι (σ x) = t * ι x * t⁻¹)
    (hE1 : E ≠ ⊥) (hEe : IsElementaryAbelian 2 ↥E) :
    Nat.card E * Nat.card {φ : ↥K →* Multiplicative (ZMod 2) // ∀ σ ∈ E, ∀ v, φ (σ v) = φ v} <
      Nat.card (↥K →* Multiplicative (ZMod 2)) := by
  set ψ := isoOfMap V ι hι K hK with hψ
  have hA : E.map (congrGL V ψ) ≤ (T.subgroupOf F).map (conjGL V) := by
    refine map_congrGL_le_of_conj V ψ hTF fun σ hσ => ?_
    obtain ⟨t, ht, hσt⟩ := hE σ hσ
    refine ⟨t, ht, fun y => ?_⟩
    rw [isoOfMap_coe, isoOfMap_coe, hσt]
  have h := hGL _ hA (map_congrGL_ne_bot V ψ hE1) (isElementaryAbelian_map_congrGL V ψ hEe)
  rwa [card_map_congrGL, card_invariant_dual_map_congrGL, card_dual_eq V ψ] at h

end Binary

theorem exists_conj_of_mem_range {G P : Type*} [Group G] [Group P] {K : Subgroup P} [K.Normal]
    (ι : P →* G) {σ : MulAut ↥K} (hσ : σ ∈ (MulAut.conjNormal : P →* MulAut ↥K).range) :
    ∃ p : P, ∀ x : ↥K, ι (σ x) = ι p * ι x * (ι p)⁻¹ := by
  obtain ⟨p, rfl⟩ := hσ
  refine ⟨p, fun x => ?_⟩
  rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]

theorem index_lt_of_card_mul_lt {K : Type*} [Group K] [Finite K] {S : Subgroup K} {e : ℕ}
    (h : e * Nat.card S < Nat.card K) : e < S.index := by
  rw [← S.card_mul_index, mul_comm] at h
  exact Nat.lt_of_mul_lt_mul_left h

section AutOn

variable {H : Type*} [Group H]

theorem fixedPoints_autOn {A K : Subgroup H} (hA : A ≤ normalizer (K : Set H)) :
    FixedPoints.subgroup ↥(autOn A K) ↥K = (centralizer (A : Set H)).subgroupOf K := by
  ext v
  rw [SteinbergBQ.mem_fixedPoints_subgroup_mulAut_iff, mem_subgroupOf, mem_centralizer_iff]
  constructor
  · intro h a ha
    have h1 := h (conjAct K ⟨a, hA ha⟩) ⟨⟨a, hA ha⟩, ha, rfl⟩
    have h2 : (a : H) * v * a⁻¹ = v :=
      ((normalizerMonoidHom_apply_apply_coe K (inclusion le_rfl ⟨a, hA ha⟩) v).symm.trans
        (congrArg Subtype.val h1))
    calc a * (v : H) = (a * v * a⁻¹) * a := by group
      _ = v * a := by rw [h2]
  · rintro h _ ⟨n, hn, rfl⟩
    apply Subtype.ext
    rw [show ((conjAct K n v : ↥K) : H) = n * v * (n : H)⁻¹ from
      normalizerMonoidHom_apply_apply_coe K (inclusion le_rfl n) v, h n hn, mul_inv_cancel_right]

end AutOn

section Witness

variable {G : Type} [Group G] {F : Subgroup G} (V : Subgroup ↥F) [V.Normal] [IsMulCommutative ↥V]
  [Module (ZMod 2) (Additive ↥V)] [Finite G]

theorem exists_witness_of_autOn {T H : Subgroup G} (hTF : T ≤ F) {A K : Subgroup ↥H}
    (hK : K.map H.subtype = V.map F.subtype) (hAT : A ≤ T.subgroupOf H)
    (hAN : A ≤ normalizer (K : Set ↥H)) (hA1 : autOn A K ≠ ⊥)
    (hAe : IsElementaryAbelian 2 ↥(autOn A K)) {d r : ℕ}
    (hd : (centralizer (A : Set ↥H)).relIndex K = 2 ^ d) (hr : Nat.card (autOn A K) = 2 ^ r)
    (hdr : d ≤ 2 * r) :
    ∃ A' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)),
      A' ≤ (T.subgroupOf F).map (conjGL V) ∧ IsElementaryAbelian 2 ↥A' ∧ A' ≠ ⊥ ∧
      ∃ r : ℕ, Nat.card A' = 2 ^ r ∧
        finrank (ZMod 2) (Additive ↥V ⧸ glFixedSpace A') ≤ 2 * r := by
  set ψ := isoOfMap V H.subtype H.subtype_injective K hK with hψ
  set E := autOn A K with hE
  have hEle : E.map (congrGL V ψ) ≤ (T.subgroupOf F).map (conjGL V) := by
    refine map_congrGL_le_of_conj V ψ hTF fun σ hσ => ?_
    obtain ⟨n, hn, rfl⟩ := hσ
    refine ⟨((n : ↥H) : G), hAT hn, fun y => ?_⟩
    rw [isoOfMap_coe, isoOfMap_coe]
    change (((conjAct K n y : ↥K) : ↥H) : G) = _
    rw [show ((conjAct K n y : ↥K) : ↥H) = n * y * (n : ↥H)⁻¹ from
      normalizerMonoidHom_apply_apply_coe K (inclusion le_rfl n) y]
    rfl
  refine ⟨E.map (congrGL V ψ), hEle, isElementaryAbelian_map_congrGL V ψ hAe,
    map_congrGL_ne_bot V ψ hA1, r, by rw [card_map_congrGL, hr], ?_⟩
  have hfin : Finite (Additive ↥V) := inferInstanceAs (Finite ↥V)
  have h1 := Submodule.card_eq_card_quotient_mul_card (glFixedSpace (E.map (congrGL V ψ)))
  rw [card_glFixedSpace_map_congrGL, card_additive_eq V ψ, hE, fixedPoints_autOn hAN,
    card_quotient_eq_two_pow_finrank] at h1
  have h2 := ((centralizer (A : Set ↥H)).subgroupOf K).card_mul_index
  rw [← relIndex, hd, h1] at h2
  have hpos : 0 < Nat.card ((centralizer (A : Set ↥H)).subgroupOf K) := Nat.card_pos
  have h3 : 2 ^ finrank (ZMod 2) (Additive ↥V ⧸ glFixedSpace (E.map (congrGL V ψ))) = 2 ^ d :=
    Nat.eq_of_mul_eq_mul_left hpos h2.symm
  rw [Nat.pow_right_injective le_rfl h3]
  exact hdr

end Witness

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem false_of_le_normalizer {F J H X : Subgroup G} (hFJ : U3.UniqueMaxTwoLocal F J)
    (hHJ : ¬ H ≤ J) (hX2 : IsPGroup 2 X) (hX1 : X ≠ ⊥)
    (hFH : F ⊔ H ≤ normalizer (X : Set G)) : False := by
  obtain ⟨J', hJ', hNJ'⟩ := NQBlock.exists_maxTwoLocal_ge_of_isTwoLocal
    (H := normalizer (X : Set G)) ⟨X, hX1, hX2, rfl⟩
  have h1 := hFJ.2.2 J' hJ' ((le_sup_left.trans hFH).trans hNJ')
  subst h1
  exact hHJ ((le_sup_right.trans hFH).trans hNJ')

theorem le_normalizer_elemThompsonIn (p : ℕ) [Fact p.Prime] {X N : Subgroup G}
    (hN : N ≤ normalizer (X : Set G)) : N ≤ normalizer (elemThompsonIn p X : Set G) := by
  intro g hg
  have h1 := LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hN hg)
  rw [LieType.Steinberg.mem_normalizer_iff_map_conj,
    ← Setup.Campbell.elemThompsonIn_map_of_injective p _ (MulAut.conj g).injective, h1]

omit [Finite G] in
theorem isElemAbelian_map_subtype {H : Subgroup G} {N : Subgroup ↥H}
    (hN : IsElementaryAbelian 2 ↥N) : IsElemAbelian 2 (N.map H.subtype) := by
  refine ⟨?_, ?_⟩
  · have e := N.equivMapOfInjective H.subtype H.subtype_injective
    exact e.surjective.isMulCommutative hN.toIsMulCommutative
  · rintro _ ⟨x, hx, rfl⟩
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hN.exponent_dvd_p ⟨x, hx⟩
    rw [← map_pow]
    have h2 : x ^ 2 = 1 := congrArg Subtype.val h
    rw [h2, map_one]

theorem map_normalClosure_eq_iSup {H X : Subgroup G} (hXH : X ≤ H) :
    (normalClosure ((X.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype =
      ⨆ (h : G) (_ : h ∈ H), X.map (MulAut.conj h).toMonoidHom := by
  set U := ⨆ (h : G) (_ : h ∈ H), X.map (MulAut.conj h).toMonoidHom with hU
  have hHU : H ≤ normalizer (U : Set G) := SteinbergCD.le_normalizer_iSup_conj
  have hUH : U ≤ H := SteinbergCD.iSup_conj_le hXH le_normalizer
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    have hn : (U.comap H.subtype).Normal := (normal_subgroupOf_iff_le_normalizer hUH).mpr hHU
    refine normalClosure_le_normal ?_
    intro x hx
    exact SteinbergCD.le_iSup_conj (H := H) hx
  · refine iSup₂_le fun h hh => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxn : (⟨x, hXH hx⟩ : ↥H) ∈ normalClosure ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      subset_normalClosure hx
    refine ⟨⟨h, hh⟩ * ⟨x, hXH hx⟩ * ⟨h, hh⟩⁻¹,
      (normalClosure_normal).conj_mem _ hxn _, rfl⟩

end Ambient

end CFSG.Quasithin.H13.NQCore
