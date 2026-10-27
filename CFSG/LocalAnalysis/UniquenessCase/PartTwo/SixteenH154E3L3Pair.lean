module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Para
import CFSG.Quasithin.EmptyFaithful.S146F3
import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup Matrix CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]
variable {A T L L₂ : Subgroup G}

private abbrev s16h_e3_l3_conj (a : G) : G →* G := (MulAut.conj a).toMonoidHom

private theorem s16h_e3_l3_conj_apply (a x : G) :
    s16h_e3_l3_conj a x = a * x * a⁻¹ := rfl

private theorem s16h_e3_l3_mem_normalizer_iff {H : Subgroup G} {g : G} :
    g ∈ normalizer H ↔ H.map (s16h_e3_l3_conj g) = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq

private theorem s16h_e3_l3_isPSL_of_isSLn {X : Type} [Group X] (h : IsSLn X 3 1) :
    IsPSL 3 2 1 X := by
  obtain ⟨K, hfield, hfin, hcard, ⟨eX⟩⟩ := h
  letI : Field K := hfield
  letI : Finite K := hfin
  have hK : Nat.card K = 2 := by simpa using hcard
  haveI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, ZMod.card, hK]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hKf
  let e0 : SpecialLinearGroup (Fin 3) K ≃* ↥(StatedSL 3 K) :=
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (StatedAPI.statedSL_eq_range_toGL 3 K).symm)
  exact isPSL_three_two_iff.mpr
    ⟨eX.trans (e0.symm.trans (slMulEquivOfRingEquiv ε 3))⟩

private theorem s16h_e3_l3_card_of_isSLn {X : Type} [Group X] (h : IsSLn X 3 1) :
    Nat.card X = 168 := by
  obtain ⟨K, hfield, _hfin, hcard, ⟨eX⟩⟩ := h
  letI : Field K := hfield
  have hK : Nat.card K = 2 := by simpa using hcard
  rw [Nat.card_congr eX.toEquiv]
  exact StatedAPI.card_statedSL_three_of_card_eq_two hK

private theorem s16h_e3_l3_map_conj_mul (a b : G) (X : Subgroup G) :
    (X.map (s16h_e3_l3_conj b)).map (s16h_e3_l3_conj a) = X.map (s16h_e3_l3_conj (a * b)) := by
  rw [Subgroup.map_map]
  have hcomp : (s16h_e3_l3_conj a).comp (s16h_e3_l3_conj b) = s16h_e3_l3_conj (a * b) := by
    ext y
    simp only [MonoidHom.comp_apply, s16h_e3_l3_conj_apply]
    group
  rw [hcomp]

private theorem s16h_e3_l3_map_conj_mul_inv (a b : G) (X : Subgroup G) :
    X.map (s16h_e3_l3_conj (a * b)) = (X.map (s16h_e3_l3_conj b)).map (s16h_e3_l3_conj a) :=
  (s16h_e3_l3_map_conj_mul a b X).symm

private theorem s16h_e3_l3_map_conj_inv_cancel (a : G) (X : Subgroup G) :
    (X.map (s16h_e3_l3_conj a)).map (s16h_e3_l3_conj a⁻¹) = X := by
  rw [s16h_e3_l3_map_conj_mul a⁻¹ a X]
  rw [show a⁻¹ * a = 1 by group]
  rw [show s16h_e3_l3_conj (1 : G) = MonoidHom.id G by
    ext y
    simp [s16h_e3_l3_conj_apply]]
  rw [Subgroup.map_id]

private theorem s16h_e3_l3_map_conj_eq_of_eq {a : G} {X Y : Subgroup G}
    (h : X.map (s16h_e3_l3_conj a) = Y.map (s16h_e3_l3_conj a)) : X = Y := by
  have h' := congrArg (Subgroup.comap (s16h_e3_l3_conj a)) h
  rwa [Subgroup.comap_map_eq_self_of_injective (f := s16h_e3_l3_conj a)
      (MulAut.conj a).injective X,
    Subgroup.comap_map_eq_self_of_injective (f := s16h_e3_l3_conj a)
      (MulAut.conj a).injective Y] at h'

private theorem s16h_e3_l3_inner_normalizes_sylow_inf {X : Subgroup G} {τ γ : G}
    (hτT : τ ∈ T) (hγX : γ ∈ X)
    (hact : ∀ l ∈ X, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    γ ∈ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact ⟨by
        rw [← hact y hy.2]
        exact T.mul_mem (T.mul_mem hτT hy.1) (T.inv_mem hτT),
      X.mul_mem (X.mul_mem hγX hy.2) (X.inv_mem hγX)⟩
  · intro hy
    have hyX : y ∈ X := by
      have : y = γ⁻¹ * (γ * y * γ⁻¹) * γ := by group
      rw [this]
      exact X.mul_mem (X.mul_mem (X.inv_mem hγX) hy.2) hγX
    have hmemT : τ * y * τ⁻¹ ∈ T := by
      rw [hact y hyX]
      exact hy.1
    have heqT : y = τ⁻¹ * (τ * y * τ⁻¹) * τ := by group
    exact ⟨by
        rw [heqT]
        exact T.mul_mem (T.mul_mem (T.inv_mem hτT) hmemT) hτT,
      hyX⟩

private theorem s16h_e3_l3_map_conj_eq_of_inner_on {X P : Subgroup G} {τ γ : G}
    (hPX : P ≤ X) (hγX : γ ∈ X)
    (hact : ∀ l ∈ X, τ * l * τ⁻¹ = γ * l * γ⁻¹) (hγP : γ ∈ P) :
    P.map (s16h_e3_l3_conj τ) = P := by
  have hγnormP : P.map (s16h_e3_l3_conj γ) = P :=
    s16h_e3_l3_mem_normalizer_iff.mp (Subgroup.le_normalizer hγP)
  have hτγ : P.map (s16h_e3_l3_conj τ) = P.map (s16h_e3_l3_conj γ) := by
    apply le_antisymm
    · rintro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨p, hp, (hact p (hPX hp)).symm⟩
    · rintro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨p, hp, (hact p (hPX hp))⟩
  rw [hτγ, hγnormP]

private theorem s16h_e3_l3_parabolic_of_conj {X : Subgroup G}
    (hXSL : IsSLn ↥X 3 1) (hTA : T ≤ A)
    (hinnerX : ∀ τ ∈ A, τ ∈ normalizer (X : Set G) →
      ∃ γ ∈ X, ∀ l ∈ X, τ * l * τ⁻¹ = γ * l * γ⁻¹)
    (hTsylX : IsSylowOf 2 (T ⊓ X) X) :
    ∃ P : Subgroup G, P ≤ X ∧ Nat.card P = 24 ∧ (∀ p ∈ P, p ^ 12 = 1) ∧
      ∀ τ ∈ T, τ ∈ normalizer (X : Set G) → P.map (s16h_e3_l3_conj τ) = P := by
  have hX168 : Nat.card ↥X = 168 := s16h_e3_l3_card_of_isSLn hXSL
  have hfac : (168 : ℕ).factorization 2 = 3 := by
    have h1 : 2 ^ 3 ∣ 168 := by norm_num
    have h2 : ¬ 2 ^ 4 ∣ 168 := by norm_num
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)] at h1 h2
    omega
  have hTcard : Nat.card ↥(T ⊓ X) = 8 := by
    have h := hTsylX.card_eq
    rw [hX168, hfac] at h
    simpa using h
  have hS8 : Nat.card ((T ⊓ X).subgroupOf X) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ X ≤ X)).toEquiv]
    exact hTcard
  have hSp : IsPGroup 2 ((T ⊓ X).subgroupOf X) := hTsylX.isPGroup.comap_subtype
  obtain ⟨P', hP'norm, hP'card, hP'pow⟩ :=
    s16h_e3_l3_parabolic_of_sylow (X := ↥X) hXSL hSp hS8
  refine ⟨P'.map X.subtype, Subgroup.map_subtype_le P', ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hP'card]
  · intro p hp
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hp
    have h := congrArg (X.subtype) (hP'pow x' hx')
    simpa using h
  · intro τ hτT hτN
    obtain ⟨γ, hγX, hγact⟩ := hinnerX τ (hTA hτT) hτN
    have hγnorm : γ ∈ Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G) :=
      s16h_e3_l3_inner_normalizes_sylow_inf hτT hγX hγact
    have hγP' : (⟨γ, hγX⟩ : ↥X) ∈ Subgroup.normalizer
        ((T ⊓ X).subgroupOf X : Set ↥X) := by
      rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right : T ⊓ X ≤ X),
        Subgroup.mem_subgroupOf]
      simpa using hγnorm
    have hγP : γ ∈ P'.map X.subtype :=
      Subgroup.mem_map.mpr ⟨⟨γ, hγX⟩, hP'norm hγP', rfl⟩
    exact s16h_e3_l3_map_conj_eq_of_inner_on (Subgroup.map_subtype_le P') hγX hγact hγP

theorem s16h_e3_l3_two_parabolics_of_inner {G : Type} [Group G] [Finite G]
    {A T L L₂ : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T A) (hL : IsSLn ↥L 3 1)
    (hLA : L ≤ A)
    (hconj : ∀ a ∈ A, L.map (MulAut.conj a).toMonoidHom = L ∨
      L.map (MulAut.conj a).toMonoidHom = L₂)
    (hL₂ : ∃ a ∈ A, L.map (MulAut.conj a).toMonoidHom = L₂) (hne : L₂ ≠ L)
    (hcomm : ∀ x ∈ L, ∀ y ∈ L₂, x * y = y * x)
    (hinner : ∀ τ ∈ A, τ ∈ normalizer (L : Set G) →
      ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    ∃ P Q : Subgroup G, P ≤ A ∧ Q ≤ A ∧ Nat.card ↥P = 24 ∧ Nat.card ↥Q = 24 ∧
      (∀ p ∈ P, p ^ 12 = 1) ∧ (∀ q ∈ Q, q ^ 12 = 1) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ P ⊓ Q = ⊥ ∧
      T ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
  classical
  have hTle : T ≤ A := hT.le
  have hLpsl : IsPSL 3 2 1 ↥L := s16h_e3_l3_isPSL_of_isSLn hL
  have hL168 : Nat.card ↥L = 168 := s16h_e3_l3_card_of_isSLn hL
  have hLsimple : IsSimpleGroup ↥L :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 3 2 1 hLpsl).2
  have hLnc : ¬ IsMulCommutative ↥L := by
    intro hc
    haveI : IsMulCommutative ↥L := hc
    have hp : Nat.Prime (Nat.card ↥L) := (Group.is_simple_iff_prime_card).mp hLsimple
    rw [hL168] at hp
    norm_num at hp
  have hcenter : Subgroup.center ↥L = ⊥ := by
    haveI : IsSimpleGroup ↥L := hLsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hLnc
  have hdisj : L ⊓ L₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzL, hzL₂⟩ := hz
    have hzc : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact hcomm (l : G) l.2 z hzL₂
    rw [hcenter, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  obtain ⟨a₂, ha₂A, ha₂⟩ := hL₂
  have hL₂A : L₂ ≤ A := by
    rw [← ha₂]
    intro x hx
    obtain ⟨l, hl, hxl⟩ := Subgroup.mem_map.mp hx
    rw [← hxl, s16h_e3_l3_conj_apply]
    exact A.mul_mem (A.mul_mem ha₂A (hLA hl)) (A.inv_mem ha₂A)
  have hL₂SL : IsSLn ↥L₂ 3 1 := by
    obtain ⟨K, hfield, hfin, hcard, ⟨eX⟩⟩ := hL
    refine ⟨K, hfield, hfin, hcard, ⟨?e⟩⟩
    let f : ↥L ≃* ↥L₂ := (MulEquiv.subgroupMap (MulAut.conj a₂) L).trans
      (MulEquiv.subgroupCongr ha₂)
    exact f.symm.trans eX
  have hswap : ∀ a ∈ A, (L.map (s16h_e3_l3_conj a) = L → L₂.map (s16h_e3_l3_conj a) = L₂) ∧
      (L.map (s16h_e3_l3_conj a) = L₂ → L₂.map (s16h_e3_l3_conj a) = L) := by
    intro a ha
    have hcomp : L₂.map (s16h_e3_l3_conj a) = L.map (s16h_e3_l3_conj (a * a₂)) := by
      rw [← ha₂, Subgroup.map_map]
      have hcomp2 : (s16h_e3_l3_conj a).comp (s16h_e3_l3_conj a₂) = s16h_e3_l3_conj (a * a₂) := by
        ext y
        simp only [MonoidHom.comp_apply, s16h_e3_l3_conj_apply]
        group
      rw [hcomp2]
    have hconjaa₂ := hconj (a * a₂) (A.mul_mem ha ha₂A)
    constructor
    · intro hLa
      rcases hconjaa₂ with h | h
      · exfalso
        have heq : L₂.map (s16h_e3_l3_conj a) = L.map (s16h_e3_l3_conj a) := by
          rw [hcomp, h, hLa]
        exact hne (s16h_e3_l3_map_conj_eq_of_eq heq)
      · rw [hcomp, h]
    · intro hLa
      rcases hconjaa₂ with h | h
      · rw [hcomp, h]
      · exfalso
        have heq : L₂.map (s16h_e3_l3_conj a) = L.map (s16h_e3_l3_conj a) := by
          rw [hcomp, h, hLa]
        exact hne (s16h_e3_l3_map_conj_eq_of_eq heq)
  have hinnerL₂ : ∀ τ ∈ A, τ ∈ normalizer (L₂ : Set G) →
      ∃ γ ∈ L₂, ∀ l ∈ L₂, τ * l * τ⁻¹ = γ * l * γ⁻¹ := by
    intro τ hτA hτN₂
    have hτmap : L₂.map (s16h_e3_l3_conj τ) = L₂ :=
      s16h_e3_l3_mem_normalizer_iff.mp hτN₂
    have hτ'N : a₂⁻¹ * τ * a₂ ∈ normalizer (L : Set G) := by
      rw [s16h_e3_l3_mem_normalizer_iff]
      rw [show a₂⁻¹ * τ * a₂ = a₂⁻¹ * (τ * a₂) by group,
        s16h_e3_l3_map_conj_mul_inv a₂⁻¹ (τ * a₂) L,
        s16h_e3_l3_map_conj_mul_inv τ a₂ L, ha₂, hτmap]
      rw [← ha₂, s16h_e3_l3_map_conj_inv_cancel a₂ L]
    have hτ'A : a₂⁻¹ * τ * a₂ ∈ A :=
      A.mul_mem (A.mul_mem (A.inv_mem ha₂A) hτA) ha₂A
    obtain ⟨γ, hγL, hγact⟩ := hinner (a₂⁻¹ * τ * a₂) hτ'A hτ'N
    refine ⟨a₂ * γ * a₂⁻¹, ?_, ?_⟩
    · rw [← ha₂]
      exact Subgroup.mem_map.mpr ⟨γ, hγL, rfl⟩
    · intro l₂ hl₂
      rw [← ha₂] at hl₂
      obtain ⟨l, hl, hll₂⟩ := Subgroup.mem_map.mp hl₂
      rw [← hll₂]
      simp only [s16h_e3_l3_conj_apply]
      calc τ * (a₂ * l * a₂⁻¹) * τ⁻¹
          = a₂ * ((a₂⁻¹ * τ * a₂) * l * (a₂⁻¹ * τ * a₂)⁻¹) * a₂⁻¹ := by group
        _ = a₂ * (γ * l * γ⁻¹) * a₂⁻¹ := by rw [hγact l hl]
        _ = (a₂ * γ * a₂⁻¹) * (a₂ * l * a₂⁻¹) * (a₂ * γ * a₂⁻¹)⁻¹ := by group
  have hNA : L ⊔ L₂ ≤ A := sup_le hLA hL₂A
  have hNnormal : A ≤ normalizer ((L ⊔ L₂ : Subgroup G) : Set G) := by
    intro a ha
    rw [s16h_e3_l3_mem_normalizer_iff, Subgroup.map_sup]
    rcases hconj a ha with hLa | hLa
    · rw [hLa, (hswap a ha).1 hLa]
    · rw [hLa, (hswap a ha).2 hLa, sup_comm]
  have hTsylN : IsSylowOf 2 (T ⊓ (L ⊔ L₂)) (L ⊔ L₂) :=
    hT.inf_of_le_normalizer hNA hNnormal
  have hNL : (L ⊔ L₂ : Subgroup G) ≤ normalizer (L : Set G) := by
    refine sup_le Subgroup.le_normalizer ?_
    intro y hy
    rw [s16h_e3_l3_mem_normalizer_iff]
    apply le_antisymm
    · rintro z ⟨l, hl, rfl⟩
      rw [s16h_e3_l3_conj_apply, show y * l * y⁻¹ = l by rw [← hcomm l hl y hy]; group]
      exact hl
    · intro l hl
      exact Subgroup.mem_map.mpr ⟨l, hl, by
        rw [s16h_e3_l3_conj_apply, show y * l * y⁻¹ = l by rw [← hcomm l hl y hy]; group]⟩
  have hN₂L : (L ⊔ L₂ : Subgroup G) ≤ normalizer (L₂ : Set G) := by
    refine sup_le ?_ Subgroup.le_normalizer
    intro y hy
    rw [s16h_e3_l3_mem_normalizer_iff]
    apply le_antisymm
    · rintro z ⟨l, hl, rfl⟩
      rw [s16h_e3_l3_conj_apply, show y * l * y⁻¹ = l by rw [hcomm y hy l hl]; group]
      exact hl
    · intro l hl
      exact Subgroup.mem_map.mpr ⟨l, hl, by
        rw [s16h_e3_l3_conj_apply, show y * l * y⁻¹ = l by rw [hcomm y hy l hl]; group]⟩
  have hTsylL : IsSylowOf 2 (T ⊓ L) L := by
    have h := hTsylN.inf_of_le_normalizer (le_sup_left : L ≤ L ⊔ L₂) hNL
    rwa [inf_assoc, inf_eq_right.mpr (le_sup_left : L ≤ L ⊔ L₂)] at h
  have hTsylL₂ : IsSylowOf 2 (T ⊓ L₂) L₂ := by
    have h := hTsylN.inf_of_le_normalizer (le_sup_right : L₂ ≤ L ⊔ L₂) hN₂L
    rwa [inf_assoc, inf_eq_right.mpr (le_sup_right : L₂ ≤ L ⊔ L₂)] at h
  obtain ⟨P, hPleL, hPcard, hPpow, hPnormT⟩ :=
    s16h_e3_l3_parabolic_of_conj hL hTle hinner hTsylL
  by_cases hx : ∃ x ∈ T, x ∉ normalizer (L : Set G)
  · obtain ⟨x, hxT, hxNotN⟩ := hx
    have hxL : L.map (s16h_e3_l3_conj x) = L₂ := by
      rcases hconj x (hTle hxT) with h | h
      · exact absurd (s16h_e3_l3_mem_normalizer_iff.mpr h) hxNotN
      · exact h
    let Q : Subgroup G := P.map (s16h_e3_l3_conj x)
    have hQleL₂ : Q ≤ L₂ := by
      dsimp only [Q]
      rw [← hxL]
      exact Subgroup.map_mono hPleL
    have hQleA : Q ≤ A := by
      dsimp only [Q]
      refine (Subgroup.map_mono (hPleL.trans hLA)).trans ?_
      intro y hy
      obtain ⟨a, ha, hconja⟩ := Subgroup.mem_map.mp hy
      rw [← hconja, s16h_e3_l3_conj_apply]
      exact A.mul_mem (A.mul_mem (hTle hxT) ha) (A.inv_mem (hTle hxT))
    have hQcard : Nat.card ↥Q = 24 := by
      dsimp only [Q]
      rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hPcard]
    have hQpow : ∀ q ∈ Q, q ^ 12 = 1 := by
      intro q hq
      obtain ⟨p, hp, hpq⟩ := Subgroup.mem_map.mp hq
      calc q ^ 12 = (s16h_e3_l3_conj x p) ^ 12 := by rw [hpq]
        _ = s16h_e3_l3_conj x (p ^ 12) := by rw [map_pow]
        _ = s16h_e3_l3_conj x 1 := by rw [hPpow p hp]
        _ = 1 := by rw [map_one]
    have hPQcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p :=
      fun p hp q hq => hcomm p (hPleL hp) q (hQleL₂ hq)
    have hPQdisj : P ⊓ Q = ⊥ := by
      apply le_bot_iff.mp
      rw [← hdisj]
      exact inf_le_inf hPleL hQleL₂
    have hTnorm : T ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
      intro t ht
      rw [s16h_e3_l3_mem_normalizer_iff]
      by_cases htN : t ∈ normalizer (L : Set G)
      · have hLt : L.map (s16h_e3_l3_conj t) = L :=
          s16h_e3_l3_mem_normalizer_iff.mp htN
        have hL₂t : L₂.map (s16h_e3_l3_conj t) = L₂ := (hswap t (hTle ht)).1 hLt
        have hxtN : x⁻¹ * t * x ∈ normalizer (L : Set G) := by
          rw [s16h_e3_l3_mem_normalizer_iff]
          rw [show x⁻¹ * t * x = x⁻¹ * (t * x) by group,
            s16h_e3_l3_map_conj_mul_inv x⁻¹ (t * x) L,
            s16h_e3_l3_map_conj_mul_inv t x L, hxL, hL₂t]
          rw [← hxL, s16h_e3_l3_map_conj_inv_cancel x L]
        have hPxtx : P.map (s16h_e3_l3_conj (x⁻¹ * t * x)) = P :=
          hPnormT _ (T.mul_mem (T.mul_mem (T.inv_mem hxT) ht) hxT) hxtN
        have hPt : P.map (s16h_e3_l3_conj t) = P := hPnormT t ht htN
        have hQt : Q.map (s16h_e3_l3_conj t) = Q := by
          dsimp only [Q]
          rw [s16h_e3_l3_map_conj_mul t x P]
          have harg : t * x = x * (x⁻¹ * t * x) := by group
          rw [harg, ← s16h_e3_l3_map_conj_mul x (x⁻¹ * t * x) P, hPxtx]
        rw [Subgroup.map_sup, hPt, hQt]
      · have hLt : L.map (s16h_e3_l3_conj t) = L₂ := by
          rcases hconj t (hTle ht) with h | h
          · exact absurd (s16h_e3_l3_mem_normalizer_iff.mpr h) htN
          · exact h
        have hL₂t : L₂.map (s16h_e3_l3_conj t) = L := (hswap t (hTle ht)).2 hLt
        have hxtN : x⁻¹ * t ∈ normalizer (L : Set G) := by
          rw [s16h_e3_l3_mem_normalizer_iff]
          rw [s16h_e3_l3_map_conj_mul_inv x⁻¹ t L, hLt]
          rw [← hxL, s16h_e3_l3_map_conj_inv_cancel x L]
        have htxN : t * x ∈ normalizer (L : Set G) := by
          rw [s16h_e3_l3_mem_normalizer_iff]
          rw [s16h_e3_l3_map_conj_mul_inv t x L, hxL, hL₂t]
        have hPxt : P.map (s16h_e3_l3_conj (x⁻¹ * t)) = P :=
          hPnormT _ (T.mul_mem (T.inv_mem hxT) ht) hxtN
        have hPtx : P.map (s16h_e3_l3_conj (t * x)) = P :=
          hPnormT _ (T.mul_mem ht hxT) htxN
        have hPt : P.map (s16h_e3_l3_conj t) = Q := by
          dsimp only [Q]
          have harg : t = x * (x⁻¹ * t) := by group
          rw [harg, ← s16h_e3_l3_map_conj_mul x (x⁻¹ * t) P, hPxt]
        have hQt : Q.map (s16h_e3_l3_conj t) = P := by
          dsimp only [Q]
          rw [s16h_e3_l3_map_conj_mul t x P, hPtx]
        rw [Subgroup.map_sup, hPt, hQt, sup_comm]
    exact ⟨P, Q, hPleL.trans hLA, hQleA, hPcard, hQcard, hPpow, hQpow, hPQcomm,
      hPQdisj, hTnorm⟩
  · have hTN : T ≤ normalizer (L : Set G) := by
      intro t ht
      by_contra h
      exact hx ⟨t, ht, h⟩
    obtain ⟨Q, hQleL₂, hQcard, hQpow, hQnormT⟩ :=
      s16h_e3_l3_parabolic_of_conj hL₂SL hTle hinnerL₂ hTsylL₂
    have hQleA : Q ≤ A := hQleL₂.trans hL₂A
    have hPQcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p :=
      fun p hp q hq => hcomm p (hPleL hp) q (hQleL₂ hq)
    have hPQdisj : P ⊓ Q = ⊥ := by
      apply le_bot_iff.mp
      rw [← hdisj]
      exact inf_le_inf hPleL hQleL₂
    have hTnorm : T ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) := by
      intro t ht
      rw [s16h_e3_l3_mem_normalizer_iff]
      have htN : t ∈ normalizer (L : Set G) := hTN ht
      have hLt : L.map (s16h_e3_l3_conj t) = L :=
        s16h_e3_l3_mem_normalizer_iff.mp htN
      have hL₂t : L₂.map (s16h_e3_l3_conj t) = L₂ := (hswap t (hTle ht)).1 hLt
      have htN₂ : t ∈ normalizer (L₂ : Set G) :=
        s16h_e3_l3_mem_normalizer_iff.mpr hL₂t
      rw [Subgroup.map_sup, hPnormT t ht htN, hQnormT t ht htN₂]
    exact ⟨P, Q, hPleL.trans hLA, hQleA, hPcard, hQcard, hPpow, hQpow, hPQcomm,
      hPQdisj, hTnorm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
