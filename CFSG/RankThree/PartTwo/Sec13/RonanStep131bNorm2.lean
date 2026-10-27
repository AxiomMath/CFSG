module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bPlan

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

@[expose] def Norm2 (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup (MulAut X), IsPGroup 3 P → Nat.card P ≤ 9 →
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ σ ∈ P, V.map σ.toMonoidHom = V

theorem norm2_mem_iff_of_map_eq {G : Type} [Group G] {K : Subgroup G} {τ : G ≃* G}
    (h : K.map τ.toMonoidHom = K) (x : G) : τ x ∈ K ↔ x ∈ K := by
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hxy : y = x := τ.injective hyx
    exact hxy ▸ hy
  · intro hx
    rw [← h]
    exact Subgroup.mem_map_of_mem τ.toMonoidHom hx

theorem norm2_map_eq_of_forall_mem_iff {G : Type} [Group G] (K : Subgroup G) (τ : G ≃* G)
    (h : ∀ x, τ x ∈ K ↔ x ∈ K) : K.map τ.toMonoidHom = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    exact (h k).mpr hk
  · intro hx
    refine Subgroup.mem_map.mpr ⟨τ.symm x, ?_, by simp⟩
    exact (h (τ.symm x)).mp (by simpa using hx)

theorem norm2_mem_center_map_iff {Y : Type} [Group Y] (σ : Y ≃* Y) (x : Y) :
    σ x ∈ Subgroup.center Y ↔ x ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h' := h (σ g)
    rw [← map_mul, ← map_mul] at h'
    exact σ.injective h'
  · intro h g
    have h' := congrArg σ (h (σ.symm g))
    simpa using h'

theorem norm2_center_map_eq {Y : Type} [Group Y] (σ : MulAut Y) :
    (Subgroup.center Y).map σ.toMonoidHom = Subgroup.center Y :=
  norm2_map_eq_of_forall_mem_iff _ σ (norm2_mem_center_map_iff σ)

def norm2_quotAutHom (Y : Type) [Group Y] : MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) where
  toFun σ := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) σ (norm2_center_map_eq σ)
  map_one' := MulEquiv.ext fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  map_mul' σ τ := MulEquiv.ext fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rfl

theorem norm2_quotAutHom_mk {Y : Type} [Group Y] (σ : MulAut Y) (y : Y) :
    norm2_quotAutHom Y σ (y : Y ⧸ Subgroup.center Y) = ((σ y : Y) : Y ⧸ Subgroup.center Y) :=
  QuotientGroup.congr_mk _ _ σ (norm2_center_map_eq σ) y

theorem Norm2.of_inner {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hAut : Nat.card (MulAut X) ≤ 2 * Nat.card X) (S : Sylow 3 X)
    (hB : ∀ B : Subgroup X, B ≤ (S : Subgroup X) → Nat.card B ≤ 9 →
      ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ B ≤ Subgroup.normalizer (V : Set X)) :
    Norm2 X := by
  intro P hP hcard
  have hconj_inj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : a ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun s : MulAut X => s g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  set I : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  have hIcard : Nat.card I = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv).symm
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hGpos : 0 < Nat.card (MulAut X) := Nat.card_pos
  have hcardI : Nat.card X * I.index = Nat.card (MulAut X) := by
    rw [← hIcard]
    exact Subgroup.card_mul_index I
  have hidx2 : I.index ≤ 2 := by
    have h2 : Nat.card X * I.index ≤ Nat.card X * 2 := by
      rw [hcardI]
      omega
    exact Nat.le_of_mul_le_mul_left h2 hXpos
  have hIpos : 0 < I.index := by
    rcases Nat.eq_zero_or_pos I.index with h0 | h0
    · rw [h0, mul_zero] at hcardI
      omega
    · exact h0
  have hInormal : I.Normal := by
    rcases (show I.index = 1 ∨ I.index = 2 by omega) with h1 | h1
    · exact Subgroup.normal_of_index_eq_one h1
    · exact Subgroup.normal_of_index_eq_two h1
  haveI := hInormal
  have hPI : ∀ σ ∈ P, σ ∈ I := by
    intro σ hσ
    obtain ⟨k, hk⟩ := hP ⟨σ, hσ⟩
    have hk' : σ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd3 : orderOf (σ : MulAut X ⧸ I) ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    have hdq : orderOf (σ : MulAut X ⧸ I) ∣ Nat.card (MulAut X ⧸ I) :=
      orderOf_dvd_natCard _
    have hqpos : 0 < Nat.card (MulAut X ⧸ I) := Nat.card_pos
    have hqle : Nat.card (MulAut X ⧸ I) ≤ 2 := hidx2
    have hle : orderOf (σ : MulAut X ⧸ I) ≤ 2 :=
      le_trans (Nat.le_of_dvd hqpos hdq) hqle
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd3
    have hj0 : j = 0 := by
      by_contra hj0
      have h3 : 3 ≤ 3 ^ j := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hj0)
      have h4 : 3 ≤ 2 := le_trans h3 (hj ▸ hle)
      norm_num at h4
    have hs1 : orderOf (σ : MulAut X ⧸ I) = 1 := by
      rw [hj, hj0, pow_zero]
    exact (QuotientGroup.eq_one_iff σ).mp (orderOf_eq_one_iff.mp hs1)
  obtain ⟨P₀, hP₀eq⟩ : ∃ P₀ : Subgroup X, P₀ = P.comap (MulAut.conj : X →* MulAut X) :=
    ⟨_, rfl⟩
  have hmemP₀ : ∀ x : X, x ∈ P₀ ↔ MulAut.conj x ∈ P := fun x => by
    rw [hP₀eq, Subgroup.mem_comap]
  have hPmap : P₀.map (MulAut.conj : X →* MulAut X) = P := by
    ext σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmemP₀ x).mp hx
    · intro hσ
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hPI σ hσ)
      exact Subgroup.mem_map.mpr ⟨x, (hmemP₀ x).mpr (by rw [hx]; exact hσ), hx⟩
  have hP₀3 : IsPGroup 3 P₀ := by
    rw [hP₀eq]
    exact hP.comap_of_injective _ hconj_inj
  have hcardP₀ : Nat.card P₀ ≤ 9 := by
    rw [← Subgroup.card_map_of_injective hconj_inj, hPmap]
    exact hcard
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP₀3
  haveI : Finite (Sylow 3 X) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q S
  have hgS : MulAut.conj g • (Q : Subgroup X) = (S : Subgroup X) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hconjS : ∀ x ∈ (Q : Subgroup X), g * x * g⁻¹ ∈ (S : Subgroup X) := by
    intro x hx
    rw [← hgS]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ hx
  obtain ⟨B, hBeq⟩ : ∃ B : Subgroup X, B = P₀.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  have hBS : B ≤ (S : Subgroup X) := by
    intro b hb
    rw [hBeq] at hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    exact hconjS x (hQ hx)
  have hinjg : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hBcard : Nat.card B ≤ 9 := by
    rw [hBeq, Subgroup.card_map_of_injective hinjg]
    exact hcardP₀
  obtain ⟨V, hVne, hV2, hVN⟩ := hB B hBS hBcard
  obtain ⟨V', hV'⟩ : ∃ V' : Subgroup X, ∀ y : X, y ∈ V' ↔ g * y * g⁻¹ ∈ V :=
    ⟨V.comap (MulAut.conj g).toMonoidHom, fun y => Iff.rfl⟩
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    apply hVne
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    have e1 : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
    have hy : g⁻¹ * v * g ∈ V' := by
      rw [hV', e1]
      exact hv
    rw [hbot] at hy
    have h1 : g⁻¹ * v * g = 1 := Subgroup.mem_bot.mp hy
    calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hV'2 : IsPGroup 2 V' := by
    intro y
    have hmem : g * (y : X) * g⁻¹ ∈ V := (hV' _).mp y.2
    obtain ⟨k, hk⟩ := hV2 ⟨g * (y : X) * g⁻¹, hmem⟩
    have hk' : (g * (y : X) * g⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [conj_pow] at hk'
    have hy : (y : X) ^ 2 ^ k = 1 := by
      calc (y : X) ^ 2 ^ k = g⁻¹ * (g * (y : X) ^ 2 ^ k * g⁻¹) * g := by group
        _ = 1 := by rw [hk']; group
    exact ⟨k, Subtype.ext (by simpa using hy)⟩
  have hV'inv : ∀ σ ∈ P, V'.map σ.toMonoidHom = V' := by
    intro σ hσ
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hPI σ hσ)
    have hxP₀ : x ∈ P₀ := (hmemP₀ x).mpr hσ
    have hbmem : g * x * g⁻¹ ∈ B := by
      rw [hBeq]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hxP₀
    have hbN : g * x * g⁻¹ ∈ Subgroup.normalizer (V : Set X) := hVN hbmem
    apply norm2_map_eq_of_forall_mem_iff
    intro y
    have key := (Subgroup.mem_normalizer_iff (H := V)).mp hbN (g * y * g⁻¹)
    have e : g * (MulAut.conj x y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      simp only [MulAut.conj_apply]
      group
    rw [hV', hV', e]
    exact key.symm
  exact ⟨V', hV'ne, hV'2, hV'inv⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
