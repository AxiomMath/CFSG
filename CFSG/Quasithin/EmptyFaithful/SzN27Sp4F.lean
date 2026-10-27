module

public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4D
public import CFSG.Quasithin.EmptyFaithful.SzN27S3

public section

namespace CFSG.Quasithin.SzN27

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj uElt_zero_eq_one card_and_isSylowTwoOf_antiUnipotent
  mem_antiUnipotentCenter_iff_central antiProjEquiv aut_eq_conj_mul_pow)
open CFSG.QuasithinUnique.Fin257.Sp4 (dSp dSp_conj_uElt)

namespace Sp4

variable {K : Type} [Field K] [CharP K 2]

theorem U_le_of_y [Finite K] (hK : 4 ≤ Nat.card K) {V H : Subgroup (antiSp K)}
    (hV4 : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1) (hVU : V ≤ antiUnipotent K)
    (hUV : antiUnipotent K ≤ Subgroup.normalizer (V : Set (antiSp K)))
    (hUH : antiUnipotent K ≤ Subgroup.normalizer (H : Set (antiSp K)))
    {y x : antiSp K} (hyH : y ∈ H) (hyV : y ∈ Subgroup.normalizer (V : Set (antiSp K)))
    (hynt : ¬ ∀ v ∈ V, y * v = v * y) (hxZ : x ∈ antiUnipotentCenter K) (hx1 : x ≠ 1)
    (hxy : y * x = x * y) : antiUnipotent K ≤ H := by
  classical
  have hVz : V ≤ antiUnipotentCenter K := V_le_center hV4 hV2 hVU hUV hK
  obtain ⟨b₀, c₀, rfl⟩ := hxZ
  have hup := y_upper hVz hyV hynt hx1 hxy
  obtain ⟨u₀, s, t, hu₀, hy, -, -⟩ := exists_unip_dSp_of_upper hup
  have hxcon : dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹ =
      uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 := by
    rw [dSp_conj_uElt]
    simp
  have hxx : dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹ = uElt 0 b₀ c₀ 0 := by
    have hcen : uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀ =
        u₀ * uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 :=
      antiUnipotentCenter_comm ⟨_, _, rfl⟩ hu₀
    have h1 : y * uElt 0 b₀ c₀ 0 * y⁻¹ = uElt 0 b₀ c₀ 0 := by
      rw [hxy]
      group
    rw [hy] at h1
    have h3 : u₀ * (dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹) * u₀⁻¹ = uElt 0 b₀ c₀ 0 := by
      calc u₀ * (dSp s t * uElt 0 b₀ c₀ 0 * (dSp s t)⁻¹) * u₀⁻¹
          = u₀ * dSp s t * uElt 0 b₀ c₀ 0 * (u₀ * dSp s t)⁻¹ := by group
        _ = uElt 0 b₀ c₀ 0 := h1
    rw [hxcon] at h3 ⊢
    refine (show uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 =
        u₀ * uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀⁻¹ from ?_).trans h3
    calc uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0
        = uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀ * u₀⁻¹ := by group
      _ = u₀ * uElt 0 ((s : K) * t * b₀) ((s : K) ^ 2 * c₀) 0 * u₀⁻¹ := by rw [hcen]
  obtain ⟨-, hxb, hxc, -⟩ := uElt_inj (hxcon.symm.trans hxx)
  have hx0 : b₀ ≠ 0 ∨ c₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact hx1 uElt_zero_eq_one
  push Not at hynt
  obtain ⟨v, hvV, hne⟩ := hynt
  obtain ⟨b, c, rfl⟩ := hVz hvV
  have hvd : dSp s t * uElt 0 b c 0 * (dSp s t)⁻¹ ≠ uElt 0 b c 0 := by
    intro h
    apply hne
    have hcen : u₀ * uElt 0 b c 0 = uElt 0 b c 0 * u₀ :=
      (antiUnipotentCenter_comm ⟨b, c, rfl⟩ hu₀).symm
    calc y * uElt 0 b c 0 = u₀ * (dSp s t * uElt 0 b c 0 * (dSp s t)⁻¹) * dSp s t := by
          rw [hy]
          group
      _ = u₀ * uElt 0 b c 0 * dSp s t := by rw [h]
      _ = uElt 0 b c 0 * u₀ * dSp s t := by rw [hcen]
      _ = uElt 0 b c 0 * y := by
          rw [hy]
          group
  have hv : (s : K) * t * b ≠ b ∨ (s : K) ^ 2 * c ≠ c := by
    by_contra hcon
    push Not at hcon
    apply hvd
    rw [dSp_conj_uElt]
    simp only [mul_zero]
    rw [hcon.1, hcon.2]
  obtain ⟨ht1, hst⟩ := char_conditions hx0 hxb hxc hv
  have hyH' : u₀ * dSp s t ∈ H := by
    rw [← hy]
    exact hyH
  obtain ⟨hα, hδ⟩ := coords_of_y hUH hu₀ hyH' hst ht1
  exact U_le_of_coords hK hα hδ

omit [CharP K 2] in
theorem outCyclic [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    OutCyclic (antiSp K) := by
  refine ⟨CFSG.QuasithinUnique.Setup.X7b.conj_injective, ⟨QuotientGroup.mk (minorAut K), fun x => ?_⟩⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, j, -, hα⟩ := aut_eq_conj_mul_pow hn hK α
  refine Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), ?_⟩
  have h1 : (QuotientGroup.mk (MulAut.conj g) : Outer (antiSp K)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  rw [hα, QuotientGroup.mk_mul, h1, one_mul, zpow_natCast, QuotientGroup.mk_pow]

end Sp4

section Transport

open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14

theorem outCyclic_of_sp4 {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) : OutCyclic X := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  exact (Sp4.outCyclic (by omega) hcard).of_mulEquiv (e.trans (antiProjEquiv K).symm)

theorem sp4_sylow_le {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f) {T V H : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hVT : V ≤ T) (hV4 : Nat.card V = 4) (hV2 : ∀ v ∈ V, v * v = 1)
    (hTV : T ≤ Subgroup.normalizer (V : Set X)) (hTH : T ≤ Subgroup.normalizer (H : Set X))
    {y z : X} (hyH : y ∈ H) (hyV : y ∈ Subgroup.normalizer (V : Set X))
    (hynt : ¬ ∀ v ∈ V, y * v = v * y) (hzT : z ∈ T) (hz1 : z ≠ 1)
    (hzc : ∀ t ∈ T, z * t = t * z) (hyz : y * z = z * y) : T ≤ H := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let ψ : X ≃* antiSp K := e.trans (antiProjEquiv K).symm
  have hT1 : IsSylowTwoOf (T.map ψ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map ψ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := ψ.toMonoidHom) ψ.bijective]
    exact hi
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hT1
    (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  let Φ : X ≃* antiSp K := ψ.trans (MulAut.conj g)
  have hΦT : T.map Φ.toMonoidHom = antiUnipotent K := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hΦU : ∀ t ∈ T, Φ t ∈ antiUnipotent K := fun t ht => hΦT ▸ ⟨t, ht, rfl⟩
  have hUH := Sp4.U_le_of_y hK4 (V := V.map Φ.toMonoidHom) (H := H.map Φ.toMonoidHom)
    ((Nat.card_congr (V.equivMapOfInjective Φ.toMonoidHom Φ.injective).toEquiv).symm.trans hV4)
    (by
      rintro _ ⟨v, hv, rfl⟩
      show Φ v * Φ v = 1
      rw [← map_mul, hV2 v hv, map_one])
    (hΦT ▸ Subgroup.map_mono hVT)
    (by
      rw [← hΦT]
      rintro _ ⟨t, ht, rfl⟩
      exact (R3c11.mem_normalizer_map_equiv_iff Φ V t).mpr (hTV ht))
    (by
      rw [← hΦT]
      rintro _ ⟨t, ht, rfl⟩
      exact (R3c11.mem_normalizer_map_equiv_iff Φ H t).mpr (hTH ht))
    (y := Φ y) (x := Φ z) ⟨y, hyH, rfl⟩ ((R3c11.mem_normalizer_map_equiv_iff Φ V y).mpr hyV)
    (by
      intro hall
      apply hynt
      intro v hv
      apply Φ.injective
      rw [map_mul, map_mul]
      exact hall (Φ v) ⟨v, hv, rfl⟩)
    ((mem_antiUnipotentCenter_iff_central _).mpr ⟨hΦU z hzT, by
      intro u hu
      rw [← hΦT] at hu
      obtain ⟨t, ht, rfl⟩ := hu
      show Φ z * Φ t = Φ t * Φ z
      rw [← map_mul, ← map_mul, hzc t ht]⟩)
    (fun h1 => hz1 (Φ.injective (by rw [h1, map_one])))
    (by rw [← map_mul, ← map_mul, hyz])
  intro t ht
  obtain ⟨h', hh', hht⟩ := hUH (hΦU t ht)
  have : h' = t := Φ.injective hht
  rwa [this] at hh'

end Transport

end CFSG.Quasithin.SzN27
