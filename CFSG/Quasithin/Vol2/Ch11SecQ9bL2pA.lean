module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bJ1
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Vol2.Ch11SecA12Cart
public import CFSG.Quasithin.Vol2.Ch11SecSPGL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

namespace C11P9B

theorem inf_pCoreOf_le {H : Subgroup G} (hKH : K ≤ H) :
    K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
  exact (le_inf Subgroup.le_normalizer
    (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem orderOf_eq_three_of_mem_xOne (hC : CartanFacts) (hF : Facts12) (hN : NatFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X) {x : G} (hx : x ∈ xOne X (LOf L V₁))
    (hx1 : x ≠ 1) : orderOf x = 3 := by
  have hcard := card_xOne hC hF hN h1102 h hV₁ hV₂ hX
  have hdvd : orderOf x ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard (xOne X (LOf L V₁)) hx
    rwa [hcard] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h3

theorem commutator_mem_of_L2p (hFb : Facts12b) (hC : CartanFacts) (hF : Facts12)
    (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hV₂ : IsVi T L I 2 2 V₂) (hX : IsCartanX T L X)
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K) (hS : ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    {x : G} (hx : x ∈ xOne X (LOf L V₁)) {k : G} (hk : k ∈ K) :
    x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX1K : xOne X (LOf L V₁) ≤ Subgroup.normalizer (K : Set G) :=
    (xOne_le_normalizer_V1 hN h1102 h hV₁ hX).trans hNK
  have hwK : x * k * x⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hX1K hx) k).mp hk) (K.inv_mem hk)
  by_cases hx1 : x = 1
  · subst hx1
    simp
  have hxo := orderOf_eq_three_of_mem_xOne hC hF hN h1102 h hV₁ hV₂ hX hx hx1
  set H := K ⊔ xOne X (LOf L V₁) with hH
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hX1K)
  have hSn : (modO2Image H K).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := modO2Image_equiv le_sup_left hKn
  obtain ⟨p, hp, hp11, hPSL⟩ := hS
  have hL₁H : LOf L V₁ ≤ H := hLK.trans le_sup_left
  have hBS : modO2Image H (LOf L V₁) ≤ modO2Image H K :=
    Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr (hLK (Subgroup.mem_subgroupOf.mp hy))
  have hB4 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image H (LOf L V₁)) ⧸ CFSG.pCore 2 ↥(modO2Image H (LOf L V₁)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF4, ⟨e₁⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
    obtain ⟨e₂⟩ := modO2Image_quotEquiv hL₁H
    exact ⟨F, inferInstance, inferInstance, hF4.trans (by norm_num), ⟨e₂.symm.trans e₁⟩⟩
  have hxH : x ∈ H := Subgroup.mem_sup_right hx
  have hxbo : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simp [← hxo])
      rw [this, map_one]
    · intro h0
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, h0⟩
      have hj' : x ^ 2 ^ j = 1 := by
        simpa using congrArg (fun y => ((y : ↥H) : G)) (congrArg Subtype.val hj)
      have := orderOf_dvd_of_pow_eq_one hj'
      rw [hxo] at this
      exact absurd (Nat.prime_three.dvd_of_dvd_pow this) (by norm_num)
  have hcomm := hFb.centL2p _ (modO2Image H K) hSn ⟨p, hp, hp11, IsPSL.of_mulEquiv e hPSL⟩ _ hBS
    hB4 _ hxbo (mk_mem_sectionCentralizer hL₁H hxH hx.2)
  have hk' := hcomm (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, Subgroup.mem_sup_left hk⟩)
    ⟨⟨k, Subgroup.mem_sup_left hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have hw : (⟨x, hxH⟩ : ↥H) * ⟨k, Subgroup.mem_sup_left hk⟩ * (⟨x, hxH⟩ : ↥H)⁻¹ *
      (⟨k, Subgroup.mem_sup_left hk⟩ : ↥H)⁻¹ ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥H), ← QuotientGroup.mk'_apply,
      map_mul, map_mul, map_mul, map_inv, map_inv, hk']
    group
  have hwH : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
    rw [pCoreOf_two_eq_map]
    exact ⟨_, hw, rfl⟩
  exact inf_pCoreOf_le le_sup_left ⟨hwK, hwH⟩

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
