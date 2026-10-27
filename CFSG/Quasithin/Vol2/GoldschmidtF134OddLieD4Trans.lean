module

public import CFSG.Quasithin.Vol2.F134LieD4
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Cont
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Elem
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5

public section

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieD4

namespace CFSG.Quasithin.H13.NQCore.D4


theorem coe_mem_graphFixedRootBorel_of_mem_normalizer {X : Type} [Group X] {K : Type} [Field K]
    {σ : K ≃+* K} {U : Subgroup X}
    (e : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (he : U.map e.toMonoidHom = (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {b : X} (hb : b ∈ Subgroup.normalizer (U : Set X)) :
    ((e b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
  have h1 : e b ∈ Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K
      σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Subgroup _) :
        Set _) := by
    rw [← he, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨b, hb, rfl⟩
  rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective]
  exact Subgroup.mem_inf.2 ⟨(e b).2, mem_normalizer_of_mem_normalizer_subgroupOf
    (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom) h1⟩

theorem commutator_mem_of_mem_normalizer {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (U : Sylow 2 X) :
    ∀ x ∈ Subgroup.normalizer ((U : Subgroup X) : Set X),
      ∀ y ∈ Subgroup.normalizer ((U : Subgroup X) : Set X),
        x * y * x⁻¹ * y⁻¹ ∈ (U : Subgroup X) := by
  obtain ⟨-, K, _, _, σ, -, -, e, he⟩ := exists_mulEquiv_map_eq hX U
  intro x hx y hy
  have h := commutator_mem_graphFixedPosUnipotent σ.surjective
    (coe_mem_graphFixedRootBorel_of_mem_normalizer e he hx)
    (coe_mem_graphFixedRootBorel_of_mem_normalizer e he hy)
  have h4 : e (x * y * x⁻¹ * y⁻¹) ∈ (graphFixedPosUnipotent TwistTag.D4 K
      σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [Subgroup.mem_subgroupOf]
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  rw [← he] at h4
  obtain ⟨z, hz, hze⟩ := h4
  rwa [← e.injective hze]

theorem le_normalizer_of_card_eq_prime {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (U : Sylow 2 X) {p a : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (ha : a = 2 ∨ a = 3) {H : Subgroup X} (hUH : (U : Subgroup X) ≤ H)
    (hH : Nat.card H = p ^ a * Nat.card (U : Subgroup X)) :
    H ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  obtain ⟨hn, K, _, _, σ, hK, hσc, e, he⟩ := exists_mulEquiv_map_eq hX U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set φ : X →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp e.toMonoidHom with hφ
  have hφi : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφr : (⊤ : Subgroup X).map φ = graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [hφ, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hφU : (U : Subgroup X).map φ = graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [hφ, ← Subgroup.map_map, he, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  obtain ⟨E, hEU, hE2, hE16⟩ := exists_isElemAbelian_le_sylow hX U
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 U.isPGroup'
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := S5.exists_proper_overgroup (holds_of_chevalleyExceptionalModel hX)
    (LieF4.isSylowOf_of_sylow U le_top) hUH (hEU.trans hUH) hE2 hE16 hp (by omega) (m := m)
    (a := a) (by rw [hH, hm, mul_comm]) (by omega)
  have hle : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ φ.range := by
    rw [← hφU]
    exact Subgroup.map_le_range φ _
  have hNcomap : (Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K))).comap φ = Subgroup.normalizer ((U : Subgroup X) : Set X) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range hle, ← hφU,
      Subgroup.comap_map_eq_self_of_injective hφi]
  have hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q.map φ := by
    intro b hb
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective] at hb
    obtain ⟨hbC, hbN⟩ := hb
    rw [← hφr] at hbC
    obtain ⟨x, -, rfl⟩ := hbC
    refine ⟨x, hNQ ?_, rfl⟩
    rw [← hNcomap]
    exact hbN
  have hHB := le_graphFixedRootBorel_of_card_eq_prime σ hn hK hσc hp hp5 ha (Q := Q.map φ)
    (H := H.map φ) hBQ
    ((Subgroup.map_le_range φ Q).trans (by rw [MonoidHom.range_eq_map, hφr]))
    (fun h => hQ (Subgroup.map_injective hφi (by rw [h, hφr]))) (Subgroup.map_mono hHQ)
    (by rw [← hφU]; exact Subgroup.map_mono hUH)
    (by rw [Subgroup.card_map_of_injective hφi, hH, ← Subgroup.card_map_of_injective hφi, hφU])
  intro x hx
  rw [← hNcomap]
  exact graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent (hHB ⟨x, hx, rfl⟩)

end CFSG.Quasithin.H13.NQCore.D4
