module

public import CFSG.Quasithin.EmptyFaithful.S146zYFD2
public import CFSG.Quasithin.Vol2.F134LieD4
public import CFSG.Quasithin.H13.NQCoreP134Group

public section

namespace CFSG.Quasithin.S146zY

namespace D4Five

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.ABGLocalTools CFSG.LieType.BorelTits CFSG.Quasithin.F134.LieD4

section Models


theorem le_normalizer_of_mul_twentyFive {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (hn2 : 2 ≤ n) (U : Sylow 2 X)
    {P : Subgroup X} (hP : Nat.card P = 25)
    (hmul : ∀ u ∈ (U : Subgroup X), ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ (U : Subgroup X), u * x = y * s) :
    P ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
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
  have hH : Nat.card (P ⊔ (U : Subgroup X) : Subgroup X) = 25 * Nat.card (U : Subgroup X) := by
    have hcop : Nat.Coprime (Nat.card P) (Nat.card (U : Subgroup X)) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 U.isPGroup'
      rw [hP, hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    rw [CFSG.Quasithin.H13.NQCore.card_sup_eq_of_mul' hcop hmul, hP]
  have hcardU : Nat.card (U : Subgroup X) = (2 ^ n) ^ 12 := by
    rw [← Subgroup.card_map_of_injective hφi, hφU,
      CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedPosUnipotent σ.surjective
        (CFSG.Timmesfeld.ExceptionalOrders.card_orbitField Nat.prime_two hn hK hσc),
      CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_twistedD4]
  have hrel : ((U : Subgroup X).subgroupOf (P ⊔ (U : Subgroup X))).index = 25 := by
    have h := Subgroup.relIndex_mul_card (U : Subgroup X) (P ⊔ (U : Subgroup X))
    rw [inf_eq_left.2 le_sup_right, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := exists_proper_overgroup_of_not_dvd
    (holds_of_chevalleyExceptionalModel hX)
    (CFSG.Quasithin.F134.LieF4.isSylowOf_of_sylow U le_top) le_sup_right (by
      rw [hrel, hH, hcardU]
      intro hdvd
      have h24 : 2 ^ 24 ∣ Nat.factorial 25 := by
        refine Dvd.dvd.trans ?_ ((Dvd.intro_left 25 rfl).trans hdvd)
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      norm_num [Nat.factorial] at h24)
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
  have hHB := le_graphFixedRootBorel_of_card_twentyFive σ hn hK hσc (Q := Q.map φ)
    (H := (P ⊔ (U : Subgroup X)).map φ) hBQ
    ((Subgroup.map_le_range φ Q).trans (by rw [MonoidHom.range_eq_map, hφr]))
    (fun h => hQ (Subgroup.map_injective hφi (by rw [h, hφr]))) (Subgroup.map_mono hHQ)
    (by rw [← hφU]; exact Subgroup.map_mono le_sup_right)
    (by rw [Subgroup.card_map_of_injective hφi, hH, ← Subgroup.card_map_of_injective hφi, hφU])
  intro x hx
  have hxB := hHB ⟨x, Subgroup.mem_sup_left hx, rfl⟩
  rw [← hNcomap]
  exact graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hxB

end Models

end D4Five

end CFSG.Quasithin.S146zY
