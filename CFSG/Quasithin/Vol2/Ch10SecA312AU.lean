module

public import CFSG.Quasithin.Vol2.Ch10SecA312AW
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentRu
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.Vol2.Ch10SecA312AA

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

theorem false_of_ru_psl32
    {T B : Subgroup X} (hT : IsPGroup 2 ↥T)
    (hRu : IsSporadic .Ru ↥(⊤ : Subgroup X)) (hY : IsPSL 3 2 1 (ModO2 B))
    (hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11) {z : X} (hzT : z ∈ T) (hz1 : z ≠ 1)
    (hzB : ∀ b ∈ B, z * b = b * z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hRu
  let ψ : X ≃* ↥CFSG.Sporadic.RuSchreier.ruP :=
    (Subgroup.topEquiv.symm.trans e).trans CFSG.Sporadic.RuSchreier.ruEquivP
  obtain ⟨k, hk1, hk2⟩ := exists_pow_involution hT (γ := ⟨z, hzT⟩)
    (fun h => hz1 (congrArg Subtype.val h))
  have hu1 : z ^ k ≠ 1 := fun h => hk1 (Subtype.ext (by simpa using h))
  have hu2 : z ^ k * z ^ k = 1 := by simpa using congrArg Subtype.val hk2
  have hord : orderOf (z ^ k) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have htord : orderOf ((ψ (z ^ k) : ↥CFSG.Sporadic.RuSchreier.ruP) :
      Equiv.Perm (Fin 4060)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
  have hcard := CFSG.QuasithinUnique.Id2519.MathNoLayer.ru_centralizer_card (ψ (z ^ k)).2 htord
  have hinj : Nat.card ↥B ≤ Nat.card ↥(CFSG.Sporadic.RuSchreier.ruP ⊓
      Subgroup.centralizer {((ψ (z ^ k) : ↥CFSG.Sporadic.RuSchreier.ruP) :
        Equiv.Perm (Fin 4060))}) := by
    refine Nat.card_le_card_of_injective (fun b => ⟨((ψ b : ↥CFSG.Sporadic.RuSchreier.ruP) :
      Equiv.Perm (Fin 4060)), (ψ b).2, ?_⟩) ?_
    · have hbu : (b : X) * z ^ k = z ^ k * b := (Commute.pow_left (hzB b b.2) k).eq.symm
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hbu]
    · intro a b h
      have h' : ((ψ a : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060)) = ψ b :=
        congrArg (fun x : ↥(CFSG.Sporadic.RuSchreier.ruP ⊓ Subgroup.centralizer
          {((ψ (z ^ k) : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060))}) =>
          (x : Equiv.Perm (Fin 4060))) h
      exact Subtype.ext (ψ.injective (Subtype.ext h'))
  have hQ : Nat.card (ModO2 B) = 168 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hY).1 rfl]
    decide
  have hB : Nat.card ↥B = 344064 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), hO2,
      show Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 168 from hQ]
    norm_num
  omega

theorem a312ZCentRu_of
    (hA5 : A312ZCentRestRuA5) : A312ZCentRu := by
  intro X _ _ T B hcase hc
  obtain ⟨h5 | h3, hO2, hRu⟩ := hcase
  · exact hA5 X T B h5 hO2 hRu hc
  · obtain ⟨-, -, -, hT, -, -, -, -, ⟨z, hzT, hz1, -, hzB⟩, -⟩ := hc
    exact false_of_ru_psl32 hT.isPGroup hRu h3 hO2 hzT hz1 hzB

end CFSG.Quasithin.Vol2.Ch10.A312A
