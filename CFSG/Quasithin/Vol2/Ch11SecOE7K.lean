module

public import CFSG.Quasithin.Background.E3ClosedTwo
public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Up

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isE_of_almostSimple_quot {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {Q' : Type} [Group Q'] [Finite Q'] {T A K : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hτK : E1.tauOf ⊤ T A ≤ K)
    (hSyl : IsSylowIn 2 (T ⊓ K) K) (ψ : ↥K →* Q') (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ψ.ker) {L' : Subgroup Q'} (hAS : SecE3.AlmostSimple L')
    (eL : ↥L' ≃* SL(2, F)) (hF : Nat.card F = 2 ^ n) (hB : (A.subgroupOf K).map ψ ≠ ⊥) :
    E1.IsE n ⊤ T A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτT : E1.tauOf ⊤ T A ≤ T := E1.tauOf_le _ _ _
  have hAτ : A ≤ E1.tauOf ⊤ T A := le_sup_left.trans (E1.le_tauOf hT hAT hA)
  have hAK : A ≤ K := hAτ.trans hτK
  refine ⟨le_top, le_inf hτT hτK, hSyl, Or.inr ?_⟩
  have hO2 : CFSG.Open.pCore 2 Q' = ⊥ :=
    le_bot_iff.mp (E3.pCore_two_le_solvableRadical.trans hAS.solvableRadical_eq_bot.le)
  have hZC : E1.IsTwoClosed ((CFSG.Open.pCore 2 Q').comap ψ) := by
    rw [hO2, MonoidHom.comap_bot]
    exact ⟨ψ.ker, ⟨le_rfl, hker, by rw [Subgroup.relIndex_self]; norm_num⟩,
      by rw [Subgroup.subgroupOf_self]; infer_instance⟩
  have hSylQ : IsSylowIn 2 ((T ⊓ K).subgroupOf K) ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (H := K) inf_le_right le_rfl).mpr hSyl
    rwa [Subgroup.subgroupOf_self] at h
  have hBS : A.subgroupOf K ≤ (T ⊓ K).subgroupOf K := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hAT hx, hAK hx⟩
  have hCS : ψ.ker ≤ (T ⊓ K).subgroupOf K := by
    have h2 := B6.pCoreOf_two_le_of_isSylowTwoOf hSylQ
    rw [E1.pCoreOf_top_eq] at h2
    exact (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hker).trans h2
  have hres : twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) :=
    E1.twoResidual_eq_perfectCore_of_surjective ψ hψ hSylQ
      (fun M hSM hM => by rwa [sup_eq_left.mpr (hCS.trans hSM)] at hM)
      (by rw [hAS.twoResidual_eq, hAS.perfectCore_eq])
  refine ⟨E1.eTwo_of_surjective ψ hψ hZC hSylQ.2.1 hBS hres (hAS.eTwo hB), ?_⟩
  rw [← E1.card_barRad_eq_of_surjective ψ hψ (E1.isSolvable_ker_of_isTwoClosed ψ hZC)]
  unfold E1.barRad
  rw [Subgroup.card_map_of_injective (by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hAS.solvableRadical_eq_bot])]
  have hAψ : IsElemAbelian 2 ((A.subgroupOf K).map ψ) := by
    refine E1.isElemAbelian_map' ψ ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := E1.commute_of_isElemAbelian hA (Subgroup.mem_subgroupOf.mp x.2)
        (Subgroup.mem_subgroupOf.mp y.2)
      simpa using this
    · have := hA.2 _ (Subgroup.mem_subgroupOf.mp hx)
      exact Subtype.ext (by simpa using this)
  exact SecE3.card_le_of_isElemAbelian_sl2 hAS eL hF hAψ

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
