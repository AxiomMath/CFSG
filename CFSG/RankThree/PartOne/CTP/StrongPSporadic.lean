module

public import CFSG.RankThree.PartOne.CTP.StrongPAssembly
public import CFSG.RankThree.PartOne.CTP.StrongPFusion
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.CTP.SporadicFusion
public import CFSG.RankThree.PartOne.CTP.SporadicFusionSuz
public import CFSG.RankThree.PartOne.CTP.SporadicFusionTh
public import CFSG.RankThree.PartOne.CTP.StrongPOuter
public import CFSG.RankThree.PartOne.Census3.NativeForm

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Blueprint TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def FusionGeneration (s : SporadicName) (p : ℕ) : Prop :=
  Fus.FusionGenerationOf (NativeSporadic.Carrier s) p

section Noncomm

theorem hasNoncommPair_carrier
    {s : SporadicName} {p : ℕ} (h : SporadicPairNC s p) :
    HasNoncommPair p (NativeSporadic.Carrier s) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hasNoncommPair_J4
  · exact hasNoncommPair_McL
  · exact hasNoncommPair_Ly
  · exact hasNoncommPair_HS
  · exact hasNoncommPair_He
  · exact hasNoncommPair_Ru
  · exact hasNoncommPair_ON
  · exact hasNoncommPair_Co3
  · exact hasNoncommPair_Co2
  · exact hasNoncommPair_HN
  · exact hasNoncommPair_Th

end Noncomm

section Out

variable {H : Type*} [Group H]

theorem card_quotient_dvd_outer [Finite H] (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) :
    Nat.card (H ⧸ S) ∣ Nat.card (Outer ↥S) := by
  let f : H ⧸ S →* Outer ↥S := QuotientGroup.lift S (outerHom S)
    (fun _ hg => (MonoidHom.mem_ker (f := outerHom S)).mp ((ker_outerHom S hSc).symm ▸ hg))
  have hf : Function.Injective f := quotientOuterHom_injective S hSc
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact Subgroup.card_subgroup_dvd_card f.range

end Out

section Fusion

theorem false_of_fusionGeneration {s : SporadicName} {p : ℕ} (hp : p.Prime)
    (hFG : FusionGeneration s p) {H : Type} [Group H] [Finite H] (S : Subgroup H) [S.Normal]
    (e : ↥S ≃* NativeSporadic.Carrier s) {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, Γ, hEp, hE1, hΓ, hfus⟩ := hFG
  let φ : NativeSporadic.Carrier s →* H := S.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := S.subtype_injective.comp e.symm.injective
  refine hY.false_of_fusion_generation S (E := E.map φ) ?_ (hEp.map φ) ?_ (Γ := φ '' Γ) ?_ ?_
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · intro h
    exact hE1 ((Subgroup.map_eq_bot_iff_of_injective _ hφ).mp h)
  · intro x hx
    rw [← MonoidHom.map_closure, hΓ]
    exact ⟨e ⟨x, hx⟩, Subgroup.mem_top _, by simp [φ]⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨e0, he0, he1, hge⟩ := hfus g hg
    refine ⟨φ e0, Subgroup.mem_map_of_mem φ he0, fun h => he1 (hφ (by rwa [map_one])), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem φ hge

end Fusion

theorem sporadicStrongPInput_of_inputs
    (hLeTwo : SporadicOuterOrderLeTwoSimple) :
    SporadicStrongPInput := by
  have hOut := sporadicOuterNoLargePrime_of_leTwo hLeTwo
  have hAb : ∀ (s : SporadicName) (p : ℕ), SporadicPairAb s p → FusionGeneration s p := by
    rintro s p (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact fusionGenerationOf_J2
    · exact fusionGenerationOf_He
    · exact fusionGenerationOf_Suz
    · exact fusionGenerationOf_Th
  intro p hp hp5 H _ _ S hSn hSs hnonab ⟨s, hs, ⟨e⟩⟩ hSc Y hY P hP hab hcard
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup s.Group := MulEquiv.isSimpleGroup e.symm
  obtain ⟨φ⟩ := Census3.nonempty_carrier_mulEquiv_of_mem hs
  let e' : ↥S ≃* NativeSporadic.Carrier s := e.trans φ.symm
  by_cases hpair : SporadicPair s p
  · rcases hpair with hnc | hab2
    · have hpair' : HasNoncommPair p (NativeSporadic.Carrier s) := hasNoncommPair_carrier hnc
      exact false_of_hasNoncommPair S hP hab
        (hpair'.map e'.symm.toMonoidHom e'.symm.injective)
    · exact false_of_fusionGeneration hp (hAb s p hab2) S e' hY
  · have hsq : ¬ p ^ 2 ∣ Nat.card ↥S := by
      intro h
      refine hpair (sporadicPair_of_sq_dvd hs hp hp5 ?_)
      rwa [← Nat.card_congr e'.toEquiv]
    have hOut' := hOut s hs ↥S hnonab ⟨e'⟩ p hp hp5
    have hnd : ¬ p ∣ Nat.card (H ⧸ S) := fun h => hOut' (h.trans (card_quotient_dvd_outer S hSc))
    have hPS : P ≤ S := le_of_isPGroup_of_not_dvd_card_quotient hP.2.1 hnd
    obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
    have hPdvd : Nat.card P ∣ Nat.card S := Subgroup.card_dvd_of_le hPS
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      refine hsq ((pow_dvd_pow p hk2).trans ?_)
      rwa [hk] at hPdvd
    have hΩ : Nat.card (omegaOne p P) ≤ p := by
      calc Nat.card (omegaOne p P) ≤ Nat.card P := Subgroup.card_le_of_le (omegaOne_le P)
        _ = p ^ k := hk
        _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
        _ = p := pow_one p
    have hp2 : p < p ^ 2 := by nlinarith [hp.one_lt]
    have hp3 : p < p ^ 3 := by nlinarith [hp.one_lt]
    rcases hcard with h | h <;> omega

end CFSG.RankThree.PartOne.CTP
