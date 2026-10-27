module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Bot
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocPU
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace ProdSetup

variable {F : FanTree Γ G} {α β : V} {x : G} {H : Subgroup G} (S : ProdSetup F α β x H)

include S

theorem finite_prod : Finite ↥H := by
  have := F.loc_finite α
  exact Finite.of_injective (Subgroup.inclusion S.le_stab) (Subgroup.inclusion_injective _)

theorem normal_of_valence_ne_three (L : LocalFacts F) (hp3 : pval Γ α ≠ 3) :
    ∀ h ∈ H, h * x * h⁻¹ ∈ Subgroup.zpowers x := by
  have := S.finite_prod
  have hsub : nbrStab Γ G β ≤ H := S.nbrStab_le
  let e : ↥((nbrStab Γ G β).subgroupOf H) ≃* ↥(nbrStab Γ G β) :=
    Subgroup.subgroupOfEquivOfLe hsub
  obtain ⟨y, hy, hyo⟩ := F.exists_orderOf_eq_valence β
  have hp : (pval Γ α).Prime := F.valence_isPrime α
  have hp2 : pval Γ α ≠ 2 := by
    have e2 : pval Γ α = Nat.card (Γ.neighborSet α) := rfl
    rw [e2]
    rcases F.valence α with h | h <;> omega
  have hP : IsPGroup 2 ((nbrStab Γ G β).subgroupOf H) :=
    (F.nbrStab_isPGroup β).of_equiv e.symm
  have hcard : Nat.card H = pval Γ α * Nat.card ((nbrStab Γ G β).subgroupOf H) := by
    rw [S.card_eq L, Nat.card_congr e.toEquiv]
  have hno : ∀ K : Subgroup ↥H, K ≤ (nbrStab Γ G β).subgroupOf H →
      (K.subgroupOf ((nbrStab Γ G β).subgroupOf H)).Characteristic → K.Normal → K = ⊥ := by
    intro K hKP hchar hKn
    have hK' : K.map H.subtype ≤ nbrStab Γ G β := by
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hKP hk)
    have hxK := mem_normalizer_map_of_normal K S.x_mem
    have hconj : ∀ g ∈ MulAction.stabilizer G β, ∀ u ∈ K.map H.subtype,
        g * u * g⁻¹ ∈ K.map H.subtype := fun g hg =>
      conj_mem_map_of_characteristic hsub K hKP hchar
        (fun e' he' => F.conj_mem_nbrStab_of_stab hg he')
        (fun e' he' => by simpa using F.conj_mem_nbrStab_of_stab (inv_mem hg) he')
    have hyK : y ∈ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      refine ⟨hconj y hy u, fun hu => ?_⟩
      have := hconj y⁻¹ (inv_mem hy) _ hu
      simpa [mul_assoc] using this
    have hbot := S.toXSetup.eq_bot_of_normalized L hy hyo hK' hxK hyK
    exact (Subgroup.map_eq_bot_iff_of_injective K (Subgroup.subtype_injective H)).1 hbot
  have hx : orderOf (⟨x, S.x_mem⟩ : ↥H) = pval Γ α := by
    rw [Subgroup.orderOf_mk, S.ord]
  have hnormal := sylow_normal_of_no_char_normal hp hp2 hp3 hP hx hcard hno
  exact fun h hh => conj_mem_zpowers_of_normal S.x_mem hnormal hh

end ProdSetup

end CFSG.Quasithin.Fan86
