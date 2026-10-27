module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem barSituation_of_hyp711 {V H E : Subgroup G} (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) :
    BarSituation X (barSub (kSub V H E) φ V) where
  elemAbelian := isElemAbelian_barSub h.elemAbelian φ
  normalClosure_eq_top := normalClosure_barSub_eq_top h hφ
  pCore_eq_bot := pCore_eq_bot_of_isBarMap hφ
  oddTransp hS := by
    rw [← barSet_dSet_eq h.toHyp73 h.transitive hφ]
    exact isOddTransp_barSet h.toHyp73 h.transitive hφ hS

theorem centralInSylow_of_hyp83 {V H T : Subgroup G} (h : Hyp83 V H T)
    (hKT : H = kGenIn V H ⊔ T) {X : Type} [Group X] {φ : ↥(ambK V H T) →* X}
    (hφ : IsBarMap (ambK V H T) (pCoreOf 2 (ambK V H T)) φ)
    (hS : Nat.card (barSub (ambK V H T) φ (ambV V H)) = 2) :
    CentralInSylow X (barSub (ambK V H T) φ (ambV V H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : Hyp83 (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H) := AmbientH.hyp83 h
  have hT : IsSylowIn 2 (T.subgroupOf H) (⊤ : Subgroup ↥H) := hh.sylow_H
  have hKN : ((ambK V H T).subgroupOf (⊤ : Subgroup ↥H)).Normal :=
    hh.kSub_normal fun _ _ => le_top
  have hSyl : IsSylowIn 2 (T.subgroupOf H ⊓ ambK V H T) (ambK V H T) := hT.inf_normal le_top hKN
  let P₀ : Sylow 2 ↥(ambK V H T) := hSyl.toSylow
  let P : Sylow 2 X := P₀.mapSurjective hφ.surjective
  have hVK : V.subgroupOf H ≤ ambK V H T := le_kSub hh.mem_omegaSet_self
  have key : ∀ p ∈ (P : Subgroup X), ∀ s ∈ barSub (ambK V H T) φ (ambV V H),
      p * s * p⁻¹ ∈ barSub (ambK V H T) φ (ambV V H) := by
    intro p hp s hs
    obtain ⟨k, hk, rfl⟩ := hp
    obtain ⟨v, hv, rfl⟩ := hs
    refine ⟨k * v * k⁻¹, ?_, by simp⟩
    have hkT : ((k : ↥(ambK V H T)) : ↥H) ∈ T.subgroupOf H :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
    have hvV : ((v : ↥(ambK V H T)) : ↥H) ∈ V.subgroupOf H := Subgroup.mem_subgroupOf.1 hv
    exact Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (hh.T_le_normalizer hkT) _).1 hvV)
  refine ⟨P, ?_, ?_⟩
  · refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.2 ⟨hh.le_T (Subgroup.mem_subgroupOf.1 hx), x.2⟩
  · intro s hs p hp
    by_cases hs1 : s = 1
    · rw [hs1, one_mul, mul_one]
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(barSub (ambK V H T) φ (ambV V H)))).1 hS
      have h1 : (⟨s, hs⟩ : ↥(barSub (ambK V H T) φ (ambV V H))) =
          ⟨p * s * p⁻¹, key p hp s hs⟩ := by
        refine (hy _ ?_).trans (hy _ ?_).symm
        · exact fun h' => hs1 (congrArg Subtype.val h')
        · intro h'
          apply hs1
          have := congrArg Subtype.val h'
          simpa using this
      have h2 := congrArg Subtype.val h1
      simp only at h2
      calc s * p = (p * s * p⁻¹) * p := by rw [← h2]
        _ = p * s := by group

end CFSG.LocalAnalysis.WeakClosure81

end
