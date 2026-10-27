module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley

namespace OrdPInnerExc

theorem coprime_of_center_eq_bot {U : Type} [Group U] (h : Subgroup.center U = ⊥) (p : ℕ) :
    Nat.Coprime (Nat.card (Subgroup.center U)) p := by
  rw [h, Subgroup.card_bot]
  exact Nat.coprime_one_left p

end OrdPInnerExc

section Univ

@[expose] def GGOrdPToralUnivAt (t : StatedLieTag) : Prop :=
  ∀ n f p : ℕ, StatedLieAdmissible t n 2 f → p.Prime → p ≠ 2 → ¬ GGOutdiagPrimeConfig p t n f →
    (∃ A : Subgroup (ggU t n f).K, IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (ggU t n f).K p

namespace OrdPInnerExc

theorem ggOrdPInnerConjAt_of_parts {t : StatedLieTag}
    (hin : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
      (ψ : (ggU t n f).K →* G), GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
      ¬ GGOutdiagPrimeConfig p t n f → ∀ c ∈ Subgroup.normalizer (G₀ : Set G), c ^ p = 1 →
        GGPsiInnerDiag (ggU t n f).D ψ c → c ∈ G₀)
    (hcop : ∀ n f p : ℕ, StatedLieAdmissible t n 2 f → p.Prime → ¬ GGOutdiagPrimeConfig p t n f →
      Nat.Coprime (Nat.card (Subgroup.center (ggU t n f).K)) p)
    (hT : GGOrdPToralUnivAt t) : GGOrdPInnerConjAt t := by
  intro G _ _ p Bs G₀ n f ψ hS h4 hout y hyN hyo hyi
  obtain ⟨⟨hadm, -⟩, ⟨-, hker⟩, -, -⟩ := hS.presents
  have hp := hS.prime
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hkc : Nat.Coprime (Nat.card ψ.ker) p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hker) (hcop n f p hadm hp hout)
  have hBs : Bs ≤ G₀ := fun b hb => hin G p Bs G₀ n f ψ hS hout b (hS.2.2.2.1.1 hb)
    (hS.2.2.2.1.2.1.2 b hb) (hS.innerDiag b hb)
  have hy := hin G p Bs G₀ n f ψ hS hout y hyN hyp hyi
  exact exists_conj_of_toralMax hS hker hkc hBs
    (hT n f p hadm hp hS.1.2 hout (exists_elemAbelian_four hS h4 hker hkc hBs)) hy hyp

theorem inner_of_psiDiagInner {t : StatedLieTag}
    (hD : ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
      GGPresentsG0 G₀ (ggU t n f).D t n f ψ → ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU t n f).D ψ c → ∃ g ∈ G₀, c * g ∈ Subgroup.centralizer (G₀ : Set G))
    (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) (hS : GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ)
    (_ : ¬ GGOutdiagPrimeConfig p t n f) (c : G) (hc : c ∈ Subgroup.normalizer (G₀ : Set G))
    (_ : c ^ p = 1) (hci : GGPsiInnerDiag (ggU t n f).D ψ c) : c ∈ G₀ := by
  obtain ⟨g, hg, hcg⟩ := hD G n f ψ G₀ hS.presents c hc hci
  exact mem_of_mul_mem_centralizer hS.centralizer_eq_bot hg hcg

end OrdPInnerExc

end Univ

section Split

namespace OrdPInnerExc


theorem isElemAbelian_torusPow (τ : Tag) (K : Type) [Field K] (p : ℕ) :
    IsElemAbelian p (TableBExc.torusPow τ K p) :=
  ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (mul_comm_of_mem_diagonalGroup
    (torusGroup_le_diagonalGroup a.2.1) (torusGroup_le_diagonalGroup b.2.1)))⟩⟩,
    fun _ hx => hx.2⟩

theorem ggOrdPToralMax_adj {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index) :
    GGOrdPToralMax (adjointGroup τ K) p := by
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  exact ggOrdPToralMax_of_conj_le (isElemAbelian_torusPow τ K p)
    fun A hA => TableBExc.exists_conj_le_torusPow hp hidx hA


theorem ggOrdPToralMax_F4_split {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) : GGOrdPToralMax (adjointGroup .F4 K) p :=
  ggOrdPToralMax_adj hp (TableBF4.not_dvd_index_torusGroup hp hp5 hpq)

theorem ggOrdPToralMax_E8_split {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1) : GGOrdPToralMax (adjointGroup .E8 K) p :=
  ggOrdPToralMax_adj hp (TableBExc.not_dvd_index_torusGroup_E8 hp hp11 hpq)

theorem ggOrdPToralMax_E7_split {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    GGOrdPToralMax (adjointGroup .E7 K) p :=
  ggOrdPToralMax_adj hp (TableBExc.not_dvd_index_torusGroup_E7 hp hp11 hpq)

end OrdPInnerExc

end Split

section Tags


@[expose] def GGOrdPToralF4Rest : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ (5 ≤ p ∧ p ∣ 2 ^ f - 1) →
    (∃ A : Subgroup (adjointGroup .F4 (GaloisField 2 f)), IsElemAbelian p A ∧
      p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (adjointGroup .F4 (GaloisField 2 f)) p

@[expose] def GGOrdPToralE7Rest : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ (11 ≤ p ∧ p ∣ 2 ^ f - 1) →
    (∃ A : Subgroup (adjointGroup .E7 (GaloisField 2 f)), IsElemAbelian p A ∧
      p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (adjointGroup .E7 (GaloisField 2 f)) p

@[expose] def GGOrdPToralE8Rest : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → ¬ (11 ≤ p ∧ p ∣ 2 ^ f - 1) →
    (∃ A : Subgroup (adjointGroup .E8 (GaloisField 2 f)), IsElemAbelian p A ∧
      p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (adjointGroup .E8 (GaloisField 2 f)) p

theorem ggOrdPToralUnivAt_F4_of_rest (h : GGOrdPToralF4Rest) : GGOrdPToralUnivAt .F4 := by
  intro n f p hadm hp hp2 _ hA
  have hf : 1 ≤ f := hadm.2.1
  by_cases hs : 5 ≤ p ∧ p ∣ 2 ^ f - 1
  · have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    exact OrdPInnerExc.ggOrdPToralMax_F4_split hp hs.1 (hK ▸ hs.2)
  · exact h f p hf hp hp2 hs hA

theorem ggOrdPToralUnivAt_E8_of_rest (h : GGOrdPToralE8Rest) : GGOrdPToralUnivAt .E8 := by
  intro n f p hadm hp hp2 _ hA
  have hf : 1 ≤ f := hadm.2.1
  by_cases hs : 11 ≤ p ∧ p ∣ 2 ^ f - 1
  · have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    exact OrdPInnerExc.ggOrdPToralMax_E8_split hp hs.1 (hK ▸ hs.2)
  · exact h f p hf hp hp2 hs hA

theorem ggOrdPToralUnivAt_E7_of_rest (h : GGOrdPToralE7Rest) : GGOrdPToralUnivAt .E7 := by
  intro n f p hadm hp hp2 _ hA
  change ∃ A : Subgroup (CFSG.LieType.Steinberg.Exceptional.e7UniversalGroup 2 f),
    IsElemAbelian p A ∧ p ^ 4 ≤ Nat.card A at hA
  change GGOrdPToralMax (CFSG.LieType.Steinberg.Exceptional.e7UniversalGroup 2 f) p
  have hf : 1 ≤ f := hadm.2.1
  let e := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)
  refine OrdPInnerExc.ggOrdPToralMax_of_mulEquiv e ?_
  by_cases hs : 11 ≤ p ∧ p ∣ 2 ^ f - 1
  · have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    exact OrdPInnerExc.ggOrdPToralMax_E7_split hp hs.1 (hK ▸ hs.2)
  · obtain ⟨A, hAel, hAc⟩ := hA
    refine h f p hf hp hp2 hs ⟨A.map e.toMonoidHom, OrdPInnerExc.isElemAbelian_map _ hAel, ?_⟩
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hAc

theorem ggOrdPInnerConjAt_F4_of_toral (hT : GGOrdPToralUnivAt .F4) : GGOrdPInnerConjAt .F4 :=
  OrdPInnerExc.ggOrdPInnerConjAt_of_parts (OrdPInnerExc.inner_of_psiDiagInner ggPsiDiagInner_F4)
    (fun _ f p _ _ _ => OrdPInnerExc.coprime_of_center_eq_bot
      (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)) p) hT

theorem ggOrdPInnerConjAt_E8_of_toral (hT : GGOrdPToralUnivAt .E8) : GGOrdPInnerConjAt .E8 :=
  OrdPInnerExc.ggOrdPInnerConjAt_of_parts (OrdPInnerExc.inner_of_psiDiagInner ggPsiDiagInner_E8)
    (fun _ f p _ _ _ => OrdPInnerExc.coprime_of_center_eq_bot
      (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)) p) hT

theorem ggOrdPInnerConjAt_E7_of_toral (hT : GGOrdPToralUnivAt .E7) : GGOrdPInnerConjAt .E7 :=
  OrdPInnerExc.ggOrdPInnerConjAt_of_parts (OrdPInnerExc.inner_of_psiDiagInner ggPsiDiagInner_E7)
    (fun _ f p _ _ _ => OrdPInnerExc.coprime_of_center_eq_bot
      (CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot (K := GaloisField 2 f)) p) hT

end Tags

end CFSG.StandardType
