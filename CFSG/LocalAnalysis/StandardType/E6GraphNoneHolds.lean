module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneInn
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFourField
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFive
public import CFSG.LocalAnalysis.StandardType.TwistedE6GraphNoneStepFiveField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

private theorem mul_comm_of_conj_mem_centralizer {M : Type*} [Group M] {C : Subgroup M}
    (hZ : Subgroup.center C = ⊥) {P : M} {η : MulAut C} (hηP : ∀ h : C, (η h : M) = P * h * P⁻¹)
    {c : C} (hc : MulAut.conj c ∈ Subgroup.centralizer ({η} : Set (MulAut C))) :
    P * c = c * P := by
  have hcη : MulAut.conj c * η = η * MulAut.conj c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hfix : η c = c := mulAut_conj_injective_of_center_eq_bot hZ
    (by rw [← mulAut_mul_conj_mul_inv, ← hcη, mul_inv_cancel_right])
  have h := hηP c
  rw [hfix] at h
  calc P * c = (P * c * P⁻¹) * P := by group
    _ = c * P := by rw [← h]

private theorem not_fix_of_moved {M : Type*} [Group M] {C : Subgroup M} {P : M} {η : MulAut C}
    (hηP : ∀ h : C, (η h : M) = P * h * P⁻¹) {c : C} (hfix : ∀ x, MulAut.conj c x = x → η x = x)
    {z : M} (hzC : z ∈ C) (hzc : Commute z (c : M)) (hzP : P * z * P⁻¹ ≠ z) : False := by
  have h1 : MulAut.conj c ⟨z, hzC⟩ = ⟨z, hzC⟩ := Subtype.ext (by
    change (c : M) * z * (c : M)⁻¹ = z
    rw [← hzc.eq, mul_inv_cancel_right])
  have h2 := congrArg Subtype.val (hfix _ h1)
  rw [hηP] at h2
  exact hzP h2

private theorem card_comap_conj {H : Type*} [Group H]
    (hinj : Function.Injective (MulAut.conj : H →* MulAut H))
    {E : Subgroup (MulAut H)} (hEI : E ≤ (MulAut.conj : H →* MulAut H).range) :
    Nat.card (E.comap (MulAut.conj : H →* MulAut H)) = Nat.card E := by
  rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hEI]


section Eta


theorem e6_exists_moved_of_card_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (adjointGroup TwistTag.E6.tag K))}
    (hEI : E ≤ (MulAut.conj : adjointGroup TwistTag.E6.tag K →*
      MulAut (adjointGroup TwistTag.E6.tag K)).range)
    (hEab : IsElemAbelian p E) (hEcard : p ^ 4 ≤ Nat.card E)
    (hEP : ∀ e : adjointGroup TwistTag.E6.tag K, MulAut.conj e ∈ E →
      (e : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K))
    {c : adjointGroup TwistTag.E6.tag K} (hc : MulAut.conj c ∈ E) :
    ∃ z ∈ adjointGroup TwistTag.E6.tag K, Commute z (c : ModGL TwistTag.E6.tag K) ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := TwistTag.E6.tag) (K := K))
  set E₁ := (E.comap (MulAut.conj : adjointGroup TwistTag.E6.tag K →*
    MulAut (adjointGroup TwistTag.E6.tag K))).map (adjointGroup TwistTag.E6.tag K).subtype
  have hle : E₁ ≤ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
    rintro _ ⟨e, he, rfl⟩
    exact hEP e he
  have hE' : IsElemAbelian p (E₁.subgroupOf (twistedFixedGroup TwistTag.E6 K (RingHom.id K))) :=
    ((hEab.comap hinj).map _).comap (Subgroup.subtype_injective _)
  have hcard : Nat.card (E₁.subgroupOf (twistedFixedGroup TwistTag.E6 K (RingHom.id K))) =
      Nat.card E := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), card_comap_conj hinj hEI]
  exact E6GraphNoneSteps.e6_step5_K hK hp hp2 _ hE' (hcard ▸ hEcard)
    (b := ⟨c, hEP c hc⟩) ⟨c, hc, rfl⟩

theorem e6GraphNoneEtaInn_holds : E6GraphNoneEtaInn := by
  intro f K _ _ _ hf hK η hηP p β E hp hp2 _hβ1 hβE hEI hEab hEcard hEη _hη2 hfix
  have hZ := center_adjointGroup_eq_bot (τ := TwistTag.E6.tag) (K := K)
  have hEP : ∀ e : adjointGroup TwistTag.E6.tag K, MulAut.conj e ∈ E →
      (e : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
    fun e he => mem_twistedFixedGroup_id_iff.2
      ⟨e.2, mul_comm_of_conj_mem_centralizer hZ hηP (hEη he)⟩
  obtain ⟨c, rfl⟩ := hEI hβE
  obtain ⟨z, hzC, hzc, hzP⟩ : ∃ z ∈ adjointGroup TwistTag.E6.tag K,
      Commute z (c : ModGL TwistTag.E6.tag K) ∧
        diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      exact e6_exists_moved_of_card_two (by simpa using hK) hp hp2 hEI hEab hEcard hEP hβE
    · have hcp : c ^ p = 1 := mulAut_conj_injective_of_center_eq_bot hZ
        (by rw [map_pow, map_one]; exact hEab.2 _ hβE)
      exact E6GraphNoneSteps.e6_step4_K hf2 hK hp hp2 (hEP c hβE)
        (by rw [← Subgroup.coe_pow, hcp, Subgroup.coe_one])
  exact not_fix_of_moved hηP hfix hzC hzc hzP

theorem e6GraphNone_holds : E6GraphNone :=
  e6GraphNone_of_etaInn e6GraphNoneEtaInn_holds

end Eta

section TwistedEta


theorem twistedE6GraphNoneEtaInn_holds : TwistedE6GraphNoneEtaInn := by
  intro f K _ _ hf hK σ hσ η hηP p β E hp hp2 _hβ1 hβE hEI hEab hEcard hEη hfix
  have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hEP : ∀ e : twistedE6RootGroup K σ, MulAut.conj e ∈ E →
      diagramMap TwistTag.E6 K * e = e * diagramMap TwistTag.E6 K :=
    fun e he => mul_comm_of_conj_mem_centralizer hZ hηP (hEη he)
  obtain ⟨c, rfl⟩ := hEI hβE
  obtain ⟨z, hzC, hzc, hzP⟩ : ∃ z ∈ twistedE6RootGroup K σ,
      Commute z (c : ModGL TwistTag.E6.tag K) ∧
        diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      refine E6GraphNoneSteps.twE6_step5_K hK hσ hp hp2
        ((E.comap (MulAut.conj : twistedE6RootGroup K σ →*
          MulAut (twistedE6RootGroup K σ))).map (twistedE6RootGroup K σ).subtype)
        (Subgroup.map_subtype_le _) ?_ ((hEab.comap hinj).map _) ?_ (b := c) ⟨c, hβE, rfl⟩
      · rintro _ ⟨e, he, rfl⟩
        exact hEP e he
      · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
          card_comap_conj hinj hEI]
        exact hEcard
    · have hcp : c ^ p = 1 := hinj (by rw [map_pow, map_one]; exact hEab.2 _ hβE)
      exact E6GraphNoneSteps.twE6_step4_K hf2 hK hσ hp hp2 c.2 (hEP c hβE)
        (by rw [← Subgroup.coe_pow, hcp, Subgroup.coe_one])
  exact not_fix_of_moved hηP hfix hzC hzc hzP

theorem twistedE6GraphNone_holds : TwistedE6GraphNone :=
  twistedE6GraphNone_of_etaInn twistedE6GraphNoneEtaInn_holds

end TwistedEta

end CFSG.StandardType
