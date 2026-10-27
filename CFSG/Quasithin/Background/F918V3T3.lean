module

public import CFSG.Quasithin.Background.F918V3T3D
public import CFSG.Quasithin.Background.F918V3Stmt
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.A3Structure36AList

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F918V3T3

theorem exists_noncomm_quotient_center {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hle : commutator K ≤ Subgroup.center K := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hcen : ∀ g : K, g ∈ Subgroup.center K := fun g => hle (hK.1 ▸ Subgroup.mem_top g)
  have := hK.2.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
  induction x using QuotientGroup.induction_on with
  | H g => exact hx ((QuotientGroup.eq_one_iff g).2 (hcen g))

end F918V3T3

theorem d392_three_dvd_component
    
    {W : Type} [CommGroup W] [Finite W] {M K : Subgroup (MulAut W)}
    (hM : IsQuotientOfSQTKTC ↥M) (hK : IsComponentOf K M) (hnsz : ¬ IsSuzukiComponent K) :
    3 ∣ Nat.card ↥K := by
  obtain ⟨S, _, _, hSQT, hKgrp, φ, hφ⟩ := hM
  obtain ⟨hKM, -, hq⟩ := hK
  let K' : Subgroup ↥M := K.subgroupOf M
  let π : ↥(K'.comap φ) →* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom.comp (φ.subgroupComap K')
  have hπ : Function.Surjective π :=
    (Subgroup.subgroupOfEquivOfLe hKM).surjective.comp
      (MonoidHom.subgroupComap_surjective φ K' hφ)
  let q : ↥(K'.comap φ) →* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp π
  have hqs : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hπ
  let e : ↥(K'.comap φ) ⧸ q.ker ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.quotientKerEquivOfSurjective q hqs
  have hsimple : IsSimpleGroup (↥(K'.comap φ) ⧸ q.ker) :=
    (MulEquiv.isSimpleGroup_congr e).2 hq.2
  have hnonab : ∃ a b : ↥(K'.comap φ) ⧸ q.ker, a * b ≠ b * a := by
    obtain ⟨u, v, huv⟩ := F918V3T3.exists_noncomm_quotient_center hq
    obtain ⟨a, rfl⟩ := e.surjective u
    obtain ⟨b, rfl⟩ := e.surjective v
    exact ⟨a, b, fun h => huv (by rw [← map_mul, ← map_mul, h])⟩
  have hlist : A23List (↥K ⧸ Subgroup.center ↥K) :=
    A36A.a23List_of_mulEquiv e.symm
      (a23SQTKListFact S ⟨hSQT, hKgrp⟩ (K'.comap φ) q.ker hsimple hnonab)
  have hfin : Finite ↥K := Finite.of_surjective π hπ
  have h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := three_dvd_card_of_a23List hlist hnsz
  exact h3.trans ⟨Nat.card (Subgroup.center ↥K), Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩

end CFSG.Quasithin
