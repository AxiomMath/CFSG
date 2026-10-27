module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108FieldL2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.PartOne.SEITZ9.SzTorus
import CFSG.RankThree.S4Free.StellmacherSzSylow
public import CFSG.RankThree.PartOne.CTP.SeitzL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint CFSG.Open CFSG.RankThree.PartOne.CTP CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

section Transport

theorem k108Field_fixed_sup_sylow_eq_top_of_mulEquiv {X P : Type} [Group X] [Group P] [Finite P]
    (e : X ≃* P) {p : ℕ}
    (h : ∀ σ : MulAut P, IsOuterOfOrder p σ → ∀ T : Sylow 2 P,
      signalizerFixedSubgroup σ ⊔ (T : Subgroup P) = ⊤)
    {α : MulAut X} (hα : IsOuterOfOrder p α) (T : Sylow 2 X) :
    signalizerFixedSubgroup α ⊔ (T : Subgroup X) = ⊤ := by
  have hσ : IsOuterOfOrder p (MulAut.congr e α) :=
    ⟨(MulEquiv.orderOf_eq (MulAut.congr e) α).trans hα.1, fun g hg =>
      hα.2 (e.symm g) (eq_conj_of_congr_eq_conj e hg)⟩
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  have h' := h _ hσ (T.mapSurjective hs)
  rw [← fixedSubgroup_eq_signalizer, fixedSubgroup_congr, Sylow.coe_mapSurjective,
    ← Subgroup.map_sup] at h'
  rw [← fixedSubgroup_eq_signalizer,
    ← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective
      (fixedSubgroup α ⊔ (T : Subgroup X)), h', Subgroup.comap_top]

end Transport

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem k108FieldSz_le_normalizer_of_sylow_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (T : Sylow 2 ↥(suzukiGroup a K)) {H : Subgroup ↥(suzukiGroup a K)}
    (hTH : (T : Subgroup ↥(suzukiGroup a K)) ≤ H) (hH : H ≠ ⊤) :
    H ≤ Subgroup.normalizer ((T : Subgroup ↥(suzukiGroup a K)) : Set ↥(suzukiGroup a K)) := by
  haveI : Finite ↥(suzukiGroup a K) := CFSG.LieType.Simplicity.finite_suzukiGroup a K
  have hB := CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isSz
    (n := 2 * a + 1) (X := ↥(suzukiGroup a K))
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  haveI : IsSimpleGroup ↥(suzukiGroup a K) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  exact CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hB T hTH hH

theorem k108FieldSz_fixed_sup_sylow_eq_top (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut ↥(suzukiGroup a K)} (hα : IsOuterOfOrder p α) (T : Sylow 2 ↥(suzukiGroup a K)) :
    signalizerFixedSubgroup α ⊔ (T : Subgroup ↥(suzukiGroup a K)) = ⊤ := by
  have hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(suzukiGroup a K) := by
    rintro ⟨g, hg⟩
    exact hα.2 g hg.symm
  obtain ⟨σ, h, -, -, -, -, -, -, -, hconj, -⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 α hα.1 hout
  obtain ⟨β, rfl⟩ : ∃ β : MulAut ↥(suzukiGroup a K), α = β * szFieldAut a K σ * β⁻¹ :=
    ⟨(MulAut.conj h)⁻¹, by rw [inv_inv, ← hconj]; group⟩
  have hfix : ∀ y ∈ fixedSubgroup (szFieldAut a K σ),
      β y ∈ signalizerFixedSubgroup (β * szFieldAut a K σ * β⁻¹) := by
    intro y hy
    rw [signalizerFixedSubgroup_conj]
    exact Subgroup.mem_map_of_mem β.toMonoidHom hy
  have hS2 : suzukiSElt a K 0 1 ^ 2 = 1 := by
    rw [← CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK one_ne_zero]
    exact pow_orderOf_eq_one _
  have hWS : orderOf (β (suzukiWElt a K) * β (suzukiSElt a K 0 1)) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq,
      CFSG.RankThree.S4Free.Suzuki.orderOf_suzukiWElt_mul_suzukiSElt hK]
  refine k108Field_eq_top_of_mul_pow_odd T
    (k108FieldSz_le_normalizer_of_sylow_le ha hK T le_sup_right)
    (Subgroup.mem_sup_left (hfix _ (CFSG.RankThree.PartOne.SEITZ9.suzukiWElt_mem_fixed σ)))
    (Subgroup.mem_sup_left
      (hfix _ (CFSG.RankThree.PartOne.SEITZ9.suzukiSElt_mem_fixed σ (map_zero σ) (map_one σ))))
    (by rw [← map_pow, sq, suzukiWElt_mul_self, map_one])
    (by rw [← map_pow, hS2, map_one]) (m := 5) ⟨2, rfl⟩
    (by rw [← hWS]; exact pow_orderOf_eq_one _) ?_
  intro h1
  rw [h1, orderOf_one] at hWS
  exact absurd hWS (by norm_num)

theorem k108FieldSz_fixed_sup_sylow_eq_top_of_mulEquiv {X : Type}
    [Group X] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : X ≃* ↥(suzukiGroup a K))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut X} (hα : IsOuterOfOrder p α)
    (T : Sylow 2 X) : signalizerFixedSubgroup α ⊔ (T : Subgroup X) = ⊤ := by
  haveI : Finite ↥(suzukiGroup a K) := CFSG.LieType.Simplicity.finite_suzukiGroup a K
  exact k108Field_fixed_sup_sylow_eq_top_of_mulEquiv e
    (fun _ hσ T' => k108FieldSz_fixed_sup_sylow_eq_top ha hK hp hp2 hσ T') hα T

end Suzuki

end CFSG.LocalAnalysis.UniquenessCase.UC22
