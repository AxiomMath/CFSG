module

public import Certificates.Certificate9543
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Perm

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Quasithin CFSG.AGLEmbedding.D4Two

theorem d4_link_check :
    arrCertOK projAct 18 validV keyV rootV lineCert = true ∧ lineCert.pts.size = 2457 ∧
      eqA 2457 d4GenA (compWord lineCert [2, 5, 10]) = true ∧
      eqA 2457 d4GenB (compWord lineCert [16, 17, 7, 4, 10]) = true ∧
      allLt 18 (fun k => siftA 2457 d4LevelsA d4ChainABaseArr 0 (piArr lineCert k)) = true :=
  Certificates.certificate9543

noncomputable def d4Rho : lineGroup →* Equiv.Perm (Fin 2457) :=
  rho d4_link_check.1 d4_link_check.2.1

theorem rep_d4Rho_letter {k : ℕ} (hk : k < 18) :
    Rep 2457 (piArr lineCert k) (d4Rho (letterX k)) :=
  rep_piArr d4_link_check.1 d4_link_check.2.1 hk

theorem d4Rho_mem
    (g : lineGroup) : d4Rho g ∈ d4P := by
  obtain ⟨x, hx⟩ := g
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    have hk' : k < 18 := hk
    have hg : (⟨letterGL k, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ : lineGroup) = letterX k := by
      apply Subtype.ext
      simp [letterX, hk']
    rw [hg]
    exact mem_d4P_of_sift (rep_d4Rho_letter hk') (allLt_spec d4_link_check.2.2.2.2 hk')
  | one =>
    have h1 : d4Rho (⟨1, Subgroup.one_mem _⟩ : lineGroup) = 1 := by
      rw [← map_one d4Rho]
      rfl
    rw [h1]
    exact d4P.one_mem
  | mul y z hy hz ihy ihz =>
    have h1 : d4Rho (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : lineGroup) =
        d4Rho ⟨y, hy⟩ * d4Rho ⟨z, hz⟩ := by
      rw [← map_mul]
      rfl
    rw [h1]
    exact d4P.mul_mem ihy ihz
  | inv y hy ihy =>
    have h1 : d4Rho (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : lineGroup) = (d4Rho ⟨y, hy⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h1]
    exact d4P.inv_mem ihy

theorem d4Rho_range :
    d4Rho.range = d4P := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact d4Rho_mem g
  · rw [d4P, closure_le]
    rintro _ (rfl | rfl)
    · have hw : ∀ l ∈ ([2, 5, 10] : List ℕ), l < 18 := by decide
      exact ⟨wordX [2, 5, 10], (eq_of_eqA rep_d4A
        (rep_compWord d4_link_check.1 d4_link_check.2.1 hw) d4_link_check.2.2.1).symm⟩
    · have hw : ∀ l ∈ ([16, 17, 7, 4, 10] : List ℕ), l < 18 := by decide
      exact ⟨wordX [16, 17, 7, 4, 10], (eq_of_eqA rep_d4B
        (rep_compWord d4_link_check.1 d4_link_check.2.1 hw) d4_link_check.2.2.2.1).symm⟩


theorem d4Rho_injective
    (hX : Nat.card lineGroup = 211341312) :
    Function.Injective (d4Rho : lineGroup →* Equiv.Perm (Fin 2457)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  have h1 : Nat.card lineGroup = Nat.card d4Rho.range * Nat.card d4Rho.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup d4Rho.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange d4Rho).toEquiv]
  rw [d4Rho_range, card_d4P, hX] at h1
  have h2 : Nat.card d4Rho.ker = 1 := by omega
  rw [Subgroup.card_eq_one] at h2
  exact h2.le

theorem d4_k3_of_equiv
    {Y : Type*} [Group Y]
    (φ : Y ≃* trialityGroup8) (hY : Nat.card Y = 211341312) {E W : Subgroup Y}
    (hEa : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hW : ¬ 3 ∣ Nat.card W)
    (hEW : E ≤ normalizer (W : Set Y)) : W = ⊥ := by
  let e : Y ≃* lineGroup := φ.trans (MulEquiv.subgroupCongr lineGroup_eq.symm)
  have hX : Nat.card lineGroup = 211341312 := by rw [← Nat.card_congr e.toEquiv, hY]
  have hinj : Function.Injective (d4Rho.comp e.toMonoidHom) :=
    (d4Rho_injective hX).comp e.injective
  exact d4_k3_of_injective (d4Rho.comp e.toMonoidHom) hinj (fun y => d4Rho_mem _) hEa hE9 hW hEW

end CFSG.RankThree.PartTwo.Sec4.Item434D42
