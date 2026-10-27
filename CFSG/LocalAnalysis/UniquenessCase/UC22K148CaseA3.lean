module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA1
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathSolvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem exists_Q [Finite G] [Finite V] (hρ : Function.Injective ρ) (hO : CFSG.pCore 2 G = ⊥)
    {A : Subgroup G} (hA : A ∈ calP ρ) (hFA : ⁅CFSG.fittingSubgroup G, A⁆ ≠ ⊥) :
    ∃ Q : Subgroup G, ∃ b ∈ A, Nat.card ↥Q = 3 ∧
      Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2 ∧ Q ≤ CFSG.pCore 3 G ∧
      A ≤ Subgroup.normalizer (Q : Set G) ∧ ∀ q ∈ Q, b * q * b⁻¹ = q⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAF : A ≤ Subgroup.normalizer ((CFSG.fittingSubgroup G : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨b, hbA, hQ3, hQV, hQF, hAQ, hinv⟩ :=
    exists_Q_of_moving hρ CFSG.fittingSubgroup_nilpotent
      (CFSG.QuasithinUnique.Setup.Wreath.odd_card_fittingSubgroup hO)
      (isElementaryAbelian_of_mem_calP hA) hAF hFA (isBestOffenderOn_of_mem_calP hρ hA)
  refine ⟨_, b, hbA, hQ3, hQV, ?_, hAQ, hinv⟩
  exact CFSG.ABGLocalTools.le_pCore_of_isPGroup_of_le_fitting
    (IsPGroup.of_card (n := 1) (by rw [hQ3, pow_one])) hQF

private theorem le_normalizer_iSup_conj {Q D : Subgroup G} :
    D ≤ Subgroup.normalizer
      (((⨆ d ∈ D, Q.map (MulAut.conj d).toMonoidHom : Subgroup G)) : Set G) := by
  refine le_normalizer_of_conj_mem fun e he y hy => ?_
  have hle : (⨆ d ∈ D, Q.map (MulAut.conj d).toMonoidHom : Subgroup G) ≤
      (⨆ d ∈ D, Q.map (MulAut.conj d).toMonoidHom : Subgroup G).comap
        (MulAut.conj e).toMonoidHom := by
    refine iSup₂_le fun d hd => ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_comap]
    refine (le_iSup₂ (f := fun d (_ : d ∈ D) => Q.map (MulAut.conj d).toMonoidHom) (e * d)
      (D.mul_mem he hd)) (Subgroup.mem_map.2 ⟨q, hq, ?_⟩)
    change e * d * q * (e * d)⁻¹ = e * (d * q * d⁻¹) * e⁻¹
    group
  exact hle hy

theorem normalizes_Q [Finite G] [Finite V] (hρ : Function.Injective ρ) {S Q : Subgroup G}
    (hS : IsPGroup 3 ↥S) (hSn : S.Normal) (hQS : Q ≤ S) (hQ3 : Nat.card ↥Q = 3)
    (hQV : Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2) {D : Subgroup G} (hD : D ∈ calP ρ) :
    D ≤ Subgroup.normalizer (Q : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD2 := isElementaryAbelian_of_mem_calP hD
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hD2.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set Y : Subgroup G := ⨆ d ∈ D, Q.map (MulAut.conj d).toMonoidHom
  have hQY : Q ≤ Y := fun q hq =>
    (le_iSup₂ (f := fun d (_ : d ∈ D) => Q.map (MulAut.conj d).toMonoidHom) 1 D.one_mem)
      (Subgroup.mem_map.2 ⟨q, hq, by simp⟩)
  have hYS : Y ≤ S := iSup₂_le fun d _ => by
    rintro _ ⟨q, hq, rfl⟩
    exact hSn.conj_mem q (hQS hq) d
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_iSup_conj
  by_cases hYD : ⁅Y, D⁆ = ⊥
  · have hQc : Q ≤ Subgroup.centralizer (D : Set G) :=
      hQY.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hYD)
    rw [Subgroup.le_centralizer_iff] at hQc
    exact hQc.trans (Subgroup.centralizer_le_normalizer _)
  have hYp : IsPGroup 3 ↥Y := hS.to_le hYS
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hYp
  have hYodd : Odd (Nat.card ↥Y) := hn ▸ Odd.pow (by decide)
  obtain ⟨b, -, hX3, hXV, hXY, hDX, -⟩ :=
    exists_Q_of_moving hρ hYp.isNilpotent hYodd hD2 hDY hYD (isBestOffenderOn_of_mem_calP hρ hD)
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨e, heD, hXe⟩ := eq_conj_of_rank_two hρ hS hQS hDS hQ3 hQV hXY hX3 hXV
  refine le_normalizer_of_conj_mem fun x hx q hq => ?_
  have h1 : x * (e * q * e⁻¹) * x⁻¹ ∈ Q.map (MulAut.conj e).toMonoidHom := by
    rw [← hXe]
    refine (Subgroup.mem_normalizer_iff.1 (hDX hx) _).1 ?_
    rw [hXe]
    exact Subgroup.mem_map.2 ⟨q, hq, rfl⟩
  obtain ⟨q', hq', hq'e⟩ := h1
  have hxe := hDcomm x hx e heD
  have h2 : e * q' * e⁻¹ = e * (x * q * x⁻¹) * e⁻¹ := by
    change e * q' * e⁻¹ = _ at hq'e
    rw [hq'e]
    calc x * (e * q * e⁻¹) * x⁻¹ = (x * e) * q * (x * e)⁻¹ := by group
      _ = (e * x) * q * (e * x)⁻¹ := by rw [hxe]
      _ = e * (x * q * x⁻¹) * e⁻¹ := by group
  rw [← mul_left_cancel (mul_right_cancel h2)]
  exact hq'

theorem Q_normal [Finite G] [Finite V] (hρ : Function.Injective ρ) {S Q : Subgroup G}
    (hS : IsPGroup 3 ↥S) (hSn : S.Normal) (hQS : Q ≤ S) (hQ3 : Nat.card ↥Q = 3)
    (hQV : Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2) (hH : hP ρ = ⊤) : Q.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hH]
  exact iSup₂_le fun D hD => normalizes_Q hρ hS hSn hQS hQ3 hQV hD

theorem exists_normal_Q [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hO : CFSG.pCore 2 G = ⊥) (hH : hP ρ = ⊤) {A : Subgroup G} (hA : A ∈ calP ρ)
    (hFA : ⁅CFSG.fittingSubgroup G, A⁆ ≠ ⊥) :
    ∃ Q : Subgroup G, ∃ b ∈ A, Q.Normal ∧ Nat.card ↥Q = 3 ∧
      Module.finrank (ZMod 2) ↥(commOn ρ Q ⊤) = 2 ∧ ∀ q ∈ Q, b * q * b⁻¹ = q⁻¹ := by
  obtain ⟨Q, b, hbA, hQ3, hQV, hQO, -, hinv⟩ := exists_Q hρ hO hA hFA
  exact ⟨Q, b, hbA, Q_normal hρ CFSG.pCore_isPGroup CFSG.pCore_normal hQO hQ3 hQV hH, hQ3, hQV,
    hinv⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
