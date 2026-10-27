module

public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
public import CFSG.Fischer.Classification.Unitary.Model
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate1022
public import Certificates.Certificate7023
public import Certificates.Certificate7059
public import Certificates.Certificate709540
public import Certificates.Certificate709541
public import Certificates.Certificate709542
import CFSG.Fischer.Classification.Final
import CFSG.Fischer.Classification.PartII.O2G.ThreeFinal
import CFSG.Fischer.Classification.Orthogonal2.SpModel
import CFSG.Fischer.Classification.Orthogonal2.LocalData
import CFSG.Fischer.Classification.PartIII.Beta.Transport
import CFSG.Fischer.Classification.PartIII.Beta.Iso
import CFSG.LocalAnalysis.StandardType.ZS.ReflHyp
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTwo
import CFSG.LocalAnalysis.StandardType.ZS.DThreeExc
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernary
import CFSG.LocalAnalysis.StandardType.ZS.DThreeWeyl
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryThree
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryReverse
import CFSG.LocalAnalysis.StandardType.ZS.DThreeObstruction
import CFSG.LocalAnalysis.StandardType.ZS.DThreeUnitary
import CFSG.LocalAnalysis.StandardType.ZS.DThreeFischerType
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTransport
import CFSG.Fischer.Assembly
import CFSG.Fischer.Classification.Milestone
import CFSG.Fischer.NoF25.Local

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification
open CFSG.StandardType.QTwoLin (TransvectionFree)
open CFSG.Quasithin.SimsG4 (IsImprimitiveOnV)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem za3_conj_symm {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {g a b : Y}
    (h : g * a * g⁻¹ = b) : φ.symm g * φ.symm a * (φ.symm g)⁻¹ = φ.symm b := by
  simpa only [map_mul, map_inv] using congrArg φ.symm h

private theorem za3_false_of_affineTriangle_R3 (hp : p ≠ 2) (hp3 : p ≠ 3)
    (hirr : AbsIrred p A) (hn : 3 ≤ Module.finrank (ZMod p) U) {m : ℕ} (hm : m = 6 ∨ m = 7)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m 2))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 m 2)) : False := by
  obtain ⟨a, b, c, g, htri, hga, hgb, hgc⟩ := exists_affineTriangle_conj_D3_diagF3_two hm
  have htri' : AffineTriangle (reflImage p A) (φ.symm a) (φ.symm b) (φ.symm c) :=
    AffineTriangle.comap φ hφ htri
  exact hp3 (eq_three_of_affineTriangle_of_conj hp hirr hn htri'
    (za3_conj_symm φ hga) (za3_conj_symm φ hgb) (za3_conj_symm φ hgc))

private theorem za3_false_of_scalarFrame_R3 (hp : p ≠ 2) (hp3 : p ≠ 3)
    (hirr : AbsIrred p A) (hn : 3 ≤ Module.finrank (ZMod p) U)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} {δ : ZMod 3} (hm : 8 ≤ m ∨ (m = 7 ∧ δ = 1)) (hδ : δ ≠ 0)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m δ))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 m δ)) : False := by
  obtain ⟨d, e, hframe, hnoncomm⟩ := exists_scalarFrame_D3_diagF3 hm hδ
  have hframe' : ScalarFrame (reflImage p A) (φ.symm ∘ d) (φ.symm e) :=
    ScalarFrame.comap φ hφ hframe
  have hall' : ∀ i, ¬ Commute (φ.symm e) ((φ.symm ∘ d) i) := fun i hc =>
    hnoncomm i ((commute_map_iff (f := φ.symm) φ.symm.injective).mp hc)
  exact hp3 (eq_three_of_scalarFrame_seven hp hirr hn h3 hframe' hall')

theorem family_of_mulEquiv_R3_diagF3
    (hp : p ≠ 2)
    (hn : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 5 ≤ m) {δ : ZMod 3} (hδ : δ ≠ 0)
    (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 m δ))
    (hφ : ∀ g, g ∈ reflImage p A ↔ φ g ∈ D3 (diagF3 m δ)) : Family p A := by
  by_cases hp3 : p = 3
  · exact family_of_mulEquiv_R3_of_eq_three hp3 hn hgen hirr h3 hm
      (isF3Form_diagF3 hδ) φ hφ
  · have hδ' : δ = 1 ∨ δ = 2 := by
      have h : ∀ δ : ZMod 3, δ = 0 ∨ δ = 1 ∨ δ = 2 := by decide
      rcases h δ with h0 | h1 | h2
      · exact absurd h0 hδ
      · exact Or.inl h1
      · exact Or.inr h2
    have hm' : m = 5 ∨ m = 6 ∨ m = 7 ∨ 8 ≤ m := by omega
    rcases hm' with rfl | rfl | rfl | hm8
    · rcases hδ' with rfl | rfl
      · exact family_of_mulEquiv_R3_five_one hp hp3 (by omega) hgen hirr h3 φ hφ
      · obtain ⟨d, hd, htop⟩ := exists_coxeterConfig_E₆_D3_diagF3_five_two
        have hd' : CoxeterConfig (reflImage p A) CoxeterMatrix.E₆ (φ.symm ∘ d) :=
          CoxeterConfig.comap φ hφ hd
        have htop' : Subgroup.closure (Set.range (φ.symm ∘ d)) = ⊤ :=
          closure_range_symm_comp_eq_top φ htop
        exact Family.weyl (linWeyl_of_coxeterConfig_E₆ hp hgen hirr (by omega)
          (oneClass_of_orderOf_mul_le_three hp hgen hirr h3) hd' htop')
    · rcases hδ' with rfl | rfl
      · exact family_of_mulEquiv_R3_six_one hp hp3 (by omega) hgen hirr h3 φ hφ
      · exact (za3_false_of_affineTriangle_R3 hp hp3 hirr (by omega) (m := 6) (hm := Or.inl rfl)
          φ hφ).elim
    · rcases hδ' with rfl | rfl
      · exact (za3_false_of_scalarFrame_R3 hp hp3 hirr (by omega) h3 (m := 7) (δ := 1)
          (hm := Or.inr ⟨rfl, rfl⟩) hδ φ hφ).elim
      · exact (za3_false_of_affineTriangle_R3 hp hp3 hirr (by omega) (m := 7) (hm := Or.inr rfl)
          φ hφ).elim
    · rcases hδ' with rfl | rfl
      · exact (za3_false_of_scalarFrame_R3 hp hp3 hirr (by omega) h3 (m := m) (δ := 1)
          (hm := Or.inl hm8) hδ φ hφ).elim
      · exact (za3_false_of_scalarFrame_R3 hp hp3 hirr (by omega) h3 (m := m) (δ := 2)
          (hm := Or.inl hm8) hδ φ hφ).elim

theorem family_of_mulEquiv_U2
    (hp : p ≠ 2) (hn : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A)
    (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {m : ℕ} (hm : 4 ≤ m) (φ : ↥A ⧸ Subgroup.center ↥A ≃* Unitary.U2 m)
    (hφ : φ '' reflImage p A = Unitary.DU m) : Family p A := by
  by_cases hm5 : 5 ≤ m
  · obtain ⟨a, b, c, d, hconf⟩ := exists_unitaryFourConfig_DU hm5
    have hEF : ∀ x, x ∈ reflImage p A ↔ φ x ∈ Unitary.DU m :=
      mem_iff_of_image_eq φ hφ
    exact (false_of_unitaryFourConfig hp hirr (by omega)
      (UnitaryFourConfig.comap φ hEF hconf)).elim
  · have hm4 : m = 4 := by omega
    subst m
    obtain ⟨ψ, hψ⟩ := exists_mulEquiv_U2_four_R3_I5
    have hψ' : ∀ x : Unitary.U2 4, ψ x ∈ D3 I5Form ↔ x ∈ Unitary.DU 4 :=
      fun x => (mem_iff_of_image_eq ψ hψ x).symm
    have hφ' : ∀ g, g ∈ reflImage p A ↔ (φ.trans ψ) g ∈ D3 I5Form := by
      intro g
      have htrans : (φ.trans ψ) g = ψ (φ g) := rfl
      rw [htrans, hψ', mem_iff_of_image_eq φ hφ g]
    by_cases hp3 : p = 3
    · exact family_of_mulEquiv_R3_of_eq_three hp3 hn hgen hirr h3 (m := 5) (by norm_num)
        isF3Form_I5Form (φ.trans ψ) hφ'
    · obtain ⟨ρ, hρ⟩ := exists_mulEquiv_R3_of_isometry (m := 5) (f := I5Form)
        (f' := diagF3 5 1) (LinearEquiv.refl (ZMod 3) (Fin 5 → ZMod 3))
        (fun x y => by rw [diagF3_five_one]; rfl)
      have hρ' : ∀ x : R3 I5Form, ρ x ∈ D3 (diagF3 5 1) ↔ x ∈ D3 I5Form :=
        fun x => (mem_iff_of_image_eq ρ hρ x).symm
      have hφ'' : ∀ g, g ∈ reflImage p A ↔ ((φ.trans ψ).trans ρ) g ∈ D3 (diagF3 5 1) := by
        intro g
        have htrans : ((φ.trans ψ).trans ρ) g = ρ ((φ.trans ψ) g) := rfl
        rw [htrans, hρ', hφ']
      exact family_of_mulEquiv_R3_five_one hp hp3 (by omega) hgen hirr h3
        ((φ.trans ψ).trans ρ) hφ''

theorem family_of_primitive_of_orderOf_mul_le_three :
    DThreeCase := by
  intro p _ U _ _ _ A hp hn hgen hirr himp htv h3
  have hn3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  have hH : Hyp (↥A ⧸ Subgroup.center ↥A) (reflImage p A) :=
    hyp_reflImage hp hn hgen hirr himp h3
  have hconcl : Conclusion (↥A ⧸ Subgroup.center ↥A) (reflImage p A) :=
    statement_of_twinFour o2TwinFourInput _ _ hH
  rcases hconcl with hcl | ⟨k, hk⟩
  · rcases hcl with ⟨m, hm, φ, hφ⟩ | ⟨m, hm, b, halt, hnd, hsp⟩ |
      ⟨m, hm, Q, hnd, hts, hO⟩ | ⟨m, hm, hCQ⟩ | ⟨m, hm, f, hsym, hnd, hCQ⟩
    · exact family_of_mulEquiv_perm hp hn hgen hirr h3 hm φ hφ
    · obtain ⟨Φ, hΦ⟩ :=
        Orth2.exists_mulEquiv_isometryGroup_of_fischerLinearModel halt hsp
      exact family_of_mulEquiv_isometryGroup hp hn hgen hirr h3 hm halt hnd Φ hΦ
    · obtain ⟨Φ, hΦ⟩ := Orth2.exists_mulEquiv_orthogonalGroup hO
      exact family_of_mulEquiv_orthogonalGroup hp hn hgen hirr h3 hm hnd hts Φ hΦ
    · obtain ⟨φU, hφU⟩ := fischerCentralQuotientModel_iff_U2.mp hCQ
      exact family_of_mulEquiv_U2 hp hn hgen hirr h3 hm φU hφU
    · obtain ⟨φR, hφR⟩ :=
        (fischerCentralQuotientModel_iff (m := m) (f := f) (reflImage p A)).mp hCQ
      have hf : IsF3Form f := ⟨hsym, hnd⟩
      obtain ⟨δ, e, hδ12, he⟩ := exists_linearEquiv_diagF3 (m := m) (by omega) hf
      have hδ : δ ≠ 0 := by
        rcases hδ12 with rfl | rfl <;> decide
      obtain ⟨ψ, hψ⟩ := exists_mulEquiv_R3_of_isometry (f := f) (f' := diagF3 m δ) e he
      have hψ' : ∀ x : R3 f, ψ x ∈ D3 (diagF3 m δ) ↔ x ∈ D3 f :=
        fun x => (mem_iff_of_image_eq ψ hψ x).symm
      have hφ' : ∀ g, g ∈ reflImage p A ↔ (φR.trans ψ) g ∈ D3 (diagF3 m δ) := by
        intro g
        have htrans : (φR.trans ψ) g = ψ (φR g) := rfl
        rw [htrans, hψ', hφR g]
      exact family_of_mulEquiv_R3_diagF3 hp hn hgen hirr h3 hm hδ (φR.trans ψ) hφ'
  · obtain ⟨a, b, c, d, hconf⟩ := exists_unitaryFourConfig_of_hasType hk
    exact (false_of_unitaryFourConfig hp hirr hn3 hconf).elim

end CFSG.StandardType.ZS
