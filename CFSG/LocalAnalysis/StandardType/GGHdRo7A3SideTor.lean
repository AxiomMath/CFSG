module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SideDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7A3STAux_markingData {G : Type} [Group G]
    (hRig : GGLabelRigidInput) {Bs X : Subgroup G} {m : ℕ} (hInn : GGInnerDiagOn Bs X)
    (hlab : A3SideLabel X m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (θ : (↥X ⧸ Subgroup.center ↥X) ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) F 2))
      (I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F 2)))),
      Nat.card F = 4 ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      I ⊆ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F 2))
        (LargeEvenGUSet (Fin m) F 2) := by
  obtain ⟨lab, hlabΛ, hhas, htag, hn, hrank⟩ := hlab
  subst hrank
  have hmark := ggInnerDiagOn_relabel hRig hInn hlabΛ hhas
  obtain ⟨-, lab', -, hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hEq : lab' = lab := hP₀.1
  rw [hEq] at hraw hP₀
  obtain ⟨Fld, hFld, hFldfin, hFldcard, hQ⟩ :=
    hdRo7SULCoordAux_twA_rawLegacy_one htag hn hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  exact ⟨Fld, hFld, hFldfin, θ, _, hFldcard, hP.2.1, hP.2.2, fun _ hx => hx⟩

theorem a3_sideTor_holds :
    A3SideTorLeaf := by
  intro hRig G _ _ p B Bs X m hp hm hm3 hBs hInn hperf hlab hcardBs hcent
  subst hp
  obtain ⟨F, hF, hFfin, θ, I, hFcard, hN, hInd, hIsub⟩ :=
    hdRo7A3STAux_markingData (Bs := Bs) (X := X) hRig hInn hlab
  have hK4 : Nat.card F = (2 ^ 1) ^ 2 := by rw [hFcard]; norm_num
  have hFdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    TableBU.unitaryFieldData_of_card hK4 le_rfl
  have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
    simpa using hBs.2.1.subgroupOf Bs
  have hAel : IsElemAbelian 3 (ggGamma X hN).range := by
    have h := htop.map (ggGamma X hN)
    rwa [← MonoidHom.range_eq_map] at h
  have hAI : ∀ a ∈ (ggGamma X hN).range,
      ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
        (LargeEvenGUSet (Fin m) F (2 ^ 1)), ∀ l : ↥X, x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggBeta X θ hN b, hIsub (ggBeta_mem X θ hN hInd b),
      fun l => ggBeta_ggQuotHom (L := X) (B := Bs) (hBN := hN) θ b l⟩
  have hkerle : (ggGamma X hN).ker ≤ (Bs ⊓ Subgroup.centralizer (X : Set G)).subgroupOf Bs := by
    intro b hb
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff] at hb
    exact Subgroup.mem_subgroupOf.mpr ⟨b.2, hb⟩
  have hker2 : Nat.card (ggGamma X hN).ker ≤ 3 ^ 2 := by
    have h1 : Nat.card (ggGamma X hN).ker ≤
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
      have h2 := Subgroup.card_le_of_le hkerle
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Bs)).toEquiv] at h2
    exact h1.trans hcent
  have hcardmul : Nat.card (ggGamma X hN).range * Nat.card (ggGamma X hN).ker =
      Nat.card ↥Bs := by
    rw [Nat.mul_comm]
    exact Subgroup.card_ker_mul_card_range (ggGamma X hN)
  have hge : 3 ^ (m - 4) ≤ Nat.card (ggGamma X hN).range := by
    have h1 : 3 ^ (m - 2) ≤
        Nat.card (ggGamma X hN).range * Nat.card (ggGamma X hN).ker := by
      rw [hcardmul]; exact hcardBs
    have h2 : Nat.card (ggGamma X hN).range * Nat.card (ggGamma X hN).ker ≤
        Nat.card (ggGamma X hN).range * 3 ^ 2 := Nat.mul_le_mul_left _ hker2
    have h5 : 3 ^ (m - 4) * 3 ^ 2 = 3 ^ (m - 2) := by
      rw [← pow_add]; congr 1; omega
    have h4 : 3 ^ (m - 4) * 3 ^ 2 ≤ Nat.card (ggGamma X hN).range * 3 ^ 2 := by
      rw [h5]; exact h1.trans h2
    exact Nat.le_of_mul_le_mul_right h4 (by norm_num)
  have hcard : 3 ^ (m / 3 + 2) ≤ Nat.card (ggGamma X hN).range := by
    have hle : m / 3 + 2 ≤ m - 4 := by
      have hmod : m % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hm3
      omega
    exact (Nat.pow_le_pow_right (by norm_num) hle).trans hge
  have hcov : LineU.UnitaryCoverAt 1 m F :=
    LineU.unitaryCoverAt hK4 (by omega) (by rintro ⟨h, -⟩; omega)
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel (L' := ↥X) (K := F) (n := 1) (d := m) (p := 3) hK4 le_rfl (by omega)
      Nat.prime_three (by norm_num) hm3 hcov (ψ := ggQuotHom θ) (ggQuotHom_surjective θ)
      (ker_ggQuotHom θ).le hperf (A := (ggGamma X hN).range) hAel hAI hcard
  exact ⟨hN, F, hF, hFfin, φ, hFcard, ⟨hFdata, hφs, hφker⟩, fun b => hdiag _ ⟨b, rfl⟩⟩

end CFSG.StandardType.HdRo7A3
