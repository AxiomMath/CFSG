module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Frame
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.RadSetting
public import Certificates.Certificate1953
public import Certificates.Certificate1954
import CFSG.LocalAnalysis.StandardType.FF81.CentE6.CentCL
import CFSG.LocalAnalysis.StandardType.FF81.CentE6.CaseOne
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenbStruct

public section

namespace CFSG.StandardType.FF81.CentE6

open CFSG CFSG.Assembly CFSG.Open CFSG.RankThree.GF2n.Smith81
open scoped MatrixGroups

theorem centralizer_le_zpowers_sup {G : Type} [Group G] [Finite G] {n : ℕ} {b t : G}
    {L : Subgroup G} {K : ℕ → Subgroup G} (hchar : IsCharTwoType G) (hA : HypA G n b L)
    (hU : Upstream n b L K t) (hYD : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t)
    (hn : n = 5) (hlab : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ)))
    (hQY : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤ ⨆ i : Fin (n + 2), K (i : ℕ)) :
    Subgroup.centralizer ({b} : Set G) ≤ Subgroup.zpowers b ⊔ L := by
  obtain ⟨z, hz, -⟩ := id hU
  rcases hz.out with ⟨-, hlines⟩ | ⟨-, -, -, hodd⟩
  · exact absurd hlines (not_conjLinesOfB_coordLines hA hU hYD hn hlab hz.model)
  · intro x hx
    obtain ⟨d, hd, l, hl, rfl⟩ := PropOne.exists_mul_mem_inf_of_model hA hz.model hodd x hx
    have hdb : d ∈ Subgroup.zpowers b := by
      rw [← centralizer_inf_centralizer_eq_zpowers hchar hA hU hYD hQY]
      exact ⟨hd.2, hd.1⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left hdb)

theorem centralizer_pair_le_sup {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G} {t : G}
    (F : E6Frame G n b L K t) {Q : Subgroup G} {eL : ↥L ≃* SL(6, ZMod 2)}
    {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b' : G}
    (_R : RadGeom t Q L eL π b')
    (hconj : ∃ y ∈ (⨆ i : Fin (n + 2), K (i : ℕ)), y * b * y⁻¹ = b')
    (hQL : Q ⊔ L = Subgroup.centralizer ({t} : Set G) ⊓ ⨆ i : Fin (n + 2), K (i : ℕ))
    (hQ : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) = Q) :
    ∀ g : G, g * t = t * g → g * b' = b' * g → g ∈ Q ⊔ L := by
  intro g hgt hgb
  obtain ⟨y, hyY, rfl⟩ := hconj
  have hQY : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    hQ ▸ le_sup_left.trans (hQL.le.trans inf_le_right)
  have hbY : b ∈ ⨆ i : Fin (n + 2), K (i : ℕ) := by
    obtain ⟨-, -, hFS⟩ := F.upstream
    have hK0 : K 0 ≤ ⨆ i : Fin (n + 2), K (i : ℕ) :=
      le_iSup (fun i : Fin (n + 2) => K (i : ℕ)) ⟨0, by omega⟩
    exact hK0 (hFS.K0 ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have hx : y⁻¹ * g * y ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y⁻¹ * g * y * b = y⁻¹ * (g * (y * b * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * b * y⁻¹) * g) * y := by rw [hgb]
      _ = b * (y⁻¹ * g * y) := by group
  have hxY : y⁻¹ * g * y ∈ ⨆ i : Fin (n + 2), K (i : ℕ) :=
    sup_le (Subgroup.zpowers_le.mpr hbY) F.yData.le
      (centralizer_le_zpowers_sup F.charTwo F.hypA F.upstream F.yData F.five F.label hQY hx)
  have hgY : g ∈ ⨆ i : Fin (n + 2), K (i : ℕ) := by
    have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ hyY hxY) (Subgroup.inv_mem _ hyY)
    rwa [show y * (y⁻¹ * g * y) * y⁻¹ = g by group] at h
  rw [hQL]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgt, hgY⟩

end CFSG.StandardType.FF81.CentE6

end
