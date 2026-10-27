module

public import CFSG.Quasithin.Vol2.Ch3Sec2Prop3210Six
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem26A8

variable {G : Type} [Group G] [Finite G]

theorem not_thompsonJ_le_centralizer (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    {T L V : Subgroup G} {z v g : G} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hvV : v ∈ V) (hv1 : v ≠ 1) (hzV : z ∈ V)
    (hgM : g ∉ Subgroup.normalizer (L : Set G)) (hgv : g⁻¹ * v * g = v * z) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
  intro hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := hH.sylow.1.toSylow hH.sylow.2
  have hVC : V ≤ Subgroup.centralizer (thompsonJ T : Set G) :=
    Subgroup.le_centralizer_iff.mp hJ
  obtain ⟨n, hn, hnv⟩ := burnside_fusion_lemma_centralizer P (W := thompsonJ T)
    (GammaExtra.thompsonJ_le_self T) Prop3210.thompsonJ_isWeaklyClosedIn (hVC hvV)
    (hVC (V.mul_mem hvV hzV)) hgv
  have hTV' : conjClosure V T = V := conjClosure_eq_self_of_normalizes hTV
  have hnM : n ∈ Subgroup.normalizer (conjClosure L T : Set G) :=
    Prop3210.normalizer_thompsonJ_le_of_V h323 h3228 hH.fsu (by rw [hTV']; exact hJ) hn
  rw [hH.conjClosure_eq] at hnM
  have hc : g * n⁻¹ ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    have h1 : (g * n⁻¹)⁻¹ * v * (g * n⁻¹) = v := by
      calc (g * n⁻¹)⁻¹ * v * (g * n⁻¹) = n * (g⁻¹ * v * g) * n⁻¹ := by group
        _ = n * (n⁻¹ * v * n) * n⁻¹ := by rw [hgv, hnv]
        _ = v := by group
    calc v * (g * n⁻¹) = (g * n⁻¹) * ((g * n⁻¹)⁻¹ * v * (g * n⁻¹)) := by group
      _ = (g * n⁻¹) * v := by rw [h1]
  have hgn := hNE v hvV hv1 hc
  apply hgM
  have hg : g = (g * n⁻¹) * n := by group
  rw [hg]
  exact Subgroup.mul_mem _ hgn hnM

end Lem26A8

end CFSG.Quasithin.H13
