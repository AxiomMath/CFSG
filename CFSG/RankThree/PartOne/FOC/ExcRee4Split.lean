module

public import CFSG.RankThree.PartOne.FOC.ReeLayerDvd
public import CFSG.RankThree.PartOne.FOC.CompDvd
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.RankThree.PartOne.KLR.SectorTori

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KLR CFSG.RankThree.LargeReeOrder


theorem compDvdAt_ree_split {a p : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ 2 ^ (2 * a + 1) - 1) (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    CompDvdAt p x := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨E, hEH, hEF, hE⟩ := torus_phi1 D.isFrob
  obtain ⟨g₀, hg₀, hFg₀, hconj⟩ := sector_hconj D _ E hEH hEF _ hE hp
    (pow_factorization_card_reeGamma_dvd_phi1 hK hp hp3 hpq)
  obtain ⟨N, -, -, hcomp, -, hdvd⟩ := component_data_of_frame_dvd D hg₀ hFg₀ hp hp3 hconj
    (fun b hordb hbT => starSimpleDvd D ha hK wPhi1 hp hp3 hordb hbT) x hx
  intro E' hE'
  have hEN : E' = N := hcomp E' hE'
  have hN1 : N ≠ ⊥ := by
    rw [← hEN]
    exact (Subgroup.nontrivial_iff_ne_bot E').1 (CFSG.LocalCores.isQuasisimple_nontrivial hE'.2.1)
  rw [hEN]
  refine Nat.dvd_trans ?_ (hdvd hN1)
  rw [hK]
  exact hpq

end CFSG.RankThree.PartOne.FOC
