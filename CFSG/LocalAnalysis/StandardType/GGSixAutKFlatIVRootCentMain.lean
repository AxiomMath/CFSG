module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVCore
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVLemmaQ
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVLift
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVMarking
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Congr

variable {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]

theorem ggPComponent_subgroupOf_congr {A B B' : Subgroup X} (h : B = B')
    (hc : CFSG.IsPComponent p (A.subgroupOf B)) : CFSG.IsPComponent p (A.subgroupOf B') := by
  subst h
  exact hc

end Congr

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggItem5_gen (hS1' : GGStructSOnePrimeRoot) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ Bs E : Subgroup G} {r : G} (hsimple : IsSimpleGroup ↥G₀)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hmark : LargeEvenMarking ↥G₀ fun _ _ _ I _ θ => ∀ c ∈ Bs,
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ)
    (hperf : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (G₀ : Set G) → ⁅P, P⁆ = P → P ≤ G₀)
    (hEBs : E ≤ Bs) (hEel : IsElemAbelian p E)
    (hfus : GGControlsStrongFusion (Subgroup.normalizer (G₀ : Set G)) E)
    (hr : r ∈ G₀) (hr2 : orderOf r = 2) (hroot : GGIsRootInvolution G₀ r)
    (hEr : E ≤ Subgroup.centralizer ({r} : Set G))
    {K : Subgroup (GGRCSNbar r)} (hK : CFSG.IsComponent K)
    (hEK : ggRCSImg r E ≤ Subgroup.normalizer (K : Set (GGRCSNbar r)))
    {W' : Type} [Group W'] [Finite W'] (π : ↥(ggRCSImg r E ⊔ K) →* W')
    (hπ : Function.Surjective π)
    (hker : ∀ w : ↥(ggRCSImg r E ⊔ K), π w = 1 →
      (w : GGRCSNbar r) ∈ Subgroup.centralizer (K : Set (GGRCSNbar r))) :
    GGHypRestIVFlat p (((ggRCSImg r E).subgroupOf (ggRCSImg r E ⊔ K)).map π) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hx hx1 C hC
  have hx' := Subgroup.mem_map.mp hx
  obtain ⟨ē, hē, hēx⟩ := hx'
  have hē' := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hē)
  obtain ⟨e', he', hee'⟩ := hē'
  have heE : (e' : G) ∈ E := Subgroup.mem_subgroupOf.mp he'
  have he1 : (e' : G) ≠ 1 := by
    intro h
    apply hx1
    have h1 : e' = 1 := Subtype.ext h
    have h2 : ē = 1 := Subtype.ext (by rw [← hee', h1, map_one]; rfl)
    rw [← hēx, h2, map_one]
  have hEbel : IsElemAbelian p (ggRCSImg r E) := (ggBarE_elem_card hp hp2 hEr hEel).1
  have hKW : K ≤ ggRCSImg r E ⊔ K := le_sup_right
  have hKn : (K.subgroupOf (ggRCSImg r E ⊔ K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKW]
    exact sup_le hEK Subgroup.le_normalizer
  have hCX := (ggLargeEvenPComponent_iff p _ C).1 hC
  have hCle : C ≤ Subgroup.centralizer {π ē} := by
    rw [hēx]
    exact hCX.1
  have hCp : CFSG.IsPComponent p (C.subgroupOf (Subgroup.centralizer {π ē})) := by
    rw [hēx]
    exact hCX.2
  have hQ := ggLemmaQ_ambient p π hπ rfl hKn hEbel.1 (fun w hw _ => hker w hw) ē hCle hCp
  obtain ⟨C₀, hC₀le, hC₀p, hC₀map⟩ := hQ
  have hKsub : IsSubnormal K (⊤ : Subgroup (GGRCSNbar r)) :=
    (ggAssemblyIsSubnormal_iff le_top).mpr hK.2.subgroupOf
  have hC₀K : C₀ ≤ K := hC₀le.trans inf_le_left
  have hsubC : IsSubnormal (K ⊓ Subgroup.centralizer {(ē : GGRCSNbar r)})
      (Subgroup.centralizer {(ē : GGRCSNbar r)}) := by
    have h := hKsub.inf (Subgroup.centralizer {(ē : GGRCSNbar r)})
    rwa [top_inf_eq] at h
  have hC₀c : CFSG.IsPComponent p
      (C₀.subgroupOf (Subgroup.centralizer {(ē : GGRCSNbar r)})) :=
    ggPComponent_subgroupOf_of_subnormal p hC₀le hsubC hC₀p
  have hPp : IsPGroup 2 (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))) :=
    CFSG.pCore_isPGroup
  have hep : e' ^ p = 1 := Subtype.ext (by simpa using hEel.2 _ heE)
  have hcent := ggCoprime_centralizer_map
    (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))) hPp hp hp2 hep
  have hcent' : Subgroup.centralizer {(ē : GGRCSNbar r)} =
      (Subgroup.centralizer {e'}).map (QuotientGroup.mk'
        (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))) := by
    rw [← hee']
    exact hcent
  have hC₀Z : C₀ ≤ (Subgroup.centralizer {e'}).map (QuotientGroup.mk'
      (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))) := by
    rw [← hcent']
    exact hC₀le.trans inf_le_right
  have hC₀' : CFSG.IsPComponent p (C₀.subgroupOf ((Subgroup.centralizer {e'}).map
      (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))))) :=
    ggPComponent_subgroupOf_congr p hcent' hC₀c
  have hker2 : IsPGroup 2 (QuotientGroup.mk'
      (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G)))).ker := by
    rw [QuotientGroup.ker_mk']
    exact hPp
  obtain ⟨S, hSY, hSpc, hSmap⟩ := ggPComponent_lift_ambient p _ hp2 hker2 hC₀Z hC₀'
  have hS₀le : S.map (Subgroup.centralizer ({r} : Set G)).subtype ≤
      Subgroup.centralizer ({r, (e' : G)} : Set G) := by
    rw [← ggMap_subtype_centralizer e']
    exact Subgroup.map_mono hSY
  have hS₀pc : CFSG.IsPComponent p ((S.map (Subgroup.centralizer ({r} : Set G)).subtype).subgroupOf
      (Subgroup.centralizer ({r, (e' : G)} : Set G))) :=
    ggPComponent_subgroupOf_congr p (ggMap_subtype_centralizer e')
      (ggPComponent_map_subtype p hSY hSpc)
  have hepord : orderOf (e' : G) = p := orderOf_eq_prime (hEel.2 _ heE) he1
  have heM : (e' : G) ∈ Subgroup.normalizer (G₀ : Set G) := hBsN (hEBs heE)
  have hmk1 := ggMarking_single (hEBs heE) hmark
  have hcomm : Commute r (e' : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hEr heE)).symm
  have hperf' : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({r, (e' : G)} : Set G) →
      ⁅P, P⁆ = P → P ≤ G₀ := by
    intro P hP hPP
    refine hperf P ((hP.trans ?_).trans (hfus.centralizer_le heE he1)) hPP
    exact Subgroup.centralizer_le (by simp)
  have hcomp := hC.2.2.1
  have hD := hcomp.2.2
  have hsurj : ∃ Θ : ↥(S.map (Subgroup.centralizer ({r} : Set G)).subtype) →*
      ↥((C.subgroupOf (Subgroup.centralizer {x})).map
        (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({x} : Set W'))))),
      Function.Surjective Θ := by
    refine ggExists_surjective_trans (ggExists_surjective_map_subtype S) ?_
    refine ggExists_surjective_trans (ggExists_surjective_of_map_eq _ hSmap) ?_
    obtain ⟨Φ, hΦ, -⟩ := ggExists_central_surj π (hC₀K.trans hKW) hC₀map
      (fun w hw => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hC₀K) (hker w hw))
    refine ggExists_surjective_trans ⟨Φ, hΦ⟩ ?_
    refine ggExists_surjective_trans (ggExists_surjective_subgroupOf hCX.1) ?_
    exact ggExists_surjective_of_map_eq _ rfl
  obtain ⟨Θ, hΘ⟩ := hsurj
  exact ggItem5_core hS1' hp hp2 hsimple heM hmk1 hr hr2 hepord hcomm hroot hperf' hS₀le hS₀pc hD
    Θ hΘ

theorem ggItem5_main (hS1' : GGStructSOnePrimeRoot) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ Bs E : Subgroup G} {r : G} (hsimple : IsSimpleGroup ↥G₀)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hmark : LargeEvenMarking ↥G₀ fun _ _ _ I _ θ => ∀ c ∈ Bs,
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ)
    (hperf : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (G₀ : Set G) → ⁅P, P⁆ = P → P ≤ G₀)
    (hEBs : E ≤ Bs) (hEel : IsElemAbelian p E)
    (hfus : GGControlsStrongFusion (Subgroup.normalizer (G₀ : Set G)) E)
    (hr : r ∈ G₀) (hr2 : orderOf r = 2) (hroot : GGIsRootInvolution G₀ r)
    (hEr : E ≤ Subgroup.centralizer ({r} : Set G))
    {K : Subgroup (GGRCSNbar r)} (hK : CFSG.IsComponent K)
    (hEK : ggRCSImg r E ≤ Subgroup.normalizer (K : Set (GGRCSNbar r))) :
    GGRCSAutKIVFlat p (ggRCSImg r (Subgroup.normalizer (G₀ : Set G))) (ggRCSImg r E) K := by
  intro hN
  refine ggItem5_gen hS1' hp hp2 hsimple hBsN hmark hperf hEBs hEel hfus hr hr2 hroot hEr hK hEK
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) ?_
  intro w hw
  have hw' := (QuotientGroup.eq_one_iff w).mp hw
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw')).2

end Main

end CFSG.StandardType
