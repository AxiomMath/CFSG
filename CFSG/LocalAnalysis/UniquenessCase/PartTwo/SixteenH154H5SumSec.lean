module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSecA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_sum_cent_sec [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    (hN : ∀ I : Subgroup W, N L I Z → s16h_SimpleScalar L I Z) {k : ℕ} (hk : k ≤ 3)
    (hS : SumOfNat N L U Z k) (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {F : Subgroup (MulAut (Sec U Z))}
    (hF : F ≤ Subgroup.centralizer (autSec L U Z : Set (MulAut (Sec U Z))))
    (hFe : IsElemAbelian q F) : Nat.card F ≤ q := by
  classical
  obtain ⟨I, hZI, hind, hspan, hNi⟩ := hS
  have hIU : ∀ i, I i ≤ U := fun i => (le_iSup I i).trans (le_sup_right.trans_eq hspan)
  have hss : ∀ i, s16h_SimpleScalar L (I i) Z := fun i => hN (I i) (hNi i)
  have hLI : ∀ i, L ≤ stabSub (I i) := fun i => s16h_le_stabSub_of_stable (hss i).1.2.1
  let Ī : Fin k → Subgroup (Sec U Z) := fun i =>
    (I i).subgroupOf U |>.map (QuotientGroup.mk' (Z.subgroupOf U))
  have hmapZ : (Z.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hQ : ∀ x : Sec U Z, x ^ 2 = 1 := by
    intro x
    obtain ⟨u, rfl⟩ := (QuotientGroup.mk'_surjective (N := Z.subgroupOf U)) x
    have h2 : u ^ 2 = 1 := Subtype.ext (by simpa using hW (u : W))
    have h3 := congrArg (QuotientGroup.mk' (Z.subgroupOf U)) h2
    simpa [map_pow] using h3
  have hstab : ∀ i, ∀ g ∈ autSec L U Z, ∀ x ∈ Ī i, g x ∈ Ī i := fun i =>
    s16h_secIncl_image_stable Z (I i) U (hIU i) (hLI i) hLZ hLU
  have hsimple : ∀ i, Ī i ≠ ⊥ ∧ ∀ J : Subgroup (Sec U Z),
      (∀ g ∈ autSec L U Z, ∀ x ∈ J, g x ∈ J) → J ≤ Ī i → J = ⊥ ∨ J = Ī i := by
    intro i
    refine ⟨?_, fun J hJstab hJle =>
      s16h_secIncl_simple Z (I i) U (hZI i) (hIU i) (hLI i) hLZ hLU (hss i).1 J hJstab hJle⟩
    intro hbot
    obtain ⟨x, hxI, hxZ⟩ := IsConcreteLE.exists_of_lt (hss i).1.1
    have hxU : x ∈ U := hIU i hxI
    have hmem : QuotientGroup.mk' (Z.subgroupOf U) ⟨x, hxU⟩ ∈ Ī i :=
      Subgroup.mem_map.mpr ⟨⟨x, hxU⟩, Subgroup.mem_subgroupOf.mpr hxI, rfl⟩
    rw [hbot] at hmem
    rw [Subgroup.mem_bot] at hmem
    have hmemZ : (⟨x, hxU⟩ : ↥U) ∈ Z.subgroupOf U :=
      (QuotientGroup.eq_one_iff (⟨x, hxU⟩ : ↥U)).mp hmem
    exact hxZ (Subgroup.mem_subgroupOf.mp hmemZ)
  have hend : ∀ i, ∀ f : Sec U Z →* Sec U Z,
      (∀ g ∈ autSec L U Z, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ Ī i, f x ∈ Ī i) →
      (∀ j, j ≠ i → ∀ x ∈ Ī j, f x = 1) →
      (∀ x ∈ Ī i, f x = x) ∨ (∀ x ∈ Ī i, f x = 1) := by
    intro i f hfcomm hfmem _
    exact s16h_secIncl_hend Z (I i) U (hZI i) (hIU i) (hLI i) hLZ hLU (hss i).2 f hfcomm hfmem
  have hspan' : ⨆ i, Ī i = ⊤ := by
    have hZU : Z ≤ U := le_sup_left.trans_eq hspan
    calc ⨆ i, Ī i
        = (⨆ i, (I i).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [Subgroup.map_iSup]
      _ = ((⨆ i, I i).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [s16h_subgroupOf_iSup hIU]
      _ = (((⨆ i, I i) ⊔ Z).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [Subgroup.subgroupOf_sup (iSup_le hIU) hZU, Subgroup.map_sup, hmapZ, sup_bot_eq]
      _ = (U.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [show (⨆ i, I i) ⊔ Z = U by rw [sup_comm]; exact hspan]
      _ = ⊤ := by
            rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
              (QuotientGroup.mk'_surjective (N := Z.subgroupOf U))]
  have hind' : ∀ i, Ī i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), Ī j) = ⊥ := by
    intro i
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxi, hxj⟩ := hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxi
    have hmapj : (⨆ (j : Fin k) (_ : j ≠ i), Ī j)
        = (⨆ (j : Fin k) (_ : j ≠ i), (I j).subgroupOf U).map
            (QuotientGroup.mk' (Z.subgroupOf U)) := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      simp only [Subgroup.map_iSup]
      rfl
    rw [hmapj] at hxj
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hxj
    have hvI : (v : W) ∈ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
      rw [← s16h_subgroupOf_iSup_ne hIU i] at hv
      exact Subgroup.mem_subgroupOf.mp hv
    have hzu : (u : W) ∈ Z := by
      have h1 : (v * u⁻¹ : ↥U) ∈ Z.subgroupOf U := by
        rw [← QuotientGroup.eq_one_iff]
        show QuotientGroup.mk' (Z.subgroupOf U) (v * u⁻¹) = 1
        rw [map_mul, map_inv, hvu, mul_inv_cancel]
      have hz : ((v * u⁻¹ : ↥U) : W) ∈ Z := Subgroup.mem_subgroupOf.mp h1
      have hmem : (u : W) ∈ I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) := by
        refine ⟨Subgroup.mem_subgroupOf.mp hu, ?_⟩
        have h2 : (((v * u⁻¹ : ↥U) : W))⁻¹ ∈ Z := Z.inv_mem hz
        have h3 : (((v * u⁻¹ : ↥U) : W))⁻¹ * (v : W) ∈
            Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j :=
          mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right hvI)
        have hu_eq : (((v * u⁻¹ : ↥U) : W))⁻¹ * (v : W) = (u : W) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [hu_eq] at h3
        exact h3
      exact hind i hmem
    exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr hzu)
  exact s16h_sum_cent_card_le (Q := Sec U Z) (Λ := autSec L U Z) (I := Ī) hQ hk
    hstab hsimple hend hspan' hind' hq hq2 hF hFe

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
