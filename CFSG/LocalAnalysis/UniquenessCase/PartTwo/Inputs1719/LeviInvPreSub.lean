module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvBarSub

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G] {P : Subgroup G}

omit [Finite G] in
theorem barSub_normal {X : Subgroup G} (hX : (X.subgroupOf P).Normal) : (barSub P X).Normal :=
  hX.map _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem barSub_mono {X Y : Subgroup G} (h : X ≤ Y) : barSub P X ≤ barSub P Y :=
  Subgroup.map_mono fun _ hx => h hx

theorem barSub_opp {X : Subgroup G} (hX : X ≤ P) : barSub P (Opp 2 X) = Opp 2 (barSub P X) := by
  rw [barSub, barSub, subgroupOf_opp hX, map_opp']

theorem barSub_oUpperTwo {X : Subgroup G} (hX : X ≤ P) :
    barSub P (S17.oUpperTwo X) = S17.oUpperTwo (barSub P X) := by
  rw [barSub, barSub, subgroupOf_oUpperTwo hX, map_oUpperTwo']

omit [Finite G] in
theorem barSub_sup {X Y : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P) :
    barSub P (X ⊔ Y) = barSub P X ⊔ barSub P Y := by
  rw [barSub, subgroupOf_sup_of_le hX hY, Subgroup.map_sup]

omit [Finite G] in
theorem barSub_iSup {ι : Type*} {X : ι → Subgroup G} (hX : ∀ i, X i ≤ P) :
    barSub P (⨆ i, X i) = ⨆ i, barSub P (X i) := by
  rw [barSub, subgroupOf_iSup hX, Subgroup.map_iSup]

omit [Finite G] in
theorem barSub_commutator {X Y : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P) :
    barSub P ⁅X, Y⁆ = ⁅barSub P X, barSub P Y⁆ := by
  rw [barSub, barSub, barSub, subgroupOf_commutator hX hY, Subgroup.map_commutator]

omit [Finite G] in
theorem barSub_pCoreOf : barSub P (pCoreOf 2 P) = ⊥ :=
  (barSub_eq_bot_iff (Subgroup.map_subtype_le _)).mpr le_rfl

omit [Finite G] in
theorem barSub_le_iff {X Y : Subgroup G} (hX : X ≤ P) (hOY : pCoreOf 2 P ≤ Y) (hY : Y ≤ P) :
    barSub P X ≤ barSub P Y ↔ X ≤ Y := by
  refine ⟨fun h => ?_, barSub_mono⟩
  have hk : (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).ker ≤ Y.subgroupOf P := by
    rw [QuotientGroup.ker_mk', ← subgroupOf_pCoreOf]
    exact fun x hx => hOY hx
  have h1 := Subgroup.comap_mono (f := QuotientGroup.mk' (CFSG.pCore 2 ↥P)) h
  rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, sup_of_le_left hk] at h1
  rw [← map_subtype_subgroupOf hX, ← map_subtype_subgroupOf hY]
  exact Subgroup.map_mono (le_sup_left.trans h1)

abbrev preSub (P : Subgroup G) (A : Subgroup (Bar2 P)) : Subgroup G :=
  (A.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).map P.subtype

omit [Finite G] in
theorem preSub_le (A : Subgroup (Bar2 P)) : preSub P A ≤ P := Subgroup.map_subtype_le _

omit [Finite G] in
theorem pCoreOf_le_preSub (A : Subgroup (Bar2 P)) : pCoreOf 2 P ≤ preSub P A := by
  intro x hx
  have hxP : x ∈ P := Subgroup.map_subtype_le _ hx
  refine ⟨⟨x, hxP⟩, ?_, rfl⟩
  have hk : (⟨x, hxP⟩ : ↥P) ∈ CFSG.pCore 2 ↥P := by
    rw [← subgroupOf_pCoreOf]
    exact hx
  show QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨x, hxP⟩ ∈ A
  rw [show QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨x, hxP⟩ = 1 from
    (QuotientGroup.eq_one_iff _).mpr hk]
  exact A.one_mem

omit [Finite G] in
theorem preSub_subgroupOf (A : Subgroup (Bar2 P)) :
    (preSub P A).subgroupOf P = A.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) :=
  Subgroup.comap_map_eq_self_of_injective P.subtype_injective _

omit [Finite G] in
theorem barSub_preSub (A : Subgroup (Bar2 P)) : barSub P (preSub P A) = A := by
  rw [barSub, preSub_subgroupOf]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) A

omit [Finite G] in
theorem preSub_normal {A : Subgroup (Bar2 P)} (hA : A.Normal) :
    ((preSub P A).subgroupOf P).Normal := by
  rw [preSub_subgroupOf]
  exact hA.comap _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
