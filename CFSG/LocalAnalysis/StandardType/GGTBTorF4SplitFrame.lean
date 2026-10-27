module

public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTorus
public import CFSG.LocalAnalysis.StandardType.GGTorusF4Split
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.Open (IsElemAbelian)

theorem standard_split_markedWeyl
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) :
    ∃ eW : WeylGroup .F4 ≃*
        ↥(ggAutomizer (⊤ : Subgroup (adjointGroup .F4 K)) (TableBF4.torusPow K p)),
      ∀ i : Fin Tag.F4.rank,
        (eW (simple .F4 i) : MulAut ↥(TableBF4.torusPow K p)) =
        ggConjAut (TableBF4.torusPow K p)
          (F4AutWeyl.canonicalRep_mem_normalizer_torusPow_F4 K p (simple .F4 i)) := by
  classical
  let V : Subgroup (adjointGroup .F4 K) := TableBF4.torusPow K p
  have hW : ∀ w : WeylGroup .F4, ∃ h ∈ (⊤ : Subgroup (adjointGroup .F4 K)),
      ∃ t ∈ torusGroup .F4 K,
        (h : ModGL .F4 K) = t * canonicalRep (coxeterSystem .F4) K w := by
    intro w
    refine ⟨⟨canonicalRep (coxeterSystem .F4) K w,
      canonicalRep_mem_adjointGroup _ _ _⟩, Subgroup.mem_top _, 1, one_mem _, ?_⟩
    rw [one_mul]
  have hAut : ggAutomizer (⊤ : Subgroup (adjointGroup .F4 K)) V =
      (F4AutWeyl.weylTorusAut K p).range :=
    F4AutWeyl.ggAutomizer_torusPow_eq_range hp hp2 hpK hW
  have hinj : Function.Injective (F4AutWeyl.weylTorusAut K p) :=
    F4AutWeyl.weylTorusAut_injective hp hp2 hpK
  let eW : WeylGroup .F4 ≃*
      ↥(ggAutomizer (⊤ : Subgroup (adjointGroup .F4 K)) V) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hAut.symm)
  refine ⟨eW, fun i => ?_⟩
  rfl

theorem centralizer_torusPow_le_coordHom_range
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) :
    Subgroup.centralizer (TableBF4.torusPow K p : Set (adjointGroup .F4 K)) ≤
      (F4SplitTorus.coordHom (K := K)).range := by
  classical
  intro x hx
  rw [F4SplitTorus.mem_range_coordHom_iff]
  have hpKunits : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpK
  have hCV := F4AutWeyl.F4_adjointGroup_inf_centralizer_torusPow_of_ne_two
    (k := K) hp hp2 hpKunits
  have hxinf : (x : ModGL .F4 K) ∈ adjointGroup .F4 K ⊓
      Subgroup.centralizer {h : ModGL .F4 K | h ∈ torusGroup .F4 K ∧ h ^ p = 1} := by
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hV : (⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ : adjointGroup .F4 K) ∈
        TableBF4.torusPow K p := by
      rw [F4SplitTorus.mem_torusPow_iff]
      refine ⟨?_, ?_⟩
      · rw [F4SplitTorus.mem_range_coordHom_iff]
        exact hh.1
      · exact Subtype.ext hh.2
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx)
      ⟨h, torusGroup_le_adjointGroup_F4 hh.1⟩ hV
    exact congrArg Subtype.val hcomm
  have hxT := hxinf
  rw [hCV] at hxT
  exact hxT

theorem exists_conjugator_torusPow
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hcard : p ^ 4 ≤ Nat.card E) :
    ∃ g : adjointGroup .F4 K,
      E.map (MulAut.conj g).toMonoidHom = TableBF4.torusPow K p := by
  have hT : GGF4ToralRankInput K p :=
    ggF4ToralRankInput_of_three hp hp2 hpK (fun _ => ggF4ThreeRankInput_holds)
  exact hT E hE hcard

end CFSG.StandardType

end
