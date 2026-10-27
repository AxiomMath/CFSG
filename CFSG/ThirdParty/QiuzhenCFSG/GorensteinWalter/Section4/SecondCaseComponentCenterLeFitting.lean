module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The center of a component lies in the Fitting subgroup of the ambient group

Fact 1.9 of Bender's dihedral-Sylow paper (refs/bender-dihedral-sylow.tex)
asserts, in the second case, that the center of the selected component `E`
lies in the Fitting subgroup `F(M)` of the maximal subgroup `M`.  This is
the group-theoretic transfer behind the source's "|F(M)| is prime to q by
(7), whence Z(E) = 1" step (L795--797): the equation-(7) prime information
`Nat.Coprime (Nat.card (fittingSubgroupOf M)) q` transfers verbatim to the
odd center `Subgroup.center E` via `Z(E) ≤ F(M)`.

The three theorems below are stated generically for any component `E` of a
finite subgroup `M` normal in `M`; the second-case data
`d.E_component`, `d.E_normal` instantiate them in
`SecondCaseLinearEquationNine.lean`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The center of a component `E` of `M` (with `E` normal in `M`) lies in
the Fitting subgroup of `M`: the center is characteristic in `E`, hence
normal in `M`, and it is abelian, hence nilpotent.  This is the Fact-1.9
transfer of `refs/bender-dihedral-sylow.tex` L795--797. -/
public theorem component_center_le_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (M E : Subgroup G) (hEcomp : IsComponentOf E M) (hEnorm : IsNormalIn E M) :
    (Subgroup.center E).map E.subtype ≤ fittingSubgroupOf M := by
  let Z : Subgroup G := (Subgroup.center E).map E.subtype
  have hZleM : Z ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨e, he, rfl⟩
    exact hEcomp.1 e.2
  have hZnormal : IsNormalIn Z M := by
    refine ⟨hZleM, ?_⟩
    intro m hm z hz
    rcases Subgroup.mem_map.mp hz with ⟨e, he, rfl⟩
    have hme : m * (e : G) * m⁻¹ ∈ E := hEnorm.2 m hm (e : G) e.2
    let eM : E := ⟨m * (e : G) * m⁻¹, hme⟩
    have heMcenter : eM ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hym : (m⁻¹ : G) * (y : G) * m ∈ E := by
        simpa using hEnorm.2 m⁻¹ (M.inv_mem hm) (y : G) y.2
      have hecomm :
          (⟨m⁻¹ * (y : G) * m, hym⟩ : E) * e = e * (⟨m⁻¹ * (y : G) * m, hym⟩ : E) :=
        (Subgroup.mem_center_iff.mp he) (⟨m⁻¹ * (y : G) * m, hym⟩ : E)
      calc
        (y : G) * (m * (e : G) * m⁻¹) =
            m * ((m⁻¹ * (y : G) * m) * (e : G)) * m⁻¹ := by group
        _ = m * ((e : G) * (m⁻¹ * (y : G) * m)) * m⁻¹ := by
          have hval : ((m⁻¹ * (y : G) * m) : G) * (e : G) =
              (e : G) * (m⁻¹ * (y : G) * m) :=
            congrArg Subtype.val hecomm
          rw [hval]
        _ = (m * (e : G) * m⁻¹) * (y : G) := by group
    exact Subgroup.mem_map.mpr ⟨eM, heMcenter, rfl⟩
  have hZnil : Group.IsNilpotent Z := by
    let : CommGroup (Subgroup.center E) :=
      { (inferInstance : Group (Subgroup.center E)) with
        mul_comm := by
          intro a b
          apply Subtype.ext
          simpa using ((Subgroup.mem_center_iff.mp a.2) (b : E)).symm }
    have hZ0 : Group.IsNilpotent (Subgroup.center E) := inferInstance
    let eZ : (Subgroup.center E) ≃* Z :=
      Subgroup.equivMapOfInjective (Subgroup.center E) E.subtype E.subtype_injective
    exact Group.nilpotent_of_mulEquiv (G := Subgroup.center E) (G' := Z) eZ
  exact le_fittingSubgroupOf_of_isNormalIn_nilpotent hZleM hZnormal hZnil

/-- The cardinal form: `|Z(E)|` divides `|F(M)|`. -/
public theorem component_center_card_dvd_fittingSubgroupOf
    {G : Type u} [Group G] [Finite G]
    (M E : Subgroup G) (hEcomp : IsComponentOf E M) (hEnorm : IsNormalIn E M) :
    Nat.card (Subgroup.center E) ∣ Nat.card (fittingSubgroupOf M) := by
  have hle := component_center_le_fittingSubgroupOf M E hEcomp hEnorm
  have hdvd : Nat.card ((Subgroup.center E).map E.subtype) ∣
      Nat.card (fittingSubgroupOf M) :=
    Subgroup.card_dvd_of_le hle
  have hcard : Nat.card ((Subgroup.center E).map E.subtype) =
      Nat.card (Subgroup.center E) :=
    Subgroup.card_map_of_injective (K := Subgroup.center E) (f := E.subtype)
      E.subtype_injective
  rwa [hcard] at hdvd

/-- The exact coprimality transfer: the equation-(7) prime information
`|F(M)|` prime to `q` implies `|Z(E)|` prime to `q`.  This is the precise
coprimality hypothesis required by the missing odd-center `PSL₂` cover
(`PSL2CenterlessCover` in `SecondCaseLinearEquationNine.lean`). -/
public theorem component_center_coprime_of_fitting_coprime
    {G : Type u} [Group G] [Finite G]
    (M E : Subgroup G) (hEcomp : IsComponentOf E M) (hEnorm : IsNormalIn E M)
    {q : ℕ} (hFMcoprime : Nat.Coprime (Nat.card (fittingSubgroupOf M)) q) :
    Nat.Coprime (Nat.card (Subgroup.center E)) q :=
  hFMcoprime.coprime_dvd_left
    (component_center_card_dvd_fittingSubgroupOf M E hEcomp hEnorm)

end CFSG.GorensteinWalter
