module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Open.StatedAPI
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem fixSubgroup_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem scalars_subgroupOf_le_center {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (H : Subgroup (GL ι K)) :
    (LargeEvenScalars ι K).subgroupOf H ≤ Subgroup.center H := by
  intro z hz
  rw [Subgroup.mem_subgroupOf] at hz
  rw [LargeEvenScalars] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.mp (by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact hz) (g : GL ι K)

theorem ggNbrLSideSp_components {ℓ : ℕ} {K : Type} [Field K] [Finite K]
    (x : StatedSp ℓ K) (A₁ A₂ : Subgroup (StatedSp ℓ K))
    (hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a)
    (hjoin : A₁ ⊔ A₂ = Subgroup.centralizer ({x} : Set (StatedSp ℓ K)))
    (h₁ : CFSG.IsQuasisimple ↥⁅A₁, A₁⁆ ∨ Group.IsSolvable ↥A₁)
    (h₂ : CFSG.IsQuasisimple ↥⁅A₂, A₂⁆ ∨ Group.IsSolvable ↥A₂)
    (J : Subgroup (LargeEvenProj (LargeEvenSpGroup K ℓ)))
    (hJ : CFSG.Open.IsComponentOf J
      (Subgroup.centralizer ({LargeEvenProjMk (LargeEvenSpGroup K ℓ) x} :
        Set (LargeEvenProj (LargeEvenSpGroup K ℓ))))) :
    (CFSG.IsQuasisimple ↥⁅A₁, A₁⁆ ∧ J = ⁅A₁, A₁⁆.map (LargeEvenProjMk (LargeEvenSpGroup K ℓ))) ∨
      (CFSG.IsQuasisimple ↥⁅A₂, A₂⁆ ∧ J = ⁅A₂, A₂⁆.map (LargeEvenProjMk (LargeEvenSpGroup K ℓ))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set π : StatedSp ℓ K →* LargeEvenProj (LargeEvenSpGroup K ℓ) :=
    LargeEvenProjMk (LargeEvenSpGroup K ℓ) with hπdef
  have hsurj : Function.Surjective π := by
    rw [hπdef]
    exact QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center (StatedSp ℓ K) := by
    rw [hπdef]
    rw [show (LargeEvenProjMk (LargeEvenSpGroup K ℓ)).ker =
        (LargeEvenScalars (Fin ℓ ⊕ Fin ℓ) K).subgroupOf (LargeEvenSpGroup K ℓ) from
      QuotientGroup.ker_mk' _]
    exact scalars_subgroupOf_le_center (LargeEvenSpGroup K ℓ)
  let A : Bool → Subgroup (StatedSp ℓ K) := fun b => if b then A₁ else A₂
  have hA0 : A false = A₂ := rfl
  have hA1 : A true = A₁ := rfl
  have hjoin' : (⨆ i : Bool, A i) = Subgroup.centralizer ({x} : Set (StatedSp ℓ K)) := by
    rw [iSup_bool_eq, hA1, hA0, hjoin]
  have hcomm : ∀ i j : Bool, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b := by
    intro i j hij a ha b hb
    cases i <;> cases j
    · exact absurd rfl hij
    · exact (hc b (by simpa [A] using hb) a (by simpa [A] using ha)).symm
    · exact hc a (by simpa [A] using ha) b (by simpa [A] using hb)
    · exact absurd rfl hij
  have htame : ∀ i : Bool, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i) := by
    intro i
    cases i
    · simpa [A] using h₂
    · simpa [A] using h₁
  have hmain := components_conj_of_orbit_family (X := StatedSp ℓ K)
    (T := LargeEvenProj (LargeEvenSpGroup K ℓ)) π hsurj hker x A hcomm hjoin' htame
  have hfix : fixSubgroup (MulAut.conj (π x)) =
      Subgroup.centralizer ({π x} : Set (LargeEvenProj (LargeEvenSpGroup K ℓ))) :=
    fixSubgroup_conj_eq_centralizer _
  obtain ⟨i, hq, hJeq⟩ := hmain J (by rw [hfix]; exact hJ)
  cases i
  · exact Or.inr ⟨hq, hJeq⟩
  · exact Or.inl ⟨hq, hJeq⟩

end CFSG.StandardType
