module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoiceCentralizer
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeEight
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeIWChoiceNormJ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_centralizer_A_eq_J (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) :
    nineI V K ⊓ Subgroup.centralizer (A : Set G) =
      ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K := by
  classical
  haveI : IsMulCommutative ↥(nineI V K) := hI.abelian.1
  let R := pCoreOf 2 K
  let I := nineI V K
  let J := ⨆ B ∈ nineOmegaIn V K S, B ⊓ R
  let U := conjSubgroup A x
  obtain ⟨a, P, ha, haR, hPK, hPcard, hXP, hPclosure, hinv⟩ := nine3_exists_inverted_P hc hI
  haveI : Fintype ↥P := Fintype.ofFinite _
  have hPodd : Odd (Nat.card ↥P) := by
    rw [hPcard]
    exact hc.core.hyp.base.prime.odd_of_ne_two hc.core.hyp.base.odd
  have hCP_le_J : I ⊓ Subgroup.centralizer (P : Set G) ≤ J :=
    nine3_centralizer_P_le_J hc hI ha hPK hPcard hPodd hXP hinv
  have hA0_le_J : A ⊓ R ≤ J := le_iSup₂_of_le A hc.core.A_mem_nineOmegaIn le_rfl
  have hJ_le_I : J ≤ I := by
    refine iSup₂_le fun B hB => ?_
    calc B ⊓ R = B ⊓ I := (Nine3Core.nineI_inf_eq hc.core hB).symm
      _ ≤ I := inf_le_right
  have hJ_le_Z : J ≤ nineZ V K S :=
    iSup₂_le fun B hB => inf_le_left.trans (le_iSup₂_of_le B hB le_rfl)
  have hZ_le_W : nineZ V K S ≤ nineW V S := by
    rw [hc.core.nineW_eq]
    exact le_sup_right
  have hJ_le_W : J ≤ nineW V S := hJ_le_Z.trans hZ_le_W
  have hA_le_W : A ≤ nineW V S := le_iSup₂_of_le A hc.core.A_mem_nineDelta le_rfl
  have hJ_le_C : J ≤ I ⊓ Subgroup.centralizer (A : Set G) := by
    refine le_inf hJ_le_I ?_
    intro j hj
    exact Subgroup.mem_centralizer_iff.mpr (fun a' ha' =>
      hc.core.nineW_mul_comm (hA_le_W ha') (hJ_le_W hj))
  have hle : I ⊓ Subgroup.centralizer (A : Set G) ≤ J := by
    rw [nine3_centralizer_A_eq_sup hc hI]
    apply sup_le hA0_le_J
    rintro y ⟨⟨hyI, hyA⟩, hyU⟩
    have hy2 : y * y = 1 := by
      have h := hI.abelian.2 y hyI
      simpa [pow_two] using h
    have huU : x⁻¹ * a * x ∈ U := by
      rw [show U = conjSubgroup A x from rfl, CFSG.Quasithin.mem_conjSubgroup_iff]
      have h : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
      rw [h]
      exact ha
    have hcomm_ya : y * a = a * y := ((Subgroup.mem_centralizer_iff.mp hyA) a ha).symm
    have hcomm_yu : y * (x⁻¹ * a * x) = (x⁻¹ * a * x) * y :=
      ((Subgroup.mem_centralizer_iff.mp hyU) (x⁻¹ * a * x) huU).symm
    have hgen : ({a, x⁻¹ * a * x} : Set G) ⊆
        (Subgroup.centralizer ({y} : Set G) : Set G) := by
      intro z hz
      exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
        rw [Set.mem_singleton_iff] at hw
        subst hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hcomm_ya
        · exact hcomm_yu)
    have hPcent : P ≤ Subgroup.centralizer ({y} : Set G) :=
      hPclosure.trans ((closure_le (K := Subgroup.centralizer ({y} : Set G))).mpr hgen)
    have hPcentZ : P ≤ Subgroup.centralizer
        ((Subgroup.zpowers y : Subgroup G) : Set G) := by
      intro p hp
      exact Subgroup.mem_centralizer_iff.mpr (fun w hw => by
        rcases nine3_mem_zpowers_involution hy2 hw with hw1 | hw2
        · subst w
          simp
        · subst w
          exact Subgroup.mem_centralizer_iff.mp (hPcent hp) y (Set.mem_singleton y))
    have hyP : y ∈ Subgroup.centralizer (P : Set G) :=
      (Subgroup.le_centralizer_iff.mp hPcentZ) (Subgroup.mem_zpowers y)
    exact hCP_le_J ⟨hyI, hyP⟩
  exact le_antisymm hle hJ_le_C

theorem nine3IW_of_choice (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S) :
    Nine3IW V K S g := by
  unfold Nine3IW
  apply le_antisymm
  · intro y hy
    obtain ⟨hyI, hyW⟩ := Subgroup.mem_inf.mp hy
    have hAW : A ≤ nineW V S := le_iSup₂_of_le A hc.core.A_mem_nineDelta le_rfl
    have hyC : y ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun a' ha' =>
        hc.core.nineW_mul_comm (hAW ha') hyW)
    have hyJ : y ∈ ⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K := by
      rw [← nine3_centralizer_A_eq_J hc hI]
      exact ⟨hyI, hyC⟩
    exact ⟨hyI, (show (⨆ B ∈ nineOmegaIn V K S, B ⊓ pCoreOf 2 K) ≤ nineW0 V K S g
      from le_sup_right) hyJ⟩
  · intro y hy
    obtain ⟨hyI, hyW0⟩ := Subgroup.mem_inf.mp hy
    exact ⟨hyI, hc.nineW0_le_nineW hyW0⟩

end CFSG.LocalAnalysis.WeakClosure81
