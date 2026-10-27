module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.GroupTheory.SteinbergCEFixedResidual
public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem mem_thetaComponentsIn_sec11K_inf' {L Y : Subgroup G} {c e : G}
    (hLc : L ∈ thetaComponentsAt 3 c) (hY : Y ∈ thetaComponentsAt 3 e)
    (hKY : Sec11.sec11K L e ≤ Y) (hq : IsQuasisimple (lBar (Sec11.sec11K L e))) :
    Sec11.sec11K L e ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
  set K := Sec11.sec11K L e with hK
  obtain ⟨hLc', hL'⟩ := mem_thetaComponentsIn_iff.mp hLc
  set Z := Y ⊓ Subgroup.centralizer ({c} : Set G) with hZdef
  have hKZ : K ≤ Z := le_inf hKY ((Sec11.sec11K_le L e).trans hLc')
  set T := K.subgroupOf Z with hT
  set eT : T ≃* K := Subgroup.subgroupOfEquivOfLe hKZ with heT
  refine mem_thetaComponentsIn_iff.mpr ⟨hKZ, ?_, ?_, ?_⟩
  · have hKp : Group.IsPerfect K := Sec6.isPerfect_inSubgroup_perfectResidual _
    exact Group.IsPerfect.ofSurjective (f := eT.symm.toMonoidHom) eT.symm.surjective
  · set ι : Z →* Subgroup.centralizer ({c} : Set G) :=
      Z.subtype.codRestrict _ (fun z => z.2.2) with hι
    set MD := (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap ι with hMD
    have hMDsn : MD.IsSubnormal := hL'.2.1.comap ι
    have hTMD : T ≤ MD := by
      intro t ht
      rw [hT, Subgroup.mem_subgroupOf] at ht
      rw [hMD, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact Sec11.sec11K_le L e ht
    have hTn : (T.subgroupOf MD).Normal := by
      constructor
      intro t ht m
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
      have hmL : ((m : Z) : G) ∈ L := m.2
      have hmM : ((m : Z) : G) ∈ L ⊓ Subgroup.centralizer ({e} : Set G) :=
        ⟨hmL, Sec6.le_centralizer_of_mem_thetaComponentsAt hY (m : Z).2.1⟩
      have := GroupTheory.conj_mem_inSubgroup_perfectResidual hmM ht
      simpa [hK, Sec11.sec11K] using this
    exact Subgroup.IsSubnormal.trans hTMD hTn.isSubnormal hMDsn
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eT (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
        Nat.prime_three eT)).symm hq

end CFSG.RankThree.PartTwo.Sec21.Hering2125
