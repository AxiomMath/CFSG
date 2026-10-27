module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrH

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

namespace S127

section Quot

variable {Y : Type} [Group Y]

theorem oTwoUpper_top_normal : (oTwoUpper (⊤ : Subgroup Y)).Normal :=
  ⟨fun _ hn g => conj_mem_oTwoUpper (Subgroup.le_normalizer (Subgroup.mem_top g)) hn⟩

theorem isSimpleGroup_of_isPSL {X : Type} [Group X] (h : IsPSL 2 2 2 X) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 2 h).2

theorem nonabelian_of_isPSL {X : Type} [Group X] (h : IsPSL 2 2 2 X) :
    ∃ a b : X, a * b ≠ b * a := by
  have hs := isSimpleGroup_of_isPSL h
  have h60 := Vol2.Ch10.SecB.C11AmS.card_of_isPSL_two_two_two h
  by_contra hc
  push Not at hc
  have : IsMulCommutative X := ⟨⟨hc⟩⟩
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  have hp := (IsSimpleGroup.prime_card (α := X))
  rw [h60] at hp
  exact absurd hp (by norm_num)

theorem not_isSolvable_of_simple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : ¬ Group.IsSolvable X := by
  intro hsol
  obtain ⟨a, b, hab⟩ := hnc
  have hc := IsSimpleGroup.comm_iff_isSolvable.2 hsol
  exact hab (hc a b)

variable [Finite Y]

theorem centralizer_oTwoUpper_eq_bot (hO : CFSG.Open.pCore 2 Y = ⊥)
    (hs : IsSimpleGroup ↥(oTwoUpper (⊤ : Subgroup Y)))
    (hnc : ∃ a b : ↥(oTwoUpper (⊤ : Subgroup Y)), a * b ≠ b * a) :
    Subgroup.centralizer (oTwoUpper (⊤ : Subgroup Y) : Set Y) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper (⊤ : Subgroup Y) with hK
  have := oTwoUpper_top_normal (Y := Y)
  have hZ : Subgroup.center ↥K = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  have hCK : ∀ c ∈ Subgroup.centralizer (K : Set Y), c ∈ K → c = 1 := by
    intro c hc hcK
    have hcz : (⟨c, hcK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc y y.2)
    rw [hZ, Subgroup.mem_bot] at hcz
    exact congrArg Subtype.val hcz
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer (K : Set Y)) := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (⊤ : Subgroup Y) (Subgroup.mem_top (c : Y))
    refine ⟨k, Subtype.ext ?_⟩
    simpa using hCK _ (Subgroup.pow_mem _ c.2 _) hk
  have hle := le_pCore 2 inferInstance h2
  rw [hO] at hle
  exact le_bot_iff.1 hle

theorem oTwoUpper_top_sup_eq_top {S : Subgroup Y} (hS : IsSylowIn 2 S ⊤) :
    oTwoUpper (⊤ : Subgroup Y) ⊔ S = ⊤ := by
  have h := E1.le_twoResidual_sup_of_isSylowIn hS
  rw [F6.twoResidual_eq_oTwoUpper] at h
  exact top_le_iff.1 h

omit [Finite Y] in
theorem oTwoUpper_top_perfect (hs : IsSimpleGroup ↥(oTwoUpper (⊤ : Subgroup Y)))
    (hnc : ∃ a b : ↥(oTwoUpper (⊤ : Subgroup Y)), a * b ≠ b * a) :
    ⁅oTwoUpper (⊤ : Subgroup Y), oTwoUpper (⊤ : Subgroup Y)⁆ = oTwoUpper (⊤ : Subgroup Y) :=
  Subgroup.isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1.1

theorem twoResidual_eq_perfectCore_of_simple (hs : IsSimpleGroup ↥(oTwoUpper (⊤ : Subgroup Y)))
    (hnc : ∃ a b : ↥(oTwoUpper (⊤ : Subgroup Y)), a * b ≠ b * a) :
    twoResidual (⊤ : Subgroup Y) = perfectCore (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [F6.twoResidual_eq_oTwoUpper]
  refine le_antisymm (le_perfectCore_of_perfect le_top (oTwoUpper_top_perfect hs hnc)) ?_
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := Y)
  have hP : IsSylowIn 2 (P : Subgroup Y) ⊤ :=
    ⟨le_top, P.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact P.not_dvd_index⟩
  have := oTwoUpper_top_normal (Y := Y)
  refine perfectCore_le_of_sup_solvable le_top (Subgroup.Normal.subgroupOf inferInstance _)
    (oTwoUpper_top_sup_eq_top hP).symm (E1.isSolvable_of_isPGroup_two P.isPGroup')

end Quot

end S127

end CFSG.Quasithin.H13
