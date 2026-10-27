module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix

namespace Res6

theorem isSolvable_of_semidirect {X : Type*} [Group X] {N C : Subgroup X} (hN : N.Normal)
    (hNc : IsMulCommutative N) (hC : IsCyclic C) (hNC : N ⊔ C = ⊤) : Group.IsSolvable X := by
  have hNs : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => hNc.is_comm.comm a b
  set π := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective (π.comp C.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ ((N ⊔ C : Subgroup X) : Set X) := by rw [hNC]; exact Set.mem_univ x
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N C (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hN]; exact le_top)] at hx
    obtain ⟨n, hn, c, hc, rfl⟩ := hx
    refine ⟨⟨c, hc⟩, ?_⟩
    have h1 : π n = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    show π c = π (n * c)
    rw [map_mul, h1, one_mul]
  obtain ⟨g, hg⟩ := hC.exists_generator
  have hQs : Group.IsSolvable (X ⧸ N) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← map_mul, ← map_mul, (Commute.zpow_zpow_self g i j).eq]
  exact Group.isSolvable_of_ker_le_range N.subtype π (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

noncomputable def pslEquivPgl_of_char_two (K : Type*) [Field K] [Finite K] (hK : ringChar K = 2) :
    ProjectiveSpecialLinearGroup (Fin 2) K ≃* ProjGenLinGroup (Fin 2) K :=
  have : Fintype K := Fintype.ofFinite K
  MulEquiv.ofBijective (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))
    ⟨ProjectiveSpecialLinearGroup.toPGL_injective, by
      intro x
      obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ x
      exact (CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare A).mpr
        (FiniteField.isSquare_of_char_two hK _)⟩

theorem card_psl_le_six {K : Type*} [Field K] [Fintype K] (hK : Fintype.card K = 2) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) ≤ 6 := by
  have h1 : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) ≤
      Nat.card (SpecialLinearGroup (Fin 2) K) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card (SpecialLinearGroup (Fin 2) K) ≤ Nat.card (GL (Fin 2) K) :=
    Nat.card_le_card_of_injective _ (SpecialLinearGroup.toGL_injective)
  have h3 : Nat.card (GL (Fin 2) K) = 6 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hK]
    norm_num
  omega

theorem psl_simple_or_solvable (k : ℕ) (hk : k ≠ 0) :
    IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 k)) ∨
      Group.IsSolvable (ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 k)) := by
  have hcard := GaloisField.card 2 k hk
  by_cases hk1 : k = 1
  · subst hk1
    right
    have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
    have h2 : Fintype.card (GaloisField 2 1) = 2 := by
      rw [← Nat.card_eq_fintype_card, hcard, pow_one]
    exact CFSG.GroupTheory.groups_order_below_sixty_solvable
      (lt_of_le_of_lt (card_psl_le_six h2) (by norm_num))
  · left
    apply ProjectiveSpecialLinearGroup.rank_two_simple
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

end Res6

theorem kFactL2PerfectSelfNormalizing_holds :
    KFactL2PerfectSelfNormalizing := by
  intro m Y _ _ ⟨e⟩ K hKtop hKbot hKperf
  set F := GaloisField 2 m with hF
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  have hFk : Nat.card F = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hk
  set P := ProjectiveSpecialLinearGroup (Fin 2) F with hP
  set φ : Y ≃* P := e.trans (Sec4.projSLEquivPSL F) with hφ
  set H := K.map φ.toMonoidHom with hH
  have hHbot : H ≠ ⊥ := fun h =>
    hKbot ((Subgroup.map_eq_bot_iff_of_injective K φ.injective).mp h)
  have hHperf : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := (K.equivMapOfInjective _ φ.injective).toMonoidHom)
      (MulEquiv.surjective _)
  suffices hN : Subgroup.normalizer (H : Set P) ≤ H by
    refine le_antisymm ?_ Subgroup.le_normalizer
    intro y hy
    have hy' : φ y ∈ Subgroup.normalizer (H : Set P) := by
      rw [hH, ← Subgroup.map_equiv_normalizer_eq K φ]
      exact ⟨y, hy, rfl⟩
    obtain ⟨y', hy'K, hyy'⟩ := hN hy'
    rwa [show y' = y from φ.injective hyy'] at hy'K
  set N := Subgroup.normalizer (H : Set P) with hNdef
  have hHN : H ≤ N := Subgroup.le_normalizer
  have hNns : ¬ Group.IsSolvable N := by
    intro hs
    have : Group.IsSolvable (H.subgroupOf N) := inferInstance
    have hHs : Group.IsSolvable H := Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hHN).toMonoidHom) (MulEquiv.surjective _)
    have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHbot
    exact Group.IsPerfect.not_isSolvable H hHs
  have key : IsSimpleGroup N → N ≤ H := by
    intro hsimple
    have hn : (H.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHN).mpr le_rfl
    rcases hsimple.eq_bot_or_eq_top_of_normal (H.subgroupOf N) with h | h
    · exfalso
      apply hHbot
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hHN hx⟩ : N) ∈ H.subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · intro x hx
      have : (⟨x, hx⟩ : N) ∈ H.subgroupOf N := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have key' : IsSimpleGroup N ∨ Group.IsSolvable N → N ≤ H := by
    rintro (h | h)
    · exact key h
    · exact absurd h hNns
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 2) hFk N with
    hEA | ⟨z, -, -, hcyc⟩ | ⟨z, -, hzc, ⟨hd⟩⟩ | ⟨-, ⟨ha4⟩⟩ | ⟨-, ⟨hs4⟩⟩ | ⟨-, ⟨ha5⟩⟩ |
      ⟨m', t, -, -, N₀, C, hN₀n, hN₀e, -, hCc, -, -, hN₀C⟩ | ⟨m', hm', -, hpslne⟩ |
      ⟨m', hm', -, hpglne⟩
  · exfalso
    exact hNns (Group.isSolvable_of_comm fun a b => hEA.toIsMulCommutative.is_comm.comm a b)
  · exfalso
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine hNns (Group.isSolvable_of_comm fun a b => ?_)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact (Commute.zpow_zpow_self g i j).eq
  · exfalso
    have hz : z ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := N)
      rw [hzc] at this
      simp at this
    have : NeZero z := ⟨hz⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact hNns (Group.isSolvable_of_surjective (f := hd.symm.toMonoidHom) (MulEquiv.surjective _))
  · exfalso
    have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact hNns (Group.isSolvable_of_surjective (f := ha4.symm.toMonoidHom)
      (MulEquiv.surjective _))
  · exfalso
    have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact hNns (Group.isSolvable_of_surjective (f := hs4.symm.toMonoidHom)
      (MulEquiv.surjective _))
  · exact key (ha5.isSimpleGroup)
  · exfalso
    exact hNns (Res6.isSolvable_of_semidirect hN₀n hN₀e.toIsMulCommutative hCc hN₀C)
  · obtain ⟨hpsl⟩ := hpslne
    refine key' ?_
    rcases Res6.psl_simple_or_solvable m' hm' with h | h
    · exact Or.inl (hpsl.isSimpleGroup)
    · exact Or.inr (Group.isSolvable_of_surjective (f := hpsl.symm.toMonoidHom)
        (MulEquiv.surjective _))
  · obtain ⟨hpgl⟩ := hpglne
    refine key' ?_
    have hcharm : ringChar (GaloisField 2 m') = 2 := ringChar.eq (GaloisField 2 m') 2
    set ε := hpgl.trans (Res6.pslEquivPgl_of_char_two (GaloisField 2 m') hcharm).symm with hε
    rcases Res6.psl_simple_or_solvable m' hm' with h | h
    · exact Or.inl (ε.isSimpleGroup)
    · exact Or.inr (Group.isSolvable_of_surjective (f := ε.symm.toMonoidHom)
        (MulEquiv.surjective _))

theorem step204FinalL2_of_kO3 (hKO3 : Step204YKO3)
    (hZ : Step204FinalL2Z) : Step204FinalL2 :=
  step204FinalL2_of kFactL2PerfectSelfNormalizing_holds (step204YAlphaNe_of hKO3) hZ

end CFSG.RankThree.PartTwo.Sec20
