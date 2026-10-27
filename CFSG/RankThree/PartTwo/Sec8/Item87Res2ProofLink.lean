module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.RankThree.PartTwo.KFacts.K71Item119
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item87Res2Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_self_eq_of_isPerfect {H : Subgroup G} (hH : Group.IsPerfect H) :
    ⁅H, H⁆ = H := by
  have h := congrArg (Subgroup.map H.subtype) hH.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem not_le_theta_of_isPerfect {T M : Subgroup G} (hT : Group.IsPerfect T) (hT1 : T ≠ ⊥) :
    ¬ T ≤ inSubgroup (aschbacherSolvableCore 3) M := by
  intro hle
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 M) :=
    (solvable_prime_complement_core_characterization (H := M) Nat.prime_three).1
  have hθs' : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) M) :=
    Group.isSolvable_of_surjective (M.subtype.subgroupMap_surjective (aschbacherSolvableCore 3 M))
  have hTs : Group.IsSolvable T := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hle)
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  exact Group.IsPerfect.not_isSolvable T hTs

theorem quot_cases_of_isGammaIndex {A Le : Subgroup G} {d : G} {m : ℕ}
    (h : IsGammaIndex A Le d m) :
    (IsGammaTypeRee (Le ⧸ aschbacherSolvableCore 3 Le) m ∧
        IsoSUThree (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))))
          (2 ^ (3 * m))) ∨
      Nonempty (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
        projSL 2 (GaloisField 2 (3 * m))) := by
  set K := inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) with hK
  have hKL : K ≤ Le := (Item87Proof.residual_le _).trans inf_le_left
  obtain ⟨-, -, hm, hcases⟩ := Item87Proof.isGammaIndex_cases h
  have hm3 : 2 ≤ 3 * m := by omega
  rcases hcases with ⟨hRee, F, hF, hFf, hFc, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKL
      (Item87Proof.NoThetaNormal.of_mulEquiv φ (Item87Proof.noThetaNormal_statedSU hFc hm3))
    exact Or.inl ⟨hRee, F, hF, hFf, hFc, ⟨ψ.trans φ⟩⟩
  · obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKL
      (Item87Proof.NoThetaNormal.of_mulEquiv φ (Item87Proof.noThetaNormal_projSL_two hm3))
    exact Or.inr ⟨ψ.trans φ⟩

theorem odd_of_isGammaTypeRee {X : Type} [Group X] {n : ℕ} (h : IsGammaTypeRee X n) : Odd n := by
  obtain ⟨k, -, hk, -⟩ := h
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | hn
  · exfalso
    omega
  · exact hn

theorem ne_bot_inSubgroup_perfectResidual_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    {C : Subgroup Q} (hC : IsQuasisimple C) : inSubgroup perfectResidual C ≠ ⊥ := by
  have hle : C ≤ inSubgroup perfectResidual C := KFacts.le_inSubgroup_perfectResidual hC.1 le_rfl
  have : Nontrivial C := LocalCores.isQuasisimple_nontrivial hC
  intro h
  rw [h, le_bot_iff] at hle
  exact ((Subgroup.nontrivial_iff_ne_bot C).mp this) hle

end Item87Res2Proof


namespace Item87Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem residual_centralizer_ne_bot_of_field {K : Subgroup G} {a : G} {n : ℕ} (hn : 2 ≤ n)
    (htype : (Odd n ∧ IsoSUThree (K ⧸ aschbacherSolvableCore 3 K) (2 ^ (3 * n))) ∨
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField 2 (3 * n))))
    (ha3 : a ^ 3 = 1) (ha : KFacts.InducesStdKind K a .field) :
    inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ≠ ⊥ := by
  have haN : a ∈ Subgroup.normalizer (K : Set G) := ha.mem_normalizer
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by rwa [pow_one]⟩
  have hC : IsQuasisimple (barCentralizer (Subgroup.zpowers a) K) := by
    rcases htype with ⟨hodd, hSU⟩ | he
    · obtain ⟨F, _, _, hF, ⟨φ⟩⟩ :=
        KFacts.isoSUThree_barCentralizer_of_inducesStdKind hodd hSU ha3 ha
      exact LocalCores.isQuasisimple_of_mulEquiv φ.symm
        (Item87Proof.isQuasisimple_statedSU_three hF hn).1
    · obtain ⟨e⟩ := he
      have hout := KFacts.InducesStdKind.inducesOuterTheta K ha (by decide)
      set α := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haN⟩) with hα
      have hα3 : α ^ 3 = 1 := by
        rw [hα, ← map_pow, ← map_pow]
        have : (⟨a, haN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 := Subtype.ext (by simpa)
        rw [this, map_one, map_one]
      have hαout : ¬ KFacts.IsInnerAut α := by
        obtain ⟨hN', hnot⟩ := hout
        exact hnot
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨ι⟩ := KFacts.nonempty_eqLocus_mulEquiv_projSL_two (p := 2) (m := n) (by omega) e hα3
        hαout
      have heq : barCentralizer (Subgroup.zpowers a) K =
          α.toMonoidHom.eqLocus (MonoidHom.id _) := by
        ext z
        rw [KFacts.mem_barCentralizer_zpowers_iff haN]
        rfl
      rw [heq]
      exact LocalCores.isQuasisimple_of_mulEquiv ι.symm (Item87Proof.isQuasisimple_projSL_two hn)
  intro h0
  apply ne_bot_inSubgroup_perfectResidual_of_isQuasisimple hC
  rw [← himg, h0, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]

end Item87Res2Proof

@[expose] def KF87LinkOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G), Sec8Pair G A c L a b X 1 →
    ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 → sec8I L a ≠ ⊥ → sec8J X a ≠ ⊥ →
      ¬ ⁅sec8I L a, sec8J X a⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))

theorem kF87Link_of (hF : KF84Field) (h1 : KF87LinkOne) : KF87Link := by
  intro G _ _ A c L a b X n h hU hI hJ
  obtain ⟨-, -, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact h1 G A c L a b X h hU hI hJ
  · have hAel := h.mem_partTwoF.1
    have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
    set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
    set T := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) with hT
    have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
    have hKX : K ≤ X := h.pairRel.2.2.2.1
    have hTK : T ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := Item87Proof.residual_le _
    have hTp : Group.IsPerfect T := Item87Proof.isPerfect_residual _
    have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) :=
      by simp only [sec8I, hU, ↓reduceIte]
    have hTI : T ≤ sec8I L a := by
      rw [hIdef]
      exact KFacts.le_inSubgroup_perfectResidual hTp
        (le_inf (hTK.trans (inf_le_left.trans hKL)) (hTK.trans inf_le_right))
    have hTJ : T ≤ sec8J X a :=
      KFacts.le_inSubgroup_perfectResidual hTp
        (le_inf (hTK.trans (inf_le_left.trans hKX)) (hTK.trans inf_le_right))
    have hT1 : T ≠ ⊥ := by
      refine Item87Res2Proof.residual_centralizer_ne_bot_of_field hn2 ?_ ha3
        (hF G A c L a b X n h)
      rcases Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex with ⟨hRee, hSU⟩ | hL2
      · exact Or.inl ⟨Item87Res2Proof.odd_of_isGammaTypeRee hRee, hSU⟩
      · exact Or.inr hL2
    intro hle
    apply Item87Res2Proof.not_le_theta_of_isPerfect hTp hT1
      (M := Subgroup.centralizer ({a} : Set G))
    calc T = ⁅T, T⁆ := (Item87Res2Proof.commutator_self_eq_of_isPerfect hTp).symm
      _ ≤ ⁅sec8I L a, sec8J X a⁆ := Subgroup.commutator_mono hTI hTJ
      _ ≤ _ := hle

end CFSG.RankThree.PartTwo.Sec8
