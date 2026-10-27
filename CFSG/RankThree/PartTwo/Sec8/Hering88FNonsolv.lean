module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FCore
public import CFSG.RankThree.PartTwo.Sec8.Hering88DT

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem not_isSolvable_inf_barCentralizer (h45 : Sec4.Item4_5) (hF : KF84Field)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n)
    {Y : Subgroup G} (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) :
    ¬ Group.IsSolvable ↥(barCentralizer (Subgroup.zpowers c) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y) := by
  intro hsolv
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 h.ne_one hAp
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)) L
      h.mem_thetaComponentsAt
  have hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 :=
    not_isUnitaryTwo_three_of_two_le hn2 (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex)
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  set T₀ := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) with hT₀def
  have hT₀ : T₀ ≠ ⊥ := by
    refine Item87Res2Proof.residual_centralizer_ne_bot_of_field hn2 ?_ ha3 (hF G A c L a b X n h)
    rcases Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex with ⟨hRee, hSU⟩ | hL2
    · exact Or.inl ⟨Item87Res2Proof.odd_of_isGammaTypeRee hRee, hSU⟩
    · exact Or.inr hL2
  have hT₀p : Group.IsPerfect T₀ := Item87Proof.isPerfect_residual _
  have hT₀le : T₀ ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := Item87Proof.residual_le _
  have hT₀I : T₀ ≤ sec8I L a := by
    rw [hIdef]
    exact KFacts.le_inSubgroup_perfectResidual hT₀p
      (le_inf (hT₀le.trans (inf_le_left.trans hKL)) (hT₀le.trans inf_le_right))
  have hKcb : K ≤ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
    le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hLc))
      ((Item87Proof.residual_le _).trans inf_le_right)
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer ((Subgroup.closure ({c, b} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hkc, hkb⟩ := Subgroup.mem_inf.mp (hKcb hk)
      rcases hw with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hk' d hdcl).symm
  have hIL : sec8I L a ≤ L := by
    rw [hIdef]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
  have hdL : d ∈ Subgroup.normalizer (L : Set G) := hAL hdA
  have hda : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc d hdA a h.a_mem)
  have hdI : d ∈ Subgroup.normalizer (sec8I L a : Set G) := by
    rw [hIdef]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ (Subgroup.inf_normalizer_le_normalizer_inf ⟨hdL, Subgroup.le_normalizer hda⟩)
  set T := inSubgroup perfectResidual (sec8I L a ⊓ Subgroup.centralizer ({d} : Set G)) with hT
  have hTp : Group.IsPerfect T := Item87Proof.isPerfect_residual _
  have hTI : T ≤ sec8I L a ⊓ Subgroup.centralizer ({d} : Set G) := Item87Proof.residual_le _
  have hTY : T ≤ Y := hTI.trans (inf_le_left.trans hIY)
  have hT₀T : T₀ ≤ T :=
    KFacts.le_inSubgroup_perfectResidual hT₀p (le_inf hT₀I (hT₀le.trans (inf_le_left.trans hKd)))
  have hT1 : T ≠ ⊥ := fun hbot => hT₀ (le_bot_iff.mp (hbot ▸ hT₀T))
  have hπT : imageModTheta Y T = inSubgroup perfectResidual
      (imageModTheta Y (sec8I L a) ⊓ barCentralizer (Subgroup.zpowers d) Y) :=
    imageModTheta_residual_inf_centralizer_eq hIY hdN hdI hd3
  have hπI : imageModTheta Y (sec8I L a) ≤ barCentralizer (Subgroup.zpowers c) Y := by
    rw [← KFacts.imageModTheta_centralizer_eq hcN ⟨1, by simpa using hc3⟩]
    exact imageModTheta_mono' (le_inf hIY (hIL.trans hLc))
  have hPle : imageModTheta Y T ≤
      barCentralizer (Subgroup.zpowers c) Y ⊓ barCentralizer (Subgroup.zpowers d) Y := by
    rw [hπT]
    exact (Item87Proof.residual_le _).trans (inf_le_inf_right _ hπI)
  have hPperf : Group.IsPerfect (imageModTheta Y T) := by
    rw [hπT]
    exact Item87Proof.isPerfect_residual _
  have hPbot : imageModTheta Y T = ⊥ := by
    by_contra hne
    haveI : Nontrivial (imageModTheta Y T) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI := hsolv
    have hs : Group.IsSolvable (imageModTheta Y T) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPle)
    exact Group.IsPerfect.not_isSolvable (imageModTheta Y T) hs
  exact Item87Res2Proof.not_le_theta_of_isPerfect hTp hT1 (M := Y)
    (Hering88D.le_theta_of_imageModTheta_eq_bot hTY hPbot)

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
