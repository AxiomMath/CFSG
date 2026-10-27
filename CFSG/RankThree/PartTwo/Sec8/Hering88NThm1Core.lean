module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NInner
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Hering88NClassOneModels

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


theorem inf_centralizer_eq_of_mem_closure {G : Type} [Group G] [Finite G] {A W : Subgroup G}
    {w v d : G} (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hwA : w ∈ A) (hvA : v ∈ A)
    (hdcl : d ∈ Subgroup.closure ({w, v} : Set G)) (hw1 : w ≠ 1) (hdw : d ∉ Subgroup.zpowers w)
    (hWw : W ≤ Subgroup.centralizer ({w} : Set G)) :
    W ⊓ Subgroup.centralizer ({d} : Set G) = W ⊓ Subgroup.centralizer ({v} : Set G) := by
  have hCdw : Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer {w} ≤
      Subgroup.centralizer {w} ⊓ Subgroup.centralizer {v} :=
    Item87Proof.inf_centralizer_le_of_mem_closure hAel hwA hvA hdcl hw1 hdw
  ext u
  constructor
  · rintro ⟨huW, hud⟩
    exact ⟨huW, (hCdw ⟨hud, hWw huW⟩).2⟩
  · rintro ⟨huW, huv⟩
    refine ⟨huW, ?_⟩
    have huw := hWw huW
    have hu' : u ∈ Subgroup.centralizer
        ((Subgroup.closure ({w, v} : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp huw).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp huv).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hu' d hdcl).symm

theorem classOne_transfer (h47 : Sec4.Inputs47ClassesD4)
    {G : Type} [Group G] [Finite G] {M Y W : Subgroup G} {a v x d : G}
    (haN : a ∈ Subgroup.normalizer (M : Set G)) (ha3 : a ^ 3 = 1)
    (haout : Sec4.InducesOuterTheta a M)
    (hvN : v ∈ Subgroup.normalizer (M : Set G)) (hv3 : v ^ 3 = 1) (hav : a * v = v * a)
    (hM1 : IsoTrialityD4 (M ⧸ aschbacherSolvableCore 3 M) 1 ∨
      IsoGTwoEven (M ⧸ aschbacherSolvableCore 3 M) (3 * 1))
    (hG2M : IsoGTwoEven (barCentralizer (Subgroup.zpowers a) M) 1)
    (hKv : Nonempty (imageModTheta M (inSubgroup perfectResidual
      (M ⊓ Subgroup.centralizer ({v} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * 1))))
    (hY1 : IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) 1 ∨
      IsoGTwoEven (Y ⧸ aschbacherSolvableCore 3 Y) (3 * 1))
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : x ^ 3 = 1)
    (hxout : Sec4.InducesOuterTheta x Y)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers x) Y) 1)
    (hWdef : W = inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)))
    (hWY : W ≤ Y)
    (hMW : imageModTheta Y W = inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) Y))
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) (hd3 : d ^ 3 = 1) (hxd : x * d = d * x)
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hvW : v ∈ Subgroup.normalizer (W : Set G))
    (hcd : W ⊓ Subgroup.centralizer ({d} : Set G) = W ⊓ Subgroup.centralizer ({v} : Set G)) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * 1))) := by
  classical
  have hWM : W ≤ M := by
    rw [hWdef]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have hWimg : imageModTheta M W =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M) := by
    rw [hWdef]
    exact KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  have e1 := factorization_card_inf_perfectResidual_of_isoGTwoEven_one hG2
    (barCentralizer (Subgroup.zpowers d) Y)
  have e2 : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) Y) ⊓
      barCentralizer (Subgroup.zpowers d) Y =
        imageModTheta Y (W ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [Hering88F.imageModTheta_inf_centralizer_eq hWY hdN hdW hd3, hMW]
  have e3 := factorization_card_imageModTheta
    (inf_le_left.trans hWY : W ⊓ Subgroup.centralizer ({d} : Set G) ≤ Y)
  have e4 := factorization_card_imageModTheta
    (inf_le_left.trans hWM : W ⊓ Subgroup.centralizer ({v} : Set G) ≤ M)
  have e5 : imageModTheta M (W ⊓ Subgroup.centralizer ({v} : Set G)) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M) ⊓
        barCentralizer (Subgroup.zpowers v) M := by
    rw [Hering88F.imageModTheta_inf_centralizer_eq hWM hvN hvW hv3, hWimg]
  have e6 := factorization_card_inf_perfectResidual_of_isoGTwoEven_one hG2M
    (barCentralizer (Subgroup.zpowers v) M)
  have h3Y : (Nat.card ↥(barCentralizer (Subgroup.zpowers x) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y)).factorization 3 =
        (Nat.card ↥(barCentralizer (Subgroup.zpowers a) M ⊓
          barCentralizer (Subgroup.zpowers v) M)).factorization 3 := by
    rw [← e1, e2, e3, hcd, ← e4, e5, e6]
  obtain ⟨hvin, hvne⟩ := isInnerAut_of_residual_projSL h47 hvN hv3 hM1 hG2M hKv
  have hDM : ClassOneDichotomy M a v := by
    rcases hM1 with hD | hG
    · obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
      exact classOne_d4 h47 haN hvN hav ha3 hv3 haout hvin hvne hK hσ e hG2M
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG
      exact classOne_g2 haN hvN hav ha3 hv3 haout hvin hvne (by rw [hK]) e
  have h3M : (Nat.card ↥(barCentralizer (Subgroup.zpowers a) M ⊓
      barCentralizer (Subgroup.zpowers v) M)).factorization 3 = 2 := by
    rcases hDM with ⟨-, h2⟩ | ⟨hne', -⟩
    · exact h2
    · exact absurd hKv hne'
  have hDY : ClassOneDichotomy Y x d := by
    rcases hY1 with hD | hG
    · obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
      exact classOne_d4 h47 hxN hdN hxd hx3 hd3 hxout hin hne hK hσ e hG2
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG
      exact classOne_g2 hxN hdN hxd hx3 hd3 hxout hin hne (by rw [hK]) e
  rcases hDY with ⟨hL2, -⟩ | ⟨-, h3⟩
  · exact hL2
  · rw [h3Y, h3M] at h3
    norm_num at h3

theorem classBOne_core (h45 : Sec4.Item4_5) (h47 : Sec4.Inputs47ClassesD4)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} (h : Sec8Pair G A c L a b X 1)
    (hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    (hL1 : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) 1 ∨
      IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * 1))
    (hKL2 : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * 1))))
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hcout : Sec4.InducesOuterTheta c Y)
    (hY1 : IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) 1 ∨
      IsoGTwoEven (Y ⧸ aschbacherSolvableCore 3 Y) (3 * 1))
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) 1)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdc : d ∉ Subgroup.zpowers c)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * 1))) := by
  classical
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hAel := h.mem_partTwoF.1
  obtain ⟨hbA, -, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hb3 : b ^ 3 = 1 := hA3 b hbA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 h.ne_one hAp
      (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)) L
      h.mem_thetaComponentsAt
  have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hAL hbA
  have haout : Sec4.InducesOuterTheta a L := h.toHyp81.inducesOuterTheta
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  have hG2L : IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) 1 := h.gTwo hL1
  have hIL_img : imageModTheta L (sec8I L a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) := by
    rw [hIdef]
    exact KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  have hI : sec8I L a ≠ ⊥ := by
    intro hbot
    have h1 := card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2L
    rw [← hIL_img, hbot] at h1
    simp [imageModTheta] at h1
  have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
  have hIL : sec8I L a ≤ L := by
    rw [hIdef]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have hM1 := Hering88E.imageModTheta_sec8I_eq_perfectResidual kF87Cent_holds h hUn hI hY hIY hcN
    (isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2)
  have hda : d ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc d hdA a h.a_mem)
  have hba : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc b hbA a h.a_mem)
  have hdI : d ∈ Subgroup.normalizer (sec8I L a : Set G) := by
    rw [hIdef]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ (Subgroup.inf_normalizer_le_normalizer_inf ⟨hAL hdA, Subgroup.le_normalizer hda⟩)
  have hbI : b ∈ Subgroup.normalizer (sec8I L a : Set G) := by
    rw [hIdef]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ (Subgroup.inf_normalizer_le_normalizer_inf ⟨hbN, Subgroup.le_normalizer hba⟩)
  have hcd : sec8I L a ⊓ Subgroup.centralizer ({d} : Set G) =
      sec8I L a ⊓ Subgroup.centralizer ({b} : Set G) :=
    inf_centralizer_eq_of_mem_closure hAel h.mem_A hbA hdcl h.ne_one hdc (hIL.trans hLc)
  exact classOne_transfer h47 haN ha3 haout hbN hb3 (hAc a h.a_mem b hbA) hL1 hG2L hKL2 hY1 hcN
    hc3 hcout hG2 hIdef hIY hM1 hdN hd3 (hAc c h.mem_A d hdA) hin hne hdI hbI hcd

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
