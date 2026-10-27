module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABEA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_of_C_TZ_eq_normalizer
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (T : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    {C : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))}
    (hcase : T ⊓ C =
      T ⊓ Subgroup.normalizer
        ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _)) :
    ∃ E : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      E ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ IsPGroup 7 E ∧ ¬ IsCyclic ↥E ∧
      E ≤ Subgroup.normalizer ((T ⊓ C : Subgroup _) : Set _) := by
  classical
  let hV := h.hyp151.isElemAbelian
  let Vt := Vtil ⊥ V hV
  let Mb : Subgroup (MulAut Vt) := Mbar D.M ⊥ V hV
  let Lb : Subgroup (MulAut Vt) := lBar ⊥ V hV L
  let B : Subgroup (MulAut Vt) := barSub ⊥ V hV (conjSubgroup L x)
  let Zt : Subgroup Vt := commSub ⊤ Lb ⊓ fixV Lb
  obtain ⟨TA, TB, _, _, hTA_syl, hTB_syl, hshape⟩ :=
    s16h_sl28_sylow_normalizer_shape D S h hs2 hW hrow hxM hxn T hT
  have hLbSL : IsSLn ↥Lb 2 3 := hrow.1
  have hBSL : IsSLn ↥B 2 3 := s16h_sl28_isSLn_conj D S h hrow hxM
  obtain ⟨-, -, b, hbLb, hbNormTA, hbord⟩ :=
    s16h_sl28_sylow_two_borel_seven hLbSL hTA_syl
  obtain ⟨-, -, b', hb'B, hb'NormTB, hb'ord⟩ :=
    s16h_sl28_sylow_two_borel_seven hBSL hTB_syl
  have hLbM : Lb ≤ Mb := barSub_mono ⊥ V hV h.hyp151.le
  have hBM : B ≤ Mb := c23_barSub_conjSubgroup_le_Mbar D h.hyp151 hV hxM
  have hcommPair := h.hyp151.commute x hxM hxn
  have hLbCentB : Lb ≤ Subgroup.centralizer ((B : Subgroup _) : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommPair.1
  have hBcentLb : B ≤ Subgroup.centralizer ((Lb : Subgroup _) : Set _) :=
    Subgroup.le_centralizer_iff.mp hLbCentB
  have hbCentTB : b ∈ Subgroup.centralizer ((TB : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    Subgroup.centralizer_le (by intro z hz; exact hTB_syl.le hz) (hLbCentB hbLb)
  have hleTB : Subgroup.centralizer ((TB : Subgroup (MulAut Vt)) : Set (MulAut Vt)) ≤
      Subgroup.normalizer ((TB : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    Subgroup.centralizer_le_normalizer _
  have hbNormTB : b ∈ Subgroup.normalizer ((TB : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    hleTB hbCentTB
  have hbNormSup : b ∈ Subgroup.normalizer ((TA ⊔ TB : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    s16h_normalizer_inf_le_normalizer_join (A := TA) (B := TB)
      (Subgroup.mem_inf.mpr ⟨hbNormTA, hbNormTB⟩)
  have hb'CentTA : b' ∈ Subgroup.centralizer ((TA : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    Subgroup.centralizer_le (by intro z hz; exact hTA_syl.le hz) (hBcentLb hb'B)
  have hleTA : Subgroup.centralizer ((TA : Subgroup (MulAut Vt)) : Set (MulAut Vt)) ≤
      Subgroup.normalizer ((TA : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    Subgroup.centralizer_le_normalizer _
  have hb'NormTA : b' ∈ Subgroup.normalizer ((TA : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    hleTA hb'CentTA
  have hb'NormSup : b' ∈ Subgroup.normalizer ((TA ⊔ TB : Subgroup (MulAut Vt)) : Set (MulAut Vt)) :=
    s16h_normalizer_inf_le_normalizer_join (A := TA) (B := TB)
      (Subgroup.mem_inf.mpr ⟨hb'NormTA, hb'NormTB⟩)
  have hbcomm : Commute b b' :=
    ((Subgroup.mem_centralizer_iff.mp (hLbCentB hbLb)) b' hb'B).symm
  have hLbBbot : Lb ⊓ B = ⊥ := by
    apply le_bot_iff.mp
    intro w hw
    rw [Subgroup.mem_bot]
    have hwcent : (⟨w, hw.1⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext_iff.mpr (((Subgroup.mem_centralizer_iff.mp (hLbCentB y.2)) w hw.2).symm)
    rw [s16h_sl28_center_eq_bot_of_isSLn_two (X := ↥Lb) (by norm_num) hLbSL] at hwcent
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hwcent)
  have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers b' = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    rw [Subgroup.mem_bot]
    have hzLb : z ∈ Lb := Subgroup.zpowers_le.mpr hbLb hz.1
    have hzB : z ∈ B := Subgroup.zpowers_le.mpr hb'B hz.2
    exact Subgroup.mem_bot.mp (hLbBbot ▸ Subgroup.mem_inf.mpr ⟨hzLb, hzB⟩)
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers b', x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hbcomm.zpow_zpow i j).eq
  have hb7 : b ^ 7 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
  have hb'7 : b' ^ 7 = 1 := by rw [← hb'ord]; exact pow_orderOf_eq_one b'
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hbord
    exact absurd hbord (by norm_num)
  have hb'1 : b' ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb'ord
    exact absurd hb'ord (by norm_num)
  have hE := s16h_zpowers_sup_noncyclic_of_prime (X := MulAut Vt) (p := 7)
    Nat.prime_seven hb7 hb'7 hb1 hb'1 hcomm hdisj
  let E : Subgroup (MulAut Vt) := Subgroup.zpowers b ⊔ Subgroup.zpowers b'
  have hEMb : E ≤ Mb := by
    show Subgroup.zpowers b ⊔ Subgroup.zpowers b' ≤ Mb
    exact sup_le (Subgroup.zpowers_le.mpr (hLbM hbLb))
      (Subgroup.zpowers_le.mpr (hBM hb'B))
  have hE7 : IsPGroup 7 E := hE.1
  have hEncyc : ¬ IsCyclic ↥E := hE.2
  have hEnorm : E ≤ Subgroup.normalizer ((T ⊓ C : Subgroup (MulAut Vt)) : Set _) := by
    have hS : T ⊓ C = TA ⊔ TB := hcase.trans hshape
    have hsup : E ≤ Subgroup.normalizer ((TA ⊔ TB : Subgroup (MulAut Vt)) : Set _) := by
      show Subgroup.zpowers b ⊔ Subgroup.zpowers b' ≤ _
      exact sup_le (Subgroup.zpowers_le.mpr hbNormSup)
        (Subgroup.zpowers_le.mpr hb'NormSup)
    rw [hS]
    exact hsup
  exact ⟨E, hEMb, hE7, hEncyc, hEnorm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
