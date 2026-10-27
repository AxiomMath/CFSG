module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNExcKacDatum
public import CFSG.LocalAnalysis.StandardType.GGTPNExcTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGE6TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGE6TwoLocalRank
public import CFSG.LocalAnalysis.StandardType.GGE6CoverThreeHolds
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Rank
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Core

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem e63_iso_tagA {labJ l : LargeEvenLabel} (hJ : labJ.tag = .A)
    (hr : 2 ≤ labJ.rank) (h : GGLabelIso labJ l) :
    (l.tag = .A ∧ labJ = l) ∨ (l.tag = .D ∧ l.rank = 3) := by
  unfold GGLabelIso at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · refine Or.inl ⟨?_, h1⟩
    rw [← h1]; exact hJ
  · rcases h2.1 with hB | hC
    · exact absurd (hB.symm.trans hJ) (by intro hh; cases hh)
    · exact absurd (hC.symm.trans hJ) (by intro hh; cases hh)
  · exact absurd (hJ.symm.trans (congrArg LargeEvenLabel.tag h3.1)) (by intro hh; cases hh)
  · obtain ⟨-, rfl⟩ := h4
    exact Or.inr ⟨rfl, rfl⟩
  · exact absurd (hJ.symm.trans (congrArg LargeEvenLabel.tag h5.1)) (by intro hh; cases hh)
  · exact absurd (hJ.symm.trans (congrArg LargeEvenLabel.tag h6.1)) (by intro hh; cases hh)
  · exact absurd (hJ.symm.trans (congrArg LargeEvenLabel.tag h7.1)) (by intro hh; cases hh)
  · have : labJ.rank = 1 := congrArg LargeEvenLabel.rank h8.2
    omega

private theorem e63_aut_A2 {J : Type} [Group J] [Finite J] (hperf : commutator J = ⊤)
    {m : ℕ} (h3 : 3 ∣ 2 ^ m - 1)
    (hlab : GGHasLabel ⟨.A, 2, m⟩ (J ⧸ Subgroup.center J)) :
    ∀ E : Subgroup (MulAut J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 := by
  intro E hE
  unfold GGHasLabel at hlab
  dsimp only [LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeLinear at hlab
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hlab
  have hb := gffa2_rank_linear (K := K) (n := m) hKcard
    (E.map (ggInducedAut e)) (CFSG.Open.IsElemAbelian.map hE (ggInducedAut e))
  have hinj : Function.Injective (ggInducedAut e) :=
    ggInducedAut_injective_of_perfect hperf e
  have hcard : Nat.card (E.map (ggInducedAut e)) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  rwa [hcard] at hb

private theorem e63_A23_contra
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    {n N : ℕ} (hd : GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J)
    (hΛX : LargeEvenInLambda2 (⟨.E6, 0, N⟩ : LargeEvenLabel))
    (hhJ : GGHasLabel ⟨.A, 2, 3 * N⟩ (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel ⟨.E6, 0, N⟩ (X ⧸ Subgroup.center X))
    (h3 : 3 ∣ 2 ^ N - 1) : False := by
  obtain ⟨hlocCore, hflat, -, hrank, -, -, -, hmarked⟩ := hd.1
  obtain ⟨hAbA, hσAb, -, hkerAb⟩ := hflat
  have hnormA : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := hlocCore.2.2.2.2
  have hperfJ : commutator ↥J = ⊤ := hlocCore.2.2.2.1.2.2.1
  have hAbab : IsElemAbelian 3 Ab := by
    obtain ⟨hc, hp⟩ := hlocCore.1
    haveI : IsMulCommutative A := hc
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative A (hAbA u.2) (hAbA v.2)
    · exact hp z (hAbA hz)
  have hnorm : ∀ a ∈ Ab, ∀ j ∈ J, a j ∈ J := fun a ha j hj => hnormA a (hAbA ha) j hj
  have h3' : 3 ∣ 2 ^ (3 * N) - 1 := by
    have h : 3 ∣ (2 ^ N) ^ 3 - 1 := h3.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ N) 3)
    have he : (2 ^ N) ^ 3 - 1 = 2 ^ (3 * N) - 1 := by rw [mul_comm 3, pow_mul]
    rwa [he] at h
  have hAut : ∀ E : Subgroup (MulAut ↥J), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 :=
    e63_aut_A2 hperfJ h3' hhJ
  have hbound : Nat.card Ab ≤ 3 ^ 4 := by
    have h := B36.card_le_of_kernel_le_zpowers (p := 3) (by norm_num) hAbab hσAb hnorm hkerAb
      (k := 3) hAut
    simpa using h
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm4 : m ≤ 4 := by
    have h : 3 ^ m ≤ 3 ^ 4 := by rw [← hmcard]; exact hbound
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have hperfX : commutator X = ⊤ := hmarked.1
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center X)
  · have h6 := ggE6CoverThreeLocalRank_holds X ⟨.E6, 0, N⟩ hΛX rfl h3 hhX hperfX hZ
    rw [if_pos hZ] at hmrank
    omega
  · have h5 := ggE6TorusLiftFiveRank (X := X) hperfX rfl h3 hhX
    rw [if_neg hZ] at hmrank
    omega

theorem ggTypeAE6Three_holds
    (hBS : GGK0ExcBS) : GGTypeAE6ThreeRK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hJA, hJ2, hJn, hpJ⟩, htagX, hp3, hpair⟩ := hr
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨D, hDval, ha, hb, hc, he⟩ := ggTPNExcKac_datum hBS hd hΛX hpair hhX
  obtain ⟨hlocCore, -, -, -, -, -, honly, -⟩ := hd.1
  have hfix : ggFixSub σ = ggAutFixedSubgroup σ := by
    ext x; simp [ggFixSub, ggAutFixedSubgroup]
  have hJfix : IsComponentOf J (ggFixSub σ) := by
    rw [hfix]
    exact hlocCore.2.2.2.1
  obtain ⟨o, ho, hqs, hdvd, hΛo, hlabo⟩ := ha J hJfix
  obtain ⟨f, hf⟩ := he
  have hEqJ : ∀ J' (hJ' : IsComponentOf J' (ggFixSub σ)), J' = J :=
    fun J' hJ' => eq_of_isComponentOf_of_ggTPNOnlyComp honly (hfix ▸ hJ') (hc J' hJ')
  haveI : Subsingleton {J' : Subgroup X // IsComponentOf J' (ggFixSub σ)} :=
    ⟨fun a b => Subtype.ext (by rw [hEqJ a.1 a.2, hEqJ b.1 b.2])⟩
  have hpos : ∀ i j : Fin D.orbits.length, D.orbits[i].qs = true →
      D.orbits[j].qs = true → i = j := by
    intro i j hi hj
    have hsub' : Subsingleton {k : Fin D.orbits.length // D.orbits[k].qs = true} := by
      constructor
      intro a b
      have h1 : f.symm a = f.symm b := Subsingleton.elim _ _
      have h2 := congrArg f h1
      simpa using h2
    have hthis : (⟨i, hi⟩ : {k : Fin D.orbits.length // D.orbits[k].qs = true}) =
        ⟨j, hj⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val hthis
  obtain ⟨T, tw, hty, hDmem⟩ := hDval
  have htype := ltqE6c_typeOfLabel_eq hΛX htagX
  rw [htype] at hty
  simp only [Option.some.injEq, Prod.mk.injEq] at hty
  obtain ⟨hT, htwb⟩ := hty
  subst hT
  have htw : ggKacTypeOfLabel labX = some (.E6, tw) := by rw [htype, htwb]
  have hclass : GGB36JLabel labX o.lab ∨ o.lab = labX :=
    ltqE6c_classify hΛX htagX htw hDmem ho hqs hpos hdvd
  have hiso : GGLabelIso labJ o.lab :=
    ggLabelRigidInput_holds labJ o.lab (↥J ⧸ Subgroup.center ↥J) hΛJ hΛo hhJ hlabo
  have hcontra : ∀ l : LargeEvenLabel, o.lab = l → l.tag ≠ .A → (l.tag ≠ .D ∨ l.rank ≠ 3) →
      False := by
    intro l hl hA hD
    have hh := e63_iso_tagA hJA hJ2 hiso
    rw [hl] at hh
    rcases hh with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hA h1
    · rcases hD with hD | hD
      · exact hD h1
      · exact hD h2
  rcases hclass with hGLo | heqo
  · unfold GGB36JLabel at hGLo
    rcases hGLo with ⟨hE6t, hres, hJ⟩ | ⟨hE6t, hres, hJ⟩ | ⟨hTwt, hres, hJ⟩ | ⟨hTwt, hres, hJ⟩
    ·
      have hlabXE6 : labX = ⟨.E6, 0, labX.n⟩ := by
        rw [ltqE6c_label_eq hΛX (Or.inl hE6t), hE6t]
      rcases hJ with hJ | hJ | hJ | hJ | hJ
      · exact (hcontra _ hJ (by simp) (Or.inr (by norm_num))).elim
      ·
        have hlabJ : labJ = ⟨.A, 5, labX.n⟩ := by
          have hh := e63_iso_tagA hJA hJ2 hiso
          rw [hJ] at hh
          rcases hh with ⟨-, h1⟩ | ⟨h1, -⟩
          · exact h1
          · exact absurd h1 (by simp)
        refine ⟨labJ, labX, hΛJ, hΛX, ?_, hhJ, hhX⟩
        rw [hlabJ, hlabXE6]
        exact ltqE6c_row_A5_E6 hres
      · exact (hcontra _ hJ (by simp) (Or.inr (by norm_num))).elim
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
      ·
        exact (e63_A23_contra hd (hlabXE6 ▸ hΛX) (by
          have hlabJ : labJ = ⟨.A, 2, 3 * labX.n⟩ := by
            have hh := e63_iso_tagA hJA hJ2 hiso
            rw [hJ] at hh
            rcases hh with ⟨-, h1⟩ | ⟨h1, -⟩
            · exact h1
            · exact absurd h1 (by simp)
          rwa [hlabJ] at hhJ) (hlabXE6 ▸ hhX) hres).elim
    ·
      have hlabXE6 : labX = ⟨.E6, 0, labX.n⟩ := by
        rw [ltqE6c_label_eq hΛX (Or.inl hE6t), hE6t]
      rcases hJ with hJ | hJ | ⟨hn1, hJ⟩
      ·
        have hlabJ : labJ = ⟨.A, 5, labX.n⟩ := by
          have hh := e63_iso_tagA hJA hJ2 hiso
          rw [hJ] at hh
          rcases hh with ⟨-, h1⟩ | ⟨h1, -⟩
          · exact h1
          · exact absurd h1 (by simp)
        refine ⟨labJ, labX, hΛJ, hΛX, ?_, hhJ, hhX⟩
        rw [hlabJ, hlabXE6]
        exact ltqE6c_row_A5_E6_qp1 hres
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
      ·
        have hlabJ : labJ = ⟨.A, 2, 2⟩ := by
          have hh := e63_iso_tagA hJA hJ2 hiso
          rw [hJ] at hh
          rcases hh with ⟨-, h1⟩ | ⟨h1, -⟩
          · exact h1
          · exact absurd h1 (by simp)
        exact (ltqSl_T4 ggE6TwoCenterBot_holds ggE6TwoLocalRankThree_holds hd
          (by rw [hlabXE6, hn1] at hhX; exact hhX) (by rwa [hlabJ] at hhJ)).elim
    ·
      rcases hJ with hJ | hJ
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
    ·
      rcases hJ with hJ | hJ | hJ | hJ | hJ | ⟨hn1, hJ⟩
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
      · exact (hcontra _ hJ (by simp) (Or.inr (by norm_num))).elim
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
      · exact (hcontra _ hJ (by simp) (Or.inl (by simp))).elim
  ·
    exfalso
    have hh := e63_iso_tagA hJA hJ2 (heqo ▸ hiso)
    rcases hh with ⟨h1, -⟩ | ⟨h1, h2⟩
    · rcases htagX with h | h <;> rw [h] at h1 <;> simp at h1
    · rcases htagX with h | h <;> rw [h] at h1 <;> simp at h1

end CFSG.StandardType

end
