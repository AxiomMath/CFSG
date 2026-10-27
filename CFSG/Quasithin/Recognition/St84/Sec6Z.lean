module

public import CFSG.Quasithin.Recognition.St84.Sec6MQ
public import CFSG.Quasithin.Recognition.St84.Sec6QQuot

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

private theorem Lst_mono {U U' : Subgroup G} (h : X.normGi U 0 ≤ X.normGi U' 0) :
    X.Lst U 0 ≤ X.Lst U' 0 :=
  oTwoPrime_mono h

private theorem Yst_mono {U U' : Subgroup G} (h : X.normGi U 0 ≤ X.normGi U' 0) :
    X.Yst U 0 ≤ X.Yst U' 0 := by
  unfold Setup.Yst
  exact CFSG.GroupTheory.pResidualOf_mono (Lst_mono X h)

private theorem E_mono {U U' : Subgroup G} (h : X.normGi U 0 ≤ X.normGi U' 0) :
    X.E U 0 ≤ X.E U' 0 := by
  intro x hx
  exact ⟨hx.1, (h ⟨hx.2, X.Q_le_Gi 0 hx.1⟩).1⟩

theorem le_Z_of_le_centerOf_sylow (i : ℤ) {S Z : Subgroup G}
    (hS : IsSylowTwoOf S (X.Gi i)) (hZ : Z ≤ centerOf S) (hZQ : Z ≤ X.Q i) : Z ≤ X.Z i := by
  unfold Setup.Z
  exact le_iSup₂_of_le S hS (le_inf hZ hZQ)

private theorem isSK_of_le_QT {R : Subgroup G} (hSK : X.IsSK X.QT) (hR : R ≠ ⊥)
    (hRQT : R ≤ X.QT) (hK : X.K ≤ Subgroup.normalizer (R : Set G))
    (hnorm : X.normGi X.QT 0 ≤ X.normGi R 0) {t : G} (htQ : t ∈ X.normGi X.QT 1)
    (htR : t ∈ X.normGi R 1) (ht02 : t • X.vert 0 = X.vert 2) : X.IsSK R := by
  refine ⟨hR, ?_, hK, ?_, ?_, ⟨t, htR.1, ht02⟩⟩
  ·
    refine X.le_arcStab_of_fixSet ?_
    intro i hi
    exact fun r hr => X.QT_fixes_vert i (hRQT hr)
  ·
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := hSK.trans0 a b ha hb
    exact ⟨g, hnorm hg, hgab⟩
  ·
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := hSK.trans2 a b ha hb
    have hconj : X.normGi R 2 = conjSub t (X.normGi R 0) :=
      (Setup.IsSK.conjSub_normGi_zero X htR ht02).symm
    have hle : X.normGi X.QT 2 ≤ X.normGi R 2 := by
      rw [hconj, ← Setup.IsSK.conjSub_normGi_zero X htQ ht02]
      exact conjSub_mono t hnorm
    exact ⟨g, hle hg, hgab⟩

private theorem QT_inf_Z_one (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.QT ⊓ X.Z 1 = ⊥ := by
  by_contra hbot
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  set R : Subgroup G := X.QT ⊓ X.Z 1 with hRdef
  have hRZ : R ≤ X.Z 1 := by rw [hRdef]; exact inf_le_right
  have hRQT : R ≤ X.QT := by rw [hRdef]; exact inf_le_left
  obtain ⟨t, htM1, ht02, -, -⟩ := Setup.IsSK.exists_t X hSK
  have hK_le : X.K ≤ Subgroup.normalizer (R : Set G) :=
    fun k hk => CFSG.Quasithin.F7.mem_normalizer_inf (X.K_le_normalizer_QT hk)
      (mem_normalizer_iff_conjSub.mpr (X.Z_normal 1 k (X.K_le_Gi 1 hk)))
  have hLst_le : X.Lst X.QT 0 ≤ Subgroup.normalizer (R : Set G) := by
    have hcomm := X.commutator_QT_Lst_eq_bot hGT hs hodd h5 hX
    have hcent : X.Lst X.QT 0 ≤ Subgroup.centralizer (X.QT : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
        rw [Subgroup.commutator_comm]; exact hcomm)
    exact hcent.trans ((Subgroup.centralizer_le hRQT).trans
      (Subgroup.centralizer_le_normalizer _))
  have hM0_le : X.normGi X.QT 0 ≤ Subgroup.normalizer (R : Set G) := by
    have hM0 : X.normGi X.QT 0 = X.Lst X.QT 0 ⊔ X.K :=
      X.normGi_eq_Lst_sup_K hSK (Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX))
    rw [hM0]
    exact sup_le hLst_le hK_le
  have hnorm : X.normGi X.QT 0 ≤ X.normGi R 0 := by
    intro x hx
    exact ⟨hM0_le hx, X.normGi_le_Gi X.QT 0 hx⟩
  have htR1 : t ∈ X.normGi R 1 :=
    ⟨CFSG.Quasithin.F7.mem_normalizer_inf (X.normGi_le_normalizer X.QT 1 htM1.1)
      (mem_normalizer_iff_conjSub.mpr (X.Z_normal 1 t (X.normGi_le_Gi X.QT 1 htM1.1))),
      X.normGi_le_Gi X.QT 1 htM1.1⟩
  have hSKR : X.IsSK R := isSK_of_le_QT X hSK hbot hRQT hK_le hnorm htM1.1 htR1 ht02
  obtain ⟨R', hR'max, hR'le⟩ := X.exists_isSKMax_above hSKR
  have hQ1_le : X.Q 1 ≤ X.normGi R 0 := fun x hx =>
    ⟨Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (Subgroup.mem_centralizer_iff.mp (((X.Z_le_center 1) (hRZ hr)).2) x hx).symm),
      (X.Q_le_Gi_adj 1 hx).1⟩
  have hskP : X.skP R' = X.Q 1 := by
    refine le_antisymm inf_le_left ?_
    exact le_inf le_rfl (hQ1_le.trans hR'le)
  have hne : ⁅X.E R' 0, X.Yst R' 0⁆ ≠ ⊥ := by
    intro hb
    obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
    have h := X.commutator_E_Yst_ne_bot hGT hs hodd h5 hX hreg
    apply h
    refine le_antisymm ?_ bot_le
    calc ⁅X.E X.QT 0, X.Yst X.QT 0⁆
        ≤ ⁅X.E R 0, X.Yst R 0⁆ :=
          Subgroup.commutator_mono (E_mono X hnorm) (Yst_mono X hnorm)
      _ ≤ ⁅X.E R' 0, X.Yst R' 0⁆ :=
          Subgroup.commutator_mono (E_mono X hR'le) (Yst_mono X hR'le)
      _ = ⊥ := hb
  have hP' : X.skP R' ≠ ⊥ ∨ 2 ≤ X.n 0 :=
    Or.inl (by rw [hskP]; exact ne_bot_of_le_ne_bot (X.QT_ne_bot hGT) (X.QT_le_Q 1))
  exact (X.skP_ne_Q_one hR'max hP' hne) hskP

private theorem QT_inf_Z_zero (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.QT ⊓ X.Z 0 = ⊥ := by
  by_contra hbot
  have hSK : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ 2 ≤ X.n 0 :=
    Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)
  set R : Subgroup G := X.QT ⊓ X.Z 0 with hRdef
  have hRZ : R ≤ X.Z 0 := by rw [hRdef]; exact inf_le_right
  have hRQT : R ≤ X.QT := by rw [hRdef]; exact inf_le_left
  have hL0 : X.L 0 = X.Lst X.QT 0 ⊔ X.Q 0 :=
    X.L_eq_Lst_sup_Q hSK hP
  have hcent : R ≤ Subgroup.centralizer (X.L 0 : Set G) := by
    rw [hL0]
    refine CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers ?_ ?_
    · have hcomm := X.commutator_QT_Lst_eq_bot hGT hs hodd h5 hX
      have hLst : X.Lst X.QT 0 ≤ Subgroup.centralizer (X.QT : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
          rw [Subgroup.commutator_comm]; exact hcomm)
      intro r hr
      exact Subgroup.le_centralizer_iff.mp hLst (hRQT hr)
    · intro r hr
      exact ((X.Z_le_center 0) (hRZ hr)).2
  have hRcL : R ≤ centerOf (X.L 0) :=
    le_inf ((hRQT.trans (X.QT_le_Q 0)).trans
      (CFSG.Quasithin.le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0))
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi 0)))) hcent
  have hRS : R ≤ X.S := (hRQT.trans (X.QT_le_Q 0)).trans (by
    rw [← X.edgeSylow_zero]; exact X.Q_le_edgeSylow_left 0)
  have hRcS : R ≤ centerOf X.S :=
    le_inf hRS (hcent.trans (Subgroup.centralizer_le (by
      rw [← X.edgeSylow_zero]; exact X.edgeSylow_le_L 0)))
  have hSylS : IsSylowTwoOf X.S (X.Gi 1) := by
    have h := isSylowTwoOf_of_edgeStab X.hyp (X.adj 0).symm
      (show IsSylowTwoOf X.S (X.Gi 1 ⊓ X.Gi 0) from by
        simpa [X.edgeSylow_zero, inf_comm] using X.isSylowTwoOf_edgeSylow 0)
    simpa using h
  have hRZ1 : R ≤ X.Z 1 :=
    le_Z_of_le_centerOf_sylow X 1 hSylS hRcS (hRQT.trans (X.QT_le_Q 1))
  have hzero : R = ⊥ := le_bot_iff.mp (by
    have h1 : R ≤ X.QT ⊓ X.Z 1 := le_inf hRQT hRZ1
    simpa [QT_inf_Z_one X hGT hs hodd h5 hX] using h1)
  exact hbot hzero

theorem QT_inf_Z_eq_bot (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (i : ℤ) :
    X.QT ⊓ X.Z i = ⊥ := by
  have hQT : ∀ m : ℤ, conjSub (X.τ ^ m) (X.QT) = X.QT := fun m =>
    mem_normalizer_iff_conjSub.mp (zpow_mem X.tau_mem_normalizer_QT m)
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' i
  · have hZi : X.Z i = conjSub (X.τ ^ m) (X.Z 0) := by
      rw [hm, show 2 * m = 0 + 2 * m by ring, X.Z_add]
    rw [hZi, ← hQT m, ← conjSub_inf, QT_inf_Z_zero X hGT hs hodd h5 hX]
    exact conjSub_bot (X.τ ^ m)
  · have hZi : X.Z i = conjSub (X.τ ^ m) (X.Z 1) := by
      rw [hm, show 2 * m + 1 = 1 + 2 * m by ring, X.Z_add]
    rw [hZi, ← hQT m, ← conjSub_inf, QT_inf_Z_one X hGT hs hodd h5 hX]
    exact conjSub_bot (X.τ ^ m)

theorem not_Z_le_GT (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (i : ℤ) :
    ¬ X.Z i ≤ X.GT := by
  intro hle
  have h2 : X.GT ⊓ X.Q i ≤ X.QT := by
    have hGTnorm : X.GT ≤
        Subgroup.normalizer ((X.GT ⊓ X.Q i : Subgroup G) : Set G) := by
      intro g hg
      refine mem_normalizer_iff_conjSub.mpr ?_
      rw [conjSub_inf, conjSub_eq_of_mem (H := X.GT) hg]
      rw [show conjSub g (X.Q i) = X.Q i from mem_normalizer_iff_conjSub.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi i)
          (X.GT_le_Gi i hg))]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hGTnorm
      ((pCoreOf_isPGroup' (X.Gi i)).to_le inf_le_right)
  have hZQ : X.Z i ≤ X.GT ⊓ X.Q i := le_inf hle (X.Z_le_Q i)
  have hbot : X.Z i = ⊥ := le_bot_iff.mp (by
    calc X.Z i ≤ X.QT ⊓ X.Z i := le_inf (hZQ.trans h2) le_rfl
      _ = ⊥ := QT_inf_Z_eq_bot X hGT hs hodd h5 hX i)
  exact X.Z_ne_bot_of i (X.Q_ne_bot hc i) hbot

theorem sq_mem_Q_neg_one_inf_Q_one {x : G} (hx : x ∈ X.Q 0) : x ^ 2 ∈ X.Q (-1) ⊓ X.Q 1 :=
  ⟨sq_mem_Q_of_relIndex X (S := X.edgeSylow (-1)) (j := -1)
      (X.isSylowTwoOf_edgeSylow_L (-1)).1 (X.relIndex_Q_edgeSylow (-1)) x
      ((by simpa using X.Q_le_edgeSylow (-1) : X.Q 0 ≤ X.edgeSylow (-1)) hx),
    sq_mem_Q_of_relIndex X (S := X.edgeSylow 0) (j := 1)
      (X.isSylowTwoOf_edgeSylow_L_succ 0).1 (X.relIndex_Q_succ_edgeSylow 0) x
      (X.Q_le_edgeSylow_left 0 hx)⟩

end Setup

end CFSG.Quasithin.St84
