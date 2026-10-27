module

public import CFSG.Quasithin.Recognition.St84.Sec67B
public import CFSG.Quasithin.Recognition.St84.Sec67C
import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

private theorem Z_zero_le_Etau_of_fixes {k : ℤ}
    (hfix1 : X.Z 0 ≤ X.Gi (2 * k + 1)) (hfixm : X.Z 0 ≤ X.Gi (2 * k - 1)) :
    X.Z 0 ≤ X.Etau k := by
  have hQ : X.Z 0 ≤ X.Q (2 * k) := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · exact X.Z_le_Q_of_le_Gi 0 (2 * k - 1) (2 * k) hfixm
        (Or.inr ⟨by omega, by omega⟩)
    · exact X.Z_le_Q_of_le_Gi 0 (2 * k + 1) (2 * k) hfix1 (Or.inl (by omega))
    · exact X.Z_le_Q_of_le_Gi 0 (2 * k + 1) (2 * k) hfix1
        (Or.inr ⟨by omega, by omega⟩)
  rw [X.Etau_eq]
  exact le_inf hQ (X.Z_le_normalizer_QT 0)

private theorem Etau_neg_two_meet {m : ℕ} (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hm : m = 4) :
    X.Etau (-2) ⊓ X.Etau (-1) ⊓ X.E X.QT 0 ⊓ X.Etau 1 = X.QT := by
  have h := X.E_minus_inf_E_inf_E_two_inf_E_four hGT hs hodd h5 hX hreg hm
  have hc := congrArg (conjSub X.τ⁻¹) h
  rw [conjSub_inf, conjSub_inf, conjSub_inf, ← X.Etau_zero,
    conjSub_inv_tau_Etau, conjSub_inv_tau_Etau, conjSub_inv_tau_Etau,
    conjSub_inv_tau_Etau] at hc
  have htau : conjSub X.τ X.QT = X.QT := X.conjSub_tau_QT
  have hQT : conjSub X.τ⁻¹ X.QT = X.QT := by
    conv_lhs => rw [← htau]
    rw [conjSub_conjSub_inv]
  rw [hQT] at hc
  simpa using hc

private theorem Etau_le_Gi (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    {j : ℤ} :
    X.Etau j ≤ X.Gi (2 * j + 2) ⊓ X.Gi (2 * j - 2) := by
  have h := X.E_QT_le_Gi_two hGT hs hodd h5 hX
  change conjSub (X.τ ^ j) (X.E X.QT 0) ≤ _
  have h2 := conjSub_mono (X.τ ^ j) h
  rw [conjSub_inf, ← X.Gi_add j 2, ← X.Gi_add j (-2)] at h2
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h2

theorem Z_zero_fixes_three (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.Z 0 ≤ X.Gi 3 := by
  by_contra hb
  by_cases h0 : 2 ≤ X.n 0
  · exact X.false_of_two_le_n_zero hb hc hGT hs hodd h5 hX h0
  · have hval : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    have hn0 : X.n 0 = 1 := by omega
    have h1 : 2 ≤ X.n 1 := by
      rcases hmax with h | h
      · exact absurd h h0
      · exact h
    exact X.false_of_n_zero_eq_one hb hc hGT hs hodd h5 hX hn0 h1

theorem Z_zero_le_ZM (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.Z 0 ≤ X.ZM := by
  by_contra hZ
  exact (X.not_Z_le_Gi_three_of_not_le_ZM hZ hc hGT hs hodd h5 hX)
    (X.Z_zero_fixes_three hc hmax hs hodd h5 hX hGT)

theorem m_eq_four {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : m = 4 := by
  have h3 : 3 ≤ m := X.three_le_m hGT hs hodd h5 hX hreg
  have h4 : m ≤ 4 := X.m_le_four hGT hs hodd h5 hX hreg
  rcases Nat.eq_or_lt_of_le h3 with h | h
  · have hZM : X.ZM = X.QT :=
      X.centerOf_eq_QT_of_m_eq_three hGT hs hodd h5 hX hreg h.symm
    have hZle : X.Z 0 ≤ X.QT := by
      have hZ0 := X.Z_zero_le_ZM hc hmax hs hodd h5 hX hGT
      rwa [hZM] at hZ0
    have hbot : X.Z 0 = ⊥ := by
      have hinf := X.QT_inf_Z_eq_bot hGT hs hodd h5 hX 0
      rw [eq_bot_iff]
      intro z hz
      have hz' : z ∈ X.QT ⊓ X.Z 0 := Subgroup.mem_inf.mpr ⟨hZle hz, hz⟩
      rw [hinf] at hz'
      simpa using hz'
    exact absurd hbot (X.Z_ne_bot_of 0 (X.Q_ne_bot hc 0))
  · omega

private theorem isSylowTwoOf_S_Gi_zero : IsSylowTwoOf X.S (X.Gi 0) := by
  simpa [X.edgeSylow_zero] using
    isSylowTwoOf_of_edgeStab X.hyp (X.adj 0) (X.isSylowTwoOf_edgeSylow 0)

theorem Z_zero_eq_centerOf_L_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.Z 0 = centerOf (X.L 0) := by
  have hQL : X.Q 0 ≤ X.L 0 := le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0))
    (X.Q_le_Gi 0)
  have hU : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ X.n 0 = 2 :=
    Or.inl (X.not_skP_QT_le_Q_zero hGT hs hodd h5 hX)
  refine le_antisymm ?_ ?_
  · have hZM := X.Z_zero_le_ZM hc hmax hs hodd h5 hX hGT
    have hzL : X.Z 0 ≤ X.L 0 := (X.Z_le_Q 0).trans hQL
    have hcent : X.Z 0 ≤ Subgroup.centralizer (X.L 0 : Set G) := by
      rw [X.L_eq_Lst_sup_Q hU (hP.imp_right Eq.ge), Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hZM hz)).2 y hy).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp
          (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2 y hy).symm
    exact le_inf hzL hcent
  · intro z hz
    obtain ⟨hzL, hzc⟩ := Subgroup.mem_inf.mp hz
    have hzQ : z ∈ X.Q 0 :=
      (hc (X.vert 0)) ⟨X.L_le_Gi 0 hzL, (Subgroup.centralizer_le hQL) hzc⟩
    have hSylS : IsSylowTwoOf X.S (X.Gi 0) := X.isSylowTwoOf_S_Gi_zero
    have hzS : z ∈ X.S := by
      rw [← X.edgeSylow_zero]
      exact X.Q_le_edgeSylow_left 0 hzQ
    have hzcent : z ∈ centerOf X.S := by
      refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hsS
      have hsL : s ∈ X.L 0 := by
        rw [← X.edgeSylow_zero] at hsS
        exact X.edgeSylow_le_L 0 hsS
      exact Subgroup.mem_centralizer_iff.mp hzc s hsL
    have hle : centerOf X.S ⊓ X.Q 0 ≤ X.Z 0 :=
      X.le_Z_of_le_centerOf_sylow 0 hSylS inf_le_left inf_le_right
    exact hle (Subgroup.mem_inf.mpr ⟨hzcent, hzQ⟩)

private theorem Z_zero_le_centerOf_S (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.Z 0 ≤ centerOf X.S := by
  refine le_inf ((X.Z_le_Q 0).trans (X.Q_le_edgeSylow_left 0)) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro s hsS
  have hSL : s ∈ X.L 0 := by
    rw [← X.edgeSylow_zero] at hsS
    exact X.edgeSylow_le_L 0 hsS
  have hcent : X.Z 0 ≤ Subgroup.centralizer (X.L 0 : Set G) := by
    rw [X.Z_zero_eq_centerOf_L_zero hc hmax hs hodd h5 hX hGT]
    exact inf_le_right
  exact Subgroup.mem_centralizer_iff.mp (hcent hz) s hSL

private theorem Z_two_eq_centerOf_L_two (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.Z 2 = centerOf (X.L 2) := by
  have h := X.Z_zero_eq_centerOf_L_zero hc hmax hs hodd h5 hX hGT
  have hc2 := congrArg (conjSub (X.τ ^ (1 : ℤ))) h
  simp only [centerOf, conjSub_inf, conjSub_centralizer] at hc2
  rw [show (2 : ℤ) = 0 + 2 * 1 by norm_num, X.Z_add 1 0, X.L_add 1 0]
  change conjSub (X.τ ^ 1) (X.Z 0) =
    conjSub (X.τ ^ 1) (X.L 0) ⊓ Subgroup.centralizer (conjSub (X.τ ^ 1) (X.L 0))
  rw [conjSub_centralizer]
  exact hc2

private theorem Z_two_le_centerOf_edgeSylow_one (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.Z 2 ≤ centerOf (X.edgeSylow 1) := by
  have hS12L : X.edgeSylow 1 ≤ X.L 2 := by
    simpa using (X.isSylowTwoOf_edgeSylow_L_succ 1).1
  have hZ2eqL := X.Z_two_eq_centerOf_L_two hc hmax hs hodd h5 hX hGT
  refine le_inf ((X.Z_le_Q 2).trans (X.Q_le_edgeSylow 1)) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro s hsS
  have hcent : X.Z 2 ≤ Subgroup.centralizer (X.L 2 : Set G) := by
    rw [hZ2eqL]
    exact inf_le_right
  exact Subgroup.mem_centralizer_iff.mp (hcent hz) s (hS12L hsS)

private theorem ZM_le_Gi_zero : X.ZM ≤ X.Gi 0 :=
  (inf_le_left : X.ZM ≤ X.Lst X.QT 0).trans
    ((oTwoPrime_le (X.normGi X.QT 0)).trans (X.normGi_le_Gi X.QT 0))

theorem card_Z_zero_le (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    Nat.card (X.Z 0) ≤ 2 ^ X.n 0 := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  haveI : Finite ↥X.GT := finite_of_le_stabilizer X.hyp (H := X.GT) (X.GT_le_Gi 0)
  haveI : Finite ↥X.QT :=
    Finite.of_injective (Subgroup.inclusion X.QT_le_GT) (Subgroup.inclusion_injective _)
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  haveI : Finite ↥X.ZM := finite_of_le_stabilizer X.hyp (H := X.ZM) X.ZM_le_Gi_zero
  have hm : m = 4 := X.m_eq_four hc hmax hs hodd h5 hX hGT hreg
  have hZM := X.Z_zero_le_ZM hc hmax hs hodd h5 hX hGT
  have hQTM := X.QT_le_centerOf_Lst hGT hs hodd h5 hX
  have hsup : X.Z 0 ⊔ X.QT ≤ X.ZM := sup_le hZM hQTM
  have hinf : Disjoint (X.Z 0) X.QT :=
    disjoint_iff.mpr (by rw [inf_comm]; exact X.QT_inf_Z_eq_bot hGT hs hodd h5 hX 0)
  have hcomm : X.QT ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    have hcent : X.QT ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hQTM hq)).2 z
        (Subgroup.mem_inf.mp (hZM hz)).1
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcard_sup : Nat.card ↥(X.Z 0 ⊔ X.QT) = Nat.card ↥(X.Z 0) * Nat.card ↥X.QT :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (X.Z 0) X.QT hcomm hinf
  have hZMcard : Nat.card ↥X.ZM = 2 ^ X.n 0 * Nat.card ↥X.QT := by
    rw [X.card_ZM hGT hs hodd h5 hX hreg, hm]
    norm_num
  have hle : Nat.card ↥(X.Z 0) * Nat.card ↥X.QT ≤ 2 ^ X.n 0 * Nat.card ↥X.QT := by
    rw [← hcard_sup, ← hZMcard]
    exact Subgroup.card_le_of_le hsup
  exact Nat.le_of_mul_le_mul_right hle Nat.card_pos

theorem Z_zero_le_Gi_four (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 0 ≤ X.Gi 4 ⊓ X.Gi (-4) := by
  have hm : m = 4 := X.m_eq_four hc hmax hs hodd h5 hX hGT hreg
  have hZM := X.Z_zero_le_ZM hc hmax hs hodd h5 hX hGT
  have hE2 : X.ZM ≤ X.Etau 1 := by
    have h : X.ZM ≤ X.E X.QT 0 ⊓ X.Etau 1 := by
      rw [X.E_inf_E_two hGT hs hodd h5 hX hreg hm]
      exact le_sup_left
    exact h.trans inf_le_right
  have hEm2 : X.ZM ≤ X.Etau (-1) := by
    have h : X.ZM ≤ X.Etau (-1) ⊓ X.E X.QT 0 ⊓ X.Etau 1 := by
      rw [X.E_minus_inf_E_inf_E_two hGT hs hodd h5 hX hreg hm]
    exact h.trans (inf_le_left.trans inf_le_left)
  refine le_inf ?_ ?_
  · exact hZM.trans (hE2.trans
      ((X.Etau_le_Gi hGT hs hodd h5 hX (j := 1)).trans inf_le_left))
  · exact hZM.trans (hEm2.trans
      ((X.Etau_le_Gi hGT hs hodd h5 hX (j := -1)).trans inf_le_right))

private theorem false_of_Z_zero_le_Gi_five {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {d : ℤ} (hd : d = 5 ∨ d = -5)
    (hfixd : X.Z 0 ≤ X.Gi d) : False := by
  have hm : m = 4 := X.m_eq_four hc hmax hs hodd h5 hX hGT hreg
  have hv : Γ.dist (X.vert 0) (X.vert d) = 5 := by
    rcases hd with rfl | rfl
    · have h := Line.dist_eq X.hyp.isTree X.line (i := (0 : ℤ)) (j := 5) (by norm_num)
      simpa using h
    · have h := Line.dist_eq X.hyp.isTree X.line (i := (-5 : ℤ)) (j := 0) (by norm_num)
      rw [SimpleGraph.dist_comm] at h
      simpa using h
  have hfixall : ∀ i : ℤ, -5 ≤ i → i ≤ 5 → X.Z 0 ≤ X.Gi i := by
    intro i hi1 hi2
    have hdist : Γ.dist (X.vert 0) (X.vert i) ≤ 5 := by
      by_cases h : 0 ≤ i
      · have hd0 := Line.dist_eq X.hyp.isTree X.line (i := (0 : ℤ)) (j := i) h
        rw [hd0]
        have h5' : i.toNat ≤ 5 := by
          have h2 : (i.toNat : ℤ) = i := Int.toNat_of_nonneg h
          omega
        simpa using h5'
      · have hneg : i < 0 := not_le.mp h
        have hd0 := Line.dist_eq X.hyp.isTree X.line (i := i) (j := (0 : ℤ)) (by omega)
        rw [SimpleGraph.dist_comm] at hd0
        rw [hd0]
        have h3 : (0 : ℤ) ≤ -i := by omega
        have h4 : ((-i).toNat : ℤ) = -i := Int.toNat_of_nonneg h3
        have h5' : (-i).toNat ≤ 5 := by omega
        simpa using h5'
    exact X.Z_fixes_of_dist 0 hs (by omega) hv hfixd (X.vert i) hdist
  have hE : ∀ k : ℤ, -2 ≤ k → k ≤ 2 → X.Z 0 ≤ X.Etau k := by
    intro k hk1 hk2
    refine X.Z_zero_le_Etau_of_fixes (k := k) ?_ ?_
    · exact hfixall (2 * k + 1) (by omega) (by omega)
    · exact hfixall (2 * k - 1) (by omega) (by omega)
  have hQTmem : X.Z 0 ≤ X.QT := by
    rcases hd with rfl | rfl
    · have hone := X.E_minus_inf_E_inf_E_two_inf_E_four hGT hs hodd h5 hX hreg hm
      rw [← hone]
      have h0 : X.Z 0 ≤ X.E X.QT 0 := by simpa using hE 0 (by omega) (by omega)
      exact le_inf (le_inf (le_inf (hE (-1) (by omega) (by omega)) h0)
        (hE 1 (by omega) (by omega))) (hE 2 (by omega) (by omega))
    · have hone := X.Etau_neg_two_meet hGT hs hodd h5 hX hreg hm
      rw [← hone]
      have h0 : X.Z 0 ≤ X.E X.QT 0 := by simpa using hE 0 (by omega) (by omega)
      exact le_inf (le_inf (le_inf (hE (-2) (by omega) (by omega)) (hE (-1) (by omega) (by omega)))
        h0) (hE 1 (by omega) (by omega))
  have hbot : X.Z 0 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ X.Z 0 ⊓ X.QT := Subgroup.mem_inf.mpr ⟨hz, hQTmem hz⟩
    rw [show X.Z 0 ⊓ X.QT = ⊥ by
      rw [inf_comm]; exact X.QT_inf_Z_eq_bot hGT hs hodd h5 hX 0] at hz'
    simpa using hz'
  exact absurd hbot (X.Z_ne_bot_of 0 (X.Q_ne_bot hc 0))

theorem not_Z_zero_le_Gi_five (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ¬ X.Z 0 ≤ X.Gi 5 ∧ ¬ X.Z 0 ≤ X.Gi (-5) := by
  constructor
  · intro h
    exact X.false_of_Z_zero_le_Gi_five hc hmax hs hodd h5 hX hGT hreg
      (Or.inl rfl) h
  · intro h
    exact X.false_of_Z_zero_le_Gi_five hc hmax hs hodd h5 hX hGT hreg
      (Or.inr rfl) h

theorem Z_zero_sup_Q_four (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 0 ⊔ X.Q 4 = X.edgeSylow 3 := by
  have h45 := X.not_Z_zero_le_Gi_five hc hmax hs hodd h5 hX hGT hreg
  have hZ0_4 : X.Z 0 ≤ X.Gi 4 :=
    (X.Z_zero_le_Gi_four hc hmax hs hodd h5 hX hGT hreg).trans inf_le_left
  have hZ0Q3 : X.Z 0 ≤ X.Q 3 :=
    X.Z_le_Q_of_le_Gi 0 4 3 hZ0_4 (Or.inr ⟨by omega, by omega⟩)
  have hA : X.Z 0 ≤ X.edgeSylow 3 := hZ0Q3.trans (X.Q_le_edgeSylow_left 3)
  have hnot : ¬ X.Z 0 ≤ X.Q 4 := fun h =>
    h45.1 (h.trans ((X.Q_le_Gi_adj 4).trans inf_le_right))
  have hK : X.K ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 k (X.K_le_Gi 0 hk)
  exact X.sup_Q_eq_edgeSylow_of_gen 3 (inf_le_left.trans hK) hA hnot

private theorem relIndex_Z_zero_inf_Q_four {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    (X.Z 0 ⊓ X.Q 4).relIndex (X.Z 0) = 2 ^ X.n 0 := by
  have hsup := X.Z_zero_sup_Q_four hc hmax hs hodd h5 hX hGT hreg
  have hZ0_4 : X.Z 0 ≤ X.Gi 4 :=
    (X.Z_zero_le_Gi_four hc hmax hs hodd h5 hX hGT hreg).trans inf_le_left
  have hZnorm : X.Z 0 ≤ Subgroup.normalizer (X.Q 4 : Set G) :=
    hZ0_4.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 4))
  have hKrel : (X.Q 4).relIndex (X.Z 0 ⊔ X.Q 4) =
      (X.Z 0 ⊓ X.Q 4).relIndex (X.Z 0) :=
    (CFSG.QuasithinUnique.C5.relIndex_inf_eq_of_le_normalizer hZnorm).symm
  have hrelS : (X.Q 4).relIndex (X.edgeSylow 3) = 2 ^ X.n 0 := by
    have hr := X.relIndex_Q_succ_edgeSylow 3
    rw [show (3 : ℤ) + 1 = 0 + 2 * 2 by norm_num, X.n_add] at hr
    exact hr
  rw [← hKrel, hsup]
  exact hrelS

theorem Z_zero_inf_Q_four (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 0 ⊓ X.Q 4 = ⊥ := by
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  haveI : Finite ↥(X.Z 0 ⊓ X.Q 4) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hrel := X.relIndex_Z_zero_inf_Q_four hc hmax hs hodd h5 hX hGT hreg
  have hle := X.card_Z_zero_le hc hmax hs hodd h5 hX hGT
  have hcard2 := Subgroup.relIndex_mul_card (H := X.Z 0 ⊓ X.Q 4) (K := X.Z 0)
  rw [show (X.Z 0 ⊓ X.Q 4) ⊓ X.Z 0 = X.Z 0 ⊓ X.Q 4 from inf_eq_left.mpr inf_le_left,
    hrel] at hcard2
  rw [← hcard2] at hle
  have hpos : 0 < 2 ^ X.n 0 := by positivity
  have hDle : Nat.card ↥(X.Z 0 ⊓ X.Q 4) ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by simpa using hle) hpos
  rw [Subgroup.eq_bot_iff_card]
  have := Nat.card_pos (α := ↥(X.Z 0 ⊓ X.Q 4))
  omega

theorem card_Z_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.Z 0) = 2 ^ X.n 0 := by
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hinf := X.Z_zero_inf_Q_four hc hmax hs hodd h5 hX hGT hreg
  have hrel := X.relIndex_Z_zero_inf_Q_four hc hmax hs hodd h5 hX hGT hreg
  have hcard2 := Subgroup.relIndex_mul_card (H := X.Z 0 ⊓ X.Q 4) (K := X.Z 0)
  rw [show (X.Z 0 ⊓ X.Q 4) ⊓ X.Z 0 = X.Z 0 ⊓ X.Q 4 from inf_eq_left.mpr inf_le_left,
    hrel, hinf] at hcard2
  simpa using hcard2.symm

private theorem Z_zero_le_Gi_of_mem {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {i : ℤ} (h1 : -4 ≤ i) (h2 : i ≤ 4) :
    X.Z 0 ≤ X.Gi i := by
  have h4 := X.Z_zero_le_Gi_four hc hmax hs hodd h5 hX hGT hreg
  intro z hz
  exact X.mem_Gi_of_between (h4 hz).2 (h4 hz).1 h1 h2

private theorem Z_two_le_Gi_of_mem {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {i : ℤ} (h1 : -2 ≤ i) (h2 : i ≤ 6) :
    X.Z 2 ≤ X.Gi i := by
  have hZ2eq : X.Z 2 = conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) := by
    have h := X.Z_add 1 0
    rw [show (0 + 2 * 1 : ℤ) = 2 by norm_num] at h
    exact h
  rw [hZ2eq]
  have hle := conjSub_mono (X.τ ^ (1 : ℤ))
    (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := i - 2)
      (by omega) (by omega))
  have hGi := X.Gi_add 1 (i - 2)
  rw [show i - 2 + 2 * 1 = i by ring] at hGi
  rw [hGi]
  exact hle

theorem Z_four_eq_conjSub_tau_sq :
    X.Z 4 = conjSub (X.τ ^ (2 : ℤ)) (X.Z 0) := by
  have h := X.Z_add 2 0
  rw [show (0 + 2 * 2 : ℤ) = 4 by norm_num] at h
  exact h

private theorem Z_neg_four_eq : X.Z (-4) = conjSub (X.τ ^ (-2 : ℤ)) (X.Z 0) := by
  have h := X.Z_add (-2) 0
  rw [show (0 + 2 * (-2) : ℤ) = -4 by norm_num] at h
  exact h

private theorem Z_two_eq : X.Z 2 = conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) := by
  have h := X.Z_add 1 0
  rw [show (0 + 2 * 1 : ℤ) = 2 by norm_num] at h
  exact h

private theorem card_Z_two {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.Z 2) = 2 ^ X.n 0 := by
  have hZ2eq := X.Z_two_eq
  rw [hZ2eq, card_conjSub, X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg]

private theorem card_Z_zero_sup_QT {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.Z 0 ⊔ X.QT) = 2 ^ X.n 0 * Nat.card ↥X.QT := by
  haveI : Finite ↥X.GT := finite_of_le_stabilizer X.hyp (H := X.GT) (X.GT_le_Gi 0)
  haveI : Finite ↥X.QT :=
    Finite.of_injective (Subgroup.inclusion X.QT_le_GT) (Subgroup.inclusion_injective _)
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hZT := X.Z_zero_le_ZM hc hmax hs hodd h5 hX hGT
  have hQT := X.QT_le_centerOf_Lst hGT hs hodd h5 hX
  have hcent : X.QT ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hQT hq)).2 z
      (Subgroup.mem_inf.mp (hZT hz)).1
  have hnorm : X.QT ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint (X.Z 0) X.QT :=
    disjoint_iff.mpr (by rw [inf_comm]; exact X.QT_inf_Z_eq_bot hGT hs hodd h5 hX 0)
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (X.Z 0) X.QT hnorm hdisj,
    X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg]

theorem ZM_eq_Z_zero_sup_QT (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.ZM = X.Z 0 ⊔ X.QT := by
  have h4 : X.Z 0 ⊔ X.QT ≤ X.ZM :=
    sup_le (X.Z_zero_le_ZM hc hmax hs hodd h5 hX hGT)
      (X.QT_le_centerOf_Lst hGT hs hodd h5 hX)
  haveI : Finite ↥X.ZM := finite_of_le_stabilizer X.hyp (H := X.ZM) X.ZM_le_Gi_zero
  have hm : m = 4 := X.m_eq_four hc hmax hs hodd h5 hX hGT hreg
  refine (Subgroup.eq_of_le_of_card_ge h4 ?_).symm
  rw [X.card_ZM hGT hs hodd h5 hX hreg,
    X.card_Z_zero_sup_QT hc hmax hs hodd h5 hX hGT hreg, hm]
  simp

theorem Z_four_sup_Q_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 4 ⊔ X.Q 0 = X.S := by
  have h45 := X.not_Z_zero_le_Gi_five hc hmax hs hodd h5 hX hGT hreg
  have hZ4 := X.Z_four_eq_conjSub_tau_sq
  have hGi : ∀ i : ℤ, -4 ≤ i → i ≤ 4 →
      conjSub (X.τ ^ (2 : ℤ)) (X.Z 0) ≤ X.Gi (i + 2 * 2) := by
    intro i h1 h2
    have hle := conjSub_mono (X.τ ^ (2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg h1 h2)
    rwa [← X.Gi_add 2 i] at hle
  have hZ4_Gi0 : X.Z 4 ≤ X.Gi 0 := by
    rw [hZ4]
    simpa using hGi (-4) (by omega) (by omega)
  have hZ4Q1 : X.Z 4 ≤ X.Q 1 :=
    X.Z_le_Q_of_le_Gi 4 0 1 hZ4_Gi0 (Or.inr ⟨by omega, by omega⟩)
  have hA : X.Z 4 ≤ X.edgeSylow 0 := (hZ4Q1.trans (X.Q_le_edgeSylow 0))
  have hnot : ¬ X.Z 4 ≤ X.Q 0 := by
    intro h
    have hle := h.trans ((X.Q_le_Gi_adj 0).trans inf_le_left)
    have hZ : conjSub (X.τ ^ (-2 : ℤ)) (X.Z 4) = X.Z 0 := by
      rw [hZ4]
      have h2 : (X.τ ^ (2 : ℤ))⁻¹ = X.τ ^ (-2 : ℤ) := (zpow_neg X.τ 2).symm
      rw [← h2]
      exact conjSub_conjSub_inv (X.τ ^ (2 : ℤ)) (X.Z 0)
    have hGi' : conjSub (X.τ ^ (-2 : ℤ)) (X.Gi (0 - 1)) = X.Gi (0 - 5) := by
      have := X.Gi_add (-2) (0 - 1)
      rw [show (0 - 1 : ℤ) + 2 * (-2) = 0 - 5 by ring] at this
      exact this.symm
    have hle' := conjSub_mono (X.τ ^ (-2 : ℤ)) hle
    rw [hZ, hGi'] at hle'
    exact h45.2 (by simpa using hle')
  have hK : X.K ≤ Subgroup.normalizer (X.Z 4 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 4 k (X.K_le_Gi 4 hk)
  have hEq := X.sup_Q_eq_edgeSylow_of_left_gen 0 (A := X.Z 4) (inf_le_left.trans hK)
    hA hnot
  rwa [X.edgeSylow_zero] at hEq

theorem Z_four_le_Gi_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 4 ≤ X.Gi 0 := by
  have h := X.Z_four_sup_Q_zero hc hmax hs hodd h5 hX hGT hreg
  have hS : X.S ≤ X.Gi 0 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left
  exact (le_sup_left : X.Z 4 ≤ X.Z 4 ⊔ X.Q 0).trans ((le_of_eq h).trans hS)

theorem Z_four_le_L_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 4 ≤ X.L 0 :=
  le_oTwoPrime_of_isPGroup
    ((pCoreOf_isPGroup' (X.Gi 4)).to_le (X.Z_le_Q 4))
    (X.Z_four_le_Gi_zero hc hmax hs hodd h5 hX hGT hreg)

theorem Z_neg_four_sup_Q_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z (-4) ⊔ X.Q 0 = X.edgeSylow (-1) := by
  have h45 := X.not_Z_zero_le_Gi_five hc hmax hs hodd h5 hX hGT hreg
  have hZm4 := X.Z_neg_four_eq
  have hGi : ∀ i : ℤ, -4 ≤ i → i ≤ 4 →
      conjSub (X.τ ^ (-2 : ℤ)) (X.Z 0) ≤ X.Gi (i + 2 * (-2)) := by
    intro i h1 h2
    have hle := conjSub_mono (X.τ ^ (-2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg h1 h2)
    rwa [← X.Gi_add (-2) i] at hle
  have hZm4_Gi0 : X.Z (-4) ≤ X.Gi 0 := by
    rw [hZm4]
    simpa using hGi 4 (by omega) (by omega)
  have hZm4Q : X.Z (-4) ≤ X.Q (-1) :=
    X.Z_le_Q_of_le_Gi (-4) 0 (-1) hZm4_Gi0 (Or.inr ⟨by omega, by omega⟩)
  have hA : X.Z (-4) ≤ X.edgeSylow (-1) := hZm4Q.trans (X.Q_le_edgeSylow_left (-1))
  have hnot : ¬ X.Z (-4) ≤ X.Q 0 := by
    intro h
    have hle := h.trans ((X.Q_le_Gi_adj 0).trans inf_le_right)
    have hZ : conjSub (X.τ ^ (2 : ℤ)) (X.Z (-4)) = X.Z 0 := by
      rw [hZm4, ← conjSub_mul]
      have h1 : X.τ ^ (2 : ℤ) * X.τ ^ (-2 : ℤ) = 1 := by
        rw [← zpow_add]
        norm_num
      rw [h1]
      exact conjSub_one (X.Z 0)
    have hGi' : conjSub (X.τ ^ (2 : ℤ)) (X.Gi (0 + 1)) = X.Gi (0 + 5) := by
      have := X.Gi_add 2 (0 + 1)
      rw [show (0 + 1 : ℤ) + 2 * 2 = 0 + 5 by ring] at this
      exact this.symm
    have hle' := conjSub_mono (X.τ ^ (2 : ℤ)) hle
    rw [hZ, hGi'] at hle'
    exact h45.1 (by simpa using hle')
  have hK : X.K ≤ Subgroup.normalizer (X.Z (-4) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal (-4) k (X.K_le_Gi (-4) hk)
  exact X.sup_Q_eq_edgeSylow_of_gen (-1) (A := X.Z (-4)) (inf_le_left.trans hK) hA hnot

theorem Z_four_inf_Q_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 4 ⊓ X.Q 0 = ⊥ := by
  haveI : Finite ↥(X.Z 4) := by
    have hle : X.Z 4 ≤ X.Gi 4 := by
      rw [X.Z_four_eq_conjSub_tau_sq]
      have h := conjSub_mono (X.τ ^ (2 : ℤ))
        (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg
          (i := 0) (by omega) (by omega))
      rwa [← X.Gi_add 2 0] at h
    exact finite_of_le_stabilizer X.hyp hle
  haveI : Finite ↥(X.Z 4 ⊓ X.Q 0) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hsup := X.Z_four_sup_Q_zero hc hmax hs hodd h5 hX hGT hreg
  have hcard4 : Nat.card ↥(X.Z 4) = 2 ^ X.n 0 := by
    rw [X.Z_four_eq_conjSub_tau_sq, card_conjSub,
      X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg]
  have hZnorm : X.Z 4 ≤ Subgroup.normalizer (X.Q 0 : Set G) := by
    have hZ0 : X.Z 4 ≤ X.Gi 0 := by
      rw [X.Z_four_eq_conjSub_tau_sq]
      have h := conjSub_mono (X.τ ^ (2 : ℤ))
        (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg
          (i := -4) (by omega) (by omega))
      rwa [← X.Gi_add 2 (-4)] at h
    exact hZ0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hKrel : (X.Q 0).relIndex (X.Z 4 ⊔ X.Q 0) = (X.Z 4 ⊓ X.Q 0).relIndex (X.Z 4) :=
    (CFSG.QuasithinUnique.C5.relIndex_inf_eq_of_le_normalizer hZnorm).symm
  have hrel : (X.Z 4 ⊓ X.Q 0).relIndex (X.Z 4) = 2 ^ X.n 0 := by
    rw [← hKrel, hsup]
    exact X.relIndex_Q_edgeSylow 0
  have hcard2 := Subgroup.relIndex_mul_card (H := X.Z 4 ⊓ X.Q 0) (K := X.Z 4)
  rw [show (X.Z 4 ⊓ X.Q 0) ⊓ X.Z 4 = X.Z 4 ⊓ X.Q 0 from inf_eq_left.mpr inf_le_left,
    hrel, hcard4] at hcard2
  have hpos : 0 < 2 ^ X.n 0 := by positivity
  have hDle : Nat.card ↥(X.Z 4 ⊓ X.Q 0) ≤ 1 := by
    have h1 : Nat.card ↥(X.Z 4 ⊓ X.Q 0) = 1 :=
      Nat.mul_left_cancel hpos (by rw [mul_one]; exact hcard2)
    omega
  rw [Subgroup.eq_bot_iff_card]
  have := Nat.card_pos (α := ↥(X.Z 4 ⊓ X.Q 0))
  omega

private theorem card_Z_four {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.Z 4) = 2 ^ X.n 0 := by
  rw [X.Z_four_eq_conjSub_tau_sq, card_conjSub,
    X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg]

private theorem card_Z_neg_four {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.Z (-4)) = 2 ^ X.n 0 := by
  rw [X.Z_neg_four_eq, card_conjSub, X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg]

private theorem Z_neg_four_inf_Q_zero {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z (-4) ⊓ X.Q 0 = ⊥ := by
  have hZm4_Gi1 : X.Z (-4) ≤ X.Gi (-1) := by
    rw [X.Z_neg_four_eq]
    have h := conjSub_mono (X.τ ^ (-2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 3) (by omega) (by omega))
    rwa [← X.Gi_add (-2) 3] at h
  have hZm4_Gi0 : X.Z (-4) ≤ X.Gi 0 := by
    rw [X.Z_neg_four_eq]
    have h := conjSub_mono (X.τ ^ (-2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 4) (by omega) (by omega))
    rwa [← X.Gi_add (-2) 4] at h
  haveI : Finite ↥(X.Z (-4)) := finite_of_le_stabilizer X.hyp (H := X.Z (-4)) hZm4_Gi1
  haveI : Finite ↥(X.Z (-4) ⊓ X.Q 0) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hsup := X.Z_neg_four_sup_Q_zero hc hmax hs hodd h5 hX hGT hreg
  have hcard := X.card_Z_neg_four hc hmax hs hodd h5 hX hGT hreg
  have hZnorm : X.Z (-4) ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hZm4_Gi0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hKrel : (X.Q 0).relIndex (X.Z (-4) ⊔ X.Q 0) =
      (X.Z (-4) ⊓ X.Q 0).relIndex (X.Z (-4)) :=
    (CFSG.QuasithinUnique.C5.relIndex_inf_eq_of_le_normalizer hZnorm).symm
  have hrel : (X.Z (-4) ⊓ X.Q 0).relIndex (X.Z (-4)) = 2 ^ X.n 0 := by
    rw [← hKrel, hsup]
    have hr := X.relIndex_Q_succ_edgeSylow (-1)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at hr
    exact hr
  have hcard2 := Subgroup.relIndex_mul_card (H := X.Z (-4) ⊓ X.Q 0) (K := X.Z (-4))
  rw [show (X.Z (-4) ⊓ X.Q 0) ⊓ X.Z (-4) = X.Z (-4) ⊓ X.Q 0 from
      inf_eq_left.mpr inf_le_left, hrel, hcard] at hcard2
  have hpos : 0 < 2 ^ X.n 0 := by positivity
  have hDle : Nat.card ↥(X.Z (-4) ⊓ X.Q 0) ≤ 1 := by
    have h1 : Nat.card ↥(X.Z (-4) ⊓ X.Q 0) = 1 :=
      Nat.mul_left_cancel hpos (by rw [mul_one]; exact hcard2)
    omega
  rw [Subgroup.eq_bot_iff_card]
  have := Nat.card_pos (α := ↥(X.Z (-4) ⊓ X.Q 0))
  omega

theorem L_zero_eq_Z_four_sup (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.L 0 = X.Z 4 ⊔ X.Z (-4) ⊔ X.Q 0 := by
  have hP4 : IsPGroup 2 (X.Z 4) := (pCoreOf_isPGroup' (X.Gi 4)).to_le (X.Z_le_Q 4)
  have hZ4_Gi0 : X.Z 4 ≤ X.Gi 0 := by
    rw [X.Z_four_eq_conjSub_tau_sq]
    have h := conjSub_mono (X.τ ^ (2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := -4) (by omega) (by omega))
    rwa [← X.Gi_add 2 (-4)] at h
  have hZ4_Gi1 : X.Z 4 ≤ X.Gi 1 := by
    rw [X.Z_four_eq_conjSub_tau_sq]
    have h := conjSub_mono (X.τ ^ (2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := -3) (by omega) (by omega))
    rwa [← X.Gi_add 2 (-3)] at h
  have hPm : IsPGroup 2 (X.Z (-4)) := (pCoreOf_isPGroup' (X.Gi (-4))).to_le (X.Z_le_Q (-4))
  have hZm_Gi0 : X.Z (-4) ≤ X.Gi 0 := by
    rw [X.Z_neg_four_eq]
    have h := conjSub_mono (X.τ ^ (-2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 4) (by omega) (by omega))
    rwa [← X.Gi_add (-2) 4] at h
  have hZm_Gi1 : X.Z (-4) ≤ X.Gi (-1) := by
    rw [X.Z_neg_four_eq]
    have h := conjSub_mono (X.τ ^ (-2 : ℤ))
      (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 3) (by omega) (by omega))
    rwa [← X.Gi_add (-2) 3] at h
  have hA : X.Z 4 ≤ X.L 0 := le_oTwoPrime_of_isPGroup hP4 hZ4_Gi0
  have hB : X.Z (-4) ≤ X.L 0 := le_oTwoPrime_of_isPGroup hPm hZm_Gi0
  have hAidx : (X.Z 4 ⊓ X.Q 0).relIndex (X.Z 4) = 2 ^ X.n 0 := by
    rw [X.Z_four_inf_Q_zero hc hmax hs hodd h5 hX hGT hreg,
      Subgroup.relIndex_bot_left, X.card_Z_four hc hmax hs hodd h5 hX hGT hreg]
  have hBidx : (X.Z (-4) ⊓ X.Q 0).relIndex (X.Z (-4)) = 2 ^ X.n 0 := by
    rw [X.Z_neg_four_inf_Q_zero hc hmax hs hodd h5 hX hGT hreg,
      Subgroup.relIndex_bot_left, X.card_Z_neg_four hc hmax hs hodd h5 hX hGT hreg]
  have hab : X.vert 1 ≠ X.vert (-1) := by
    intro h
    have := X.vert_injective h
    omega
  exact X.L_eq_sup_of_fixes 0 (X.adj 0) (by simpa using (X.adj (-1)).symm) hab
    hA hB hZ4_Gi1 hZm_Gi1 hAidx hBidx

theorem Z_zero_sup_Z_two_le (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 0 ⊔ X.Z 2 ≤ X.Z 1 := by
  have hS : IsSylowTwoOf X.S (X.Gi 1) := by
    simpa using isSylowTwoOf_of_edgeStab X.hyp (X.adj 0).symm
      (show IsSylowTwoOf X.S (X.Gi 1 ⊓ X.Gi 0) from by
        simpa [X.edgeSylow_zero, inf_comm] using X.isSylowTwoOf_edgeSylow 0)
  have hS12 : IsSylowTwoOf (X.edgeSylow 1) (X.Gi 1) :=
    isSylowTwoOf_of_edgeStab X.hyp (X.adj 1) (X.isSylowTwoOf_edgeSylow 1)
  have hZ0_2 : X.Z 0 ≤ X.Gi 2 :=
    X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 2) (by omega) (by omega)
  have hZ0Q1 : X.Z 0 ≤ X.Q 1 :=
    X.Z_le_Q_of_le_Gi 0 2 1 hZ0_2 (Or.inr ⟨by omega, by omega⟩)
  have hZ0S := X.Z_zero_le_centerOf_S hc hmax hs hodd h5 hX hGT
  have hZ2_Gi0 : X.Z 2 ≤ X.Gi 0 :=
    X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 0)
      (by omega) (by omega)
  have hZ2Q1 : X.Z 2 ≤ X.Q 1 :=
    X.Z_le_Q_of_le_Gi 2 0 1 hZ2_Gi0 (Or.inr ⟨by omega, by omega⟩)
  have hZ2S := X.Z_two_le_centerOf_edgeSylow_one hc hmax hs hodd h5 hX hGT
  refine sup_le ?_ ?_
  · have hle : centerOf X.S ⊓ X.Q 1 ≤ X.Z 1 :=
      X.le_Z_of_le_centerOf_sylow 1 hS inf_le_left inf_le_right
    intro z hz
    exact hle (Subgroup.mem_inf.mpr ⟨hZ0S hz, hZ0Q1 hz⟩)
  · have hle : centerOf (X.edgeSylow 1) ⊓ X.Q 1 ≤ X.Z 1 :=
      X.le_Z_of_le_centerOf_sylow 1 hS12 inf_le_left inf_le_right
    intro z hz
    exact hle (Subgroup.mem_inf.mpr ⟨hZ2S hz, hZ2Q1 hz⟩)

theorem Z_zero_inf_Z_two (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 0 ⊓ X.Z 2 = ⊥ := by
  have hZ2_5 : X.Z 2 ≤ X.Gi 5 :=
    X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 5)
      (by omega) (by omega)
  have hZ2Q4 : X.Z 2 ≤ X.Q 4 :=
    X.Z_le_Q_of_le_Gi 2 5 4 hZ2_5 (Or.inr ⟨by omega, by omega⟩)
  refine le_antisymm ?_ bot_le
  exact (le_inf inf_le_left (inf_le_right.trans hZ2Q4)).trans
    (le_of_eq (X.Z_zero_inf_Q_four hc hmax hs hodd h5 hX hGT hreg))

private theorem card_Z_zero_sup_Z_two {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card ↥(X.Z 0 ⊔ X.Z 2) = 2 ^ X.n 0 * 2 ^ X.n 0 := by
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  haveI : Finite ↥(X.Z 2) := finite_of_le_stabilizer X.hyp (H := X.Z 2)
    (X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 2)
      (by omega) (by omega))
  haveI : Finite ↥(X.Z 0 ⊔ X.Z 2) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 0 ⊔ X.Z 2)
      (sup_le (X.Z_le_Gi 0) (X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg
        (i := 0) (by omega) (by omega)))
  have hdisj : Disjoint (X.Z 0) (X.Z 2) :=
    disjoint_iff.mpr (X.Z_zero_inf_Z_two hc hmax hs hodd h5 hX hGT hreg)
  have hnorm : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 k
      (X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 0)
        (by omega) (by omega) hk)
  have hcardZ2 : Nat.card ↥(X.Z 2) = 2 ^ X.n 0 :=
    X.card_Z_two hc hmax hs hodd h5 hX hGT hreg
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (X.Z 0) (X.Z 2) hnorm hdisj,
    X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg, hcardZ2]

private theorem Z_one_le_normalizer_ZM : X.Z 1 ≤ Subgroup.normalizer (X.ZM : Set G) :=
  ((le_inf (X.Z_le_normalizer_QT
      1) ((X.Z_le_Q 1).trans ((X.Q_le_Gi_adj 1).trans inf_le_left))).trans
    ((le_normalizer_oTwoPrime (X.normGi X.QT 0)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_centerOf (X.Lst X.QT 0))))

theorem Z_one_inf_ZM {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 ⊓ X.ZM = X.Z 0 := by
  have hZM_sup : X.ZM = X.Z 0 ⊔ X.QT :=
    X.ZM_eq_Z_zero_sup_QT hc hmax hs hodd h5 hX hGT hreg
  have hZ0_le_Z1 : X.Z 0 ≤ X.Z 1 :=
    le_trans le_sup_left (X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg)
  have hprod : (↑(X.Z 0 ⊔ X.QT) : Set G) = (X.Z 0 : Set G) * (X.QT : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 0) X.QT (X.Z_le_normalizer_QT 0)
  refine le_antisymm ?_ (le_inf hZ0_le_Z1 (X.Z_zero_le_ZM hc hmax hs hodd h5 hX hGT))
  intro x hx
  obtain ⟨hx1, hxM⟩ := Subgroup.mem_inf.mp hx
  rw [hZM_sup] at hxM
  have hxmul : x ∈ (X.Z 0 : Set G) * (X.QT : Set G) := by rw [← hprod]; exact hxM
  obtain ⟨a, ha, b, hb, hab⟩ := hxmul
  have hb1 : b ∈ X.Z 1 := by
    have hbeq : b = a⁻¹ * x := by rw [← hab]; group
    rw [hbeq]
    exact (X.Z 1).mul_mem ((X.Z 1).inv_mem (hZ0_le_Z1 ha)) hx1
  have hbZ1QT : b ∈ X.Z 1 ⊓ X.QT := Subgroup.mem_inf.mpr ⟨hb1, hb⟩
  have hbot : X.Z 1 ⊓ X.QT = ⊥ := by
    rw [inf_comm]
    exact X.QT_inf_Z_eq_bot hGT hs hodd h5 hX 1
  rw [hbot] at hbZ1QT
  have hb1' : b = 1 := by simpa using hbZ1QT
  rw [show x = a * b from hab.symm, hb1', mul_one]
  exact ha

theorem Z_one_le_relCent (hZ1E : X.Z 1 ≤ X.E X.QT 0) :
    X.Z 1 ≤ relCent (X.E X.QT 0) X.ZM (X.skP X.QT) := by
  intro z hz
  rw [mem_relCent X.E_le_normalizer_ZM]
  refine ⟨hZ1E hz, fun a ha => ?_⟩
  have hcomm : a * z = z * a :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2) a
      ((inf_le_left : X.skP X.QT ≤ X.Q 1) ha)
  rw [show ⁅z, a⁆ = 1 by rw [commutatorElement_def, ← hcomm]; group]
  exact X.ZM.one_mem

theorem ZM_le_relCent_of_le_Lst (hZME : X.ZM ≤ X.E X.QT 0) {P : Subgroup G}
    (hP : P ≤ X.Lst X.QT 0) : X.ZM ≤ relCent (X.E X.QT 0) X.ZM P := by
  intro z hz
  rw [mem_relCent X.E_le_normalizer_ZM]
  refine ⟨hZME hz, fun a ha => ?_⟩
  have hcomm : a * z = z * a :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2) a (hP ha)
  rw [show ⁅z, a⁆ = 1 by rw [commutatorElement_def, ← hcomm]; group]
  exact X.ZM.one_mem

private theorem relIndex_Z_one_inf_ZM_le (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    :
    (X.Z 1 ⊓ X.ZM).relIndex (X.Z 1) ≤ 2 ^ X.n 0 := by
  haveI : Finite ↥X.ZM := finite_of_le_stabilizer X.hyp (H := X.ZM) X.ZM_le_Gi_zero
  haveI : Finite ↥(relCent (X.E X.QT 0) X.ZM (X.skP X.QT)) :=
    finite_of_le_stabilizer X.hyp
      (H := relCent (X.E X.QT 0) X.ZM (X.skP X.QT))
      (fun x hx => (inf_le_left.trans (X.Q_le_Gi 0)) hx.1)
  have hNQ := X.natQuot_M hGT hs hodd h5 hX
  have hPSyl := X.isSylowTwoOf_skP_Lst_QT hGT hs hodd h5 hX
  have hZ1rel : X.Z 1 ≤ relCent (X.E X.QT 0) X.ZM (X.skP X.QT) :=
    X.Z_one_le_relCent (X.Z_one_le_E hGT hs hodd h5 hX)
  have hZMrel : X.ZM ≤ relCent (X.E X.QT 0) X.ZM (X.skP X.QT) :=
    X.ZM_le_relCent_of_le_Lst hNQ.Z_le hPSyl.1
  have hsup_rel : X.Z 1 ⊔ X.ZM ≤ relCent (X.E X.QT 0) X.ZM (X.skP X.QT) :=
    sup_le hZ1rel hZMrel
  have hline : X.ZM.relIndex (relCent (X.E X.QT 0) X.ZM (X.skP X.QT)) = 2 ^ X.n 0 :=
    hNQ.line (X.skP X.QT) hPSyl
  have hKrel : X.ZM.relIndex (X.Z 1 ⊔ X.ZM) = (X.Z 1 ⊓ X.ZM).relIndex (X.Z 1) :=
    (CFSG.QuasithinUnique.C5.relIndex_inf_eq_of_le_normalizer X.Z_one_le_normalizer_ZM).symm
  have hne : X.ZM.relIndex (relCent (X.E X.QT 0) X.ZM (X.skP X.QT)) ≠ 0 := by
    intro h0
    have hdvd := Subgroup.relIndex_dvd_card
      (H := X.ZM) (K := relCent (X.E X.QT 0) X.ZM (X.skP X.QT))
    rw [h0] at hdvd
    have hzero : Nat.card ↥(relCent (X.E X.QT 0) X.ZM (X.skP X.QT)) = 0 :=
      Nat.eq_zero_of_zero_dvd hdvd
    exact (Nat.card_pos (α := ↥(relCent (X.E X.QT 0) X.ZM (X.skP X.QT)))).ne' hzero
  rw [← hKrel, ← hline]
  exact Subgroup.relIndex_le_of_le_right hsup_rel hne

theorem card_Z_one_sq (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    Nat.card (X.Z 1) = 2 ^ (2 * X.n 0) := by
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  haveI : Finite ↥X.ZM := finite_of_le_stabilizer X.hyp (H := X.ZM) X.ZM_le_Gi_zero
  haveI : Finite ↥(X.Z 1 ⊓ X.ZM) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hZ1_Gi0 : X.Z 1 ≤ X.Gi 0 :=
    (X.Z_le_Q 1).trans ((X.Q_le_Gi_adj 1).trans inf_le_left)
  have hZM_Gi0 : X.ZM ≤ X.Gi 0 := X.ZM_le_Gi_zero
  haveI : Finite ↥(X.Z 1 ⊔ X.ZM) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 1 ⊔ X.ZM) (sup_le hZ1_Gi0 hZM_Gi0)
  have hZ1ZM := X.Z_one_inf_ZM hc hmax hs hodd h5 hX hGT hreg
  have hrel_le := X.relIndex_Z_one_inf_ZM_le hGT hs hodd h5 hX
  have hcardD : Nat.card ↥(X.Z 1 ⊓ X.ZM) = 2 ^ X.n 0 := by
    rw [hZ1ZM]
    exact X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg
  have hupper : Nat.card ↥(X.Z 1) ≤ 2 ^ (2 * X.n 0) := by
    have hmul := Subgroup.relIndex_mul_card (H := X.Z 1 ⊓ X.ZM) (K := X.Z 1)
    rw [show (X.Z 1 ⊓ X.ZM) ⊓ X.Z 1 = X.Z 1 ⊓ X.ZM from inf_eq_left.mpr inf_le_left] at hmul
    rw [← hmul]
    calc (X.Z 1 ⊓ X.ZM).relIndex (X.Z 1) * Nat.card ↥(X.Z 1 ⊓ X.ZM)
        ≤ 2 ^ X.n 0 * 2 ^ X.n 0 := Nat.mul_le_mul hrel_le (le_of_eq hcardD)
      _ = 2 ^ (2 * X.n 0) := by
          rw [← pow_add]
          congr 1
          ring
  have hlower : 2 ^ (2 * X.n 0) ≤ Nat.card ↥(X.Z 1) := by
    rw [show 2 ^ (2 * X.n 0) = 2 ^ X.n 0 * 2 ^ X.n 0 by
        rw [← pow_add]
        congr 1
        ring,
      ← X.card_Z_zero_sup_Z_two hc hmax hs hodd h5 hX hGT hreg]
    exact Subgroup.card_le_of_le
      (X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg)
  exact le_antisymm hupper hlower

theorem Z_one_eq_Z_zero_sup_Z_two (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 = X.Z 0 ⊔ X.Z 2 := by
  have hle := X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hZ2_2 : X.Z 2 ≤ X.Gi 2 :=
    X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 2)
      (by omega) (by omega)
  haveI : Finite ↥(X.Z 2) := finite_of_le_stabilizer X.hyp (H := X.Z 2) hZ2_2
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [X.card_Z_zero_sup_Z_two hc hmax hs hodd h5 hX hGT hreg,
    X.card_Z_one_sq hc hmax hs hodd h5 hX hGT hreg]
  rw [← pow_add, show 2 * X.n 0 = X.n 0 + X.n 0 by ring]

theorem Z_three_eq_Z_two_sup_Z_four (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 3 = X.Z 2 ⊔ X.Z 4 := by
  have h := congrArg (conjSub X.τ)
    (X.Z_one_eq_Z_zero_sup_Z_two hc hmax hs hodd h5 hX hGT hreg)
  rw [conjSub_sup] at h
  have hZ1 : conjSub X.τ (X.Z 1) = X.Z 3 := by simpa using (X.Z_add 1 1).symm
  have hZ0 : conjSub X.τ (X.Z 0) = X.Z 2 := by simpa using (X.Z_add 1 0).symm
  have hZ2 : conjSub X.τ (X.Z 2) = X.Z 4 := by simpa using (X.Z_add 1 2).symm
  rw [hZ1, hZ0, hZ2] at h
  exact h

theorem Z_one_b_facts (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 ≤ X.Gi (-2) ⊓ X.Gi 4 ∧ ¬ X.Z 1 ≤ X.Gi 5 ∧ ¬ X.Z 1 ≤ X.Gi (-3) := by
  have hZ1 := X.Z_one_eq_Z_zero_sup_Z_two hc hmax hs hodd h5 hX hGT hreg
  have h45 := X.not_Z_zero_le_Gi_five hc hmax hs hodd h5 hX hGT hreg
  have hle := X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg
  refine ⟨?_, ?_, ?_⟩
  · refine le_inf ?_ ?_
    · rw [hZ1]
      exact sup_le
        (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg
          (i := -2) (by omega) (by omega))
        (X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg
          (i := -2) (by omega) (by omega))
    · rw [hZ1]
      exact sup_le
        (X.Z_zero_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg
          (i := 4) (by omega) (by omega))
        (X.Z_two_le_Gi_of_mem hc hmax hs hodd h5 hX hGT hreg (i := 4) (by omega) (by omega))
  · intro h
    exact h45.1 (le_trans le_sup_left (le_trans hle h))
  · intro h
    have hZ2le : X.Z 2 ≤ X.Z 1 := le_trans le_sup_right hle
    have h2 : X.Z 2 ≤ X.Gi (-3) := le_trans hZ2le h
    have hZ2eq := X.Z_two_eq
    have hZ : conjSub (X.τ ^ (-1 : ℤ)) (X.Z 2) = X.Z 0 := by
      rw [hZ2eq, ← conjSub_mul]
      have h1 : X.τ ^ (-1 : ℤ) * X.τ ^ (1 : ℤ) = 1 := by
        rw [← zpow_add]
        norm_num
      rw [h1]
      exact conjSub_one (X.Z 0)
    have hGi : conjSub (X.τ ^ (-1 : ℤ)) (X.Gi (-3)) = X.Gi (-5) := by
      have h0 := X.Gi_add (-1) (-3)
      rw [show (-3 : ℤ) + 2 * (-1) = -5 by ring] at h0
      exact h0.symm
    have hle' := conjSub_mono (X.τ ^ (-1 : ℤ)) h2
    rw [hZ, hGi] at hle'
    exact h45.2 hle'

private theorem Z_one_le_S : X.Z 1 ≤ X.S := by
  rw [← X.edgeSylow_zero]
  exact (X.Z_le_Q 1).trans (X.Q_le_edgeSylow (i := 0))

theorem Z_one_le_Q_zero {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 ≤ X.Q 0 := by
  exact X.Z_le_Q_of_le_Gi 1 (-2) 0 ((X.Z_one_b_facts hc hmax hs hodd h5 hX hGT
    hreg).1.trans inf_le_left) (Or.inr ⟨by omega, by omega⟩)

private theorem Z_one_le_Q_two {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 ≤ X.Q 2 := by
  exact X.Z_le_Q_of_le_Gi 1 4 2 ((X.Z_one_b_facts hc hmax hs hodd h5 hX hGT
    hreg).1.trans inf_le_right) (Or.inr ⟨by omega, by omega⟩)

theorem L_one_inf_centralizer_Z_one (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.L 1 ⊓ Subgroup.centralizer (X.Z 1 : Set G) = X.Q 1 := by
  by_contra hne
  have hZ1cent : X.Z 1 ≤ centerOf (X.L 1) :=
    X.Z_one_le_centerOf_L_one_of_ne hne
  have hZ1_Q0 := X.Z_one_le_Q_zero hc hmax hs hodd h5 hX hGT hreg
  have hZ1_S := X.Z_one_le_S
  have hS : IsSylowTwoOf X.S (X.Gi 0) := X.isSylowTwoOf_S_Gi_zero
  have hS_L1 : X.S ≤ X.L 1 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hZ1_centS : X.Z 1 ≤ centerOf X.S := by
    refine le_inf hZ1_S ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hzcent : z ∈ Subgroup.centralizer (X.L 1 : Set G) :=
      (Subgroup.mem_inf.mp (hZ1cent hz)).2
    exact Subgroup.mem_centralizer_iff.mp hzcent s (hS_L1 hs)
  have hle : centerOf X.S ⊓ X.Q 0 ≤ X.Z 0 :=
    X.le_Z_of_le_centerOf_sylow 0 hS inf_le_left inf_le_right
  have hZ1_Z0 : X.Z 1 ≤ X.Z 0 := by
    intro z hz
    exact hle (Subgroup.mem_inf.mpr ⟨hZ1_centS hz, hZ1_Q0 hz⟩)
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  haveI : Finite ↥(X.Z 0) := finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hcard_le : Nat.card ↥(X.Z 1) ≤ Nat.card ↥(X.Z 0) := Subgroup.card_le_of_le hZ1_Z0
  rw [X.card_Z_one_sq hc hmax hs hodd h5 hX hGT hreg,
    X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg] at hcard_le
  have hn0pos : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
  have hpow : 2 ^ X.n 0 * 2 ^ X.n 0 = 2 ^ (2 * X.n 0) := by
    rw [← pow_add]
    congr 1
    ring
  have hle1 : 2 ^ X.n 0 ≤ 1 := by
    refine Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < 2 ^ X.n 0)
    calc 2 ^ X.n 0 * 2 ^ X.n 0 = 2 ^ (2 * X.n 0) := hpow
      _ ≤ 2 ^ X.n 0 := hcard_le
      _ = 1 * 2 ^ X.n 0 := (one_mul _).symm
  have h2 : 2 ≤ 2 ^ X.n 0 := by
    have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn0pos
    simpa using h
  omega

private theorem Z_one_inf_centralizer_eq {T : Set G} {W Y : Subgroup G}
    (hW : W ≤ X.Z 1 ⊓ Subgroup.centralizer T) (hY : Y ≤ X.Z 1)
    (hdisj : X.Z 1 ⊓ Subgroup.centralizer T ⊓ Y = ⊥)
    (hcardY : Nat.card ↥Y = 2 ^ X.n 0) (hcardW : Nat.card ↥W = 2 ^ X.n 0)
    (hcardZ1 : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 0)) :
    X.Z 1 ⊓ Subgroup.centralizer T = W := by
  haveI : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  haveI : Finite ↥Y := finite_of_le_stabilizer X.hyp (H := Y) (hY.trans (X.Z_le_Gi 1))
  haveI : Finite ↥(X.Z 1 ⊓ Subgroup.centralizer T) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  haveI : Finite ↥W :=
    finite_of_le_stabilizer X.hyp (H := W) (hW.trans (inf_le_left.trans (X.Z_le_Gi 1)))
  have hnorm : Y ≤ Subgroup.normalizer
      ((X.Z 1 ⊓ Subgroup.centralizer T : Subgroup G) : Set G) := by
    have hcent : Y ≤ Subgroup.centralizer
        (X.Z 1 ⊓ Subgroup.centralizer T : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact X.Z_commute 1 c hc.1 k (hY hk)
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcard_sup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (X.Z 1 ⊓ Subgroup.centralizer T) Y hnorm (disjoint_iff.mpr hdisj)
  have hle_sup : X.Z 1 ⊓ Subgroup.centralizer T ⊔ Y ≤ X.Z 1 :=
    sup_le inf_le_left hY
  have hcard_le : Nat.card ↥(X.Z 1 ⊓ Subgroup.centralizer T ⊔ Y) ≤
      Nat.card ↥(X.Z 1) := Subgroup.card_le_of_le hle_sup
  rw [hcard_sup, hcardY, hcardZ1] at hcard_le
  have hcardC : Nat.card ↥(X.Z 1 ⊓ Subgroup.centralizer T) ≤ 2 ^ X.n 0 := by
    have hpos : 0 < 2 ^ X.n 0 := by positivity
    have h2 : 2 ^ (2 * X.n 0) = 2 ^ X.n 0 * 2 ^ X.n 0 := by
      rw [← pow_add]
      congr 1
      ring
    rw [h2] at hcard_le
    exact Nat.le_of_mul_le_mul_right hcard_le hpos
  refine (Subgroup.eq_of_le_of_card_ge hW ?_).symm
  rw [hcardW]
  exact hcardC

theorem centralizer_S_eq (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 ⊓ Subgroup.centralizer (X.S : Set G) = X.Z 0 := by
  have hsup := X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg
  have hZ0_le_Z1 : X.Z 0 ≤ X.Z 1 := le_sup_left.trans hsup
  have hZ2_le_Z1 : X.Z 2 ≤ X.Z 1 := le_sup_right.trans hsup
  have hZ0_le_C : X.Z 0 ≤ X.Z 1 ⊓ Subgroup.centralizer (X.S : Set G) := by
    refine le_inf hZ0_le_Z1 ?_
    exact (X.Z_zero_le_centerOf_S hc hmax hs hodd h5 hX hGT).trans inf_le_right
  have hS0 : IsSylowTwoOf X.S (X.Gi 0) := X.isSylowTwoOf_S_Gi_zero
  have hdisj : X.Z 1 ⊓ Subgroup.centralizer (X.S : Set G) ⊓ X.Z 2 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxC, hxZ2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxZ1, hxcentS⟩ := Subgroup.mem_inf.mp hxC
    have hxS : x ∈ X.S := X.Z_one_le_S hxZ1
    have hxZS : x ∈ centerOf X.S := Subgroup.mem_inf.mpr ⟨hxS, hxcentS⟩
    have hxZ0 : x ∈ X.Z 0 := by
      have hle : centerOf X.S ⊓ X.Q 0 ≤ X.Z 0 :=
        X.le_Z_of_le_centerOf_sylow 0 hS0 inf_le_left inf_le_right
      exact hle (Subgroup.mem_inf.mpr
        ⟨hxZS, X.Z_one_le_Q_zero hc hmax hs hodd h5 hX hGT hreg hxZ1⟩)
    have hx0 : x ∈ X.Z 0 ⊓ X.Z 2 := Subgroup.mem_inf.mpr ⟨hxZ0, hxZ2⟩
    rw [X.Z_zero_inf_Z_two hc hmax hs hodd h5 hX hGT hreg] at hx0
    simpa using hx0
  exact X.Z_one_inf_centralizer_eq (T := X.S) (W := X.Z 0) (Y := X.Z 2)
    hZ0_le_C hZ2_le_Z1 hdisj
    (X.card_Z_two hc hmax hs hodd h5 hX hGT hreg)
    (X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg)
    (X.card_Z_one_sq hc hmax hs hodd h5 hX hGT hreg)

private theorem Q_one_comm_Z_one : ∀ q ∈ X.Q 1, ∀ z ∈ X.Z 1, q * z = z * q := by
  intro q hq z hz
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2 q hq

private theorem Z_zero_exp_two {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∀ z ∈ X.Z 0, z ^ 2 = 1 := by
  intro z hz
  have h4 : z ^ 2 ∈ X.Q 4 := by
    refine X.sq_mem_Q_of_relIndex (S := X.edgeSylow 3) (j := 4)
      (X.isSylowTwoOf_edgeSylow_L_succ 3).1 (X.relIndex_Q_succ_edgeSylow 3) z ?_
    rw [← X.Z_zero_sup_Q_four hc hmax hs hodd h5 hX hGT hreg]
    exact Subgroup.mem_sup_left hz
  have hmem : z ^ 2 ∈ X.Z 0 ⊓ X.Q 4 :=
    Subgroup.mem_inf.mpr ⟨(X.Z 0).pow_mem hz 2, h4⟩
  rw [X.Z_zero_inf_Q_four hc hmax hs hodd h5 hX hGT hreg] at hmem
  simpa using hmem

private theorem Z_two_exp_two {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∀ z ∈ X.Z 2, z ^ 2 = 1 := by
  intro z hz
  have hZ2eq := X.Z_two_eq
  rw [hZ2eq, mem_conjSub] at hz
  have h : (X.τ ^ (-1 : ℤ) * z * X.τ) ^ 2 = 1 := by
    refine X.Z_zero_exp_two hc hmax hs hodd h5 hX hGT hreg _ ?_
    simpa using hz
  have hzτ : z = X.τ * (X.τ ^ (-1 : ℤ) * z * X.τ) * X.τ ^ (-1 : ℤ) := by group
  rw [hzτ, pow_two]
  rw [show X.τ * (X.τ ^ (-1 : ℤ) * z * X.τ) * X.τ ^ (-1 : ℤ) *
      (X.τ * (X.τ ^ (-1 : ℤ) * z * X.τ) * X.τ ^ (-1 : ℤ)) =
      X.τ * ((X.τ ^ (-1 : ℤ) * z * X.τ) * (X.τ ^ (-1 : ℤ) * z * X.τ)) *
        X.τ ^ (-1 : ℤ) by group]
  rw [show (X.τ ^ (-1 : ℤ) * z * X.τ) * (X.τ ^ (-1 : ℤ) * z * X.τ) =
      (X.τ ^ (-1 : ℤ) * z * X.τ) ^ 2 by rw [pow_two]]
  rw [h]
  group

private theorem Z_one_exp_two {m : ℕ} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∀ z ∈ X.Z 1, z ^ 2 = 1 := by
  intro z hz
  have hsup := X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg
  have hZ1eq := X.Z_one_eq_Z_zero_sup_Z_two hc hmax hs hodd h5 hX hGT hreg
  have hZ0_le_Z1 : X.Z 0 ≤ X.Z 1 := le_sup_left.trans hsup
  have hZ2_le_Z1 : X.Z 2 ≤ X.Z 1 := le_sup_right.trans hsup
  have hZ0cent : X.Z 0 ≤ Subgroup.centralizer (X.Z 2 : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (X.Z_commute 1 g (hZ0_le_Z1 hg) x (hZ2_le_Z1 hx)).symm
  have hprod : (↑(X.Z 0 ⊔ X.Z 2) : Set G) = (X.Z 0 : Set G) * (X.Z 2 : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 0) (X.Z 2)
      (hZ0cent.trans (Subgroup.centralizer_le_normalizer _))
  rw [hZ1eq] at hz
  have hz' : z ∈ (↑(X.Z 0 ⊔ X.Z 2) : Set G) := hz
  rw [hprod] at hz'
  obtain ⟨u, hu, v, hv, huv⟩ := hz'
  rw [← huv]
  have h0 := X.Z_zero_exp_two hc hmax hs hodd h5 hX hGT hreg u hu
  have h2 := X.Z_two_exp_two hc hmax hs hodd h5 hX hGT hreg v hv
  have hcomm : u * v = v * u := X.Z_commute 1 u (hZ0_le_Z1 hu) v (hZ2_le_Z1 hv)
  calc (u * v) ^ 2 = u * (v * u) * v := by rw [pow_two]; group
    _ = u * (u * v) * v := by rw [← hcomm]
    _ = u ^ 2 * v ^ 2 := by rw [pow_two, pow_two]; group
    _ = 1 := by rw [h0, h2]; group

private theorem sq_mem_Q_one_of_mem_S {x : G} (hx : x ∈ X.S) : x ^ 2 ∈ X.Q 1 := by
  have hS : X.S ≤ X.L 1 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hrel : (X.Q 1).relIndex X.S = 2 ^ X.n 1 := by
    rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_succ_edgeSylow 0
  exact X.sq_mem_Q_of_relIndex hS hrel x hx

private theorem commutator_mem_Z_one_of_mem_normalizer {w a : G} (hw : w ∈ X.Z 1)
    (ha : a ∈ Subgroup.normalizer (X.Z 1 : Set G)) : ⁅w, a⁆ ∈ X.Z 1 := by
  have haw : a * w * a⁻¹ ∈ X.Z 1 :=
    (Subgroup.mem_normalizer_iff.mp ha w).mp hw
  have h1 : ⁅w, a⁆ = w * (a * w * a⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [h1]
  exact (X.Z 1).mul_mem hw ((X.Z 1).inv_mem haw)

private def Z_one_commHom (a : G) (ha : a ∈ Subgroup.normalizer (X.Z 1 : Set G)) :
    ↥(X.Z 1) →* ↥(X.Z 1) where
  toFun w := ⟨⁅(w : G), a⁆, commutator_mem_Z_one_of_mem_normalizer X w.2 ha⟩
  map_one' := by
    apply Subtype.ext
    show ⁅(1 : G), a⁆ = 1
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    show ⁅((x * y : ↥(X.Z 1)) : G), a⁆ = ⁅(x : G), a⁆ * ⁅(y : G), a⁆
    rw [show ((x * y : ↥(X.Z 1)) : G) = (x : G) * (y : G) from rfl]
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hx1 : (x : G) * ⁅(y : G), a⁆ * (x : G)⁻¹ = ⁅(y : G), a⁆ := by
      have h := X.Z_commute 1 (x : G) x.2 ⁅(y : G), a⁆
        (commutator_mem_Z_one_of_mem_normalizer X y.2 ha)
      rw [h]
      group
    rw [hx1]
    exact X.Z_commute 1 ⁅(y : G), a⁆ (commutator_mem_Z_one_of_mem_normalizer X y.2 ha)
      ⁅(x : G), a⁆ (commutator_mem_Z_one_of_mem_normalizer X x.2 ha)

private theorem Z_one_commHom_ker (a : G)
    (ha : a ∈ Subgroup.normalizer (X.Z 1 : Set G)) :
    (X.Z_one_commHom a ha).ker =
      (X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (X.Z 1) := by
  ext w
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hw
    refine ⟨w.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst c
    have h1 : ⁅(w : G), a⁆ = 1 := Subtype.ext_iff.mp hw
    rw [commutatorElement_def] at h1
    have h2 : (w : G) * a = a * (w : G) := by
      calc (w : G) * a = ((w : G) * a * (w : G)⁻¹ * a⁻¹) * (a * (w : G)) := by group
        _ = a * (w : G) := by rw [h1, one_mul]
    exact h2.symm
  · rintro ⟨-, hw⟩
    rw [Subgroup.mem_centralizer_iff] at hw
    apply Subtype.ext
    show ⁅(w : G), a⁆ = 1
    rw [commutatorElement_def]
    rw [← hw a (Set.mem_singleton a)]
    group

private theorem Z_one_commHom_range_le_ker (a : G)
    (ha : a ∈ Subgroup.normalizer (X.Z 1 : Set G)) (ha2 : a * a ∈ X.Q 1)
    (hexp : ∀ z ∈ X.Z 1, z ^ 2 = 1) :
    (X.Z_one_commHom a ha).range ≤ (X.Z_one_commHom a ha).ker := by
  have hA2 : ∀ w ∈ X.Z 1, a * (a * w * a⁻¹) * a⁻¹ = w := by
    intro w hw
    have hcomm := X.Q_one_comm_Z_one (a * a) ha2 w hw
    calc a * (a * w * a⁻¹) * a⁻¹ = (a * a) * w * (a * a)⁻¹ := by group
      _ = w := by rw [hcomm]; group
  rintro _ ⟨w, rfl⟩
  rw [Z_one_commHom_ker]
  refine Subgroup.mem_subgroupOf.mpr
    ⟨commutator_mem_Z_one_of_mem_normalizer X w.2 ha, ?_⟩
  have hu_eq : ⁅(w : G), a⁆ = (w : G) * (a * (w : G) * a⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  have hAu : a * ⁅(w : G), a⁆ * a⁻¹ = (⁅(w : G), a⁆)⁻¹ := by
    rw [hu_eq]
    calc a * ((w : G) * (a * (w : G) * a⁻¹)⁻¹) * a⁻¹
        = (a * (w : G) * a⁻¹) * (a * (a * (w : G) * a⁻¹) * a⁻¹)⁻¹ := by group
      _ = (a * (w : G) * a⁻¹) * (w : G)⁻¹ := by rw [hA2 w w.2]
      _ = ((w : G) * (a * (w : G) * a⁻¹)⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv]
  have hexpw : ⁅(w : G), a⁆ ^ 2 = 1 :=
    hexp _ (commutator_mem_Z_one_of_mem_normalizer X w.2 ha)
  have hconj1 : ⁅⁅(w : G), a⁆, a⁆ = 1 := by
    rw [commutatorElement_def]
    calc ⁅(w : G), a⁆ * a * (⁅(w : G), a⁆)⁻¹ * a⁻¹
        = ⁅(w : G), a⁆ * (a * ⁅(w : G), a⁆ * a⁻¹)⁻¹ := by group
      _ = ⁅(w : G), a⁆ * ⁅(w : G), a⁆ := by rw [hAu]; group
      _ = 1 := by rw [← pow_two]; exact hexpw
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro c hcx
  rw [Set.mem_singleton_iff] at hcx
  subst c
  change a * ⁅(w : G), a⁆ = ⁅(w : G), a⁆ * a
  exact (commutatorElement_eq_one_iff_commute.mp hconj1).symm

private theorem Z_one_inf_centralizer_of_conj {a t : G} {j : ℤ} {Y W : Subgroup G}
    (hYeq : Y = X.Z j) (hYnorm : t ∈ Subgroup.normalizer (Y : Set G))
    (hconj : conjSub (t⁻¹ * a) (X.Z j) = W) (hdisj : W ⊓ Y = ⊥)
    (hYle : Y ≤ X.Z 1) (hWle : W ≤ X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G))
    (hcardY : Nat.card ↥Y = 2 ^ X.n 0) (hcardW : Nat.card ↥W = 2 ^ X.n 0)
    (hcardZ1 : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 0)) :
    X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G) = W := by
  have hdisj' : X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyC, hyY⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨-, hyCent⟩ := Subgroup.mem_inf.mp hyC
    have hyj : y ∈ X.Z j := hYeq ▸ hyY
    have hacomm : a * y = y * a :=
      Subgroup.mem_centralizer_iff.mp hyCent a (Set.mem_singleton a)
    have hkey : (t⁻¹ * a) * y * (t⁻¹ * a)⁻¹ = t⁻¹ * y * t := by
      rw [show (t⁻¹ * a) * y = t⁻¹ * (a * y) by group, hacomm]
      group
    have hWmem : (t⁻¹ * a) * y * (t⁻¹ * a)⁻¹ ∈ W := by
      rw [← hconj]
      exact mul_mem_conjSub (g := t⁻¹ * a) hyj
    have htinv : t⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
      (Subgroup.normalizer (Y : Set G)).inv_mem hYnorm
    have hYmem : t⁻¹ * y * t ∈ Y := by
      simpa using (Subgroup.mem_normalizer_iff.mp htinv y).mp hyY
    rw [hkey] at hWmem
    have hmem : t⁻¹ * y * t ∈ W ⊓ Y := Subgroup.mem_inf.mpr ⟨hWmem, hYmem⟩
    rw [hdisj] at hmem
    have h1 : t⁻¹ * y * t = 1 := by simpa using hmem
    calc y = t * (t⁻¹ * y * t) * t⁻¹ := by group
      _ = 1 := by rw [h1]; group
  exact X.Z_one_inf_centralizer_eq hWle hYle hdisj' hcardY hcardW hcardZ1

private theorem commutator_mem_of_centralizer {a : G}
    (ha : a ∈ Subgroup.normalizer (X.Z 1 : Set G)) (ha2 : a * a ∈ X.Q 1)
    (hexp : ∀ z ∈ X.Z 1, z ^ 2 = 1) {W : Subgroup G}
    (hW : X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G) = W) {z : G} (hz : z ∈ X.Z 1) :
    ⁅z, a⁆ ∈ W := by
  have hrange := X.Z_one_commHom_range_le_ker a ha ha2 hexp
  have hmem : (X.Z_one_commHom a ha) ⟨z, hz⟩ ∈
      (X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (X.Z 1) := by
    rw [← X.Z_one_commHom_ker a ha]
    exact hrange ⟨⟨z, hz⟩, rfl⟩
  rw [hW] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem Z_one_inf_centralizer_S {a : G} (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (ha : a ∈ X.S) (haQ : a ∉ X.Q 1) :
    X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G) = X.Z 0 := by
  have hsup := X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg
  have hdisj : X.Z 0 ⊓ X.Z 2 = ⊥ := X.Z_zero_inf_Z_two hc hmax hs hodd h5 hX hGT hreg
  have haS : a ∈ X.edgeSylow 0 := by rwa [X.edgeSylow_zero]
  have haG0 : a ∈ X.Gi 0 := ((X.isSylowTwoOf_edgeSylow 0).1 haS).1
  have haG1 : a ∈ X.Gi 1 := ((X.isSylowTwoOf_edgeSylow 0).1 haS).2
  have hfix0 : a • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp haG0
  have hfix1 : a • X.vert 1 = X.vert 1 := MulAction.mem_stabilizer_iff.mp haG1
  have hxS : a ∈ vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert (0 + 1)))
      (X.vert 0) := by
    rw [← X.edgeSylow_eq_vertexSylow_succ 0]
    exact haS
  have hxQ : a ∉ pCoreOf 2 (MulAction.stabilizer G (X.vert (0 + 1))) := by
    simpa using haQ
  have huniq := edgeSylow_fixes_unique_of_not_pcore X.hyp
    (X.hyp.isLocL2_oTwoPrime (X.vert (0 + 1))) (X.adj 0).symm hxS hxQ
  have hadj : Γ.Adj (X.vert (0 + 1)) (a • X.vert 2) := by
    have h' := (X.hyp.adj_smul a (X.vert 1) (X.vert 2)).2 (X.adj 1)
    rwa [hfix1] at h'
  have hne : a • X.vert 2 ≠ X.vert 2 := by
    intro h
    have hfix' : a • (a • X.vert 2) = a • X.vert 2 := congrArg (fun v => a • v) h
    have heq := huniq.unique ⟨(X.adj 0).symm, hfix0⟩ ⟨hadj, hfix'⟩
    exact (by norm_num : (0 : ℤ) ≠ 2) (X.vert_injective (heq.trans h))
  have hne02 : X.vert 0 ≠ X.vert 2 := by
    intro h
    exact (by norm_num : (0 : ℤ) ≠ 2) (X.vert_injective h)
  obtain ⟨t, ht, htT⟩ := X.edgeSylow_transitive_left 1 (X.vert 0) (a • X.vert 2)
    (X.adj 0).symm hne02 hadj hne
  have htT' : (t⁻¹ * a) • X.vert 2 = X.vert 0 := by
    rw [mul_smul, ← htT, ← mul_smul, inv_mul_cancel, one_smul]
  have hconj : conjSub (t⁻¹ * a) (X.Z 2) = X.Z 0 := X.Z_conj htT'
  have htG2 : t ∈ X.Gi 2 := ((X.isSylowTwoOf_edgeSylow 1).1 ht).2
  have hYnorm : t ∈ Subgroup.normalizer (X.Z 2 : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 2 t htG2)
  have hZ2leZ1 : X.Z 2 ≤ X.Z 1 := le_sup_right.trans hsup
  have hZ0leC : X.Z 0 ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hzc
    rw [Set.mem_singleton_iff] at hzc
    subst c
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (X.Z_zero_le_centerOf_S hc hmax hs hodd h5 hX hGT hx)).2 a ha
  have hWle : X.Z 0 ≤ X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G) :=
    le_inf (le_sup_left.trans hsup) hZ0leC
  exact X.Z_one_inf_centralizer_of_conj (a := a) (t := t) (j := 2) (Y := X.Z 2)
    (W := X.Z 0) rfl hYnorm hconj hdisj hZ2leZ1 hWle
    (X.card_Z_two hc hmax hs hodd h5 hX hGT hreg)
    (X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg)
    (X.card_Z_one_sq hc hmax hs hodd h5 hX hGT hreg)

private theorem Z_one_inf_centralizer_edgeSylow_one {a : G}
    (hc : CharTwoStab (V := V) (G := G)) (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (ha : a ∈ X.edgeSylow 1)
    (haQ : a ∉ X.Q 1) :
    X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G) = X.Z 2 := by
  have hsup := X.Z_zero_sup_Z_two_le hc hmax hs hodd h5 hX hGT hreg
  have hdisj : X.Z 2 ⊓ X.Z 0 = ⊥ := by
    rw [inf_comm]
    exact X.Z_zero_inf_Z_two hc hmax hs hodd h5 hX hGT hreg
  have haG1 : a ∈ X.Gi 1 := ((X.isSylowTwoOf_edgeSylow 1).1 ha).1
  have haG2 : a ∈ X.Gi 2 := ((X.isSylowTwoOf_edgeSylow 1).1 ha).2
  have hfix1 : a • X.vert 1 = X.vert 1 := MulAction.mem_stabilizer_iff.mp haG1
  have hfix2 : a • X.vert 2 = X.vert 2 := MulAction.mem_stabilizer_iff.mp haG2
  have hxS : a ∈ vertexSylowMap X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert 1)) (X.vert 2) := by
    have h := ha
    rw [X.edgeSylow_eq_vertexSylow 1] at h
    simpa using h
  have hxQ : a ∉ pCoreOf 2 (MulAction.stabilizer G (X.vert 1)) := by
    simpa using haQ
  have huniq := edgeSylow_fixes_unique_of_not_pcore X.hyp
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)) (X.adj 1) hxS hxQ
  have hadj : Γ.Adj (X.vert 1) (a • X.vert 0) := by
    have h' := (X.hyp.adj_smul a (X.vert 1) (X.vert 0)).2 (X.adj 0).symm
    rwa [hfix1] at h'
  have hne : a • X.vert 0 ≠ X.vert 0 := by
    intro h
    have hfix' : a • (a • X.vert 0) = a • X.vert 0 := congrArg (fun v => a • v) h
    have heq := huniq.unique ⟨X.adj 1, hfix2⟩ ⟨hadj, hfix'⟩
    exact (by norm_num : (2 : ℤ) ≠ 0) (X.vert_injective (heq.trans h))
  have hne02 : X.vert 2 ≠ X.vert 0 := by
    intro h
    exact (by norm_num : (2 : ℤ) ≠ 0) (X.vert_injective h)
  obtain ⟨t, ht, htT⟩ := X.edgeSylow_transitive 0 (X.vert 2) (a • X.vert 0)
    (X.adj 1) hne02 hadj hne
  have htT' : (t⁻¹ * a) • X.vert 0 = X.vert 2 := by
    rw [mul_smul, ← htT, ← mul_smul, inv_mul_cancel, one_smul]
  have hconj : conjSub (t⁻¹ * a) (X.Z 0) = X.Z 2 := X.Z_conj htT'
  have htG0 : t ∈ X.Gi 0 := ((X.isSylowTwoOf_edgeSylow 0).1 ht).1
  have hYnorm : t ∈ Subgroup.normalizer (X.Z 0 : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 0 t htG0)
  have hZ0leZ1 : X.Z 0 ≤ X.Z 1 := le_sup_left.trans hsup
  have hZ2leC : X.Z 2 ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hzc
    rw [Set.mem_singleton_iff] at hzc
    subst c
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp
        (X.Z_two_le_centerOf_edgeSylow_one hc hmax hs hodd h5 hX hGT hx)).2 a ha
  have hWle : X.Z 2 ≤ X.Z 1 ⊓ Subgroup.centralizer ({a} : Set G) :=
    le_inf (le_sup_right.trans hsup) hZ2leC
  exact X.Z_one_inf_centralizer_of_conj (a := a) (t := t) (j := 0) (Y := X.Z 0)
    (W := X.Z 2) rfl hYnorm hconj hdisj hZ0leZ1 hWle
    (X.card_Z_zero hc hmax hs hodd h5 hX hGT hreg)
    (X.card_Z_two hc hmax hs hodd h5 hX hGT hreg)
    (X.card_Z_one_sq hc hmax hs hodd h5 hX hGT hreg)

theorem commutator_Z_one_S_le (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.Z 1, X.S⁆ ≤ X.Z 0 := by
  refine Subgroup.commutator_le.mpr ?_
  intro z hz a ha
  by_cases haQ : a ∈ X.Q 1
  · have hcomm : ⁅z, a⁆ = 1 := by
      rw [commutatorElement_def, ← X.Q_one_comm_Z_one a haQ z hz]
      group
    rw [hcomm]
    exact (X.Z 0).one_mem
  · have haN : a ∈ Subgroup.normalizer (X.Z 1 : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (X.Z_normal 1 a (((X.isSylowTwoOf_edgeSylow 0).1 (by rwa [X.edgeSylow_zero])).2))
    have ha2 : a * a ∈ X.Q 1 := by
      simpa [pow_two] using X.sq_mem_Q_one_of_mem_S ha
    exact X.commutator_mem_of_centralizer haN ha2
      (fun y hy => X.Z_one_exp_two hc hmax hs hodd h5 hX hGT hreg y hy)
      (X.Z_one_inf_centralizer_S hc hmax hs hodd h5 hX hGT hreg ha haQ) hz

theorem commutator_Z_one_edgeSylow_le (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.Z 1, X.edgeSylow 1⁆ ≤ X.Z 2 := by
  refine Subgroup.commutator_le.mpr ?_
  intro z hz a ha
  by_cases haQ : a ∈ X.Q 1
  · have hcomm : ⁅z, a⁆ = 1 := by
      rw [commutatorElement_def, ← X.Q_one_comm_Z_one a haQ z hz]
      group
    rw [hcomm]
    exact (X.Z 2).one_mem
  · have haN : a ∈ Subgroup.normalizer (X.Z 1 : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (X.Z_normal 1 a (((X.isSylowTwoOf_edgeSylow 1).1 ha).1))
    have ha2 : a * a ∈ X.Q 1 := by
      rw [← pow_two]
      exact X.sq_mem_Q_of_relIndex (S := X.edgeSylow 1) (j := 1)
        (X.isSylowTwoOf_edgeSylow_L 1).1 (X.relIndex_Q_edgeSylow 1) a ha
    exact X.commutator_mem_of_centralizer haN ha2
      (fun y hy => X.Z_one_exp_two hc hmax hs hodd h5 hX hGT hreg y hy)
      (X.Z_one_inf_centralizer_edgeSylow_one hc hmax hs hodd h5 hX hGT hreg ha haQ) hz

private theorem isElemSec_bot_Z_one_subgroupOf (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    CFSG.GH74.QTGen4.DSGen4.IsElemSec (⊥ : Subgroup ↥(X.L 1))
      ((X.Z 1).subgroupOf (X.L 1)) := by
  have hexp := fun z hz => X.Z_one_exp_two hc hmax hs hodd h5 hX hGT hreg z hz
  refine ⟨bot_le, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxZ : (x : G) ∈ X.Z 1 := Subgroup.mem_subgroupOf.mp hx
    have hyZ : (y : G) ∈ X.Z 1 := Subgroup.mem_subgroupOf.mp hy
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change ⁅(x : G), (y : G)⁆ = 1
    rw [commutatorElement_def, X.Z_commute 1 (x : G) hxZ (y : G) hyZ]
    group
  · intro x hx
    have hxZ : (x : G) ∈ X.Z 1 := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    exact hexp (x : G) hxZ

private theorem exists_commutator_L_one_Z_one_notMem (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∃ l ∈ (⊤ : Subgroup ↥(X.L 1)), ∃ v ∈ (X.Z 1).subgroupOf (X.L 1),
      ⁅l, v⁆ ∉ (⊥ : Subgroup ↥(X.L 1)) := by
  by_contra h
  push Not at h
  have hZ1L : X.Z 1 ≤ X.L 1 :=
    (X.Z_le_Q 1).trans (X.hyp.isLocL2_oTwoPrime (X.vert 1)).oTwo_le
  have hcent : X.L 1 ≤ Subgroup.centralizer (X.Z 1 : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzL : z ∈ X.L 1 := hZ1L hz
    have h1 : ⁅(⟨l, hl⟩ : ↥(X.L 1)), (⟨z, hzL⟩ : ↥(X.L 1))⁆ = 1 := by
      simpa using h ⟨l, hl⟩ (Subgroup.mem_top _) ⟨z, hzL⟩
        (Subgroup.mem_subgroupOf.mpr hz)
    have h2 : ⁅l, z⁆ = 1 := by
      have hcoe := map_commutatorElement (f := Subgroup.subtype (X.L 1))
        (g₁ := (⟨l, hl⟩ : ↥(X.L 1))) (g₂ := (⟨z, hzL⟩ : ↥(X.L 1)))
      rw [h1] at hcoe
      simpa using hcoe.symm
    exact (commutatorElement_eq_one_iff_commute.mp h2).symm
  have hLQ : X.L 1 ≤ X.Q 1 := by
    rw [← X.L_one_inf_centralizer_Z_one hc hmax hs hodd h5 hX hGT hreg]
    exact le_inf le_rfl hcent
  have hSleL : X.S ≤ X.L 1 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hSleQ : X.S ≤ X.Q 1 := hSleL.trans hLQ
  have hrel : (X.Q 1).relIndex X.S = 2 ^ X.n 1 := by
    rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_succ_edgeSylow 0
  have hone : (X.Q 1).relIndex X.S = 1 := Subgroup.relIndex_eq_one.mpr hSleQ
  rw [hone] at hrel
  have h2 : 2 ≤ 2 ^ X.n 1 := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ X.n 1 := Nat.pow_le_pow_right (by norm_num) (X.hyp.valency (X.vert 1)).1
  omega

theorem n_one_le_n_zero (hc : CharTwoStab (V := V) (G := G))
    (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    X.n 1 ≤ X.n 0 := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hZ1L : X.Z 1 ≤ X.L 1 :=
    (X.Z_le_Q 1).trans (X.hyp.isLocL2_oTwoPrime (X.vert 1)).oTwo_le
  let H : Subgroup G := X.L 1
  let V' : Subgroup ↥H := (X.Z 1).subgroupOf H
  haveI : Finite ↥H := finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hquot : IsL2Quot (X.n 1) (oTwoQuot ↥(⊤ : Subgroup ↥H)) := by
    obtain ⟨e⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr Subgroup.topEquiv).trans e⟩
  have hsec : CFSG.GH74.QTGen4.DSGen4.IsElemSec (⊥ : Subgroup ↥H) V' :=
    X.isElemSec_bot_Z_one_subgroupOf hc hmax hs hodd h5 hX hGT hreg
  have hL : (⊤ : Subgroup ↥H) ≤ Subgroup.normalizer (V' : Set ↥H) ⊓
      Subgroup.normalizer ((⊥ : Subgroup ↥H) : Set ↥H) := by
    refine le_inf ?_ ?_
    · exact le_normalizer_subgroupOf_of_le_normalizer hZ1L (fun x hx =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 x (X.L_le_Gi 1 hx)))
    · rw [show Subgroup.normalizer ((⊥ : Subgroup ↥H) : Set ↥H) = ⊤ from
        Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  have hQ : ∀ p ∈ pCoreOf 2 (⊤ : Subgroup ↥H), ∀ v ∈ V', ⁅p, v⁆ ∈ (⊥ : Subgroup ↥H) := by
    intro p hp v hv
    have hQtop : pCoreOf 2 (⊤ : Subgroup ↥H) = (X.Q 1).subgroupOf H := by
      rw [CFSG.Quasithin.F53Push.pCoreOf_top_eq, ← CFSG.openPCoreOf_subgroupOf 2 H,
        (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq]
    rw [hQtop] at hp
    have hpQ : (p : G) ∈ X.Q 1 := Subgroup.mem_subgroupOf.mp hp
    have hvZ : (v : G) ∈ X.Z 1 := Subgroup.mem_subgroupOf.mp hv
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change ⁅(p : G), (v : G)⁆ = 1
    rw [commutatorElement_def, X.Q_one_comm_Z_one (p : G) hpQ (v : G) hvZ]
    group
  have hnt : ∃ l ∈ (⊤ : Subgroup ↥H), ∃ v ∈ V', ⁅l, v⁆ ∉ (⊥ : Subgroup ↥H) :=
    X.exists_commutator_L_one_Z_one_notMem hc hmax hs hodd h5 hX hGT hreg
  have hle := two_pow_le_relIndex_of_nontrivial (G := ↥H) (V := V') (Z := ⊥) (L := ⊤)
    (m := X.n 1) (X.hyp.valency (X.vert 1)).1 hquot hsec hL hQ hnt
  rw [Subgroup.relIndex_bot_left] at hle
  have hcardV : Nat.card ↥V' = 2 ^ (2 * X.n 0) := by
    rw [← X.card_Z_one_sq hc hmax hs hodd h5 hX hGT hreg]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ1L).toEquiv
  rw [hcardV] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  omega

theorem false_of_n_one_two (hc : CharTwoStab (V := V) (G := G))
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) (hmax : X.n 0 = 2 ∨ X.n 1 = 2)
    (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) : False := by
  have := X.n_one_le_n_zero hc (hmax.imp Eq.ge Eq.ge) hs hodd h5 hX hGT
  omega

end Setup

end CFSG.Quasithin.St84
