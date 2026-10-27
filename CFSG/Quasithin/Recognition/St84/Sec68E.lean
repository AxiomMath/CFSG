module

public import CFSG.Quasithin.Recognition.St84.Sec68D
import CFSG.Quasithin.Recognition.St84.Gen.Sec6TorusCent
import CFSG.Quasithin.Recognition.St84.Gen.MixedCentralZData

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

private theorem le_normalizer_relCent {E Z A : Subgroup G}
    (hZ : E ≤ Subgroup.normalizer (Z : Set G)) (hA : E ≤ Subgroup.normalizer (A : Set G)) :
    E ≤ Subgroup.normalizer (relCent E Z A : Set G) := by
  have hmem : ∀ g, g ∈ relCent E Z A ↔ g ∈ E ∧ ∀ a ∈ A, ⁅g, a⁆ ∈ Z :=
    fun g => mem_relCent hZ
  have hconjC : ∀ l ∈ E, ∀ c ∈ relCent E Z A, l * c * l⁻¹ ∈ relCent E Z A := by
    intro l hl c hc
    rw [hmem] at hc ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hl hc.1) (Subgroup.inv_mem _ hl), ?_⟩
    intro a ha
    have ha' : l⁻¹ * a * l ∈ A := (Subgroup.mem_normalizer_iff''.mp (hA hl) a).mp ha
    have h1 : ⁅c, l⁻¹ * a * l⁆ ∈ Z := hc.2 _ ha'
    have h2 : l * ⁅c, l⁻¹ * a * l⁆ * l⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hZ hl) _).mp h1
    have heq : l * ⁅c, l⁻¹ * a * l⁆ * l⁻¹ = ⁅l * c * l⁻¹, a⁆ := by
      rw [conjugate_commutatorElement]
      congr 1 <;> group
    rwa [heq] at h2
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => hconjC l hl c hc, fun hc => by
    have h := hconjC l⁻¹ (Subgroup.inv_mem _ hl) (l * c * l⁻¹) hc
    have hgc : l⁻¹ * (l * c * l⁻¹) * (l⁻¹)⁻¹ = c := by group
    rwa [hgc] at h⟩

theorem commutator_A_L_zero_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.A, X.L 0⁆ ≤ X.V0 := by
  have hV0norm := (X.L_le_Gi 0).trans (X.Gi_zero_le_normalizer_V0 hc hn0 hs hodd h5 hX hGT hreg)
  have hAnorm : X.L 0 ≤ Subgroup.normalizer (X.A : Set G) :=
    (X.L_le_Gi 0).trans (X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg)
  let C : Subgroup G := relCent (X.L 0) (X.V0) (X.A)
  have hmem : ∀ g, g ∈ C ↔ g ∈ X.L 0 ∧ ∀ a ∈ X.A, ⁅g, a⁆ ∈ X.V0 :=
    fun g => mem_relCent hV0norm
  have hAG0 : X.A ≤ X.Gi 0 := (inf_le_left : X.A ≤ X.Q 1).trans
    ((X.Q_le_Gi_adj 1).trans inf_le_left)
  have hAL0 : X.A ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup
      (IsPGroup.to_le (pCoreOf_isPGroup' (X.Gi 1)) inf_le_left) hAG0
  have hX0 : X.X0 ≤ C := by
    intro x hx
    rw [hmem]
    refine ⟨?_, ?_⟩
    · rw [X.L_zero_eq_Z_four_sup hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
      exact Subgroup.mem_sup_left hx
    · intro a ha
      have h1 : ⁅a, x⁆ ∈ X.V0 :=
        (Subgroup.commutator_le.mp (X.commutator_A_X0_le hc hn0 hs hodd h5 hX hGT hreg))
          a ha x hx
      have h2 := X.V0.inv_mem h1
      rwa [commutatorElement_inv] at h2
  have hK0 : X.Ki 0 ≤ C := by
    intro k hk
    rw [hmem]
    refine ⟨hk.2, ?_⟩
    intro a ha
    have h1 : ⁅a, k⁆ ∈ X.V0 :=
      X.Ki_zero_centralizes_mod hc hn0 hs hodd h5 hX hGT hreg k hk a ha
    have h2 := X.V0.inv_mem h1
    rwa [commutatorElement_inv] at h2
  have hA : X.A ≤ C := by
    intro a ha
    rw [hmem]
    refine ⟨hAL0 ha, ?_⟩
    intro b hb
    have hcomm : Commute a b :=
      (CFSG.Quasithin.F7.isElemAbelian_comm
        (X.isElemAbelian_A hc hn0 hs hodd h5 hX hGT hreg)) ha hb
    rw [hcomm.commutator_eq]
    exact X.V0.one_mem
  have hCnorm : X.L 0 ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_relCent hV0norm hAnorm
  have hcomm : ⁅X.Q 0, X.Ki 0⁆ ≤ C :=
    (Subgroup.commutator_mono_right hK0).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0)) (X.Q_le_Gi 0)).trans hCnorm))
  have hQ0C : X.Q 0 ≤ C := by
    rw [X.Q_eq_commutator_sup hc hn0 hs hodd h5 hX hGT hreg]
    exact sup_le hcomm hA
  have hL0C : X.L 0 ≤ C := by
    rw [X.L_zero_eq_Z_four_sup hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    exact sup_le hX0 hQ0C
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro l hl a ha
  exact ((hmem l).mp (hL0C hl)).2 a ha

private theorem Z_neg_four_le_Gi_zero (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z (-4) ≤ X.Gi 0 := by
  have h := X.Z_zero_le_Gi_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg
  have hZ : X.Z (-4) = conjSub (X.τ ^ (-2 : ℤ)) (X.Z 0) := by
    rw [← X.Z_add (-2) 0]; norm_num
  rw [hZ]
  calc conjSub (X.τ ^ (-2 : ℤ)) (X.Z 0) ≤ conjSub (X.τ ^ (-2 : ℤ)) (X.Gi 4) :=
        conjSub_mono _ (h.trans inf_le_left)
    _ = X.Gi 0 := by simpa using (X.Gi_add (-2) 4).symm

private theorem Q_one_eq_Z_four_sup (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Q 1 = X.Z 4 ⊔ (X.Q 1 ⊓ X.Q 0) := by
  have hZ4Q1 : X.Z 4 ≤ X.Q 1 :=
    X.Z_le_Q_of_le_Gi 4 0 1 (X.Z_four_le_Gi_zero
          hc (Or.inl hn0) hs hodd h5 hX hGT hreg)
      (Or.inr ⟨by norm_num, by norm_num⟩)
  have hQ1S : X.Q 1 ≤ X.Z 4 ⊔ X.Q 0 := by
    rw [X.Z_four_sup_Q_zero hc (Or.inl hn0) hs hodd h5 hX hGT hreg,
      ← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0
  have hZ4N : X.Z 4 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.Z_four_le_Gi_zero
          hc (Or.inl hn0) hs hodd h5 hX hGT hreg).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  exact CFSG.Quasithin.A3.eq_sup_inf_of_le_sup hZ4N hZ4Q1 hQ1S

private theorem Q_neg_one_eq_Z_neg_four_sup (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Q (-1) = X.Z (-4) ⊔ (X.Q (-1) ⊓ X.Q 0) := by
  have hZQ : X.Z (-4) ≤ X.Q (-1) :=
    X.Z_le_Q_of_le_Gi (-4) 0 (-1)
      (X.Z_neg_four_le_Gi_zero hc hn0 hs hodd h5 hX hGT hreg)
      (Or.inr ⟨by norm_num, by norm_num⟩)
  have hQS : X.Q (-1) ≤ X.Z (-4) ⊔ X.Q 0 := by
    rw [X.Z_neg_four_sup_Q_zero hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    exact X.Q_le_edgeSylow_left (-1)
  have hZN : X.Z (-4) ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.Z_neg_four_le_Gi_zero hc hn0 hs hodd h5 hX hGT hreg).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  exact CFSG.Quasithin.A3.eq_sup_inf_of_le_sup hZN hZQ hQS

private theorem Z_le_centralizer_QT (i : ℤ) :
    X.Z i ≤ Subgroup.centralizer (X.QT : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i hz)).2)
    q (X.QT_le_Q i hq)

theorem commutator_QT_Q_zero_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.QT, X.Q 0⁆ ≤ X.V0 := by
  have hQTA : X.QT ≤ X.A := le_inf (X.QT_le_Q 1) (X.QT_le_Q (-1))
  have hQ0L : X.Q 0 ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0)) (X.Q_le_Gi 0)
  exact (Subgroup.commutator_mono hQTA hQ0L).trans
    (X.commutator_A_L_zero_le hc hn0 hs hodd h5 hX hGT hreg)

private theorem conjSub_tau_commutator_QT_Q (i : ℤ) :
    conjSub X.τ ⁅X.QT, X.Q i⁆ = ⁅X.QT, X.Q (i + 2)⁆ := by
  rw [← conjSub_commutator, X.conjSub_tau_QT,
    show conjSub X.τ (X.Q i) = X.Q (i + 2) by simpa using (X.Q_add 1 i).symm]

theorem commutator_QT_Q_two_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.QT, X.Q 2⁆ ≤ X.V2 :=
  (X.conjSub_tau_commutator_QT_Q 0).symm.le.trans
    (conjSub_mono _ (X.commutator_QT_Q_zero_le hc hn0 hs hodd h5 hX hGT hreg))

theorem commutator_QT_Q_one_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.QT, X.Q 1⁆ ≤ X.Z 1 := by
  have hV0norm := (X.L_le_Gi 0).trans (X.Gi_zero_le_normalizer_V0 hc hn0 hs hodd h5 hX hGT hreg)
  have hQ1L : X.Q 1 ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) ((X.Q_le_Gi_adj 1).trans inf_le_left)
  have hQmL : X.Q (-1) ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (-1)))
      ((X.Q_le_Gi_adj (-1)).trans inf_le_right)
  have hQ1N : X.Q 1 ≤ Subgroup.normalizer (X.V0 : Set G) := hQ1L.trans hV0norm
  have hQmN : X.Q (-1) ≤ Subgroup.normalizer (X.V0 : Set G) := hQmL.trans hV0norm
  have hV0 : ⁅X.QT, X.Q 1⁆ ≤ X.V0 := by
    have hZ4Q1 : X.Z 4 ≤ X.Q 1 :=
      X.Z_le_Q_of_le_Gi 4 0 1 (X.Z_four_le_Gi_zero
          hc (Or.inl hn0) hs hodd h5 hX hGT hreg)
        (Or.inr ⟨by norm_num, by norm_num⟩)
    have hZ4 : X.Z 4 ≤ relCent (X.Q 1) (X.V0) (X.QT) := by
      intro z hz
      refine (mem_relCent hQ1N).mpr ⟨hZ4Q1 hz, fun b hb => ?_⟩
      have hcomm : z * b = b * z :=
        (Subgroup.mem_centralizer_iff.mp (X.Z_le_centralizer_QT 4 hz) b hb).symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact X.V0.one_mem
    have hQ10 : X.Q 1 ⊓ X.Q 0 ≤ relCent (X.Q 1) (X.V0) (X.QT) := by
      intro k hk
      refine (mem_relCent hQ1N).mpr ⟨(Subgroup.mem_inf.mp hk).1, fun b hb => ?_⟩
      have h1 : ⁅b, k⁆ ∈ X.V0 :=
        (Subgroup.commutator_le.mp (X.commutator_QT_Q_zero_le hc hn0 hs hodd h5 hX hGT hreg))
          b hb k (Subgroup.mem_inf.mp hk).2
      have h2 := X.V0.inv_mem h1
      rwa [commutatorElement_inv] at h2
    have hQ1C : X.Q 1 ≤ relCent (X.Q 1) (X.V0) (X.QT) := by
      conv_lhs => rw [X.Q_one_eq_Z_four_sup hc hn0 hs hodd h5 hX hGT hreg]
      exact sup_le hZ4 hQ10
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have h1 : ⁅x, a⁆ ∈ X.V0 := ((mem_relCent hQ1N).mp (hQ1C hx)).2 a ha
    have h2 := X.V0.inv_mem h1
    rwa [commutatorElement_inv] at h2
  have hm : ⁅X.QT, X.Q (-1)⁆ ≤ X.V0 := by
    have hZm4 : X.Z (-4) ≤ relCent (X.Q (-1)) (X.V0) (X.QT) := by
      intro z hz
      refine (mem_relCent hQmN).mpr ⟨X.Z_le_Q_of_le_Gi (-4) 0 (-1)
        (X.Z_neg_four_le_Gi_zero hc hn0 hs hodd h5 hX hGT hreg)
        (Or.inr ⟨by norm_num, by norm_num⟩) hz, fun b hb => ?_⟩
      have hcomm : z * b = b * z :=
        (Subgroup.mem_centralizer_iff.mp (X.Z_le_centralizer_QT (-4) hz) b hb).symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact X.V0.one_mem
    have hQ10 : X.Q (-1) ⊓ X.Q 0 ≤ relCent (X.Q (-1)) (X.V0) (X.QT) := by
      intro k hk
      refine (mem_relCent hQmN).mpr ⟨(Subgroup.mem_inf.mp hk).1, fun b hb => ?_⟩
      have h1 : ⁅b, k⁆ ∈ X.V0 :=
        (Subgroup.commutator_le.mp (X.commutator_QT_Q_zero_le hc hn0 hs hodd h5 hX hGT hreg))
          b hb k (Subgroup.mem_inf.mp hk).2
      have h2 := X.V0.inv_mem h1
      rwa [commutatorElement_inv] at h2
    have hQC : X.Q (-1) ≤ relCent (X.Q (-1)) (X.V0) (X.QT) := by
      conv_lhs => rw [X.Q_neg_one_eq_Z_neg_four_sup hc hn0 hs hodd h5 hX hGT hreg]
      exact sup_le hZm4 hQ10
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have h1 : ⁅x, a⁆ ∈ X.V0 := ((mem_relCent hQmN).mp (hQC hx)).2 a ha
    have h2 := X.V0.inv_mem h1
    rwa [commutatorElement_inv] at h2
  have hV2 : ⁅X.QT, X.Q 1⁆ ≤ X.V2 := by
    have hQ1 : X.Q 1 = conjSub X.τ (X.Q (-1)) := by
      simpa using (X.Q_add 1 (-1))
    calc ⁅X.QT, X.Q 1⁆ = ⁅X.QT, conjSub X.τ (X.Q (-1))⁆ := by rw [hQ1]
      _ = ⁅conjSub X.τ X.QT, conjSub X.τ (X.Q (-1))⁆ := by rw [X.conjSub_tau_QT]
      _ = conjSub X.τ ⁅X.QT, X.Q (-1)⁆ :=
          conjSub_commutator X.τ X.QT (X.Q (-1))
      _ ≤ conjSub X.τ X.V0 := conjSub_mono _ hm
      _ = X.V2 := rfl
  exact (le_inf hV0 hV2).trans (X.V0_inf_V2_le hc hn0 hs hodd h5 hX
    hGT hreg)

@[expose] def Kst : Subgroup G :=
  X.K ⊓ ⨅ (a : V) (_ : a ∈ Γ.neighborSet (X.vert 1)), MulAction.stabilizer G a

private theorem Gi_le_normalizer_Z (i : ℤ) : X.Gi i ≤ Subgroup.normalizer (X.Z i : Set G) :=
  fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal i g hg)

private theorem mem_Kst {k : G} :
    k ∈ X.Kst ↔ k ∈ X.K ∧ ∀ w : V, Γ.Adj (X.vert 1) w → k • w = w := by
  simp only [Setup.Kst, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff,
    SimpleGraph.mem_neighborSet]

private theorem Kst_eq_inf_fixSet :
    X.Kst = X.K ⊓ fixSet G (Γ.neighborSet (X.vert 1)) := by
  ext k
  rw [X.mem_Kst, Subgroup.mem_inf, Fan86.mem_fixSet]
  simp only [SimpleGraph.mem_neighborSet]

private theorem L_Kst_le_Q (j : ℤ)
    (hfix : ∀ k ∈ X.Kst, ∀ w : V, Γ.Adj (X.vert j) w → k • w = w) :
    ⁅X.L j, X.Kst⁆ ≤ X.Q j := by
  rw [Subgroup.commutator_le]
  intro l hl k hk
  have hinv := (X.Q j).inv_mem (X.commutator_mem_Q_of_fixes_neighbors j
    ((inf_le_left.trans (X.K_le_Gi j)) hk) (hfix k hk) l hl)
  rwa [commutatorElement_inv] at hinv

theorem Kst_ne_bot (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Kst ≠ ⊥ := by
  have hK : ∀ a ∈ X.K, ∀ b ∈ X.K, a * b = b * a :=
    fun a ha b hb => X.mul_comm_of_mem_K hc hn0 hs hodd h5 hX hGT ha hb
  have hcard := X.card_K_eq_mul hK 1
  rw [X.n_one_eq_n_zero hc hn0 hs hodd h5 hX hGT, ← X.Kst_eq_inf_fixSet,
    X.card_K_eq_sq hc hn0 hs hodd h5 hX hGT, pow_two] at hcard
  have hpos : 0 < 2 ^ X.n 0 - 1 := by
    have hnpos : 0 < X.n 0 := lt_of_lt_of_le Nat.zero_lt_two hn0
    exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hnpos))
  have hKst : Nat.card ↥X.Kst = 2 ^ X.n 0 - 1 := Nat.eq_of_mul_eq_mul_left hpos hcard.symm
  have hthree : 3 ≤ Nat.card ↥X.Kst := by
    rw [hKst]
    have hfour : 4 ≤ 2 ^ X.n 0 := by
      simpa using Nat.pow_le_pow_right Nat.zero_lt_two hn0
    rw [show 3 = 4 - 1 by decide]
    exact Nat.sub_le_sub_right hfour 1
  intro hbot
  have h1 : Nat.card ↥X.Kst = 1 := by rw [hbot, Subgroup.card_bot]
  rw [h1] at hthree
  exact absurd hthree (by decide)

theorem commutator_commutator_QT_Q_two_Kst_le (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅⁅X.QT, X.Q 2⁆, X.Kst⁆ ≤ X.Z 1 := by
  have hKstK : X.Kst ≤ X.K := inf_le_left
  have hKstG1 : X.Kst ≤ X.Gi 1 := hKstK.trans (X.K_le_Gi 1)
  have hL1K := X.L_Kst_le_Q 1 fun k hk => (X.mem_Kst.mp hk).2
  have hQTcomm : X.QT ≤ Subgroup.centralizer (X.K : Set G) := by
    rw [X.QT_eq_inf_centralizer_K hc hn0 hs hodd h5 hX hGT hreg]
    exact inf_le_right
  have hKQT : ⁅X.Kst, X.QT⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ((inf_le_left : X.Kst ≤ X.K).trans
      (Subgroup.le_centralizer_iff.mp hQTcomm))
  have hQTZ : ⁅X.QT, X.Q 1⁆ ≤ X.Z 1 :=
    X.commutator_QT_Q_one_le hc hn0 hs hodd h5 hX hGT hreg
  have h1amb : ⁅⁅X.L 1, X.Kst⁆, X.QT⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono_left hL1K).trans
      ((Subgroup.commutator_comm (X.Q 1) (X.QT)).le.trans hQTZ)
  have h2amb : ⁅⁅X.Kst, X.QT⁆, X.L 1⁆ ≤ X.Z 1 := by
    rw [hKQT]
    simp
  have h3amb : ⁅⁅X.QT, X.L 1⁆, X.Kst⁆ ≤ X.Z 1 :=
    CFSG.Quasithin.S153D.commutator_commutator_le_of_rotate
      (((X.QT_le_Q 1).trans (X.Q_le_Gi 1)).trans (X.Gi_le_normalizer_Z 1))
      ((X.L_le_Gi 1).trans (X.Gi_le_normalizer_Z 1))
      (hKstG1.trans (X.Gi_le_normalizer_Z 1)) h1amb h2amb
  have hQ2L1 : X.Q 2 ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 2))
      ((X.Q_le_Gi_adj 2).trans inf_le_left)
  have hm : ⁅X.QT, X.Q 2⁆ ≤ ⁅X.QT, X.L 1⁆ :=
    Subgroup.commutator_mono_right (H := X.QT) (K₁ := X.Q 2) (K₂ := X.L 1) hQ2L1
  exact (Subgroup.commutator_mono hm le_rfl).trans h3amb

structure Ctx (X : Setup Γ G) (s : ℕ) : Prop where
  hc : CharTwoStab (V := V) (G := G)
  hn0 : 2 ≤ X.n 0
  hs : IsSingularity Γ G s
  hodd : Odd s
  h5 : 5 ≤ s
  hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s
  hGT : Even (Nat.card X.GT)

variable {X : Setup Γ G} {s : ℕ}

private theorem Ztau_one_eq (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Ztau 1 = X.Z 2 ⊔ X.QT := by
  have h1 : X.Ztau 1 = conjSub X.τ X.ZM := by
    unfold Setup.Ztau
    simp
  rw [h1, X.ZM_eq_Z_zero_sup_QT h.hc (Or.inl h.hn0) h.hs h.hodd h.h5
    h.hX h.hGT hreg]
  rw [conjSub_sup, X.conjSub_tau_QT, show conjSub X.τ (X.Z 0) = X.Z 2 by
    simpa using (X.Z_add 1 0).symm]

private theorem E_two_eq_V2_sup_QT (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.E X.QT 2 = X.V2 ⊔ X.QT := by
  rw [X.E_two_eq, X.E_eq_V0_sup_QT h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg,
    conjSub_sup, X.conjSub_tau_QT]
  rfl

private theorem V2_inf_QT (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.V2 ⊓ X.QT = ⊥ := by
  have h' := X.V0_inf_QT h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have h2 := congrArg (conjSub X.τ) h'
  rw [conjSub_inf, conjSub_bot, X.conjSub_tau_QT] at h2
  exact h2

private theorem Z_two_le_V2 (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 2 ≤ X.V2 := by
  have h' := X.Z_zero_sup_Z_two_le h.hc (Or.inl h.hn0) h.hs h.hodd
    h.h5 h.hX h.hGT hreg
  have hV2eq := X.V2_eq_Z_one_sup_Z_three h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  exact (le_sup_right.trans h').trans (le_sup_left.trans (le_of_eq hV2eq.symm))

private theorem Z_zero_le_V0 (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 0 ≤ X.V0 := by
  have h' := X.Z_zero_sup_Z_two_le h.hc (Or.inl h.hn0) h.hs h.hodd
    h.h5 h.hX h.hGT hreg
  have hV0eq := X.V0_eq_Z_one_sup_Z_neg_one h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  exact (le_sup_left.trans h').trans (le_sup_left.trans (le_of_eq hV0eq.symm))

private theorem commutator_QT_Q_zero_sup_ZM_dichotomy (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.QT, X.Q 0⁆ ⊔ X.ZM = X.ZM ∨ ⁅X.QT, X.Q 0⁆ ⊔ X.ZM = X.E X.QT 0 := by
  have hE0 : X.E X.QT 0 = X.V0 ⊔ X.QT :=
    X.E_eq_V0_sup_QT h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have hZM : X.ZM = X.Z 0 ⊔ X.QT :=
    X.ZM_eq_Z_zero_sup_QT h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX
      h.hGT hreg
  have hZA : X.ZM ≤ ⁅X.QT, X.Q 0⁆ ⊔ X.ZM := le_sup_right
  have hAE : ⁅X.QT, X.Q 0⁆ ⊔ X.ZM ≤ X.E X.QT 0 := by
    rw [hE0]
    refine sup_le ((X.commutator_QT_Q_zero_le h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT
      hreg).trans le_sup_left) ?_
    rw [hZM]
    exact sup_le ((Z_zero_le_V0 h hreg).trans le_sup_left) le_sup_right
  have hLstQT : X.Lst X.QT 0 ≤ Subgroup.normalizer (X.QT : Set G) :=
    (oTwoPrime_le (X.normGi X.QT 0)).trans inf_le_left
  have hLstQ0 : X.Lst X.QT 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((oTwoPrime_le (X.normGi X.QT 0)).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hLstZM : X.Lst X.QT 0 ≤ Subgroup.normalizer (X.ZM : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcenter : conjSub l (centerOf (X.Lst X.QT 0)) = centerOf (X.Lst X.QT 0) := by
      unfold centerOf
      rw [conjSub_inf, ← conjSub_centralizer, conjSub_eq_of_mem hl]
    exact hcenter
  have hNA : X.Lst X.QT 0 ≤
      Subgroup.normalizer ((⁅X.QT, X.Q 0⁆ ⊔ X.ZM : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : conjSub l X.QT = X.QT :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLstQT hl)
    have h2 : conjSub l (X.Q 0) = X.Q 0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLstQ0 hl)
    have h3 : conjSub l X.ZM = X.ZM :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLstZM hl)
    have hEq : conjSub l (⁅X.QT, X.Q 0⁆ ⊔ X.ZM) = ⁅X.QT, X.Q 0⁆ ⊔ X.ZM := by
      rw [conjSub_sup, ← conjSub_commutator, h1, h2, h3]
    exact hEq
  exact (X.natQuot_M h.hGT h.hs h.hodd h.h5 h.hX).irred
    (⁅X.QT, X.Q 0⁆ ⊔ X.ZM) hZA hAE hNA

private theorem Q_tau_zero : conjSub X.τ (X.Q 0) = X.Q 2 := by
  simpa using (X.Q_add 1 0).symm

private theorem Ztau_conj : X.Ztau 1 = conjSub X.τ X.ZM := by
  unfold Setup.Ztau
  simp

private theorem commutator_QT_Q_two_le_Z_two_of_sup_eq_ZM (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hZM : ⁅X.QT, X.Q 0⁆ ⊔ X.ZM = X.ZM) : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2 := by
  have hZtau : X.Ztau 1 = X.Z 2 ⊔ X.QT := Ztau_one_eq h hreg
  have hV2QT : X.V2 ⊓ X.QT = ⊥ := V2_inf_QT h hreg
  have hZ2V2 : X.Z 2 ≤ X.V2 := Z_two_le_V2 h hreg
  have hQTQ2 : ⁅X.QT, X.Q 2⁆ ≤ X.V2 :=
    X.commutator_QT_Q_two_le h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have hQTtau : conjSub X.τ X.QT = X.QT := X.conjSub_tau_QT
  have h2 : ⁅X.QT, X.Q 0⁆ ≤ X.ZM := hZM ▸ le_sup_left
  have h3 : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2 ⊔ X.QT := by
    have h3' : conjSub X.τ ⁅X.QT, X.Q 0⁆ ≤ conjSub X.τ X.ZM := conjSub_mono X.τ h2
    rw [← conjSub_commutator, hQTtau, Q_tau_zero, ← Ztau_conj, hZtau] at h3'
    exact h3'
  have hLN : X.Z 2 ≤ Subgroup.normalizer (X.QT : Set G) :=
    (X.Z_le_centralizer_QT 2).trans (Subgroup.centralizer_le_normalizer _)
  have hsum : (X.Z 2 ⊔ ⁅X.QT, X.Q 2⁆) ⊓ X.QT = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right X.QT (sup_le hZ2V2 hQTQ2)).trans hV2QT.le)
  have hkey : X.Z 2 ⊔ ⁅X.QT, X.Q 2⁆ = X.Z 2 := by
    have h' := CFSG.Quasithin.A3.eq_sup_inf_of_le_sup (L := X.Z 2) (N := X.QT)
      (P := X.Z 2 ⊔ ⁅X.QT, X.Q 2⁆) hLN le_sup_left
      (sup_le le_sup_left h3)
    rw [hsum, sup_bot_eq] at h'
    exact h'
  exact le_sup_right.trans (le_of_eq hkey)

private theorem commutator_QT_Q_two_sup_Z_two_eq_V2_of_sup_eq_E (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hE : ⁅X.QT, X.Q 0⁆ ⊔ X.ZM = X.E X.QT 0) :
    ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2 := by
  have hZtau : X.Ztau 1 = X.Z 2 ⊔ X.QT := Ztau_one_eq h hreg
  have hE2 : X.E X.QT 2 = X.V2 ⊔ X.QT := E_two_eq_V2_sup_QT h hreg
  have hV2QT : X.V2 ⊓ X.QT = ⊥ := V2_inf_QT h hreg
  have hZ2V2 : X.Z 2 ≤ X.V2 := Z_two_le_V2 h hreg
  have hQTQ2 : ⁅X.QT, X.Q 2⁆ ≤ X.V2 :=
    X.commutator_QT_Q_two_le h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have hQTtau : conjSub X.τ X.QT = X.QT := X.conjSub_tau_QT
  have hA2 : ⁅X.QT, X.Q 2⁆ ⊔ X.Ztau 1 = X.E X.QT 2 := by
    have h4 : conjSub X.τ (⁅X.QT, X.Q 0⁆ ⊔ X.ZM) = X.E X.QT 2 := by
      rw [hE, X.E_two_eq]
    have h5' : conjSub X.τ (⁅X.QT, X.Q 0⁆ ⊔ X.ZM) = ⁅X.QT, X.Q 2⁆ ⊔ X.Ztau 1 := by
      rw [conjSub_sup, ← conjSub_commutator, hQTtau, Q_tau_zero, Ztau_conj]
    rw [← h5']; exact h4
  have hsum : (⁅X.QT, X.Q 2⁆ ⊔ X.Z 2) ⊔ X.QT = X.V2 ⊔ X.QT := by
    rw [sup_assoc, ← hZtau, hA2, hE2]
  have hLHSle : ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 ≤ X.V2 := sup_le hQTQ2 hZ2V2
  have hD := CFSG.Quasithin.A3.eq_sup_inf_of_le_sup (L := ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2)
    (N := X.QT) (P := X.V2) ((hLHSle.trans (le_sup_left.trans hE2.ge)).trans
      (inf_le_right : X.E X.QT 2 ≤ Subgroup.normalizer (X.QT : Set G)))
    hLHSle (le_sup_left.trans hsum.ge)
  rw [hV2QT, sup_bot_eq] at hD
  exact hD.symm

theorem commutator_QT_Q_two_dichotomy (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.QT, X.Q 2⁆ ≤ X.Z 2 ∨ ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2 := by
  have hctx : Ctx X s := ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩
  rcases commutator_QT_Q_zero_sup_ZM_dichotomy hctx hreg with hA | hA
  · left
    exact commutator_QT_Q_two_le_Z_two_of_sup_eq_ZM hctx hreg hA
  · right
    exact commutator_QT_Q_two_sup_Z_two_eq_V2_of_sup_eq_E hctx hreg hA

variable {X : Setup Γ G} {s : ℕ}

private theorem Z_two_center (h : Ctx X s) : X.Z 2 = centerOf (X.L 2) := by
  have h0 : X.Z 0 = centerOf (X.L 0) :=
    X.Z_zero_eq_centerOf_L_zero h.hc (Or.inl h.hn0) h.hs h.hodd h.h5
      h.hX h.hGT
  have hZ : X.Z 2 = conjSub X.τ (X.Z 0) := by simpa using (X.Z_add 1 0)
  have hL : X.L 2 = conjSub X.τ (X.L 0) := by simpa using (X.L_add 1 0)
  have hcomm : centerOf (conjSub X.τ (X.L 0)) = conjSub X.τ (centerOf (X.L 0)) := by
    unfold centerOf
    rw [conjSub_inf, conjSub_centralizer]
  rw [hZ, h0, hL, hcomm]

private theorem Ki_two_centralizes_Z_two (h : Ctx X s) :
    X.Ki 2 ≤ Subgroup.centralizer (X.Z 2 : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Z_two_center h] at hz
  have hz' : z ∈ Subgroup.centralizer (X.L 2 : Set G) := (Subgroup.mem_inf.mp hz).2
  have hcomm : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hz') k hk.2
  exact hcomm.symm

private theorem K_centralizes_QT (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.K, X.QT⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine Subgroup.le_centralizer_iff.mp ?_
  rw [X.QT_eq_inf_centralizer_K h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg]
  exact inf_le_right

private theorem Q_two_K_two_centralizes_QT (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hZ : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2) :
    ⁅⁅X.Q 2, X.Ki 2⁆, X.QT⁆ = ⊥ := by
  have hK2Z2 : X.Ki 2 ≤ Subgroup.centralizer (X.Z 2 : Set G) := Ki_two_centralizes_Z_two h
  have h1 : ⁅⁅X.Ki 2, X.QT⁆, X.Q 2⁆ = ⊥ := by
    have hle : ⁅X.Ki 2, X.QT⁆ ≤ ⁅X.K, X.QT⁆ := Subgroup.commutator_mono_left inf_le_left
    rw [K_centralizes_QT h hreg] at hle
    have hbot : ⁅X.Ki 2, X.QT⁆ = ⊥ := le_bot_iff.mp hle
    rw [hbot]
    simp
  have h2 : ⁅⁅X.QT, X.Q 2⁆, X.Ki 2⁆ = ⊥ := by
    have hle : ⁅⁅X.QT, X.Q 2⁆, X.Ki 2⁆ ≤ ⁅X.Z 2, X.Ki 2⁆ :=
      Subgroup.commutator_mono_left hZ
    have hbot : ⁅X.Z 2, X.Ki 2⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hK2Z2
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

private theorem Q_zero_K_zero_centralizes_QT (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hZ : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2) :
    ⁅⁅X.Q 0, X.Ki 0⁆, X.QT⁆ = ⊥ := by
  have h3 : ⁅⁅X.Q 2, X.Ki 2⁆, X.QT⁆ = ⊥ := Q_two_K_two_centralizes_QT h hreg hZ
  have hQTtau : conjSub X.τ X.QT = X.QT := X.conjSub_tau_QT
  have hKi : X.Ki 2 = conjSub X.τ (X.Ki 0) := by
    unfold Setup.Ki
    have hL : X.L 2 = conjSub X.τ (X.L 0) := by simpa using (X.L_add 1 0)
    have hK : conjSub X.τ X.K = X.K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp X.τ_norm
    rw [hL, conjSub_inf, hK]
  have hQ2 : X.Q 2 = conjSub X.τ (X.Q 0) := (Q_tau_zero (X := X)).symm
  have h4 : conjSub X.τ ⁅⁅X.Q 0, X.Ki 0⁆, X.QT⁆ = ⊥ := by
    rw [← conjSub_commutator, ← conjSub_commutator, hQTtau, ← hQ2, ← hKi]
    exact h3
  exact (conjSub_eq_bot_iff X.τ).mp h4

private theorem Q_zero_centralizes_QT (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hZ : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2) :
    ⁅X.Q 0, X.QT⁆ = ⊥ := by
  have h4 : ⁅⁅X.Q 0, X.Ki 0⁆, X.QT⁆ = ⊥ := Q_zero_K_zero_centralizes_QT h hreg hZ
  have hAab : IsElemAbelian 2 X.A :=
    X.isElemAbelian_A h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg
  have hAK : X.A ≤ Subgroup.centralizer (X.QT : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqA : q ∈ X.A := le_inf (X.QT_le_Q 1) (X.QT_le_Q (-1)) hq
    exact (CFSG.Quasithin.F7.isElemAbelian_comm hAab ha hqA).symm
  have hK0C : ⁅X.Q 0, X.Ki 0⁆ ≤ Subgroup.centralizer (X.QT : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h4
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro q hq
  rw [X.Q_eq_commutator_sup h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg] at hq
  exact (sup_le hK0C hAK) hq

private theorem QT_le_Z_zero (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hZ : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2) : X.QT ≤ X.Z 0 := by
  have hQ0QT : ⁅X.Q 0, X.QT⁆ = ⊥ := Q_zero_centralizes_QT h hreg hZ
  have hLstQT : ⁅X.Lst X.QT 0, X.QT⁆ = ⊥ := by
    have h' := X.commutator_QT_Lst_eq_bot h.hGT h.hs h.hodd h.h5 h.hX
    rw [Subgroup.commutator_comm]
    exact h'
  have hL0 : X.L 0 = X.Lst X.QT 0 ⊔ X.Q 0 :=
    X.L_eq_Lst_sup_Q (X.isSK_QT h.hGT h.hs h.hodd h.h5 h.hX) (Or.inr h.hn0)
  have hLstC : X.Lst X.QT 0 ≤ Subgroup.centralizer (X.QT : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLstQT
  have hQ0C : X.Q 0 ≤ Subgroup.centralizer (X.QT : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQ0QT
  have hLC : X.L 0 ≤ Subgroup.centralizer (X.QT : Set G) := by
    rw [hL0]
    exact sup_le hLstC hQ0C
  have hQTc : X.QT ≤ Subgroup.centralizer (X.L 0 : Set G) :=
    Subgroup.le_centralizer_iff.mp hLC
  have hQTL : X.QT ≤ X.L 0 :=
    (X.QT_le_Q 0).trans
      (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0)) (X.Q_le_Gi 0))
  rw [X.Z_zero_eq_centerOf_L_zero h.hc (Or.inl h.hn0) h.hs h.hodd h.h5
      h.hX h.hGT]
  intro q hq
  exact Subgroup.mem_inf.mpr ⟨hQTL hq, hQTc hq⟩

private theorem false_of_Z_two (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hZ : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2) : False := by
  have hQTZ0 : X.QT ≤ X.Z 0 := QT_le_Z_zero h hreg hZ
  have hbot : X.QT ⊓ X.Z 0 = ⊥ :=
    X.QT_inf_Z_eq_bot h.hGT h.hs h.hodd h.h5 h.hX 0
  have hQTbot : X.QT = ⊥ := le_bot_iff.mp (hbot ▸ le_inf le_rfl hQTZ0)
  exact X.QT_ne_bot h.hGT hQTbot

theorem false_of_commutator_le_Z_two (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (h : ⁅X.QT, X.Q 2⁆ ≤ X.Z 2) : False := by
  exact false_of_Z_two ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩ hreg h

variable {X : Setup Γ G} {s : ℕ}

private theorem V2_le_Gi_one (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.V2 ≤ X.Gi 1 := by
  have hZ3 : X.Z 3 = conjSub X.τ (X.Z 1) := by simpa using (X.Z_add 1 1)
  have hZ3G0 : X.Z 3 ≤ X.Gi 0 := by
    rw [hZ3]
    calc conjSub X.τ (X.Z 1) ≤ conjSub X.τ (X.Gi (-2)) :=
          conjSub_mono _ ((X.Z_one_b_facts h.hc (Or.inl h.hn0) h.hs
            h.hodd h.h5 h.hX h.hGT hreg).1.trans inf_le_left)
      _ = X.Gi 0 := by simpa using (X.Gi_add 1 (-2)).symm
  have hZ3Q1 : X.Z 3 ≤ X.Q 1 :=
    X.Z_le_Q_of_le_Gi 3 0 1 hZ3G0 (Or.inr ⟨by norm_num, by norm_num⟩)
  rw [X.V2_eq_Z_one_sup_Z_three h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg]
  exact sup_le ((X.Z_le_Q 1).trans (X.Q_le_Gi 1)) (hZ3Q1.trans (X.Q_le_Gi 1))

private theorem V2_Kst_le_Z_one (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hV2 : ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2) : ⁅X.V2, X.Kst⁆ ≤ X.Z 1 := by
  have hV2N : X.V2 ≤ Subgroup.normalizer (X.Z 1 : Set G) :=
    (V2_le_Gi_one h hreg).trans (X.Gi_le_normalizer_Z 1)
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 :=
    le_sup_right.trans (X.Z_zero_sup_Z_two_le h.hc (Or.inl h.hn0) h.hs
      h.hodd h.h5 h.hX h.hGT hreg)
  have hKstN : X.Kst ≤ Subgroup.normalizer (X.Z 2 : Set G) :=
    ((inf_le_left : X.Kst ≤ X.K).trans (X.K_le_Gi 2)).trans (X.Gi_le_normalizer_Z 2)
  rw [← hV2]
  exact CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _
    (X.commutator_commutator_QT_Q_two_Kst_le h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT
      hreg)
    ((Subgroup.le_normalizer_iff_commutator_le_left.mp hKstN).trans hZ2Z1)
    ((le_sup_left.trans hV2.le).trans hV2N) ((le_sup_right.trans hV2.le).trans hV2N)

private theorem Z_four_Kst_le_Q_zero (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hV2 : ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2) :
    ⁅X.Z 4, X.Kst⁆ ≤ X.Q 0 :=
  (Subgroup.commutator_mono_left (((X.Z_three_eq_Z_two_sup_Z_four
          h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg).symm
      ▸ le_sup_right : X.Z 4 ≤ X.Z 3).trans (le_sup_right.trans
    (X.V2_eq_Z_one_sup_Z_three h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT hreg).ge))).trans
    ((V2_Kst_le_Z_one h hreg hV2).trans (X.Z_one_le_Q_zero
          h.hc (Or.inl h.hn0) h.hs h.hodd h.h5 h.hX h.hGT hreg))

private theorem Kst_fixes_neighbors_zero (h : Ctx X s) {m : ℕ}
    (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) (hV2 : ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2)
    {k : G} (hk : k ∈ X.Kst) :
    ∀ w : V, Γ.Adj (X.vert 0) w → k • w = w :=
  X.fixes_neighbors_of_commutator_Z_four_mem h.hc h.hn0 h.hs h.hodd h.h5 h.hX h.hGT
    hreg ((inf_le_left : X.Kst ≤ X.K) hk) fun z hz =>
      Subgroup.commutator_le.mp (Z_four_Kst_le_Q_zero h hreg hV2) z hz k hk

private theorem L_zero_Kst_le_Q_zero (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hV2 : ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2) : ⁅X.L 0, X.Kst⁆ ≤ X.Q 0 := by
  rw [Subgroup.commutator_le]
  intro l hl k hk
  have hkG0 : k ∈ X.Gi 0 := (inf_le_left.trans (X.K_le_Gi 0)) hk
  have hfix : ∀ w : V, Γ.Adj (X.vert 0) w → k • w = w :=
    Kst_fixes_neighbors_zero h hreg hV2 hk
  have hinv := (X.Q 0).inv_mem
    (X.commutator_mem_Q_of_fixes_neighbors 0 hkG0 hfix l hl)
  rwa [commutatorElement_inv] at hinv

private theorem L_one_Kst_le_Q_one :
    ⁅X.L 1, X.Kst⁆ ≤ X.Q 1 :=
  X.L_Kst_le_Q 1 fun k hk => (X.mem_Kst.mp hk).2

private theorem Kst_eq_bot (h : Ctx X s) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (hV2 : ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2) : X.Kst = ⊥ := by
  have hL0 : ⁅X.L 0, X.Kst⁆ ≤ X.Q 0 := L_zero_Kst_le_Q_zero h hreg hV2
  have hL1 : ⁅X.L 1, X.Kst⁆ ≤ X.Q 1 := L_one_Kst_le_Q_one
  have hodd : Odd (Nat.card ↥X.Kst) :=
    X.odd_card_K.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  refine X.eq_bot_of_commutator_le_Q (X.adj 0) hodd ?_ hL0 hL1
  exact le_inf (inf_le_left.trans (X.K_le_Gi 0)) (inf_le_left.trans (X.K_le_Gi 1))

theorem Kst_eq_bot_of_commutator_sup (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    (h : ⁅X.QT, X.Q 2⁆ ⊔ X.Z 2 = X.V2) : X.Kst = ⊥ := by
  exact Kst_eq_bot ⟨hc, hn0, hs, hodd, h5, hX, hGT⟩ hreg h

end Setup

theorem sec6_false {G : Type} [Group G] [MulAction G V]
    (hc : CharTwoStab (V := V) (G := G)) (X : Setup Γ G) (hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    False := by
  obtain ⟨m, -, hreg⟩ := X.exists_isMaxReg hs hodd hX
  have hn0 : 2 ≤ X.n 0 := by
    have hle := X.n_one_le_n_zero hc hmax hs hodd h5 hX hGT
    omega
  rcases X.commutator_QT_Q_two_dichotomy hc hn0 hs hodd h5 hX hGT hreg with h | h
  · exact X.false_of_commutator_le_Z_two hc hn0 hs hodd h5 hX hGT hreg h
  · exact X.Kst_ne_bot hc hn0 hs hodd h5 hX hGT hreg
      (X.Kst_eq_bot_of_commutator_sup hc hn0 hs hodd h5 hX hGT hreg h)

theorem sec6_false_of_exists_two_le {G : Type} [Group G] [MulAction G V]
    (hc : CharTwoStab (V := V) (G := G)) (h2 : ∃ v : V, 2 ≤ nOf Γ v) (X : Setup Γ G)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    False := by
  obtain ⟨v, hv⟩ := h2
  have hmax : 2 ≤ X.n 0 ∨ 2 ≤ X.n 1 := by
    have hnOf_smul : ∀ (g : G) (w : V), nOf Γ (g • w) = nOf Γ w := X.hyp.nOf_smul
    have horb := orbit_eq_even_of_adj (G := G) X.hyp.isTree X.hyp.adj_smul X.hyp.edgeTrans
      X.hyp.preservesParts (X.adj 0) (fun w => X.hyp.exists_adj w)
    rcases horb with ⟨h0, h1⟩
    rcases Nat.even_or_odd (Γ.dist (X.vert 0) v) with hev | hod
    · left
      obtain ⟨g, hg⟩ := (h0 v).mpr hev
      rw [← hg, hnOf_smul] at hv
      simpa using hv
    · right
      obtain ⟨g, hg⟩ := (h1 v).mpr hod
      rw [← hg, hnOf_smul] at hv
      simpa using hv
  exact sec6_false hc X hmax hs hodd h5 hX hGT

theorem sec6_false' {G : Type} [Group G] [MulAction G V] (h : Hyp30 Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (hn : ∀ v : V, nOf Γ v = 1 ∨ nOf Γ v = 2)
    (h11 : ∃ v : V, nOf Γ v = 2) (X : Setup Γ G) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) : False := by
  obtain ⟨v, hv⟩ := h11
  exact sec6_false_of_exists_two_le hc ⟨v, hv.ge⟩ X hs hodd h5 hX hGT

end CFSG.Quasithin.St84
