module

public import CFSG.Quasithin.Recognition.St84.Sec4Comm
public import CFSG.Quasithin.Recognition.St84.Sec4QuotA
public import CFSG.Quasithin.Recognition.St84.Sec4Sections
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
public import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
import CFSG.Quasithin.Recognition.St84.Gen.NatSecLines
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)
variable {r : ℕ}

private theorem hasB_self_of_even (H : X.Sec4Hyp s r) {d₀ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hev : Even d₀) : X.HasB (d₀ : ℤ) d₀ := by
  refine (X.hasB_iff_of_even (i := (d₀ : ℤ)) (j := 0) ?_ d₀).mpr hd₀
  obtain ⟨k, hk⟩ := hev
  exact ⟨(k : ℤ), by omega⟩

private theorem le_normalizer_Z_of_le_Gi {U : Subgroup G} {i : ℤ} (h : U ≤ X.Gi i) :
    U ≤ Subgroup.normalizer (X.Z i : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [conjSub] using X.Z_normal i g (h hg)

private theorem commutator_Z_zero_Z_le_inf {d₀ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hdZ : X.HasB (d₀ : ℤ) d₀) : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≤ X.Z 0 ⊓ X.Z (d₀ : ℤ) := by
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      (le_normalizer_Z_of_le_Gi X (hdZ.Z_le_Gi (by omega)))
  · exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      (le_normalizer_Z_of_le_Gi X (hd₀.Z_le_Gi (by omega)))

private theorem relCent_Z_zero_bot (A : Subgroup G) :
    relCent (X.Z 0) (⊥ : Subgroup G) A = X.Z 0 ⊓ Subgroup.centralizer (A : Set G) := by
  have hEZ : X.Z 0 ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  ext y
  rw [mem_relCent hEZ]
  constructor
  · rintro ⟨hyZ, hc⟩
    refine Subgroup.mem_inf.mpr ⟨hyZ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ⁅y, a⁆ = 1 := by simpa using hc a ha
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · intro hy
    obtain ⟨hyZ, hyC⟩ := Subgroup.mem_inf.mp hy
    refine ⟨hyZ, ?_⟩
    intro a ha
    have hcomm : a * y = y * a := Subgroup.mem_centralizer_iff.mp hyC a ha
    simpa using (commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm)

private theorem Z_sup_Q_zero_eq_S (H : X.Sec4Hyp s r) {d₀ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hev : Even d₀) : X.Z ((d₀ : ℤ)) ⊔ X.Q 0 = X.S := by
  have hd0ge2 : 2 ≤ d₀ := by
    have h1 := X.one_le_of_hasB hd₀
    obtain ⟨k, hk⟩ := hev
    omega
  have hdZ : X.HasB ((d₀ : ℤ)) d₀ := hasB_self_of_even X H hd₀ hev
  have hZleQ1 : X.Z ((d₀ : ℤ)) ≤ X.Q 1 := by
    have hZ2 : IsPGroup 2 (X.Z ((d₀ : ℤ))) :=
      (pCoreOf_isPGroup' (X.Gi ((d₀ : ℤ)))).to_le (X.Z_le_Q ((d₀ : ℤ)))
    have hZGi1 : X.Z ((d₀ : ℤ)) ≤ X.Gi 1 := by
      have h := hdZ.1 (1 - (d₀ : ℤ)) (by omega)
      simpa using h
    have hadjL : Γ.Adj (X.vert 1) (X.vert 0) := (X.adj 0).symm
    have hadjR : Γ.Adj (X.vert 1) (X.vert 2) := X.adj 1
    have hne : X.vert 0 ≠ X.vert 2 := by
      intro h
      have := X.vert_injective h
      omega
    refine le_pCoreOf_of_isPGroup_fixes_two X.hyp hZ2 hZGi1 hadjL hadjR hne ?_ ?_
    · intro y hy
      simpa using (MulAction.mem_stabilizer_iff.mp (hdZ.1 (-(d₀ : ℤ)) (by omega) hy))
    · intro y hy
      simpa using (MulAction.mem_stabilizer_iff.mp (hdZ.1 (2 - (d₀ : ℤ)) (by omega) hy))
  have hZK : X.K ≤ Subgroup.normalizer (X.Z ((d₀ : ℤ)) : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.K_le_Gi _)
  have hZedge0 : X.Z ((d₀ : ℤ)) ≤ X.edgeSylow 0 :=
    hZleQ1.trans (X.Q_le_edgeSylow (i := 0))
  have hnotZQ0 : ¬ X.Z ((d₀ : ℤ)) ≤ X.Q 0 := by
    have h := (X.not_Z_le_Q_edge hdZ).2
    simpa using h
  have h := X.sup_Q_eq_edgeSylow_of_left_gen 0 (inf_le_left.trans hZK) hZedge0 hnotZQ0
  rw [X.edgeSylow_zero] at h
  exact h

private theorem comm_Z_zero_le_centralizer_S (H : X.Sec4Hyp s r) {d₀ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hev : Even d₀) :
    ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ Subgroup.centralizer (X.S : Set G) := by
  have hZQ0 : X.Z ((d₀ : ℤ)) ⊔ X.Q 0 = X.S := Z_sup_Q_zero_eq_S X H hd₀ hev
  have hdZ : X.HasB ((d₀ : ℤ)) d₀ := hasB_self_of_even X H hd₀ hev
  have hled : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ X.Z ((d₀ : ℤ)) :=
    (commutator_Z_zero_Z_le_inf X hd₀ hdZ).trans inf_le_right
  have hEQ : ⁅X.Z ((d₀ : ℤ)), X.Q 0⁆ ≤ X.Q 0 := by
    refine Subgroup.le_normalizer_iff_commutator_le_right.mp ?_
    intro z hz
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hzGi : z ∈ X.Gi 0 := by
      have h := hdZ.1 (-(d₀ : ℤ)) (by omega)
      simpa using h hz
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hzGi)
  have hQZ : ⁅X.Q 0, X.Z 0⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact (X.Z_le_center 0).trans inf_le_right
  have hXQ0 : ⁅⁅X.Z 0, X.Z ((d₀ : ℤ))⁆, X.Q 0⁆ = ⊥ := by
    have h1 : ⁅⁅X.Z ((d₀ : ℤ)), X.Q 0⁆, X.Z 0⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact (Subgroup.commutator_mono_left hEQ).trans (le_of_eq hQZ)
    have h2 : ⁅⁅X.Q 0, X.Z 0⁆, X.Z ((d₀ : ℤ))⁆ = ⊥ := by
      rw [hQZ, Subgroup.commutator_bot_left]
    exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hXcQ0 : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ Subgroup.centralizer (X.Q 0 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXQ0
  rw [← hZQ0]
  refine CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
    (K := ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆) (A := X.Z ((d₀ : ℤ))) (B := X.Q 0) ?_ hXcQ0
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact X.Z_commute ((d₀ : ℤ)) z hz x (hled hx)

private theorem sq_mem_centerOf_L_zero_of_comm (H : X.Sec4Hyp s r) {d₀ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hev : Even d₀) (hcomm : ⁅X.Z 0, X.S⁆ = ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆) :
    ∀ x ∈ X.Z 0, x ^ 2 ∈ centerOf (X.L 0) := by
  have hdZ : X.HasB ((d₀ : ℤ)) d₀ := hasB_self_of_even X H hd₀ hev
  have hQ0L : X.Q 0 ≤ X.L 0 := X.Q_le_L 0
  have hle0 : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ X.Z 0 :=
    (commutator_Z_zero_Z_le_inf X hd₀ hdZ).trans inf_le_left
  have hXcS : ∀ x ∈ ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆, ∀ s ∈ X.S, x * s = s * x := fun x hx s hs =>
    (Subgroup.mem_centralizer_iff.mp (comm_Z_zero_le_centralizer_S X H hd₀ hev hx) s hs).symm
  have hsqS : ∀ x ∈ X.Z 0, x ^ 2 ∈ Subgroup.centralizer (X.S : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hxS : ⁅x, s⁆ ∈ ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ := by
      have h := Subgroup.commutator_mem_commutator hx hs
      rwa [hcomm] at h
    have hxcomm : Commute x ⁅x, s⁆ := by
      rw [Commute]
      exact X.Z_commute 0 x hx ⁅x, s⁆ (hle0 hxS)
    have hscomm : Commute s ⁅x, s⁆ := by
      rw [Commute]
      exact (hXcS ⁅x, s⁆ hxS s hs).symm
    have hS2 : IsPGroup 2 X.S := by
      simpa [Setup.S, Setup.edgeSylow] using X.isPGroup_edgeSylow 0
    have hSL : X.S ≤ X.L 0 := X.edgeSylow_le_L 0
    have hs2Q : s ^ 2 ∈ X.Q 0 :=
      (X.sq_comm_mem_Q_of_le_L 0 hS2 hSL).1 s hs
    have hcomm1 : ⁅x ^ 2, s⁆ = 1 := by
      rw [← Commute.commutatorElement_pow_left hxcomm 2,
        Commute.commutatorElement_pow_right hscomm 2]
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 0 hx)).2
        (s ^ 2) hs2Q).symm
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm1).symm
  have hsqSq : ∀ x ∈ X.Z 0, ∀ l ∈ X.L 0,
      x ^ 2 ∈ Subgroup.centralizer (conjSub l (X.S) : Set G) := by
    intro x hx l hl
    have hxL : l⁻¹ * x * l ∈ X.Z 0 := by
      have h := X.Z_normal 0 l (X.L_le_Gi 0 hl)
      exact mem_conjSub.mp (by rw [h]; exact hx)
    have hmem : l⁻¹ * x ^ 2 * l ∈ Subgroup.centralizer (X.S : Set G) := by
      have heq : l⁻¹ * x ^ 2 * l = (l⁻¹ * x * l) ^ 2 := by
        simp only [pow_two]; group
      rw [heq]
      exact hsqS (l⁻¹ * x * l) hxL
    rw [conjSub_centralizer l (X.S)]
    exact mem_conjSub.mpr hmem
  intro x hx
  have hx2L : x ^ 2 ∈ X.L 0 := hQ0L (X.Z_le_Q 0 ((X.Z 0).pow_mem hx 2))
  refine Subgroup.mem_inf.mpr ⟨hx2L, ?_⟩
  obtain ⟨t, ht, htref, -⟩ := X.exists_reflection_oTwoRes H 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) (Subgroup.mem_inf.mp ht).1
  have hS' : conjSub t (X.S) = X.edgeSylow (-1) := by
    rw [← X.edgeSylow_zero]
    exact X.conjSub_edgeSylow_swap (by simpa using htref 0) (by simpa using htref 1)
  have hLsup : X.L 0 = X.S ⊔ conjSub t (X.S) := by
    rw [← X.edgeSylow_sup_edgeSylow 0, hS']
    rw [show (0 : ℤ) - 1 = -1 by norm_num, sup_comm]
    rfl
  have hzpS : Subgroup.zpowers (x ^ 2) ≤ Subgroup.centralizer (X.S : Set G) :=
    Subgroup.zpowers_le.mpr (hsqS x hx)
  have hzpS' : Subgroup.zpowers (x ^ 2) ≤
      Subgroup.centralizer (conjSub t (X.S) : Set G) :=
    Subgroup.zpowers_le.mpr (hsqSq x hx t htL)
  have hzpL : Subgroup.zpowers (x ^ 2) ≤ Subgroup.centralizer (X.L 0 : Set G) := by
    rw [hLsup]
    exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hzpS hzpS'
  exact Subgroup.mem_centralizer_iff.mp (hzpL (Subgroup.mem_zpowers (x ^ 2)))

private theorem relIndex_relCent_S_le (H : X.Sec4Hyp s r) {d₀ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hev : Even d₀) :
    (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)).relIndex (X.Z 0) ≤ 2 ^ X.n 0 := by
  haveI hfinZ : Finite ↥(X.Z 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hd0ge2 : 2 ≤ d₀ := by
    have h1 := X.one_le_of_hasB hd₀
    obtain ⟨k, hk⟩ := hev
    omega
  have hZQ0 : X.Z ((d₀ : ℤ)) ⊔ X.Q 0 = X.S := Z_sup_Q_zero_eq_S X H hd₀ hev
  have hZleSp : X.Z 0 ≤ X.edgeSylow ((d₀ : ℤ) - 1) := by
    have hZQpred : X.Z 0 ≤ X.Q ((d₀ : ℤ) - 1) := by
      have hZ2 : IsPGroup 2 (X.Z 0) :=
        (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
      have hZGi : X.Z 0 ≤ X.Gi ((d₀ : ℤ) - 1) := by
        have h := hd₀.1 ((d₀ : ℤ) - 1) (by omega)
        simpa using h
      have hadjL : Γ.Adj (X.vert ((d₀ : ℤ) - 1)) (X.vert ((d₀ : ℤ) - 2)) := by
        have h := (X.adj ((d₀ : ℤ) - 2)).symm
        rwa [show ((d₀ : ℤ) - 2) + 1 = (d₀ : ℤ) - 1 by ring] at h
      have hadjR : Γ.Adj (X.vert ((d₀ : ℤ) - 1)) (X.vert (d₀ : ℤ)) := by
        simpa using X.adj ((d₀ : ℤ) - 1)
      have hne : X.vert ((d₀ : ℤ) - 2) ≠ X.vert (d₀ : ℤ) := by
        intro h
        have := X.vert_injective h
        omega
      refine le_pCoreOf_of_isPGroup_fixes_two X.hyp hZ2 hZGi hadjL hadjR hne ?_ ?_
      · intro y hy
        have h := hd₀.1 ((d₀ : ℤ) - 2) (by omega) hy
        simpa using (MulAction.mem_stabilizer_iff.mp h)
      · intro y hy
        have h := hd₀.1 (d₀ : ℤ) (by simp) hy
        simpa using (MulAction.mem_stabilizer_iff.mp h)
    exact hZQpred.trans (X.Q_le_edgeSylow_left ((d₀ : ℤ) - 1))
  have hrel : (X.Q ((d₀ : ℤ))).relIndex (X.edgeSylow ((d₀ : ℤ) - 1)) =
      2 ^ X.n 0 := by
    have h := X.relIndex_Q_succ_edgeSylow ((d₀ : ℤ) - 1)
    obtain ⟨k, hk⟩ := hev
    rw [show ((d₀ : ℤ) - 1) + 1 = (d₀ : ℤ) by ring, show X.n (d₀ : ℤ) = X.n 0 by
      rw [show (d₀ : ℤ) = 0 + 2 * (k : ℤ) by omega]; exact X.n_add k 0] at h
    simpa using h
  have hZidx : (X.Z 0 ⊓ X.Q ((d₀ : ℤ))).relIndex (X.Z 0) ≤ 2 ^ X.n 0 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    calc (X.Q ((d₀ : ℤ))).relIndex (X.Z 0)
        ≤ (X.Q ((d₀ : ℤ))).relIndex (X.edgeSylow ((d₀ : ℤ) - 1)) :=
          Subgroup.relIndex_le_of_le_right hZleSp (by rw [hrel]; positivity)
      _ = 2 ^ X.n 0 := hrel
  have hEZ : X.Z 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
    (X.Z_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)
  have hZQ0sub : X.Z 0 ⊓ X.Q ((d₀ : ℤ)) ≤
      relCent (X.Z 0) (centerOf (X.L 0)) (X.S) := by
    intro y hy
    obtain ⟨hyZ, hyQ⟩ := Subgroup.mem_inf.mp hy
    have hyZc : Subgroup.zpowers y ≤ Subgroup.centralizer (X.Z ((d₀ : ℤ)) : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center ((d₀ : ℤ)) ha)).2 y hyQ).symm
    have hyQc : Subgroup.zpowers y ≤ Subgroup.centralizer (X.Q 0 : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center 0 hyZ)).2 q hq
    have hySc : Subgroup.zpowers y ≤ Subgroup.centralizer (X.S : Set G) := by
      rw [← hZQ0]
      exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hyZc hyQc
    rw [mem_relCent hEZ]
    refine ⟨hyZ, ?_⟩
    intro s hs
    have hcomm : y * s = s * y :=
      (Subgroup.mem_centralizer_iff.mp (hySc (Subgroup.mem_zpowers y)) s hs).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact (centerOf (X.L 0)).one_mem
  have hT4 : (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)).relIndex (X.Z 0) ≤
      2 ^ X.n 0 := by
    have hne0 : (X.Z 0 ⊓ X.Q ((d₀ : ℤ))).relIndex (X.Z 0) ≠ 0 := by
      intro h0
      have hcard := Subgroup.relIndex_mul_card
        (H := X.Z 0 ⊓ X.Q ((d₀ : ℤ))) (K := X.Z 0)
      rw [h0, zero_mul] at hcard
      exact Nat.card_pos.ne' hcard.symm
    exact (Subgroup.relIndex_le_of_le_left hZQ0sub hne0).trans hZidx
  exact hT4

private theorem relIndex_relCent_edgeSylow_neg_one_le (H : X.Sec4Hyp s r) {c : ℕ}
    (hT : (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)).relIndex (X.Z 0) ≤ c) :
    (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1))).relIndex (X.Z 0) ≤ c := by
  have hEZ : X.Z 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
    (X.Z_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)
  obtain ⟨t, ht, htref, -⟩ := X.exists_reflection_oTwoRes H 0
  have htL : t ∈ X.L 0 := oTwoRes_le (X.L 0) (Subgroup.mem_inf.mp ht).1
  have htGi : t ∈ X.Gi 0 := X.L_le_Gi 0 htL
  have hconjS : conjSub t (X.S) = X.edgeSylow (-1) := by
    rw [← X.edgeSylow_zero]
    exact X.conjSub_edgeSylow_swap (by simpa using htref 0) (by simpa using htref 1)
  have hconjZ : conjSub t (X.Z 0) = X.Z 0 := by
    simpa [conjSub] using X.Z_normal 0 t htGi
  have hconjC : conjSub t (centerOf (X.L 0)) = centerOf (X.L 0) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (X.Gi_le_normalizer_centerOf_L 0 htGi)
  have hrelconj : conjSub t (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)) =
      relCent (X.Z 0) (centerOf (X.L 0)) (conjSub t (X.S)) := by
    rw [conjSub_relCent t hEZ, hconjZ, hconjC]
  have hT4' : (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1))).relIndex
      (X.Z 0) ≤ c := by
    have hEq : relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1)) =
        conjSub t (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)) := by
      rw [hrelconj, hconjS]
    have hidx := CFSG.Quasithin.F9.relIndex_conjSub t
      (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)) (X.Z 0)
    rw [hEq]
    have hidx' : (conjSub t (relCent (X.Z 0) (centerOf (X.L 0)) (X.S))).relIndex
        (X.Z 0) ≤ c := by
      have h := hidx
      rw [hconjZ] at h
      rw [h]
      exact hT
    exact hidx'
  exact hT4'

private theorem natQuot_Z_zero_of_relIndex_le
    (H : X.Sec4Hyp s r) (hne : centerOf (X.L 0) ≠ X.Z 0)
    (hsec : IsElemSec (centerOf (X.L 0)) (X.Z 0))
    (hT4 : (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)).relIndex (X.Z 0) ≤ 2 ^ X.n 0)
    (hT4' : (relCent (X.Z 0) (centerOf (X.L 0)) (X.edgeSylow (-1))).relIndex (X.Z 0) ≤
      2 ^ X.n 0) :
    NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) := by
  haveI hfinGi : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI hfinL : Finite ↥(X.L 0) :=
    finite_of_le_stabilizer X.hyp (H := X.L 0) (X.L_le_Gi 0)
  haveI hfinZ : Finite ↥(X.Z 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
  have hQ0L : X.Q 0 ≤ X.L 0 := X.Q_le_L 0
  have hEZ : X.Z 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
    (X.Z_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)
  have hLsup : X.L 0 = X.edgeSylow (-1) ⊔ X.S := by
    rw [← X.edgeSylow_sup_edgeSylow 0]
    rfl
  have hgen : X.L 0 ≤ (X.S ⊔ X.edgeSylow (-1)) ⊔ pCoreOf 2 (X.L 0) := by
    rw [hLsup]
    exact (sup_le le_sup_right le_sup_left).trans le_sup_left
  have hq : IsL2Quot (X.n 0) (oTwoQuot ↥(X.L 0)) :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).quot
  have hLcomm : X.L 0 = ⁅X.L 0, X.L 0⁆ ⊔ X.Q 0 :=
    X.L_eq_commutator_sup_Q 0 (H.two_le_n 0) hq
  have hQE : X.Q 0 ≤ Subgroup.centralizer (X.Z 0 : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2 q hq).symm
  have hLE : X.L 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X (X.L_le_Gi 0)
  have hEQ : X.Z 0 ≤ X.Q 0 := X.Z_le_Q 0
  have hcent : relCent (X.Z 0) (centerOf (X.L 0)) (X.L 0) = centerOf (X.L 0) := by
    have h := relCent_L_eq (L := X.L 0) (Q := X.Q 0) (E := X.Z 0) hEQ hQE hLcomm
    rwa [inf_eq_left.mpr (X.centerOf_L_le_Z H.char 0)] at h
  have hE2 : IsPGroup 2 (X.Z 0) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
  have hLZ : X.L 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
    (X.L_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)
  have hT : X.S ≤ X.L 0 := X.edgeSylow_le_L 0
  have hT' : X.edgeSylow (-1) ≤ X.L 0 := by
    have h := X.isSylowTwoOf_edgeSylow_L_succ (-1)
    simpa using h.1
  have hpLQ : pCoreOf 2 (X.L 0) ≤ X.Q 0 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq.le
  have hcore : ⁅X.Z 0, pCoreOf 2 (X.L 0)⁆ ≤ centerOf (X.L 0) := by
    have hZcent : X.Z 0 ≤ Subgroup.centralizer (X.Q 0 : Set G) :=
      (X.Z_le_center 0).trans inf_le_right
    calc ⁅X.Z 0, pCoreOf 2 (X.L 0)⁆ ≤ ⁅X.Z 0, X.Q 0⁆ :=
          Subgroup.commutator_mono le_rfl hpLQ
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcent
      _ ≤ centerOf (X.L 0) := bot_le
  have hlines := relIndex_eq_two_pow_of_lines (L := X.L 0) (E := X.Z 0)
    (Z := centerOf (X.L 0)) (T := X.S) (T' := X.edgeSylow (-1)) (n := X.n 0)
    (by have := H.two_le_n 0; omega) hq (X.centerOf_L_le_Z H.char 0) hEZ hLE hLZ hE2
    hcore hT hT' hgen hcent hne hT4 hT4'
  have hGiZ : X.Gi 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X le_rfl
  have hGiC : X.Gi 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
    X.Gi_le_normalizer_centerOf_L 0
  have hnontriv : ∃ l ∈ X.L 0, ∃ e ∈ X.Z 0, ⁅l, e⁆ ∉ centerOf (X.L 0) := by
    by_contra h
    apply hne
    apply le_antisymm (X.centerOf_L_le_Z H.char 0) ?_
    intro e heZ
    rw [← hcent, mem_relCent hEZ]
    refine ⟨heZ, ?_⟩
    intro l hl
    by_contra hc
    apply h
    refine ⟨l, hl, e, heZ, ?_⟩
    intro hle
    exact hc (by
      rw [← commutatorElement_inv l e]
      exact (centerOf (X.L 0)).inv_mem hle)
  have hpre : NatPre (X.Gi 0) (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) := by
    refine ⟨X.L_le_Gi 0, CFSG.Quasithin.le_normalizer_oTwoPrime (X.Gi 0), hGiZ, hGiC,
      hsec, hlines.1, ?_, hq, hnontriv⟩
    · intro q hq e he
      have hq1 : ⁅q, e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center 0 he)).2 q hq)
      rw [hq1]
      exact (centerOf (X.L 0)).one_mem
  have hnat : NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) :=
    natQuot_of_two_pow_le (P := X.Gi 0) (L := X.L 0) (E := X.Z 0)
      (Z := centerOf (X.L 0)) (T := X.S) (H.two_le_n 0) hpre
      (X.Z_le_Q 0 |>.trans hQ0L)
      (by simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_L 0)
      (le_of_eq hlines.2.symm)
  exact hnat

theorem s45_step2 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) :
    NatQuot (X.L 0) (X.Z 0) (centerOf (X.L 0)) (X.n 0) ∧ X.Z d₀ ⊔ X.Q 0 = X.S ∧
      ⁅X.Z 0, X.S⁆ = ⁅X.Z 0, X.Z d₀⁆ := by
  have hP0 := X.s45_Z_zero_not_central H hd₀ hd₁ hna hev
  have hstep1 := X.s45_step1 H hd₀ hd₁ hna hev
  obtain ⟨hd1, h2d, hrle⟩ := hstep1
  have hdZ : X.HasB ((d₀ : ℤ)) d₀ := hasB_self_of_even X H hd₀ hev
  have hZQ0 : X.Z ((d₀ : ℤ)) ⊔ X.Q 0 = X.S := Z_sup_Q_zero_eq_S X H hd₀ hev
  have hcomm : ⁅X.Z 0, X.S⁆ = ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ := by
    rw [← hZQ0, sup_comm]
    refine CFSG.RankThree.PartOne.Sec9A.commutator_sup_eq_of_le_centralizer
      (R := X.Z 0) (B := X.Q 0) (E := X.Z ((d₀ : ℤ))) ?_ ?_
    · exact sup_le (le_normalizer_Z_of_le_Gi X (X.Q_le_Gi 0))
        (le_normalizer_Z_of_le_Gi X (hdZ.Z_le_Gi (by omega)))
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2 q hq).symm
  have hsqL := sq_mem_centerOf_L_zero_of_comm X H hd₀ hev hcomm
  have hsec : IsElemSec (centerOf (X.L 0)) (X.Z 0) := by
    refine ⟨X.centerOf_L_le_Z H.char 0, ?_, hsqL⟩
    have hZZ : ⁅X.Z 0, X.Z 0⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact X.Z_commute 0 w hw z hz
    rw [hZZ]
    exact bot_le
  have hT4 := relIndex_relCent_S_le X H hd₀ hev
  have hT4' := relIndex_relCent_edgeSylow_neg_one_le X H hT4
  have hne : centerOf (X.L 0) ≠ X.Z 0 := by
    intro h
    apply hP0.1
    rw [← h]
    exact inf_le_right
  exact ⟨natQuot_Z_zero_of_relIndex_le X H hne hsec hT4 hT4', hZQ0, hcomm⟩

private theorem centerOf_L_succ_ne_bot {d₀ d₁ : ℕ} (hd1 : d₀ + 1 = d₁) (hev : Even d₀)
    (hZL : centerOf (X.L 0) ≠ ⊥) :
    centerOf (X.L ((d₁ : ℤ) + 1)) ≠ ⊥ := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  obtain ⟨k, hk⟩ := hev
  have hh2 : h = 0 + 2 * ((k : ℤ) + 1) := by omega
  rw [hh2, X.centerOf_L_add]
  intro hbot
  apply hZL
  rwa [conjSub_eq_bot_iff] at hbot

private theorem centerOf_L_le_Z_pred (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hdH : X.HasB ((d₁ : ℤ) + 1) d₀) (h2d0 : 2 ≤ d₀) :
    centerOf (X.L ((d₁ : ℤ) + 1)) ≤ X.Z (((d₁ : ℤ) + 1) - 1) := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  have hZh_le : centerOf (X.L h) ≤ X.Z h := X.centerOf_L_le_Z H.char h
  have hZh_le_Q : X.Z h ≤ X.Q (h - 1) ⊓ X.Q (h + 1) :=
    X.Z_le_Q_inf_of_hasB hdH (by omega)
  have hcenter_le_Sm : centerOf (X.L h) ≤ X.edgeSylow (h - 1) :=
    (hZh_le.trans ((hZh_le_Q.trans inf_le_left).trans (X.Q_le_edgeSylow_left (h - 1))))
  have hSylm : IsSylowTwoOf (X.edgeSylow (h - 1)) (X.Gi (h - 1)) :=
    X.isSylowTwoOf_edgeSylow_Gi (h - 1)
  have hle : centerOf (X.L h) ≤ centerOf (X.edgeSylow (h - 1)) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hcenter_le_Sm hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL : y ∈ X.L h := by
      have hmem := (X.isSylowTwoOf_edgeSylow_L_succ (h - 1)).1 hy
      simpa [show (h - 1) + 1 = h by ring] using hmem
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y hyL
  exact hle.trans (X.centerOf_sylow_le_Z H.char (h - 1) hSylm).1

private theorem centerOf_L_le_Z_succ (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hdH : X.HasB ((d₁ : ℤ) + 1) d₀) (h2d0 : 2 ≤ d₀) :
    centerOf (X.L ((d₁ : ℤ) + 1)) ≤ X.Z (((d₁ : ℤ) + 1) + 1) := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  have hZh_le : centerOf (X.L h) ≤ X.Z h := X.centerOf_L_le_Z H.char h
  have hZh_le_Q : X.Z h ≤ X.Q (h - 1) ⊓ X.Q (h + 1) :=
    X.Z_le_Q_inf_of_hasB hdH (by omega)
  have hcenter_le_Sp : centerOf (X.L h) ≤ X.edgeSylow h :=
    (hZh_le.trans ((hZh_le_Q.trans inf_le_right).trans (X.Q_le_edgeSylow (i := h))))
  have hSylp : IsSylowTwoOf (X.edgeSylow h) (X.Gi (h + 1)) :=
    X.isSylowTwoOf_edgeSylow_Gi_succ h
  have hle : centerOf (X.L h) ≤ centerOf (X.edgeSylow h) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hcenter_le_Sp hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL : y ∈ X.L h := (X.isSylowTwoOf_edgeSylow_L h).1 hy
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y hyL
  exact hle.trans (X.centerOf_sylow_le_Z H.char (h + 1) hSylp).1

private theorem Icc_subset_fixSet_centerOf_L
    {d₁ : ℕ} (hd1pos : 1 ≤ d₁) (hdHm : X.HasB (((d₁ : ℤ) + 1) - 1) d₁)
    (hdHp : X.HasB (((d₁ : ℤ) + 1) + 1) d₁)
    (hZm : centerOf (X.L ((d₁ : ℤ) + 1)) ≤ X.Z (((d₁ : ℤ) + 1) - 1))
    (hZp : centerOf (X.L ((d₁ : ℤ) + 1)) ≤ X.Z (((d₁ : ℤ) + 1) + 1)) :
    Set.Icc (0 : ℤ) ((2 * d₁ + 2 : ℕ) : ℤ) ⊆
      X.fixSet (centerOf (X.L ((d₁ : ℤ) + 1))) := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  intro j hj
  rw [Set.mem_Icc] at hj
  intro g hg
  by_cases hjm : j ≤ ((2 * d₁ : ℕ) : ℤ)
  · have hjm' : j ∈ X.fixSet (X.Z (h - 1)) := by
      rw [X.fixSet_Z (h - 1) hdHm, Set.mem_Icc]
      constructor <;> push_cast at hjm ⊢ <;> omega
    exact hjm' g (hZm hg)
  · push Not at hjm
    have hjp : j ∈ X.fixSet (X.Z (h + 1)) := by
      rw [X.fixSet_Z (h + 1) hdHp, Set.mem_Icc]
      constructor <;> push_cast at hjm ⊢ <;> omega
    exact hjp g (hZp hg)

private theorem r_eq_two_mul_add_two (H : X.Sec4Hyp s r)
    {d₁ : ℕ} (hd₁ : X.HasB 1 d₁)
    (hZLh : centerOf (X.L ((d₁ : ℤ) + 1)) ≠ ⊥)
    (hcover : Set.Icc (0 : ℤ) ((2 * d₁ + 2 : ℕ) : ℤ) ⊆
      X.fixSet (centerOf (X.L ((d₁ : ℤ) + 1)))) :
    r = 2 * d₁ + 2 := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  have harc : centerOf (X.L h) ≤ X.arcStab 0 (((2 * d₁ + 2 : ℕ) : ℤ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    exact hcover hj
  have hcenter2 : IsPGroup 2 (centerOf (X.L h)) :=
    (pCoreOf_isPGroup' (X.Gi h)).to_le ((X.centerOf_L_le_Z H.char h).trans (X.Z_le_Q h))
  have h2d1 : 2 * d₁ + 2 ≤ r := by
    let U : Subgroup G := centerOf (X.L h)
    have hU2 : IsPGroup 2 U := hcenter2
    have hUne : U ≠ ⊥ := hZLh
    have hUarc : U ≤ X.arcStab (0 : ℤ) (0 + ((2 * d₁ + 2 : ℕ) : ℤ)) := by
      simpa using harc
    have := X.le_r_of_fixes H hU2 hUne hUarc
    simpa using this
  have hrbounds := X.hasB_one_bounds H hd₁
  obtain ⟨hr2d, hrle2⟩ := hrbounds
  omega

private theorem centerOf_L_le_pCoreOf_arcStab (H : X.Sec4Hyp s r)
    {d₁ : ℕ}
    (hcover : Set.Icc (0 : ℤ) ((2 * d₁ + 2 : ℕ) : ℤ) ⊆
      X.fixSet (centerOf (X.L ((d₁ : ℤ) + 1))))
    (hr_eq : r = 2 * d₁ + 2) :
    centerOf (X.L ((d₁ : ℤ) + 1)) ≤ pCoreOf 2 (X.arcStab 0 ((r : ℤ))) := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  have harc : centerOf (X.L h) ≤ X.arcStab 0 (((2 * d₁ + 2 : ℕ) : ℤ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    exact hcover hj
  have hcenter2 : IsPGroup 2 (centerOf (X.L h)) :=
    (pCoreOf_isPGroup' (X.Gi h)).to_le ((X.centerOf_L_le_Z H.char h).trans (X.Z_le_Q h))
  have hcenter_le_arc : centerOf (X.L h) ≤ X.arcStab 0 ((r : ℤ)) := by
    rw [hr_eq]
    exact harc
  have h := X.le_pCoreOf_arcStab_r (H := H) (U := centerOf (X.L h)) (a := 0)
    hcenter2 (by simpa using hcenter_le_arc)
  simpa using h

private theorem centerOf_L_eq_pCoreOf_arcStab (H : X.Sec4Hyp s r)
    {d₁ : ℕ} (hZLh : centerOf (X.L ((d₁ : ℤ) + 1)) ≠ ⊥)
    (hle : centerOf (X.L ((d₁ : ℤ) + 1)) ≤ pCoreOf 2 (X.arcStab 0 ((r : ℤ)))) :
    centerOf (X.L ((d₁ : ℤ) + 1)) = pCoreOf 2 (X.arcStab 0 ((r : ℤ))) := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  have hKcenter : X.K ≤ Subgroup.normalizer (centerOf (X.L h) : Set G) :=
    (X.K_le_Gi h).trans (X.Gi_le_normalizer_centerOf_L h)
  have h := X.eq_of_le_pCoreOf_arcStab_r (H := H) (U := centerOf (X.L h)) (a := 0)
    hKcenter hZLh (by simpa using hle)
  simpa using h

private theorem card_centerOf_L_succ (H : X.Sec4Hyp s r)
    {d₁ : ℕ} (hZLh : centerOf (X.L ((d₁ : ℤ) + 1)) ≠ ⊥)
    (heq : centerOf (X.L ((d₁ : ℤ) + 1)) = pCoreOf 2 (X.arcStab 0 ((r : ℤ)))) :
    Nat.card (centerOf (X.L ((d₁ : ℤ) + 1))) = 2 ^ X.n 0 := by
  have hne : pCoreOf 2 (X.arcStab 0 ((r : ℤ))) ≠ ⊥ := by
    rw [← heq]
    exact hZLh
  have h := (X.pCoreOf_arcStab_r H 0 (by simpa using hne)).1
  simpa [heq] using h

private theorem card_centerOf_L_zero {d₀ d₁ : ℕ} (hd1 : d₀ + 1 = d₁) (hev : Even d₀)
    (hcard_h : Nat.card (centerOf (X.L ((d₁ : ℤ) + 1))) = 2 ^ X.n 0) :
    Nat.card (centerOf (X.L 0)) = 2 ^ X.n 0 := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  obtain ⟨k, hk⟩ := hev
  have hconj_center : centerOf (X.L h) = conjSub (X.τ ^ ((k : ℤ) + 1)) (centerOf (X.L 0)) := by
    have hh2 : h = 0 + 2 * ((k : ℤ) + 1) := by omega
    rw [hh2, X.centerOf_L_add]
  have := hcard_h
  rw [hconj_center, card_conjSub] at this
  exact this

private theorem card_centerOf_S (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hcard0 : Nat.card (centerOf (X.L 0)) = 2 ^ X.n 0) :
    Nat.card (centerOf (X.S)) = 2 ^ X.n 0 * 2 ^ X.n 0 ∧
      centerOf (X.L 0) ≤ centerOf (X.S) := by
  have hstep2 := X.s45_step2 H hd₀ hd₁ hna hev
  have hnat := hstep2.1
  have hSylL : IsSylowTwoOf X.S (X.L 0) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_L 0
  have hSylG0 : IsSylowTwoOf X.S (X.Gi 0) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_Gi 0
  have hline : (centerOf (X.L 0)).relIndex
      (relCent (X.Z 0) (centerOf (X.L 0)) (X.S)) = 2 ^ X.n 0 := hnat.line X.S hSylL
  have hEZ : X.Z 0 ≤ Subgroup.normalizer (centerOf (X.L 0) : Set G) :=
    (X.Z_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_L 0)
  have hXS : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ Subgroup.centralizer (X.S : Set G) :=
    comm_Z_zero_le_centralizer_S X H hd₀ hev
  have hcenterS_le_rel : centerOf (X.S) ≤
      relCent (X.Z 0) (centerOf (X.L 0)) (X.S) := by
    intro y hy
    have hyZ : y ∈ X.Z 0 := (X.centerOf_sylow_le_Z H.char 0 hSylG0).1 hy
    rw [mem_relCent hEZ]
    refine ⟨hyZ, ?_⟩
    intro s hs
    have hyC : y ∈ Subgroup.centralizer (X.S : Set G) := (Subgroup.mem_inf.mp hy).2
    have hcomm : y * s = s * y :=
      (Subgroup.mem_centralizer_iff.mp hyC s hs).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact (centerOf (X.L 0)).one_mem
  have hrel_le_centerS : relCent (X.Z 0) (centerOf (X.L 0)) (X.S) ≤ centerOf (X.S) := by
    have hcommEq := hnat.comm_eq X.S hSylL
    have hleC : relCent (X.Z 0) (centerOf (X.L 0)) (X.S) ≤
        Subgroup.centralizer (X.S : Set G) := by
      rw [← hcommEq]
      refine sup_le ?_ ?_
      · rw [hstep2.2.2]
        exact hXS
      · intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hcL : c ∈ Subgroup.centralizer (X.L 0 : Set G) := (Subgroup.mem_inf.mp hc).2
        have hsL : s ∈ X.L 0 := by
          have h := (X.isSylowTwoOf_edgeSylow_L 0).1
            (by simpa [Setup.S, Setup.edgeSylow] using hs)
          simpa using h
        exact Subgroup.mem_centralizer_iff.mp hcL s hsL
    rw [← (X.centerOf_sylow_le_Z H.char 0 hSylG0).2]
    exact le_inf (fun _ hy => ((mem_relCent hEZ).mp hy).1) hleC
  have hrel_eq : relCent (X.Z 0) (centerOf (X.L 0)) (X.S) = centerOf (X.S) :=
    le_antisymm hrel_le_centerS hcenterS_le_rel
  have hcenter0_le_rel : centerOf (X.L 0) ≤
      relCent (X.Z 0) (centerOf (X.L 0)) (X.S) := by
    intro c hc
    have hcZ : c ∈ X.Z 0 := (X.centerOf_L_le_Z H.char 0) hc
    rw [mem_relCent hEZ]
    refine ⟨hcZ, ?_⟩
    intro s hs
    have hcL : c ∈ Subgroup.centralizer (X.L 0 : Set G) := (Subgroup.mem_inf.mp hc).2
    have hsL : s ∈ X.L 0 := by
      have h := (X.isSylowTwoOf_edgeSylow_L 0).1
        (by simpa [Setup.S, Setup.edgeSylow] using hs)
      simpa using h
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hcL s hsL).symm]
    exact (centerOf (X.L 0)).one_mem
  have hcenter_le_rel : centerOf (X.L 0) ≤ centerOf (X.S) :=
    hcenter0_le_rel.trans_eq hrel_eq
  have hline' : (centerOf (X.L 0)).relIndex (centerOf (X.S)) = 2 ^ X.n 0 := by
    rwa [hrel_eq] at hline
  have hmul := Subgroup.relIndex_mul_card (H := centerOf (X.L 0)) (K := centerOf (X.S))
  rw [hline', inf_eq_left.mpr hcenter_le_rel, hcard0] at hmul
  exact ⟨hmul.symm, hcenter_le_rel⟩

private theorem cube_le_card_of_inf_le {Y Yg Z : Subgroup G} [Finite ↥Z] {q : ℕ} (hq : 0 < q)
    (hY : Y ≤ Z) (hYg : Yg ≤ Z) (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hYc : Nat.card Y = q * q) (hYgc : Nat.card Yg = q * q)
    (hD : Nat.card ↥(Y ⊓ Yg) ≤ q) : q * q * q ≤ Nat.card Z := by
  let Y' : Subgroup ↥Z := Y.subgroupOf Z
  let Yg' : Subgroup ↥Z := Yg.subgroupOf Z
  have hcomm' : ∀ a ∈ Y', ∀ b ∈ Yg', a * b = b * a := by
    intro a _ b _
    apply Subtype.ext
    simpa using hZ (a : G) a.2 (b : G) b.2
  have hcardY' : Nat.card Y' = q * q := by
    rw [show Nat.card Y' = Nat.card Y from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv]
    exact hYc
  have hcardYg' : Nat.card Yg' = q * q := by
    rw [show Nat.card Yg' = Nat.card Yg from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYg).toEquiv]
    exact hYgc
  have hinf' : Y' ⊓ Yg' = (Y ⊓ Yg).subgroupOf Z := by
    ext x
    simp [Y', Yg', Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hsup' : Y' ⊔ Yg' = (Y ⊔ Yg).subgroupOf Z := (Subgroup.subgroupOf_sup hY hYg).symm
  have hcardD' : Nat.card ↥(Y' ⊓ Yg') = Nat.card ↥(Y ⊓ Yg) := by
    rw [hinf']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hY)).toEquiv
  have hcardSup' : Nat.card ↥(Y' ⊔ Yg') = Nat.card ↥(Y ⊔ Yg) := by
    rw [hsup']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hY hYg)).toEquiv
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Y' Yg' hcomm').1
  rw [hcardY', hcardYg', hcardD', hcardSup'] at hcard
  have h1 : q * q * q * q ≤ Nat.card ↥(Y ⊔ Yg) * q := by
    calc q * q * q * q = q * q * (q * q) := by ring
      _ = Nat.card ↥(Y ⊔ Yg) * Nat.card ↥(Y ⊓ Yg) := hcard.symm
      _ ≤ Nat.card ↥(Y ⊔ Yg) * q := Nat.mul_le_mul le_rfl hD
  exact (Nat.le_of_mul_le_mul_right h1 hq).trans
    (Subgroup.card_le_of_le (sup_le hY hYg))

private theorem cube_le_card_Z_one (H : X.Sec4Hyp s r)
    (hcard0 : Nat.card (centerOf (X.L 0)) = 2 ^ X.n 0)
    (hYcard : Nat.card (centerOf (X.S)) = 2 ^ X.n 0 * 2 ^ X.n 0)
    (hcenter_le_Y : centerOf (X.L 0) ≤ centerOf (X.S)) :
    2 ^ X.n 0 * 2 ^ X.n 0 * 2 ^ X.n 0 ≤ Nat.card ↥(X.Z 1) := by
  haveI hfinZ1 : Finite ↥(X.Z 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 1) (X.Z_le_Gi 1)
  haveI hfinY : Finite ↥(centerOf (X.S)) :=
    finite_of_le_stabilizer X.hyp (H := centerOf (X.S))
      ((inf_le_left : centerOf (X.S) ≤ X.S).trans
        (by simpa [Setup.S, Setup.edgeSylow] using
          (X.isSylowTwoOf_edgeSylow 0).1 |>.trans inf_le_left))
  have hSylG1 : IsSylowTwoOf X.S (X.Gi 1) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_Gi_succ 0
  have hSyl1G1 : IsSylowTwoOf (X.edgeSylow 1) (X.Gi 1) :=
    X.isSylowTwoOf_edgeSylow_Gi 1
  have hYleZ1 : centerOf (X.S) ≤ X.Z 1 := (X.centerOf_sylow_le_Z H.char 1 hSylG1).1
  obtain ⟨g, hgL, hg02⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).trans
    (X.vert 0) (X.vert 2) (by simpa using (X.adj 0).symm) (X.adj 1)
  have hconjS : conjSub g (X.S) = X.edgeSylow 1 := by
    rw [← X.edgeSylow_zero]
    exact X.conjSub_edgeSylow_swap (by simpa using hg02)
      (by simpa using MulAction.mem_stabilizer_iff.mp (X.L_le_Gi 1 hgL))
  have hYg_eq : conjSub g (centerOf (X.S)) = centerOf (X.edgeSylow 1) := by
    rw [← centerOf_conjSub g (X.S), hconjS]
  have hYgleZ1 : conjSub g (centerOf (X.S)) ≤ X.Z 1 := by
    rw [hYg_eq]
    exact (X.centerOf_sylow_le_Z H.char 1 hSyl1G1).1
  have hLsup : X.L 1 = X.S ⊔ conjSub g (X.S) := by
    rw [← X.edgeSylow_sup_edgeSylow 1, hconjS]
    rfl
  have hD_le_center1 : centerOf (X.S) ⊓ conjSub g (centerOf (X.S)) ≤ centerOf (X.L 1) := by
    intro d hd
    obtain ⟨hdY, hdYg⟩ := Subgroup.mem_inf.mp hd
    have hdZ1 : d ∈ X.Z 1 := hYleZ1 hdY
    have hdL1 : d ∈ X.L 1 := X.Q_le_L 1 (X.Z_le_Q 1 hdZ1)
    refine Subgroup.mem_inf.mpr ⟨hdL1, ?_⟩
    have hdS : d ∈ Subgroup.centralizer (X.S : Set G) := (Subgroup.mem_inf.mp hdY).2
    have hdYg' : d ∈ centerOf (X.edgeSylow 1) := by rwa [hYg_eq] at hdYg
    have hdSg : d ∈ Subgroup.centralizer (conjSub g (X.S) : Set G) := by
      rw [hconjS]
      exact (Subgroup.mem_inf.mp hdYg').2
    have hzpS : Subgroup.zpowers d ≤ Subgroup.centralizer (X.S : Set G) :=
      Subgroup.zpowers_le.mpr hdS
    have hzpSg : Subgroup.zpowers d ≤ Subgroup.centralizer (conjSub g (X.S) : Set G) :=
      Subgroup.zpowers_le.mpr hdSg
    have hzp : Subgroup.zpowers d ≤ Subgroup.centralizer (X.L 1 : Set G) := by
      rw [hLsup]
      exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hzpS hzpSg
    exact Subgroup.mem_centralizer_iff.mp (hzp (Subgroup.mem_zpowers d))
  have hD_bot : (centerOf (X.S) ⊓ conjSub g (centerOf (X.S))) ⊓ centerOf (X.L 0) = ⊥ := by
    apply le_bot_iff.mp
    calc (centerOf (X.S) ⊓ conjSub g (centerOf (X.S))) ⊓ centerOf (X.L 0)
        ≤ centerOf (X.L 1) ⊓ centerOf (X.L 0) := inf_le_inf hD_le_center1 le_rfl
      _ = ⊥ := by
        rw [inf_comm]
        have h := X.centerOf_L_inf_succ H.char 0
        simpa using h
  have hD_le_Y : centerOf (X.S) ⊓ conjSub g (centerOf (X.S)) ≤ centerOf (X.S) := inf_le_left
  have hcardD : Nat.card ↥(centerOf (X.S) ⊓ conjSub g (centerOf (X.S))) ≤
      2 ^ X.n 0 := by
    have h := CFSG.card_mul_card_le_of_inf_eq_bot
      (A := centerOf (X.S))
      (D := centerOf (X.S) ⊓ conjSub g (centerOf (X.S)))
      (D' := centerOf (X.L 0)) hD_le_Y hcenter_le_Y hD_bot
    rw [hYcard, hcard0] at h
    exact Nat.le_of_mul_le_mul_right h (by positivity)
  exact cube_le_card_of_inf_le (by positivity) hYleZ1 hYgleZ1 (X.Z_commute 1) hYcard
    (by rw [card_conjSub]; exact hYcard) hcardD

private theorem relIndex_Z_one_inf_Q_le (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1)) :
    (X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1)).relIndex (X.Z 1) ≤ 2 ^ X.n 0 := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  have hodd1 : Odd d₁ := (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
  have hd1pos : 1 ≤ d₁ := by
    obtain ⟨k, hk⟩ := hodd1
    omega
  have hA2 : IsPGroup 2 (X.Z 1) := (pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)
  have hA_Q : X.Z 1 ≤ X.Q (h - 1) := by
    have hZGi : X.Z 1 ≤ X.Gi (h - 1) := by
      have hfix := hd₁.1 ((d₁ : ℤ) - 1) (by omega)
      have hh1 : 1 + ((d₁ : ℤ) - 1) = h - 1 := by rw [hhdef]; ring
      simpa [hh1] using hfix
    have hadjL : Γ.Adj (X.vert (h - 1)) (X.vert (h - 2)) := by
      simpa [show (h - 2) + 1 = h - 1 by ring] using (X.adj (h - 2)).symm
    have hadjR : Γ.Adj (X.vert (h - 1)) (X.vert h) := by
      simpa [show (h - 1) + 1 = h by ring] using X.adj (h - 1)
    have hne : X.vert (h - 2) ≠ X.vert h := by
      intro heq
      have := X.vert_injective heq
      omega
    refine le_pCoreOf_of_isPGroup_fixes_two X.hyp hA2 hZGi hadjL hadjR hne ?_ ?_
    · intro y hy
      have hfix := hd₁.1 ((d₁ : ℤ) - 2) (by omega)
      have hy' : y ∈ X.Gi (1 + ((d₁ : ℤ) - 2)) := hfix hy
      have hh2 : 1 + ((d₁ : ℤ) - 2) = h - 2 := by rw [hhdef]; ring
      simpa [hh2] using (MulAction.mem_stabilizer_iff.mp hy')
    · intro y hy
      have hfix := hd₁.1 (d₁ : ℤ) (by simp)
      have hy' : y ∈ X.Gi (1 + (d₁ : ℤ)) := hfix hy
      have hh3 : 1 + (d₁ : ℤ) = h := by rw [hhdef]; ring
      simpa [hh3] using (MulAction.mem_stabilizer_iff.mp hy')
  have hA_B : X.Z 1 ≤ X.edgeSylow (h - 1) := hA_Q.trans (X.Q_le_edgeSylow_left (h - 1))
  have hCrelB : (X.Q h).relIndex (X.edgeSylow (h - 1)) = 2 ^ X.n 0 := by
    obtain ⟨m, hm⟩ := hodd1
    have hrel := X.relIndex_Q_succ_edgeSylow (h - 1)
    rw [show (h - 1) + 1 = h by ring, show X.n h = X.n 0 by
      rw [show h = 0 + 2 * ((m : ℤ) + 1) by rw [hhdef]; omega]; exact X.n_add _ 0] at hrel
    simpa using hrel
  rw [Subgroup.inf_relIndex_left]
  exact (Subgroup.relIndex_le_of_le_right hA_B (by rw [hCrelB]; positivity)).trans hCrelB.le

private theorem relIndex_Z_one_inf_Q_reflect_le (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1)) :
    (X.Z 1 ⊓ X.Q (2 - ((d₁ : ℤ) + 1))).relIndex (X.Z 1) ≤ 2 ^ X.n 0 := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  have h1 := relIndex_Z_one_inf_Q_le X H hd₀ hd₁ hna
  obtain ⟨t, htL1, htref, ht2⟩ := X.exists_reflection_oTwoRes H 1
  have ht1 : t • X.vert 1 = X.vert 1 := by
    simpa using htref 0
  have hth : t • X.vert h = X.vert (2 - h) := by
    have href := htref (d₁ : ℤ)
    have hh1 : (1 : ℤ) + (d₁ : ℤ) = h := by omega
    have hh2 : (1 : ℤ) - (d₁ : ℤ) = 2 - h := by omega
    simpa [hh1, hh2] using href
  have hZ1 : conjSub t (X.Z 1) = X.Z 1 := by
    rw [← Setup.Z_smul (X := X) (Y := X) ht1]
  have hQ : conjSub t (X.Q h) = X.Q (2 - h) := by
    rw [← Setup.Q_smul (X := X) (Y := X) hth]
  have hidx := CFSG.Quasithin.F9.relIndex_conjSub t (X.Z 1 ⊓ X.Q h) (X.Z 1)
  rw [conjSub_inf, hZ1, hQ] at hidx
  rw [hidx]
  exact h1

private theorem two_pow_le_card_Z_one_inf_Q_inf_Q (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hZ1card : 2 ^ X.n 0 * 2 ^ X.n 0 * 2 ^ X.n 0 ≤ Nat.card ↥(X.Z 1)) :
    2 ^ X.n 0 ≤ Nat.card ↥((X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1)) ⊓
      (X.Z 1 ⊓ X.Q (2 - ((d₁ : ℤ) + 1)))) := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  let P : Subgroup G := (X.Z 1 ⊓ X.Q h) ⊓ (X.Z 1 ⊓ X.Q (2 - h))
  have hPle : P ≤ X.Z 1 := (inf_le_left.trans inf_le_left)
  have hidx : P.relIndex (X.Z 1) ≤ 2 ^ X.n 0 * 2 ^ X.n 0 := by
    have hinf := Subgroup.relIndex_inf_le (H := X.Z 1 ⊓ X.Q h)
      (K := X.Z 1 ⊓ X.Q (2 - h)) (L := X.Z 1)
    have h1 := relIndex_Z_one_inf_Q_le X H hd₀ hd₁ hna
    have h2 := relIndex_Z_one_inf_Q_reflect_le X H hd₀ hd₁ hna
    calc P.relIndex (X.Z 1) ≤ (X.Z 1 ⊓ X.Q h).relIndex (X.Z 1) *
        (X.Z 1 ⊓ X.Q (2 - h)).relIndex (X.Z 1) := hinf
      _ ≤ 2 ^ X.n 0 * 2 ^ X.n 0 := Nat.mul_le_mul h1 h2
  have hmul := Subgroup.relIndex_mul_card (H := P) (K := X.Z 1)
  rw [inf_eq_left.mpr hPle] at hmul
  have h3 : 2 ^ X.n 0 * 2 ^ X.n 0 * 2 ^ X.n 0 ≤
      (2 ^ X.n 0 * 2 ^ X.n 0) * Nat.card ↥P := by
    calc 2 ^ X.n 0 * 2 ^ X.n 0 * 2 ^ X.n 0 ≤ Nat.card ↥(X.Z 1) := hZ1card
      _ = P.relIndex (X.Z 1) * Nat.card ↥P := hmul.symm
      _ ≤ (2 ^ X.n 0 * 2 ^ X.n 0) * Nat.card ↥P := Nat.mul_le_mul hidx le_rfl
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

private theorem false_of_two_pow_le_card_Z_one_inf (H : X.Sec4Hyp s r)
    {d₁ : ℕ} (hd₁ : X.HasB 1 d₁) (hodd1 : Odd d₁)
    (hr_eq : r = 2 * d₁ + 2) (hsr : s ≤ r)
    (hPcard : 2 ^ X.n 0 ≤ Nat.card ↥((X.Z 1 ⊓ X.Q ((d₁ : ℤ) + 1)) ⊓
      (X.Z 1 ⊓ X.Q (2 - ((d₁ : ℤ) + 1))))) :
    False := by
  set h : ℤ := (d₁ : ℤ) + 1 with hhdef
  let P : Subgroup G := (X.Z 1 ⊓ X.Q h) ⊓ (X.Z 1 ⊓ X.Q (2 - h))
  have hPcard' : 2 ^ X.n 0 ≤ Nat.card ↥P := hPcard
  have hPleZ1 : P ≤ X.Z 1 := inf_le_left.trans inf_le_left
  have hPleQh : P ≤ X.Q h := inf_le_left.trans inf_le_right
  have hPleQ2h : P ≤ X.Q (2 - h) := inf_le_right.trans inf_le_right
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard'
    have := Nat.one_lt_two_pow (n := X.n 0) (by have := H.two_le_n 0; omega)
    omega
  have hP2 : IsPGroup 2 P :=
    (pCoreOf_isPGroup' (X.Gi 1)).to_le (hPleZ1.trans (X.Z_le_Q 1))
  have hfix_arc : P ≤ X.arcStab (1 - h) ((1 - h) + (r : ℤ)) := by
    refine X.le_arcStab_of_fixSet ?_
    intro j hj
    rw [Set.mem_Icc] at hj
    intro p hp
    by_cases hle : j ≤ h
    · by_cases hleft : j = 1 - h
      · subst hleft
        have hfixQ : ∀ q ∈ X.Q (2 - h), q • X.vert (1 - h) = X.vert (1 - h) := by
          intro q hq
          have hadj : Γ.Adj (X.vert (2 - h)) (X.vert (1 - h)) := by
            simpa [show (1 - h) + 1 = 2 - h by ring] using (X.adj (1 - h)).symm
          exact X.Q_fixes_neighbors_vert (2 - h) (X.vert (1 - h)) hadj q hq
        exact hfixQ p (hPleQ2h hp)
      · have hmem : j ∈ X.fixSet (X.Z 1) := by
          rw [X.fixSet_Z 1 hd₁]
          rw [Set.mem_Icc]
          constructor <;> omega
        exact hmem p (hPleZ1 hp)
    · push Not at hle
      have hjeq : j = h + 1 := by omega
      subst hjeq
      have hfixQ : ∀ q ∈ X.Q h, q • X.vert (h + 1) = X.vert (h + 1) := by
        intro q hq
        exact X.Q_fixes_neighbors_vert h (X.vert (h + 1)) (by simpa using X.adj h) q hq
      exact hfixQ p (hPleQh hp)
  have hPcore : P ≤ pCoreOf 2 (X.arcStab (1 - h) ((1 - h) + (r : ℤ))) :=
    X.le_pCoreOf_arcStab_r H hP2 hfix_arc
  have hPne' : pCoreOf 2 (X.arcStab (1 - h) ((1 - h) + (r : ℤ))) ≠ ⊥ := by
    intro hbot
    exact hPne (le_bot_iff.mp (hbot ▸ hPcore))
  obtain ⟨-, -, -, -, hRight⟩ := X.pCoreOf_arcStab_r H (1 - h) hPne'
  have hends := (H.ends_even (1 - h) r hsr).1 hRight
  have hodd : Odd (1 - h + (r : ℤ)) := by
    rw [hr_eq]
    obtain ⟨m, hm⟩ := hodd1
    have : 1 - ((d₁ : ℤ) + 1) + ((2 * d₁ + 2 : ℕ) : ℤ) = (d₁ : ℤ) + 2 := by omega
    rw [this]
    exact ⟨m + 1, by omega⟩
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨k, hk⟩ := hends
  omega

theorem s45_step4 (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    centerOf (X.L 0) = ⊥ := by
  by_contra hZL
  have hd1eq := (X.s45_step1 H hd₀ hd₁ hna hev).1
  have h2d0 : 2 ≤ d₀ := by
    have h1 := X.one_le_of_hasB hd₀
    obtain ⟨k, hk⟩ := hev
    omega
  have hdZ : X.HasB ((d₀ : ℤ)) d₀ := hasB_self_of_even X H hd₀ hev
  have hdH : X.HasB ((d₁ : ℤ) + 1) d₀ := by
    refine (X.hasB_iff_of_even (i := (d₁ : ℤ) + 1) (j := (d₀ : ℤ)) ?_ d₀).mpr hdZ
    exact ⟨1, by omega⟩
  have hodd1 : Odd d₁ := (X.s45_lt_odd_of_not_comm_le H hd₀ hd₁ hna).2.1
  have hdHm : X.HasB (((d₁ : ℤ) + 1) - 1) d₁ := by
    refine (X.hasB_iff_of_even (i := ((d₁ : ℤ) + 1) - 1) (j := 1) ?_ d₁).mpr hd₁
    obtain ⟨m, hm⟩ := hodd1
    exact ⟨m, by omega⟩
  have hdHp : X.HasB (((d₁ : ℤ) + 1) + 1) d₁ := by
    refine (X.hasB_iff_of_even (i := ((d₁ : ℤ) + 1) + 1) (j := 1) ?_ d₁).mpr hd₁
    obtain ⟨m, hm⟩ := hodd1
    exact ⟨m + 1, by omega⟩
  have hd1pos : 1 ≤ d₁ := by omega
  have hZLh := centerOf_L_succ_ne_bot (X := X) (d₁ := d₁) hd1eq hev hZL
  have hZm := centerOf_L_le_Z_pred X H (d₀ := d₀) hdH h2d0
  have hZp := centerOf_L_le_Z_succ X H (d₀ := d₀) hdH h2d0
  have hcover := Icc_subset_fixSet_centerOf_L X hd1pos hdHm hdHp hZm hZp
  have hr_eq := r_eq_two_mul_add_two X H hd₁ hZLh hcover
  have hleQ := centerOf_L_le_pCoreOf_arcStab X H hcover hr_eq
  have heqQ := centerOf_L_eq_pCoreOf_arcStab X H hZLh hleQ
  have hcard_h := card_centerOf_L_succ X H hZLh heqQ
  have hcard0 := card_centerOf_L_zero (X := X) (d₀ := d₀) (d₁ := d₁) hd1eq hev hcard_h
  obtain ⟨hYcard, hcenter_le_Y⟩ := card_centerOf_S X H hd₀ hd₁ hna hev hcard0
  have hZ1card := cube_le_card_Z_one X H hcard0 hYcard hcenter_le_Y
  have hsr : s ≤ r := by
    by_contra h
    have hrs : r < s := Nat.lt_of_not_ge h
    have hle : r + 1 ≤ s := Nat.succ_le_of_lt hrs
    have hsle : s ≤ r + 1 := (Nat.sub_le_iff_le_add).mp H.le_r
    have hseq : s = r + 1 := le_antisymm hsle hle
    exact hb hseq.symm
  have hPcard := two_pow_le_card_Z_one_inf_Q_inf_Q X H hd₀ hd₁ hna hZ1card
  exact false_of_two_pow_le_card_Z_one_inf X H hd₁ hodd1 hr_eq hsr hPcard

private theorem s45_step56 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ} (hd₀ : X.HasB 0 d₀)
    (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) :
    (d₀ = 2 ∧ d₁ = 3 ∧ (r = 6 ∨ r = 8)) ∨ (d₀ = 4 ∧ d₁ = 5 ∧ r = 12) := by
  have hstep1 := X.s45_step1 H hd₀ hd₁ hna hev
  obtain ⟨hd1, h2d, hrle⟩ := hstep1
  have hP0 := X.s45_Z_zero_not_central H hd₀ hd₁ hna hev
  have hdZ : X.HasB ((d₀ : ℤ)) d₀ := hasB_self_of_even X H hd₀ hev
  have hXinf : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ X.Z 0 ⊓ X.Z ((d₀ : ℤ)) :=
    commutator_Z_zero_Z_le_inf X hd₀ hdZ
  have hXne : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≠ ⊥ := hP0.2
  have hfixunion : Set.Icc (-(d₀ : ℤ)) ((2 * d₀ : ℕ) : ℤ) ⊆
      X.fixSet (⁅X.Z 0, X.Z ((d₀ : ℤ))⁆) := by
    intro j hj
    rw [Set.mem_Icc] at hj
    intro g hg
    by_cases hjd : j ≤ (d₀ : ℤ)
    · have hj0 : j ∈ X.fixSet (X.Z 0) := by
        rw [X.fixSet_Z 0 hd₀]
        constructor <;> omega
      exact hj0 g (hXinf hg).1
    · push Not at hjd
      have hj2 : (0 : ℤ) ≤ j := by omega
      have hj0 : j ∈ X.fixSet (X.Z ((d₀ : ℤ))) := by
        rw [X.fixSet_Z ((d₀ : ℤ)) hdZ]
        constructor <;> omega
      exact hj0 g (hXinf hg).2
  have hXarc : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤
      X.arcStab (-(d₀ : ℤ)) (-(d₀ : ℤ) + ((3 * d₀ : ℕ) : ℤ)) := by
    apply X.le_arcStab_of_fixSet
    intro j hj
    exact hfixunion (by
      rw [Set.mem_Icc] at hj ⊢
      push_cast at hj ⊢
      omega)
  have hXQ : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ X.Q 0 :=
    (hXinf.trans inf_le_left).trans (X.Z_le_Q 0)
  have hX2 : IsPGroup 2 ↥(⁅X.Z 0, X.Z ((d₀ : ℤ))⁆) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le hXQ
  have h3d : 3 * d₀ ≤ r := X.le_r_of_fixes H hX2 hXne hXarc
  have hd0le4 : d₀ ≤ 4 := by omega
  have hd0ge1 : 1 ≤ d₀ := X.one_le_of_hasB hd₀
  obtain ⟨k, hk⟩ := hev
  obtain ⟨m, hm⟩ := H.even_r
  rcases (by omega : d₀ = 2 ∨ d₀ = 4) with h2 | h4
  · left
    refine ⟨h2, by omega, ?_⟩
    omega
  · right
    refine ⟨h4, by omega, by omega⟩

private theorem s45_comm_Z_eq_centerOf (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    ⁅X.Z 0, X.Z d₀⁆ = centerOf X.S ∧
      ⁅X.Z 0, X.Z d₀⁆ = centerOf (X.edgeSylow ((d₀ : ℤ) - 1)) := by
  have hZL : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
  have hstep2 := X.s45_step2 H hd₀ hd₁ hna hev
  have hnat := hstep2.1
  have hSylG0 : IsSylowTwoOf X.S (X.Gi 0) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_Gi 0
  have hSylS : IsSylowTwoOf X.S (X.L 0) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_L 0
  have hrel_eq : relCent (X.Z 0) (⊥ : Subgroup G) (X.S) = centerOf X.S :=
    (relCent_Z_zero_bot X X.S).trans (X.centerOf_sylow_le_Z H.char 0 hSylG0).2
  have hcommEq := hnat.comm_eq X.S hSylS
  rw [hZL, hrel_eq] at hcommEq
  rw [sup_bot_eq] at hcommEq
  have hfirst : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ = centerOf X.S := by
    rw [← hstep2.2.2]
    exact hcommEq
  constructor
  · exact hfirst
  ·
    obtain ⟨k, hk⟩ := hev
    obtain ⟨t, ht, htref, ht2⟩ := X.exists_reflection_oTwoRes H (k : ℤ)
    have ht0 : t • X.vert 0 = X.vert (d₀ : ℤ) := by
      have h := htref (-(k : ℤ))
      simpa [show (k : ℤ) + -(k : ℤ) = 0 by ring,
        show (k : ℤ) - -(k : ℤ) = (d₀ : ℤ) by omega] using h
    have htd0 : t • X.vert (d₀ : ℤ) = X.vert 0 := by
      have h := htref (k : ℤ)
      simpa [show (k : ℤ) + (k : ℤ) = (d₀ : ℤ) by omega,
        show (k : ℤ) - (k : ℤ) = 0 by ring] using h
    have ht1 : t • X.vert 1 = X.vert ((d₀ : ℤ) - 1) := by
      have h := htref ((1 : ℤ) - (k : ℤ))
      simpa [show (k : ℤ) + ((1 : ℤ) - (k : ℤ)) = 1 by ring,
        show (k : ℤ) - ((1 : ℤ) - (k : ℤ)) = (d₀ : ℤ) - 1 by omega] using h
    have hZ_conj : conjSub t (X.Z 0) = X.Z (d₀ : ℤ) := by
      rw [← Setup.Z_smul (X := X) (Y := X) ht0]
    have hZd0_conj : conjSub t (X.Z (d₀ : ℤ)) = X.Z 0 := by
      rw [← Setup.Z_smul (X := X) (Y := X) htd0]
    have hS_conj : conjSub t (X.edgeSylow 0) = X.edgeSylow ((d₀ : ℤ) - 1) :=
      X.conjSub_edgeSylow_swap (by rw [sub_add_cancel]; exact ht0)
        (by rw [zero_add]; exact ht1)
    have hS_conj' : conjSub t (X.S) = X.edgeSylow ((d₀ : ℤ) - 1) := by
      rw [← X.edgeSylow_zero]
      exact hS_conj
    have hcenter_conj : conjSub t (centerOf X.S) = centerOf (X.edgeSylow ((d₀ : ℤ) - 1)) := by
      rw [← centerOf_conjSub t X.S, hS_conj']
    have hcomm_conj : conjSub t ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ = ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ := by
      change Subgroup.map (MulAut.conj t).toMonoidHom ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ = _
      rw [Subgroup.map_commutator (f := (MulAut.conj t).toMonoidHom)]
      change ⁅conjSub t (X.Z 0), conjSub t (X.Z (d₀ : ℤ))⁆ = _
      rw [hZ_conj, hZd0_conj, Subgroup.commutator_comm]
    rw [← hfirst] at hcenter_conj
    rw [hcomm_conj] at hcenter_conj
    exact hcenter_conj

private theorem le_centralizer_L_two (H : X.Sec4Hyp s r) {U : Subgroup G} (h1 : U ≤ X.Z 1)
    (h3 : U ≤ X.Z 3) : U ≤ Subgroup.centralizer (X.L 2 : Set G) := by
  have hQ1c : U ≤ Subgroup.centralizer (X.Q 1 : Set G) :=
    h1.trans ((X.Z_le_center 1).trans inf_le_right)
  have hQ3c : U ≤ Subgroup.centralizer (X.Q 3 : Set G) :=
    h3.trans ((X.Z_le_center 3).trans inf_le_right)
  have hQ21 : U ≤ Subgroup.centralizer (X.Q 2 ⊓ X.Q 1 : Set G) :=
    hQ1c.trans (Subgroup.centralizer_le (by
      intro x hx
      exact (Subgroup.mem_inf.mp hx).2))
  have hQ23 : U ≤ Subgroup.centralizer (X.Q 2 ⊓ X.Q 3 : Set G) :=
    hQ3c.trans (Subgroup.centralizer_le (by
      intro x hx
      exact (Subgroup.mem_inf.mp hx).2))
  have hQ2c : U ≤ Subgroup.centralizer (X.Q 2 : Set G) := by
    have hsup := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
      (K := U) (A := X.Q 2 ⊓ X.Q 1) (B := X.Q 2 ⊓ X.Q 3) hQ21 hQ23
    have hgen := (X.Q_quot H.char H.sing (le_trans (by norm_num) H.five_le) 2).2.2.2.2.2
    rw [hgen, sup_comm]
    exact hsup
  have hQsup1 : X.Q 1 ⊔ X.Q 2 = X.edgeSylow 1 :=
    sup_pCoreOf_eq_edgeSylow X.hyp (X.adj 1) (X.Q_ne_bot H.char 1)
  have hE1c : U ≤ Subgroup.centralizer (X.edgeSylow 1 : Set G) := by
    have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hQ1c hQ2c
    rwa [hQsup1] at h
  have hQsup2 : X.Q 2 ⊔ X.Q 3 = X.edgeSylow 2 :=
    sup_pCoreOf_eq_edgeSylow X.hyp (X.adj 2) (X.Q_ne_bot H.char 2)
  have hE2c : U ≤ Subgroup.centralizer (X.edgeSylow 2 : Set G) := by
    have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hQ2c hQ3c
    rwa [hQsup2] at h
  have hL2c : U ≤ Subgroup.centralizer (X.L 2 : Set G) := by
    have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hE1c hE2c
    have hL : X.edgeSylow 1 ⊔ X.edgeSylow 2 = X.L 2 := by
      simpa using X.edgeSylow_sup_edgeSylow 2
    rwa [hL] at h
  exact hL2c

private theorem s45_d₀_ne_four (H : X.Sec4Hyp s r)
    {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    d₀ ≠ 4 := by
  intro h4
  have hZL : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
  have hR1 := s45_comm_Z_eq_centerOf X H hd₀ hd₁ hna hev hb
  have hXne : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≠ ⊥ :=
    (X.s45_Z_zero_not_central H hd₀ hd₁ hna hev).2
  have hSylG1 : IsSylowTwoOf X.S (X.Gi 1) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_Gi_succ 0
  have hXZ1 : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≤ X.Z 1 := by
    rw [hR1.1]
    exact (X.centerOf_sylow_le_Z H.char 1 hSylG1).1
  have hXZ3 : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≤ X.Z 3 := by
    rw [hR1.2, h4]
    have hSylG3 : IsSylowTwoOf (X.edgeSylow ((4 : ℤ) - 1)) (X.Gi 3) := by
      simpa using X.isSylowTwoOf_edgeSylow_Gi ((4 : ℤ) - 1)
    exact (X.centerOf_sylow_le_Z H.char 3 hSylG3).1
  have hL2c := le_centralizer_L_two X H hXZ1 hXZ3
  have h56 := s45_step56 X H hd₀ hd₁ hna hev
  have hd1ge2 : 2 ≤ d₁ := by
    rcases h56 with ⟨h2, h3, hr⟩ | ⟨h4', h5, hr⟩
    · omega
    · omega
  have hXQ2 : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≤ X.Q 2 :=
    hXZ1.trans ((X.Z_le_Q_inf_of_hasB hd₁ hd1ge2).trans inf_le_right)
  have hQ2L : X.Q 2 ≤ X.L 2 := X.Q_le_L 2
  have hXleL2 : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≤ X.L 2 :=
    hXQ2.trans hQ2L
  have hcentL2 : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≤ centerOf (X.L 2) :=
    le_inf hXleL2 hL2c
  have hcentL2bot : centerOf (X.L 2) = ⊥ := by
    have hL2eq : X.L 2 = X.L (0 + 2 * 1) := by norm_num
    rw [hL2eq, X.centerOf_L_add]
    rw [conjSub_eq_bot_iff]
    exact hZL
  have hXbot : ⁅X.Z 0, X.Z (d₀ : ℤ)⁆ ≤ ⊥ := by
    simpa [hcentL2bot] using hcentL2
  exact hXne (le_bot_iff.mp hXbot)

theorem s45_step7 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) (h2 : d₀ = 2) :
    X.Z 1 = centerOf (X.L 1) ∧ X.Z 1 = ⁅X.Z 0, X.Z 2⁆ ∧
      Nat.card (X.Z 1) = 2 ^ X.n 0 := by
  have hZL : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
  have hR1 := s45_comm_Z_eq_centerOf X H hd₀ hd₁ hna hev hb
  have hstep2 := X.s45_step2 H hd₀ hd₁ hna hev
  have hnat := hstep2.1
  have hSylG1 : IsSylowTwoOf X.S (X.Gi 1) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_Gi_succ 0
  have hSylS : IsSylowTwoOf X.S (X.L 0) := by
    simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_L 0
  have hXeq : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ = centerOf X.S := hR1.1
  have hXeq2 : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ = centerOf (X.edgeSylow 1) := by
    simpa [h2] using hR1.2
  have hXcS : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ Subgroup.centralizer (X.S : Set G) := by
    rw [hXeq]
    exact inf_le_right
  have hXcE : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤
      Subgroup.centralizer (X.edgeSylow 1 : Set G) := by
    rw [hXeq2]
    exact inf_le_right
  have hXcL1 : ⁅X.Z 0, X.Z ((d₀ : ℤ))⁆ ≤ Subgroup.centralizer (X.L 1 : Set G) := by
    have h := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers hXcS hXcE
    have hL : X.S ⊔ X.edgeSylow 1 = X.L 1 := by
      have h := X.edgeSylow_sup_edgeSylow 1
      simpa [X.edgeSylow_zero, show (1 : ℤ) - 1 = 0 by ring] using h
    rwa [hL] at h
  have hLcent : X.L 1 ≤ Subgroup.centralizer (centerOf X.S : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    rwa [← hXeq]
  have hZ := X.Z_eq_centerOf_of_centralizes H.char 1 hSylG1 hLcent
  have hZ1X : X.Z 1 = ⁅X.Z 0, X.Z 2⁆ := by
    rw [hZ.1, ← hXeq, h2]
    norm_num
  have hcard : Nat.card (X.Z 1) = 2 ^ X.n 0 := by
    have hSylS0 : IsSylowTwoOf X.S (X.Gi 0) := by
      simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_Gi 0
    have hrel_eq : relCent (X.Z 0) (⊥ : Subgroup G) (X.S) = centerOf X.S :=
      (relCent_Z_zero_bot X X.S).trans (X.centerOf_sylow_le_Z H.char 0 hSylS0).2
    have hline := hnat.line X.S hSylS
    rw [hZL, hrel_eq, Subgroup.relIndex_bot_left] at hline
    rw [hZ.1]
    exact hline
  exact ⟨hZ.2, hZ1X, hcard⟩

private theorem Z_zero_inf_centralizer_eq (hZQ0 : X.Z 2 ⊔ X.Q 0 = X.S) (hZ2S : X.Z 2 ≤ X.S) :
    X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G) =
      X.Z 0 ⊓ Subgroup.centralizer (X.S : Set G) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hyZ, hyC⟩ := Subgroup.mem_inf.mp hy
    refine Subgroup.mem_inf.mpr ⟨hyZ, ?_⟩
    rw [← hZQ0]
    refine (CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
      (K := Subgroup.zpowers y) (A := X.Z 2) (B := X.Q 0) ?_ ?_)
      (Subgroup.mem_zpowers y)
    · exact Subgroup.zpowers_le.mpr hyC
    · refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (X.Z_le_center 0 hyZ)).2 q hq
  · intro y hy
    obtain ⟨hyZ, hyC⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨hyZ, Subgroup.centralizer_le hZ2S hyC⟩

theorem s45_step8 (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hna : ¬ ⁅X.Z 1, X.Z ((d₁ : ℤ) + 1)⁆ ≤ X.Z 1 ⊓ X.Z ((d₁ : ℤ) + 1))
    (hev : Even d₀) (hb : r + 1 ≠ s) :
    d₀ = 2 ∧ d₁ = 3 ∧ (r = 6 ∨ r = 8) ∧ ⁅X.Z 0, X.Z 2⁆ = X.Z 1 ∧
      X.Z 1 = X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G) := by
  have h56 := s45_step56 X H hd₀ hd₁ hna hev
  have hne4 := s45_d₀_ne_four X H hd₀ hd₁ hna hev hb
  rcases h56 with ⟨h2, h3, hr⟩ | ⟨h4, h5, hr⟩
  · have h7 := X.s45_step7 H hd₀ hd₁ hna hev hb h2
    refine ⟨h2, h3, hr, h7.2.1.symm, ?_⟩
    have hstep2 := X.s45_step2 H hd₀ hd₁ hna hev
    have hZL : centerOf (X.L 0) = ⊥ := X.s45_step4 H hd₀ hd₁ hna hev hb
    have hZQ0 : X.Z 2 ⊔ X.Q 0 = X.S := by
      simpa [h2] using hstep2.2.1
    have hZ2S : X.Z 2 ≤ X.S := by
      rw [← hZQ0]
      exact le_sup_left
    have hd2 : X.HasB 2 2 := by
      refine (X.hasB_iff_of_even (i := (2 : ℤ)) (j := 0) ?_ 2).mpr ?_
      · exact ⟨1, by norm_num⟩
      · simpa [h2] using hd₀
    have hZ2Gi0 : X.Z 2 ≤ X.Gi 0 := by
      intro g hg
      have h0 : (0 : ℤ) ∈ X.fixSet (X.Z 2) := by
        rw [X.fixSet_Z 2 hd2, Set.mem_Icc]
        constructor <;> norm_num
      exact MulAction.mem_stabilizer_iff.mpr (h0 g hg)
    have hZ1Z0 : X.Z 1 ≤ X.Z 0 := by
      rw [h7.2.1]
      have hnorm : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
        le_normalizer_Z_of_le_Gi X hZ2Gi0
      have h := Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm
      rwa [Subgroup.commutator_comm] at h
    have hSL1 : X.S ≤ X.L 1 := by
      have h := (X.isSylowTwoOf_edgeSylow_L_succ 0).1
      rwa [X.edgeSylow_zero] at h
    have hZ1cS : X.Z 1 ≤ Subgroup.centralizer (X.S : Set G) := by
      rw [h7.1]
      exact inf_le_right.trans (Subgroup.centralizer_le hSL1)
    have hZ1le : X.Z 1 ≤ X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G) :=
      le_inf hZ1Z0 (hZ1cS.trans (Subgroup.centralizer_le hZ2S))
    have hinf := Z_zero_inf_centralizer_eq X hZQ0 hZ2S
    have hSylS : IsSylowTwoOf X.S (X.L 0) := by
      simpa [Setup.S, Setup.edgeSylow] using X.isSylowTwoOf_edgeSylow_L 0
    have hline := hstep2.1.line X.S hSylS
    rw [hZL, Subgroup.relIndex_bot_left] at hline
    have hcardR : Nat.card (relCent (X.Z 0) (⊥ : Subgroup G) (X.S)) = 2 ^ X.n 0 := by
      simpa using hline
    have hRCEq := relCent_Z_zero_bot X X.S
    have hcard : Nat.card ↥(X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G)) =
        2 ^ X.n 0 := by
      rw [hinf, ← hRCEq]
      exact hcardR
    have hcardle : Nat.card ↥(X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G)) ≤
        Nat.card ↥(X.Z 1) :=
      hcard.trans_le (le_of_eq h7.2.2.symm)
    haveI hfinZ0 : Finite ↥(X.Z 0) :=
      finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
    haveI hfinR : Finite ↥(X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G)) :=
      Finite.of_injective
        (Subgroup.inclusion
          (inf_le_left : X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G) ≤ X.Z 0))
        (Subgroup.inclusion_injective
          (inf_le_left : X.Z 0 ⊓ Subgroup.centralizer (X.Z 2 : Set G) ≤ X.Z 0))
    exact Subgroup.eq_of_le_of_card_ge hZ1le hcardle
  · exact absurd h4 hne4

end Setup

end CFSG.Quasithin.St84
