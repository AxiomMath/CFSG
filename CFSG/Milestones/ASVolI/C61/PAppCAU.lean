module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCAU
public import CFSG.Milestones.ASVolI.C61.PAppCSplit
public import CFSG.Milestones.ASVolI.C61.PAppCStd

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

structure Cfg (T M H S L : Subgroup G) where
  hcs : burnsideC56_CS G T M H S L
  hj : conjJoin S L = L
  h5 : IsAltType L 5
  P : A5Pi L
  hJ : P.im (thompsonJ S) = Estd
  hB : P.im (baum S) = Estd
  hS : P.im S = Dstd
  hX : P.im (L ⊔ baum S) = ⊤

theorem nonempty_cfg {T M H S L : Subgroup G} (hcs : burnsideC56_CS G T M H S L)
    (hj : conjJoin S L = L) (h5 : IsAltType L 5) : Nonempty (Cfg T M H S L) := by
  obtain ⟨P⟩ := nonempty_a5pi (C56.isShort hcs) h5
  obtain ⟨P', hJ, hB, hS, hX⟩ := a5_core_std hcs hj P
  exact ⟨⟨hcs, hj, h5, P', hJ, hB, hS, hX⟩⟩

namespace Cfg

variable {T M H S L : Subgroup G} (C : Cfg T M H S L)

include C in
theorem hL : IsShort2 L := C56.isShort C.hcs

include C in
theorem hSN : S ≤ Subgroup.normalizer (L : Set G) := C56.S_le_normalizer C.hj

include C in
theorem hSH : S ≤ H := C.hcs.sylow.le

include C in
theorem hQS : pCoreOf 2 H ≤ S := C56.pCoreOf_le_S C.hcs

include C in
theorem hUQ : blockU L ≤ pCoreOf 2 H := C56.blockU_le_pCoreOf C.hcs C.hj

include C in
theorem hUS : blockU L ≤ S := C.hUQ.trans C.hQS

include C in
theorem hU : IsElemAbelian 2 (blockU L) := isElemAbelian_blockU C.hL

include C in
theorem card_U : Nat.card ↥(blockU L) = 16 := C.P.card_blockU

include C in
theorem hQ : H ⊓ Subgroup.centralizer (blockU L : Set G) = pCoreOf 2 H :=
  C56.inf_centralizer_eq C.hcs C.hj

include C in
theorem Q_comm_U {q u : G} (hq : q ∈ pCoreOf 2 H) (hu : u ∈ blockU L) : q * u = u * q :=
  pCoreOf_comm_blockU C.hcs C.hj hq hu

include C in
theorem aU_spec {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAS : A ≤ S) :
    IsElemAbelian 2 (aU L A) ∧ Nat.card A ≤ Nat.card ↥(aU L A) ∧ aU L A ≤ pCoreOf 2 H ∧
      blockU L ≤ aU L A := by
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hAS.trans C.hSN
  set K := A ⊓ Subgroup.centralizer (blockU L : Set G) with hK
  have hKe : IsElemAbelian 2 K := B2F.isElemAbelian_mono inf_le_left hA
  have hcomm : ∀ k ∈ K, ∀ u ∈ blockU L, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hB1e := B2F.isElemAbelian_sup_of_commute hKe C.hU hcomm
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(K ⊓ blockU L) ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA ha hx.1.1
  have h4 := C.P.card_im_mul hAN
  have h5 := C.P.card_fix hAN
  have h6 := C.card_U
  have h7 := card_mul_fix_le (C.P.im A) (C.P.im_elemAbelian hA).1 (C.P.im_elemAbelian hA).2
  have hbpos : 0 < Nat.card ↥(K ⊓ blockU L) := Nat.card_pos
  rw [h5] at h3
  set p := Nat.card (C.P.im A)
  set f := Nat.card (FixΔ (C.P.im A))
  set b := Nat.card ↥(K ⊓ blockU L)
  set a := Nat.card ↥(K ⊔ blockU L)
  set k := Nat.card ↥K
  have h8 : Nat.card A ≤ a := by
    rw [← h4]
    have hab : a * b = k * 16 := by rw [h2, h6]
    have h9 : (k * p) * b ≤ a * b := by
      calc (k * p) * b ≤ (k * p) * f := Nat.mul_le_mul_left _ h3
        _ = k * (p * f) := by ring
        _ ≤ k * 16 := Nat.mul_le_mul_left _ h7
        _ = a * b := hab.symm
    have := Nat.le_of_mul_le_mul_right h9 hbpos
    nlinarith
  refine ⟨hB1e, h8, sup_le ?_ C.hUQ, le_sup_right⟩
  intro x hx
  rw [← C.hQ]
  exact ⟨C.hSH (hAS hx.1), hx.2⟩

include C in
theorem omegaOneCenter_le_pCoreOf : omegaOneCenterOf (thompsonJ S) ≤ pCoreOf 2 H := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
  obtain ⟨he, hcard, hle, -⟩ := C.aU_spec hA₀.2.1 hA₀.1
  have hmax : IsMaxElemAbelian S (aU L A₀) :=
    ⟨sup_le (inf_le_left.trans hA₀.1) C.hUS, he, fun B hBS hBe => (hA₀.2.2 B hBS hBe).trans hcard⟩
  rw [(omegaOne_centralizer_thompsonJ S).2]
  exact (iInf₂_le (aU L A₀) hmax).trans hle

include C in
theorem blockU_le_baum : blockU L ≤ baum S := by
  refine le_inf C.hUS ?_
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact C.Q_comm_U (C.omegaOneCenter_le_pCoreOf hz) hu

end Cfg

end CFSG.QuasithinUnique.burnsideC56_P.AppC
