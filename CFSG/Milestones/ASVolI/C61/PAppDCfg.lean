module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDCfg
public import CFSG.Milestones.ASVolI.C61.PBasic245Single

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC (FixΔ card_mul_fix_le)

variable {G : Type} [Group G] [Finite G]

structure GCfg (T M H S L : Subgroup G) where
  hcs : burnsideC56_CS G T M H S L
  U : Subgroup G
  hUdef : U = blockU0 S L
  P : PiS S U
  hB : P.im (baum S) = Estd
  hS : P.im S = Dstd
  hUQ : U ≤ pCoreOf 2 H
  hQ : H ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 H
  hUD : U ⊓ blockD S L = ⊥
  hQeq : pCoreOf 2 H = U ⊔ blockD S L
  hU1 : blockU L ≤ U

namespace GCfg

variable {T M H S L : Subgroup G} (C : GCfg T M H S L)
include C

theorem hSH : S ≤ H := C.hcs.sylow.le

theorem hQS : pCoreOf 2 H ≤ S := C56.pCoreOf_le_S C.hcs

theorem hUS : C.U ≤ S := C.hUQ.trans C.hQS

theorem hU : IsElemAbelian 2 C.U := C.P.isElemAbelian_U

theorem card_U : Nat.card ↥C.U = 16 := C.P.card_U

theorem Q_comm_U {q u : G} (hq : q ∈ pCoreOf 2 H) (hu : u ∈ C.U) : q * u = u * q := by
  rw [← C.hQ] at hq
  exact (Subgroup.mem_centralizer_iff.1 hq.2 u hu).symm

theorem aU_spec {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAS : A ≤ S) :
    IsElemAbelian 2 (gaU C.U A) ∧ Nat.card A ≤ Nat.card ↥(gaU C.U A) ∧
      gaU C.U A ≤ pCoreOf 2 H ∧ C.U ≤ gaU C.U A := by
  set K := A ⊓ Subgroup.centralizer (C.U : Set G) with hK
  have hKe : IsElemAbelian 2 K := B2F.isElemAbelian_mono inf_le_left hA
  have hcomm : ∀ k ∈ K, ∀ u ∈ C.U, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hB1e := B2F.isElemAbelian_sup_of_commute hKe C.hU hcomm
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(K ⊓ C.U) ≤
      Nat.card ↥(C.U ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA ha hx.1.1
  have h4 := C.P.card_im_mul hAS
  have h5 := C.P.card_fix hAS
  have h6 := C.card_U
  have h7 := card_mul_fix_le (C.P.im A) (C.P.im_elemAbelian hA).1 (C.P.im_elemAbelian hA).2
  have hbpos : 0 < Nat.card ↥(K ⊓ C.U) := Nat.card_pos
  rw [h5] at h3
  set p := Nat.card (C.P.im A)
  set f := Nat.card (FixΔ (C.P.im A))
  set b := Nat.card ↥(K ⊓ C.U)
  set a := Nat.card ↥(K ⊔ C.U)
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

theorem omegaOneCenter_le_pCoreOf : omegaOneCenterOf (thompsonJ S) ≤ pCoreOf 2 H := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
  obtain ⟨he, hcard, hle, -⟩ := C.aU_spec hA₀.2.1 hA₀.1
  have hmax : IsMaxElemAbelian S (gaU C.U A₀) :=
    ⟨sup_le (inf_le_left.trans hA₀.1) C.hUS, he, fun B hBS hBe => (hA₀.2.2 B hBS hBe).trans hcard⟩
  rw [(omegaOne_centralizer_thompsonJ S).2]
  exact (iInf₂_le (gaU C.U A₀) hmax).trans hle

theorem U_le_baum : C.U ≤ baum S := by
  refine le_inf C.hUS ?_
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact C.Q_comm_U (C.omegaOneCenter_le_pCoreOf hz) hu

end GCfg

end CFSG.QuasithinUnique.burnsideC56_P.AppD
