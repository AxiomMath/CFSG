module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

variable {S : Type} [Group S] [Finite S]

@[expose] def NoCQAt (s : S) : Prop :=
  ∀ K : Subgroup S, s ∈ K → K ≤ Subgroup.centralizer {s} → IsQuasisimple K →
    IsType425 (K ⧸ aschbacherSolvableCore 3 K) → False

theorem noCQ425_of_at (h : ∀ s : S, orderOf s = 3 → NoCQAt s) : NoCQ425 S :=
  fun s K hs3 hsK hKs hKq hT => h s hs3 K hsK hKs hKq hT

theorem noCQAt_of_card_dvd {s : S} {M B : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M) (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : typeOrders425 M B = []) : NoCQAt s := by
  intro K _ hKs hKq hT
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hKs).trans hC)
  have := card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) hM0 hB hT hdvd
  rw [hfree] at this
  exact List.not_mem_nil this

theorem noCQAt_of_not_mem_commutator {s : S}
    (h : s ∉ ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆) :
    NoCQAt s := by
  intro K hsK hKs hKq _
  apply h
  haveI hKp : Group.IsPerfect K := hKq.1
  have hKK : ⁅K, K⁆ = K := Subgroup.commutator_eq_self (H := K)
  exact Subgroup.commutator_mono hKs hKs (hKK.symm ▸ hsK)

theorem exists_surjective_A6 {X : Type} [Group X] [Finite X] (hX : IsType425 X)
    (h : Nat.card X = 1080) :
    ∃ f : X →* alternatingGroup (Fin 6), Function.Surjective f := by
  have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rcases hX with hX | ⟨N, hN, -, ⟨eQ⟩⟩ | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩
  · exact absurd h (Sec13.Item131bProof.card_ne_of_isSLThreePi hX)
  · exact ⟨eQ.toMonoidHom.comp (QuotientGroup.mk' N),
      eQ.surjective.comp (QuotientGroup.mk'_surjective N)⟩
  all_goals
    exfalso
    have hcard : Nat.card X = Nat.card N * Nat.card (X ⧸ N) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup N).trans (mul_comm _ _)
    rw [Nat.card_congr eN.toEquiv, Nat.card_congr eQ.toEquiv, hZ3, h] at hcard
  · rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at hcard
    norm_num [Nat.factorial] at hcard
  · rw [KFacts.KS14.card_nativeM22] at hcard
    norm_num at hcard

theorem noCQAt_of_noA6 {s : S} {M B : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M) (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : ∀ t ∈ typeOrders425 M B, t = 1080)
    (hA6 : ∀ H : Subgroup S, H ≤ Subgroup.centralizer {s} →
      ∀ f : H →* alternatingGroup (Fin 6), ¬ Function.Surjective f) :
    NoCQAt s := by
  intro K _ hKs hKq hT
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hKs).trans hC)
  have h1080 := hfree _ (card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) hM0 hB hT hdvd)
  obtain ⟨f, hf⟩ := exists_surjective_A6 hT h1080
  exact hA6 K hKs (f.comp (QuotientGroup.mk' _))
    (hf.comp (QuotientGroup.mk'_surjective _))

theorem noCQAt_of_card_eq {s : S} {M B : ℕ}
    (hC : Nat.card (Subgroup.centralizer ({s} : Set S)) = M) (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : ∀ t ∈ typeOrders425 M B, t = M)
    (hnp : ⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆ ≠
      Subgroup.centralizer ({s} : Set S)) :
    NoCQAt s := by
  intro K _ hKs hKq hT
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hKs).trans hC.dvd)
  have hM := hfree _ (card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) hM0 hB hT hdvd)
  have hle : Nat.card (Subgroup.centralizer ({s} : Set S)) ≤ Nat.card K := by
    rw [hC, ← hM]
    exact Nat.le_of_dvd Nat.card_pos (card_theta_quot_dvd K)
  have hKC : K = Subgroup.centralizer ({s} : Set S) := Subgroup.eq_of_le_of_card_ge hKs hle
  apply hnp
  haveI hKp : Group.IsPerfect K := hKq.1
  rw [← hKC]
  exact Subgroup.commutator_eq_self (H := K)

variable {T : Type} [Group T] [Finite T]

theorem NoCQAt.of_mulEquiv (e : S ≃* T) {s : S} (h : NoCQAt (e s)) : NoCQAt s := by
  intro K hsK hKs hKq hT
  have eK : K ≃* K.map (e : S →* T) := K.equivMapOfInjective _ e.injective
  refine h (K.map (e : S →* T)) ⟨s, hsK, rfl⟩ ?_ (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq)
    (isType425_theta_congr eK hT)
  rw [← map_centralizer_singleton_equiv e s]
  exact Subgroup.map_mono hKs

theorem noCQ425_of_at_mulEquiv (e : S ≃* T) (h : ∀ t : T, orderOf t = 3 → NoCQAt t) :
    NoCQ425 S :=
  noCQ425_of_at fun s hs => NoCQAt.of_mulEquiv e (h (e s) (by rwa [MulEquiv.orderOf_eq]))

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
