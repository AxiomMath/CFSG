module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelH4Pieces
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Card
public import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Proj
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4H4Psl64_dvd_card_of_hasLabel {G : Type} [Group G] {J : Subgroup G} {f : ℕ}
    (hf2 : 2 ≤ f) (h4 : 4 ∣ f)
    (hJlab : GGHasLabel ⟨.A, 2, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    5 ∣ Nat.card ↥J ∧ 13 ∣ Nat.card ↥J ∧ 17 ∣ Nat.card ↥J := by
  obtain ⟨F', hF'field, hF'fin, hF'card, ⟨e'⟩⟩ := hJlab
  letI := hF'field
  have := hF'fin
  have hJqcard : Nat.card (J ⧸ Subgroup.center J) =
      Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 3) F')) :=
    Nat.card_congr e'.toEquiv
  obtain ⟨h5dvd, h13dvd, h17dvd⟩ := ggF4H4Psl64_card_dvd hF'card h4 hf2
  have h13q : 13 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rw [hJqcard]; exact h13dvd
  have h17q : 17 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rw [hJqcard]; exact h17dvd
  have h5q : 5 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    rw [hJqcard]; exact h5dvd
  have hcardJ : Nat.card J =
      Nat.card (J ⧸ Subgroup.center J) * Nat.card (Subgroup.center J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
  refine ⟨?_, ?_, ?_⟩
  · rw [hcardJ]; exact dvd_mul_of_dvd_left h5q _
  · rw [hcardJ]; exact dvd_mul_of_dvd_left h13q _
  · rw [hcardJ]; exact dvd_mul_of_dvd_left h17q _

theorem ggF4H4Psl64_false_of_le {G : Type} [Group G] [Finite G] {J K : Subgroup G}
    (hJK : J ≤ K) (hKlab : GGHasLabel ⟨.A, 5, 2⟩ (↥K ⧸ Subgroup.center ↥K))
    (hKc : Subgroup.center ↥K = ⊥) (h13J : 13 ∣ Nat.card ↥J) (h17J : 17 ∣ Nat.card ↥J)
    (h3 : 3 ∣ Nat.card ↥(Subgroup.center ↥J)) : False := by
  obtain ⟨F, hFfield, hFfin, hFcard2, ⟨eK⟩⟩ := hKlab
  letI := hFfield
  have := hFfin
  have hFcard : Nat.card F = 4 := by simpa using hFcard2
  let ι : J →* LargeEvenProj (LargeEvenSLGroup (Fin 6) F) :=
    eK.toMonoidHom.comp
      ((QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hJK))
  have hmk : Function.Injective
      (QuotientGroup.mk' (Subgroup.center K) : K →* K ⧸ Subgroup.center K) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hKc])
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : (QuotientGroup.mk' (Subgroup.center K)) (Subgroup.inclusion hJK a) =
        (QuotientGroup.mk' (Subgroup.center K)) (Subgroup.inclusion hJK b) :=
      eK.injective hab
    exact Subgroup.inclusion_injective hJK (hmk h1)
  exact ggF4H4Psl64_no_embedding hFcard ι hι h13J h17J h3

theorem ggF4H4Psl64_of_balance
    (hL : GGLBalanceInput) : GGF4H4Psl64 := by
  intro G _ _ p B Bs x L D J ks hres _hB3 f hf2 hpf hLlab hJblk K hK hp5 hKlab hKc
  have hI : GGThmIHyp p B x L := hres.1.1.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hres.1.1.1.2.2
  have h5 : 5 ∣ 2 ^ f - 1 := hp5 ▸ hpf
  have h4dvd : 4 ∣ f := ggF4H4Psl64_four_dvd h5
  obtain ⟨hJlab, hJcenter⟩ := hJblk.1 hpf hLlab
  have hJcenter3 : Nat.card (Subgroup.center J) = 3 :=
    hJcenter.trans (ggF4H4Psl64_gcd_three h4dvd)
  obtain ⟨h5J, h13J, h17J⟩ := ggF4H4Psl64_dvd_card_of_hasLabel hf2 h4dvd hJlab
  have hpJ : p ∣ Nat.card J := by rw [hp5]; exact h5J
  obtain ⟨y, hnbr⟩ := hres.1.2.2.2.1.2 K hK
  have hJK : J ≤ K := le_of_ggNbr hL hI hDJ hpJ hnbr
  exact ggF4H4Psl64_false_of_le hJK hKlab hKc h13J h17J (by simp [hJcenter3])

end CFSG.StandardType
