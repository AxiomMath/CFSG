module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LargeExtraspecial.S111SJBenB
public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4F
public import CFSG.StronglyEmbedded.UniqueCosetEnd
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.NormalComplement

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.Quasithin.SzN27 (OutCyclic outCyclic_of_sp4)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (exceptionalAut exceptionalAut_proj)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_symplectic_two_exterior_square_automorphism)

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {n : ℕ}

private theorem conjNormal_injective_of_centralizer_eq_bot (hL : L.Normal)
    (hC : centralizer (L : Set Q) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := L) : Q →* MulAut ↥L) := by
  haveI := hL
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  simpa [CFSG.BenderSuzuki.External.conjNormal_ker_eq_centralizer (H := L), hC] using hq

private theorem conjNormal_mem_inner_of_mem [L.Normal] {a : Q} (ha : a ∈ L) :
    MulAut.conjNormal (H := L) a ∈ inner ↥L := by
  refine ⟨⟨a, ha⟩, ?_⟩
  ext x
  simp [MulAut.conj_apply, MulAut.conjNormal_apply]

private theorem card_outer_eq_of_isSp4 (hn : 2 ≤ n) (hSp : IsSp4 ↥L n) :
    Nat.card (Outer ↥L) = 2 * n := by
  have hscm : StatedClassicalModel ↥L .PSp 2 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hSp
  obtain ⟨-, K, hfield, hfin, hKcard, ⟨e⟩⟩ := hscm
  letI : Field K := hfield
  letI : Finite K := hfin
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  have hmain := (even_symplectic_two_exterior_square_automorphism (f := n) (K := K)
    (by omega) hKcard).2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, hcardOutK, -, -, -, -⟩ :=
    hmain (exceptionalAut K) exceptionalAut_proj
  calc Nat.card (Outer ↥L)
      = Nat.card (Outer (StatedProj (StatedSp 2 K))) :=
        Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    _ = 2 * n := hcardOutK

private theorem isPGroup_quotient_of_sup_eq_top (hL : L.Normal) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) : IsPGroup 2 (Q ⧸ L) := by
  haveI := hL
  let tMap : ↥T →* Q ⧸ L := (QuotientGroup.mk' L).comp T.subtype
  have hsurj : Function.Surjective tMap := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective L y
    have hq : q ∈ L ⊔ T := by rw [hLT]; exact Subgroup.mem_top q
    rw [Subgroup.mem_sup_of_normal_left] at hq
    obtain ⟨l, hl, t, ht, hlt⟩ := hq
    refine ⟨⟨t, ht⟩, ?_⟩
    change (QuotientGroup.mk' L) (t : Q) = (QuotientGroup.mk' L) q
    rw [← hlt, map_mul]
    have hl1 : (QuotientGroup.mk' L) l = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff l).mpr hl
    rw [hl1, one_mul]
  exact hT.isPGroup.of_surjective tMap hsurj

theorem card_le_two_mul_card_inf (hn : 2 ≤ n) (hL : L.Normal) (hSp : IsSp4 ↥L n)
    (hC : centralizer (L : Set Q) = ⊥) {A : Subgroup Q} (hA : IsElemAbelian 2 A) :
    Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ L) := by
  haveI := hL
  have hinj : Function.Injective (MulAut.conjNormal (H := L) : Q →* MulAut ↥L) :=
    conjNormal_injective_of_centralizer_eq_bot hL hC
  have hout : OutCyclic ↥L := outCyclic_of_sp4 hn (by
    exact CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hSp)
  haveI : IsCyclic (Outer ↥L) := hout.2
  let c : Q →* MulAut ↥L := MulAut.conjNormal (H := L)
  let Λ : Subgroup (MulAut ↥L) := A.map c
  have hΛ : ∀ l ∈ Λ, l * l = 1 := by
    intro l hl
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hl
    have ha2 : a * a = 1 := by
      simpa [pow_two] using hA.2 a ha
    rw [← map_mul, ha2, map_one]
  have hcardA : Nat.card Λ = Nat.card ↥A := Subgroup.card_map_of_injective (K := A) hinj
  have hinf : Λ ⊓ inner ↥L = (A ⊓ L).map c := by
    ext l
    constructor
    · rintro ⟨hl, hli⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hl
      have haL : a ∈ L :=
        CFSG.StronglyEmbedded.UniqueCoset.mem_of_conjNormal_mem_inner hC hli
      exact Subgroup.mem_map.mpr ⟨a, ⟨ha, haL⟩, rfl⟩
    · rintro ⟨a, ⟨ha, haL⟩, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, conjNormal_mem_inner_of_mem haL⟩
  have hle := CFSG.LargeExtraspecial.S11.card_le_two_mul_inf_inner Λ hΛ
  rw [hcardA, hinf, Subgroup.card_map_of_injective (K := A ⊓ L) hinj] at hle
  exact hle

theorem index_le_two (hn : 2 ≤ n) (hL : L.Normal) (hSp : IsSp4 ↥L n)
    (hC : centralizer (L : Set Q) = ⊥) (hodd : Odd n) {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    (hLT : L ⊔ T = ⊤) : L.index ≤ 2 := by
  haveI := hL
  let c : Q →* MulAut ↥L := MulAut.conjNormal (H := L)
  let f : Q →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp c
  have hLker : L ≤ f.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (c l)).mpr (conjNormal_mem_inner_of_mem hl)
  let ψ : Q ⧸ L →* Outer ↥L := QuotientGroup.lift L f hLker
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective L x
    have hfq : f q = 1 := by
      simpa [ψ] using hx
    have hmem : c q ∈ inner ↥L := (QuotientGroup.eq_one_iff (c q)).mp (by simpa [f] using hfq)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
    have hqL : q ∈ L :=
      CFSG.StronglyEmbedded.UniqueCoset.mem_of_conjNormal_mem_inner hC hmem
    exact (QuotientGroup.eq_one_iff q).mpr hqL
  have h2 : IsPGroup 2 (Q ⧸ L) := isPGroup_quotient_of_sup_eq_top hL hT hLT
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hcardOut : Nat.card (Outer ↥L) = 2 * n := card_outer_eq_of_isSp4 hn hSp
  have hcardRange : Nat.card (Q ⧸ L) = Nat.card ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
  have hdvd : Nat.card (Q ⧸ L) ∣ Nat.card (Outer ↥L) := by
    rw [hcardRange]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have hdvd2 : 2 ^ k ∣ 2 := by
    have hcop : Nat.Coprime (2 ^ k) n := (Nat.coprime_two_left.mpr hodd).pow_left k
    exact hcop.dvd_of_dvd_mul_right (by rw [hk, hcardOut] at hdvd; exact hdvd)
  calc L.index = Nat.card (Q ⧸ L) := Subgroup.index_eq_card L
    _ = 2 ^ k := hk
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model
