module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFRank
public import Certificates.Certificate2236
public import Certificates.Certificate2237
public import Certificates.Certificate2238
public import Certificates.Certificate2239
public import Certificates.Certificate2281
public import Certificates.Certificate2283
public import Certificates.Certificate3169
public import Certificates.Certificate8004
import CFSG.Sporadic.SmallOddCore.J3Aut
import CFSG.Sporadic.Schreier.PairJ3Faithful
import CFSG.RankThree.Asc83Table.J3
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Foundations
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofList
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesExc
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Hering611Facts
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFBridge
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofPSL2
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate43
public import Certificates.Certificate8169
import CFSG.RankThree.PartTwo.Sec4.Item426A6Inner

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section J3


theorem aut_bound_J3 {M : Type} [Group M] (e : M ≃* Blueprint.NativeSporadic.J3)
    (Y : Subgroup (MulAut M)) (hY : CFSG.Assembly.IsElemAbelian 3 Y) : Nat.card Y ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite Blueprint.NativeSporadic.J3 := (CFSG.Sporadic.J3.fam_j3_simplicity).1
  have : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have hOut : Nat.card (Outer M) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
      (e.trans CFSG.Sporadic.Schreier.j3PermEquiv)).toEquiv]
    exact CFSG.Sporadic.SmallOddCore.j3_outer_card_le
  have hYin : Y ≤ inner M := by
    intro σ hσ
    have h3 : σ ^ 3 = 1 := hY.2 σ hσ
    have h3' : (QuotientGroup.mk σ : Outer M) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
    have hord : orderOf (QuotientGroup.mk σ : Outer M) ∣ 3 := orderOf_dvd_of_pow_eq_one h3'
    have hord2 : orderOf (QuotientGroup.mk σ : Outer M) ∣ Nat.card (Outer M) :=
      orderOf_dvd_natCard _
    have hle : orderOf (QuotientGroup.mk σ : Outer M) ≤ 2 :=
      (Nat.le_of_dvd Nat.card_pos hord2).trans hOut
    have h1 : orderOf (QuotientGroup.mk σ : Outer M) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
      · exact h
      · omega
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hcenter : Subgroup.center M = ⊥ := by
    have hsJ := (CFSG.Sporadic.J3.fam_j3_simplicity).2.2
    haveI hsM : IsSimpleGroup M := @MulEquiv.isSimpleGroup M _ _ _ hsJ e
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : M, a * b = b * a := fun a b => by
        have : a ∈ Subgroup.center M := h ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp this b).symm
      letI : CommGroup M := { (inferInstance : Group M) with mul_comm := hcomm }
      have hp := IsSimpleGroup.prime_card (α := M)
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3] at hp
      have h2 : (2 : ℕ) ∣ 50232960 := by norm_num
      rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
  have hinj : Function.Injective (MulAut.conj : M →* MulAut M) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      have : g ∈ Subgroup.center M := by
        rw [Subgroup.mem_center_iff]
        intro z
        have := congrArg (fun γ : MulAut M => γ z) h
        exact (mul_inv_eq_iff_eq_mul.mp (by simpa [MulAut.conj_apply] using this)).symm
      rwa [hcenter, Subgroup.mem_bot] at this
    · rintro rfl
      exact map_one _
  set W : Subgroup M := Y.comap (MulAut.conj : M →* MulAut M) with hW
  have hWmap : W.map (MulAut.conj : M →* MulAut M) = Y := by
    rw [hW, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hYin
  have hWcard : Nat.card W = Nat.card Y := by
    rw [← Subgroup.card_map_of_injective hinj, hWmap]
  have hWe : CFSG.Assembly.IsElemAbelian 3 W := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      have ha' : (MulAut.conj (a : M)) ∈ Y := a.2
      have hb' : (MulAut.conj (b : M)) ∈ Y := b.2
      have hc := congrArg Subtype.val (hY.1.is_comm.comm ⟨_, ha'⟩ ⟨_, hb'⟩)
      apply hinj
      simpa using hc
    · apply hinj
      have := hY.2 _ ha
      simpa using this
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hWe).exists_card_eq
  have hkr : k ≤ CFSG.pRank 3 M := by
    refine le_csSup ⟨Nat.card M, ?_⟩ ⟨W, hWe.isElementaryAbelian, hk⟩
    rintro r ⟨B, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card M := Subgroup.card_le_card_group B
  have hrank : CFSG.pRank 3 M = 3 :=
    (CFSG.RankThree.Asc83Table.J3.table (L := M) ⟨e⟩).1
  rw [← hWcard, hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hkr.trans hrank.le)
    _ = 27 := by norm_num

theorem autJ3CoverRank_holds : AutJ3CoverRank := by
  intro X _ _ hperf hcov Y hY
  obtain ⟨-, ⟨e⟩⟩ := hcov
  let r : MulAut X →* MulAut (X ⧸ Subgroup.center X) :=
    { toFun := fun σ => QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) σ
        (Subgroup.map_center_eq σ)
      map_one' := by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x => rfl
      map_mul' := fun σ τ => by
        ext x
        induction x using QuotientGroup.induction_on with
        | H x => rfl }
  have hrinj : Function.Injective r := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    refine Sec4.Item426.mulAut_eq_of_forall_inv_mul_mem_center hperf (σ₂ := 1) (fun g => ?_)
    have h1 := congrArg (fun γ : MulAut (X ⧸ Subgroup.center X) =>
      γ (g : X ⧸ Subgroup.center X)) hσ
    have h2 : (QuotientGroup.mk (σ g) : X ⧸ Subgroup.center X) = QuotientGroup.mk g := h1
    rw [QuotientGroup.eq] at h2
    simpa using h2
  have hY'e : CFSG.Assembly.IsElemAbelian 3 (Y.map r) := CFSG.Open.IsElemAbelian.map hY r
  have hcard : Nat.card (Y.map r) = Nat.card Y := Subgroup.card_map_of_injective hrinj
  rw [← hcard]
  exact aut_bound_J3 e (Y.map r) hY'e

end J3

end CFSG.RankThree.PartTwo.Sec8.Hering611
