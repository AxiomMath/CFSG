module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EB2
public import CFSG.RankThree.PartTwo.Sec21.Hering214EFinal
public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartTwo.Sec21.Hering2119
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits)
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open Item211Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem central_of_comp_mk {L : Subgroup G} [Group.IsPerfect L]
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L) {Q : Type} [Group Q]
    (Φ : lBar L →* Q) (hΦ : Φ.ker ≤ Subgroup.center (lBar L)) :
    ∀ z : ↥L, Φ (z : lBar L) = 1 → ∀ h : ↥L, h * z = z * h := by
  intro z hz h
  have hzc : (z : lBar L) ∈ Subgroup.center (lBar L) := hΦ hz
  let conjZ : ↥L →* ↥L := (MulAut.conj z).toMonoidHom
  have hdisp : ∀ x : ↥L, x⁻¹ * conjZ x ∈ Subgroup.center ↥L := by
    intro x
    apply hθc
    rw [← QuotientGroup.eq_one_iff]
    change ((x⁻¹ * (z * x * z⁻¹) : ↥L) : lBar L) = 1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← Subgroup.mem_center_iff.mp hzc (x : lBar L)]
    group
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    conjZ hdisp
  have h1 : z * h * z⁻¹ = h := DFunLike.congr_fun hid h
  calc h * z = z * h * z⁻¹ * z := by rw [h1]
    _ = z * h := by group

theorem item214EvenTypeC_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h213 : Item213) :
    Item214EvenTypeC := by
  intro G _ _ A E U c L hpair _heven h7 hA27
  classical
  have hPF := Item211LieProof.pairFacts h45 h66 hpair
  have hq := h213 G A E U c L hpair
  haveI : Group.IsPerfect ↥L := hq.1
  have hθc : aschbacherSolvableCore 3 ↥L ≤ Subgroup.center ↥L := by
    obtain ⟨hTs, hTch, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    have : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
    exact Sec4.Census.le_of_isSolvable_of_normal inferInstance hTs
  have hEA : E = A := Subgroup.eq_of_le_of_card_ge hpair.mem_E.2
    (by rw [hA27, hpair.mem_E.1.2.1]; norm_num)
  have hbar : ∀ e (he : e ∈ E), barAct L ⟨e, hPF.EL he⟩ ∈ barImage L E := fun e he =>
    mem_barImage_iff.mpr ⟨e, hPF.EL he, he, rfl⟩
  have hmk : ∀ e (he : e ∈ E) (x : ↥L), barAct L ⟨e, hPF.EL he⟩ (x : lBar L) =
      ((L.normalizerMonoidHom ⟨e, hPF.EL he⟩ x : ↥L) : lBar L) := fun e he x =>
    Sec4.thetaQuotMulAut_mk _ x
  have hfinish : ∀ (F : Type) [Field F] [CharP F 2] (Φ : lBar L →* projectiveSL 3 F),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (lBar L) →
      ∀ (g : GL (Fin 3) F) (τ : Fˣ), τ ≠ 1 →
      (∀ σ ∈ barImage L E, ∃ s t : Fˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧ ∀ z,
        Φ (σ z) = conjAut 3 F (g * diagUnits 1 s t * g⁻¹) (Φ z)) →
      (∃ σ ∈ barImage L E, ∀ z, Φ (σ z) = conjAut 3 F (g * diagUnits 1 τ 1 * g⁻¹) (Φ z)) →
      ∃ U' ∈ fourGroupsMinus E, U' ≤ L := by
    intro F _ _ Φ hΦs hΦk g τ hτ1 hp1 hp2
    set Ψ : ↥L →* projectiveSL 3 F := Φ.comp (QuotientGroup.mk' _) with hΨ
    have hΨs : Function.Surjective Ψ :=
      hΦs.comp (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L))
    refine exists_fourGroupsMinus_of_model hPF.Ee hPF.EL Ψ hΨs
      (central_of_comp_mk hθc Φ hΦk) g hτ1 ?_ ?_
    · intro e he
      obtain ⟨s, t, -, -, hst⟩ := hp1 _ (hbar e he)
      exact ⟨s, t, fun x => by
        change Φ ((L.normalizerMonoidHom ⟨e, hPF.EL he⟩ x : ↥L) : lBar L) = _
        rw [← hmk e he x, hst]
        rfl⟩
    · obtain ⟨σ, hσ, hσΦ⟩ := hp2
      obtain ⟨e, heN, he, rfl⟩ := mem_barImage_iff.mp hσ
      refine ⟨e, he, fun x => ?_⟩
      change Φ ((L.normalizerMonoidHom ⟨e, hPF.EL he⟩ x : ↥L) : lBar L) = _
      rw [← hmk e he x, hσΦ]
      rfl
  obtain ⟨n, hn, hev, hcase⟩ := h7
  rcases hcase with ⟨⟨eL⟩, hC⟩ | ⟨⟨eL⟩, hC⟩
  ·
    have hC' : Hering214.IsTypeCSub (lBar L) (barImage L E) := by
      rw [Hering214.barImage_eq_autThetaQuot, hEA]
      exact Hering214.isTypeCSub_of_isTypeCOn hC
    obtain ⟨F, hF, hFin, Φ, g, τ, hFcard, hτ3, hτ1, hpart1, hpart2⟩ :=
      Hering214.exists_typeC_model_sub hC' hn eL
    haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
    refine hfinish F Φ.toMonoidHom Φ.surjective ?_ g τ hτ1 hpart1 (hpart2 τ 1 hτ3 (one_pow 3))
    rw [(MonoidHom.ker_eq_bot_iff _).mpr Φ.injective]
    exact bot_le
  ·
    have hC' : Hering214.IsTypeCSubSL (lBar L) (barImage L E) := by
      rw [Hering214.barImage_eq_autThetaQuot, hEA]
      exact Hering214.isTypeCSubSL_of_isTypeCOnBarSL hC
    have hn2 : 2 ≤ n := by
      obtain ⟨k, rfl⟩ := hev
      omega
    obtain ⟨F, hF, hFin, Φ, hΦ, hker, -, g, τ, hFcard, hτ3, hτ1, hpart1, hpart2⟩ :=
      Hering214.exists_typeCSL_model_sub hC' hn2 eL
    haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
    exact hfinish F Φ hΦ hker g τ hτ1 hpart1 (hpart2 τ 1 hτ3 (one_pow 3))

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
