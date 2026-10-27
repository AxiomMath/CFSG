module

public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofDefs
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Late.Transitivity
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1523Res3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mulEquiv_quot_of_inf_eq_bot {X Y : Subgroup G} (hXY : X ≤ Y)
    (hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y) (hXQ : X ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    Nonempty (↥X ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hXY) with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hXN : X ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) :=
      hXY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    have hy : (y : G) ∈ ((X ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
      rw [← hY]
      exact y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X _ hXN] at hy
    obtain ⟨x, hx, p, hp, hxp⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    change QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hXY hx⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hpY : p ∈ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y hp
    have he : (⟨x, hXY hx⟩ : ↥Y)⁻¹ * y = ⟨p, hpY⟩ := by
      apply Subtype.ext
      change x⁻¹ * (y : G) = p
      rw [← hxp]
      group
    rw [he]
    exact (mem_pCoreOf_iff1523 (⟨p, hpY⟩ : ↥Y)).mp hp
  have hfi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : Subgroup.inclusion hXY x ∈ CFSG.pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : G) ∈ CFSG.Open.pCoreOf 2 Y :=
      (mem_pCoreOf_iff1523 (Subgroup.inclusion hXY x)).mpr h1
    have h3 : (x : G) ∈ X ⊓ CFSG.Open.pCoreOf 2 Y := ⟨x.2, h2⟩
    rw [hXQ] at h3
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h3))
  exact ⟨MulEquiv.ofBijective f ⟨hfi, hfs⟩⟩

end Proof1523Res3

open Proof1523Res3

theorem step1523ZPickY4_of_ks (hKS : KS1523NormTwo) : Step1523ZPickY4 := by
  intro G _ _ A c L h hJ Y hY hm d D hQd
  set K := k1523 A d with hK
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  set X := oPrimeResidualOf 3 (Y ⊓ K) with hX
  have hXY : X ≤ Y := (oPrimeResidualOf_le_self 3 _).trans inf_le_left
  have hXK : X ≤ K := (oPrimeResidualOf_le_self 3 _).trans inf_le_right
  have hKC : K ≤ Subgroup.centralizer ({d} : Set G) :=
    (oPrimeResidualOf_le_self 3 _).trans (delta_le _)
  have hXQ : X ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ Q ⊓ Subgroup.centralizer ({d} : Set G) := ⟨hx.2, hKC (hXK hx.1)⟩
    rwa [hQd] at h1
  obtain ⟨e⟩ := mulEquiv_quot_of_inf_eq_bot hXY D.eq_y hXQ
  have hXtype : (∃ _ : Fact (Nat.Prime 7), Nonempty (↥X ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∨
      Nonempty (↥X ≃* alternatingGroup (Fin 7)) := by
    rcases D.type_y with ⟨h7, ⟨φ⟩⟩ | hφ
    · exact Or.inl ⟨h7, ⟨e.trans φ⟩⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inr ⟨e.trans φ⟩
  have hD := h.toSec13Data
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := D.mem_x.1.2
  obtain ⟨U, hUX, hU1, hU2, hAU⟩ := hKS G X A hXtype hA3 hAX
  have hcop : Nat.Coprime 3 (Nat.card U) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU2
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 2
    Nat.prime_three A U hD.isElemAbelian (by rw [hD.card_eq]; norm_num) hAU hcop
  obtain ⟨B, ⟨hBA, hB9⟩, hUB⟩ : ∃ B ∈ CFSG.Open.signalizerFunctorEk 3 2 A,
      U ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hU1
    rw [← hgen, eq_bot_iff]
    exact iSup₂_le fun B hB => (hall B hB).le
  obtain ⟨b, hbB, hbd⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers d := by
    by_contra hall
    push Not at hall
    have hle : B ≤ Subgroup.zpowers d := fun b hb => hall b hb
    have h1 := Subgroup.card_le_of_le hle
    rw [hB9, Sec13.card_zpowers_of_pow_three (hD.isElemAbelian.2 d D.mem_d) D.ne_d] at h1
    norm_num at h1
  have hAab : IsMulCommutative A := hD.isElemAbelian.1
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (hAab.is_comm.comm ⟨x, hBA hx⟩ ⟨a, ha⟩)
  refine ⟨b, hBA hbB, hbd, U ⊓ Subgroup.centralizer (B : Set G), le_inf
    (inf_le_left.trans (hUX.trans hXY))
    (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))),
    hU2.to_le inf_le_left,
    Late.le_normalizer_inf hAU (hAB.trans Subgroup.le_normalizer), fun hle => hUB ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ X ⊓ Q := ⟨hUX hx.1, hle hx⟩
  rwa [hXQ] at h1

end CFSG.RankThree.PartTwo.Sec15
