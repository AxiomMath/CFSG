module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res4ProofL34
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.Asc83Table.Reduction
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBar

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step142LowerGenA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

@[expose] def Step142LowerGenNA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
    ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

namespace Res4A7

open Equiv KFacts.KP2

theorem vOne_le_alternatingGroup : vOne ≤ alternatingGroup (Fin 7) :=
  vOne_le_centOne.trans inf_le_right

theorem vTwo_le_alternatingGroup : vTwo ≤ alternatingGroup (Fin 7) :=
  vTwo_le_centTwo.trans inf_le_right

theorem eNineF_conj_vOneF : ∀ (i j : Fin 3) (m : Fin 4), ∃ m' : Fin 4,
    eNineF i j * vOneF m * (eNineF i j)⁻¹ = vOneF m' := by
  decide +kernel

theorem eNineF_conj_vTwoF : ∀ (i j : Fin 3) (m : Fin 4), ∃ m' : Fin 4,
    eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF m' := by
  decide +kernel

theorem eNine_le_normalizer_vOne : eNine ≤ Subgroup.normalizer (vOne : Set (Perm (Fin 7))) := by
  refine Item148PtRes2.le_normalizer_of_conj_mem' fun g hg v hv => ?_
  obtain ⟨i, j, rfl⟩ := hg
  obtain ⟨m, rfl⟩ := hv
  obtain ⟨m', hm'⟩ := eNineF_conj_vOneF i j m
  exact ⟨m', hm'⟩

theorem eNine_le_normalizer_vTwo : eNine ≤ Subgroup.normalizer (vTwo : Set (Perm (Fin 7))) := by
  refine Item148PtRes2.le_normalizer_of_conj_mem' fun g hg v hv => ?_
  obtain ⟨i, j, rfl⟩ := hg
  obtain ⟨m, rfl⟩ := hv
  obtain ⟨m', hm'⟩ := eNineF_conj_vTwoF i j m
  exact ⟨m', hm'⟩

@[expose] def tr : Fin 7 → Perm (Fin 7) :=
  ![1, vTwoF 1, vTwoF 2, vOneF 3 * vTwoF 3, vOneF 2 * vTwoF 3, vOneF 1 * vTwoF 3, vTwoF 3]

theorem tr_apply_zero : ∀ y : Fin 7, tr y 0 = y := by
  decide +kernel

theorem tr_mem (y : Fin 7) : tr y ∈ vOne ⊔ vTwo := by
  have h1 : ∀ m : Fin 4, vOneF m ∈ vOne ⊔ vTwo := fun m => Subgroup.mem_sup_left ⟨m, rfl⟩
  have h2 : ∀ m : Fin 4, vTwoF m ∈ vOne ⊔ vTwo := fun m => Subgroup.mem_sup_right ⟨m, rfl⟩
  fin_cases y
  · exact one_mem _
  · exact h2 1
  · exact h2 2
  · exact mul_mem (h1 3) (h2 3)
  · exact mul_mem (h1 2) (h2 3)
  · exact mul_mem (h1 1) (h2 3)
  · exact h2 3

theorem isPretransitive_sup : MulAction.IsPretransitive ↥(vOne ⊔ vTwo) (Fin 7) := by
  refine ⟨fun x y => ⟨⟨tr y * (tr x)⁻¹, mul_mem (tr_mem y) (inv_mem (tr_mem x))⟩, ?_⟩⟩
  have hx : (tr x)⁻¹ x = 0 := by
    rw [Perm.inv_eq_iff_eq, tr_apply_zero]
  change (tr y * (tr x)⁻¹) x = y
  rw [Perm.mul_apply, hx, tr_apply_zero]

@[expose] def threeCycle : Perm (Fin 7) := (vOneF 1 * vTwoF 1) ^ 2

theorem isThreeCycle_threeCycle : threeCycle.IsThreeCycle := by
  have h3 : threeCycle ^ 3 = 1 := by decide +kernel
  have h1 : threeCycle ≠ 1 := by decide +kernel
  have hs : threeCycle.support.card = 3 := by decide +kernel
  change threeCycle.cycleType = {3}
  rw [cycleType_of_pow_three h3 h1, hs]
  rfl

theorem vOne_sup_vTwo : vOne ⊔ vTwo = alternatingGroup (Fin 7) := by
  refine le_antisymm (sup_le vOne_le_alternatingGroup vTwo_le_alternatingGroup) ?_
  have := isPretransitive_sup
  have h7 : (Nat.card (Fin 7)).Prime := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hprim : MulAction.IsPreprimitive ↥(vOne ⊔ vTwo) (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card h7
  refine Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    isThreeCycle_threeCycle ?_
  have h1 : vOneF 1 ∈ vOne := ⟨1, rfl⟩
  have h2 : vTwoF 1 ∈ vTwo := ⟨1, rfl⟩
  exact pow_mem (mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)) 2

theorem sSup_eq_top_of_mulEquiv {X : Type*} [Group X] (φ : X ≃* ↥(alternatingGroup (Fin 7)))
    {E : Subgroup X} (hE : Nat.card E = 9) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A7 := alternatingGroup (Fin 7) with hA7
  have hcard : Nat.card A7 = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hfac : (Nat.card A7).factorization 3 = 2 := by
    rw [hcard]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 2520 = 3 ^ 2 * 280 by norm_num) (by norm_num)
  set E' := E.map φ.toMonoidHom with hE'
  set N9 := eNine.subgroupOf A7 with hN9def
  have hE'9 : Nat.card E' = 9 := by rw [hE', Subgroup.card_map_of_injective φ.injective, hE]
  have hN9 : Nat.card N9 = 9 := by
    rw [hN9def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv,
      card_eNine]
  let P₁ : Sylow 3 A7 := Sylow.ofCard E' (by rw [hE'9, hfac]; norm_num)
  let P₂ : Sylow 3 A7 := Sylow.ofCard N9 (by rw [hN9, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 P₂ P₁
  have hgE : ∀ x : X, x ∈ E → ∃ e : A7, (e : Perm (Fin 7)) ∈ eNine ∧ g * e * g⁻¹ = φ x := by
    intro x hx
    have h1 : φ x ∈ ((g • P₂ : Sylow 3 A7) : Subgroup A7) := by
      rw [hg]
      exact ⟨x, hx, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨e, he, hge⟩ := h1
    exact ⟨e, Subgroup.mem_subgroupOf.mp he, hge⟩
  have key : ∀ V : Subgroup (Perm (Fin 7)), V ≤ A7 →
      eNine ≤ Subgroup.normalizer (V : Set (Perm (Fin 7))) → Nat.card V = 4 →
      ((V.subgroupOf A7).map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom ∈
        {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} := by
    intro V hVA hEV hV4
    refine ⟨?_, ?_⟩
    · rw [Subgroup.card_map_of_injective φ.symm.injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hV4]
      norm_num
    · refine Item148PtRes2.le_normalizer_of_conj_mem' fun x hx y hy => ?_
      obtain ⟨e, he, hge⟩ := hgE x hx
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hy ⊢
      obtain ⟨v, hv, hgv⟩ := hy
      refine ⟨e * v * e⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (hEV he) v).mp (Subgroup.mem_subgroupOf.mp hv)
        simpa using h1
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgv ⊢
        rw [map_mul, map_mul, map_inv, ← hge, ← hgv]
        group
  set Y₁ := ((vOne.subgroupOf A7).map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom
  set Y₂ := ((vTwo.subgroupOf A7).map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom
  have hY₁ := key vOne vOne_le_alternatingGroup eNine_le_normalizer_vOne card_vOne
  have hY₂ := key vTwo vTwo_le_alternatingGroup eNine_le_normalizer_vTwo card_vTwo
  have htop : Y₁ ⊔ Y₂ = ⊤ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup vOne_le_alternatingGroup
      vTwo_le_alternatingGroup, vOne_sup_vTwo, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective,
      Subgroup.map_top_of_surjective _ φ.symm.surjective]
  exact eq_top_iff.mpr (htop.ge.trans (sup_le (le_sSup hY₁) (le_sSup hY₂)))

end Res4A7

open Res4A7 in
theorem step142LowerGenA7_of (h131 : Item131) (hspor : SporadicModels131) :
    Step142LowerGenA7 := by
  intro G _ _ A c L h ⟨φ⟩
  have hD := h.toSec13Data
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor hD
    (center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2)
    (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
  have hLc := hD.le_centralizer
  have hcA := hD.mem_A
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set E := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hE
  have hE3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x => by
    have hx3 : ((x : L) : G) ^ 3 = 1 := hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2).1
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hx3))⟩
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec4.Item424Proof.card_map_mk_of_isPGroup hE3,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  refine eq_top_iff.mpr ((sSup_eq_top_of_mulEquiv φ hE9).ge.trans (sSup_le_sSup ?_))
  rintro Y ⟨hY3, hEY⟩
  refine ⟨hY3, fun σ hσ => ?_⟩
  obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
  rw [hAc, sup_comm] at haA
  obtain ⟨β, hβ, j, rfl⟩ :=
    Res4L34.exists_eq_mul_zpow_of_mem_sup (B := A ⊓ L) (fun β hβ => hAab β hβ.1 c hcA) haA
  have hσeq : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨β * c ^ j, haN⟩) =
      MulAut.conj (QuotientGroup.mk' θ ⟨β, hβ.2⟩) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      change (((L.normalizerMonoidHom ⟨β * c ^ j, haN⟩ l : L)) : ↥L ⧸ θ) =
        (QuotientGroup.mk' θ ⟨β, hβ.2⟩) * (l : ↥L ⧸ θ) * (QuotientGroup.mk' θ ⟨β, hβ.2⟩)⁻¹
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      refine Subtype.ext ?_
      have hlc : Commute (l : G) c := Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)
      change (β * c ^ j) * (l : G) * (β * c ^ j)⁻¹ = β * (l : G) * β⁻¹
      have hcj : c ^ j * (l : G) * (c ^ j)⁻¹ = l := by
        rw [((hlc.symm).zpow_left j).eq]
        group
      calc (β * c ^ j) * (l : G) * (β * c ^ j)⁻¹ = β * (c ^ j * (l : G) * (c ^ j)⁻¹) * β⁻¹ := by
            group
        _ = β * (l : G) * β⁻¹ := by rw [hcj]
  rw [hσeq]
  have hmem : QuotientGroup.mk' θ ⟨β, hβ.2⟩ ∈ E := ⟨⟨β, hβ.2⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩
  exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEY hmem)).le

theorem step142LowerGen_of_a7 (hA7 : Step142LowerGenA7) (hN : Step142LowerGenNA7) :
    Step142LowerGen := by
  intro G _ _ A c L h hL34
  by_cases h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
  · exact hA7 G A c L h h7
  · exact hN G A c L h h7 hL34

theorem step142LowerS14_of_genNA7 (h131 : Item131) (hspor : SporadicModels131)
    (hN : Step142LowerGenNA7) : Step142LowerS14 :=
  step142LowerS14_of_gen (step142LowerGen_of_a7 (step142LowerGenA7_of h131 hspor) hN)

end CFSG.RankThree.PartTwo.Sec14
