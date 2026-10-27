module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res4ProofA7
public import CFSG.RankThree.PartTwo.KFacts.KP4Basic
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInnerBar

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step142LowerGenM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

@[expose] def Step142LowerGenM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

@[expose] def Step142LowerGenHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

@[expose] def Step142LowerGenL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

namespace Res5Gen

theorem sSup_eq_top_of_conj_mem {X Γ : Type*} [Group X] [Group Γ] (φ : X ≃* Γ)
    {E : Subgroup X} {P₀ : Subgroup Γ} {g : Γ} (hgE : ∀ x ∈ E, ∃ p ∈ P₀, g * p * g⁻¹ = φ x)
    {ι : Type*} (V : ι → Subgroup Γ) (hV3 : ∀ i, ¬ 3 ∣ Nat.card (V i))
    (hVN : ∀ i, P₀ ≤ Subgroup.normalizer (V i : Set Γ)) (htop : ⨆ i, V i = ⊤) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ := by
  set Y : ι → Subgroup X := fun i =>
    ((V i).map (MulAut.conj g).toMonoidHom).map φ.symm.toMonoidHom with hYdef
  have hY : ∀ i, Y i ∈
      {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} := by
    intro i
    refine ⟨?_, ?_⟩
    · rw [hYdef, Subgroup.card_map_of_injective φ.symm.injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hV3 i
    · refine Item148PtRes2.le_normalizer_of_conj_mem' fun x hx y hy => ?_
      obtain ⟨p, hp, hgp⟩ := hgE x hx
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hy ⊢
      obtain ⟨v, hv, hgv⟩ := hy
      refine ⟨p * v * p⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hVN i hp) v).mp hv
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgv ⊢
        rw [map_mul, map_mul, map_inv, ← hgp, ← hgv]
        group
  have htopY : ⨆ i, Y i = ⊤ := by
    rw [hYdef]
    simp only
    rw [← Subgroup.map_iSup, ← Subgroup.map_iSup, htop,
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective,
      Subgroup.map_top_of_surjective _ φ.symm.surjective]
  exact eq_top_iff.mpr (htopY.ge.trans (iSup_le fun i => le_sSup (hY i)))

theorem exists_conj_mem_of_card {Γ : Type*} [Group Γ] [Finite Γ] {P₀ E' : Subgroup Γ}
    (hP : Nat.card P₀ = 9) (hE : Nat.card E' = 9) (hfac : (Nat.card Γ).factorization 3 = 2) :
    ∃ g : Γ, ∀ e ∈ E', ∃ p ∈ P₀, g * p * g⁻¹ = e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S₁ : Sylow 3 Γ := Sylow.ofCard E' (by rw [hE, hfac]; norm_num)
  let S₂ : Sylow 3 Γ := Sylow.ofCard P₀ (by rw [hP, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S₂ S₁
  refine ⟨g, fun e he => ?_⟩
  have h1 : e ∈ ((g • S₂ : Sylow 3 Γ) : Subgroup Γ) := by
    rw [hg]
    exact he
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨p, hp, hpe⟩ := h1
  exact ⟨p, hp, hpe⟩

section M22

open CFSG.RankThree.PartTwo.KFacts.KP4 CFSG.Sporadic.Mathieu

theorem m22gA_eq : m22gA = vB 2 * vA 0 * vA 2 * vA 0 * vB 2 := by
  decide +kernel

theorem m22gB_eq : m22gB = vB 2 * vA 0 * vB 1 * vA 3 * vA 0 * vB 1 * vA 2 := by
  decide +kernel

theorem iSup_V_eq_top : ⨆ i, V i = ⊤ := by
  set T := ⨆ i, V i with hT
  have hA : ∀ i, vAE i ∈ T := fun i =>
    le_iSup V i (show vAE i ∈ V i from mem_V_iff.mpr (Or.inr (Or.inl rfl)))
  have hB : ∀ i, vBE i ∈ T := fun i =>
    le_iSup V i (show vBE i ∈ V i from mem_V_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have ha : m22a ∈ T := by
    have he : m22a = vBE 2 * vAE 0 * vAE 2 * vAE 0 * vBE 2 := Subtype.ext m22gA_eq
    rw [he]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hB 2) (hA 0)) (hA 2)) (hA 0)) (hB 2)
  have hb : m22b ∈ T := by
    have he : m22b = vBE 2 * vAE 0 * vBE 1 * vAE 3 * vAE 0 * vBE 1 * vAE 2 :=
      Subtype.ext m22gB_eq
    rw [he]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hB 2) (hA 0)) (hB 1)) (hA 3))
      (hA 0)) (hB 1)) (hA 2)
  rw [eq_top_iff, ← closure_pair_eq_top m22_eq m22a.2 m22b.2, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ha
  · exact hb

theorem sSup_eq_top_of_mulEquiv_M22 {X : Type*} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.M22) {E : Subgroup X} (hE : Nat.card E = 9) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ := by
  have hfac : (Nat.card G22).factorization 3 = 2 := by
    rw [KFacts.KS14.card_nativeM22]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 443520 = 3 ^ 2 * 49280 by norm_num) (by norm_num)
  have hE' : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card card_P0 hE' hfac
  refine sSup_eq_top_of_conj_mem φ (P₀ := P0) (g := g) (fun x hx => hg _ ⟨x, hx, rfl⟩) V
    (fun i => by rw [card_V]; norm_num) P0_le_normalizer_V iSup_V_eq_top

end M22

variable {G : Type} [Group G] [Finite G]

theorem sSup_autThetaQuot_eq_top_of_inner {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hgen : sSup {Y : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card Y ∧
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
        Subgroup.normalizer (Y : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))} = ⊤) :
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤ := by
  have hD := h.toSec13Data
  have hLc := hD.le_centralizer
  have hcA := hD.mem_A
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set E := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hE
  refine eq_top_iff.mpr (hgen.ge.trans (sSup_le_sSup ?_))
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

theorem card_image_inf {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Nat.card (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9 := by
  have hD := h.toSec13Data
  have hE3 : IsPGroup 3 ((A ⊓ L).subgroupOf L) := fun x => by
    have hx3 : ((x : L) : G) ^ 3 = 1 := hD.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2).1
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hx3))⟩
  rw [Sec4.Item424Proof.card_map_mk_of_isPGroup hE3,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]

end Res5Gen

open Res5Gen in
theorem step142LowerGenM22_of
    (h131 : Item131) :
    Step142LowerGenM22 := by
  intro G _ _ A c L h ⟨φ⟩
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor h.toSec13Data
    (center_eq_bot_of_mulEquiv φ hspor.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  exact sSup_autThetaQuot_eq_top_of_inner h hAc
    (sSup_eq_top_of_mulEquiv_M22 φ (card_image_inf h h9))

theorem step142LowerGenNA7_of_types
    (h131 : Item131) (hM12 : Step142LowerGenM12) (hHJ : Step142LowerGenHJ)
    (hL3 : Step142LowerGenL3) : Step142LowerGenNA7 := by
  intro G _ _ A c L h hA7 hL34
  rcases (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with hJ | hL | h7 | h22 | h12
  · exact hHJ G A c L h hJ
  · exact hL3 G A c L h hL hL34
  · exact absurd h7 hA7
  · exact step142LowerGenM22_of h131 G A c L h h22
  · exact hM12 G A c L h h12

end CFSG.RankThree.PartTwo.Sec14
