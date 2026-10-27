module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFix
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddInv
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddRep
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSL2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddStrong
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93g
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93i
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups IsMulCommutative
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_of_apply_eq {K U W : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r K U W) [(W.subgroupOf U).Normal]
    [IsElementaryAbelian r (↥U ⧸ W.subgroupOf U)]
    (ρ : Representation (ZMod r) ↥K (Additive (↥U ⧸ W.subgroupOf U)))
    (happ : ∀ (k : ↥K) (u : ↥U), ρ k (Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : ↥U ⧸ W.subgroupOf U))
    {k : ↥K} {u : ↥U} (h : ρ k (Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) :
    (k : G) * u * (k : G)⁻¹ * (u : G)⁻¹ ∈ W := by
  rw [happ] at h
  have hmem := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp (Additive.ofMul.injective h))
  rw [Subgroup.coe_mul, Subgroup.coe_inv, CFSG.ABGLocalTools.chiefConj_apply_coe] at hmem
  have h2 := hUW.2.2.2.1 (u : G) u.2 _ (W.inv_mem hmem)
  rwa [show (u : G) * (((k : G) * u * (k : G)⁻¹)⁻¹ * u)⁻¹ * (u : G)⁻¹ =
    (k : G) * u * (k : G)⁻¹ * (u : G)⁻¹ by group] at h2

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem eq_zero_of_fixed_chief (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {U W : Subgroup G} {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r (Opp 3 Y) U W) [(W.subgroupOf U).Normal]
    [IsElementaryAbelian r (↥U ⧸ W.subgroupOf U)] (hW3 : ¬ 3 ∣ Nat.card W) (hWM : W ≤ D.M)
    (hUM : U ⊓ D.M ≤ W)
    (ρ : Representation (ZMod r) ↥(Opp 3 Y) (Additive (↥U ⧸ W.subgroupOf U)))
    (happ : ∀ (k : ↥(Opp 3 Y)) (u : ↥U), ρ k (Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : ↥U ⧸ W.subgroupOf U))
    {x t : ↥(Opp 3 Y)} (hx : (orderOf x).Prime) (hx2 : orderOf x ≠ 2) (hxt : x * t = t * x)
    (ht : ∀ v, ρ t v = -v) (v : Additive (↥U ⧸ W.subgroupOf U)) (hv : ρ x v = v) : v = 0 := by
  obtain ⟨u, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
  have htinv : ∀ w ∈ U, w * ((t : G) * w * (t : G)⁻¹) ∈ W := by
    intro w hw
    have h := ht (Additive.ofMul ((⟨w, hw⟩ : ↥U) : ↥U ⧸ W.subgroupOf U))
    rw [happ, ← ofMul_inv, ← QuotientGroup.mk_inv] at h
    have h' := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp (Additive.ofMul.injective h))
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      CFSG.ABGLocalTools.chiefConj_apply_coe] at h'
    have h'' := W.inv_mem h'
    rwa [mul_inv_rev, inv_inv, inv_inv] at h''
  have hfix : ∀ a ∈ zpowers (x : G), a * u * a⁻¹ * (u : G)⁻¹ ∈ W := by
    intro a ha
    obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr ha
    have h := conj_mem_of_apply_eq hUW ρ happ (k := x ^ n) (u := u) (by
      rw [map_pow, Module.End.pow_apply]
      exact Function.iterate_fixed hv n)
    rwa [Subgroup.coe_pow] at h
  have hcard : Nat.card (zpowers (x : G)) = orderOf x := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
  have htA : ∀ a ∈ zpowers (x : G), a * t = t * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : Commute (x : G) (t : G) := congrArg Subtype.val hxt
    exact (hc.zpow_left k).eq
  have huW := S.mem_of_fixed_of_inv_opp hN ((Fact.out : r.Prime).odd_of_ne_two hr) hUW hW3 hWM
    hUM ((Subgroup.zpowers_le).mpr x.2) (by rw [hcard]; exact hx) (by rw [hcard]; exact hx2) t.2
    htA htinv u u.2 hfix
  rw [(QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr huW)]
  rfl

theorem exists_sl2_rep_of_not_le (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hIM : ¬ F09.I9 H ≤ D.M) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (F : Type) (_ : Field F) (_ : Fintype F) (V : Type)
      (_ : AddCommGroup V) (_ : Module (ZMod p) V) (_ : Finite V)
      (σ : Representation (ZMod p) SL(2, F) V),
      Fintype.card F = q ∧ p ≠ 2 ∧ p ≠ q ∧ Function.Injective σ ∧ (∀ v, σ (-1) v = -v) ∧
      ∀ g : SL(2, F), (orderOf g).Prime → orderOf g ≠ 2 → ∀ v : V, σ g v = v → v = 0 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXY : Opp 3 Y ≤ Y := opp_le 3 Y
  have hXH : Opp 3 Y ≤ H := hXY.trans hyp.2.1.1
  have hHK : CFSG.Open.IsKGroup ↥H :=
    CFSG.Open.IsKProper.isKGroup D.standing.kProper H S.H_ne_top
  have hXK : CFSG.Open.IsKGroup ↥(Opp 3 Y) := CFSG.Open.IsKGroup.of_le hHK hXH
  have hE9 := F09.not_hasE9_opp hyp
  have hX := S.not_isPGroup_barO3_opp
  have hDU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    hyp.1.2.2 E (hyp.2.2.1.trans hXY) hyp.2.2.2
  have hI3 : ¬ 3 ∣ Nat.card (F09.I9 H) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore H)
  have hKgen : ∀ B : Subgroup G, B ≤ Opp 3 Y → Opp 3 Y ≤ normalizer (B : Set G) → E ≤ B →
      B = Opp 3 Y := fun B hBX hBn hDB =>
    F09.eq_opp_of_normal hSch hXK hE9 hX hyp.2.2.1 hyp.2.2.2 hBX hBn hDB
  haveI hperf' : Group.IsPerfect ↥(Opp 3 Y) := F09.isPerfect_opp hE9 hX
  obtain ⟨p, U, W, hp, -, hUW, hUI, hWM, hUM, hfix⟩ := F09.exists_chief_factor_not_le hSch
    (CFSG.Open.IsKGroup.of_le hHK (sup_le (map_subtype_le _) hXH)) hyp.2.2.1 hyp.2.2.2
    (hXY.trans hyp.1.1) ((centralizer_le_normalizer _).trans
      (CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hDU))
    (Subgroup.isPerfect_iff.mp hperf') hKgen
    (hXH.trans (CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H))
    hI3 hIM
  have hW3 : ¬ 3 ∣ Nat.card W := fun h =>
    hI3 (h.trans (Subgroup.card_dvd_of_le (hUW.1.le.trans hUI)))
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hWn : (W.subgroupOf U).Normal := hUW.normal
  haveI hEl : IsElementaryAbelian p (↥U ⧸ W.subgroupOf U) := hUW.isElementaryAbelian
  haveI : Nontrivial (↥U ⧸ W.subgroupOf U) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hUW.1.ne ((Subgroup.subgroupOf_eq_top.mp htop).antisymm hUW.1.le).symm
  let ρ : Representation (ZMod p) ↥(Opp 3 Y) (Additive (↥U ⧸ W.subgroupOf U)) :=
    (Units.coeHom _).comp (CFSG.ABGLocalTools.chiefRep (p := p) hUW.2.1 hUW.2.2.1)
  have happ : ∀ (k : ↥(Opp 3 Y)) (u : ↥U), ρ k (Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : ↥U ⧸ W.subgroupOf U) :=
    fun k u => CFSG.ABGLocalTools.chiefRep_apply_mk (p := p) hUW.2.1 hUW.2.2.1 k u
  have hirr : ∀ V₀ : Submodule (ZMod p) (Additive (↥U ⧸ W.subgroupOf U)),
      (∀ g : ↥(Opp 3 Y), ∀ v ∈ V₀, ρ g v ∈ V₀) → V₀ = ⊥ ∨ V₀ = ⊤ := fun V₀ hV₀ =>
    CFSG.ABGLocalTools.chiefRep_irreducible hUW V₀ (fun k v hv => hV₀ k v hv)
  have hfixV : fixV ρ (E.subgroupOf (Opp 3 Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨u, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
    have huW : (u : G) ∈ W := hfix (u : G) u.2 fun x hx =>
      conj_mem_of_apply_eq hUW ρ happ (k := ⟨x, hyp.2.2.1 hx⟩)
        (hv _ (Subgroup.mem_subgroupOf.mpr hx))
    rw [Submodule.mem_bot, (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr huW)]
    rfl
  have hD3 : Nat.card (E.subgroupOf (Opp 3 Y)) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.2.2.1).toEquiv).trans hyp.2.2.2
  obtain ⟨hN3, hcases⟩ := F09.quot_ker_cases hK461 hK462 hXK hE9
    Group.IsPerfect.commutator_eq_top hD3 (F09.normalClosure_subgroupOf_eq_top hyp.2.2.1 hKgen)
    ρ hirr hfixV
  have hker2 : ρ.ker ≤ CFSG.pCore 2 ↥(Opp 3 Y) :=
    le_pCore_two_of_normal S.isSimpleGroup_bar2_opp S.three_dvd_card_bar2_opp hN3
  have hkerψ : ρ.ker ≤ (QuotientGroup.mk' (CFSG.pCore 2 ↥(Opp 3 Y))).ker := by
    rwa [QuotientGroup.ker_mk']
  obtain ⟨F, hF, hFt, ⟨e⟩, hcardF, h2⟩ := exists_sl2_of_quot_cases S.gt S.shape_opp
    (QuotientGroup.lift _ _ hkerψ) (QuotientGroup.lift_surjective_of_surjective _ _
      (QuotientGroup.mk'_surjective _) hkerψ) hcases
  have hker : IsPGroup 2 ρ.ker := CFSG.pCore_isPGroup.to_le hker2
  obtain ⟨t₀, ht₀⟩ := QuotientGroup.mk_surjective (e.symm (-1))
  obtain ⟨hneg, hne⟩ := apply_eq_neg_of_mk_eq ρ hirr e h2 ht₀
  have hp2 : p ≠ 2 := ne_two_of_apply_eq_neg ρ hneg hne
  obtain ⟨σ, hσ, hσneg, hσfpf⟩ := exists_sl2_rep_of_quot ρ hker e ht₀ hneg
    fun x t hx hx2 hxt ht v hv =>
      S.eq_zero_of_fixed_chief hN hp2 hUW hW3 hWM hUM ρ happ hx hx2 hxt ht v hv
  have hpq : p ≠ Fintype.card F :=
    ne_card_of_fpf σ (by rw [hcardF]; exact S.prime) (by rw [hcardF]; have := S.gt; omega) hσfpf
  exact ⟨p, inferInstance, F, hF, hFt, _, _, _, inferInstance, σ, hcardF, hp2, hcardF ▸ hpq, hσ,
    hσneg, hσfpf⟩

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
