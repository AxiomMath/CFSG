module

public import CFSG.RankThree.GF2n.Tim81.Sec5.S512Aux
import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55
public import CFSG.RankThree.GF2n.Tim78S48PhaseSz
import CFSG.GroupTheory.CoprimeActionSupport.OddConjClassFixed

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.LocalAnalysis.EvenBN.Common
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

namespace Sec5Hyp

private theorem forall_commutator_mem_kOf_of_commute (hS : Sec5Hyp M V) {g h : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) (hU' : conjSubgroup h V ∈ sigmaSet M V)
    (hc : ⁅conjSubgroup g V, conjSubgroup h V⁆ = ⊥)
    (h57 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt57 M' V') :
    ∀ u ∈ conjSubgroup g V,
      (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
        u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G) :=
  Sec5Hyp.forall_commutator_mem_kOf_of_le hS hU' hU hc
    (Sec5.Stmt57.le_of_commute (h57 M V hS) hU hU' hc)

private theorem isHMember_case_eq (hS : Sec5Hyp M V) {g h : G}
    (hU' : conjSubgroup h V ∈ sigmaSet M V)
    (hne : conjSubgroup g V ≠ conjSubgroup h V) (hEq : hOf M V g = hOf M V h) :
    IsHMember (conjSubgroup h M) (conjSubgroup h V)
      (conjSubgroup g (Pc M V) ⊔ conjSubgroup h (Pc M V)) := by
  classical
  have hroot := hS.toRootHyp
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hU'
  obtain ⟨y_g, hy_g, hPyg, hVyg, -⟩ :=
    hroot.exists_mem_conj_eq_of_eq_sup (H := hOf M V g) le_sup_left rfl
  have hy_g' : y_g ∈ hOf M V h := hEq ▸ hy_g
  obtain ⟨y_h, hy_h, hPyh, hVyh, -⟩ := hroot.exists_mem_conj_eq_of_eq_sup hSh.Pc_le hSh.hH
  set y : G := y_g * y_h⁻¹ with hy_def
  have hyH : y ∈ hOf M V h := (hOf M V h).mul_mem hy_g' ((hOf M V h).inv_mem hy_h)
  have hyy : y * y_h = y_g := by rw [hy_def]; group
  have hconjV : conjSubgroup y (conjSubgroup h V) = conjSubgroup g V := by
    calc conjSubgroup y (conjSubgroup h V) = conjSubgroup y (conjSubgroup y_h V) := by rw [hVyh]
      _ = conjSubgroup (y * y_h) V := CGT.Timmesfeld75.conjSubgroup_conjSubgroup y y_h V
      _ = conjSubgroup y_g V := by rw [hyy]
      _ = conjSubgroup g V := hVyg.symm
  have hconjP : conjSubgroup y (Pc (conjSubgroup h M) (conjSubgroup h V)) =
      conjSubgroup g (Pc M V) := by
    have hPc : Pc (conjSubgroup h M) (conjSubgroup h V) = conjSubgroup y_h (Pc M V) := by
      rw [Pc_conjSubgroup]
      exact hPyh
    calc conjSubgroup y (Pc (conjSubgroup h M) (conjSubgroup h V))
        = conjSubgroup y (conjSubgroup y_h (Pc M V)) := by rw [hPc]
      _ = conjSubgroup (y * y_h) (Pc M V) :=
        CGT.Timmesfeld75.conjSubgroup_conjSubgroup y y_h (Pc M V)
      _ = conjSubgroup y_g (Pc M V) := by rw [hyy]
      _ = conjSubgroup g (Pc M V) := hPyg.symm
  have hyVne : conjSubgroup y (conjSubgroup h V) ≠ conjSubgroup h V := by
    rw [hconjV]
    exact hne
  have hSh' : Sec45Shape (conjSubgroup h M) (conjSubgroup h V) (hOf M V h) h⁻¹ :=
    hS.shape_conj_self hU'
  have hmain := Sec45Shape.isHMember_sup_conj (hS.root h) hSh' hyH hyVne
  rw [hconjP, Pc_conjSubgroup, sup_comm] at hmain
  exact hmain

private theorem exists_torus_card {M V : Subgroup G} (hroot : RootHyp M V)
    {H : Subgroup G} {h₀ : G} (hSh : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)}
    {ψ : HBar V H ≃* SL(2, F)} (hw : Sec45ShapeWith M V H F l hl ψ) :
    ∃ T : Subgroup SL(2, F),
      T ≤ Subgroup.normalizer ((imgK V H (Pc M V)).map ψ.toMonoidHom : Set (SL(2, F))) ∧
      Nat.card T = Fintype.card F - 1 ∧ Odd (Nat.card T) ∧ T ≠ ⊥ := by
  classical
  obtain ⟨s, hs_eq⟩ := hSh.exists_map_imgK_eq_conj_utri hroot ψ (x := 1) H.one_mem
  have hA : (imgK V H (Pc M V)).map ψ.toMonoidHom = conjSubgroup s (utri F) := by
    simpa [CGT.Timmesfeld75.conjSubgroup_one] using hs_eq
  have hl1 : 1 ≤ l := hw.one_le
  refine ⟨conjSubgroup s (torus F), ?_, ?_, ?_, ?_⟩
  · rw [hA, CFSG.RankThree.GF2n.Tim78.normalizer_conjSubgroup]
    exact conjSubgroup_mono (by rw [normalizer_utri]; exact torus_le_borel)
  · rw [card_conjSubgroup, card_torus, Nat.card_eq_fintype_card]
  · rw [card_conjSubgroup, card_torus, Nat.card_eq_fintype_card, hl]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  · intro hbot
    have hcard1 : Nat.card (conjSubgroup s (torus F)) = 1 := by rw [hbot]; simp
    rw [card_conjSubgroup, card_torus, Nat.card_eq_fintype_card, hl] at hcard1
    have h4 : 4 ≤ 2 ^ (2 * l) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * l) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

private theorem exists_mem_H₁_piK_eq {V H H₁ : Subgroup G} (hH₁ : H₁ ≤ H)
    (hsup : kOf V H ⊔ H₁ = H) {z : ↥H} :
    ∃ h₁ : ↥H₁, piK V H (Subgroup.inclusion hH₁ h₁) = piK V H z := by
  classical
  have hKnorm : H₁ ≤ Subgroup.normalizer (kOf V H : Set G) :=
    hH₁.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (kOf_le V H)).mp
      (kOf_normal V H))
  have hzH : (z : G) ∈ ((kOf V H ⊔ H₁ : Subgroup G) : Set G) := by
    rw [hsup]
    exact z.2
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (kOf V H) H₁ hKnorm
  rw [hcoe] at hzH
  obtain ⟨k, hk, h₁, hh₁, hkh⟩ := hzH
  refine ⟨⟨h₁, hh₁⟩, ?_⟩
  have hkH : k ∈ H := kOf_le V H hk
  have hhH : h₁ ∈ H := hH₁ hh₁
  let w : ↥H := ⟨k * h₁, H.mul_mem hkH hhH⟩
  have hwz : w = z := Subtype.ext hkh
  have hker : piK V H w = piK V H ⟨h₁, hhH⟩ := by
    have hw : w = ⟨k, hkH⟩ * ⟨h₁, hhH⟩ := Subtype.ext rfl
    rw [hw, map_mul, (piK_eq_one_iff _).mpr hk, one_mul]
  change piK V H (⟨h₁, hH₁ hh₁⟩ : ↥H) = piK V H z
  rw [← hker, show piK V H w = piK V H z from congrArg (piK V H) hwz]

private theorem isPGroup_ker_comp_piK {M V H H₁ : Subgroup G} (hroot : RootHyp M V)
    {h₀ : G} (hSh : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {ψ : HBar V H ≃* SL(2, F)} (hH₁ : H₁ ≤ H) :
    IsPGroup 2 (MonoidHom.ker
      (ψ.toMonoidHom.comp ((piK V H).comp (Subgroup.inclusion hH₁)))) := by
  have h1 : MonoidHom.ker
      (ψ.toMonoidHom.comp ((piK V H).comp (Subgroup.inclusion hH₁))) =
      ((kOf V H).subgroupOf H).comap (Subgroup.inclusion hH₁) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hy
      have hpi : piK V H (Subgroup.inclusion hH₁ y) = 1 :=
        ψ.injective (by simpa using hy)
      exact (piK_eq_one_iff _).mp hpi
    · intro hy
      simp only [MonoidHom.comp_apply, MonoidHom.mem_ker]
      rw [(piK_eq_one_iff _).mpr hy, map_one]
  rw [h1]
  have hK2 : IsPGroup 2 ((kOf V H).subgroupOf H) :=
    (RootHyp.isPGroup_kOf_of_factorization hroot hSh.kFact).of_equiv
      (Subgroup.subgroupOfEquivOfLe (kOf_le V H)).symm
  exact hK2.comap_of_injective (Subgroup.inclusion hH₁) (Subgroup.inclusion_injective hH₁)

private theorem exists_lift_torus {M V : Subgroup G} (hroot : RootHyp M V)
    {H : Subgroup G} {h₀ : G} (hSh : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)}
    {ψ : HBar V H ≃* SL(2, F)} (hw : Sec45ShapeWith M V H F l hl ψ)
    {H₁ : Subgroup G} (hH₁ : H₁ ≤ H) (hsup : kOf V H ⊔ H₁ = H)
    {T : Subgroup SL(2, F)} (hTodd : Odd (Nat.card T)) :
    ∃ R : Subgroup G, R ≤ H₁ ∧ Nat.card R = Nat.card T ∧
      (imgK V H R).map ψ.toMonoidHom = T := by
  classical
  let ε : ↥H₁ →* SL(2, F) :=
    ψ.toMonoidHom.comp ((piK V H).comp (Subgroup.inclusion hH₁))
  have hεsurj : Function.Surjective ε := by
    intro t
    obtain ⟨z, hz⟩ := piK_surjective V H (ψ.symm t)
    obtain ⟨h₁, hh₁⟩ := exists_mem_H₁_piK_eq hH₁ hsup (z := z)
    refine ⟨h₁, ?_⟩
    change ψ (piK V H (Subgroup.inclusion hH₁ h₁)) = t
    rw [hh₁, hz]
    exact MulEquiv.apply_symm_apply ψ t
  have hεker : IsPGroup 2 ε.ker := isPGroup_ker_comp_piK hroot hSh hH₁
  obtain ⟨R, hRε, hRker, hRcard⟩ := Tim78.exists_lift_of_odd ε hεsurj hεker T hTodd
  let RG : Subgroup G := R.map H₁.subtype
  have hRGle : RG ≤ H₁ := by
    intro y hy
    obtain ⟨r, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact r.2
  refine ⟨RG, hRGle, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (K := R) H₁.subtype_injective, hRcard]
  · have h1 : (imgK V H RG).map ψ.toMonoidHom = R.map ε := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, hx, rfl⟩ := mem_imgK_iff.mp hw
        obtain ⟨r, hr, heq⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_map.mpr ⟨r, hr, ?_⟩
        have hx' : x = ⟨(r : G), hH₁ r.2⟩ := Subtype.ext heq.symm
        rw [hx']
        rfl
      · rintro ⟨r, hr, rfl⟩
        refine Subgroup.mem_map.mpr ⟨piK V H ⟨(r : G), hH₁ r.2⟩, ?_, rfl⟩
        exact (mem_imgK_iff).mpr ⟨⟨(r : G), hH₁ r.2⟩,
          Subgroup.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩
    rw [h1]
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) ?_
    · obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
      exact hRε r hr
    · have hcardR : Nat.card (R.map ε) = Nat.card R := by
        have h := Subgroup.relIndex_mul_card (H := ε.ker) (K := R)
        rw [Subgroup.relIndex_ker] at h
        have hinf : ε.ker ⊓ R = ⊥ := by rw [inf_comm]; exact hRker
        rw [hinf] at h
        simpa using h
      rw [hcardR, hRcard]

private theorem le_M_of_imgK_le_normalizer {M V : Subgroup G} (hroot : RootHyp M V)
    {H : Subgroup G} {h₀ : G} (hSh : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {ψ : HBar V H ≃* SL(2, F)}
    {R : Subgroup G} (hR : R ≤ H) {T : Subgroup SL(2, F)}
    (hT : T ≤ Subgroup.normalizer ((imgK V H (Pc M V)).map ψ.toMonoidHom :
      Set (SL(2, F))))
    (himg : (imgK V H R).map ψ.toMonoidHom ≤ T) : R ≤ M := by
  intro r hr
  have hrH : r ∈ H := hR hr
  have hrT : ψ (piK V H ⟨r, hrH⟩) ∈ T := by
    refine himg (Subgroup.mem_map.mpr ⟨piK V H ⟨r, hrH⟩, ?_, rfl⟩)
    exact (mem_imgK_iff).mpr ⟨⟨r, hrH⟩, hr, rfl⟩
  have hN : ψ (piK V H ⟨r, hrH⟩) ∈
      Subgroup.normalizer ((imgK V H (Pc M V)).map ψ.toMonoidHom : Set (SL(2, F))) :=
    hT hrT
  have hN' : ψ (piK V H ⟨r, hrH⟩) ∈
      (Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H))).map ψ.toMonoidHom := by
    rwa [Subgroup.map_equiv_normalizer_eq]
  have hN'' : piK V H ⟨r, hrH⟩ ∈
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
    simpa using (Subgroup.mem_map_equiv (f := ψ)).mp hN'
  exact (RootHyp.mem_M_and_mem_normalizer_inf_of_mem_normalizer_imgK hroot hSh.Pc_le hN'').1

private theorem mem_xOf_of_mem_inf_Pc_kOf_centralizer {M V : Subgroup G} (hroot : RootHyp M V)
    {H : Subgroup G} {h₀ : G} (hSh : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)}
    {ψ : HBar V H ≃* SL(2, F)} (hw : Sec45ShapeWith M V H F l hl ψ)
    {T : Subgroup SL(2, F)} (hTodd : Odd (Nat.card T)) (hTne : T ≠ ⊥)
    (hTN : T ≤ Subgroup.normalizer ((imgK V H (Pc M V)).map ψ.toMonoidHom :
      Set (SL(2, F))))
    {R : Subgroup G} (himg : (imgK V H R).map ψ.toMonoidHom = T) :
    ∀ m ∈ Pc M V ⊓ kOf V H, m ∈ Subgroup.centralizer (R : Set G) → m ∈ Tim79a.xOf V H := by
  classical
  have hsyl := hSh.map_imgK_conj_sylow hroot ψ (x := 1) H.one_mem
  have hA2 : ∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom, a * a = 1 := by
    simpa [CGT.Timmesfeld75.conjSubgroup_one] using hsyl.1
  have hAcard : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = Fintype.card F := by
    simpa [CGT.Timmesfeld75.conjSubgroup_one] using hsyl.2
  have hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H) := hSh.isElemAbelian hroot
  haveI hmodW : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have hs : QuotMod.Hyp H (kOf V H) (Tim79a.xOf V H) := hSh.quotModHyp hroot
  haveI hKnormal : ((Tim79a.xOf V H).subgroupOf (kOf V H)).Normal := hs.normal
  haveI hmodK : Module (ZMod 2) (SecMod hs) := SecMod.module hs hw.sq_mem
  have hσ : Sec2.IsNatSumModule (repSec hs hs.comm SL(2, F) ψ) :=
    hw.natSum hs (inferInstance : Module (ZMod 2) (SecMod hs))
  intro m hm hmC
  have hmP : m ∈ Pc M V := (Subgroup.mem_inf.mp hm).1
  have hmK : m ∈ kOf V H := (Subgroup.mem_inf.mp hm).2
  have hfixA : SecMod.mk hs ⟨m, hmK⟩ ∈
      fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) := by
    rw [Sec45Shape.fixedSub_repSec_Pc hroot hSh hw hs]
    exact (mk_mem_subSec_iff hs le_sup_right).mpr (Subgroup.mem_sup_left ⟨hmP, hmK⟩)
  have hfixT : SecMod.mk hs ⟨m, hmK⟩ ∈
      fixedSub (repSec hs hs.comm SL(2, F) ψ) T := by
    rw [← himg, mem_fixedSub]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨r, hr, rfl⟩ := (mem_imgK_iff).mp hb
    change repSec hs hs.comm SL(2, F) ψ (ψ (piK V H r)) (SecMod.mk hs ⟨m, hmK⟩) =
      SecMod.mk hs ⟨m, hmK⟩
    rw [show repSec hs hs.comm SL(2, F) ψ (ψ (piK V H r)) (SecMod.mk hs ⟨m, hmK⟩) =
        SecMod.mk hs (⟨(r : G) * m * (r : G)⁻¹,
          hs.conj r r.2 m hmK⟩ : ↥(kOf V H)) from
      repSec_apply_piK_mk hs hs.comm SL(2, F) ψ r ⟨m, hmK⟩]
    congr 1
    apply Subtype.ext
    change (r : G) * m * (r : G)⁻¹ = m
    have hcomm : (r : G) * m = m * (r : G) := Subgroup.mem_centralizer_iff.mp hmC r hr
    rw [hcomm]
    group
  have hbot := Sec2.IsNatSumModule.fixedSub_inf_fixedSub_eq_bot hσ hA2 hAcard hTN hTodd hTne
  have hmem : SecMod.mk hs ⟨m, hmK⟩ ∈
      fixedSub (repSec hs hs.comm SL(2, F) ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) ⊓
        fixedSub (repSec hs hs.comm SL(2, F) ψ) T :=
    Submodule.mem_inf.mpr ⟨hfixA, hfixT⟩
  rw [hbot] at hmem
  have hzero : SecMod.mk hs ⟨m, hmK⟩ = 0 := by simpa using hmem
  exact (SecMod.mk_eq_zero_iff hs ⟨m, hmK⟩).mp hzero

private theorem inf_xOf_centralizer_eq_bot {M V : Subgroup G} (hroot : RootHyp M V)
    {H : Subgroup G} {h₀ : G} (hSh : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    {hl : Fintype.card F = 2 ^ (2 * l)}
    {ψ : HBar V H ≃* SL(2, F)} (hw : Sec45ShapeWith M V H F l hl ψ)
    {T : Subgroup SL(2, F)} (hTN : T ≤ Subgroup.normalizer
      ((imgK V H (Pc M V)).map ψ.toMonoidHom : Set (SL(2, F))))
    (hTcard : Nat.card T = 2 ^ (2 * l) - 1)
    {R : Subgroup G} (hR : R ≤ H)
    (himg : (imgK V H R).map ψ.toMonoidHom = T) :
    Tim79a.xOf V H ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
  classical
  have hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H) := hSh.isElemAbelian hroot
  haveI hmodW : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW hW ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  have hsyl := hSh.map_imgK_conj_sylow hroot ψ (x := 1) H.one_mem
  have hA2 : ∀ a ∈ (imgK V H (Pc M V)).map ψ.toMonoidHom, a * a = 1 := by
    simpa [CGT.Timmesfeld75.conjSubgroup_one] using hsyl.1
  have hAcard : Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = 2 ^ (2 * l) := by
    rw [show Nat.card ((imgK V H (Pc M V)).map ψ.toMonoidHom) = Fintype.card F from
      (by simpa [CGT.Timmesfeld75.conjSubgroup_one] using hsyl.2), hl]
  have hl2 : 2 ≤ l := by
    by_contra h
    have h1 : l ≤ 1 := by omega
    have h2 : 2 ^ l ≤ 2 := by
      calc 2 ^ l ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    have h4 := hroot.four_le_card
    rw [hw.card_V] at h4
    omega
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfix := horth.fixedSub_eq_bot_of_torus hl2 hA2 hAcard hTN hTcard
  have hfixed : fixedSub (repW hW ψ) T =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer (R : Set G)) := by
    rw [← himg]
    exact fixedSub_repW hW ψ hR
  rw [hfixed] at hfix
  rw [eq_bot_iff]
  intro m hm
  have hmW : m ∈ Tim79a.xOf V H := (Subgroup.mem_inf.mp hm).1
  have hmC : m ∈ Subgroup.centralizer (R : Set G) := (Subgroup.mem_inf.mp hm).2
  have hmem : ofW hW ⟨m, hmW⟩ ∈
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer (R : Set G)) :=
    (mem_subW_iff hW).mpr ⟨hmW, hmC⟩
  rw [hfix] at hmem
  have hzero : ofW hW ⟨m, hmW⟩ = 0 := by simpa using hmem
  have h1 : (⟨m, hmW⟩ : ↥(Tim79a.xOf V H)) = 1 :=
    ofW_injective hW (by rw [hzero, ofW_one hW])
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

private theorem exists_torus_lift (hS : Sec5Hyp M V) {h : G}
    (hU' : conjSubgroup h V ∈ sigmaSet M V) {H₁ : Subgroup G} (hH₁ : H₁ ≤ hOf M V h)
    (hsup : kOf V (hOf M V h) ⊔ H₁ = hOf M V h) :
    ∃ R : Subgroup G, R ≤ H₁ ∧ R ≤ M ∧ Odd (Nat.card R) ∧
      ∀ m ∈ Pc M V ⊓ kOf V (hOf M V h), m ∈ Subgroup.centralizer (R : Set G) → m = 1 := by
  classical
  have hroot := hS.toRootHyp
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hU'
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hSh.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  obtain ⟨T, hTN, hTcardF, hTodd, hTne⟩ := exists_torus_card hroot hSh hw
  have hTcard : Nat.card T = 2 ^ (2 * l) - 1 := by
    rw [hTcardF, hl]
  obtain ⟨R, hRle, hRcard, himg⟩ :=
    exists_lift_torus hroot hSh hw hH₁ hsup hTodd
  have hRleH : R ≤ hOf M V h := hRle.trans hH₁
  have hRM : R ≤ M := le_M_of_imgK_le_normalizer hroot hSh hRleH hTN himg.le
  have hRodd : Odd (Nat.card R) := by rw [hRcard]; exact hTodd
  refine ⟨R, hRle, hRM, hRodd, fun m hm hmC => ?_⟩
  have hmW :=
    mem_xOf_of_mem_inf_Pc_kOf_centralizer hroot hSh hw hTodd hTne hTN himg m hm hmC
  have hbot := inf_xOf_centralizer_eq_bot hroot hSh hw hTN hTcard hRleH himg
  have hmem : m ∈ Tim79a.xOf V (hOf M V h) ⊓ Subgroup.centralizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨hmW, hmC⟩
  rw [hbot] at hmem
  simpa using hmem

private theorem exists_conj_eq_of_mem_M (hS : Sec5Hyp M V) {g : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) {x p₀ x₂ r : G} (hx : x ∈ conjSubgroup g V)
    (hx1 : x ≠ 1) (hp₀ : p₀ ∈ Pc M V) (hxeq : x = p₀ * x₂) (hrM : r ∈ M)
    (hr : r * x₂ * r⁻¹ = x₂) : ∃ p ∈ Pc M V, r * x * r⁻¹ = p * x * p⁻¹ := by
  classical
  have hroot := hS.toRootHyp
  have hxM : x ∈ M := (hS.le_M_of_mem_sigmaSet hU).1 hx
  have hrN : r ∈ Subgroup.normalizer (Pc M V : Set G) := hroot.toHyp.le_normalizer_Pc hrM
  have hxN : x ∈ Subgroup.normalizer (Pc M V : Set G) := hroot.toHyp.le_normalizer_Pc hxM
  have hconj : r * p₀ * r⁻¹ ∈ Pc M V :=
    (Subgroup.mem_normalizer_iff.mp hrN p₀).mp hp₀
  have hpP : r * p₀ * r⁻¹ * p₀⁻¹ ∈ Pc M V :=
    (Pc M V).mul_mem hconj ((Pc M V).inv_mem hp₀)
  have hp : x⁻¹ * (r * p₀ * r⁻¹ * p₀⁻¹) * x ∈ Pc M V := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp hpP
  have hxP' : r * (p₀ * x₂) * r⁻¹ =
      (p₀ * x₂) * ((p₀ * x₂)⁻¹ * (r * p₀ * r⁻¹ * p₀⁻¹) * (p₀ * x₂)) := by
    calc r * (p₀ * x₂) * r⁻¹ = (r * p₀ * r⁻¹) * (r * x₂ * r⁻¹) := by group
      _ = (r * p₀ * r⁻¹) * x₂ := by rw [hr]
      _ = (p₀ * x₂) * ((p₀ * x₂)⁻¹ * (r * p₀ * r⁻¹ * p₀⁻¹) * (p₀ * x₂)) := by group
  have hxP : r * x * r⁻¹ = x * (x⁻¹ * (r * p₀ * r⁻¹ * p₀⁻¹) * x) := by
    rw [hxeq]
    exact hxP'
  exact Sec5Hyp.stmt55e hS (conjSubgroup g V) hU x hx hx1 r hrM ⟨_, hp, hxP⟩

private theorem mem_Pc_inf_kOf_mul_inv (hS : Sec5Hyp M V) {g h : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) (hU' : conjSubgroup h V ∈ sigmaSet M V)
    (hKF : ∀ u ∈ conjSubgroup g V, (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
      u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    {x p₀ x₂ q : G} (hx : x ∈ conjSubgroup g V)
    (hp₀ : p₀ ∈ Pc M V ⊓ kOf V (hOf M V h)) (hxeq : x = p₀ * x₂)
    (hqP : q ∈ Pc M V) :
    (q * x * q⁻¹) * x₂⁻¹ ∈ Pc M V ⊓ kOf V (hOf M V h) := by
  have hroot := hS.toRootHyp
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hU'
  have h1 : (q * x * q⁻¹) * x₂⁻¹ = ⁅q, x⁆ * p₀ := by
    have hx₂ : x₂⁻¹ = x⁻¹ * p₀ := by rw [hxeq]; group
    rw [hx₂, commutatorElement_def]
    group
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h1]
    exact (Pc M V).mul_mem
      (hS.commutator_le_Pc hU (Subgroup.commutator_mem_commutator hqP hx))
      (Subgroup.mem_inf.mp hp₀).1
  · rw [h1]
    have hxq : ⁅x, q⁆ ∈ kOf V (hOf M V h) := (hKF x hx).1 q (hSh.Pc_le hqP)
    have hqx : ⁅q, x⁆ ∈ kOf V (hOf M V h) := by
      rw [← commutatorElement_inv x q]
      exact (kOf V (hOf M V h)).inv_mem hxq
    exact (kOf V (hOf M V h)).mul_mem hqx (Subgroup.mem_inf.mp hp₀).2

private theorem exists_mem_inf_Pc_kOf_conj_eq (hS : Sec5Hyp M V) {g h : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) (hU' : conjSubgroup h V ∈ sigmaSet M V)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))
    {x q : G} (hx : x ∈ conjSubgroup g V) (hqP : q ∈ Pc M V) :
    ∃ k ∈ Pc M V ⊓ kOf V (hOf M V h), q * x * q⁻¹ = k * x * k⁻¹ := by
  classical
  have hroot := hS.toRootHyp
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hU'
  have hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    obtain ⟨y, hyH, -, hVy, -⟩ := hroot.exists_mem_conj_eq_of_eq_sup hSh.Pc_le hSh.hH
    have hyVne : conjSubgroup y V ≠ V := by
      rw [← hVy]
      exact ne_of_mem_sigmaSet hroot hU'
    rw [hVy]
    exact hSh.Pc_inf_centralizer_conj hroot hyH hyVne
  have hCnorm : Pc M V ≤ Subgroup.normalizer
      (((Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    calc ⁅Pc M V, Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)⁆ ≤
          ⁅Pc M V, Pc M V⁆ := Subgroup.commutator_mono le_rfl inf_le_left
      _ = V := hSh.commutator_Pc hroot
      _ ≤ Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G) :=
          le_inf hroot.toHyp.le_Pc (Subgroup.le_centralizer_iff.mpr
            (hS.le_M_of_mem_sigmaSet hU).2)
  have hq' : q ∈ (((Pc M V ⊓ kOf V (hOf M V h)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) : Subgroup G) : Set G) := by
    rw [sup_comm, ← hCcK, ← hPC]
    exact hqP
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
    (Pc M V ⊓ kOf V (hOf M V h))
    (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G))
    (inf_le_left.trans hCnorm)
  rw [hcoe] at hq'
  obtain ⟨k, hk, c, hc, rfl⟩ := hq'
  have hcx : c * x * c⁻¹ = x := by
    have h1 : x * c = c * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 x hx
    rw [← h1]
    group
  refine ⟨k, hk, ?_⟩
  calc (k * c) * x * (k * c)⁻¹ = k * (c * x * c⁻¹) * k⁻¹ := by group
    _ = k * x * k⁻¹ := by rw [hcx]

private theorem exists_mem_Pc_inf_kOf_mul_conj (hS : Sec5Hyp M V) {g h : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) (hU' : conjSubgroup h V ∈ sigmaSet M V)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))
    (hKF : ∀ u ∈ conjSubgroup g V, (∀ z ∈ hOf M V h, ⁅u, z⁆ ∈ kOf V (hOf M V h)) ∧
      u ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V h) : Set G))
    {H₁ : Subgroup G} (hH₁ : H₁ ≤ hOf M V h)
    (hsup : kOf V (hOf M V h) ⊔ H₁ = hOf M V h)
    {x p₀ x₂ : G} (hx : x ∈ conjSubgroup g V) (hx1 : x ≠ 1)
    (hp₀ : p₀ ∈ Pc M V ⊓ kOf V (hOf M V h))
    (hxeq : x = p₀ * x₂)
    (hx₂cent : x₂ ∈ Subgroup.centralizer (H₁ : Set G)) :
    ∃ k ∈ Pc M V ⊓ kOf V (hOf M V h), x₂ = k * x * k⁻¹ := by
  classical
  have hroot := hS.toRootHyp
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hU'
  obtain ⟨R, hRle, hRM, hRodd, hRfree⟩ := exists_torus_lift hS hU' hH₁ hsup
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hRN : R ≤ Subgroup.normalizer (Pc M V : Set G) :=
    hRM.trans hroot.toHyp.le_normalizer_Pc
  have hxconj : ∀ r ∈ R, ∃ p ∈ Pc M V, r * x * r⁻¹ = p * x * p⁻¹ := by
    intro r hr
    have hcomm : r * x₂ = x₂ * r :=
      Subgroup.mem_centralizer_iff.mp hx₂cent r (hRle hr)
    have hrx₂ : r * x₂ * r⁻¹ = x₂ := by rw [hcomm]; group
    exact exists_conj_eq_of_mem_M hS hU hx hx1 (Subgroup.mem_inf.mp hp₀).1 hxeq
      (hRM hr) hrx₂
  obtain ⟨q, hqP, hqfix⟩ := exists_conj_fixed hP2 hRodd hRN hxconj
  have hm : (q * x * q⁻¹) * x₂⁻¹ ∈ Pc M V ⊓ kOf V (hOf M V h) :=
    mem_Pc_inf_kOf_mul_inv hS hU hU' hKF hx hp₀ hxeq hqP
  have hmC : (q * x * q⁻¹) * x₂⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h2 : r * x₂ * r⁻¹ = x₂ := by
      have hcomm : r * x₂ = x₂ * r :=
        Subgroup.mem_centralizer_iff.mp hx₂cent r (hRle hr)
      rw [hcomm]; group
    have hconj : r * ((q * x * q⁻¹) * x₂⁻¹) * r⁻¹ = (q * x * q⁻¹) * x₂⁻¹ := by
      calc r * ((q * x * q⁻¹) * x₂⁻¹) * r⁻¹
          = (r * (q * x * q⁻¹) * r⁻¹) * (r * x₂ * r⁻¹)⁻¹ := by group
        _ = (q * x * q⁻¹) * x₂⁻¹ := by rw [hqfix r hr, h2]
    calc r * ((q * x * q⁻¹) * x₂⁻¹)
        = (r * ((q * x * q⁻¹) * x₂⁻¹) * r⁻¹) * r := by group
      _ = ((q * x * q⁻¹) * x₂⁻¹) * r := by rw [hconj]
  have hm1 : (q * x * q⁻¹) * x₂⁻¹ = 1 := hRfree _ hm hmC
  have hz : q * x * q⁻¹ = x₂ := by
    calc q * x * q⁻¹ = (q * x * q⁻¹) * x₂⁻¹ * x₂ := by group
      _ = 1 * x₂ := by rw [hm1]
      _ = x₂ := one_mul x₂
  obtain ⟨k, hk, hkq⟩ := exists_mem_inf_Pc_kOf_conj_eq hS hU hU' hPC hx hqP
  refine ⟨k, hk, ?_⟩
  rw [← hz, hkq]

private theorem le_normalizer_conjSubgroup_of_centralizer {M V H₁ : Subgroup G}
    (hroot : RootHyp M V)
    {k g x₂ : G} (hx₂ : x₂ ∈ Subgroup.centralizer (H₁ : Set G))
    (hx₂U : x₂ ∈ conjSubgroup (k * g) V) (hx₂1 : x₂ ≠ 1)
    (hN : conjSubgroup (k * g) M = Subgroup.normalizer (conjSubgroup (k * g) V : Set G)) :
    H₁ ≤ Subgroup.normalizer (conjSubgroup (k * g) V : Set G) := by
  have hcent : H₁ ≤ Subgroup.centralizer ({x₂} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hx₂ z hz
  calc H₁ ≤ Subgroup.centralizer ({x₂} : Set G) := hcent
    _ ≤ conjSubgroup (k * g) M := hroot.toHyp.centralizer_conj_singleton_le hx₂U hx₂1
    _ = Subgroup.normalizer (conjSubgroup (k * g) V : Set G) := hN

private theorem isHMember_conj_mem_sigmaSet {M V : Subgroup G} (hroot : RootHyp M V)
    (hS : Sec5Hyp M V) {g k : G} (hU : conjSubgroup g V ∈ sigmaSet M V) (hkM : k ∈ M) :
    IsHMember (conjSubgroup (k * g) M) (conjSubgroup (k * g) V)
      (Pc M V ⊔ conjSubgroup (k * g) (Pc M V)) := by
  have hUk : conjSubgroup (k * g) V ∈ sigmaSet M V := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hS.conj_mem_sigmaSet hkM hU
  exact (hroot.isHMember_hOf_conj_iff (g := k * g)).mpr
    ((mem_sigmaSet_iff hroot.toHyp).mp hUk)

private theorem exists_conj_data (hS : Sec5Hyp M V) {g h : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) (hU' : conjSubgroup h V ∈ sigmaSet M V)
    {H₁ : Subgroup G} (hH₁ : H₁ ≤ hOf M V h)
    (hsup : kOf V (hOf M V h) ⊔ H₁ = hOf M V h)
    {k x₂ : G} (hkP : k ∈ Pc M V) (hkK : k ∈ kOf V (hOf M V h))
    (hx₂ : x₂ ∈ Subgroup.centralizer (H₁ : Set G))
    (hx₂U : x₂ ∈ conjSubgroup (k * g) V) (hx₂1 : x₂ ≠ 1) :
    IsHMember (conjSubgroup (k * g) M) (conjSubgroup (k * g) V)
        (Pc M V ⊔ conjSubgroup (k * g) (Pc M V)) ∧
      k ∈ Subgroup.centralizer (conjSubgroup h V : Set G) ∧
      ∃ x' ∈ H₁, conjSubgroup x' (Pc M V) = conjSubgroup h (Pc M V) ∧
        x' ∈ conjSubgroup (k * g) M ∧
        x' ∈ Subgroup.normalizer (conjSubgroup (k * g) (Pc M V) : Set G) ∧
        H₁ ≤ Subgroup.normalizer (conjSubgroup (k * g) V : Set G) := by
  classical
  have hroot := hS.toRootHyp
  have hkM : k ∈ M := hroot.toHyp.Pc_le_M hkP
  have hUmem := isHMember_conj_mem_sigmaSet hroot hS hU hkM
  have hN : conjSubgroup (k * g) M =
      Subgroup.normalizer (conjSubgroup (k * g) V : Set G) := by
    rw [CFSG.RankThree.GF2n.Tim78.normalizer_conjSubgroup, hroot.toHyp.normalizer_eq]
  have hx'N := le_normalizer_conjSubgroup_of_centralizer hroot hx₂ hx₂U hx₂1 hN
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hU'
  obtain ⟨y, hyH, -, hVy, -⟩ := hroot.exists_mem_conj_eq_of_eq_sup hSh.Pc_le hSh.hH
  have hKc : k ∈ Subgroup.centralizer (conjSubgroup h V : Set G) := by
    rw [hVy]
    exact RootHyp.kOf_le_centralizer_conjSubgroup_of_mem (V := V) (H := hOf M V h) hyH hkK
  have hHnormK : hOf M V h ≤ Subgroup.normalizer (kOf V (hOf M V h) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (kOf_le V (hOf M V h))).mp
      (kOf_normal V (hOf M V h))
  have hyH' : y ∈ (kOf V (hOf M V h) : Set G) * (H₁ : Set G) := by
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (kOf V (hOf M V h)) H₁
      (hH₁.trans hHnormK)
    rw [← hcoe, hsup]
    exact hyH
  obtain ⟨k₁, hk₁K, x', hx'H₁, rfl⟩ := hyH'
  have hVx' : conjSubgroup x' V = conjSubgroup h V := by
    have hk₁cent : k₁ ∈ Subgroup.centralizer (conjSubgroup x' V : Set G) :=
      RootHyp.kOf_le_centralizer_conjSubgroup_of_mem (V := V) (H := hOf M V h) (hH₁ hx'H₁) hk₁K
    have hfix : conjSubgroup k₁ (conjSubgroup x' V) = conjSubgroup x' V :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hk₁cent)
    calc conjSubgroup x' V = conjSubgroup k₁ (conjSubgroup x' V) := hfix.symm
      _ = conjSubgroup (k₁ * x') V := CGT.Timmesfeld75.conjSubgroup_conjSubgroup k₁ x' V
      _ = conjSubgroup h V := hVy.symm
  have hPx' : conjSubgroup x' (Pc M V) = conjSubgroup h (Pc M V) :=
    hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hVx'
  have hx'U : x' ∈ conjSubgroup (k * g) M := by
    have hN : conjSubgroup (k * g) M =
        Subgroup.normalizer (conjSubgroup (k * g) V : Set G) := by
      rw [CFSG.RankThree.GF2n.Tim78.normalizer_conjSubgroup, hroot.toHyp.normalizer_eq]
    rw [hN]
    exact hx'N hx'H₁
  have hx'PU : x' ∈ Subgroup.normalizer (conjSubgroup (k * g) (Pc M V) : Set G) := by
    have hMP : conjSubgroup (k * g) M ≤
        Subgroup.normalizer (conjSubgroup (k * g) (Pc M V) : Set G) := by
      rw [CFSG.RankThree.GF2n.Tim78.normalizer_conjSubgroup]
      exact Subgroup.map_mono (f := (MulAut.conj (k * g)).toMonoidHom)
        hroot.toHyp.le_normalizer_Pc
    exact hMP hx'U
  exact ⟨hUmem, hKc, x', hx'H₁, hPx', hx'U, hx'PU, hx'N⟩

private theorem isHMember_of_conj_stepA {M V : Subgroup G} (hroot : RootHyp M V) {g h k : G}
    (hKc : k ∈ Subgroup.centralizer (conjSubgroup h V : Set G))
    (hstepA : IsHMember (conjSubgroup (k * g) M) (conjSubgroup (k * g) V)
      (conjSubgroup h (Pc M V) ⊔ conjSubgroup (k * g) (Pc M V))) :
    IsHMember (conjSubgroup h M) (conjSubgroup h V)
      (conjSubgroup g (Pc M V) ⊔ conjSubgroup h (Pc M V)) := by
  classical
  have hPk : conjSubgroup k⁻¹ (conjSubgroup h (Pc M V)) = conjSubgroup h (Pc M V) := by
    have hVk : conjSubgroup (k⁻¹ * h) V = conjSubgroup h V := by
      rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      have hkinv : k⁻¹ ∈ Subgroup.centralizer (conjSubgroup h V : Set G) :=
        (Subgroup.centralizer (conjSubgroup h V : Set G)).inv_mem hKc
      exact conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hkinv)
    calc conjSubgroup k⁻¹ (conjSubgroup h (Pc M V)) =
        conjSubgroup (k⁻¹ * h) (Pc M V) := CGT.Timmesfeld75.conjSubgroup_conjSubgroup k⁻¹ h (Pc M V)
      _ = conjSubgroup h (Pc M V) :=
        hroot.toHyp.conjSubgroup_Pc_eq_of_conjSubgroup_eq hVk
  have hstepB : IsHMember (conjSubgroup g M) (conjSubgroup g V)
      (conjSubgroup h (Pc M V) ⊔ conjSubgroup g (Pc M V)) := by
    have h1 := (isHMember_conjSubgroup_iff (a := k⁻¹)
      (M := conjSubgroup (k * g) M) (V := conjSubgroup (k * g) V)
      (L := conjSubgroup h (Pc M V) ⊔ conjSubgroup (k * g) (Pc M V))).mpr hstepA
    rw [conjSubgroup_sup, hPk,
      show conjSubgroup k⁻¹ (conjSubgroup (k * g) (Pc M V)) = conjSubgroup g (Pc M V) from by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, show k⁻¹ * (k * g) = g by group],
      show conjSubgroup k⁻¹ (conjSubgroup (k * g) M) = conjSubgroup g M from by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, show k⁻¹ * (k * g) = g by group],
      show conjSubgroup k⁻¹ (conjSubgroup (k * g) V) = conjSubgroup g V from by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, show k⁻¹ * (k * g) = g by group]] at h1
    exact h1
  exact (RootHyp.isHMember_sup_conj_comm hroot g h).mp (by rwa [sup_comm] at hstepB)

private theorem isHMember_of_split_data (hS : Sec5Hyp M V) {g h : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) (hU' : conjSubgroup h V ∈ sigmaSet M V)
    {H₁ : Subgroup G} (hH₁ : H₁ ≤ hOf M V h)
    (hsup : kOf V (hOf M V h) ⊔ H₁ = hOf M V h)
    {k x₂ : G} (hkP : k ∈ Pc M V) (hkK : k ∈ kOf V (hOf M V h))
    (hx₂ : x₂ ∈ Subgroup.centralizer (H₁ : Set G))
    (hx₂U : x₂ ∈ conjSubgroup (k * g) V) (hx₂1 : x₂ ≠ 1) :
    IsHMember (conjSubgroup h M) (conjSubgroup h V)
      (conjSubgroup g (Pc M V) ⊔ conjSubgroup h (Pc M V)) := by
  classical
  have hroot := hS.toRootHyp
  obtain ⟨hUmem, hKc, x', hx'H₁, hPx', hx'U, hx'PU, hx'N⟩ :=
    exists_conj_data hS hU hU' hH₁ hsup hkP hkK hx₂ hx₂U hx₂1
  refine isHMember_of_conj_stepA hroot hKc ?_
  have h1 := (isHMember_conjSubgroup_iff (a := x')
    (M := conjSubgroup (k * g) M) (V := conjSubgroup (k * g) V)
    (L := Pc M V ⊔ conjSubgroup (k * g) (Pc M V))).mpr hUmem
  rw [conjSubgroup_sup, hPx',
    show conjSubgroup x' (conjSubgroup (k * g) (Pc M V)) =
      conjSubgroup (k * g) (Pc M V) from conjSubgroup_eq_self_iff.mpr hx'PU,
    show conjSubgroup x' (conjSubgroup (k * g) M) = conjSubgroup (k * g) M from
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hx'U),
    show conjSubgroup x' (conjSubgroup (k * g) V) = conjSubgroup (k * g) V from
      conjSubgroup_eq_self_iff.mpr (hx'N hx'H₁)] at h1
  exact h1

private theorem isHMember_case_sup (hS : Sec5Hyp M V) {g h : G}
    (hU : conjSubgroup g V ∈ sigmaSet M V) (hU' : conjSubgroup h V ∈ sigmaSet M V)
    (hc : ⁅conjSubgroup g V, conjSubgroup h V⁆ = ⊥)
    (hPC : Pc M V = (Pc M V ⊓ Subgroup.centralizer (conjSubgroup g V : Set G)) ⊔
      (Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G)))
    (h57 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt57 M' V') :
    IsHMember (conjSubgroup h M) (conjSubgroup h V)
      (conjSubgroup g (Pc M V) ⊔ conjSubgroup h (Pc M V)) := by
  classical
  have hroot := hS.toRootHyp
  have hSh : Sec45Shape M V (hOf M V h) h := hS.shape hU'
  obtain ⟨y, hyH, -, hVy, -⟩ := hroot.exists_mem_conj_eq_of_eq_sup hSh.Pc_le hSh.hH
  have hyVne : conjSubgroup y V ≠ V := by
    rw [← hVy]
    exact ne_of_mem_sigmaSet hroot hU'
  have hCcK : Pc M V ⊓ Subgroup.centralizer (conjSubgroup h V : Set G) =
      Pc M V ⊓ kOf V (hOf M V h) := by
    rw [hVy]
    exact hSh.Pc_inf_centralizer_conj hroot hyH hyVne
  have hVg_ne : conjSubgroup g V ≠ ⊥ := by
    intro hbot
    have hVbot : V = ⊥ := by
      have h1 := congrArg (conjSubgroup g⁻¹) hbot
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
      simpa [CGT.Timmesfeld75.conjSubgroup] using h1
    exact hroot.toHyp.ne_bot hVbot
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVg_ne
  have hxU : (x : G) ∈ conjSubgroup g V := x.2
  have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hKF := forall_commutator_mem_kOf_of_commute hS hU hU' hc h57
  obtain ⟨H₁, hH₁, hsup, p₀, hp₀, x₂, hxeq, hx₂cent⟩ :=
    Sec5Hyp.s512_split hS hU' hc hKF hPC hxU
  obtain ⟨k, hk, hkx⟩ :=
    exists_mem_Pc_inf_kOf_mul_conj hS hU hU' hPC hKF hH₁ hsup hxU hx1' hp₀ hxeq hx₂cent
  have hkP : k ∈ Pc M V := (Subgroup.mem_inf.mp hk).1
  have hkK : k ∈ kOf V (hOf M V h) := (Subgroup.mem_inf.mp hk).2
  have hx₂1 : x₂ ≠ 1 := by
    rw [hkx]
    intro h1
    apply hx1'
    calc (x : G) = k⁻¹ * (k * (x : G) * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  have hx₂U : x₂ ∈ conjSubgroup (k * g) V := by
    rw [hkx, ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact Subgroup.mem_map.mpr ⟨(x : G), hxU, rfl⟩
  exact isHMember_of_split_data hS hU hU' hH₁ hsup hkP hkK hx₂cent hx₂U hx₂1

theorem stmt512 (hS : Sec5Hyp M V)
    (h57 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt57 M' V')
    (h58 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt58 M' V') :
    Sec5.Stmt512 M V := by
  intro g h hU' hU hc hne
  rcases h58 M V hS g h hU' hU hc with hEq | hPC
  · exact isHMember_case_eq hS hU' hne hEq
  · exact isHMember_case_sup hS hU hU' hc hPC h57

end Sec5Hyp

end CFSG.RankThree.GF2n.Tim81
