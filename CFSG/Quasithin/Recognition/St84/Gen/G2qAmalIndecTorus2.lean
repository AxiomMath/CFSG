module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecTorus


public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

private theorem conj_mem_of_mem_normalizer {G : Type*} [Group G] {K : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) : g * k * g⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp hg k).mp hk

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

attribute [local instance] G2qCoord.field G2qCoord.fintype

private abbrev IsEquivSec {L E : Subgroup G} {F : Type} [Field F] (α : ↥L →* SL(2, F))
    (β : ↥E →* Multiplicative (Fin 2 → F)) : Prop :=
  ∀ ℓ : ↥L, ∀ u v : ↥E, (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

private theorem le_left_of_g2q (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L1 :=
  (hD.borelOf_inf_borelOf hH h1 h2).symm.le.trans (inf_le_left.trans (borelOf_le L1 S))

private theorem le_right_of_g2q (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L2 :=
  (hD.borelOf_inf_borelOf hH h1 h2).symm.le.trans (inf_le_right.trans (borelOf_le L2 S))

private theorem conj_mul_inv_mem_centerOf_left (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) {h : G}
    (hhQ2 : h ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G)) (ht1 : h ∈ trivOTwoQuot L1)
    (hcent : ∀ w ∈ c.W, ⁅h, w⁆ ∈ centerOf (pCoreOf 2 L2)) {z : G}
    (hz : z ∈ centerOf (pCoreOf 2 L2)) : h * z * h⁻¹ * z⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
  have hSL1 := le_left_of_g2q hH hD h1 h2
  have hZ1 : ∀ {x y : G}, x ∈ L1 → y ∈ centerOf (pCoreOf 2 L1) →
      x * y * x⁻¹ ∈ centerOf (pCoreOf 2 L1) := fun hx hy =>
    mem_centerOf_conj_of_mem_normalizer (le_normalizer_pCoreOf 2 L1 hx) hy
  have key : ∀ y ∈ Subgroup.closure {x | ∃ w ∈ c.W, ∃ a ∈ pCoreOf 2 L2, x = ⁅w, a⁆},
      y ∈ L1 ∧ h * y * h⁻¹ * y⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, a, ha, rfl⟩ := hx
      have hwQ2 := c.le_pCoreOf hw
      have hZwa : ⁅w, a⁆ ∈ centerOf (pCoreOf 2 L2) :=
        c.commutator_le (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 ha))
      refine ⟨hSL1 (hH.pCoreOf_le_right (Subgroup.mem_inf.mp hZwa).1), ?_⟩
      have hk1 : h * a * h⁻¹ * a⁻¹ ∈ pCoreOf 2 L1 :=
        (mem_trivOTwoQuot.mp ht1).2 a (hSL1 (hH.pCoreOf_le_right ha))
      have hk2 : h * a * h⁻¹ * a⁻¹ ∈ pCoreOf 2 L2 :=
        mul_mem (conj_mem_of_mem_normalizer hhQ2 ha) (inv_mem ha)
      have e1 : h * ⁅w, a⁆ * h⁻¹ = ⁅⁅h, w⁆ * w, (h * a * h⁻¹ * a⁻¹) * a⁆ := by
        simp only [commutatorElement_def]
        group
      have hcomm : (h * a * h⁻¹ * a⁻¹) * ⁅w, a⁆ * (h * a * h⁻¹ * a⁻¹)⁻¹ = ⁅w, a⁆ := by
        rw [mul_comm_of_mem_centerOf hZwa hk2, mul_inv_cancel_right]
      have e2 : ⁅w, (h * a * h⁻¹ * a⁻¹) * a⁆ * ⁅w, a⁆⁻¹ = ⁅w, h * a * h⁻¹ * a⁻¹⁆ *
          ((h * a * h⁻¹ * a⁻¹) * ⁅w, a⁆ * (h * a * h⁻¹ * a⁻¹)⁻¹ * ⁅w, a⁆⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e1, commutator_mul_left_eq_of_mem_centerOf (hcent w hw) hwQ2 (mul_mem hk2 ha), e2,
        hcomm, mul_inv_cancel, mul_one]
      exact hD.commutator_mem_centerOf_left (c.W_le_pCoreOf_left hH hD h1 h2 hw) hk1
    | one => exact ⟨one_mem _, by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨mul_mem hx.1 hy.1, ?_⟩
      rw [show h * (x * y) * h⁻¹ * (x * y)⁻¹ =
        (h * x * h⁻¹ * x⁻¹) * (x * (h * y * h⁻¹ * y⁻¹) * x⁻¹) by group]
      exact mul_mem hx.2 (hZ1 hx.1 hy.2)
    | inv x _ hx =>
      refine ⟨inv_mem hx.1, ?_⟩
      rw [show h * x⁻¹ * h⁻¹ * x⁻¹⁻¹ = x⁻¹ * (h * x * h⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ by group]
      exact hZ1 (inv_mem hx.1) (inv_mem hx.2)
  exact (key z (c.centerOf_le_closure_commutator_W hz)).2

private theorem alpha_conj_eq (c : G2qCoordRight L2 S f) {h t h' x : G} (hdec : h = t * h')
    (ht : t ∈ L2) (hh' : h' ∈ trivOTwoQuot L2) (hx : x ∈ L2) (hc : h * x * h⁻¹ ∈ L2) :
    c.α ⟨h * x * h⁻¹, hc⟩ = c.α ⟨t, ht⟩ * c.α ⟨x, hx⟩ * (c.α ⟨t, ht⟩)⁻¹ := by
  have hh'x : h' * x * h'⁻¹ ∈ L2 := conj_mem_of_mem_normalizer (mem_trivOTwoQuot.mp hh').1 hx
  have h1 : c.α ⟨h' * x * h'⁻¹, hh'x⟩ = c.α ⟨x, hx⟩ := by
    refine c.alpha_eq_of_inv_mul_mem hh'x hx ?_
    have := (mem_trivOTwoQuot.mp hh').2 x⁻¹ (inv_mem hx)
    rwa [show (h' * x * h'⁻¹)⁻¹ * x = h' * x⁻¹ * h'⁻¹ * x⁻¹⁻¹ by group]
  have e : (⟨h * x * h⁻¹, hc⟩ : ↥L2) = ⟨t, ht⟩ * ⟨h' * x * h'⁻¹, hh'x⟩ * ⟨t, ht⟩⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hdec]
    group
  rw [e, map_mul, map_mul, map_inv, h1]

private theorem mem_pCoreOf_right_of_conj (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {h t h' : G} (hdec : h = t * h') (ht : t ∈ L2)
    (htB : c.α ⟨t, ht⟩ ∈ borel c.F) (hlam : (c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 ^ 2 ≠ 1)
    (hh' : h' ∈ trivOTwoQuot L2) {x : G} (hx : x ∈ pCoreOf 2 L1)
    (hxh : h * x * h⁻¹ * x⁻¹ ∈ pCoreOf 2 L2) : x ∈ pCoreOf 2 L2 := by
  have hxL2 : x ∈ L2 := le_right_of_g2q hH hD h1 h2 (hH.pCoreOf_le_left hx)
  obtain ⟨r, hr⟩ := mem_utri_iff.mp ((c.memS ⟨x, hxL2⟩).mp (hH.pCoreOf_le_left hx))
  have hhL2 : h ∈ Subgroup.normalizer (L2 : Set G) := by
    rw [hdec]
    exact mul_mem (Subgroup.le_normalizer ht) (mem_trivOTwoQuot.mp hh').1
  have hc : h * x * h⁻¹ ∈ L2 := conj_mem_of_mem_normalizer hhL2 hxL2
  have heq : c.α ⟨h * x * h⁻¹, hc⟩ = c.α ⟨x, hxL2⟩ := by
    refine c.alpha_eq_of_inv_mul_mem hc hxL2 ?_
    have := conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 (inv_mem hxL2)) (inv_mem hxh)
    rwa [show x⁻¹ * (h * x * h⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ = (h * x * h⁻¹)⁻¹ * x by group] at this
  rw [alpha_conj_eq c hdec ht hh' hxL2 hc, hr, conj_utriElt_eq_of_mem_borel htB] at heq
  have hrr := utriElt_injective heq
  have hr0 : r = 0 := by
    have hsub : ((c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 ^ 2 - 1) * r = 0 := by
      rw [sub_mul, one_mul, hrr, sub_self]
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hlam)
  rw [hr0, utriElt_zero] at hr
  exact (c.ker _).mp hr

private theorem natSecVec_conj_commutator_zero (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f)
    {β : ↥(pCoreOf 2 L2) →* Multiplicative (Fin 2 → c.F)}
    (hβker : β.ker = c.W.subgroupOf (pCoreOf 2 L2)) (hβeq : IsEquivSec c.α β) {h t h' : G}
    (hdec : h = t * h') (ht : t ∈ L2) (htB : c.α ⟨t, ht⟩ ∈ borel c.F)
    (hh' : h' ∈ trivOTwoQuot L2) (ht1 : h ∈ trivOTwoQuot L1)
    (hhQ2 : h ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G)) {x a₀ : G} {r : c.F}
    (hx : x ∈ pCoreOf 2 L1) (hxL2 : x ∈ L2) (hxα : c.α ⟨x, hxL2⟩ = utriElt r)
    (ha₀ : a₀ ∈ pCoreOf 2 L2) (hva₀ : natSecVec β a₀ = ![0, 1]) :
    natSecVec β (h * ⁅x, a₀⁆ * h⁻¹) 0 = (c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 ^ 2 * r := by
  have hSL1 := le_left_of_g2q hH hD h1 h2
  have hhL2 : h ∈ Subgroup.normalizer (L2 : Set G) := by
    rw [hdec]
    exact mul_mem (Subgroup.le_normalizer ht) (mem_trivOTwoQuot.mp hh').1
  have hc : h * x * h⁻¹ ∈ L2 := conj_mem_of_mem_normalizer hhL2 hxL2
  have ha' : h * a₀ * h⁻¹ ∈ pCoreOf 2 L2 := conj_mem_of_mem_normalizer hhQ2 ha₀
  have hk1 : h * a₀ * h⁻¹ * a₀⁻¹ ∈ pCoreOf 2 L1 :=
    (mem_trivOTwoQuot.mp ht1).2 a₀ (hSL1 (hH.pCoreOf_le_right ha₀))
  have hk2 : h * a₀ * h⁻¹ * a₀⁻¹ ∈ pCoreOf 2 L2 := mul_mem ha' (inv_mem ha₀)
  have hva' : natSecVec β (h * a₀ * h⁻¹) 1 = 1 := by
    have e := natSecVec_mul β hk2 ha₀
    rw [show h * a₀ * h⁻¹ * a₀⁻¹ * a₀ = h * a₀ * h⁻¹ by group] at e
    rw [e, Pi.add_apply, c.natSecVec_snd_eq_zero_of_mem_inf hH hD h1 h2 hβker hβeq hk1 hk2, hva₀]
    simp
  have hcomm : h * ⁅x, a₀⁆ * h⁻¹ = ⁅((⟨h * x * h⁻¹, hc⟩ : ↥L2) : G), h * a₀ * h⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hcomm, natSecVec_commutator hβeq ⟨h * x * h⁻¹, hc⟩ ha'
    (conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hc) ha'),
    alpha_conj_eq c hdec ht hh' hxL2 hc, hxα, conj_utriElt_eq_of_mem_borel htB, Pi.sub_apply,
    utriElt_mulVec_apply_zero, hva']
  ring

private theorem mem_W_of_conj (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {h t h' : G} (hdec : h = t * h') (ht : t ∈ L2)
    (htB : c.α ⟨t, ht⟩ ∈ borel c.F) (hlam : (c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 ^ 2 ≠ 1)
    (hh' : h' ∈ trivOTwoQuot L2) (ht1 : h ∈ trivOTwoQuot L1)
    (hhQ2 : h ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    (hhW : h ∈ Subgroup.normalizer (c.W : Set G)) {y : G} (hy1 : y ∈ pCoreOf 2 L1)
    (hy2 : y ∈ pCoreOf 2 L2) (hyh : h * y * h⁻¹ * y⁻¹ ∈ c.W) : y ∈ c.W := by
  obtain ⟨β, hβs, hβker, hβeq⟩ := c.natW
  have hy0 := c.natSecVec_snd_eq_zero_of_mem_inf hH hD h1 h2 hβker hβeq hy1 hy2
  obtain ⟨x, hx, hxL2, hxα⟩ := c.exists_pCoreOf_left_alpha_eq hH hD h1 h2 (natSecVec β y 0)
  obtain ⟨a₀, ha₀, hva₀⟩ := exists_natSecVec_eq hβs ![0, 1]
  have hca : x * a₀ * x⁻¹ ∈ pCoreOf 2 L2 :=
    conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hxL2) ha₀
  have hy₀ : ⁅x, a₀⁆ ∈ pCoreOf 2 L2 := mul_mem hca (inv_mem ha₀)
  have hvy₀ : natSecVec β ⁅x, a₀⁆ = natSecVec β y := by
    rw [natSecVec_commutator hβeq ⟨x, hxL2⟩ ha₀ hca, hxα, hva₀]
    ext i
    fin_cases i
    · simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]
    · simp [utriElt_apply_10, utriElt_apply_11, hy0]
  have hw : ⁅x, a₀⁆⁻¹ * y ∈ c.W := (natSecVec_eq_iff hβker hy₀ hy2).mp hvy₀
  have hhw : h * (⁅x, a₀⁆⁻¹ * y) * h⁻¹ ∈ c.W := conj_mem_of_mem_normalizer hhW hw
  have hhy₀ : h * ⁅x, a₀⁆ * h⁻¹ ∈ pCoreOf 2 L2 := conj_mem_of_mem_normalizer hhQ2 hy₀
  have hhy : h * y * h⁻¹ ∈ pCoreOf 2 L2 := conj_mem_of_mem_normalizer hhQ2 hy2
  have e1 : natSecVec β (h * y * h⁻¹) = natSecVec β (h * ⁅x, a₀⁆ * h⁻¹) := by
    rw [show h * y * h⁻¹ = (h * ⁅x, a₀⁆ * h⁻¹) * (h * (⁅x, a₀⁆⁻¹ * y) * h⁻¹) by group,
      natSecVec_mul β hhy₀ (c.le_pCoreOf hhw),
      (natSecVec_eq_zero_iff hβker (c.le_pCoreOf hhw)).mpr hhw, add_zero]
  have e2 : natSecVec β (h * y * h⁻¹) = natSecVec β y := by
    have := (natSecVec_eq_zero_iff hβker (mul_mem hhy (inv_mem hy2))).mpr hyh
    rw [natSecVec_mul β hhy (inv_mem hy2), natSecVec_inv β hy2, ← sub_eq_add_neg,
      sub_eq_zero] at this
    exact this
  have k := congrFun (e2.symm.trans e1) 0
  rw [natSecVec_conj_commutator_zero hH hD h1 h2 c hβker hβeq hdec ht htB hh' ht1 hhQ2 hx hxL2
    hxα ha₀ hva₀] at k
  have hs0 : natSecVec β y 0 = 0 := by
    have hsub : ((c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 ^ 2 - 1) * natSecVec β y 0 = 0 := by
      rw [sub_mul, one_mul, ← k, sub_self]
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hlam)
  have hv : natSecVec β y = 0 := by
    ext i
    fin_cases i
    · simpa using hs0
    · simpa using hy0
  exact (natSecVec_eq_zero_iff hβker hy2).mp hv

private theorem le_normalizer_W_of_torus (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {h t h' : G} {n : ℕ} (hn : Odd n) (hhn : h ^ n = 1)
    (hhB : h ∈ bigB L1 L2 S) (ht1 : h ∈ trivOTwoQuot L1) (hdec : h = t * h') (ht : t ∈ L2)
    (htB : c.α ⟨t, ht⟩ ∈ borel c.F) (hlam : (c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 ^ 2 ≠ 1)
    (hh' : h' ∈ trivOTwoQuot L2) (hcent : ∀ w ∈ c.W, ⁅h, w⁆ ∈ centerOf (pCoreOf 2 L2)) :
    L1 ≤ Subgroup.normalizer (c.W : Set G) := by
  have hSL1 := le_left_of_g2q hH hD h1 h2
  have hNB := hD.bigB_le_normalizer hH h1 h2 hhB
  have hhL1 : h ∈ Subgroup.normalizer (L1 : Set G) := (Subgroup.mem_inf.mp
    (Subgroup.mem_inf.mp hNB).1).1
  have hhL2 : h ∈ Subgroup.normalizer (L2 : Set G) := (Subgroup.mem_inf.mp
    (Subgroup.mem_inf.mp hNB).1).2
  have hhQ1 := normalizer_le_normalizer_pCoreOf 2 L1 hhL1
  have hhQ2 := normalizer_le_normalizer_pCoreOf 2 L2 hhL2
  have hhW := c.normalizer_le_normalizer_W hhL2
  have hWQ1 := c.W_le_pCoreOf_left hH hD h1 h2
  have hWZ1 : ∀ w ∈ c.W, h * w * h⁻¹ * w⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
    intro w hw
    have hy := hcent w hw
    rw [commutatorElement_def] at hy
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_mem_pCoreOf (Subgroup.mem_inf.mp hy).1
    exact mem_of_conj_eq_mul_of_odd (x := w) hn hhn
      (fun k hk => mem_centerOf_conj_of_mem_normalizer hhQ1 hk)
      (fun k hk => mem_centerOf_conj_of_mem_normalizer (le_normalizer_pCoreOf 2 L1
        (hSL1 (hH.pCoreOf_le_right (Subgroup.mem_inf.mp hy).1))) hk)
      hm (conj_mul_inv_mem_centerOf_left hH hD h1 h2 c hhQ2 ht1 hcent hy) (by group)
  have hX : ∀ x ∈ pCoreOf 2 L1, h * x * h⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L1) → x ∈ c.W := by
    intro x hx hxZ
    have hxZ2 : h * x * h⁻¹ * x⁻¹ ∈ c.W :=
      c.center_le (hD.centerOf_pCoreOf_left_le_right hH h1 h2 hxZ)
    exact mem_W_of_conj hH hD h1 h2 c hdec ht htB hlam hh' ht1 hhQ2 hhW hx
      (mem_pCoreOf_right_of_conj hH hD h1 h2 c hdec ht htB hlam hh' hx (c.le_pCoreOf hxZ2)) hxZ2
  refine le_normalizer_of_forall_conj_mem_of_mem fun l hl w hw => ?_
  have hx' : l * w * l⁻¹ ∈ pCoreOf 2 L1 :=
    conj_mem_of_mem_normalizer (le_normalizer_pCoreOf 2 L1 hl) (hWQ1 hw)
  refine hX _ hx' ?_
  obtain ⟨z₁, hz₁, z₂, hz₂, e⟩ := hD.exists_conj_commutator_eq_mul hl ht1 hhQ1 (hWQ1 hw)
  rw [show h * (l * w * l⁻¹) * h⁻¹ * (l * w * l⁻¹)⁻¹ =
    z₁⁻¹ * (l * (h * w * h⁻¹ * w⁻¹) * l⁻¹) * z₂⁻¹ by rw [e]; group]
  exact mul_mem (mul_mem (inv_mem hz₁) (mem_centerOf_conj_of_mem_normalizer
    (le_normalizer_pCoreOf 2 L1 hl) (hWZ1 w hw))) (inv_mem hz₂)

theorem G2qCoordRight.false_of_trivOTwoQuot_centralizes_W (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hcent : ∀ h ∈ H ⊓ trivOTwoQuot L1, ∀ w ∈ c.W, ⁅h, w⁆ ∈ centerOf (pCoreOf 2 L2)) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP c.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c.card])
  obtain ⟨-, hH0card, -, -, -⟩ := hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  obtain ⟨-, -, hsup2, -, -⟩ := hD.torus_right_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨h₀, hh₀, hh₀1⟩ : ∃ h₀ ∈ H ⊓ trivOTwoQuot L1, h₀ ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one (H ⊓ trivOTwoQuot L1) with hbot | hex
    · rw [hbot, Subgroup.card_bot] at hH0card
      omega
    · exact hex
  obtain ⟨hh₀H, ht1⟩ := Subgroup.mem_inf.mp hh₀
  have hnorm : H ⊓ trivOTwoQuot L2 ≤ Subgroup.normalizer ((H ⊓ L2 : Subgroup G) : Set G) :=
    fun x hx => Subgroup.centralizer_le_normalizer ((H ⊓ L2 : Subgroup G) : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        hHcomm y (Subgroup.mem_inf.mp hy).1 x (Subgroup.mem_inf.mp hx).1)
  obtain ⟨t, htT, h', hh'T, hdec⟩ :=
    (mem_sup_iff_exists_mul_of_normalizes hnorm).mp (hsup2.symm ▸ hh₀H)
  obtain ⟨htH, ht⟩ := Subgroup.mem_inf.mp htT
  obtain ⟨hh'H, hh'⟩ := Subgroup.mem_inf.mp hh'T
  have htS : t ∉ S := fun htS => by
    have ht1' : t ∈ S ⊓ H := ⟨htS, htH⟩
    rw [hSinfH, Subgroup.mem_bot] at ht1'
    rw [ht1', one_mul] at hdec
    have hbot := hD.trivOTwoQuot_inf_trivOTwoQuot_eq_bot hH h1 h2 hHB hSinfH hHcard
    have hmem : h₀ ∈ H ⊓ trivOTwoQuot L1 ⊓ trivOTwoQuot L2 := ⟨hh₀, hdec ▸ hh'⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hh₀1 hmem
  have hSL2 := le_right_of_g2q hH hD h1 h2
  have htN : t ∈ Subgroup.normalizer (S : Set G) :=
    (Subgroup.mem_inf.mp (hD.bigB_le_normalizer hH h1 h2 (hHB htH))).2
  have htB : c.α ⟨t, ht⟩ ∈ borel c.F :=
    (mem_borelOf_iff_alpha_mem_borel hSL2 c.α c.surj c.memS ⟨t, ht⟩).mp
      ((borelOf_eq_inf_of_le hSL2).symm ▸ ⟨ht, htN⟩)
  have hlam : (c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 ^ 2 ≠ 1 := by
    intro hsq
    have hlam1 : (c.α ⟨t, ht⟩ : SL(2, c.F)) 0 0 = 1 :=
      CharTwo.sq_injective (hsq.trans (one_pow 2).symm)
    exact htS ((c.memS ⟨t, ht⟩).mpr (mem_utri_entries.mpr ⟨mem_borel_iff.mp htB, hlam1⟩))
  have hf1 : 1 ≤ f := by omega
  have hodd1 : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    ((show Even 2 by norm_num).pow_of_ne_zero (by omega)) odd_one
  have hn : Odd (Nat.card H) := by rw [hHcard]; exact hodd1.mul hodd1
  have hhn : h₀ ^ Nat.card H = 1 := by
    have e := congrArg Subtype.val (pow_card_eq_one' (G := ↥H) (x := ⟨h₀, hh₀H⟩))
    rw [Subgroup.coe_pow, Subgroup.coe_one] at e
    exact e
  exact c.false_of_le_normalizer_W hH (le_normalizer_W_of_torus hH hD h1 h2 c hn hhn (hHB hh₀H)
    ht1 hdec ht htB hlam hh' (hcent h₀ hh₀))

end CFSG.Quasithin.F112R.St84

end
