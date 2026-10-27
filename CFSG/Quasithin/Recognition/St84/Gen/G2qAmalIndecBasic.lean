module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSec

import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem le_left_of_g2q (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L1 :=
  (hD.borelOf_inf_borelOf hH h1 h2).symm.le.trans (inf_le_left.trans (borelOf_le L1 S))

private theorem le_right_of_g2q (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L2 :=
  (hD.borelOf_inf_borelOf hH h1 h2).symm.le.trans (inf_le_right.trans (borelOf_le L2 S))

theorem G2qCoord.one_le_f {L : Subgroup G} (c : G2qCoord L S f) : 1 ≤ f := by
  letI := c.field
  letI := c.fintype
  have htwo : 1 < Nat.card c.F := Finite.one_lt_card
  rw [c.card] at htwo
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at htwo
  exact lt_irrefl 1 htwo

private theorem comm_of_mem_centerOf_left (hD : G2qLocalData L1 L2 S f) {z y : G}
    (hz : z ∈ centerOf (pCoreOf 2 L1)) (hy : y ∈ L1) : y * z = z * y := by
  rw [hD.center_left] at hz
  exact mul_comm_of_mem_centerOf hz hy

private theorem card_centerOf_right (c : G2qCoordRight L2 S f) :
    Nat.card (centerOf (pCoreOf 2 L2)) = 2 ^ (2 * f) := by
  letI := c.field
  letI := c.fintype
  obtain ⟨β, hβs, hβker, -⟩ := c.nat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hβinj, hβs⟩)]
  change Nat.card (Fin 2 → c.F) = 2 ^ (2 * f)
  rw [Nat.card_fun, c.card, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  ring

theorem G2qLocalData.commutator_mem_centerOf_left (hD : G2qLocalData L1 L2 S f) {x y : G}
    (hx : x ∈ pCoreOf 2 L1) (hy : y ∈ pCoreOf 2 L1) : ⁅x, y⁆ ∈ centerOf (pCoreOf 2 L1) := by
  rcases hD.special_left.1.2 with ⟨hcomm, -⟩ | ⟨hcomm, -, -⟩
  · have h : x * y = y * x :=
      congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : ↥(pCoreOf 2 L1)) ⟨y, hy⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h]
    exact one_mem _
  · let a : ↥(pCoreOf 2 L1) := ⟨x, hx⟩
    let b : ↥(pCoreOf 2 L1) := ⟨y, hy⟩
    have hmem : ⁅a, b⁆ ∈ Subgroup.center ↥(pCoreOf 2 L1) := by
      rw [← hcomm, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    refine mem_centerOf_of_forall_comm (⁅a, b⁆).2 fun z hz => ?_
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hmem (⟨z, hz⟩ : ↥(pCoreOf 2 L1)))

theorem G2qLocalData.pCoreOf_left_sup_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    pCoreOf 2 L1 ⊔ pCoreOf 2 L2 = S := by
  have hnorm : pCoreOf 2 L1 ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    (hH.pCoreOf_le_left.trans (le_right_of_g2q hH hD h1 h2)).trans (le_normalizer_pCoreOf 2 L2)
  have hcard := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hD.card_inf, hD.card_left, hD.card_right] at hcard
  have hcard' : Nat.card ↥(pCoreOf 2 L1 ⊔ pCoreOf 2 L2) = Nat.card S := by
    rw [hD.card_S]
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ (4 * f) by positivity)
    rw [hcard, ← pow_add, ← pow_add]
    ring_nf
  exact Subgroup.eq_of_le_of_card_ge (sup_le hH.pCoreOf_le_left hH.pCoreOf_le_right) hcard'.ge

theorem G2qCoordRight.mem_W_iff (c : G2qCoordRight L2 S f) {x : G} :
    x ∈ c.W ↔ x ∈ pCoreOf 2 L2 ∧ ∀ l ∈ L2, ⁅l, x⁆ ∈ centerOf (pCoreOf 2 L2) := by
  constructor
  · intro hx
    refine ⟨c.le_pCoreOf hx, fun l hl => c.commutator_le ?_⟩
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl hx
  · rintro ⟨hxQ, hcomm⟩
    letI := c.field
    obtain ⟨β, -, hβker, hβeq⟩ := c.natW
    have hfix : ∀ g : SL(2, c.F),
        (g : Matrix (Fin 2) (Fin 2) c.F) *ᵥ natSecVec β x = natSecVec β x := by
      intro g
      obtain ⟨l, rfl⟩ := c.surj g
      have h0 : natSecVec β ⁅(l : G), x⁆ = 0 :=
        (natSecVec_eq_zero_iff hβker (commutator_mem_pCoreOf_of_mem l.2 hxQ)).mpr
          (c.center_le (hcomm l l.2))
      rw [natSecVec_commutator hβeq l hxQ (conj_mem_pCoreOf_of_mem l.2 hxQ)] at h0
      exact sub_eq_zero.mp h0
    exact (natSecVec_eq_zero_iff hβker hxQ).mp (eq_zero_of_forall_sl2_mulVec_eq hfix)

private theorem conj_mem_W_of_mem_normalizer (c : G2qCoordRight L2 S f) {g x : G}
    (hg : g ∈ Subgroup.normalizer (L2 : Set G)) (hx : x ∈ c.W) : g * x * g⁻¹ ∈ c.W := by
  rw [c.mem_W_iff] at hx ⊢
  have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L2 hg
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgQ x).mp hx.1, fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ L2 := (Subgroup.mem_normalizer_iff''.mp hg l).mp hl
  have e : ⁅l, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * l * g, x⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mem_centerOf_conj_of_mem_normalizer hgQ (hx.2 _ hl')

theorem G2qCoordRight.normalizer_le_normalizer_W (c : G2qCoordRight L2 S f) :
    Subgroup.normalizer (L2 : Set G) ≤ Subgroup.normalizer (c.W : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_W_of_mem_normalizer c hg, fun hx => ?_⟩
  have := conj_mem_W_of_mem_normalizer c (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem G2qCoordRight.bigB_le_normalizer_W (hH : Hyp111 L1 L2 S) (c : G2qCoordRight L2 S f) :
    bigB L1 L2 S ≤ Subgroup.normalizer (c.W : Set G) :=
  (sup_le (sup_le hH.h2.borel_le ((borelOf_le L2 S).trans Subgroup.le_normalizer))
    hH.h2.normalizes).trans c.normalizer_le_normalizer_W

private theorem exists_mem_W_inv_mul_mem (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {w₀ : G} (hw₀ : w₀ ∈ c.W) (hw₀Q : w₀ ∉ pCoreOf 2 L1) {s : G}
    (hs : s ∈ S) : ∃ w ∈ c.W, w⁻¹ * s ∈ pCoreOf 2 L1 := by
  classical
  obtain ⟨c1⟩ := hD.exists_coordLeft hH h1
  letI := c1.field
  letI := c1.fintype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP c1.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c1.card])
  have hSL1 : S ≤ L1 := le_left_of_g2q hH hD h1 h2
  have hw₀S : w₀ ∈ S := hH.pCoreOf_le_right (c.le_pCoreOf hw₀)
  obtain ⟨r₀, hα₀⟩ := mem_utri_iff.mp ((c1.memS ⟨w₀, hSL1 hw₀S⟩).mp hw₀S)
  have hr₀ : r₀ ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hα₀
    exact hw₀Q ((c1.ker _).mp hα₀)
  obtain ⟨t, hαs⟩ := mem_utri_iff.mp ((c1.memS ⟨s, hSL1 hs⟩).mp hs)
  by_cases ht : t = 0
  · refine ⟨1, c.W.one_mem, ?_⟩
    rw [ht, utriElt_zero] at hαs
    rw [inv_one, one_mul]
    exact (c1.ker _).mp hαs
  obtain ⟨a, ha⟩ := exists_torusElt_conj_utriElt hr₀ ht
  obtain ⟨b, hb⟩ := c1.surj (torusElt a)
  have hbB : (b : G) ∈ borelOf L1 S :=
    (mem_borelOf_iff_alpha_mem_borel hSL1 c1.α c1.surj c1.memS b).mpr
      (by rw [hb]; exact torusElt_mem_borel a)
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hbW : (b : G) ∈ Subgroup.normalizer (c.W : Set G) := c.bigB_le_normalizer_W hH (hB1B hbB)
  refine ⟨(b : G) * w₀ * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hbW w₀).mp hw₀, ?_⟩
  have hmem : ((b : G) * w₀ * (b : G)⁻¹)⁻¹ * s ∈ L1 :=
    mul_mem (inv_mem (mul_mem (mul_mem b.2 (hSL1 hw₀S)) (inv_mem b.2))) (hSL1 hs)
  have e : (⟨((b : G) * w₀ * (b : G)⁻¹)⁻¹ * s, hmem⟩ : ↥L1) =
      (b * ⟨w₀, hSL1 hw₀S⟩ * b⁻¹)⁻¹ * ⟨s, hSL1 hs⟩ := rfl
  refine (c1.ker ⟨_, hmem⟩).mp ?_
  rw [e]
  simp only [map_mul, map_inv]
  rw [hb, hα₀, ha, hαs, inv_mul_cancel]

theorem G2qCoordRight.W_le_pCoreOf_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) : c.W ≤ pCoreOf 2 L1 := by
  by_contra hle
  obtain ⟨w₀, hw₀, hw₀Q⟩ := SetLike.not_le_iff_exists.mp hle
  have hSL2 : S ≤ L2 := le_right_of_g2q hH hD h1 h2
  have hcomm : ∀ y ∈ pCoreOf 2 L1, ∀ a ∈ pCoreOf 2 L2, ⁅y, a⁆ ∈ centerOf (pCoreOf 2 L2) := by
    intro y hy a ha
    obtain ⟨w, hw, hk⟩ :=
      exists_mem_W_inv_mul_mem hH hD h1 h2 c hw₀ hw₀Q (hH.pCoreOf_le_right ha)
    have hwQ : w ∈ pCoreOf 2 L2 := c.le_pCoreOf hw
    have hyL2 : y ∈ L2 := hSL2 (hH.pCoreOf_le_left hy)
    have h1' : ⁅y, w⁆ ∈ centerOf (pCoreOf 2 L2) := c.commutator_le (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hyL2 hw)
    have h2' : ⁅y, w⁻¹ * a⁆ ∈ centerOf (pCoreOf 2 L2) :=
      hD.centerOf_pCoreOf_left_le_right hH h1 h2 (hD.commutator_mem_centerOf_left hy hk)
    have e : ⁅y, a⁆ = ⁅y, w⁆ * (w * ⁅y, w⁻¹ * a⁆ * w⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem h1' (mem_centerOf_conj_of_mem_normalizer (Subgroup.le_normalizer hwQ) h2')
  letI := c.field
  obtain ⟨β, hβs, hβker, hβeq⟩ := c.natW
  have hf := c.one_le_f
  obtain ⟨x, hxQ1, hxQ2⟩ : ∃ x ∈ pCoreOf 2 L1, x ∉ pCoreOf 2 L2 := by
    refine SetLike.not_le_iff_exists.mp fun hle' => ?_
    have hcard := hD.card_inf
    rw [inf_eq_left.mpr hle', hD.card_left] at hcard
    have := Nat.pow_right_injective (le_refl 2) hcard
    omega
  have hxL2 : x ∈ L2 := hSL2 (hH.pCoreOf_le_left hxQ1)
  obtain ⟨r, hr⟩ := mem_utri_iff.mp ((c.memS ⟨x, hxL2⟩).mp (hH.pCoreOf_le_left hxQ1))
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hr
    exact hxQ2 ((c.ker _).mp hr)
  obtain ⟨a, haQ, ha⟩ := exists_natSecVec_eq hβs ![0, 1]
  have hz := hcomm x hxQ1 a haQ
  have h0 : natSecVec β ⁅x, a⁆ = 0 :=
    (natSecVec_eq_zero_iff hβker (c.le_pCoreOf (c.center_le hz))).mpr (c.center_le hz)
  rw [natSecVec_commutator hβeq ⟨x, hxL2⟩ haQ (conj_mem_pCoreOf_of_mem hxL2 haQ), hr, ha] at h0
  have k := congrFun h0 0
  rw [Pi.sub_apply, utriElt_mulVec_apply_zero] at k
  simp at k
  exact hr0 k

theorem G2qLocalData.centerOf_pCoreOf_right_le_left (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) : centerOf (pCoreOf 2 L2) ≤ pCoreOf 2 L1 := by
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  exact c.center_le.trans (c.W_le_pCoreOf_left hH hD h1 h2)

theorem G2qCoordRight.false_of_le_normalizer_W (hH : Hyp111 L1 L2 S) (c : G2qCoordRight L2 S f)
    (hW : L1 ≤ Subgroup.normalizer (c.W : Set G)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : L2 ≤ Subgroup.normalizer (c.W : Set G) :=
    Subgroup.le_normalizer.trans c.normalizer_le_normalizer_W
  have hS : S ≤ Subgroup.normalizer (c.W : Set G) :=
    hH.h2.normalizes.trans c.normalizer_le_normalizer_W
  have hle : c.W ≤ L1 ⊔ L2 ⊔ S :=
    (c.le_pCoreOf.trans (pCoreOf_le 2 L2)).trans (le_sup_right.trans le_sup_left)
  have hcore := le_pCoreOf_of_le_normalizer 2 hle (sup_le (sup_le hW hL2) hS)
    ((pCoreOf_isPGroup 2 L2).to_le c.le_pCoreOf)
  rw [hH.o2, le_bot_iff] at hcore
  have hcard := c.card_W
  rw [hcore, Subgroup.card_bot] at hcard
  have hf := c.one_le_f
  have hlt : 1 < 2 ^ (3 * f) := Nat.one_lt_two_pow (by omega)
  omega

theorem G2qCoordRight.commutator_sup_W (c : G2qCoordRight L2 S f) :
    ⁅pCoreOf 2 L2, L2⁆ ⊔ c.W = pCoreOf 2 L2 := by
  letI := c.field
  obtain ⟨β, hβs, hβker, hβeq⟩ := c.natW
  refine le_antisymm (sup_le (commutator_pCoreOf_le_pCoreOf L2) c.le_pCoreOf) fun x hx => ?_
  obtain ⟨y, hyc, hyQ, hy⟩ :=
    exists_commutator_natSecVec_eq c.surj hβs hβeq (le_normalizer_pCoreOf 2 L2) x
  have hyx : y⁻¹ * x ∈ c.W := (natSecVec_eq_iff hβker hyQ hx).mp hy
  rw [show x = y * (y⁻¹ * x) by group]
  exact Subgroup.mul_mem_sup (by rwa [Subgroup.commutator_comm]) hyx

theorem G2qCoordRight.commutator_eq_of_W_le (c : G2qCoordRight L2 S f)
    (hW : c.W ≤ ⁅pCoreOf 2 L2, L2⁆) : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2 := by
  have h := c.commutator_sup_W
  rwa [sup_eq_left.mpr hW] at h

theorem G2qCoordRight.conj_commutator_W (c : G2qCoordRight L2 S f) {l w a : G} (hl : l ∈ L2)
    (hw : w ∈ c.W) (ha : a ∈ pCoreOf 2 L2) : l * ⁅w, a⁆ * l⁻¹ = ⁅w, l * a * l⁻¹⁆ := by
  have hz : ⁅l, w⁆ ∈ centerOf (pCoreOf 2 L2) := c.commutator_le (by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl hw)
  calc l * ⁅w, a⁆ * l⁻¹ = ⁅⁅l, w⁆ * w, l * a * l⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅w, l * a * l⁻¹⁆ := commutator_mul_left_eq_of_mem_centerOf hz (c.le_pCoreOf hw)
        (conj_mem_pCoreOf_of_mem hl ha)

theorem G2qCoordRight.commute_of_mem_W (c : G2qCoordRight L2 S f) {w w' : G} (hw : w ∈ c.W)
    (hw' : w' ∈ c.W) : w * w' = w' * w := by
  letI := c.field
  obtain ⟨β, -, hβker, hβeq⟩ := c.nat
  have hwQ := c.le_pCoreOf hw
  have hw'Q := c.le_pCoreOf hw'
  have hZ : ⁅w, w'⁆ ∈ centerOf (pCoreOf 2 L2) :=
    c.commutator_le (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 hw'Q))
  have hfix : ∀ g : SL(2, c.F),
      (g : Matrix (Fin 2) (Fin 2) c.F) *ᵥ natSecVec β ⁅w, w'⁆ = natSecVec β ⁅w, w'⁆ := by
    intro g
    obtain ⟨l, rfl⟩ := c.surj g
    have hz' : ⁅(l : G), w'⁆ ∈ centerOf (pCoreOf 2 L2) := c.commutator_le (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator l.2 hw')
    have e : (l : G) * ⁅w, w'⁆ * (l : G)⁻¹ = ⁅w, w'⁆ := by
      rw [c.conj_commutator_W l.2 hw hw'Q,
        show (l : G) * w' * (l : G)⁻¹ = ⁅(l : G), w'⁆ * w' by rw [commutatorElement_def]; group]
      exact commutator_mul_right_eq_of_mem_centerOf hz' hwQ hw'Q
    have key := natSecVec_conj hβeq l hZ (by rw [e]; exact hZ)
    rw [e] at key
    exact key.symm
  have h0 := eq_zero_of_forall_sl2_mulVec_eq hfix
  have h1 : ⁅w, w'⁆ ∈ (⊥ : Subgroup G) := (natSecVec_eq_zero_iff hβker hZ).mp h0
  rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1

private theorem conj_mem_closure_commutator_W (c : G2qCoordRight L2 S f) {l : G} (hl : l ∈ L2)
    {y : G} (hy : y ∈ Subgroup.closure {x | ∃ w ∈ c.W, ∃ a ∈ pCoreOf 2 L2, x = ⁅w, a⁆}) :
    l * y * l⁻¹ ∈ Subgroup.closure {x | ∃ w ∈ c.W, ∃ a ∈ pCoreOf 2 L2, x = ⁅w, a⁆} := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, a, ha, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨w, hw, l * a * l⁻¹, conj_mem_pCoreOf_of_mem hl ha,
      c.conj_commutator_W hl hw ha⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem G2qCoordRight.centerOf_le_closure_commutator_W (c : G2qCoordRight L2 S f) :
    centerOf (pCoreOf 2 L2) ≤
      Subgroup.closure {x | ∃ w ∈ c.W, ∃ a ∈ pCoreOf 2 L2, x = ⁅w, a⁆} := by
  letI := c.field
  obtain ⟨β, -, hβker, hβeq⟩ := c.nat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ c.W, w ∉ centerOf (pCoreOf 2 L2) := by
    refine SetLike.not_le_iff_exists.mp fun hle => ?_
    have hle' := Subgroup.card_le_of_le hle
    rw [c.card_W, card_centerOf_right c] at hle'
    have hf := c.one_le_f
    exact absurd hle' (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  obtain ⟨a, ha, hwa⟩ : ∃ a ∈ pCoreOf 2 L2, ⁅w, a⁆ ≠ 1 := by
    by_contra hcon
    refine hwZ (mem_centerOf_of_forall_comm (c.le_pCoreOf hw) fun a ha => ?_)
    have h1 : ⁅w, a⁆ = 1 := by
      by_contra h1
      exact hcon ⟨a, ha, h1⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hgenZ : ⁅w, a⁆ ∈ centerOf (pCoreOf 2 L2) :=
    c.commutator_le (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 ha))
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  exact natSec_mem_of_conj_mem c.surj hβinj hβeq
    (le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L2))
    (fun l hl y hy => conj_mem_closure_commutator_W c hl hy) hgenZ
    (Subgroup.subset_closure ⟨w, hw, a, ha, rfl⟩) hwa hz hz1

theorem G2qCoordRight.mem_centerOf_of_commutator_mem (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) {w : G} (hw : w ∈ c.W)
    (hc : ∀ a ∈ pCoreOf 2 L2, ⁅w, a⁆ ∈ centerOf (pCoreOf 2 L1)) :
    w ∈ centerOf (pCoreOf 2 L2) := by
  letI := c.field
  obtain ⟨β, -, hβker, hβeq⟩ := c.nat
  have hSL1 := le_left_of_g2q hH hD h1 h2
  have hwQ : w ∈ pCoreOf 2 L2 := c.le_pCoreOf hw
  have hZ : ∀ a ∈ pCoreOf 2 L2, ⁅w, a⁆ ∈ centerOf (pCoreOf 2 L2) := fun a ha =>
    c.commutator_le (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 ha))
  obtain ⟨s, hs⟩ := c.surj (utriElt 1)
  have hsS : (s : G) ∈ S := (c.memS s).mpr (by rw [hs]; exact utriElt_mem_utri 1)
  have hsnd : ∀ a ∈ pCoreOf 2 L2, natSecVec β ⁅w, a⁆ 1 = 0 := by
    intro a ha
    have hcomm : (s : G) * ⁅w, a⁆ * (s : G)⁻¹ = ⁅w, a⁆ := by
      rw [comm_of_mem_centerOf_left hD (hc a ha) (hSL1 hsS), mul_inv_cancel_right]
    have key := natSecVec_conj hβeq s (hZ a ha) (by rw [hcomm]; exact hZ a ha)
    rw [hcomm, hs] at key
    have k := congrFun key 0
    rw [utriElt_mulVec_apply_zero, one_mul] at k
    linear_combination -k
  obtain ⟨l, hl⟩ := c.surj (ltriElt 1)
  have hzero : ∀ a ∈ pCoreOf 2 L2, natSecVec β ⁅w, a⁆ = 0 := by
    intro a ha
    have hla : (l : G) * a * (l : G)⁻¹ ∈ pCoreOf 2 L2 := conj_mem_pCoreOf_of_mem l.2 ha
    have e := c.conj_commutator_W l.2 hw ha
    have key := natSecVec_conj hβeq l (hZ a ha) (by rw [e]; exact hZ _ hla)
    rw [e, hl] at key
    have k := congrFun key 1
    rw [ltriElt_mulVec_apply_one, one_mul, hsnd _ hla, hsnd a ha, add_zero] at k
    ext i
    fin_cases i
    · simpa using k.symm
    · simpa using hsnd a ha
  refine mem_centerOf_of_forall_comm hwQ fun a ha => ?_
  have h1' : ⁅w, a⁆ ∈ (⊥ : Subgroup G) := (natSecVec_eq_zero_iff hβker (hZ a ha)).mp (hzero a ha)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1'
  exact h1'.symm

end CFSG.Quasithin.F112R.St84

end
