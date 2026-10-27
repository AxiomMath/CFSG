module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofSeven
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item434Kit Subgroup

namespace Res423Three

section Wreath

variable {H : Type*} [Group H] {z : Fin 3 → H} {t : H}

theorem vecElt_neg (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) :
    vecElt z (-v) = (vecElt z v)⁻¹ :=
  map_inv (vecHom hf) (Multiplicative.ofAdd v)

theorem t_mul_vecElt (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) :
    t * vecElt z v = vecElt z ![v 2, v 0, v 1] * t := by
  rw [← conj_vecElt hf v, inv_mul_cancel_right]

theorem vecElt_mul_t_pow_three (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) :
    (vecElt z v * t) ^ 3 = vecElt z (fun _ => v 0 + v 1 + v 2) := by
  have h1 := t_mul_vecElt hf v
  have h2 : t * vecElt z ![v 2, v 0, v 1] = vecElt z ![v 1, v 2, v 0] * t := by
    rw [t_mul_vecElt hf]
    rfl
  have ht3 : t ^ 3 = 1 := hf.pow_t
  calc (vecElt z v * t) ^ 3
      = vecElt z v * (t * vecElt z v) * (t * vecElt z v) * t := by
        rw [pow_three]
        simp only [mul_assoc]
    _ = vecElt z v * (vecElt z ![v 2, v 0, v 1] * t) * (vecElt z ![v 2, v 0, v 1] * t) * t := by
        rw [h1]
    _ = vecElt z v * vecElt z ![v 2, v 0, v 1] * (t * vecElt z ![v 2, v 0, v 1]) * t * t := by
        group
    _ = vecElt z v * vecElt z ![v 2, v 0, v 1] * (vecElt z ![v 1, v 2, v 0] * t) * t * t := by
        rw [h2]
    _ = vecElt z v * vecElt z ![v 2, v 0, v 1] * vecElt z ![v 1, v 2, v 0] * t ^ 3 := by
        rw [pow_three]
        simp only [mul_assoc]
    _ = vecElt z (fun _ => v 0 + v 1 + v 2) := by
        rw [ht3, mul_one, ← vecElt_add hf, ← vecElt_add hf]
        congr 1
        funext i
        fin_cases i
        · show v 0 + v 2 + v 1 = v 0 + v 1 + v 2
          exact (by decide : ∀ a b c : ZMod 3, a + c + b = a + b + c) _ _ _
        · show v 1 + v 0 + v 2 = v 0 + v 1 + v 2
          exact (by decide : ∀ a b c : ZMod 3, b + a + c = a + b + c) _ _ _
        · show v 2 + v 1 + v 0 = v 0 + v 1 + v 2
          exact (by decide : ∀ a b c : ZMod 3, c + b + a = a + b + c) _ _ _

theorem conj_eq_vecElt_mul_t (hf : WreathFacts z t) {v : Fin 3 → ZMod 3}
    (hs : v 0 + v 1 + v 2 = 0) :
    vecElt z ![0, v 1, -v 0] * t * (vecElt z ![0, v 1, -v 0])⁻¹ = vecElt z v * t := by
  rw [← vecElt_neg hf, mul_assoc, t_mul_vecElt hf, ← mul_assoc, ← vecElt_add hf]
  congr 2
  funext i
  fin_cases i
  · show 0 + - -v 0 = v 0
    exact (by decide : ∀ a : ZMod 3, 0 + - -a = a) _
  · show v 1 + -0 = v 1
    exact (by decide : ∀ a : ZMod 3, a + -0 = a) _
  · show -v 0 + -v 1 = v 2
    exact (by decide : ∀ a b c : ZMod 3, a + b + c = 0 → -a + -b = c) _ _ _ hs

theorem vecElt_comm_t_of_comm {w : Fin 3 → ZMod 3} {k : ℕ}
    (h : vecElt z w * t ^ k * t = t * (vecElt z w * t ^ k)) :
    vecElt z w * t = t * vecElt z w := by
  have h1 : vecElt z w * t * t ^ k = t * vecElt z w * t ^ k := by
    calc vecElt z w * t * t ^ k = vecElt z w * (t * t ^ k) := by rw [mul_assoc]
      _ = vecElt z w * (t ^ k * t) := by rw [(Commute.self_pow t k).eq]
      _ = vecElt z w * t ^ k * t := by rw [mul_assoc]
      _ = t * (vecElt z w * t ^ k) := h
      _ = t * vecElt z w * t ^ k := by rw [mul_assoc]
  exact mul_right_cancel h1

theorem mem_sup_of_comm_t (hf : WreathFacts z t) {y : H} (hyW : y ∈ wreathW z t)
    (hyt : y * t = t * y) :
    y ∈ zpowers (vecElt z ![1, 1, 1]) ⊔ zpowers t := by
  obtain ⟨w, k, rfl⟩ := mem_wreathW hf hyW
  have hwt := vecElt_comm_t_of_comm hyt
  obtain ⟨h01, h12⟩ := eq_of_commute hf (j := 1) (by decide)
    (by simpa only [Fin.val_one, pow_one] using hwt)
  exact mul_mem (mem_sup_left (vecElt_mem_zpowers_of_const hf h01 h12))
    (mem_sup_right (pow_mem (mem_zpowers t) _))

theorem c_mul_t (hf : WreathFacts z t) :
    vecElt z ![1, 1, 1] * t = t * vecElt z ![1, 1, 1] := by
  rw [t_mul_vecElt hf]
  rfl

theorem c_ne_one (hf : WreathFacts z t) : vecElt z ![1, 1, 1] ≠ 1 := by
  intro h
  have h0 := congrFun (hf.inj _ h) 0
  exact absurd h0 (by decide)

theorem isElemAbelian_cte [Finite H] (hf : WreathFacts z t) {e : H} (he3 : e ^ 3 = 1)
    (hec : e * vecElt z ![1, 1, 1] = vecElt z ![1, 1, 1] * e) (het : e * t = t * e)
    (heW : e ∉ wreathW z t) :
    CFSG.Assembly.IsElemAbelian 3 (zpowers (vecElt z ![1, 1, 1]) ⊔ zpowers t ⊔ zpowers e) ∧
      Nat.card (zpowers (vecElt z ![1, 1, 1]) ⊔ zpowers t ⊔ zpowers e : Subgroup H) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set c := vecElt z ![1, 1, 1] with hcdef
  have hcA : c ∈ baseA z := vecElt_mem_baseA hf _
  have hc3 : c ^ 3 = 1 := (isElemAbelian_baseA hf).2 _ hcA
  have hZc : CFSG.Assembly.IsElemAbelian 3 (zpowers c) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hcard : Nat.card (zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hc3 (c_ne_one hf)
  have htc : t ∉ zpowers c := fun h => t_notMem_baseA hf (zpowers_le.mpr hcA h)
  obtain ⟨hA1, hA1card⟩ := Sec5.isElemAbelian_sup_zpowers hZc htc hf.pow_t fun a ha => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (c_mul_t hf) k).eq
  have hA1W : zpowers c ⊔ zpowers t ≤ wreathW z t :=
    sup_le (zpowers_le.mpr (mem_sup_left hcA)) (zpowers_le.mpr t_mem_wreathW)
  have hle : zpowers c ⊔ zpowers t ≤ centralizer {e} :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hec.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr het.symm))
  obtain ⟨hE, hEcard⟩ := Sec5.isElemAbelian_sup_zpowers hA1 (fun h => heW (hA1W h)) he3
    fun a ha => mem_centralizer_singleton_iff.mp (hle ha)
  refine ⟨hE, ?_⟩
  rw [hEcard, hA1card, hcard]

theorem exists_E27_of_le [Finite H] (hf : WreathFacts z t) {e : H} (he3 : e ^ 3 = 1)
    (hec : e * vecElt z ![1, 1, 1] = vecElt z ![1, 1, 1] * e) (het : e * t = t * e)
    (heW : e ∉ wreathW z t) {D : Subgroup H} (hDW : D ≤ wreathW z t)
    (hD : CFSG.Assembly.IsElemAbelian 3 D) :
    ∃ E : Subgroup H, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ Nat.card E = 27 := by
  by_cases hA : D ≤ baseA z
  · exact ⟨baseA z, isElemAbelian_baseA hf, hA, card_baseA hf⟩
  obtain ⟨x, hxD, hxA⟩ : ∃ x ∈ D, x ∉ baseA z := by
    by_contra hc
    push Not at hc
    exact hA hc
  obtain ⟨v, j, rfl⟩ := mem_wreathW hf (hDW hxD)
  obtain ⟨v', hv'D⟩ : ∃ v' : Fin 3 → ZMod 3, vecElt z v' * t ∈ D := by
    fin_cases j
    · exact absurd (by simpa using vecElt_mem_baseA hf v) hxA
    · exact ⟨v, by simpa using hxD⟩
    · refine ⟨![-v 2, -v 0, -v 1], ?_⟩
      have hinv := inv_mem hxD
      have ht2 : (t ^ 2)⁻¹ = t := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ']
        exact hf.pow_t
      have hx : (vecElt z v * t ^ (2 : ℕ))⁻¹ = vecElt z ![-v 2, -v 0, -v 1] * t := by
        rw [mul_inv_rev, ht2, ← vecElt_neg hf, t_mul_vecElt hf]
        rfl
      simp only at hinv
      rw [hx] at hinv
      exact hinv
  have hx3 : (vecElt z v' * t) ^ 3 = 1 := hD.2 _ hv'D
  rw [vecElt_mul_t_pow_three hf] at hx3
  have hs : v' 0 + v' 1 + v' 2 = 0 := congrFun (hf.inj _ hx3) 0
  set b := vecElt z ![0, v' 1, -v' 0] with hbdef
  have hb := conj_eq_vecElt_mul_t hf hs
  rw [← hbdef] at hb
  obtain ⟨hE0, hE0card⟩ := isElemAbelian_cte hf he3 hec het heW
  refine ⟨(zpowers (vecElt z ![1, 1, 1]) ⊔ zpowers t ⊔ zpowers e).map (MulAut.conj b).toMonoidHom,
    Res423Two.isElemAbelian_map' _ hE0, fun y hy => ?_, ?_⟩
  · have hbW : b ∈ wreathW z t := mem_sup_left (vecElt_mem_baseA hf _)
    have hy'W : b⁻¹ * y * b ∈ wreathW z t := mul_mem (mul_mem (inv_mem hbW) (hDW hy)) hbW
    have hyx : y * (b * t * b⁻¹) = b * t * b⁻¹ * y := by
      rw [hb]
      exact Res423Two.comm_of_isElemAbelian hD _ hy _ hv'D
    have hy't : b⁻¹ * y * b * t = t * (b⁻¹ * y * b) := by
      calc b⁻¹ * y * b * t = b⁻¹ * (y * (b * t * b⁻¹)) * b := by group
        _ = b⁻¹ * (b * t * b⁻¹ * y) * b := by rw [hyx]
        _ = t * (b⁻¹ * y * b) := by group
    refine ⟨b⁻¹ * y * b, mem_sup_left (mem_sup_of_comm_t hf hy'W hy't), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj b).injective, hE0card]

theorem exists_E27 [Finite H] (hf : WreathFacts z t) {e : H} (he3 : e ^ 3 = 1)
    (hec : e * vecElt z ![1, 1, 1] = vecElt z ![1, 1, 1] * e) (het : e * t = t * e)
    (heW : e ∉ wreathW z t) (hW : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3)
    {D : Subgroup H} (hD : CFSG.Assembly.IsElemAbelian 3 D) :
    ∃ E : Subgroup H, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hW
    (Sec5.isPGroup_of_isElemAbelian hD)
  obtain ⟨E, hE, hDE, hE27⟩ := exists_E27_of_le hf he3 hec het heW
    (Item434AltPerm.map_conj_inv_le hg) (Res423Two.isElemAbelian_map' _ hD)
  refine ⟨E.map (MulAut.conj g).toMonoidHom, Res423Two.isElemAbelian_map' _ hE, ?_, ?_⟩
  · rw [← Item434AltPerm.map_conj_map_conj_inv D g]
    exact Subgroup.map_mono hDE
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE27]

end Wreath

section Sp62

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

@[expose] def eCode : List ℕ :=
  [0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1,
    1, 0, 0, 1]

@[expose] def eCodeInv : List ℕ :=
  [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0]

set_option maxRecDepth 100000 in
theorem zPair_check : ∀ i : Fin 3, pairCheck (Item434SmallTwoIII.zPair i) = true := by
  decide

set_option maxRecDepth 100000 in
theorem tPair_check : pairCheck Item434SmallTwoIII.tPair = true := by
  decide

set_option maxRecDepth 100000 in
theorem ePair_check : pairCheck (eCode, eCodeInv) = true := by
  decide

noncomputable def zS (i : Fin 3) : H6 :=
  ofCode (Item434SmallTwoIII.zPair i) (zPair_check i)

noncomputable def tS : H6 :=
  ofCode Item434SmallTwoIII.tPair tPair_check

noncomputable def eS : H6 :=
  ofCode (eCode, eCodeInv) ePair_check

theorem mat6_zS (i : Fin 3) : mat6 (zS i) = dec6 (Item434SmallTwoIII.zCode i) :=
  mat6_ofCode _ _

theorem mat6_tS : mat6 tS = dec6 Item434SmallTwoIII.tCode :=
  mat6_ofCode _ _

theorem mat6_tS_inv : mat6 tS⁻¹ = dec6 Item434SmallTwoIII.tCodeInv :=
  mat6_ofCode_inv _ _

theorem mat6_eS : mat6 eS = dec6 eCode :=
  mat6_ofCode _ _

theorem mat6_vecElt_zS (v : Fin 3 → ZMod 3) :
    mat6 (vecElt zS v) = dec6 (Item434SmallTwoIII.vecCodeZ v) := by
  rw [Item434SmallTwoIII.vecCodeZ, Item434SmallTwoIII.vecCode, dec6_mul6, dec6_mul6,
    Item434SmallTwoIII.dec6_powCode, Item434SmallTwoIII.dec6_powCode,
    Item434SmallTwoIII.dec6_powCode, vecElt, map_mul, map_mul, map_pow, map_pow, map_pow,
    mat6_zS, mat6_zS, mat6_zS]

set_option maxRecDepth 100000 in
theorem wreath_check :
    (∀ i : Fin 3, mul6 (mul6 (Item434SmallTwoIII.zCode i) (Item434SmallTwoIII.zCode i))
      (Item434SmallTwoIII.zCode i) = one6) ∧
    (∀ i j : Fin 3,
      commutes6 (Item434SmallTwoIII.zCode i) (Item434SmallTwoIII.zCode j) = true) ∧
    mul6 (mul6 Item434SmallTwoIII.tCode Item434SmallTwoIII.tCode) Item434SmallTwoIII.tCode =
      one6 ∧
    (∀ i : Fin 3, mul6 (mul6 Item434SmallTwoIII.tCode (Item434SmallTwoIII.zCode i))
      Item434SmallTwoIII.tCodeInv = Item434SmallTwoIII.zCode (i + 1)) := by
  decide

set_option maxRecDepth 100000 in
theorem vecCode_check : ∀ a < 3, ∀ b < 3, ∀ c < 3,
    (a + b + c = 0 ∨ Item434SmallTwoIII.vecCode a b c ≠ one6) ∧
      Item434SmallTwoIII.vecCode a b c ≠ Item434SmallTwoIII.tCode := by
  decide

theorem canon6_vecCodeZ (v : Fin 3 → ZMod 3) :
    canon6 (Item434SmallTwoIII.vecCodeZ v) = true :=
  Item434SmallTwoIII.canon6_vecCode _ _ _

theorem wreathFacts_zS : WreathFacts zS tS := by
  obtain ⟨hz3, hzc, ht3, hconj⟩ := wreath_check
  have hzpow : ∀ i, zS i ^ 3 = 1 := fun i => by
    apply mat6_injective
    rw [map_pow, pow_three', mat6_zS, ← dec6_mul6, ← dec6_mul6, hz3 i, dec6_one6, map_one]
  have htconj : ∀ i, tS * zS i * tS⁻¹ = zS (i + 1) := fun i => by
    apply mat6_injective
    rw [map_mul, map_mul, mat6_tS, mat6_tS_inv, mat6_zS, mat6_zS, ← dec6_mul6, ← dec6_mul6,
      hconj i]
  refine ⟨hzpow, fun i j => commute_of_commutes6 (mat6_zS i) (mat6_zS j) (hzc i j),
    fun v hv => ?_, ?_, htconj 0, htconj 1, htconj 2, fun v hv => ?_⟩
  · have hm := congrArg mat6 hv
    rw [map_one, mat6_vecElt_zS, ← dec6_one6] at hm
    have he := dec6_injective (canon6_vecCodeZ v) canon6_one6 hm
    rcases (vecCode_check _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _
        (ZMod.val_lt (v 2))).1 with h0 | hne
    · have e0 : (v 0).val = 0 := by omega
      have e1 : (v 1).val = 0 := by omega
      have e2 : (v 2).val = 0 := by omega
      funext i
      fin_cases i
      · exact (ZMod.val_eq_zero _).mp e0
      · exact (ZMod.val_eq_zero _).mp e1
      · exact (ZMod.val_eq_zero _).mp e2
    · exact absurd he hne
  · apply mat6_injective
    rw [map_pow, pow_three', mat6_tS, ← dec6_mul6, ← dec6_mul6, ht3, dec6_one6, map_one]
  · have hm := congrArg mat6 hv
    rw [mat6_vecElt_zS, mat6_tS] at hm
    exact (vecCode_check _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _
      (ZMod.val_lt (v 2))).2 (dec6_injective (canon6_vecCodeZ v)
        (pairCheck_spec tPair_check).1 hm)

theorem card_wreathW_zS : Nat.card (wreathW zS tS) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts_zS)
  rw [Item434SmallTwoIII.factorization_card_H6] at hle
  have := le_card_wreathW wreathFacts_zS
  norm_num at hle
  omega

set_option maxRecDepth 100000 in
theorem e_check :
    mul6 (mul6 eCode eCode) eCode = one6 ∧
      commutes6 eCode (Item434SmallTwoIII.vecCodeZ ![1, 1, 1]) = true ∧
      commutes6 eCode Item434SmallTwoIII.tCode = true ∧
      ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ j < 3,
        eCode ≠ mul6 (Item434SmallTwoIII.vecCode a b c)
          (Item434SmallTwoIII.powCode Item434SmallTwoIII.tCode j) := by
  decide

theorem eS_pow_three : eS ^ 3 = 1 := by
  apply mat6_injective
  rw [map_pow, pow_three', mat6_eS, ← dec6_mul6, ← dec6_mul6, e_check.1, dec6_one6, map_one]

theorem eS_comm_c : eS * vecElt zS ![1, 1, 1] = vecElt zS ![1, 1, 1] * eS :=
  commute_of_commutes6 mat6_eS (mat6_vecElt_zS _) e_check.2.1

theorem eS_comm_t : eS * tS = tS * eS :=
  commute_of_commutes6 mat6_eS mat6_tS e_check.2.2.1

theorem eS_not_mem_wreathW : eS ∉ wreathW zS tS := by
  intro h
  obtain ⟨v, j, hv⟩ := mem_wreathW wreathFacts_zS h
  have hm := congrArg mat6 hv
  rw [map_mul, map_pow, mat6_eS, mat6_vecElt_zS, mat6_tS, ← Item434SmallTwoIII.dec6_powCode,
    ← dec6_mul6] at hm
  exact e_check.2.2.2 _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _ (ZMod.val_lt (v 2)) _ j.isLt
    (dec6_injective (pairCheck_spec ePair_check).1 (canon6_mul6 _ _) hm)

theorem exists_E27_sp62 {D : Subgroup H6} (hD : CFSG.Assembly.IsElemAbelian 3 D) :
    ∃ E : Subgroup H6, CFSG.Assembly.IsElemAbelian 3 E ∧ D ≤ E ∧ Nat.card E = 27 :=
  exists_E27 wreathFacts_zS eS_pow_three eS_comm_c eS_comm_t eS_not_mem_wreathW
    (by rw [card_wreathW_zS, Item434SmallTwoIII.factorization_card_H6]; norm_num) hD

end Sp62

end Res423Three

open Res423Three

theorem k423SevenSp62 : K423SevenSp62 := by
  rintro X _ _ ⟨φ⟩ D hD hD9 Y hY hα
  exfalso
  set ψ : X ≃* Census.Carrier.Sp6Two.H6 := φ.trans Item434SmallTwoIII.sp62Equiv
  obtain ⟨E, hE, hDE, hE27⟩ := exists_E27_sp62 (Res423Two.isElemAbelian_map' ψ.toMonoidHom hD.prop)
  have hle : D ≤ E.map ψ.symm.toMonoidHom := fun x hx =>
    ⟨ψ x, hDE ⟨x, hx, rfl⟩, ψ.symm_apply_apply x⟩
  have h1 := Subgroup.card_le_of_le (hD.2 (Res423Two.isElemAbelian_map' _ hE) hle)
  rw [Subgroup.card_map_of_injective ψ.symm.injective, hE27, hD9] at h1
  omega

end CFSG.RankThree.PartTwo.Sec4
