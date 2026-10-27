module

public import CFSG.Quasithin.SteinbergBSA7ReversalPair
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.Quasithin.SteinbergBN

open Subgroup CFSG CFSG.QuasithinUnique CFSG.LocalAnalysis.SteinbergBV.ConstantRank
open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

theorem conjugate_conjugate' (H : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate H a) b = CFSG.conjugate H (a * b) :=
  SteinbergBS.ReversalOvergroup.conjugate_conjugate_eq H a b

theorem conjugate_commutator' (H K : Subgroup G) (g : G) :
    CFSG.conjugate ⁅H, K⁆ g = ⁅CFSG.conjugate H g, CFSG.conjugate K g⁆ :=
  Subgroup.map_commutator _ _ _

theorem conjugate_le_conjJoin {D U : Subgroup G} {g : G} (hg : g ∈ D) :
    CFSG.conjugate U g ≤ conjJoin D U :=
  le_iSup (fun s : D => U.map (MulAut.conj (s : G)).toMonoidHom) ⟨g⁻¹, inv_mem hg⟩

theorem commutator_le_of_le_normalizer {H K V : Subgroup G} (hH : H ≤ normalizer (V : Set G))
    (hK : K ≤ V) : ⁅H, K⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 (hH hh) k).1 (hK hk)) (inv_mem (hK hk))

end Helpers

variable {G : Type} [Group G] [Finite G]

theorem A3_reversal_diagonal_characteristic_two_overgroup
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {P K U Q D₀ V X A E : Subgroup G} (hPT : P ≤ T) (hTP : P.relIndex T = 2)
    (hK : IsShort2 K) (h3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3)
    (hPK : P ≤ normalizer (K : Set G)) (hU : U = blockQ K) (hUP : U ≤ P) {t x : G}
    (htT : t ∈ T) (htP : t ∉ P) (hKt : ⁅K, CFSG.conjugate K t⁆ = ⊥)
    (hx : x ∈ normalizer (P : Set G)) (hUx : ⁅U, CFSG.conjugate U x⁆ ≠ ⊥)
    (hQ : Q = P ⊓ centralizer (U : Set G))
    (hD₀ : D₀ = closure ((P : Set G) ∪ {y | y ∈ normalizer (P : Set G) ∧ Odd (orderOf y)}))
    (hV : V = conjJoin D₀ U) (hX : X = D₀ ⊔ K) (hA : A = CFSG.conjugate U x)
    (hE : E = ⁅U, A⁆) :
    (V ≤ X ∧ X ≤ normalizer (V : Set G)) ∧ U ≤ V ∧ V ≤ Q ∧ Q ≤ P ∧ IsSylowTwoOf P X ∧
      X ⊓ normalizer (P : Set G) = D₀ ∧
      ¬ X ⊓ normalizer (P : Set G) ≤ X ⊓ normalizer (U : Set G) ∧
      x ∉ X ∧ t ∉ X ∧ x * t ∈ D₀ ∧ (A ≤ P ∧ P ≤ normalizer (A : Set G)) ∧
      Nat.card ↥(A ⊓ centralizer (U : Set G)) = 2 ∧
      (∀ e ∈ E, e ≠ 1 →
        E ≠ CFSG.conjugate E t ∧ Nat.card E = 2 ∧ Nat.card (CFSG.conjugate E t) = 2 ∧
          E ≤ V ∧ CFSG.conjugate E t ≤ V ∧ e * (t⁻¹ * e * t) ∈ V ∧
          e * (t⁻¹ * e * t) ∈ (T : Subgroup G) ⊓ centralizer (T : Set G) ∧
          e * (t⁻¹ * e * t) ≠ 1 ∧ (e * (t⁻¹ * e * t)) ^ 2 = 1) ∧
      CharTwo (normalizer (V : Set G)) ∧ CharTwo X := by
  classical
  have hP2 : IsPGroup 2 P := T.isPGroup'.to_le hPT
  obtain ⟨-, hUK, -, hUexp, hUab, -, hUKC, -, -⟩ := SteinbergBS.ReversalPair.a3_data hK h3
  rw [← hU] at hUK hUexp hUab hUKC
  obtain ⟨⟨-, -, hKU, -, -, hQK, -, -, -⟩, hrev, hodd⟩ :=
    SteinbergBS.actual_A3_reversal_pair_identities_and_odd_commutation hK h3 hP2 hPK hU hUP hQ
      rfl
  have hE1 : E ≠ ⊥ := by
    rw [hE, hA]
    exact hUx
  obtain ⟨hAP, hPA, hEUA, hUAC, hUCA, hEcard, hEZ, -⟩ := hrev x hx A E hA hE hE1
  have hPU : P ≤ normalizer (U : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
    rw [hU]
    exact hPK.trans h
  have hSchar : (P.subgroupOf P).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hxQ : ¬ CFSG.conjugate U x ≤ Q := by
    intro h
    apply hUx
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h.trans (hQ ▸ inf_le_right)
  have hUt : ⁅U, CFSG.conjugate U t⁆ = ⊥ := by
    rw [eq_bot_iff, ← hKt]
    exact Subgroup.commutator_mono hUK (Subgroup.map_mono hUK)
  obtain ⟨-, hUV, hVQ, hQP, hVX, hXV, hD₀Y, hD₀idx, hXY, hSyl, hxX, htX, -, hXPU⟩ :=
    SteinbergBS.odd_conjugates_construct_actual_reversal_overgroup T hPT hTP le_rfl hSchar hUP
      hUab hPU hQ hodd hx hxQ htT htP hUt hQK hD₀ hV hX
  have hPTn : (P.subgroupOf T).Normal := normal_of_index_eq_two hTP
  have hTY : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hPT).1 hPTn
  have htY : t ∈ normalizer (P : Set G) := hTY htT
  have hD₀X : D₀ ≤ X := hX ▸ le_sup_left
  have hxt : x * t ∈ D₀ := by
    have hidx : (D₀.subgroupOf (normalizer (P : Set G))).index = 2 := hD₀idx
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨t, htY⟩)).2
      (iff_of_false (fun h => hxX (hD₀X h)) fun h => htX (hD₀X h))
    exact h
  have hCA : Nat.card ↥(A ⊓ centralizer (U : Set G)) = 2 := by
    rw [← hUCA, ← hUAC, ← hEUA, hEcard]
  have hKKt : K ⊓ CFSG.conjugate K t = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyK, hyKt⟩ := mem_inf.1 hy
    have hyC : y ∈ centralizer (K : Set G) := by
      have h := Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((Subgroup.commutator_comm _ _).trans hKt)
      exact h hyKt
    have hyU : y ∈ U := by
      rw [← hKU]
      exact mem_inf.2 ⟨hyK, centralizer_le hUK hyC⟩
    rw [← hUKC]
    exact mem_inf.2 ⟨hyU, hyC⟩
  have hEU : E ≤ U := hEUA ▸ inf_le_left
  have hEEt : E ⊓ CFSG.conjugate E t = ⊥ := by
    rw [eq_bot_iff, ← hKKt]
    exact inf_le_inf (hEU.trans hUK) (Subgroup.map_mono (hEU.trans hUK))
  have hEtV : CFSG.conjugate E t ≤ V := by
    rw [hE, conjugate_commutator', hA, conjugate_conjugate']
    refine commutator_le_of_le_normalizer ?_ ((conjugate_le_conjJoin hxt).trans hV.ge)
    have hUtP : CFSG.conjugate U t ≤ P := by
      rw [← conjugate_eq_self_of_mem_normalizer htY]
      exact Subgroup.map_mono hUP
    exact (hUtP.trans (hSyl.1)).trans hXV
  have hdiag : ∀ e ∈ E, e ≠ 1 →
      e * (t⁻¹ * e * t) ∈ V ∧ e * (t⁻¹ * e * t) ∈ (T : Subgroup G) ⊓ centralizer (T : Set G) ∧
      e * (t⁻¹ * e * t) ≠ 1 ∧ (e * (t⁻¹ * e * t)) ^ 2 = 1 := by
    intro e he he1
    have hetE : t⁻¹ * e * t ∈ CFSG.conjugate E t := by
      rw [mem_conjugate_iff_conj]
      simpa [mul_assoc] using he
    have heZ := hEZ he
    have hZt : CFSG.conjugate (P ⊓ centralizer (P : Set G)) t = P ⊓ centralizer (P : Set G) := by
      rw [conjugate_inf, conjugate_centralizer, conjugate_eq_self_of_mem_normalizer htY]
    have hetZ : t⁻¹ * e * t ∈ P ⊓ centralizer (P : Set G) := by
      rw [← hZt, mem_conjugate_iff_conj]
      simpa [mul_assoc] using heZ
    have he2 : e * e = 1 := hUexp e (hEU he)
    have hcomm : e * (t⁻¹ * e * t) = (t⁻¹ * e * t) * e :=
      (mem_centralizer_iff.1 (mem_inf.1 heZ).2 _ (mem_inf.1 hetZ).1).symm
    have hzT : e * (t⁻¹ * e * t) ∈ (T : Subgroup G) :=
      mul_mem (hPT (mem_inf.1 heZ).1) (hPT (mem_inf.1 hetZ).1)
    have ht2 : t * t ∈ P := by
      have := Subgroup.sq_mem_of_index_two (show (P.subgroupOf T).index = 2 from hTP) ⟨t, htT⟩
      rw [sq] at this
      exact this
    have htt : t * e * t⁻¹ = t⁻¹ * e * t := by
      have h := mem_centralizer_iff.1 (mem_inf.1 heZ).2 (t * t) ht2
      calc t * e * t⁻¹ = t⁻¹ * ((t * t) * e) * t⁻¹ := by group
        _ = t⁻¹ * (e * (t * t)) * t⁻¹ := by rw [h]
        _ = t⁻¹ * e * t := by group
    have hzt : t * (e * (t⁻¹ * e * t)) * t⁻¹ = e * (t⁻¹ * e * t) := by
      calc t * (e * (t⁻¹ * e * t)) * t⁻¹ = (t * e * t⁻¹) * e := by group
        _ = (t⁻¹ * e * t) * e := by rw [htt]
        _ = e * (t⁻¹ * e * t) := hcomm.symm
    have hzP : ∀ p ∈ P, p * (e * (t⁻¹ * e * t)) = e * (t⁻¹ * e * t) * p := by
      intro p hp
      have h1 := mem_centralizer_iff.1 (mem_inf.1 heZ).2 p hp
      have h2 := mem_centralizer_iff.1 (mem_inf.1 hetZ).2 p hp
      calc p * (e * (t⁻¹ * e * t)) = (p * e) * (t⁻¹ * e * t) := by group
        _ = (e * p) * (t⁻¹ * e * t) := by rw [h1]
        _ = e * (p * (t⁻¹ * e * t)) := by group
        _ = e * ((t⁻¹ * e * t) * p) := by rw [h2]
        _ = e * (t⁻¹ * e * t) * p := by group
    refine ⟨mul_mem (hUV (hEU he)) (hEtV hetE), mem_inf.2 ⟨hzT, ?_⟩, ?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro s hs
      by_cases hsP : s ∈ P
      · exact hzP s hsP
      · have hst : s * t⁻¹ ∈ P := by
          have h := (Subgroup.mul_mem_iff_of_index_two
            (show (P.subgroupOf T).index = 2 from hTP) (a := ⟨s, hs⟩)
            (b := ⟨t⁻¹, inv_mem htT⟩)).2 (iff_of_false hsP fun h => htP (by
              have := inv_mem (show t⁻¹ ∈ P from h)
              rwa [inv_inv] at this))
          exact h
        have h1 := hzP _ hst
        have h2 : t * (e * (t⁻¹ * e * t)) = e * (t⁻¹ * e * t) * t := by
          calc t * (e * (t⁻¹ * e * t)) = t * (e * (t⁻¹ * e * t)) * t⁻¹ * t := by group
            _ = e * (t⁻¹ * e * t) * t := by rw [hzt]
        calc s * (e * (t⁻¹ * e * t)) = (s * t⁻¹) * (t * (e * (t⁻¹ * e * t))) := by group
          _ = (s * t⁻¹) * (e * (t⁻¹ * e * t) * t) := by rw [h2]
          _ = ((s * t⁻¹) * (e * (t⁻¹ * e * t))) * t := by group
          _ = (e * (t⁻¹ * e * t) * (s * t⁻¹)) * t := by rw [h1]
          _ = e * (t⁻¹ * e * t) * s := by group
    · intro hz
      apply he1
      have het : t⁻¹ * e * t = e := by
        calc t⁻¹ * e * t = e * (e * (t⁻¹ * e * t)) := by
              rw [← mul_assoc, he2, one_mul]
          _ = e := by rw [hz, mul_one]
      have hmem : e ∈ E ⊓ CFSG.conjugate E t := mem_inf.2 ⟨he, het ▸ hetE⟩
      rwa [hEEt, mem_bot] at hmem
    · rw [sq]
      calc e * (t⁻¹ * e * t) * (e * (t⁻¹ * e * t)) =
          (e * e) * ((t⁻¹ * e * t) * (t⁻¹ * e * t)) := by
            calc e * (t⁻¹ * e * t) * (e * (t⁻¹ * e * t)) =
                e * ((t⁻¹ * e * t) * e) * (t⁻¹ * e * t) := by group
              _ = e * (e * (t⁻¹ * e * t)) * (t⁻¹ * e * t) := by rw [← hcomm]
              _ = (e * e) * ((t⁻¹ * e * t) * (t⁻¹ * e * t)) := by group
        _ = 1 := by
          rw [he2, one_mul]
          calc t⁻¹ * e * t * (t⁻¹ * e * t) = t⁻¹ * (e * e) * t := by group
            _ = 1 := by rw [he2, mul_one, inv_mul_cancel]
  obtain ⟨⟨e, heE⟩, he1⟩ := ne_bot_iff_exists_ne_one.mp hE1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  obtain ⟨hzV, hzZ, hz1, -⟩ := hdiag e heE he1'
  have hTsyl : IsSylowTwoOf (T : Subgroup G) ⊤ := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [show ((T : Subgroup G).subgroupOf ⊤).index = (T : Subgroup G).relIndex ⊤ from rfl,
      Subgroup.relIndex_top_right]
    exact T.not_dvd_index
  have hV2 : IsPGroup 2 V := hP2.to_le (hVQ.trans hQP)
  have hNV : CharTwo (normalizer (V : Set G)) := by
    refine charTwo_normalizer_of_inf_center hev hTsyl hV2 fun h => hz1 ?_
    have : e * (t⁻¹ * e * t) ∈ V ⊓ ((T : Subgroup G) ⊓
        centralizer (((T : Subgroup G) : Set G))) := mem_inf.2 ⟨hzV, hzZ⟩
    rwa [h, mem_bot] at this
  have hXchar : CharTwo X := by
    obtain ⟨S, hPS, hS⟩ := exists_isSylowTwoOf_of_le (hSyl.1.trans hXV) hP2
    refine charTwo_of_relIndex_le_two hNV hS hXV ?_
    have hST : Nat.card S ≤ Nat.card (T : Subgroup G) := by
      obtain ⟨T', hST'⟩ := hS.2.1.exists_le_sylow
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      calc Nat.card S ≤ Nat.card (T' : Subgroup G) := Subgroup.card_le_of_le hST'
        _ = Nat.card (T : Subgroup G) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    have hTcard : Nat.card (T : Subgroup G) = 2 * Nat.card P := by
      have h := Subgroup.relIndex_mul_card P T
      rw [hTP, inf_of_le_left hPT] at h
      exact h.symm
    have hXS := Subgroup.relIndex_mul_card X S
    have hPXS : Nat.card P ≤ Nat.card ↥(X ⊓ S) := Subgroup.card_le_of_le (le_inf hSyl.1 hPS)
    have hPpos : 0 < Nat.card P := Nat.card_pos
    by_contra hcon
    push Not at hcon
    have : 3 * Nat.card P ≤ X.relIndex S * Nat.card ↥(X ⊓ S) :=
      Nat.mul_le_mul (by omega) hPXS
    omega
  refine ⟨⟨hVX, hXV⟩, hUV, hVQ, hQP, hSyl, hXY, hXPU, hxX, htX, hxt, ⟨hAP, hPA⟩, hCA,
    fun e he he1 => ?_, hNV, hXchar⟩
  obtain ⟨h1, h2, h3', h4⟩ := hdiag e he he1
  have hcardt : Nat.card (CFSG.conjugate E t) = Nat.card E :=
    card_map_of_injective (MulAut.conj t⁻¹).injective
  refine ⟨fun h => hE1 ?_, hEcard, by rw [hcardt, hEcard], hEU.trans hUV, hEtV, h1, h2, h3', h4⟩
  rw [eq_bot_iff, ← hEEt]
  exact le_inf le_rfl h.le
