module

public import CFSG.Quasithin.Background.SmithB42U33GenData
public import CFSG.Quasithin.Vol2.Ch12Sec4G2OffTwo
public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.B42U33

open CFSG.Open CFSG.Quasithin H13 H13.Orbit JonesParshall Explicit
open scoped Pointwise

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

@[expose] def colCode (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) (k : Fin 8) : ℕ :=
  (M 0 k).val + 2 * (M 1 k).val + 4 * (M 2 k).val + 8 * (M 3 k).val + 16 * (M 4 k).val +
    32 * (M 5 k).val + 64 * (M 6 k).val + 128 * (M 7 k).val

theorem zornCoord_symm_single : ∀ k : Fin 8,
    (zornCoord (F := ZMod 2)).symm (Pi.single k 1) = decodeZ (2 ^ (k : ℕ)) := by
  decide +kernel

theorem encodeZ_eq_colCode (g : Amb) (k : Fin 8) :
    encodeZ (g (decodeZ (2 ^ (k : ℕ)))) = colCode (zmat g.toLinearMap) k := by
  have h : ∀ i : Fin 8, zmat g.toLinearMap i k = zornCoord (g (decodeZ (2 ^ (k : ℕ)))) i := by
    intro i
    rw [← zornCoord_symm_single k]
    simp [zmat, LinearMap.toMatrix'_apply]
  simp only [colCode, h]
  rfl

theorem matCode_eq_colCode (g : Amb) :
    matCode ⇑g = (List.finRange 8).map (colCode (zmat g.toLinearMap)) := by
  apply List.ext_getElem (by simp [matCode])
  intro n h1 _
  have hn : n < 8 := by simpa [matCode] using h1
  simp only [matCode, List.getElem_map, List.getElem_range, List.getElem_finRange]
  exact encodeZ_eq_colCode g ⟨n, hn⟩

theorem matCode_g2a :
    matCode ⇑(g2a : Amb) = codeA := by
  rw [matCode_eq_colCode]
  change (List.finRange 8).map (colCode (cmat g2a)) = _
  rw [cmat_g2a]
  decide +kernel

theorem matCode_g2b :
    matCode ⇑(g2b : Amb) = codeB := by
  rw [matCode_eq_colCode]
  change (List.finRange 8).map (colCode (cmat g2b)) = _
  rw [cmat_g2b]
  decide +kernel

theorem g2a_inv :
    (g2a : Amb)⁻¹ = (g2a : Amb) * (g2a : Amb) := by
  refine inv_eq_of_mul_eq_one_right (linearEquiv_eq_of_matCode ?_)
  rw [matCode_mul, matCode_mul, matCode_g2a, matCode_one, code_cubes.1, code_cubes.2.2.1]

theorem g2b_inv :
    (g2b : Amb)⁻¹ = (g2b : Amb) * (g2b : Amb) := by
  refine inv_eq_of_mul_eq_one_right (linearEquiv_eq_of_matCode ?_)
  rw [matCode_mul, matCode_mul, matCode_g2b, matCode_one, code_cubes.2.1, code_cubes.2.2.2]

@[expose] noncomputable def letE (i : ℕ) : Amb :=
  [(g2a : Amb), (g2b : Amb), (g2a : Amb)⁻¹, (g2b : Amb)⁻¹].getD i 1

@[expose] noncomputable def wordE (w : List ℕ) : Amb := (w.map letE).prod

theorem letE_of_four_le {i : ℕ} (hi : 4 ≤ i) : letE i = 1 := by
  rw [letE, List.getD_eq_default _ _ (by simpa using hi)]

theorem matCode_letE
    (i : ℕ) : matCode ⇑(letE i) = letC i := by
  match i with
  | 0 => exact matCode_g2a
  | 1 => exact matCode_g2b
  | 2 =>
    change matCode ⇑(g2a : Amb)⁻¹ = codeAi
    rw [g2a_inv, matCode_mul, matCode_g2a, code_cubes.1]
  | 3 =>
    change matCode ⇑(g2b : Amb)⁻¹ = codeBi
    rw [g2b_inv, matCode_mul, matCode_g2b, code_cubes.2.1]
  | n + 4 =>
    rw [letE_of_four_le (by omega), letC, List.getD_eq_default _ _ (by simp)]
    exact matCode_one

theorem wordE_cons (i : ℕ) (w : List ℕ) : wordE (i :: w) = letE i * wordE w := by
  simp [wordE]

theorem wordE_append (u v : List ℕ) : wordE (u ++ v) = wordE u * wordE v := by
  simp [wordE]

theorem matCode_wordE
    (w : List ℕ) : matCode ⇑(wordE w) = wordC w := by
  induction w with
  | nil => exact matCode_one
  | cons i w ih =>
    rw [wordE_cons, matCode_mul, matCode_letE, ih]
    rfl

theorem letE_swapL (i : ℕ) : letE (swapL i) = (letE i)⁻¹ := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => exact (inv_inv _).symm
  | 3 => exact (inv_inv _).symm
  | n + 4 =>
    have h : swapL (n + 4) = n + 4 := by
      rw [swapL, List.getD_eq_default _ _ (by simp)]
    rw [h, letE_of_four_le (by omega), inv_one]

theorem wordE_invW (w : List ℕ) : wordE (invW w) = (wordE w)⁻¹ := by
  induction w with
  | nil => simp [wordE, invW]
  | cons i w ih =>
    have e : invW (i :: w) = invW w ++ [swapL i] := by simp [invW]
    rw [e, wordE_append, ih, wordE_cons i w, mul_inv_rev]
    simp [wordE, letE_swapL]

theorem letE_mem_subG2 (i : ℕ) : letE i ∈ subG2 := by
  have ha : (g2a : Amb) ∈ subG2 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : (g2b : Amb) ∈ subG2 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | 2 => exact subG2.inv_mem ha
  | 3 => exact subG2.inv_mem hb
  | n + 4 =>
    rw [letE_of_four_le (by omega)]
    exact subG2.one_mem

theorem wordE_mem_subG2 (w : List ℕ) : wordE w ∈ subG2 := by
  refine subG2.list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact letE_mem_subG2 i

theorem subG2_le_g2 : subG2 ≤ quasithinG2 (ZMod 2) := by
  rw [subG2, Subgroup.closure_le, G11.P3G2.quasithinG2_eq_cayleyGroup]
  rintro x (rfl | rfl)
  · exact g2a.2
  · exact g2b.2

theorem subG2_eq_commutator :
    subG2 = ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  rw [← g2Two_commutator_eq, G11.P3G2.quasithinG2_eq_cayleyGroup]

@[expose] noncomputable def wordG (w : List ℕ) : ↥(quasithinG2 (ZMod 2)) :=
  ⟨wordE w, subG2_le_g2 (wordE_mem_subG2 w)⟩

theorem wordG_mem
    (w : List ℕ) : wordG w ∈ g2Derived (ZMod 2) := by
  rw [g2Derived, Subgroup.mem_subgroupOf, ← subG2_eq_commutator]
  exact wordE_mem_subG2 w

@[expose] noncomputable def Wit.conjElts (W : Wit) : List Amb :=
  W.conj.flatMap fun d => W.gens.map fun t => wordE d * sElt t * (wordE d)⁻¹

@[expose] noncomputable def prodE (X : List Amb) (w : List ℕ) : Amb :=
  (w.map fun k => X.getD k 1).prod

theorem Wit.map_conjElts
    {W : Wit} (hW : ∀ t ∈ W.gens, t < 64) :
    W.conjElts.map (fun x : Amb => matCode ⇑x) = W.conjCodes := by
  simp only [Wit.conjElts, Wit.conjCodes, List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun d _ => List.map_congr_left fun t ht => ?_
  simp only [Function.comp_apply]
  rw [matCode_mul, matCode_mul, matCode_wordE, matCode_sElt (hW t ht), ← wordE_invW,
    matCode_wordE]
  rfl

theorem matCode_prodE (X : List Amb) (w : List ℕ) :
    matCode ⇑(prodE X w) = prodC (X.map fun x : Amb => matCode ⇑x) w := by
  induction w with
  | nil => exact matCode_one
  | cons k w ih =>
    simp only [prodE, List.map_cons, List.prod_cons] at ih ⊢
    rw [matCode_mul, ih]
    change _ = mmul _ _
    congr 1
    rw [show idMat = (fun x : Amb => matCode ⇑x) 1 from matCode_one.symm, List.getD_map]

theorem Wit.prodE_wa
    {W : Wit} (hW : W.ok = true) (hg : ∀ t ∈ W.gens, t < 64) :
    prodE W.conjElts W.wa = (g2a : Amb) ∧ prodE W.conjElts W.wb = (g2b : Amb) := by
  simp only [Wit.ok, Bool.and_eq_true, beq_iff_eq] at hW
  obtain ⟨⟨h1, h2⟩, h3⟩ := hW
  constructor
  · apply linearEquiv_eq_of_matCode
    rw [matCode_prodE, Wit.map_conjElts hg, ← h1, h2, matCode_g2a]
  · apply linearEquiv_eq_of_matCode
    rw [matCode_prodE, Wit.map_conjElts hg, ← h1, h3, matCode_g2b]

theorem Wit.le_closure
    {W : Wit} (hW : W.ok = true)
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : ∀ t ∈ W.gens, t < 64 ∧ sEltG t ∈ B) :
    g2Derived (ZMod 2) ≤ Subgroup.closure (⋃ i : Fin W.conj.length,
      ((B.map (MulAut.conj (wordG (W.conj.get i))).toMonoidHom :
        Subgroup ↥(quasithinG2 (ZMod 2))) : Set ↥(quasithinG2 (ZMod 2)))) := by
  set C := Subgroup.closure (⋃ i : Fin W.conj.length,
      ((B.map (MulAut.conj (wordG (W.conj.get i))).toMonoidHom :
        Subgroup ↥(quasithinG2 (ZMod 2))) : Set ↥(quasithinG2 (ZMod 2)))) with hC
  set C' := C.map (quasithinG2 (ZMod 2)).subtype with hC'
  have hX : ∀ x ∈ W.conjElts, x ∈ C' := by
    intro x hx
    simp only [Wit.conjElts, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨d, hd, t, ht, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hd
    refine ⟨wordG (W.conj.get i) * sEltG t * (wordG (W.conj.get i))⁻¹,
      Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, ⟨sEltG t, (hB t ht).2, rfl⟩⟩), rfl⟩
  have hP : ∀ w, prodE W.conjElts w ∈ C' := by
    intro w
    refine C'.list_prod_mem fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rcases lt_or_ge k W.conjElts.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hX _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      exact C'.one_mem
  obtain ⟨ha, hb⟩ := Wit.prodE_wa hW fun t ht => (hB t ht).1
  have hsub : subG2 ≤ C' := by
    rw [subG2, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [← ha]
      exact hP _
    · rw [← hb]
      exact hP _
  intro x hx
  have hx' : (x : Amb) ∈ subG2 := by
    rw [subG2_eq_commutator]
    exact Subgroup.mem_subgroupOf.1 hx
  obtain ⟨y, hy, hyx⟩ := hsub hx'
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem g2Derived_isNormal (K : Type) [Field K] : (g2Derived K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.commutator_le_self _)).2
    (Subgroup.normalizer_commutator_ge_left _ _)

theorem shortGen_of_wit
    {W : Wit} (hW : W.ok = true)
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : ∀ t ∈ W.gens, t < 64 ∧ sEltG t ∈ B) :
    ∃ d : Fin W.conj.length → ↥(quasithinG2 (ZMod 2)), (∀ i, d i ∈ g2Derived (ZMod 2)) ∧
      g2Derived (ZMod 2) ≤ Subgroup.closure (⋃ i, ((B.map (MulAut.conj (d i)).toMonoidHom :
        Subgroup ↥(quasithinG2 (ZMod 2))) : Set ↥(quasithinG2 (ZMod 2)))) :=
  ⟨fun i => wordG (W.conj.get i), fun _ => wordG_mem _, Wit.le_closure hW hB⟩

theorem shortGen_sylow
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    ∃ r m : ℕ, Nat.card B = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ d : Fin m → ↥(quasithinG2 (ZMod 2)), (∀ i, d i ∈ g2Derived (ZMod 2)) ∧
        g2Derived (ZMod 2) ≤ Subgroup.closure (⋃ i, ((B.map (MulAut.conj (d i)).toMonoidHom :
          Subgroup ↥(quasithinG2 (ZMod 2))) : Set ↥(quasithinG2 (ZMod 2)))) := by
  classical
  have hcard := card_eq_idx hB
  have hw1 : ∀ i ∈ idx B, i ≠ 0 → (wit1 i).conj.length ≤ 4 ∧
      (i ∈ sOuter → (wit1 i).conj.length ≤ 3) ∧
      ∃ d : Fin (wit1 i).conj.length → ↥(quasithinG2 (ZMod 2)),
        (∀ k, d k ∈ g2Derived (ZMod 2)) ∧
        g2Derived (ZMod 2) ≤ Subgroup.closure (⋃ k, ((B.map (MulAut.conj (d k)).toMonoidHom :
          Subgroup ↥(quasithinG2 (ZMod 2))) : Set ↥(quasithinG2 (ZMod 2)))) := by
    intro i hi hi0
    obtain ⟨hok, hgens, hlen, hout⟩ := wit1_ok i (idx_inv hB2 hi hi0)
    refine ⟨hlen, hout, shortGen_of_wit hok fun t ht => ?_⟩
    rw [hgens, List.mem_singleton] at ht
    subst ht
    exact mem_idx.1 hi
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exact absurd (Subgroup.eq_bot_of_card_eq B (by rw [hcard, hn])) hB1
  · obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    obtain ⟨hlen, -, d, hd, hle⟩ := hw1 i hi hi0
    exact ⟨1, _, by rw [hcard, hn]; rfl, le_rfl, by norm_num, by omega, d, hd, hle⟩
  · obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    have h4 : Nat.card B = 2 ^ 2 := by rw [hcard, hn]; norm_num
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with hiI | hiO
    · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with hjI | hjO
      · obtain ⟨hok, hgens, hlen⟩ := wit2_ok i hiI j hjI (Ne.symm hj0.2) (idx_comm hBc hi hj)
        obtain ⟨d, hd, hle⟩ := shortGen_of_wit hok fun t ht => by
          rcases hgens t ht with rfl | rfl
          · exact mem_idx.1 hi
          · exact mem_idx.1 hj
        exact ⟨2, _, h4, by norm_num, by norm_num, by omega, d, hd, hle⟩
      · obtain ⟨-, hout, d, hd, hle⟩ := hw1 j hj hj0.1
        have := hout hjO
        exact ⟨2, _, h4, by norm_num, by norm_num, by omega, d, hd, hle⟩
    · obtain ⟨-, hout, d, hd, hle⟩ := hw1 i hi hi0
      have := hout hiO
      exact ⟨2, _, h4, by norm_num, by norm_num, by omega, d, hd, hle⟩
  · have hcard8 := card_idx_le_8 hB hB2 hBc h8
    obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    obtain ⟨hok, hgens, hlen⟩ := wit3_ok e he
    obtain ⟨d, hd, hle⟩ := shortGen_of_wit hok fun t ht => mem_idx.1 ((hiff t).2 (hgens t ht))
    exact ⟨3, _, by rw [hcard, hcard8]; rfl, by norm_num, le_rfl, by omega, d, hd, hle⟩

theorem le_closure_conj {X : Type*} [Group X] {D B : Subgroup X} [D.Normal] (g : X) {m : ℕ}
    (d : Fin m → X)
    (h : D ≤ Subgroup.closure (⋃ i, (((B.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (d i)).toMonoidHom : Subgroup X) : Set X))) :
    D ≤ Subgroup.closure (⋃ i, ((B.map (MulAut.conj (g⁻¹ * d i * g)).toMonoidHom :
      Subgroup X) : Set X)) := by
  have key : Subgroup.closure (⋃ i, (((B.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (d i)).toMonoidHom : Subgroup X) : Set X)) ≤
      (Subgroup.closure (⋃ i, ((B.map (MulAut.conj (g⁻¹ * d i * g)).toMonoidHom :
        Subgroup X) : Set X))).comap (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := hi
    refine Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, b, hb, ?_⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  intro x hx
  have h1 := key (h (‹D.Normal›.conj_mem _ hx g))
  rw [Subgroup.mem_comap] at h1
  have e : (MulAut.conj g⁻¹).toMonoidHom (g * x * g⁻¹) = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rwa [e] at h1

theorem shortGen
    {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1) :
    ∃ r m : ℕ, Nat.card B = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ d : Fin m → ↥(quasithinG2 (ZMod 2)), (∀ i, d i ∈ g2Derived (ZMod 2)) ∧
        g2Derived (ZMod 2) ≤ Subgroup.closure (⋃ i, ((B.map (MulAut.conj (d i)).toMonoidHom :
          Subgroup ↥(quasithinG2 (ZMod 2))) : Set ↥(quasithinG2 (ZMod 2)))) := by
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB2 g.1 g.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) P sylowSub
  set c := (MulAut.conj g).toMonoidHom with hcdef
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  set B₁ := B.map c with hB₁def
  have hB₁S : B₁ ≤ sSubG := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : MulAut.conj g • b ∈ MulAut.conj g • (P : Subgroup ↥(quasithinG2 (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP hb)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    exact hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hcinj).1 h)
  have hB₁c : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  have hB₁2 : ∀ b ∈ B₁, b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  obtain ⟨r, m, hr, hr1, hr3, hmr, d, hd, hle⟩ := shortGen_sylow hB₁S hB₁ne hB₁c hB₁2
  refine ⟨r, m, ?_, hr1, hr3, hmr, fun i => g⁻¹ * d i * g, fun i => ?_, ?_⟩
  · rw [← hr, hB₁def, Subgroup.card_map_of_injective hcinj]
  · have := (g2Derived_isNormal (ZMod 2)).conj_mem _ (hd i) g⁻¹
    rwa [inv_inv] at this
  · exact @le_closure_conj _ _ _ _ (g2Derived_isNormal (ZMod 2)) g m d hle

end CFSG.Quasithin.B42U33
