module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofFrame

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.Assembly.RankThreeEven (projSp)

namespace Item812Res12

section Base

variable {H : Type*} [Group H] {z : Fin 3 → H} {t₀ : H}

@[expose] def sgnV (w : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  ![2 * w 0, 2 * w 1, w 2]

theorem sq_pow_val {x : H} (hx : x ^ 3 = 1) (e : ZMod 3) : (x ^ 2) ^ e.val = x ^ (2 * e).val := by
  have he : e = 0 ∨ e = 1 ∨ e = 2 := by decide +revert
  rcases he with rfl | rfl | rfl
  · rw [show (0 : ZMod 3).val = 0 from rfl, show ((2 : ZMod 3) * 0).val = 0 from rfl, pow_zero,
      pow_zero]
  · rw [show (1 : ZMod 3).val = 1 from rfl, show ((2 : ZMod 3) * 1).val = 2 from rfl, pow_one]
  · have h1 : (2 : ZMod 3).val = 2 := rfl
    have h2 : ((2 : ZMod 3) * 2).val = 1 := rfl
    rw [h1, h2, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hx, one_mul, pow_one]

theorem conj_vecElt_of_sgn (hf : WreathFacts z t₀) {s : H} (h0 : s * z 0 * s⁻¹ = z 0 ^ 2)
    (h1 : s * z 1 * s⁻¹ = z 1 ^ 2) (h2 : s * z 2 * s⁻¹ = z 2) (w : Fin 3 → ZMod 3) :
    s * vecElt z w * s⁻¹ = vecElt z (sgnV w) := by
  have hc : ∀ x : H, s * x * s⁻¹ = MulAut.conj s x := fun x => rfl
  rw [hc, vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc, ← hc, ← hc, h0, h1, h2,
    vecElt, sgnV]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [sq_pow_val (hf.pow_z 0), sq_pow_val (hf.pow_z 1)]

set_option maxRecDepth 100000 in
theorem irred_checks :
    (∀ w : Fin 3 → ZMod 3, w + sgnV w = Pi.single 2 (2 * w 2)) ∧
    (∀ w : Fin 3 → ZMod 3, Item8KFacts3.rotV
      (Item8KFacts3.rotV (Item8KFacts3.rotV w) + sgnV (Item8KFacts3.rotV (Item8KFacts3.rotV w))) =
        Pi.single 0 (2 * w 0)) ∧
    (∀ w : Fin 3 → ZMod 3, Item8KFacts3.rotV (Item8KFacts3.rotV
      (Item8KFacts3.rotV w + sgnV (Item8KFacts3.rotV w))) = Pi.single 1 (2 * w 1)) ∧
    (∀ (i : Fin 3) (c : ZMod 3), c ≠ 0 →
      (Pi.single i c : Fin 3 → ZMod 3) = Pi.single i 1 ∨
        (Pi.single i c : Fin 3 → ZMod 3) + Pi.single i c = Pi.single i 1) ∧
    (∀ w : Fin 3 → ZMod 3, w ≠ 0 → ∃ i : Fin 3, 2 * w i ≠ 0) ∧
    (∀ w : Fin 3 → ZMod 3, sgnV (sgnV w) = w) ∧
    (∀ i : Fin 3, Item8KFacts3.rotV (Pi.single i 1) = (Pi.single (i + 1) 1 : Fin 3 → ZMod 3)) ∧
    (∀ i j : Fin 3, j = i ∨ j = i + 1 ∨ j = i + 1 + 1) := by
  decide +kernel

theorem eq_bot_or_eq_baseA (hf : WreathFacts z t₀) {s : H}
    (hs : ∀ w, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)) {U : Subgroup H} (hUA : U ≤ baseA z)
    (hN : Subgroup.normalizer (baseA z : Set H) ≤ Subgroup.normalizer (U : Set H)) :
    U = ⊥ ∨ U = baseA z := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := irred_checks
  have hsN : s ∈ Subgroup.normalizer (baseA z : Set H) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨w, rfl⟩ := (mem_baseA_iff hf).mp hx
      rw [hs]
      exact vecElt_mem_baseA hf _
    · intro hx
      obtain ⟨w, hw⟩ := (mem_baseA_iff hf).mp hx
      have e1 : x = vecElt z (sgnV w) := by
        have h1 : s * vecElt z (sgnV w) * s⁻¹ = s * x * s⁻¹ := by rw [hs, c6, hw]
        exact (mul_left_cancel (mul_right_cancel h1)).symm
      rw [e1]
      exact vecElt_mem_baseA hf _
  have htU : ∀ u ∈ U, t₀ * u * t₀⁻¹ ∈ U := fun u hu =>
    (mem_normalizer_iff.mp (hN (t_mem_normalizer hf)) u).mp hu
  have hsU : ∀ u ∈ U, s * u * s⁻¹ ∈ U := fun u hu => (mem_normalizer_iff.mp (hN hsN) u).mp hu
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
  obtain ⟨w, hw⟩ := (mem_baseA_iff hf).mp (hUA y.2)
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hy1
    apply Subtype.ext
    rw [← hw]
    simp [vecElt]
  have hwU : vecElt z w ∈ U := by rw [hw]; exact y.2
  have hrot : ∀ v, vecElt z v ∈ U → vecElt z (Item8KFacts3.rotV v) ∈ U := fun v hv => by
    have := htU _ hv
    rwa [conj_vecElt hf] at this
  have hsgn : ∀ v, vecElt z v ∈ U → vecElt z (sgnV v) ∈ U := fun v hv => by
    have := hsU _ hv
    rwa [hs] at this
  have hadd : ∀ v v', vecElt z v ∈ U → vecElt z v' ∈ U → vecElt z (v + v') ∈ U :=
    fun v v' hv hv' => by
      rw [vecElt_add hf]
      exact U.mul_mem hv hv'
  have hP : ∀ v, vecElt z v ∈ U → vecElt z (v + sgnV v) ∈ U := fun v hv =>
    hadd _ _ hv (hsgn v hv)
  have p0 : vecElt z (Pi.single 0 (2 * w 0)) ∈ U := by
    rw [← c2 w]
    exact hrot _ (hP _ (hrot _ (hrot _ hwU)))
  have p1 : vecElt z (Pi.single 1 (2 * w 1)) ∈ U := by
    rw [← c3 w]
    exact hrot _ (hrot _ (hP _ (hrot _ hwU)))
  have p2 : vecElt z (Pi.single 2 (2 * w 2)) ∈ U := by
    rw [← c1 w]
    exact hP _ hwU
  obtain ⟨i, hi⟩ := c5 w hw0
  have hpi : vecElt z (Pi.single i (2 * w i)) ∈ U := by
    fin_cases i
    · exact p0
    · exact p1
    · exact p2
  have hei : vecElt z (Pi.single i 1) ∈ U := by
    rcases c4 i (2 * w i) hi with h | h
    · rwa [h] at hpi
    · rw [← h]
      exact hadd _ _ hpi hpi
  have hz : ∀ j, z j ∈ U := by
    intro j
    rw [← vecElt_single_one (z := z) j]
    rcases c8 i j with rfl | rfl | rfl
    · exact hei
    · rw [← c7]
      exact hrot _ hei
    · rw [← c7, ← c7]
      exact hrot _ (hrot _ hei)
  refine le_antisymm hUA ?_
  exact sup_le (sup_le (zpowers_le.mpr (hz 0)) (zpowers_le.mpr (hz 1))) (zpowers_le.mpr (hz 2))

theorem normalizer_map_le {M N : Type*} [Group M] [Group N] (e : M ≃* N) {E U : Subgroup M}
    (hN : Subgroup.normalizer (E : Set M) ≤ Subgroup.normalizer (U : Set M)) :
    Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup N) : Set N) ≤
      Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup N) : Set N) := by
  rw [← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq]
  exact map_mono hN

theorem irred_of_model [Finite H] (hf : WreathFacts z t₀)
    (hW : Nat.card (wreathW z t₀) = 3 ^ (Nat.card H).factorization 3)
    (h81 : Nat.card (wreathW z t₀) = 81) {s : H}
    (hs : ∀ w, s * vecElt z w * s⁻¹ = vecElt z (sgnV w)) {E U : Subgroup H}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hUE : U ≤ E)
    (hN : Subgroup.normalizer (E : Set H) ≤ Subgroup.normalizer (U : Set H)) :
    U = ⊥ ∨ U = E := by
  obtain ⟨g, rfl⟩ := Item812Res5.exists_eq_map_conj_baseA hf hW h81 hE hE27
  set c : H ≃* H := MulAut.conj g⁻¹ with hc
  have hE' : ((baseA z).map (MulAut.conj g).toMonoidHom).map c.toMonoidHom = baseA z := by
    have h1 := Sec4.Item434AltPerm.map_conj_map_conj_inv (baseA z) g⁻¹
    rwa [inv_inv] at h1
  have hN' := normalizer_map_le c hN
  rw [hE'] at hN'
  have hU' : U.map c.toMonoidHom ≤ baseA z := hE' ▸ map_mono hUE
  have hinj : Function.Injective c.toMonoidHom := c.injective
  rcases eq_bot_or_eq_baseA hf hs hU' hN' with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp h
  · right
    rw [← hE'] at h
    exact Subgroup.map_injective hinj h

end Base

@[expose] def sPerm9 : Perm (Fin 9) :=
  swap 0 1 * swap 3 4

theorem sPerm9_mem : sPerm9 ∈ alternatingGroup (Fin 9) := by
  rw [mem_alternatingGroup, sPerm9, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
  decide

@[expose] def sA9 : alternatingGroup (Fin 9) :=
  ⟨sPerm9, sPerm9_mem⟩

theorem sPerm9_conj : sPerm9 * Item812Res5.zPerm9 0 * sPerm9⁻¹ = Item812Res5.zPerm9 0 ^ 2 ∧
    sPerm9 * Item812Res5.zPerm9 1 * sPerm9⁻¹ = Item812Res5.zPerm9 1 ^ 2 ∧
    sPerm9 * Item812Res5.zPerm9 2 * sPerm9⁻¹ = Item812Res5.zPerm9 2 := by
  decide

theorem sA9_conj (w : Fin 3 → ZMod 3) :
    sA9 * vecElt Item812Res5.zA9 w * sA9⁻¹ = vecElt Item812Res5.zA9 (sgnV w) := by
  obtain ⟨h0, h1, h2⟩ := sPerm9_conj
  exact conj_vecElt_of_sgn Item812Res5.wreathFacts_A9 (Subtype.ext h0) (Subtype.ext h1)
    (Subtype.ext h2) w

@[expose] def sCode : List ℕ :=
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1]

set_option maxRecDepth 10000 in
theorem sPair_check : pairCheck (sCode, sCode) = true := by
  decide

set_option maxRecDepth 10000 in
theorem sCode_conj : mul6 (mul6 sCode (zCode 0)) sCode = mul6 (zCode 0) (zCode 0) ∧
    mul6 (mul6 sCode (zCode 1)) sCode = mul6 (zCode 1) (zCode 1) ∧
    mul6 (mul6 sCode (zCode 2)) sCode = zCode 2 := by
  decide

@[expose] noncomputable def sH6 : H6 :=
  ofCode (sCode, sCode) sPair_check

theorem sH6_conj (w : Fin 3 → ZMod 3) : sH6 * vecElt zH w * sH6⁻¹ = vecElt zH (sgnV w) := by
  obtain ⟨c0, c1, c2⟩ := sCode_conj
  have hm : ∀ i : Fin 3, mat6 (sH6 * zH i * sH6⁻¹) = dec6 (mul6 (mul6 sCode (zCode i)) sCode) := by
    intro i
    rw [map_mul, map_mul, sH6, mat6_ofCode, mat6_ofCode_inv, mat6_zH, ← dec6_mul6, ← dec6_mul6]
  have hsq : ∀ i : Fin 3, mat6 (zH i ^ 2) = dec6 (mul6 (zCode i) (zCode i)) := by
    intro i
    rw [map_pow, mat6_zH, sq, dec6_mul6]
  refine conj_vecElt_of_sgn wreathFacts_zH ?_ ?_ ?_ w
  · apply mat6_injective
    rw [hm, hsq, c0]
  · apply mat6_injective
    rw [hm, hsq, c1]
  · apply mat6_injective
    rw [hm, mat6_zH, c2]

end Item812Res12

open Item812Res12 in
theorem kF812E27NormIrred_holds :
    ∀ (M : Type) [Group M] [Finite M],
      (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨ Nonempty (M ≃* projSp 3 (GaloisField 2 1))) →
      ∀ E U : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 → U ≤ E →
        Subgroup.normalizer (E : Set M) ≤ Subgroup.normalizer (U : Set M) → U = ⊥ ∨ U = E := by
  intro M _ _ hM E U hE hE27 hUE hN
  have hfi : ∀ {N : Type} [Group N] (e : M ≃* N), Function.Injective e.toMonoidHom :=
    fun e => e.injective
  rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rcases irred_of_model Item812Res5.wreathFacts_A9 Item812Res5.card_wreathW_A9_eq_pow
        Item812Res5.card_wreathW_A9 sA9_conj (Item812Res5.isElemAbelian_map_hom e.toMonoidHom hE)
        (by rw [card_map_of_injective (hfi e), hE27]) (map_mono hUE) (normalizer_map_le e hN)
      with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ (hfi e)).mp h)
    · exact Or.inr (Subgroup.map_injective (hfi e) h)
  · set e' : M ≃* H6 := e.trans sp62Equiv with he'
    rcases irred_of_model wreathFacts_zH Item812Res5.card_wreathW_zH_eq_pow card_wreathW_zH
        sH6_conj (Item812Res5.isElemAbelian_map_hom e'.toMonoidHom hE)
        (by rw [card_map_of_injective (hfi e'), hE27]) (map_mono hUE) (normalizer_map_le e' hN)
      with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ (hfi e')).mp h)
    · exact Or.inr (Subgroup.map_injective (hfi e') h)

namespace Item812Res12

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_subgroupOf {Y E : Subgroup G} (hEY : E ≤ Y) {g : Y}
    (hg : g ∈ Subgroup.normalizer ((E.subgroupOf Y : Subgroup Y) : Set Y)) :
    (g : G) ∈ Subgroup.normalizer (E : Set G) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    have h1 := (hg ⟨x, hEY hx⟩).mp (mem_subgroupOf.mpr hx)
    simpa using mem_subgroupOf.mp h1
  · intro hx
    have hxY : x ∈ Y := by
      have e1 : x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g := by group
      rw [e1]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem g.2) (hEY hx)) g.2
    have h1 := (hg ⟨x, hxY⟩).mpr (mem_subgroupOf.mpr (by simpa using hx))
    exact mem_subgroupOf.mp h1

omit [Finite G] in
theorem mem_normalizer_subgroupOf {Y U : Subgroup G} {g : Y}
    (hg : (g : G) ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer ((U.subgroupOf Y : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro x
  rw [mem_subgroupOf, mem_subgroupOf]
  simpa using hg x

end Item812Res12

end CFSG.RankThree.PartTwo.Sec8
