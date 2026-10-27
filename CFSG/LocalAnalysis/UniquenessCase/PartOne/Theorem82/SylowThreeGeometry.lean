module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeFrame
import CFSG.RankThree.PartTwo.Sec11.Item116Coords
import CFSG.LinearAlgebra.F3ConnectedPairingScalar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem axis_le_AA (d : SylowThreeData G) (i : Fin 3) : d.A i ≤ d.AA := by
  rw [d.A_eq_AA_inf_Lf i]
  exact inf_le_left

private structure CoordModel (d : SylowThreeData G) where
  e : Multiplicative (Fin 3 → ZMod 3) ≃* d.AA
  gen : Fin 3 → G
  gen_mem : ∀ i, gen i ∈ d.A i
  gen_zpowers : ∀ i, Subgroup.zpowers (gen i) = d.A i
  gen_pow_three : ∀ i, gen i ^ 3 = 1
  e_single : ∀ i,
    e (Multiplicative.ofAdd (Pi.single i 1)) = ⟨gen i, axis_le_AA d i (gen_mem i)⟩
  e_prod : ∀ v, (e (Multiplicative.ofAdd v) : G) =
    gen 0 ^ (v 0).val * gen 1 ^ (v 1).val * gen 2 ^ (v 2).val

namespace CoordModel

variable {d : SylowThreeData G}

private theorem e_single_val (c : CoordModel d) (i : Fin 3) :
    (c.e (Multiplicative.ofAdd (Pi.single i 1)) : G) = c.gen i :=
  congrArg Subtype.val (c.e_single i)

end CoordModel

private theorem exists_coordModel (d : SylowThreeData G) : Nonempty (CoordModel d) := by
  classical
  have hgen : ∀ i : Fin 3, ∃ x ∈ d.A i, Subgroup.zpowers x = d.A i := by
    intro i
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (d.isCyclic_A i)
    refine ⟨(g : d.A i), g.2, ?_⟩
    have hmap : (Subgroup.zpowers g).map (Subgroup.subtype (d.A i)) =
        Subgroup.zpowers ((g : d.A i) : G) := MonoidHom.map_zpowers _ _
    rw [hg, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  choose gen gen_mem gen_zpowers using hgen
  have hclosure : Subgroup.closure ({gen 0, gen 1, gen 2} : Set G) = d.AA := by
    rw [d.AA_def, ← gen_zpowers 0, ← gen_zpowers 1, ← gen_zpowers 2]
    rw [show ({gen 0, gen 1, gen 2} : Set G) = ({gen 0} ∪ {gen 1}) ∪ {gen 2} by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto]
    rw [Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcomm : ∀ u ∈ d.AA, ∀ v ∈ d.AA, u * v = v * u := by
    intro u hu v hv
    exact d.S_commute u v (d.AA_le_S hu) (d.AA_le_S hv)
  have hexp : ∀ u ∈ d.AA, u ^ 3 = 1 := by
    intro u hu
    exact d.isElemAbelian_AA.2 u hu
  obtain ⟨e, he0, he1, he2, hprod⟩ :=
    CFSG.RankThree.PartTwo.Sec11.exists_coords_triple (A := d.AA) hcomm hexp d.card_AA
      (x := gen 0) (y := gen 1) (z := gen 2)
      (axis_le_AA d 0 (gen_mem 0)) (axis_le_AA d 1 (gen_mem 1))
      (axis_le_AA d 2 (gen_mem 2)) hclosure
  have hmem0 : gen 0 ∈ d.A 0 := gen_mem 0
  have hmem1 : gen 1 ∈ d.A 1 := gen_mem 1
  have hmem2 : gen 2 ∈ d.A 2 := gen_mem 2
  have hpow : ∀ i, gen i ^ 3 = 1 := by
    intro i
    exact ((d.mem_A_iff i).mp (gen_mem i)).2
  exact ⟨{
    e := e
    gen := gen
    gen_mem := gen_mem
    gen_zpowers := gen_zpowers
    gen_pow_three := hpow
    e_single := by
      intro i
      fin_cases i
      · simpa using he0
      · simpa using he1
      · simpa using he2
    e_prod := hprod }⟩

private def eps (b : Fin 2) : ZMod 3 := if b = 0 then 1 else -1

private def v (t : Fin 2 × Fin 2) : Fin 3 → ZMod 3 := ![1, eps t.1, eps t.2]

private theorem eps_zero : eps 0 = 1 := by decide

private theorem eps_one : eps 1 = -1 := by decide

private theorem eps_ne_zero (b : Fin 2) : eps b ≠ 0 := by
  fin_cases b <;> decide

private theorem eps_eq_one_or_neg_one (b : Fin 2) : eps b = 1 ∨ eps b = -1 := by
  fin_cases b <;> decide

private theorem eps_injective : Function.Injective eps := by
  decide

private theorem eps_succ (b : Fin 2) : eps (b + 1) = -eps b := by
  fin_cases b <;> decide

private theorem v_zero (t : Fin 2 × Fin 2) : v t 0 = 1 := rfl

private theorem v_one (t : Fin 2 × Fin 2) : v t 1 = eps t.1 := rfl

private theorem v_two (t : Fin 2 × Fin 2) : v t 2 = eps t.2 := rfl

private theorem v_ne_zero (t : Fin 2 × Fin 2) : v t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [v_zero] at h0
  exact one_ne_zero h0

private theorem v_coord_ne_zero (t : Fin 2 × Fin 2) (j : Fin 3) : v t j ≠ 0 := by
  fin_cases j <;> simp [v, eps_ne_zero]

private theorem v_eq_one_or_neg_one (t : Fin 2 × Fin 2) (j : Fin 3) :
    v t j = 1 ∨ v t j = -1 := by
  fin_cases j <;> simp [v, eps_eq_one_or_neg_one]

private theorem v_injective : Function.Injective v := by
  intro t u h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rw [v_one, v_one] at h1
  rw [v_two, v_two] at h2
  exact Prod.ext (eps_injective h1) (eps_injective h2)

private theorem eq_add_one_of_ne (a b : Fin 2) (h : a ≠ b) : a + 1 = b := by
  fin_cases a <;> fin_cases b <;> simp_all

private theorem axis_eq_zpowers {d : SylowThreeData G} (c : CoordModel d) (i : Fin 3) :
    (d.A i).subgroupOf d.AA =
      Subgroup.zpowers (c.e (Multiplicative.ofAdd (Pi.single i 1))) := by
  rw [← Subgroup.map_subtype_inj]
  rw [Subgroup.map_subgroupOf_eq_of_le (axis_le_AA d i)]
  rw [MonoidHom.map_zpowers]
  change d.A i = Subgroup.zpowers
    ((c.e (Multiplicative.ofAdd (Pi.single i 1)) : d.AA) : G)
  rw [c.e_single_val i, c.gen_zpowers i]

private theorem exists_smul_of_mem_zpowers {d : SylowThreeData G} (c : CoordModel d)
    {w v : Fin 3 → ZMod 3}
    (h : c.e (Multiplicative.ofAdd w) ∈
      Subgroup.zpowers (c.e (Multiplicative.ofAdd v))) :
    ∃ m : ℤ, w = m • v := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hpow : (c.e (Multiplicative.ofAdd v)) ^ m =
      c.e (Multiplicative.ofAdd (m • v)) := by
    rw [← map_zpow, ofAdd_zsmul]
  have heq : c.e (Multiplicative.ofAdd (m • v)) = c.e (Multiplicative.ofAdd w) :=
    hpow.symm.trans hm
  exact ⟨m, Multiplicative.ofAdd.injective (c.e.injective heq.symm)⟩

private theorem fin_three_eq_or (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (l : Fin 3) : l = i ∨ l = j ∨ l = k := by
  decide +revert

private theorem mem_plane_zpowers_iff {d : SylowThreeData G} (c : CoordModel d)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w : Fin 3 → ZMod 3) :
    c.e (Multiplicative.ofAdd w) ∈
        Subgroup.zpowers (c.e (Multiplicative.ofAdd (Pi.single i 1))) ⊔
        Subgroup.zpowers (c.e (Multiplicative.ofAdd (Pi.single j 1))) ↔ w k = 0 := by
  let _ : CommGroup ↥d.AA :=
    { (inferInstance : Group ↥d.AA) with
      mul_comm := fun a b => Subtype.ext
        (d.S_commute a b (d.AA_le_S a.2) (d.AA_le_S b.2)) }
  have hki : k ≠ i := fun h => hik h.symm
  have hkj : k ≠ j := fun h => hjk h.symm
  constructor
  · intro hmem
    have hmem' : ∃ x ∈ Subgroup.zpowers
          (c.e (Multiplicative.ofAdd (Pi.single i 1))),
        ∃ y ∈ Subgroup.zpowers (c.e (Multiplicative.ofAdd (Pi.single j 1))),
          x * y = c.e (Multiplicative.ofAdd w) :=
      (Subgroup.mem_sup
        (s := Subgroup.zpowers (c.e (Multiplicative.ofAdd (Pi.single i 1))))
        (t := Subgroup.zpowers (c.e (Multiplicative.ofAdd (Pi.single j 1))))).mp hmem
    obtain ⟨x, hx, y, hy, hxy⟩ := hmem'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hx' : x = c.e (Multiplicative.ofAdd (m • Pi.single i 1)) := by
      rw [← hm, ← map_zpow, ofAdd_zsmul]
    have hy' : y = c.e (Multiplicative.ofAdd (n • Pi.single j 1)) := by
      rw [← hn, ← map_zpow, ofAdd_zsmul]
    have heq : c.e (Multiplicative.ofAdd w) =
        c.e (Multiplicative.ofAdd
          (m • Pi.single i 1 + n • Pi.single j 1)) := by
      rw [← hxy, hx', hy', ← map_mul, ← ofAdd_add]
    have hvec : w = m • Pi.single i 1 + n • Pi.single j 1 :=
      Multiplicative.ofAdd.injective (c.e.injective heq)
    rw [hvec]
    simp [Pi.add_apply, hki, hkj]
  · intro hk
    have hvec : w = (w i) • Pi.single i 1 + (w j) • Pi.single j 1 := by
      funext l
      rcases fin_three_eq_or i j k hij hik hjk l with rfl | rfl | rfl
      · simp [Pi.add_apply, Pi.smul_apply, hij]
      · simp [Pi.add_apply, Pi.smul_apply, hij]
      · simp [Pi.add_apply, Pi.smul_apply, hki, hkj, hk]
    have hsmul (a : ZMod 3) : a • (Pi.single i 1 : Fin 3 → ZMod 3) =
        a.val • (Pi.single i 1 : Fin 3 → ZMod 3) := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) a.val (Pi.single i 1),
        ZMod.natCast_zmod_val]
    have hsmul' (a : ZMod 3) : a • (Pi.single j 1 : Fin 3 → ZMod 3) =
        a.val • (Pi.single j 1 : Fin 3 → ZMod 3) := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) a.val (Pi.single j 1),
        ZMod.natCast_zmod_val]
    rw [hvec, hsmul, hsmul', ofAdd_add, map_mul]
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [ofAdd_nsmul, map_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [ofAdd_nsmul, map_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

private theorem mem_plane_iff {d : SylowThreeData G} (c : CoordModel d)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w : Fin 3 → ZMod 3) :
    c.e (Multiplicative.ofAdd w) ∈
        (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA ↔ w k = 0 := by
  rw [axis_eq_zpowers c i, axis_eq_zpowers c j]
  exact mem_plane_zpowers_iff c hij hik hjk w

theorem exists_axis_coordinates {G : Type} [Group G] [Finite G]
    (d : SylowThreeData G) :
    ∃ e : Multiplicative (Fin 3 → ZMod 3) ≃* d.AA,
      (∀ i : Fin 3, (d.A i).subgroupOf d.AA =
        Subgroup.zpowers (e (Multiplicative.ofAdd (Pi.single i 1)))) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        ∀ v : Fin 3 → ZMod 3,
          e (Multiplicative.ofAdd v) ∈
              (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA ↔ v k = 0) := by
  obtain ⟨c⟩ := exists_coordModel d
  refine ⟨c.e, (fun i => axis_eq_zpowers c i), ?_⟩
  intro i j k hij hik hjk v
  exact mem_plane_iff c hij hik hjk v

private theorem exists_fin_three_ne_ne (i j : Fin 3) (hij : i ≠ j) :
    ∃ k, k ≠ i ∧ k ≠ j := by
  decide +revert

private noncomputable def line {d : SylowThreeData G} (c : CoordModel d) (t : Fin 2 × Fin 2) :
    Subgroup d.AA :=
  Subgroup.zpowers (c.e (Multiplicative.ofAdd (v t)))

private theorem line_card {d : SylowThreeData G} (c : CoordModel d)
    (t : Fin 2 × Fin 2) : Nat.card (line c t) = 3 := by
  rw [line, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · have hcube : ((c.e (Multiplicative.ofAdd (v t)) : d.AA) : G) ^ 3 = 1 :=
      d.isElemAbelian_AA.2 _ (c.e (Multiplicative.ofAdd (v t))).2
    exact Subtype.ext (by simpa using hcube)
  · intro h
    have h1 : Multiplicative.ofAdd (v t) = 1 := c.e.injective (by simpa using h)
    exact v_ne_zero t (Multiplicative.ofAdd.injective (by simpa using h1))

private theorem line_injective {d : SylowThreeData G} (c : CoordModel d) :
    Function.Injective (line c) := by
  intro t u h
  have h' : Subgroup.zpowers (c.e (Multiplicative.ofAdd (v t))) =
      Subgroup.zpowers (c.e (Multiplicative.ofAdd (v u))) := by
    simpa [line] using h
  have hmem : c.e (Multiplicative.ofAdd (v u)) ∈
      Subgroup.zpowers (c.e (Multiplicative.ofAdd (v t))) := by
    rw [h']
    exact Subgroup.mem_zpowers _
  obtain ⟨m, hm⟩ := exists_smul_of_mem_zpowers c hmem
  have hm0 : (m : ZMod 3) = 1 := by
    have h0 := congrFun hm 0
    simp [v] at h0
    exact h0.symm
  apply v_injective
  funext j
  have hj := congrFun hm j
  simp [Pi.smul_apply] at hj
  rw [hm0, one_mul] at hj
  exact hj.symm

private theorem line_not_in_plane {d : SylowThreeData G} (c : CoordModel d)
    (t : Fin 2 × Fin 2) {i j : Fin 3} (hij : i ≠ j) :
    ¬ line c t ≤ (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA := by
  intro hle
  have hmem : c.e (Multiplicative.ofAdd (v t)) ∈
      (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA :=
    hle (Subgroup.mem_zpowers _)
  obtain ⟨k, hki, hkj⟩ := exists_fin_three_ne_ne i j hij
  exact v_coord_ne_zero t k
    ((mem_plane_iff c hij (fun h => hki h.symm) (fun h => hkj h.symm) (v t)).mp hmem)

private theorem axis_injective {d : SylowThreeData G} (c : CoordModel d) :
    Function.Injective (fun i : Fin 3 => (d.A i).subgroupOf d.AA) := by
  intro i j hij
  by_contra hne
  have hmem' : c.e (Multiplicative.ofAdd (Pi.single j 1)) ∈
      (d.A j).subgroupOf d.AA := by
    rw [axis_eq_zpowers c j]
    exact Subgroup.mem_zpowers _
  have hmem'' : c.e (Multiplicative.ofAdd (Pi.single j 1)) ∈
      (d.A i).subgroupOf d.AA := by
    simpa [hij] using hmem'
  have hmem : c.e (Multiplicative.ofAdd (Pi.single j 1)) ∈
      Subgroup.zpowers (c.e (Multiplicative.ofAdd (Pi.single i 1))) := by
    rw [← axis_eq_zpowers c i]
    exact hmem''
  obtain ⟨m, hm⟩ := exists_smul_of_mem_zpowers c hmem
  have hcoord := congrFun hm j
  simp [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at hcoord

private theorem val_neg_one_zmod3 : ((-1 : ZMod 3)).val = 2 := by decide

private theorem neg_one_ne_one_zmod_three : (-1 : ZMod 3) ≠ 1 := by decide

private theorem conj_apply_of_sign {d : SylowThreeData G} (c : CoordModel d) {l : G}
    (hlN : l ∈ Subgroup.normalizer (d.AA : Set G)) {i : Fin 3}
    (hsign : ∀ j, ∀ a ∈ d.A j, l * a * l⁻¹ = if j = i then a⁻¹ else a)
    (w : Fin 3 → ZMod 3) (hw : ∀ j, w j = 1 ∨ w j = -1) :
    (⟨l * (c.e (Multiplicative.ofAdd w) : G) * l⁻¹,
        ((Subgroup.mem_normalizer_iff.mp hlN (c.e (Multiplicative.ofAdd w))).mp
          (c.e (Multiplicative.ofAdd w)).2)⟩ : d.AA) =
      c.e (Multiplicative.ofAdd (fun j => if j = i then -w j else w j)) := by
  apply Subtype.ext
  have hfac (j : Fin 3) :
      (MulAut.conj l) (c.gen j ^ (w j).val) =
        c.gen j ^ ((if j = i then -w j else w j)).val := by
    have hinv : (c.gen j)⁻¹ = (c.gen j) ^ 2 := by
      have hsq : (c.gen j) ^ 2 * c.gen j = 1 := by
        rw [← pow_succ, show 2 + 1 = 3 by norm_num, c.gen_pow_three j]
      exact (mul_eq_one_iff_eq_inv.mp hsq).symm
    have hinv2 : (c.gen j)⁻¹ ^ 2 = c.gen j := by
      rw [hinv, ← pow_mul]
      rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, c.gen_pow_three j, one_mul, pow_one]
    calc (MulAut.conj l) (c.gen j ^ (w j).val)
        = ((MulAut.conj l) (c.gen j)) ^ (w j).val := map_pow _ _ _
      _ = (if j = i then (c.gen j)⁻¹ else c.gen j) ^ (w j).val := by
            rw [MulAut.conj_apply, hsign j (c.gen j) (c.gen_mem j)]
      _ = c.gen j ^ ((if j = i then -w j else w j)).val := by
            by_cases hji : j = i
            · subst hji
              rw [if_pos rfl, if_pos rfl]
              rcases hw j with h | h
              · have hwj : (w j).val = 1 := by rw [h]; decide
                rw [hwj, h, val_neg_one_zmod3]
                simpa using hinv
              · have hwj : (w j).val = 2 := by rw [h]; decide
                rw [hwj, h]
                have hval : ((-(-1) : ZMod 3)).val = 1 := by decide
                rw [hval, pow_one]
                exact hinv2
            · rw [if_neg hji, if_neg hji]
  have hconj : l * (c.e (Multiplicative.ofAdd w) : G) * l⁻¹ =
      (MulAut.conj l) (c.gen 0 ^ (w 0).val * c.gen 1 ^ (w 1).val *
        c.gen 2 ^ (w 2).val) := by
    rw [c.e_prod w, MulAut.conj_apply]
  calc l * (c.e (Multiplicative.ofAdd w) : G) * l⁻¹
      = (MulAut.conj l) (c.gen 0 ^ (w 0).val * c.gen 1 ^ (w 1).val *
          c.gen 2 ^ (w 2).val) := hconj
    _ = (MulAut.conj l) (c.gen 0 ^ (w 0).val) *
          (MulAut.conj l) (c.gen 1 ^ (w 1).val) *
          (MulAut.conj l) (c.gen 2 ^ (w 2).val) := by
        rw [map_mul, map_mul]
    _ = c.gen 0 ^ ((if (0 : Fin 3) = i then -w 0 else w 0)).val *
          c.gen 1 ^ ((if (1 : Fin 3) = i then -w 1 else w 1)).val *
          c.gen 2 ^ ((if (2 : Fin 3) = i then -w 2 else w 2)).val := by
        rw [hfac 0, hfac 1, hfac 2]
    _ = (c.e (Multiplicative.ofAdd (fun j => if j = i then -w j else w j)) : G) :=
        (c.e_prod (fun j => if j = i then -w j else w j)).symm

private def flipAt (i : Fin 3) (t : Fin 2 × Fin 2) : Fin 2 × Fin 2 :=
  if i = 1 then (t.1 + 1, t.2) else if i = 2 then (t.1, t.2 + 1) else t

private theorem v_flipAt (i : Fin 3) (hi : i = 1 ∨ i = 2) (t : Fin 2 × Fin 2) :
    v (flipAt i t) = fun j => if j = i then -v t j else v t j := by
  rcases hi with rfl | rfl
  · funext j
    fin_cases j <;> simp [flipAt, v, eps_succ]
  · funext j
    fin_cases j <;> simp [flipAt, v, eps_succ]

private theorem line_map_sign {d : SylowThreeData G} (c : CoordModel d) {l : G}
    (hlN : l ∈ Subgroup.normalizer (d.AA : Set G)) {i : Fin 3}
    (hi : i = 1 ∨ i = 2)
    (hsign : ∀ j, ∀ a ∈ d.A j, l * a * l⁻¹ = if j = i then a⁻¹ else a)
    (t : Fin 2 × Fin 2) :
    (line c t).map
        ((d.AA.normalizerMonoidHom ⟨l, hlN⟩).toMonoidHom) = line c (flipAt i t) := by
  rw [line, MonoidHom.map_zpowers, line]
  rw [v_flipAt i hi t]
  congr 1
  exact conj_apply_of_sign c hlN hsign (v t) (v_eq_one_or_neg_one t)

private theorem exists_fin_three_pair_ne (k : Fin 3) :
    ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  decide +revert

private theorem line_mem_iff {d : SylowThreeData G} (c : CoordModel d)
    (B : Subgroup d.AA) :
    (∃ t : Fin 2 × Fin 2, line c t = B) ↔
      Nat.card B = 3 ∧
        ∀ i j : Fin 3, i ≠ j →
          ¬ B ≤ (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨line_card c t, fun i j hij => line_not_in_plane c t hij⟩
  · rintro ⟨hB3, hno⟩
    have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hBne : B ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hB3
      norm_num at hB3
    have hBgt : 1 < Nat.card B := by rw [hB3]; norm_num
    have _ : Nontrivial ↥B := Finite.one_lt_card_iff_nontrivial.mp hBgt
    obtain ⟨b, hb_ne⟩ := exists_ne (1 : ↥B)
    have hgenB : Subgroup.zpowers b = ⊤ :=
      zpowers_eq_top_of_prime_card hB3 hb_ne
    obtain ⟨vv, hvv⟩ := c.e.surjective (b : d.AA)
    let w : Fin 3 → ZMod 3 := Multiplicative.toAdd vv
    have hw : c.e (Multiplicative.ofAdd w) = (b : d.AA) := by
      simpa [w] using hvv
    have hBzp : B = Subgroup.zpowers (c.e (Multiplicative.ofAdd w)) := by
      rw [hw]
      have hmap := MonoidHom.map_zpowers (Subgroup.subtype B) b
      rw [hgenB, Subgroup.map_top, Subgroup.range_subtype] at hmap
      exact hmap
    have hw_ne : w ≠ 0 := by
      intro h0
      have hb1 : (b : d.AA) = 1 := by
        rw [← hw, h0]
        simp
      exact hb_ne (Subtype.ext hb1)
    have hwnz : ∀ k, w k ≠ 0 := by
      intro k hk
      obtain ⟨i, j, hij, hik, hjk⟩ := exists_fin_three_pair_ne k
      have hmem : c.e (Multiplicative.ofAdd w) ∈
          (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA :=
        (mem_plane_iff c hij hik hjk w).mpr hk
      have hle : B ≤ (d.A i).subgroupOf d.AA ⊔ (d.A j).subgroupOf d.AA := by
        rw [hBzp]
        exact Subgroup.zpowers_le.mpr hmem
      exact hno i j hij hle
    have hw0 : w 0 = 1 ∨ w 0 = -1 := CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one _ (hwnz 0)
    let w' : Fin 3 → ZMod 3 := if w 0 = 1 then w else -w
    have hw'0 : w' 0 = 1 := by
      by_cases h : w 0 = 1
      · simp [w', h]
      · have hw'eq : w' = -w := by simp [w', h]
        rw [hw'eq, Pi.neg_apply, hw0.resolve_left h]
        exact neg_neg 1
    have hw'nz : ∀ k, w' k ≠ 0 := by
      intro k
      by_cases h : w 0 = 1
      · simpa [w', h] using hwnz k
      · have hw'eq : w' = -w := by simp [w', h]
        rw [hw'eq, Pi.neg_apply]
        exact neg_ne_zero.mpr (hwnz k)
    have hBzp' : B = Subgroup.zpowers (c.e (Multiplicative.ofAdd w')) := by
      by_cases h : w 0 = 1
      · simp [w', h, hBzp]
      · have hw'eq : w' = -w := by simp [w', h]
        have hgen : c.e (Multiplicative.ofAdd w') =
            (c.e (Multiplicative.ofAdd w))⁻¹ := by
          rw [hw'eq, ofAdd_neg]
          exact map_inv c.e.toMonoidHom (Multiplicative.ofAdd w)
        rw [hBzp, hgen]
        exact (Subgroup.zpowers_inv (g := c.e (Multiplicative.ofAdd w))).symm
    have hw'1 : w' 1 = 1 ∨ w' 1 = -1 := CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one _ (hw'nz 1)
    have hw'2 : w' 2 = 1 ∨ w' 2 = -1 := CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one _ (hw'nz 2)
    let t : Fin 2 × Fin 2 :=
      (if w' 1 = 1 then 0 else 1, if w' 2 = 1 then 0 else 1)
    have hvt : v t = w' := by
      funext j
      fin_cases j
      · simp [v, hw'0]
      · by_cases h : w' 1 = 1
        · simp [v, t, h, eps_zero]
        · have hneg : w' 1 = -1 := hw'1.resolve_left h
          simp [v, t, hneg, neg_one_ne_one_zmod_three, eps_one]
      · by_cases h : w' 2 = 1
        · simp [v, t, h, eps_zero]
        · have hneg : w' 2 = -1 := hw'2.resolve_left h
          simp [v, t, hneg, neg_one_ne_one_zmod_three, eps_one]
    exact ⟨t, by rw [line, hvt]; exact hBzp'.symm⟩

private theorem flipAt_one_eq (t u : Fin 2 × Fin 2) (h1 : t.1 ≠ u.1) (h2 : t.2 = u.2) :
    flipAt 1 t = u := by
  simp only [flipAt, if_true]
  exact Prod.ext (eq_add_one_of_ne t.1 u.1 h1) h2

private theorem flipAt_two_eq (t u : Fin 2 × Fin 2) (h1 : t.1 = u.1) (h2 : t.2 ≠ u.2) :
    flipAt 2 t = u := by
  simp only [flipAt, if_true]
  exact Prod.ext h1 (eq_add_one_of_ne t.2 u.2 h2)

private theorem flipAt_one_two_eq (t u : Fin 2 × Fin 2) (h1 : t.1 ≠ u.1) (h2 : t.2 ≠ u.2) :
    flipAt 1 (flipAt 2 t) = u := by
  simp only [flipAt, if_true]
  exact Prod.ext (eq_add_one_of_ne t.1 u.1 h1) (eq_add_one_of_ne t.2 u.2 h2)

private theorem normalizer_map_mul {d : SylowThreeData G} (B : Subgroup d.AA)
    (n1 n2 : Subgroup.normalizer (d.AA : Set G)) :
    B.map ((d.AA.normalizerMonoidHom (n1 * n2)).toMonoidHom) =
      (B.map ((d.AA.normalizerMonoidHom n2).toMonoidHom)).map
        ((d.AA.normalizerMonoidHom n1).toMonoidHom) := by
  rw [map_mul, Subgroup.map_map]
  congr 1

theorem exists_four_full_support_lines {G : Type} [Group G] [Finite G]
    (d : SylowThreeData G) :
    let a : Fin 3 → Subgroup d.AA := fun i => (d.A i).subgroupOf d.AA
    Function.Injective a ∧
    ∃ F : Finset (Subgroup d.AA),
      F.card = 4 ∧
      (∀ B, B ∈ F ↔ Nat.card B = 3 ∧
        ∀ i j, i ≠ j → ¬ B ≤ a i ⊔ a j) ∧
      (∀ i, a i ∉ F) ∧
      (∀ B ∈ F, ∀ C ∈ F,
        ∃ l : Subgroup.normalizer (d.AA : Set G),
          (l : G) ∈ d.L ∧
          B.map (d.AA.normalizerMonoidHom l).toMonoidHom = C) := by
  classical
  obtain ⟨c⟩ := exists_coordModel d
  let a : Fin 3 → Subgroup d.AA := fun i => (d.A i).subgroupOf d.AA
  let F : Finset (Subgroup d.AA) := Finset.univ.image (line c)
  have ha : Function.Injective a := axis_injective c
  have hFcard : F.card = 4 := by
    rw [show F = Finset.univ.image (line c) from rfl,
      Finset.card_image_of_injective _ (line_injective c)]
    simp
  have hFmem : ∀ B, B ∈ F ↔ ∃ t : Fin 2 × Fin 2, line c t = B := by
    intro B
    simp [F, Finset.mem_image]
  have hFchar : ∀ B, B ∈ F ↔ Nat.card B = 3 ∧
      ∀ i j : Fin 3, i ≠ j → ¬ B ≤ a i ⊔ a j := by
    intro B
    rw [hFmem B]
    exact line_mem_iff c B
  have hdisj : ∀ i, a i ∉ F := by
    intro i hi
    obtain ⟨-, hno⟩ := (hFchar (a i)).mp hi
    obtain ⟨j, hji⟩ := exists_ne i
    exact hno i j (fun h => hji h.symm) le_sup_left
  obtain ⟨l1, hl1L, hl1N, hl1sign⟩ := d.exists_sign_in_product 1
  obtain ⟨l2, hl2L, hl2N, hl2sign⟩ := d.exists_sign_in_product 2
  have htrans : ∀ B ∈ F, ∀ C ∈ F,
      ∃ l : Subgroup.normalizer (d.AA : Set G),
        (l : G) ∈ d.L ∧
        B.map (d.AA.normalizerMonoidHom l).toMonoidHom = C := by
    intro B hB C hC
    obtain ⟨t, rfl⟩ := (hFmem B).mp hB
    obtain ⟨u, rfl⟩ := (hFmem C).mp hC
    by_cases h1 : t.1 = u.1
    · by_cases h2 : t.2 = u.2
      · have htu : t = u := Prod.ext h1 h2
        subst htu
        refine ⟨1, d.L.one_mem, ?_⟩
        have hone : (d.AA.normalizerMonoidHom
            (1 : Subgroup.normalizer (d.AA : Set G))).toMonoidHom = MonoidHom.id d.AA := by
          refine MonoidHom.ext fun x => ?_
          apply Subtype.ext
          change ((d.AA.normalizerMonoidHom
            (1 : Subgroup.normalizer (d.AA : Set G))) x : G) = (x : G)
          rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
          simp
        rw [hone, Subgroup.map_id]
      · refine ⟨⟨l2, hl2N⟩, hl2L, ?_⟩
        rw [line_map_sign c hl2N (Or.inr rfl) hl2sign t,
          flipAt_two_eq t u h1 h2]
    · by_cases h2 : t.2 = u.2
      · refine ⟨⟨l1, hl1N⟩, hl1L, ?_⟩
        rw [line_map_sign c hl1N (Or.inl rfl) hl1sign t,
          flipAt_one_eq t u h1 h2]
      · let n1 : Subgroup.normalizer (d.AA : Set G) := ⟨l1, hl1N⟩
        let n2 : Subgroup.normalizer (d.AA : Set G) := ⟨l2, hl2N⟩
        refine ⟨n1 * n2, d.L.mul_mem hl1L hl2L, ?_⟩
        rw [normalizer_map_mul (line c t) n1 n2,
            line_map_sign c hl2N (Or.inr rfl) hl2sign t,
            line_map_sign c hl1N (Or.inl rfl) hl1sign (flipAt 2 t),
            flipAt_one_two_eq t u h1 h2]
  exact ⟨ha, F, hFcard, hFchar, hdisj, htrans⟩

