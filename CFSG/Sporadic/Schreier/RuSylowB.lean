module

public import CFSG.Sporadic.Schreier.RuSylowA

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped commutatorElement

theorem quotient_comm_of_gens {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {X : Set G}
    (hX : Subgroup.closure X = ⊤) (h : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ N) :
    ∀ a b : G ⧸ N, a * b = b * a := by
  set q := QuotientGroup.mk' N
  have hk : (q '' X).Pairwise Commute := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ -
    have h1 : q (x * y * x⁻¹ * y⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 (h x hx y hy)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have htop : Subgroup.closure (q '' X) = ⊤ := by
    rw [← MonoidHom.map_closure, hX,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hcomm := Subgroup.isMulCommutative_closure hk
  intro a b
  have ha : a ∈ Subgroup.closure (q '' X) := htop ▸ Subgroup.mem_top a
  have hb : b ∈ Subgroup.closure (q '' X) := htop ▸ Subgroup.mem_top b
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem commutator_le_of_quotient_comm {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (h : ∀ a b : G ⧸ N, a * b = b * a) : commutator G ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff (N := N)]
  have hab := h (a : G ⧸ N) (b : G ⧸ N)
  simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hab]
  group

theorem sq_eq_one_of_gens {Q : Type*} [Group Q] (hcomm : ∀ a b : Q, a * b = b * a) {X : Set Q}
    (hX : Subgroup.closure X = ⊤) (h : ∀ x ∈ X, x ^ 2 = 1) : ∀ q : Q, q ^ 2 = 1 := by
  intro q
  have hq : q ∈ Subgroup.closure X := hX ▸ Subgroup.mem_top q
  induction hq using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => exact one_pow 2
  | mul x y _ _ hx hy => rw [(Commute.mul_pow (hcomm x y) 2), hx, hy, one_mul]
  | inv x _ hx => rw [inv_pow, hx, inv_one]

@[expose] def ruSGenSet : Set ruS := Subtype.val ⁻¹' {g | g ∈ ruSGens}

theorem ruSGenSet_closure : Subgroup.closure ruSGenSet = ⊤ := Subgroup.closure_closure_coe_preimage

theorem mem_ruSGenSet {x : ruS} (hx : x ∈ ruSGenSet) : ∃ j < 4, x = ruSGenS j := by
  obtain ⟨j, hj, he⟩ := mem_ruSGens_iff.1 hx
  exact ⟨j, hj, Subtype.ext he.symm⟩

theorem ruSGenS_mem (j : ℕ) (hj : j < 4) : ruSGenS j ∈ ruSGenSet :=
  mem_ruSGens_iff.2 ⟨j, hj, rfl⟩

abbrev RuQ :
    Type := ruS ⧸ ruRS

theorem ruQ_comm :
    ∀ a b : RuQ, a * b = b * a := by
  apply quotient_comm_of_gens ruRS ruSGenSet_closure
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := mem_ruSGenSet hx
  obtain ⟨j, hj, rfl⟩ := mem_ruSGenSet hy
  exact Subgroup.mem_subgroupOf.2 (ruS_comm_R hi hj)

theorem commutator_ruS_le :
    commutator ruS ≤ ruRS :=
  commutator_le_of_quotient_comm ruRS ruQ_comm

theorem ruQ_sq :
    ∀ q : RuQ, q ^ 2 = 1 := by
  apply sq_eq_one_of_gens ruQ_comm (X := (QuotientGroup.mk' ruRS) '' ruSGenSet)
  · rw [← MonoidHom.map_closure, ruSGenSet_closure,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_ruSGenSet hx
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, pow_two]
    exact Subgroup.mem_subgroupOf.2 (ruS_sq_R hj)

theorem evalSigned_four (g : List (Equiv.Perm (Fin 4060))) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    evalSigned g [-a, -b, a, b] = ⁅(g.getD (a.natAbs - 1) 1)⁻¹, (g.getD (b.natAbs - 1) 1)⁻¹⁆ := by
  have h1 : ¬ (0 < -a) := by omega
  have h2 : ¬ (0 < -b) := by omega
  simp only [evalSigned, h1, h2, ha, hb, ↓reduceIte, Int.natAbs_neg, commutatorElement_def,
    inv_inv, mul_one, mul_assoc]

theorem ruRGens_mem_comm : ∀ g ∈ ruRGens, g ∈ ⁅ruS, ruS⁆ := by
  intro g hg
  have hs : ∀ k, ruSGens.getD k 1 ∈ ruS := ruSGens_getD_mem
  have hc : ∀ a b, 0 < a → 0 < b → evalSigned ruSGens [-a, -b, a, b] ∈ ⁅ruS, ruS⁆ := by
    intro a b ha hb
    rw [evalSigned_four _ a b ha hb]
    exact Subgroup.commutator_mem_commutator (ruS.inv_mem (hs _)) (ruS.inv_mem (hs _))
  simp only [ruRGens, ruRWords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact hc 1 3 (by norm_num) (by norm_num)
  · exact hc 1 4 (by norm_num) (by norm_num)
  · exact hc 2 4 (by norm_num) (by norm_num)
  · exact hc 3 4 (by norm_num) (by norm_num)
  · set c := ruSGens.getD 2 1
    have e0 : evalSigned ruSGens [-3, -1, -4, 1, 4, 3] =
        c⁻¹ * ((ruSGens.getD 0 1)⁻¹ * ((ruSGens.getD 3 1)⁻¹ * (ruSGens.getD 0 1 *
          (ruSGens.getD 3 1 * (c * 1))))) := rfl
    have e : evalSigned ruSGens [-3, -1, -4, 1, 4, 3] =
        ⁅c⁻¹ * (ruSGens.getD 0 1)⁻¹ * c, c⁻¹ * (ruSGens.getD 3 1)⁻¹ * c⁆ := by
      rw [e0, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator
      (ruS.mul_mem (ruS.mul_mem (ruS.inv_mem (hs 2)) (ruS.inv_mem (hs 0))) (hs 2))
      (ruS.mul_mem (ruS.mul_mem (ruS.inv_mem (hs 2)) (ruS.inv_mem (hs 3))) (hs 2))

theorem map_commutator_subtype (H : Subgroup (Equiv.Perm (Fin 4060))) :
    (commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem ruR_eq_commutator :
    ruR = ⁅ruS, ruS⁆ := by
  apply le_antisymm
  · exact closure_list_le ruRGens_mem_comm
  · rw [← map_commutator_subtype]
    calc (commutator ruS).map ruS.subtype ≤ ruRS.map ruS.subtype := Subgroup.map_mono
          commutator_ruS_le
      _ = ruR ⊓ ruS := Subgroup.subgroupOf_map_subtype _ _
      _ ≤ ruR := inf_le_left

theorem ruRS_eq_commutator :
    ruRS = commutator ruS := by
  apply le_antisymm _ commutator_ruS_le
  intro x hx
  have h1 : (x : Equiv.Perm (Fin 4060)) ∈ ⁅ruS, ruS⁆ :=
    ruR_eq_commutator ▸ Subgroup.mem_subgroupOf.1 hx
  rw [← map_commutator_subtype] at h1
  obtain ⟨y, hy, hxy⟩ := h1
  rw [show x = y from Subtype.ext hxy.symm]
  exact hy

end CFSG.Sporadic.RuSchreier
