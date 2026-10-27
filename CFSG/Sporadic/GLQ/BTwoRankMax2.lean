module

public import CFSG.GH74.Filter.Sporadic.BMax2
public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.Sporadic.GLQ

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Pinned CFSG.GH74.Filter
  MulOpposite

section


theorem exists_elem2_five_B_of_max2 :
    ∃ x : Fin 5 → NativeSporadic.B, (∀ k, x k ^ 2 = 1) ∧ (∀ k l, Commute (x k) (x l)) ∧
      ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun k => x k ^ (a k : ℕ)).prod ≠ 1 := by
  have := finite_B
  obtain ⟨β, hβ⟩ : ∃ β : Cbar →* GL (Fin 4370) (ZMod 2), IsExplicitBinary β :=
    ⟨_, betaS_explicit⟩
  obtain ⟨ι, hιinj, hιβ, -⟩ := iota_facts hβ
  obtain ⟨-, -, -, hle⟩ := pinned_B_max2_full_native_centralizer_and_two_part hβ ι hιβ
  set u := uS gSeq ι
  set e : Fin 5 → Sbp := fun k => eS gSeq (max2Five k) with he
  have hy : ∀ k, ∃ x : NativeSporadic.B, ι x = u * e k * u⁻¹ := by
    intro k
    have hmem : e k ∈ Jbar.op :=
      Subgroup.mem_op.2 (Ebar_le_Jbar (eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar _))
    obtain ⟨x, hx⟩ := hle (Subgroup.mem_map_of_mem _ hmem)
    exact ⟨x, by rw [hx]; rfl⟩
  choose x hx using hy
  have h0 : op (gSeq 0) * op (gSeq 0) = 1 := by rw [← op_mul, gSeq_zero_mul_self, op_one]
  have he2 : ∀ k, e k * e k = 1 := by
    intro k
    simp only [he, eS]
    generalize wordS gSeq (basisWord.take (basisLens.getD (max2Five k) 0)) = P
    calc P⁻¹ * op (gSeq 0) * P * (P⁻¹ * op (gSeq 0) * P) =
          P⁻¹ * (op (gSeq 0) * op (gSeq 0)) * P := by
          group
      _ = 1 := by rw [h0, mul_one, inv_mul_cancel]
  have hec : ∀ k l, e k * e l = e l * e k := by
    intro k l
    have h := commutator_eS hβ (max2Five k) (max2Five l)
    rw [gram_max2Five k l, ZMod.val_zero, pow_zero] at h
    calc e k * e l = e l * e k * ((e k)⁻¹ * (e l)⁻¹ * e k * e l) := by group
      _ = e l * e k := by rw [h, mul_one]
  have hsq : ∀ k, x k * x k = 1 := by
    intro k
    apply hιinj
    rw [map_mul, hx, map_one]
    calc u * e k * u⁻¹ * (u * e k * u⁻¹) = u * (e k * e k) * u⁻¹ := by group
      _ = 1 := by rw [he2, mul_one, mul_inv_cancel]
  have hcomm : ∀ k l, x k * x l = x l * x k := by
    intro k l
    apply hιinj
    rw [map_mul, map_mul, hx, hx]
    calc u * e k * u⁻¹ * (u * e l * u⁻¹) = u * (e k * e l) * u⁻¹ := by group
      _ = u * (e l * e k) * u⁻¹ := by rw [hec]
      _ = u * e l * u⁻¹ * (u * e k * u⁻¹) := by group
  have hprod : ∀ a : Fin 5 → Fin 2, ι (List.ofFn fun k => x k ^ (a k : ℕ)).prod =
      MulAut.conj u (List.ofFn fun k => e k ^ (a k : ℕ)).prod := by
    intro a
    rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    simp only [Function.comp_apply, map_pow, hx, MulAut.conj_apply]
  have hE : ∀ a : Fin 5 → Fin 2, (List.ofFn fun k => e k ^ (a k : ℕ)).prod =
      op ((((List.ofFn fun k => eE (max2Five k) ^ (a k : ℕ)).reverse.prod : Ebar)) : Cbar) := by
    intro a
    rw [Subgroup.val_list_prod, MulOpposite.op_list_prod]
    simp only [List.map_reverse, List.reverse_reverse, List.map_map, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    simp only [Function.comp_apply, Subgroup.coe_pow, op_pow, he]
    rfl
  refine ⟨x, fun k => by rw [pow_two]; exact hsq k, fun k l => hcomm k l, ?_⟩
  intro a ha h
  have h1 := congrArg ι h
  rw [hprod, map_one, MulEquiv.map_eq_one_iff, hE, op_eq_one_iff, OneMemClass.coe_eq_one] at h1
  exact psiBar_prod_ne_one hβ a ha h1

theorem b_two_rank_five_of_max2 :
    ∀ (K : Type*) [Group K] [Finite K], Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.B) →
      (∃ A : Subgroup K, CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 32) ∧
        5 ≤ CFSG.pRank 2 K := by
  intro K _ _ hK
  obtain ⟨f⟩ := hK
  obtain ⟨x, hsq, hcomm, hker⟩ := exists_elem2_five_B_of_max2
  obtain ⟨-, -, -, -, hE, hcard⟩ := exists_elemAbelian_two x hsq hcomm hker
  obtain ⟨⟨A, hA, hAc⟩, hr⟩ := transport_elemAbelian_two _ hE hcard f
  exact ⟨⟨A, hA, hAc.trans rfl⟩, hr⟩

end

end CFSG.Sporadic.GLQ
