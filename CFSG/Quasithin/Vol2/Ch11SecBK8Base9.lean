module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def ptA : Option K → K
  | none => 0
  | some _ => 1

@[expose] def ptB : Option K → K
  | none => 1
  | some c => c

@[expose] def natPt (p : Option K) : Subgroup (W6 K) := natSub (ptA p) (ptB p)

theorem ptA_ne_or (p : Option K) : ptA p ≠ 0 ∨ ptB p ≠ 0 := by
  cases p with
  | none => exact Or.inr one_ne_zero
  | some c => exact Or.inl one_ne_zero

theorem exists_smul_of_natSub_eq {a b a' b' : K} (h : natSub a' b' = natSub a b) :
    ∃ c : K, a' = c * a ∧ b' = c * b := by
  have hx : natEmb a' b' (Multiplicative.ofAdd (Pi.single 0 1)) ∈ natSub a b := by
    rw [← h]
    exact ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := mem_natSub.mp hx
  rw [toAdd_natEmb, toAdd_ofAdd] at hu
  refine ⟨u 0, ?_, ?_⟩
  · have := congrFun hu (Sum.inl 0)
    simpa [natVec, mul_comm] using this
  · have := congrFun hu (Sum.inr 0)
    simpa [natVec, mul_comm] using this

theorem natPt_injective : Function.Injective (natPt (K := K)) := by
  intro p p' h
  obtain ⟨c, h1, h2⟩ := exists_smul_of_natSub_eq h.symm
  cases p with
  | none =>
    cases p' with
    | none => rfl
    | some d =>
      simp only [ptA] at h1
      exact absurd h1 (by simp)
  | some d =>
    cases p' with
    | none =>
      simp only [ptA, ptB, mul_one] at h1 h2
      rw [← h1, zero_mul] at h2
      exact absurd h2 one_ne_zero
    | some d' =>
      simp only [ptA, ptB, mul_one] at h1 h2
      rw [← h1, one_mul] at h2
      rw [h2]

theorem exists_map_natPt [Finite K] {x : MulAut (W6 K)} (hx : x ∈ normD K) (p : Option K) :
    ∃ p' : Option K, (natPt p).map x.toMonoidHom = natPt p' := by
  rcases eq_natSub_of_card (isInvD_map hx (natSub_isInv _ _))
    (by rw [card_map_aut]; exact card_natSub (ptA_ne_or p)) with h | ⟨c, h⟩
  · exact ⟨none, h⟩
  · exact ⟨some c, h⟩

@[expose] noncomputable def act [Finite K] (x : ↥(normD K)) (p : Option K) : Option K :=
  Classical.choose (exists_map_natPt x.2 p)

theorem map_natPt_act [Finite K] (x : ↥(normD K)) (p : Option K) :
    (natPt p).map (x : MulAut (W6 K)).toMonoidHom = natPt (act x p) :=
  Classical.choose_spec (exists_map_natPt x.2 p)

theorem act_eq_iff [Finite K] (x : ↥(normD K)) (p p' : Option K) :
    act x p = p' ↔ (natPt p).map (x : MulAut (W6 K)).toMonoidHom = natPt p' := by
  rw [map_natPt_act]
  exact ⟨fun h => h ▸ rfl, fun h => natPt_injective h⟩

theorem act_mul [Finite K] (x y : ↥(normD K)) (p : Option K) : act (x * y) p = act x (act y p) := by
  rw [act_eq_iff, ← map_natPt_act x (act y p), ← map_natPt_act y p, Subgroup.map_map]
  rfl

theorem act_one [Finite K] (p : Option K) : act (1 : ↥(normD K)) p = p := by
  rw [act_eq_iff]
  exact Subgroup.map_id _

theorem act_inv_act [Finite K] (x : ↥(normD K)) (p : Option K) : act x⁻¹ (act x p) = p := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_injective [Finite K] (x : ↥(normD K)) : Function.Injective (act x) := fun p p' h => by
  rw [← act_inv_act x p, h, act_inv_act]

theorem map_natSub_dg [Finite K] (g : GL (Fin 3) K) (a b : K) :
    (natSub a b).map (matAut (dgHom g)).toMonoidHom = natSub a b := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_map_aut])
  rintro _ ⟨y, ⟨u, rfl⟩, rfl⟩
  exact ⟨matAut g u, (matAut_dgHom_natEmb g a b u).symm⟩

theorem act_dg [Finite K] {x : ↥(normD K)} {g : GL (Fin 3) K}
    (hx : (x : MulAut (W6 K)) = matAut (dgHom g)) (p : Option K) : act x p = p := by
  rw [act_eq_iff, hx]
  exact map_natSub_dg g _ _

omit [Field K] in
theorem card_ne_pt [Finite K] (p₀ : Option K) : Nat.card {p : Option K // p ≠ p₀} = Nat.card K := by
  have := Fintype.ofFinite K
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_option,
    Fintype.card_subtype_eq, Nat.card_eq_fintype_card, Nat.add_sub_cancel]

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
