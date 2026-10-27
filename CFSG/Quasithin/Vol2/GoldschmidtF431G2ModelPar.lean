module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam

public noncomputable section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair

section Generic

variable {X : Type*} [Group X] {n : ℕ} (R : RankTwoSystem X n)

theorem eq_P_of_lifts {M : Subgroup X} (hBM : R.B ≤ M) (b : Bool) (m₁ m₂ : R.N)
    (h₁ : (m₁ : R.Weyl) = gen R.w₁ R.w₂ b) (h₂ : (m₂ : R.Weyl) = gen R.w₁ R.w₂ (!b))
    (hm₁ : (m₁ : X) ∈ M) (hm₂ : (m₂ : X) ∉ M) : M = P R b := by
  rcases eq_B_or_P_or_top R hBM with h | ⟨j, h⟩ | h
  · exfalso
    refine R.rank2.not_mem_B_of_mem_dc (R.rank2.gen_mem b) ?_ (h ▸ hm₁)
    have := coe_mem_dc (B := R.B) (N := R.N) m₁
    rwa [h₁] at this
  · by_cases hj : j = b
    · rw [h, hj]
    · exfalso
      have : j = !b := by cases b <;> cases j <;> simp_all
      subst this
      apply hm₂
      rw [h]
      refine (mem_P_iff R).2 (Or.inr ?_)
      have := coe_mem_dc (B := R.B) (N := R.N) m₂
      rwa [h₂] at this
  · exact absurd (h ▸ Subgroup.mem_top _) hm₂

end Generic

end CFSG.Quasithin.H13.F431.BN

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.SP CFSG.GH74.BNPair
  CFSG.Quasithin.H13.F431.BN

section Idx

@[expose] def idx : Bool → Fin Tag.G2.rank
  | true => ⟨1, by decide⟩
  | false => ⟨0, by decide⟩

theorem idx_injective : Function.Injective idx := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [idx] at this)

end Idx

section Main


variable {K : Type} [Field K]

@[expose] def Pmin (K : Type) [Field K] (i : Fin Tag.G2.rank) : Subgroup ↥(adjointGroup .G2 K) :=
  (parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)

theorem B_eq (hK : 3 ≤ Nat.card K) :
    (g2ModelSystem K hK).B =
      ((⨆ i, torus (τ := Tag.G2) K i) ⊔ posUnipotent (g2Datum K)).map (proj K) := by
  rw [Subgroup.map_sup]
  rfl

theorem B_le_map_Pmin (hK : 3 ≤ Nat.card K) (i : Fin Tag.G2.rank) :
    (g2ModelSystem K hK).B ≤ (Pmin K i).map (proj K) := by
  rw [B_eq hK]
  refine Subgroup.map_mono (sup_le (iSup_le fun j => ?_) ?_)
  · rintro _ ⟨t, rfl⟩
    exact Subgroup.mem_subgroupOf.2
      (torusGroup_le_parabolicSubgroup _ (torusElt_mem_torusGroup j t))
  · rw [← posUnipotentSub_eq]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx)))

theorem exists_lift (hK : 3 ≤ Nat.card K) (b : Bool) :
    ∃ m : (g2ModelSystem K hK).N, (m : (g2ModelSystem K hK).Weyl) =
        gen (g2ModelSystem K hK).w₁ (g2ModelSystem K hK).w₂ b ∧
      (m : AdjointQuotient .G2 K) = proj K (weylElement .G2 K (idx b)) := by
  cases b
  · exact ⟨(hexQuotRGD2 (g2Data K)).nrep 1, rfl, rfl⟩
  · exact ⟨(hexQuotRGD2 (g2Data K)).nrep 0, rfl, rfl⟩

theorem map_proj_Pmin [Finite K] (hK : 3 ≤ Nat.card K) (b : Bool) :
    (Pmin K (idx b)).map (proj K) = P (g2ModelSystem K hK) b := by
  obtain ⟨m₁, h₁, e₁⟩ := exists_lift hK b
  obtain ⟨m₂, h₂, e₂⟩ := exists_lift hK (!b)
  refine eq_P_of_lifts _ (B_le_map_Pmin hK _) b m₁ m₂ h₁ h₂ ?_ ?_
  · rw [e₁]
    exact ⟨weylElement .G2 K (idx b), Subgroup.mem_subgroupOf.2
      (weylElt_mem_parabolicSubgroup (Set.mem_singleton _)), rfl⟩
  · rw [e₂]
    rintro ⟨y, hy, hyx⟩
    have hy' : y = weylElement .G2 K (idx (!b)) := proj_injective hyx
    subst hy'
    have h3 := weylElt_mem_parabolicSubgroup_iff.1 (Subgroup.mem_subgroupOf.1 hy)
    exact absurd (idx_injective (Set.mem_singleton_iff.1 h3)) (by cases b <;> simp)

theorem map_Pmin [Finite K] (hK : 3 ≤ Nat.card K) (b : Bool) :
    (Pmin K (idx b)).map (mk K).toMonoidHom = P (g2ModelSystem K hK) b :=
  map_proj_Pmin hK b

theorem map_Pmin_one [Finite K] (hK : 3 ≤ Nat.card K) :
    (Pmin K ⟨1, by decide⟩).map (mk K).toMonoidHom = (g2ModelSystem K hK).P₁ :=
  map_Pmin hK true

theorem map_Pmin_zero [Finite K] (hK : 3 ≤ Nat.card K) :
    (Pmin K ⟨0, by decide⟩).map (mk K).toMonoidHom = (g2ModelSystem K hK).P₂ :=
  map_Pmin hK false

end Main

end CFSG.Quasithin.H13.F431.G2
