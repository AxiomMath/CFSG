module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Datum

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open CFSG.LieType.D4Small

section Index

variable {K : Type*} [Field K] {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module K E]

theorem exists_add_fixed_of_index (ρ : G →* Module.End K E) (S : Submodule K E) (H : Subgroup G)
    [H.FiniteIndex] (hH : (H.index : K) ≠ 0) (v : E) (hv : ∀ g, ρ g v - v ∈ S)
    (hvH : ∀ g ∈ H, ρ g v = v) : ∃ s ∈ S, ∀ g, ρ g (v + s) = v + s := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set δ : G → E := fun g => ρ g v - v with hδ
  have hδmul : ∀ g h, δ (g * h) = δ g + ρ g (δ h) := fun g h => by
    simp only [hδ, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hδH : ∀ g, ∀ h ∈ H, δ (g * h) = δ g := fun g h hh => by
    rw [hδmul, show δ h = 0 from sub_eq_zero.2 (hvH h hh), map_zero, add_zero]
  set δq : G ⧸ H → E := fun c => δ c.out with hδq
  have hδq : ∀ g : G, δq (g : G ⧸ H) = δ g := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    simp only [hδq]
    rw [hh, hδH g h h.2]
  set σ : E := ∑ c : G ⧸ H, δq c with hσ
  have hσS : σ ∈ S := S.sum_mem fun c _ => hv _
  have key : ∀ g, (H.index : K) • δ g = σ - ρ g σ := fun g => by
    have h1 : σ = ∑ c : G ⧸ H, δq (g • c) := by
      rw [hσ, ← Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm (G ⧸ H))]
      rfl
    have h2 : ∀ c : G ⧸ H, δq (g • c) = δ g + ρ g (δq c) := fun c => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, hδq, hδq, hδmul]
    have h3 : σ = (H.index : K) • δ g + ρ g σ := by
      conv_lhs => rw [h1]
      rw [Finset.sum_congr rfl fun c _ => h2 c, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, ← map_sum, ← Nat.card_eq_fintype_card, ← Subgroup.index,
        ← Nat.cast_smul_eq_nsmul K]
    exact eq_sub_of_add_eq h3.symm
  refine ⟨(H.index : K)⁻¹ • σ, S.smul_mem _ hσS, fun g => ?_⟩
  have e := congrArg (fun y => (H.index : K)⁻¹ • y) (key g)
  simp only [smul_smul, inv_mul_cancel₀ hH, one_smul, smul_sub, hδ] at e
  rw [map_add, map_smul]
  rw [sub_eq_iff_eq_add] at e
  rw [e]
  abel

end Index

section Torus

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem isGoodVal_of_small {x : ℤ} (hx : x ≠ 0) (h2 : |x| ≤ 2) : IsGoodVal x := by
  obtain ⟨h1, h2⟩ := abs_le.1 h2
  interval_cases x <;> simp_all [IsGoodVal]

theorem torusSep_zero {m : ℕ} (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K)
    {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W) (a : ℕ) :
    ∀ β ∈ posRoot, ∀ χ ∈ W, ∃ z : Fin 4 → Kˣ, wtChar m 0 β z = 1 ∧ wtChar m a χ z ≠ 1 := by
  intro β hβ χ hχ
  obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
  obtain ⟨e, -, he0, hne, hle, -⟩ := sep_nonzero hW hW β hβ χ hχ χ hχ
  have hne' : dot4 χ e ≠ 0 := hne.elim id id
  refine ⟨fun i => g ^ e i, ?_, ?_⟩
  · rw [wtChar_zpow, he0, zero_mul, mul_zero, zpow_zero]
  · rw [wtChar_zpow]
    exact zpow_ne_one_of_isGoodVal hg hm hq (isGoodVal_of_small hne' hle) a

end Torus

section H1

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {G : Type*} [Group G] [Finite G]
  (D : D4Datum G K) {E : Type*} [AddCommGroup E] [Module K E]

theorem exists_add_fixed_of_minWt {m : ℕ} (hm : 2 * m = Fintype.card K)
    (hq : 4 ≤ Fintype.card K) (hB : ((borel D).index : K) ≠ 0) (ρ : G →* Module.End K E)
    (S : Submodule K E) (hS : ∀ g, ∀ s ∈ S, ρ g s ∈ S) {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W)
    {a : ℕ} (bS : Module.Basis W K S)
    (hbSh : ∀ z χ, ρ (D.h z) (bS χ) = (wtChar m a (χ : Fin 4 → ℤ) z : K) • (bS χ : E))
    (v : E) (hv : ∀ g, ρ g v - v ∈ S) : ∃ s ∈ S, ∀ g, ρ g (v + s) = v + s := by
  classical
  obtain ⟨s₁, hs₁, hv₁⟩ := exists_add_fixed_of_index (ρ.comp D.h) S ⊥
    (by rw [Subgroup.index_bot]; exact natCard_torus_ne_zero) v (fun z => hv _)
    (fun z hz => by rw [Subgroup.mem_bot.1 hz, map_one]; rfl)
  set v₁ := v + s₁ with hv₁def
  have hv₁S : ∀ g, ρ g v₁ - v₁ ∈ S := fun g => by
    rw [hv₁def, map_add, show ρ g v + ρ g s₁ - (v + s₁) = (ρ g v - v) + (ρ g s₁ - s₁) by abel]
    exact S.add_mem (hv g) (S.sub_mem (hS g s₁ hs₁) hs₁)
  have hz₁ : ∀ z, ρ (D.h z) v₁ = v₁ := fun z => hv₁ z
  have hcoord : ∀ z (y : S) χ, bS.repr ⟨ρ (D.h z) y, hS _ _ y.2⟩ χ =
      (wtChar m a (χ : Fin 4 → ℤ) z : K) * bS.repr y χ := by
    intro z y χ
    have hy : (⟨ρ (D.h z) y, hS _ _ y.2⟩ : S) =
        ∑ ψ, (bS.repr y ψ * (wtChar m a (ψ : Fin 4 → ℤ) z : K)) • bS ψ := by
      apply Subtype.ext
      conv_lhs => rw [← bS.sum_repr y]
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hbSh, smul_smul]
    rw [hy, Module.Basis.repr_sum_self, mul_comm]
  have hroot : ∀ β ∈ posRoot, ∀ t, ρ (posX D β t) v₁ = v₁ := by
    intro β hβ t
    set d : S := ⟨ρ (posX D β t) v₁ - v₁, hv₁S _⟩ with hd
    have hdz : ∀ z, wtChar m 0 β z = 1 → (⟨ρ (D.h z) d, hS _ _ d.2⟩ : S) = d := by
      intro z hz
      apply Subtype.ext
      simp only [hd, map_sub, hz₁]
      rw [← Module.End.mul_apply, ← map_mul, h_posX D hm β hβ, map_mul, Module.End.mul_apply,
        hz₁, hz, Units.val_one, one_mul]
    have hd0 : d = 0 := by
      refine bS.repr.injective (Finsupp.ext fun χ => ?_)
      obtain ⟨z, hz1, hz2⟩ := torusSep_zero hm hq hW a β hβ χ χ.2
      have h := hcoord z d χ
      rw [hdz z hz1] at h
      have h' : ((wtChar m a (χ : Fin 4 → ℤ) z : K) - 1) * bS.repr d χ = 0 := by
        rw [sub_mul, ← h, one_mul, sub_self]
      rw [map_zero, Finsupp.zero_apply]
      exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 fun h => hz2 (Units.ext h))
    have := congrArg Subtype.val hd0
    simp only [hd, ZeroMemClass.coe_zero] at this
    exact sub_eq_zero.1 this
  let stab : Subgroup G :=
    { carrier := {g | ρ g v₁ = v₁}
      mul_mem' := fun {g h} hg hh => by
        simp only [Set.mem_setOf_eq] at hg hh ⊢
        rw [map_mul, Module.End.mul_apply, hh, hg]
      one_mem' := by simp
      inv_mem' := fun {g} hg => by
        simp only [Set.mem_setOf_eq] at hg ⊢
        conv_lhs => rw [← hg]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hBstab : borel D ≤ stab := by
    rw [borel, Subgroup.closure_le]
    rintro g (⟨β, hβ, t, rfl⟩ | ⟨z, rfl⟩)
    · exact hroot β hβ t
    · exact hz₁ z
  obtain ⟨s₂, hs₂, hv₂⟩ := exists_add_fixed_of_index ρ S (borel D) hB v₁ hv₁S
    (fun g hg => hBstab hg)
  refine ⟨s₁ + s₂, S.add_mem hs₁ hs₂, fun g => ?_⟩
  rw [← add_assoc]
  exact hv₂ g

end H1

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
