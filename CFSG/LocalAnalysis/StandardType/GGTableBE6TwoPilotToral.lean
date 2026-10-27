module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotAct
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  TableBExc.E6Three E6TwoMat

namespace E6TwoPilot

@[expose] def actG (g : G9) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  msFun^[(Multiplicative.toAdd g.1).val] (mtFun^[(Multiplicative.toAdd g.2).val] v)

theorem card_fix_le_nine : ∀ g : G9, g ≠ 1 →
    (Finset.univ.filter fun v : Fin 4 → ZMod 3 => actG g v = v).card ≤ 9 := by
  decide +kernel

theorem card_fix_two_le_three : ∀ g₁ g₂ : G9, g₁ ≠ 1 → g₂ ≠ 1 → g₂ ≠ g₁ → g₂ ≠ g₁ * g₁ →
    (Finset.univ.filter fun v : Fin 4 → ZMod 3 => actG g₁ v = v ∧ actG g₂ v = v).card ≤ 3 := by
  decide +kernel

section Semidirect

abbrev NG : Type := Multiplicative (Fin 4 → ZMod 3) ⋊[phiAct] G9

theorem phiAct_eq_actG (g : G9) (n : Multiplicative (Fin 4 → ZMod 3)) :
    phiAct g n = .ofAdd (actG g n.toAdd) :=
  phiAct_ofAdd g n.toAdd

theorem actG_eq_of_comm {x y : NG} (hy : y.right = 1) (hxy : x * y = y * x) :
    actG x.right y.left.toAdd = y.left.toAdd := by
  have h := congrArg SemidirectProduct.left hxy
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, hy, map_one, MulAut.one_apply,
    mul_comm y.left x.left] at h
  have h' := mul_left_cancel h
  rw [phiAct_eq_actG] at h'
  exact congrArg Multiplicative.toAdd h'

theorem card_range_inl : Nat.card (SemidirectProduct.inl : _ →* NG).range = 3 ^ 4 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv,
    RankThree.CentralCover.card_multiplicative_fin_zmod]

theorem g9_pow_three : ∀ g : G9, g ^ 3 = 1 := by
  decide

theorem card_G9 : Nat.card G9 = 3 ^ 2 := by
  rw [Nat.card_prod]
  change Nat.card (ZMod 3) * Nat.card (ZMod 3) = 3 ^ 2
  rw [Nat.card_zmod]
  norm_num

theorem card_ker_le {A : Subgroup NG} (P : (Fin 4 → ZMod 3) → Prop) [DecidablePred P]
    (hP : ∀ y ∈ A, y.right = 1 → P y.left.toAdd) :
    Nat.card (SemidirectProduct.rightHom.comp A.subtype).ker ≤
      (Finset.univ.filter P).card := by
  have hinj : Function.Injective fun y : (SemidirectProduct.rightHom.comp A.subtype).ker =>
      (⟨(y : A).1.left.toAdd, hP _ (y : A).2 y.2⟩ : {v // P v}) := by
    intro y₁ y₂ h
    have h1 : (y₁ : A).1.left = (y₂ : A).1.left :=
      Multiplicative.toAdd.injective (congrArg Subtype.val h)
    have h2 : (y₁ : A).1.right = (y₂ : A).1.right := y₁.2.trans y₂.2.symm
    exact Subtype.ext (Subtype.ext (SemidirectProduct.ext h1 h2))
  refine (Nat.card_le_card_of_injective _ hinj).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem eq_range_inl_of_comm {A : Subgroup NG} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcard : 3 ^ 4 ≤ Nat.card A) : A = (SemidirectProduct.inl : _ →* NG).range := by
  set π := SemidirectProduct.rightHom.comp A.subtype with hπ
  have hmul := Subgroup.card_ker_mul_card_range π
  by_cases hR : ∀ x ∈ A, x.right = 1
  · have hle : A ≤ (SemidirectProduct.inl : _ →* NG).range := by
      intro x hx
      rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      exact hR x hx
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_range_inl]; exact hcard)
  push Not at hR
  obtain ⟨x₁, hx₁, hg₁⟩ := hR
  exfalso
  by_cases h2 : ∀ x ∈ A, x.right = 1 ∨ x.right = x₁.right ∨ x.right = x₁.right * x₁.right
  ·
    have hker : Nat.card π.ker ≤ 9 := by
      refine (card_ker_le (fun v => actG x₁.right v = v) fun y hy hy1 =>
        actG_eq_of_comm hy1 (hA x₁ hx₁ y hy)).trans ?_
      exact card_fix_le_nine _ hg₁
    have hran : Nat.card π.range ≤ 3 := by
      have hsub : π.range ≤ Subgroup.zpowers x₁.right := by
        rintro _ ⟨x, rfl⟩
        rcases h2 x.1 x.2 with h | h | h
        · change x.1.right ∈ _
          rw [h]
          exact one_mem _
        · change x.1.right ∈ _
          rw [h]
          exact Subgroup.mem_zpowers _
        · change x.1.right ∈ _
          rw [h]
          exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
      refine (Subgroup.card_le_of_le hsub).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (g9_pow_three _)
    have : Nat.card A ≤ 27 := by
      rw [← hmul]
      calc Nat.card π.ker * Nat.card π.range ≤ 9 * 3 := Nat.mul_le_mul hker hran
        _ = 27 := by norm_num
    omega
  · push Not at h2
    obtain ⟨x₂, hx₂, h21, h22, h23⟩ := h2
    have hker : Nat.card π.ker ≤ 3 := by
      refine (card_ker_le (fun v => actG x₁.right v = v ∧ actG x₂.right v = v)
        fun y hy hy1 => ⟨actG_eq_of_comm hy1 (hA x₁ hx₁ y hy),
          actG_eq_of_comm hy1 (hA x₂ hx₂ y hy)⟩).trans ?_
      exact card_fix_two_le_three _ _ hg₁ h21 h22 h23
    have hran : Nat.card π.range ≤ 9 := by
      refine (Subgroup.card_le_card_group _).trans ?_
      rw [card_G9]
      norm_num
    have : Nat.card A ≤ 27 := by
      rw [← hmul]
      calc Nat.card π.ker * Nat.card π.range ≤ 3 * 9 := Nat.mul_le_mul hker hran
        _ = 27 := by norm_num
    omega

end Semidirect

section Final

variable {K : Type} [Field K] [CharP K 2]

theorem eq_range_torusE6Two_of_le (h2 : (2 : K) = 0) {A : Subgroup (adjointGroup .E6 K)}
    (hAS : A ≤ (psiHom K h2).range) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcard : 3 ^ 4 ≤ Nat.card A) : A = (torusE6Two h2).range := by
  have hmap : (A.comap (psiHom K h2)).map (psiHom K h2) = A := Subgroup.map_comap_eq_self hAS
  have hcard' : Nat.card (A.comap (psiHom K h2)) = Nat.card A := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective (psiHom_injective h2)).symm
  have hcomm : ∀ x ∈ A.comap (psiHom K h2), ∀ y ∈ A.comap (psiHom K h2), x * y = y * x := by
    intro x hx y hy
    apply psiHom_injective h2
    rw [map_mul, map_mul]
    exact hA _ hx _ hy
  have hN := eq_range_inl_of_comm hcomm (by rw [hcard']; exact hcard)
  rw [← hmap, hN, MonoidHom.map_range]
  exact congrArg MonoidHom.range (SemidirectProduct.lift_comp_inl _ _ _)

variable [Finite K]

theorem exists_conj_eq_range_torusE6Two (h2 : (2 : K) = 0) (hK : Nat.card K = 2)
    {A : Subgroup (adjointGroup .E6 K)} (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A) :
    ∃ c : adjointGroup .E6 K,
      A.map (MulAut.conj c).toMonoidHom = (torusE6Two (K := K) h2).range := by
  have := Fact.mk Nat.prime_three
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have hC0 : Nat.card (adjointGroup .E6 K) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card (adjointGroup .E6 K)).factorization 3 = 6 := by
    have h6 : 3 ^ 6 ∣ Nat.card (adjointGroup .E6 K) := by
      rw [← card_range_psiHom h2]
      exact Subgroup.card_subgroup_dvd_card _
    have h7 := not_pow_seven_dvd_E6_two hK
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hC0] at h6 h7
    omega
  have : Finite (Sylow 3 (adjointGroup .E6 K)) :=
    Finite.of_injective (fun P : Sylow 3 (adjointGroup .E6 K) =>
      (P : Subgroup (adjointGroup .E6 K))) fun _ _ h => Sylow.ext h
  let P : Sylow 3 (adjointGroup .E6 K) :=
    Sylow.ofCard (psiHom K h2).range (by rw [card_range_psiHom h2, hfac])
  obtain ⟨Q, hAQ⟩ := (TableB.isPGroup_of_isElemAbelian hA).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup .E6 K) Q P
  refine ⟨c, eq_range_torusE6Two_of_le h2 ?_ ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj c) x ∈ ((c • Q : Sylow 3 _) : Subgroup (adjointGroup .E6 K)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (Q : Subgroup _) (hAQ hx)
    rw [hc] at h1
    exact h1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hA hx hy]
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hcard

end Final

end E6TwoPilot

namespace E6ThreeEnd

section Input


theorem ggE6TwoToralInput_holds : GGE6TwoToralInput := by
  intro K _ _ h2 hK A hA hcard
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  obtain ⟨c, hc⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK hA hcard
  exact ⟨MulAut.conj c, hc⟩

end Input

end E6ThreeEnd

end CFSG.StandardType
