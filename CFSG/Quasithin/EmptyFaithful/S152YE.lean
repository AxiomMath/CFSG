module

public import CFSG.Quasithin.EmptyFaithful.S14610P0
public import CFSG.Quasithin.EmptyFaithful.S1469Sev

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.exists_y_fpf {H : Subgroup G} {u : G} {I I₂ : Subgroup G}
    (c : Hyp14610 T M H u I I₂)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    ∃ y : G, y ∈ oTwoUpper I ∧ y ∈ Subgroup.normalizer (VZ T M : Set G) ∧
      (∀ v ∈ VZ T M, y * v * y⁻¹ = v → v = 1) ∧ VZ T M ≤ i1Of1469 T M I := by
  have S : Setting146 G T M := c.setting
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hV4 : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  obtain ⟨hVred, -⟩ := S.hyp1281.isTwoReducedIn
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVsq : ∀ a ∈ VZ T M, a * a = 1 := fun a ha => by
    simpa [sq] using hVred.2.2.1.2 a ha
  have hy : ∃ y ∈ yOfL22 T M ⊓ I, Odd (orderOf y) ∧ y ∉ mcOf T := by
    by_contra hcon
    push Not at hcon
    exact S.not_lI_le_mcOf hLT ((Subgroup.closure_le _).mpr fun y hy => hcon y hy.1 hy.2)
  obtain ⟨y, hyLI, hyodd, hyG⟩ := hy
  obtain ⟨z, hzZ, hzy⟩ : ∃ z ∈ quasithinOmegaOneCenter T, ¬ (z * y = y * z) := by
    by_contra hno
    push Not at hno
    exact hyG (Subgroup.mem_centralizer_iff.mpr hno)
  have hzT : z ∈ T := S146T.Z_le hzZ
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzy (by simp)
  have hz2 : z ^ 2 = 1 := S146T.Z_sq hzZ
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have huQ : u ∈ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf_mcOf c.hH c.hu.mem
  have hQ1T : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_mcOf_le
  have hzu : z ∈ tU T u := (S146T.mem_tU_iff).mpr ⟨hzT,
    commutatorElement_eq_one_iff_mul_comm.mpr (S146T.comm_Z_T (hQ1T huQ) hzZ).symm⟩
  have hzI : z ∈ I := c.hI.1.1.1 hzu
  have hyL : y ∈ yOfL22 T M := hyLI.1
  have hyI : y ∈ I := hyLI.2
  have hyM : y ∈ M := S.hyp1281.le hyL
  obtain ⟨z', hz'def⟩ : ∃ z' : G, z' = y * z * y⁻¹ := ⟨_, rfl⟩
  have hz'V : z' ∈ VZ T M := hz'def ▸ (Subgroup.mem_normalizer_iff.mp (hMV hyM) z).mp hzV
  have hz'I : z' ∈ I := hz'def ▸ I.mul_mem (I.mul_mem hyI hzI) (I.inv_mem hyI)
  have hz'z : z' ≠ z := by
    intro h
    apply hzy
    have h1 : y * z * y⁻¹ = z := hz'def ▸ h
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have h1 : y * z * y⁻¹ = 1 := hz'def ▸ h
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hz'z' : z' * z' = 1 := hVsq z' hz'V
  obtain ⟨z'', hz''def⟩ : ∃ z'' : G, z'' = y * z' * y⁻¹ := ⟨_, rfl⟩
  have hz''V : z'' ∈ VZ T M := hz''def ▸ (Subgroup.mem_normalizer_iff.mp (hMV hyM) z').mp hz'V
  have hz''1 : z'' ≠ 1 := by
    intro h
    apply hz'1
    have h1 : y * z' * y⁻¹ = 1 := hz''def ▸ h
    calc z' = y⁻¹ * (y * z' * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hz''z' : z'' ≠ z' := by
    intro h
    apply hz'z
    have h1 : y * z' * y⁻¹ = y * z * y⁻¹ := by
      rw [← hz''def, h]
      exact hz'def
    exact mul_left_cancel (mul_right_cancel h1)
  have hz''z : z'' ≠ z := by
    intro h
    apply hzy
    obtain ⟨m, hm⟩ := hyodd
    have h1 : y * (y * z * y⁻¹) * y⁻¹ = z := by
      rw [← hz'def, ← hz''def]
      exact h
    have hc : (y * y) * z = z * (y * y) := by
      calc y * y * z = y * (y * z * y⁻¹) * y⁻¹ * (y * y) := by group
        _ = z * (y * y) := by rw [h1]
    have hcp : ∀ k : ℕ, (y * y) ^ k * z = z * (y * y) ^ k := fun k =>
      ((Commute.pow_left (show Commute (y * y) z from hc) k) : Commute ((y * y) ^ k) z)
    have hyy : (y * y) ^ (m + 1) = y := by
      rw [← pow_two, ← pow_mul]
      have : 2 * (m + 1) = orderOf y + 1 := by omega
      rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
    have := hcp (m + 1)
    rw [hyy] at this
    exact this.symm
  have hzz'V : z * z' ∈ VZ T M := (VZ T M).mul_mem hzV hz'V
  have hd1 : z * z' ≠ 1 := by
    intro h
    apply hz'z
    have : z' = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzz
  have hdz : z * z' ≠ z := fun h => hz'1 (mul_eq_left.mp h)
  have hdz' : z * z' ≠ z' := fun h => hz1 (mul_eq_right.mp h)
  have hall : ∀ w ∈ VZ T M, w = 1 ∨ w = z ∨ w = z' ∨ w = z * z' := by
    intro w hw
    rcases eq_or_eq_or_eq_or_eq_of_card_four hV4 (a := (1 : VZ T M)) (b := ⟨z, hzV⟩)
      (c := ⟨z', hz'V⟩) (d := ⟨z * z', hzz'V⟩)
      (fun he => hz1 (congrArg Subtype.val he).symm) (fun he => hz'1 (congrArg Subtype.val he).symm)
      (fun he => hd1 (congrArg Subtype.val he).symm) (fun he => hz'z (congrArg Subtype.val he).symm)
      (fun he => hdz (congrArg Subtype.val he).symm) (fun he => hdz' (congrArg Subtype.val he).symm)
      ⟨w, hw⟩ with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  have hz''eq : z'' = z * z' := by
    rcases hall z'' hz''V with h | h | h | h
    · exact absurd h hz''1
    · exact absurd h hz''z
    · exact absurd h hz''z'
    · exact h
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'z'
  have hyz'' : y * z'' * y⁻¹ = z := by
    calc y * z'' * y⁻¹ = y * (z * z') * y⁻¹ := by rw [hz''eq]
      _ = (y * z * y⁻¹) * (y * z' * y⁻¹) := by group
      _ = z' * z'' := by rw [← hz'def, ← hz''def]
      _ = z' * (z * z') := by rw [hz''eq]
      _ = (z' * z) * z' := (mul_assoc z' z z').symm
      _ = (z * z') * z' := by rw [hVab z' hz'V z hzV]
      _ = z * (z' * z') := mul_assoc z z' z'
      _ = z := by rw [hz'z', mul_one]
  refine ⟨y, mem_oTwoUpper_of_odd hyI hyodd, hMV hyM, ?_, ?_⟩
  · intro v hv hfix
    rcases hall v hv with h | h | h | h
    · exact h
    · rw [h] at hfix
      exact absurd (hz'def.trans hfix) hz'z
    · rw [h] at hfix
      exact absurd (hz''def.trans hfix) hz''z'
    · rw [h] at hfix
      have h2 : y * (z * z') * y⁻¹ = z := by rw [← hz''eq]; exact hyz''
      exact absurd (hfix.symm.trans h2) hdz
  ·
    have hI₁def : i1Of1469 T M I = lI T M I ⊔ (T ⊓ I) := rfl
    have hyLI' : y ∈ lI T M I := mem_oTwoUpper_of_odd hyLI hyodd
    have hyI₁ : y ∈ i1Of1469 T M I := hI₁def ▸ (Subgroup.mem_sup_left hyLI')
    have hzI₁ : z ∈ i1Of1469 T M I := hI₁def ▸ (Subgroup.mem_sup_right (⟨hzT, hzI⟩ : z ∈ T ⊓ I))
    have hz'I₁ : z' ∈ i1Of1469 T M I :=
      hz'def ▸ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyI₁ hzI₁) (Subgroup.inv_mem _ hyI₁))
    intro w hw
    rcases hall w hw with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact hzI₁
    · rw [h]; exact hz'I₁
    · rw [h]; exact Subgroup.mul_mem _ hzI₁ hz'I₁

end CFSG.Quasithin
