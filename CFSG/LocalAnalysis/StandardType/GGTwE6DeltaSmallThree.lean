module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC6Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaSmallThreeOdd

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly


theorem ggTwE6DeltaSmallThreeInput_of_cube (hC : GGTwE6CubeNodeInput) :
    GGTwE6DeltaSmallThreeInput := by
  intro K _ _ n hn hK h3
  have hcenR := TwE6Delta.center_recipeR_eq_bot hn hK
  refine ggStdSubTwoTorusDeltaSmall_three_of_odd hcenR ?_
  intro L' _ _ ψ hψ hker hperf hodd A hA hAI _ _ hadm a ha ha1 hcomp hcent hsm
  exfalso
  classical
  haveI := TwE6Delta.finite_recipeR hK
  haveI := TwE6Delta.finite_mulAut_recipeR hK
  have hkc : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hcenR
  have hρinj := BstarDesc.descAut_injective hψ hkc hperf
  have hρa : ∀ b : MulAut L', ∀ l, BstarDesc.descAut hψ hkc b (ψ l) = ψ (b l) :=
    BstarDesc.descAut_apply hψ hkc
  set ρ := BstarDesc.descAut hψ hkc with hρ
  have h5 := TwE6DS3.five_le_card hn hK h3 hψ hker hperf hadm
  have hXc : Nat.card (A.map ρ) = Nat.card A := Subgroup.card_map_of_injective hρinj
  have hXI : ((A.map ρ : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
      Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨φ, hφ, hφb⟩ := hAI b hb
    have h1 : ρ b = φ := MulEquiv.ext fun r => by
      obtain ⟨l, rfl⟩ := hψ r
      rw [hρa, hφb]
    rw [h1]
    exact hφ
  have hXel : IsElemAbelian 3 (A.map ρ) := TableB.isElemAbelian_map hA _
  obtain ⟨Y, hXY, hY, hYI, hYc, -⟩ :=
    TwE6DD2.exists_cubeTorus_recipe hn hK h3 hXel hXI (by rw [hXc]; exact h5)
  obtain ⟨E, hE, hZE, hEc, hEfix⟩ := TwE6DS3.exists_fixed hn hK h3 hψ hker hperf hodd hA h5 hAI
    hY hYI hYc fun b hb => ⟨ρ b, hXY ⟨b, hb, rfl⟩, hρa b⟩
  have hA6 : Nat.card A = 3 ^ 6 := by
    have hdvd : Nat.card A ∣ 3 ^ 6 := by
      rw [← hXc, ← hYc]
      exact Subgroup.card_dvd_of_le hXY
    obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hk5 : 5 ≤ k := by
      by_contra hlt
      have h5' : 3 ^ 5 ≤ 3 ^ k := hk ▸ h5
      have h4 : 3 ^ 5 ≤ 3 ^ 4 := h5'.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      norm_num at h4
    rcases (by omega : k = 5 ∨ k = 6) with rfl | rfl
    · exact (TwE6D3.false_of_fixed hadm hE hEfix (by rw [hk]; exact hEc)).elim
    · exact hk
  have hXY' : A.map ρ = Y := Subgroup.eq_of_le_of_card_ge hXY (le_of_eq (by rw [hYc, hXc, hA6]))
  have hlay := USixTwo.layer_map_eq hψ hker (hρa a)
  have hend : ∀ y ∈ Y, (∀ j ∈ LargeEvenLayer (ggFix (ρ a)), y j = j) ↔
      y ∈ Subgroup.zpowers (ρ a) := by
    intro y hy
    rw [← hXY'] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hz : ρ b ∈ Subgroup.zpowers (ρ a) ↔ b ∈ Subgroup.zpowers a := by
      rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      exact exists_congr fun k => by rw [← map_zpow, hρinj.eq_iff]
    rw [hz, ← USixTwo.fix_layer_iff hψ hker (hρa a) (hρa b)]
    exact hcent b hb
  have hEfixR : E.map ψ ≤ ggFix (ρ a) := by
    rintro _ ⟨e, he, rfl⟩
    rw [mem_ggFix, hρa, hEfix a ha e he]
  have hbound := hC K n hn hK h3 Y hY hYI hYc (ρ a) (hXY ⟨a, ha, rfl⟩)
    (fun h1 => ha1 (hρinj (by rw [h1, map_one])))
    (USixTwo.isComponentOf_layer_down hψ hker (hρa a) hcomp) hend (E.map ψ)
    (TableB.isElemAbelian_map hE _) hEfixR
  have hinf : E.map ψ ⊓ LargeEvenLayer (ggFix (ρ a)) ≤
      (E ⊓ LargeEvenLayer (ggFix a)).map ψ := by
    rintro _ ⟨⟨e, he, rfl⟩, hj⟩
    rw [← hlay] at hj
    obtain ⟨j, hjJ, hje⟩ := hj
    refine ⟨j, ⟨?_, hjJ⟩, hje⟩
    have hz : e⁻¹ * j ∈ Subgroup.center L' := by
      rw [← hkc, MonoidHom.mem_ker, map_mul, map_inv, hje, inv_mul_cancel]
    simpa using E.mul_mem he (hZE hz)
  have hψE : 3 ^ 5 ≤ Nat.card (E.map ψ) :=
    Nat.le_of_mul_le_mul_left (hEc.trans (card_le_card_center_mul_card_map hkc E)) Nat.card_pos
  have hEJ : Nat.card (E.map ψ ⊓ LargeEvenLayer (ggFix (ρ a)) : Subgroup _) ≤
      Nat.card (E ⊓ LargeEvenLayer (ggFix a) : Subgroup L') :=
    (Subgroup.card_le_of_le hinf).trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _))
  have hEJel : IsElemAbelian 3 (E ⊓ LargeEvenLayer (ggFix a) : Subgroup L') :=
    ⟨⟨⟨fun x y => Subtype.ext (hE.comm x.2.1 y.2.1)⟩⟩, fun x hx => hE.2 x hx.1⟩
  have hsmall := hsm _ hEJel inf_le_right (fun b hb e he => hEfix b hb e he.1)
    (Or.inl fun e he => hadm.1 e (hE.2 e he.1) fun b hb => hEfix b hb e he.1)
  have e5 : (3 : ℕ) ^ 5 = 243 := by norm_num
  have e3 : (3 : ℕ) ^ 3 = 27 := by norm_num
  rw [e5] at hψE
  rw [e3] at hsmall
  omega

end CFSG.StandardType.SmallExc

end
