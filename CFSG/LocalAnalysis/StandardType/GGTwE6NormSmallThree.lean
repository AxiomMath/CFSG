module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC6Defs
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeOdd
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeLift
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaSmallThreeOdd

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly


theorem ggTwE6NormSmallThreeInput_of_endNode
    (h5 : ∀ {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
      (h3 : 3 ∣ 2 ^ n + 1) {X : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
      (hX : IsElemAbelian 3 X)
      (hXI : (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
      (hX4 : 3 ^ 4 ≤ Nat.card X)
      (hXU : ∃ U : Subgroup (TwE6Delta.RecipeR K n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U)
      {x : MulAut (TwE6Delta.RecipeR K n)} (hx : x ∈ X) (hx1 : x ≠ 1)
      (hcomp : IsComponentOf (LargeEvenLayer (ggFix x)) (ggFix x))
      (hend : ∀ y ∈ X, (∀ j ∈ LargeEvenLayer (ggFix x), y j = j) ↔ y ∈ Subgroup.zpowers x),
      ∃ (Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))) (ι : Type)
        (r s : ι → TwE6Delta.RecipeR K n) (u : TwE6Delta.RecipeR K n)
        (F : Subgroup (TwE6Delta.RecipeR K n)),
        IsElemAbelian 3 Y ∧ X ≤ Y ∧ (∀ i, MulAut.conj (s i) ∈ Y) ∧
        (∀ i, ∀ y ∈ Y, ∃ k : ℕ,
          MulAut.conj (r i) * y * (MulAut.conj (r i))⁻¹ = MulAut.conj (s i) ^ k * y) ∧
        (∀ i, r i * s i * (r i)⁻¹ = (s i)⁻¹) ∧ u * u = 1 ∧ u ≠ 1 ∧ (∀ φ ∈ X, φ u = u) ∧
        F ≤ Subgroup.closure (Set.range s) ∧ F ≤ LargeEvenLayer (ggFix x) ∧
        (∀ f ∈ F, f * u = u * f) ∧ 3 ^ 3 ≤ Nat.card F) :
    GGTwE6NormSmallThreeInput := by
  intro K _ _ n hn hK h3
  have hcenR := TwE6Delta.center_recipeR_eq_bot hn hK
  refine ggStdSubTwoTorusNormSmallR_three_of_odd hcenR ?_
  intro L' _ _ ψ hψ hker hperf hodd A hA hAI hr _ hnorm a ha ha1 hcomp hcent hsm
  haveI := TwE6Delta.finite_recipeR hK
  have hkc : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hcenR
  have hρinj := BstarDesc.descAut_injective hψ hkc hperf
  have hρa : ∀ b : MulAut L', ∀ l, BstarDesc.descAut hψ hkc b (ψ l) = ψ (b l) :=
    BstarDesc.descAut_apply hψ hkc
  set ρ := BstarDesc.descAut hψ hkc
  have hXI : ((A.map ρ : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
      Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨φ, hφ, hφb⟩ := hAI b hb
    have h1 : ρ b = φ := MulEquiv.ext fun r => by
      obtain ⟨l, rfl⟩ := hψ r
      rw [hρa, hφb]
    rw [h1]
    exact hφ
  have hXU : ∃ U : Subgroup (TwE6Delta.RecipeR K n), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ φ ∈ A.map ρ, ∀ v ∈ U, φ v ∈ U := by
    obtain ⟨U, hU1, hU2, hUA⟩ := hnorm
    refine ⟨U, hU1, hU2, ?_⟩
    rintro _ ⟨b, hb, rfl⟩ v hv
    obtain ⟨l, rfl⟩ := hψ v
    rw [hρa]
    exact hUA b hb l hv
  have hend : ∀ y ∈ A.map ρ, (∀ j ∈ LargeEvenLayer (ggFix (ρ a)), y j = j) ↔
      y ∈ Subgroup.zpowers (ρ a) := by
    rintro _ ⟨b, hb, rfl⟩
    have hz : ρ b ∈ Subgroup.zpowers (ρ a) ↔ b ∈ Subgroup.zpowers a := by
      rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      exact exists_congr fun k => by rw [← map_zpow, hρinj.eq_iff]
    rw [hz, ← USixTwo.fix_layer_iff hψ hker (hρa a) (hρa b)]
    exact hcent b hb
  obtain ⟨Y, ι, r, s, u, F, hY, hXY, hs, hrs, hrsi, hu2, hu1, huX, hFs, hFJ, hFu, hF⟩ :=
    h5 hn hK h3 (TableB.isElemAbelian_map hA ρ) hXI
      (by rw [Subgroup.card_map_of_injective hρinj]; exact hr) hXU
      (Subgroup.mem_map_of_mem ρ ha) (fun h1 => ha1 (hρinj (by rw [h1, map_one])))
      (USixTwo.isComponentOf_layer_down hψ hker (hρa a) hcomp) hend
  have hZ : Nat.card (Subgroup.center L') ∣ 3 := by
    rcases TwE6DS3.card_center_eq_one_or_three hn hK hψ hker hperf hodd with h | h <;>
      simp [h]
  obtain ⟨E, hE, hZE, hsE, hEfix⟩ :=
    TwE6D3.exists_fixed_of_refl hψ hker hZ hcenR hY r s hs hrs hrsi
  have hAE : ∀ b ∈ A, ∀ e ∈ E, b e = e := fun b hb =>
    hEfix b (hA.2 b hb) ⟨ρ b, hXY (Subgroup.mem_map_of_mem ρ hb), hρa b⟩
  have hZ3 : ∀ z ∈ Subgroup.center L', z ^ 3 = 1 := fun z hz => by
    obtain ⟨c, hc⟩ := hZ
    have h1 : (⟨z, hz⟩ : Subgroup.center L') ^ 3 = 1 := by
      rw [hc, pow_mul, pow_card_eq_one', one_pow]
    simpa using congrArg Subtype.val h1
  obtain ⟨w, rfl⟩ := hψ u
  have hcube : ∀ v, ψ v = ψ w → v ^ 3 = w ^ 3 := fun v hv => by
    have hz : w⁻¹ * v ∈ Subgroup.center L' := by
      rw [← hkc, MonoidHom.mem_ker, map_mul, map_inv, hv, inv_mul_cancel]
    have hc : Commute w (w⁻¹ * v) := Subgroup.mem_center_iff.1 hz w
    calc v ^ 3 = (w * (w⁻¹ * v)) ^ 3 := by rw [mul_inv_cancel_left]
      _ = w ^ 3 := by rw [hc.mul_pow, hZ3 _ hz, mul_one]
  have hsq : (w ^ 3) ^ 2 = 1 := by
    rw [pow_right_comm, hZ3 _ (hker (MonoidHom.mem_ker.2 (by rw [map_pow, pow_two, hu2])))]
  have hψ3 : ψ (w ^ 3) = ψ w := by rw [map_pow, pow_three, hu2, mul_one]
  have hne : w ^ 3 ≠ 1 := fun h => hu1 (by rw [← hψ3, h, map_one])
  have hAu : ∀ b ∈ A, b (w ^ 3) = w ^ 3 := fun b hb => by
    rw [map_pow]
    exact hcube _ (by rw [← hρa, huX _ (Subgroup.mem_map_of_mem ρ hb)])
  have hcomm : ∀ e, ψ e ∈ F → Commute e (w ^ 3) := fun e he => by
    have h := hcube (e * w * e⁻¹) (by
      rw [map_mul, map_mul, map_inv, hFu _ he, mul_inv_cancel_right])
    rw [conj_pow] at h
    show e * w ^ 3 = w ^ 3 * e
    calc e * w ^ 3 = e * w ^ 3 * e⁻¹ * e := (inv_mul_cancel_right _ _).symm
      _ = w ^ 3 * e := by rw [h]
  have hU2 : IsPGroup 2 (Subgroup.zpowers (w ^ 3)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hsq hne, pow_one])
  have hUA : ∀ b ∈ A, ∀ v ∈ Subgroup.zpowers (w ^ 3), b v ∈ Subgroup.zpowers (w ^ 3) :=
    fun b hb v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [map_zpow, hAu b hb]
      exact Subgroup.zpow_mem_zpowers _ k
  have hsmall : ∀ E' : Subgroup L', E' ≤ E → E' ≤ LargeEvenLayer (ggFix a) →
      (∀ e ∈ E', ψ e ∈ F) → Nat.card E' < 3 ^ 3 := by
    intro E' hE'E hE'J hE'F
    refine hsm E' ⟨⟨⟨fun x y => Subtype.ext (hE.comm (hE'E x.2) (hE'E y.2))⟩⟩,
      fun x hx => hE.2 x (hE'E hx)⟩ hE'J (fun b hb e he => hAE b hb e (hE'E he))
      (Or.inr ⟨Subgroup.zpowers (w ^ 3), Subgroup.zpowers_ne_bot.2 hne, hU2, hUA,
        fun e he => ?_⟩)
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hh)
    exact ((hcomm e (hE'F e he)).zpow_right k).eq.symm
  have hlay := USixTwo.layer_map_eq hψ hker (hρa a)
  have hFE : F ≤ (E ⊓ LargeEvenLayer (ggFix a) ⊓ F.comap ψ).map ψ := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := hsE (hFs hf)
    have hj := hFJ hf
    rw [← hlay] at hj
    obtain ⟨j, hjJ, hje⟩ := hj
    have hz : e⁻¹ * j ∈ Subgroup.center L' := by
      rw [← hkc, MonoidHom.mem_ker, map_mul, map_inv, hje, inv_mul_cancel]
    have hjF : ψ j ∈ F := by rw [hje]; exact hf
    exact ⟨j, ⟨⟨by simpa using E.mul_mem he (hZE hz), hjJ⟩, hjF⟩, hje⟩
  have hlt := hsmall (E ⊓ LargeEvenLayer (ggFix a) ⊓ F.comap ψ) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) fun e he => he.2
  exact absurd (hF.trans ((Subgroup.card_le_of_le hFE).trans
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)))) (not_le.2 hlt)

end CFSG.StandardType.SmallExc

end
