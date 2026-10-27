module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangThree

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TwE6DD2


variable {n : ℕ} {K : Type} [Field K] [Finite K] {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n}

theorem false_of_cubeTorus (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hlt : Nat.card A < 3 ^ 6)
    (hfix : ∀ e : L', e ^ 3 = 1 → (∀ a ∈ A, a e = e) → MulAut.conj e ∈ A)
    (hlast : ∃ a ∈ A, a ∉ (MulAut.conj : L' →* MulAut L').range ∨
      ∀ l : L', MulAut.conj l = a → 3 ∣ orderOf (l ^ 3))
    {Y W : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hAY : ∀ a ∈ A, ∃ φ ∈ Y, ∀ l : L', φ (ψ l) = ψ (a l)) (hY3 : ∀ y ∈ Y, y ^ 3 = 1)
    (hYc : 3 ^ 6 ≤ Nat.card Y)
    (hYinn : Y ≤ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range)
    (hW : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) (hW9 : ∀ w ∈ W, w ^ 9 = 1)
    (hYW : ∀ y ∈ Y, ∃ w ∈ W, w ^ 3 = y) : False := by
  have hZR := TwE6Delta.center_recipeR_eq_bot hn hK
  have hZ := BstarDesc.ker_eq_center hψ hker hZR
  have hδi := BstarDesc.descAut_injective hψ hZ hperf
  have hcenter : ∀ {G : Type} [Group G] (g : G), MulAut.conj g = 1 → g ∈ Subgroup.center G := by
    intro G _ g hg
    rw [Subgroup.mem_center_iff]
    intro h
    have h' := congrArg (fun f : MulAut G => f h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h'
    calc h * g = g * h * g⁻¹ * g := by rw [h']
      _ = g * h := by group
  have hconjinj : Function.Injective
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hrZ := hcenter r hr
    rw [hZR] at hrZ
    exact hrZ
  have hp4 : ∀ {M : Type} [Monoid M] {g : M}, g ^ 3 = 1 → ∀ k : ℕ, g ^ 4 ^ k = g := by
    intro M _ g hg k
    induction k with
    | zero => rw [pow_zero, pow_one]
    | succ k ih => rw [pow_succ, pow_mul, ih, pow_succ, hg, one_mul]
  have hδc : ∀ l : L', BstarDesc.descAut hψ hZ (MulAut.conj l) = MulAut.conj (ψ l) := fun l =>
    MulEquiv.ext fun r => by
      obtain ⟨g, rfl⟩ := hψ r
      rw [BstarDesc.descAut_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
        map_inv]
  have hδA : ∀ a ∈ A, BstarDesc.descAut hψ hZ a ∈ Y := by
    intro a ha
    obtain ⟨φ, hφY, hφ⟩ := hAY a ha
    have h : BstarDesc.descAut hψ hZ a = φ := MulEquiv.ext fun r => by
      obtain ⟨l, rfl⟩ := hψ r
      rw [BstarDesc.descAut_apply, hφ]
    rw [h]
    exact hφY
  have hinn : ∀ a ∈ A, ∃ l : L', MulAut.conj l = a ∧ MulAut.conj (ψ l) ∈ Y := by
    intro a ha
    obtain ⟨r, hr⟩ := hYinn (hδA a ha)
    obtain ⟨l, rfl⟩ := hψ r
    refine ⟨l, hδi ((hδc l).trans hr), ?_⟩
    rw [hr]
    exact hδA a ha
  have hM : ∀ l₁ l₂ : L', MulAut.conj (ψ l₁) ∈ Y → MulAut.conj (ψ l₂) ∈ Y → l₁ * l₂ = l₂ * l₁ :=
    fun l₁ l₂ h₁ h₂ => commute_of_cube_mem hn hK hψ hker hperf hW hW9 hYW h₁ h₂
  obtain ⟨hcf1, hcf2⟩ := center_facts hn hK hψ hker hperf
  obtain ⟨a₀, ha₀, hl⟩ := hlast
  obtain ⟨l₁, hl₁, hl₁Y⟩ := hinn a₀ ha₀
  have hlast' : ∀ l : L', MulAut.conj l = a₀ → 3 ∣ orderOf (l ^ 3) := by
    rcases hl with h | h
    · exact absurd (MonoidHom.mem_range.2 ⟨l₁, hl₁⟩) h
    · exact h
  set m := 4 ^ Nat.card L' with hm
  have ha₀3 : a₀ ^ 3 = 1 := hA.2 a₀ ha₀
  have hl₀ : MulAut.conj (l₁ ^ m) = a₀ := by rw [map_pow, hl₁, hp4 ha₀3]
  have hl₀Y : MulAut.conj (ψ (l₁ ^ m)) ∈ Y := by
    rw [map_pow, map_pow]
    exact pow_mem hl₁Y _
  have hl₁3 : l₁ ^ 3 ∈ Subgroup.center L' := hcenter _ (by rw [map_pow, hl₁, ha₀3])
  have hz₀Z : (l₁ ^ m) ^ 3 ∈ Subgroup.center L' := by
    rw [pow_right_comm]
    exact pow_mem hl₁3 _
  have hz₀3 : ((l₁ ^ m) ^ 3) ^ 3 = 1 := by
    rw [pow_right_comm l₁]
    exact hcf1 _ hl₁3
  have ho : orderOf ((l₁ ^ m) ^ 3) = 3 :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hz₀3) (hlast' _ hl₀)
  have hYA : Y ≤ A.map (BstarDesc.descAut hψ hZ) := by
    intro y hy
    obtain ⟨r, hr⟩ := hYinn hy
    obtain ⟨x, rfl⟩ := hψ r
    have hy3 : y ^ 3 = 1 := hY3 y hy
    have hxY : MulAut.conj (ψ (x ^ m)) = y := by rw [map_pow, map_pow, hr, hp4 hy3]
    have hx3 : x ^ 3 ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker]
      apply hconjinj
      rw [map_pow, map_pow, hr, hy3, map_one]
    have hx'Z : (x ^ m) ^ 3 ∈ Subgroup.center L' := by
      rw [pow_right_comm]
      exact pow_mem hx3 _
    have hx'3 : ((x ^ m) ^ 3) ^ 3 = 1 := by
      rw [pow_right_comm x]
      exact hcf1 _ hx3
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hcf2 _ hz₀Z _ hx'Z ho hx'3)
    set x' := x ^ m with hx'
    set l₀ := l₁ ^ m with hl₀def
    set e := x' * l₀ ^ (-k) with he
    have hcomm : Commute x' l₀ := hM _ _ (by rw [hxY]; exact hy) hl₀Y
    have he3 : e ^ 3 = 1 := by
      rw [he, (hcomm.zpow_right (-k)).mul_pow, ← hk]
      group
    have heY : MulAut.conj (ψ e) ∈ Y := by
      rw [he, map_mul ψ, map_zpow ψ, map_mul MulAut.conj, map_zpow MulAut.conj]
      exact mul_mem (by rw [hxY]; exact hy) (zpow_mem hl₀Y _)
    have hefix : ∀ a ∈ A, a e = e := by
      intro a ha
      obtain ⟨la, hla, hlaY⟩ := hinn a ha
      rw [← hla, MulAut.conj_apply, hM la e hlaY heY, mul_inv_cancel_right]
    have hx'A : MulAut.conj x' ∈ A := by
      have hxe : x' = e * l₀ ^ k := by
        rw [he, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      rw [hxe, map_mul MulAut.conj, map_zpow MulAut.conj, hl₀]
      exact mul_mem (hfix e he3 hefix) (zpow_mem ha₀ k)
    exact Subgroup.mem_map.2 ⟨_, hx'A, (hδc x').trans hxY⟩
  have : Finite (MulAut (TwE6Delta.RecipeR K n)) := TwE6Delta.finite_mulAut_recipeR hK
  have h1 := Subgroup.card_le_of_le hYA
  rw [Subgroup.card_map_of_injective hδi] at h1
  exact absurd (hYc.trans h1) (not_le.mpr hlt)

end TwE6DD2

section Holds


theorem ggTwE6ThreeDeltaTwoInput_holds : GGTwE6ThreeDeltaTwoInput := by
  intro K _ _ n hn hK h3 h3n L' _ _ ψ hψ hker hperf _ A Ah hA hAI hlt hadm _ _
  exfalso
  obtain ⟨-, hC6⟩ := ggTwE6ThreeCoverRankInput_holds K n hn hK h3 L' ψ hψ hker hperf
  obtain ⟨E6, hE6, hE6c⟩ := hC6 (Or.inl h3n)
  obtain ⟨hfix, hcase⟩ := hadm
  rcases hcase with ⟨-, hb⟩ | ⟨-, hb, hlast⟩
  ·
    exact absurd (hE6c.trans (hb E6 hE6)) (not_le.mpr hlt)
  have h5 : 3 ^ 5 ≤ Nat.card A := by
    refine Nat.le_of_mul_le_mul_left ?_ (by norm_num : 0 < 3)
    calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
      _ ≤ Nat.card E6 := hE6c
      _ ≤ 3 * Nat.card A := hb E6 hE6
  have hZ := BstarDesc.ker_eq_center hψ hker (TwE6Delta.center_recipeR_eq_bot hn hK)
  have hδi := BstarDesc.descAut_injective hψ hZ hperf
  have hX : IsElemAbelian 3 (A.map (BstarDesc.descAut hψ hZ)) := TableB.isElemAbelian_map hA _
  have hXI : ((A.map (BstarDesc.descAut hψ hZ) : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
      Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have h : BstarDesc.descAut hψ hZ a = φ := MulEquiv.ext fun r => by
      obtain ⟨l, rfl⟩ := hψ r
      rw [BstarDesc.descAut_apply, hφ]
    rw [h]
    exact hφI
  have hX5 : 3 ^ 5 ≤ Nat.card (A.map (BstarDesc.descAut hψ hZ)) := by
    rw [Subgroup.card_map_of_injective hδi]
    exact h5
  obtain ⟨Y, hXY, hY, -, hYc, h9⟩ := TwE6DD2.exists_cubeTorus_recipe hn hK h3 hX hXI hX5
  obtain ⟨hYinn, W, hW, hW9, hYW⟩ := h9 (SmallKG.nine_dvd_two_pow_add_one h3 h3n)
  exact TwE6DD2.false_of_cubeTorus hn hK hψ hker hperf hA hlt hfix hlast
    (fun a ha => ⟨_, hXY ⟨a, ha, rfl⟩, BstarDesc.descAut_apply hψ hZ a⟩) hY.2 hYc.ge hYinn hW
    hW9 hYW

end Holds

end CFSG.StandardType
