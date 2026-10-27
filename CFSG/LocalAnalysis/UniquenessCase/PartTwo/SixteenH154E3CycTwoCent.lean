module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_e3_CycTwoCent_centralizer_le
    [Finite W] (hcard : Nat.card W = 2 ^ 4)
    {D : Subgroup (MulAut W)} (hD : Nat.card ↥D = 9) {u₀ : W}
    (hreg : ∀ d ∈ D, d ≠ 1 → d u₀ ≠ u₀) :
    ∀ g : MulAut W, g ∈ Subgroup.centralizer (D : Set (MulAut W)) → g ∈ D := by
  have hu0 : u₀ ≠ 1 := by
    intro h1
    have hbot : D = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro d hd
      by_contra hd1
      exact hreg d hd hd1 (by simp [h1])
    rw [hbot, Subgroup.card_bot] at hD
    norm_num at hD
  let f : ↥D → W := fun d => (d : MulAut W) u₀
  have hf : Function.Injective f := by
    intro d₁ d₂ h
    change (d₁ : MulAut W) u₀ = (d₂ : MulAut W) u₀ at h
    have hmem : (d₂ : MulAut W)⁻¹ * (d₁ : MulAut W) ∈ D :=
      D.mul_mem (D.inv_mem d₂.2) d₁.2
    have hfix : ((d₂ : MulAut W)⁻¹ * (d₁ : MulAut W)) u₀ = u₀ := by
      rw [MulAut.mul_apply, h, MulAut.inv_apply_self]
    have hone : (d₂ : MulAut W)⁻¹ * (d₁ : MulAut W) = 1 := by
      by_contra hne
      exact hreg _ hmem hne hfix
    exact Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hOcard : (Set.range f).ncard = 9 := by
    rw [Set.ncard_range_of_injective hf, hD]
  have h1O : (1 : W) ∉ Set.range f := by
    rintro ⟨d, hd⟩
    change (d : MulAut W) u₀ = 1 at hd
    refine hu0 ((d : MulAut W).injective ?_)
    rw [hd, map_one]
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg
  let O' : Set W := g '' Set.range f
  have hO'card : O'.ncard = 9 := by
    change (g '' Set.range f).ncard = 9
    rw [Set.ncard_image_of_injective _ g.injective, hOcard]
  have h1O' : (1 : W) ∉ O' := by
    rintro ⟨x, hxO, hx⟩
    change g x = 1 at hx
    have hx1 : x = 1 := by
      refine g.injective ?_
      rw [hx, map_one]
    rw [hx1] at hxO
    exact h1O hxO
  have hOsub : Set.range f ⊆ {w : W | w ≠ 1} := fun w hw hw1 => h1O (hw1 ▸ hw)
  have hO'sub : O' ⊆ {w : W | w ≠ 1} := fun w hw hw1 => h1O' (hw1 ▸ hw)
  have hinter : (Set.range f ∩ O').Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hdisj : Disjoint (Set.range f) O' := Set.disjoint_iff_inter_eq_empty.mpr hne
    have hunion : ((Set.range f) ∪ O').ncard = 18 := by
      rw [Set.ncard_union_eq hdisj, hOcard, hO'card]
    have hsub : (Set.range f) ∪ O' ⊆ {w : W | w ≠ 1} :=
      Set.union_subset hOsub hO'sub
    have hle : ((Set.range f) ∪ O').ncard ≤ ({w : W | w ≠ 1} : Set W).ncard :=
      Set.ncard_le_ncard hsub
    have hT : ({w : W | w ≠ 1} : Set W).ncard = 15 := by
      have heq : ({w : W | w ≠ 1} : Set W) = Set.univ \ {1} := by
        ext w; simp
      rw [heq, Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, Set.ncard_singleton,
        hcard]
      norm_num
    rw [hunion, hT] at hle
    omega
  obtain ⟨x, hx⟩ := hinter
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hxO, hxO'⟩ := hx
  obtain ⟨d₁, hd₁⟩ := hxO
  obtain ⟨y, hyO, hyx⟩ := hxO'
  obtain ⟨d₂, hd₂⟩ := hyO
  have hkey : (d₂ : MulAut W) (g u₀) = (d₁ : MulAut W) u₀ := by
    have hcomm : (d₂ : MulAut W) * g = g * (d₂ : MulAut W) := hg _ d₂.2
    have h1 : (d₂ : MulAut W) (g u₀) = g ((d₂ : MulAut W) u₀) := by
      have := congrArg (fun e : MulAut W => e u₀) hcomm
      simpa [MulAut.mul_apply] using this
    rw [h1, show (d₂ : MulAut W) u₀ = y from hd₂, hyx,
      show (d₁ : MulAut W) u₀ = x from hd₁]
  let d₀ : ↥D := d₂⁻¹ * d₁
  have hd0 : (d₀ : MulAut W) u₀ = g u₀ := by
    have h2 : (d₂ : MulAut W)⁻¹ ((d₁ : MulAut W) u₀) = g u₀ := by
      have := congrArg (fun w => (d₂ : MulAut W)⁻¹ w) hkey
      simpa [MulAut.inv_apply_self] using this.symm
    show ((d₂⁻¹ * d₁ : ↥D) : MulAut W) u₀ = g u₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply]
    exact h2
  have hDcomm : ∀ a b : ↥D, a * b = b * a := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsMulCommutative ↥D :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hD]; norm_num)
    exact fun a b => mul_comm' a b
  let g' : MulAut W := (d₀ : MulAut W)⁻¹ * g
  have hg'u0 : g' u₀ = u₀ := by
    change ((d₀ : MulAut W)⁻¹ * g) u₀ = u₀
    rw [MulAut.mul_apply, ← hd0, MulAut.inv_apply_self]
  have hg'comm : ∀ d : ↥D, (d : MulAut W) * g' = g' * (d : MulAut W) := by
    intro d
    have hcommD : (d : MulAut W) * (d₀ : MulAut W)⁻¹
        = (d₀ : MulAut W)⁻¹ * (d : MulAut W) := by
      have h := congrArg (fun x : ↥D => (x : MulAut W)) (hDcomm d d₀⁻¹)
      simpa using h
    have hdg' : (d : MulAut W) * g'
        = ((d : MulAut W) * (d₀ : MulAut W)⁻¹) * g := by
      change (d : MulAut W) * ((d₀ : MulAut W)⁻¹ * g)
        = ((d : MulAut W) * (d₀ : MulAut W)⁻¹) * g
      rw [mul_assoc]
    have hg'd : g' * (d : MulAut W)
        = ((d₀ : MulAut W)⁻¹ * (d : MulAut W)) * g := by
      change ((d₀ : MulAut W)⁻¹ * g) * (d : MulAut W)
        = ((d₀ : MulAut W)⁻¹ * (d : MulAut W)) * g
      rw [mul_assoc, ← hg (d : MulAut W) d.2, ← mul_assoc]
    rw [hdg', hg'd, hcommD]
  have hg'fix : ∀ d : ↥D, g' ((d : MulAut W) u₀) = (d : MulAut W) u₀ := by
    intro d
    have hcomm := hg'comm d
    calc g' ((d : MulAut W) u₀) = (g' * (d : MulAut W)) u₀ := rfl
      _ = ((d : MulAut W) * g') u₀ := by rw [← hcomm]
      _ = (d : MulAut W) (g' u₀) := rfl
      _ = (d : MulAut W) u₀ := by rw [hg'u0]
  have hfixS : ∀ w ∈ Subgroup.closure (Set.range f), g' w = w := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨d, hd⟩ := hx
        rw [← hd]
        exact hg'fix d
    | one => exact map_one g'
    | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]
    | inv x hx ih => rw [map_inv, ih]
  have hStop : Subgroup.closure (Set.range f) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have hSdvd : Nat.card ↥(Subgroup.closure (Set.range f)) ∣ 2 ^ 4 := by
      rw [show (2 : ℕ) ^ 4 = Nat.card W from hcard.symm]
      exact Subgroup.card_subgroup_dvd_card _
    have hSge : 10 ≤ Nat.card ↥(Subgroup.closure (Set.range f)) := by
      have hsub : Set.range f ∪ {1} ⊆ (Subgroup.closure (Set.range f) : Set W) := by
        intro w hw
        rcases hw with hw | hw
        · exact Subgroup.subset_closure hw
        · rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact Subgroup.one_mem _
      have hcu : (Set.range f ∪ {1}).ncard = 10 := by
        rw [Set.ncard_union_eq (Set.disjoint_singleton_right.mpr h1O), hOcard,
          Set.ncard_singleton]
      have hle := Set.ncard_le_ncard hsub
      rw [hcu, ← Nat.card_coe_set_eq] at hle
      exact hle
    have hS16 : Nat.card ↥(Subgroup.closure (Set.range f)) = 16 := by
      obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow (p := 2) (by norm_num) (m := 4)).mp hSdvd
      have hge2 : 10 ≤ 2 ^ k := by rw [← hk]; exact hSge
      have hk_eq : k = 4 := by
        interval_cases k
        · norm_num at hge2
        · norm_num at hge2
        · norm_num at hge2
        · norm_num at hge2
        · rfl
      rw [hk, hk_eq]
      norm_num
    rw [hS16, hcard]
    norm_num
  have hg'one : g' = 1 := by
    ext w
    rw [MulAut.one_apply]
    exact hfixS w (by rw [hStop]; exact Subgroup.mem_top w)
  have hg_eq : g = (d₀ : MulAut W) := by
    have h : (d₀ : MulAut W)⁻¹ * g = 1 := hg'one
    exact (inv_mul_eq_one.mp h).symm
  rw [hg_eq]
  exact d₀.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
