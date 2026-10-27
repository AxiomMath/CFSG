module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UComb

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

@[expose] def gramDet3 (x y z : Fin τ.rank → ℤ) : ℤ :=
  8 + 2 * (iform x y * iform x z * iform y z) -
    2 * (iform x y ^ 2 + iform x z ^ 2 + iform y z ^ 2)

theorem iform_neg_right_eq_neg
    (x y : Fin τ.rank → ℤ) : iform x (-y) = - iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

theorem iform_neg_left_eq_neg
    (x y : Fin τ.rank → ℤ) : iform (-x) y = - iform x y := by
  rw [iform_comm, iform_neg_right_eq_neg, iform_comm]

theorem vec_eq_zero_of_iform_self_eq_zero
    {x : Fin τ.rank → ℤ} (h : iform x x = 0) : x = 0 := by
  by_contra hx
  exact (iform_self_pos hx).ne' h

theorem iform_comb3
    (α β x : Fin τ.rank → ℤ) (p q r : ℤ) :
    iform (p • α + q • β + r • x) (p • α + q • β + r • x) =
      p ^ 2 * iform α α + q ^ 2 * iform β β + r ^ 2 * iform x x +
        2 * p * q * iform α β + 2 * p * r * iform α x + 2 * q * r * iform β x := by
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right]
  rw [iform_comm β α, iform_comm x α, iform_comm x β]
  ring

theorem abs_iform_le_one
    {x y : Fin τ.rank → ℤ} (hx : iform x x = 2) (hy : iform y y = 2)
    (h1 : y ≠ x) (h2 : y ≠ -x) : -1 ≤ iform x y ∧ iform x y ≤ 1 := by
  have hsub : iform (x - y) (x - y) = 4 - 2 * iform x y := by
    simp only [iform_sub_left, iform_sub_right]
    rw [iform_comm y x, hx, hy]
    ring
  have hadd : iform (x + y) (x + y) = 4 + 2 * iform x y := by
    simp only [iform_add_left, iform_add_right]
    rw [iform_comm y x, hx, hy]
    ring
  have hxy : x - y ≠ 0 := fun h => h1 (sub_eq_zero.1 h).symm
  have hxy' : x + y ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_right h)
  have p1 := iform_self_pos hxy
  have p2 := iform_self_pos hxy'
  omega

theorem gram3_dependent
    {α β : Fin τ.rank → ℤ} (hα : iform α α = 2) (hβ : iform β β = 2) :
    gramDet3 α β α = 0 ∧ gramDet3 α β (-α) = 0 ∧ gramDet3 α β β = 0 ∧ gramDet3 α β (-β) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gramDet3, hα, iform_comm β α]
    ring
  · simp only [gramDet3, iform_neg_right_eq_neg, hα, iform_comm β α]
    ring
  · simp only [gramDet3, hβ]
    ring
  · simp only [gramDet3, iform_neg_right_eq_neg, hβ]
    ring

theorem three_smul_mem_span_of_gram3_eq_zero
    {α β x : Fin τ.rank → ℤ} (hα : iform α α = 2)
    (hβ : iform β β = 2) (hx : iform x x = 2) (hs : iform α β ^ 2 = 1)
    (hg : gramDet3 α β x = 0) :
    (3 : ℤ) • x = (2 * iform α x - iform α β * iform β x) • α +
      (2 * iform β x - iform α β * iform α x) • β := by
  set s := iform α β with hsdef
  set b := iform α x with hb
  set c := iform β x with hc
  have hw : iform ((-(2 * b - s * c)) • α + (-(2 * c - s * b)) • β + (3 : ℤ) • x)
      ((-(2 * b - s * c)) • α + (-(2 * c - s * b)) • β + (3 : ℤ) • x) = 0 := by
    rw [iform_comb3, hα, hβ, hx]
    have h3 : gramDet3 α β x = 8 + 2 * (s * b * c) - 2 * (s ^ 2 + b ^ 2 + c ^ 2) := rfl
    have hs3 : s ^ 2 = 1 := hs
    nlinarith [h3, hg, hs3]
  have hz := vec_eq_zero_of_iform_self_eq_zero hw
  have hz' : (3 : ℤ) • x = (2 * b - s * c) • α + (2 * c - s * b) • β := by
    have := congrArg (fun v => v + ((2 * b - s * c) • α + (2 * c - s * b) • β)) hz
    simp only [zero_add] at this
    rw [← this]
    simp only [neg_smul]
    abel
  exact hz'

theorem exists_path_of_three_le_finrank
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hnorm : ∀ x ∈ Ψ, iform x x = 2) (h3 : 3 ≤ Module.finrank ℤ (Submodule.span ℤ Ψ)) :
    ∃ α ∈ Ψ, ∃ β ∈ Ψ, ∃ γ ∈ Ψ, β ≠ α ∧ β ≠ -α ∧ iform α β ≠ 0 ∧
      (iform α γ ≠ 0 ∨ iform β γ ≠ 0) ∧ gramDet3 α β γ ≠ 0 := by
  classical
  obtain ⟨α, hα, β, hβ, hne1, hne2, hs⟩ := exists_pair_ne_of_two_le_finrank_span hΨ (by omega)
  by_contra hcon
  push Not at hcon
  have hα2 := hnorm α hα
  have hβ2 := hnorm β hβ
  have hs1 : iform α β ^ 2 = 1 := by
    obtain ⟨hl, hu⟩ := abs_iform_le_one hα2 hβ2 hne1 hne2
    have : iform α β = 1 ∨ iform α β = -1 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  have horth : ∀ γ ∈ Ψ, gramDet3 α β γ ≠ 0 → iform α γ = 0 ∧ iform β γ = 0 := by
    intro γ hγ hg
    by_contra hnot
    exact hg (hcon α hα β hβ γ hγ hne1 hne2 hs (not_and_or.1 hnot))
  have hmem3 : ∀ x ∈ Ψ, gramDet3 α β x = 0 →
      (3 : ℤ) • x ∈ Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ)) := by
    intro x hx hg
    rw [three_smul_mem_span_of_gram3_eq_zero hα2 hβ2 (hnorm x hx) hs1 hg]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hSorth : ∀ a ∈ {x ∈ Ψ | gramDet3 α β x = 0}, ∀ b ∈ Ψ,
      b ∉ {x ∈ Ψ | gramDet3 α β x = 0} → iform a b = 0 := by
    intro a ha b hb hbS
    have hb0 : gramDet3 α β b ≠ 0 := fun h => hbS ⟨hb, h⟩
    obtain ⟨hαb, hβb⟩ := horth b hb hb0
    have heq := three_smul_mem_span_of_gram3_eq_zero hα2 hβ2 (hnorm a ha.1) hs1 ha.2
    have := congrArg (fun v => iform v b) heq
    simp only [iform_smul_left, iform_add_left, hαb, hβb] at this
    omega
  have hsub : {x ∈ Ψ | gramDet3 α β x = 0} ⊆ Ψ := fun x hx => hx.1
  rcases hΨ.irreducible _ hsub hSorth with hS | hS
  · exact absurd hS (Set.nonempty_iff_ne_empty.1 ⟨α, hα, (gram3_dependent hα2 hβ2).1⟩)
  · have hall : ∀ x ∈ Ψ, gramDet3 α β x = 0 := fun x hx => by
      have : x ∈ {x ∈ Ψ | gramDet3 α β x = 0} := by rw [hS]; exact hx
      exact this.2
    let f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ) := (3 : ℤ) • LinearMap.id
    have hfinj : Function.Injective f := fun u v h =>
      smul_right_injective _ (by norm_num : (3 : ℤ) ≠ 0) h
    have hsp : Submodule.span ℤ Ψ ≤ (Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))).comap f := by
      rw [Submodule.span_le]
      intro x hx
      exact hmem3 x hx (hall x hx)
    let g : Submodule.span ℤ Ψ →ₗ[ℤ] Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ)) :=
      LinearMap.codRestrict _ (f.domRestrict (Submodule.span ℤ Ψ)) (fun x => hsp x.2)
    have hg : Function.Injective g := fun u v h =>
      Subtype.ext (hfinj (congrArg Subtype.val h))
    have hle : Module.finrank ℤ (Submodule.span ℤ Ψ) ≤ 2 := by
      calc Module.finrank ℤ (Submodule.span ℤ Ψ)
          ≤ Module.finrank ℤ (Submodule.span ℤ ({α, β} : Set (Fin τ.rank → ℤ))) :=
            LinearMap.finrank_le_finrank_of_injective hg
        _ ≤ 2 := by
          have h := finrank_span_finset_le_card (R := ℤ) ({α, β} : Finset (Fin τ.rank → ℤ))
          rw [Finset.coe_insert, Finset.coe_singleton] at h
          exact h.trans Finset.card_le_two
    omega

theorem gram3_eq_four
    {α β γ : Fin τ.rank → ℤ} (hα : iform α α = 2) (hβ : iform β β = 2)
    (hγ : iform γ γ = 2) (hne1 : β ≠ α) (hne2 : β ≠ -α) (hs : iform α β ≠ 0)
    (hbc : iform α γ ≠ 0 ∨ iform β γ ≠ 0) (hg : gramDet3 α β γ ≠ 0) : gramDet3 α β γ = 4 := by
  obtain ⟨hdep1, hdep2, hdep3, hdep4⟩ := gram3_dependent hα hβ
  have hγ1 : γ ≠ α := fun h => hg (h ▸ hdep1)
  have hγ2 : γ ≠ -α := fun h => hg (h ▸ hdep2)
  have hγ3 : γ ≠ β := fun h => hg (h ▸ hdep3)
  have hγ4 : γ ≠ -β := fun h => hg (h ▸ hdep4)
  obtain ⟨ha1, ha2⟩ := abs_iform_le_one hα hβ hne1 hne2
  obtain ⟨hb1, hb2⟩ := abs_iform_le_one hα hγ hγ1 hγ2
  obtain ⟨hc1, hc2⟩ := abs_iform_le_one hβ hγ hγ3 hγ4
  have key : ∀ a b c : ℤ, -1 ≤ a → a ≤ 1 → a ≠ 0 → -1 ≤ b → b ≤ 1 → -1 ≤ c → c ≤ 1 →
      (b ≠ 0 ∨ c ≠ 0) → 8 + 2 * (a * b * c) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≠ 0 →
      8 + 2 * (a * b * c) - 2 * (a ^ 2 + b ^ 2 + c ^ 2) = 4 := by
    intro a b c h1 h2 h3 h4 h5 h6 h7 h8 h9
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all
  exact key _ _ _ ha1 ha2 hs hb1 hb2 hc1 hc2 hbc hg

end CFSG.StandardType.TableCRes
