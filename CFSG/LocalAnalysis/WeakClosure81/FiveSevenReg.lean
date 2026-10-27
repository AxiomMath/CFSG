module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

lemma b5_FiveSevenReg_even_swap_mul_swap {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    {x y z w : Δ} (hxy : x ≠ y) (hzw : z ≠ w) :
    Equiv.swap x y * Equiv.swap z w ∈ alternatingGroup Δ :=
  Perm.mul_mem_alternatingGroup_of_isSwap (Perm.swap_isSwap_iff.2 hxy)
    (Perm.swap_isSwap_iff.2 hzw)

lemma b5_FiveSevenReg_swap_mem_iff_of_mem {Δ : Type*} [DecidableEq Δ] {s : Set Δ} {u v : Δ}
    (hu : u ∈ s) (hv : v ∈ s) (x : Δ) : Equiv.swap u v x ∈ s ↔ x ∈ s := by
  by_cases hx : x = u
  · rw [hx, Equiv.swap_apply_left]
    exact ⟨fun _ => hu, fun _ => hv⟩
  · by_cases hy : x = v
    · rw [hy, Equiv.swap_apply_right]
      exact ⟨fun _ => hv, fun _ => hu⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma b5_FiveSevenReg_swap_mem_iff_of_notMem {Δ : Type*} [DecidableEq Δ] {s : Set Δ} {u v : Δ}
    (hu : u ∉ s) (hv : v ∉ s) (x : Δ) : Equiv.swap u v x ∈ s ↔ x ∈ s := by
  by_cases hx : x = u
  · rw [hx, Equiv.swap_apply_left]
    exact ⟨fun h => absurd h hv, fun h => absurd h hu⟩
  · by_cases hy : x = v
    · rw [hy, Equiv.swap_apply_right]
      exact ⟨fun h => absurd h hu, fun h => absurd h hv⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

theorem exists_smul_eq_of_maxOver_eq_stabilizer {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    {K A : Subgroup (Perm Δ)} (hAlt : alternatingGroup Δ ≤ K) (hAne : A ≠ ⊥) {α : Δ}
    (hM : maxOver K A = {K ⊓ MulAction.stabilizer (Perm Δ) α}) :
    (∀ a ∈ A, a α = α) ∧ ∀ β γ : Δ, β ≠ α → γ ≠ α → ∃ a ∈ A, a β = γ := by
  obtain ⟨_, hAM, hu⟩ := isUniqueMaxOver_iff.1 hM
  have hfix : ∀ a ∈ A, a α = α := by
    intro a ha
    have hmem : a ∈ MulAction.stabilizer (Perm Δ) α := (Subgroup.mem_inf.1 (hAM ha)).2
    rw [MulAction.mem_stabilizer_iff] at hmem
    rwa [Perm.smul_def] at hmem
  obtain ⟨a₁, ha₁⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  have ha₁perm : (a₁ : Perm Δ) ≠ 1 := fun h => ha₁ (Subtype.ext h)
  have hex : ∃ β₀ : Δ, (a₁ : Perm Δ) β₀ ≠ β₀ := by
    by_contra h
    apply ha₁perm
    ext x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨β₀, hβ₀⟩ := hex
  have hβ₀α : β₀ ≠ α := by
    intro h
    exact hβ₀ (by rw [h]; exact hfix (a₁ : Perm Δ) a₁.2)
  let β₁ : Δ := (a₁ : Perm Δ) β₀
  let Γ : Set Δ := {x | ∃ a ∈ A, a β₀ = x}
  have hβ₀Γ : β₀ ∈ Γ := ⟨1, A.one_mem, rfl⟩
  have hβ₁Γ : β₁ ∈ Γ := ⟨(a₁ : Perm Δ), a₁.2, rfl⟩
  have hαΓ : α ∉ Γ := by
    rintro ⟨a, ha, haα⟩
    exact hβ₀α (a.injective (haα.trans (hfix a ha).symm))
  have hAΓ : ∀ a ∈ A, ∀ x, a x ∈ Γ ↔ x ∈ Γ := by
    intro a ha x
    constructor
    · rintro ⟨b, hb, hbx⟩
      refine ⟨a⁻¹ * b, A.mul_mem (A.inv_mem ha) hb, ?_⟩
      rw [Perm.mul_apply, hbx]
      simp
    · rintro ⟨b, hb, hbx⟩
      exact ⟨a * b, A.mul_mem ha hb, by rw [Perm.mul_apply, hbx]⟩
  let N' : Subgroup (Perm Δ) :=
    { carrier := {k | ∀ x, k x ∈ Γ ↔ x ∈ Γ}
      one_mem' := by intro x; rfl
      mul_mem' := by
        intro k₁ k₂ h₁ h₂ x
        rw [Perm.mul_apply]
        exact (h₁ (k₂ x)).trans (h₂ x)
      inv_mem' := by
        intro k hk x
        have h := hk (k⁻¹ x)
        have hx : k (k⁻¹ x) = x := Equiv.apply_symm_apply k x
        rw [hx] at h
        exact h.symm }
  have hAN' : A ≤ N' := fun a ha => hAΓ a ha
  have hAK : A ≤ K := hAM.trans inf_le_left
  have hAinf : A ≤ K ⊓ N' := le_inf hAK hAN'
  have hclaim : ∀ δ, δ ≠ α → δ ∈ Γ := by
    intro δ hδα
    by_contra hδΓ
    have hβ₀δ : β₀ ≠ δ := fun h => hδΓ (h ▸ hβ₀Γ)
    have hcK : Equiv.swap β₀ δ * Equiv.swap δ α ∈ K :=
      hAlt (b5_FiveSevenReg_even_swap_mul_swap hβ₀δ hδα)
    have hcβ₀ : (Equiv.swap β₀ δ * Equiv.swap δ α) β₀ = δ := by
      rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hβ₀δ hβ₀α, Equiv.swap_apply_left]
    have hcN' : Equiv.swap β₀ δ * Equiv.swap δ α ∉ N' := by
      intro hc
      have hmem : (Equiv.swap β₀ δ * Equiv.swap δ α) β₀ ∈ Γ := (hc β₀).2 hβ₀Γ
      rw [hcβ₀] at hmem
      exact hδΓ hmem
    have hne : K ⊓ N' ≠ K := by
      intro h
      have : Equiv.swap β₀ δ * Equiv.swap δ α ∈ K ⊓ N' := by rw [h]; exact hcK
      exact hcN' this.2
    have hlt : K ⊓ N' < K := lt_of_le_of_ne inf_le_left hne
    obtain ⟨N, hNmax, hNin⟩ := exists_isMaxSubgroupIn hlt
    have hAN : A ≤ N := hAinf.trans hNin
    have hNM : N = K ⊓ MulAction.stabilizer (Perm Δ) α := hu N hNmax hAN
    have hN'M : K ⊓ N' ≤ MulAction.stabilizer (Perm Δ) α :=
      (hNin.trans (le_of_eq hNM)).trans inf_le_right
    have hαβ₀ : α ≠ β₀ := hβ₀α.symm
    have hαβ₁ : α ≠ β₁ := fun h => hαΓ (h.symm ▸ hβ₁Γ)
    have hgK : Equiv.swap α δ * Equiv.swap β₀ β₁ ∈ K :=
      hAlt (b5_FiveSevenReg_even_swap_mul_swap hδα.symm hβ₀.symm)
    have hgN' : Equiv.swap α δ * Equiv.swap β₀ β₁ ∈ N' := by
      intro x
      rw [Perm.mul_apply]
      exact (b5_FiveSevenReg_swap_mem_iff_of_notMem hαΓ hδΓ (Equiv.swap β₀ β₁ x)).trans
        (b5_FiveSevenReg_swap_mem_iff_of_mem hβ₀Γ hβ₁Γ x)
    have hgα : (Equiv.swap α δ * Equiv.swap β₀ β₁) α = δ := by
      rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hαβ₀ hαβ₁, Equiv.swap_apply_left]
    have hgstab : Equiv.swap α δ * Equiv.swap β₀ β₁ ∉ MulAction.stabilizer (Perm Δ) α := by
      intro h
      rw [MulAction.mem_stabilizer_iff, Perm.smul_def] at h
      exact hδα (hgα.symm.trans h)
    exact hgstab (hN'M ⟨hgK, hgN'⟩)
  have hΓeq : Γ = {x | x ≠ α} := by
    ext x
    exact ⟨fun hx h => hαΓ (h ▸ hx), fun hx => hclaim x hx⟩
  refine ⟨hfix, ?_⟩
  intro β γ hβ hγ
  have hβΓ : β ∈ Γ := by rw [hΓeq]; exact hβ
  have hγΓ : γ ∈ Γ := by rw [hΓeq]; exact hγ
  obtain ⟨b, hbA, hb⟩ := hβΓ
  obtain ⟨b', hb'A, hb'⟩ := hγΓ
  refine ⟨b' * b⁻¹, A.mul_mem hb'A (A.inv_mem hbA), ?_⟩
  have hbinv : b⁻¹ β = β₀ := by rw [← hb]; exact Equiv.symm_apply_apply b β₀
  rw [Perm.mul_apply, hbinv, hb']

theorem existsUnique_smul_eq_of_isMulCommutative {Δ : Type*} {A : Subgroup (Perm Δ)}
    (hA : IsMulCommutative ↥A) {α : Δ} (hfix : ∀ a ∈ A, a α = α)
    (htrans : ∀ β γ : Δ, β ≠ α → γ ≠ α → ∃ a ∈ A, a β = γ) :
    ∀ β γ : Δ, β ≠ α → γ ≠ α → ∃! a : ↥A, (a : Perm Δ) β = γ := by
  intro β γ hβ hγ
  obtain ⟨a, haA, ha⟩ := htrans β γ hβ hγ
  refine ⟨⟨a, haA⟩, ha, fun b hb => ?_⟩
  have hb' : (b : Perm Δ) β = a β := hb.trans ha.symm
  have hcA : a⁻¹ * (b : Perm Δ) ∈ A := A.mul_mem (A.inv_mem haA) b.2
  have hcomm : ∀ d ∈ A, (a⁻¹ * (b : Perm Δ)) * d = d * (a⁻¹ * (b : Perm Δ)) := by
    intro d hd
    exact congrArg Subtype.val (hA.is_comm.comm (⟨_, hcA⟩ : ↥A) ⟨d, hd⟩)
  have hcβ : (a⁻¹ * (b : Perm Δ)) β = β := by
    rw [Perm.mul_apply, hb']
    simp
  have key : a⁻¹ * (b : Perm Δ) = 1 := by
    apply Equiv.ext
    intro x
    by_cases hx : x = α
    · rw [hx, Perm.mul_apply, hfix _ b.2, Equiv.Perm.one_apply, Equiv.Perm.inv_eq_iff_eq]
      exact (hfix a haA).symm
    · obtain ⟨d, hdA, hd⟩ := htrans β x hβ hx
      have h2 := congrArg (fun z : Perm Δ => z β) (hcomm d hdA)
      simp only [Perm.mul_apply, hcβ, hd] at h2
      rw [← hd]
      simpa [Perm.mul_apply, hd] using h2
  apply Subtype.ext
  exact (inv_mul_eq_one.1 key).symm

theorem card_eq_of_existsUnique_smul_eq {Δ : Type*} [Finite Δ] {A : Subgroup (Perm Δ)} {α : Δ}
    (h2 : 2 ≤ Nat.card Δ) (hfix : ∀ a ∈ A, a α = α)
    (hreg : ∀ β γ : Δ, β ≠ α → γ ≠ α → ∃! a : ↥A, (a : Perm Δ) β = γ) :
    Nat.card A = Nat.card Δ - 1 := by
  classical
  have hnt : Nontrivial Δ := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨β₀, hβ₀⟩ := exists_ne α
  have hne : ∀ a : ↥A, (a : Perm Δ) β₀ ≠ α := fun a h => hβ₀ (by
    apply (a : Perm Δ).injective
    rw [h, hfix a a.2])
  have hbij : Function.Bijective
      (fun a : ↥A => (⟨(a : Perm Δ) β₀, hne a⟩ : {y : Δ // y ≠ α})) := by
    constructor
    · intro a b hab
      have h1 : (a : Perm Δ) β₀ = (b : Perm Δ) β₀ := congrArg Subtype.val hab
      obtain ⟨c, -, hc⟩ := hreg β₀ ((a : Perm Δ) β₀) hβ₀ (hne a)
      exact (hc a rfl).trans (hc b h1.symm).symm
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha, -⟩ := hreg β₀ y hβ₀ hy
      exact ⟨a, Subtype.ext ha⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij)]
  have := Fintype.ofFinite Δ
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Set.card_ne_eq α

end CFSG.LocalAnalysis.WeakClosure81
