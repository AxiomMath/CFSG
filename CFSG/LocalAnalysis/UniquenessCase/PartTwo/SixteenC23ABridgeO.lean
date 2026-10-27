module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ABridgeP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ABridgeC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem c23a_bridgeo_preTil_mono {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {S T : Subgroup (Vtil (⊥ : Subgroup G) V hV)} (h : S ≤ T) :
    preTil (⊥ : Subgroup G) V hV S ≤ preTil (⊥ : Subgroup G) V hV T := by
  intro g hg
  obtain ⟨x, rfl, hx⟩ := (mem_preTil (⊥ : Subgroup G) V hV S).1 hg
  exact (mem_preTil (⊥ : Subgroup G) V hV T).2 ⟨x, rfl, h hx⟩

theorem c23a_bridge_oneSided {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G))
    {L₁ L₂ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV))}
    {E₁ E₂ Z₁ Z₂ : Subgroup (Vtil (⊥ : Subgroup G) V hV)}
    (hP : C23AModPair (barSub (⊥ : Subgroup G) V hV M) L₁ L₂ E₁ E₂ Z₁ Z₂) :
    ∀ t ∈ M, (∃ j : ℕ, orderOf t = 2 ^ j) → ¬ V ≤ centralizer ({t} : Set G) →
      mSub (commElt V t) ≤ 2 →
        (((∀ y ∈ preTil (⊥ : Subgroup G) V hV E₂, t * y = y * t) ∧
            commElt V t ≤ preTil (⊥ : Subgroup G) V hV E₁) ∨
          ((∀ y ∈ preTil (⊥ : Subgroup G) V hV E₁, t * y = y * t) ∧
            commElt V t ≤ preTil (⊥ : Subgroup G) V hV E₂)) ∧
        2 ≤ mSub (commElt V t) := by
  intro t htM ht2 hnc hm
  have hM₀ : M ≤ normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hts : t ∈ stabTil (⊥ : Subgroup G) V := (le_stabTil hM hM₀) htM
  set τ : MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    actTil (⊥ : Subgroup G) V hV ⟨t, hts⟩ with hτ
  have hτ2 : ∃ j : ℕ, orderOf τ = 2 ^ j := by
    obtain ⟨j, hj⟩ := ht2
    have h1 : orderOf (actTil (⊥ : Subgroup G) V hV ⟨t, hts⟩) ∣
        orderOf (⟨t, hts⟩ : ↥(stabTil (⊥ : Subgroup G) V)) :=
      orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf τ ∣ 2 ^ j := by
      rw [hτ]
      rw [hj] at h1
      exact h1
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact ⟨a, ha⟩
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hnc
    have h1' : actTil (⊥ : Subgroup G) V hV ⟨t, hts⟩ = 1 := by
      rw [← hτ]
      exact h1
    have hone : ∀ v ∈ V, t * v * t⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) :=
      (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨t, hts⟩).1 h1'
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : t * v * t⁻¹ = v :=
      mul_inv_eq_one.1 (Subgroup.mem_bot.1 (hone v hv))
    calc v * t = (t * v * t⁻¹) * t := by rw [hconj]
      _ = t * v := by group
  have hτmem : τ ∈ barSub (⊥ : Subgroup G) V hV M := by
    rw [hτ]
    exact actTil_mem_barSub (⊥ : Subgroup G) V hV htM hts
  have hC : preTil (⊥ : Subgroup G) V hV (commSub ⊤ (Subgroup.zpowers τ)) = commElt V t := by
    rw [hτ]
    exact c23a_preTil_commSub_zpowers hV hts
  have hmSub : mSub (commElt V t) = rk ↥(commSub ⊤ (Subgroup.zpowers τ)) := by
    rw [← hC]
    exact c23a_bridge_mSub hV (commSub ⊤ (Subgroup.zpowers τ))
  have hr : rk ↥(commSub ⊤ (Subgroup.zpowers τ)) ≤ 2 := by
    rw [← hmSub]
    exact hm
  have hmain := c23a_modPair_oneSided hP hτmem hτ2 hτ1 hr
  have key : ∀ {E : Subgroup (Vtil (⊥ : Subgroup G) V hV)},
      (∀ y ∈ E, τ y = y) → ∀ y ∈ preTil (⊥ : Subgroup G) V hV E, t * y = y * t := by
    intro E hfix y hy
    have hyV : y ∈ V := preTil_le (⊥ : Subgroup G) V hV E hy
    have hu : mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨y, hyV⟩) ∈ E :=
      (mem_preTil_iff_of_mem (⊥ : Subgroup G) V hV E hyV).1 hy
    have hfy := hfix _ hu
    have hfy' : mkTil (⊥ : Subgroup G) V hV
        (actStab (⊥ : Subgroup G) V hV ⟨t, hts⟩ (IntMod.mk hV ⟨y, hyV⟩)) =
        mkTil (⊥ : Subgroup G) V hV (IntMod.mk hV ⟨y, hyV⟩) := by
      rw [hτ, actTil_mk] at hfy
      exact hfy
    have hmem := (mkTil_eq_iff (⊥ : Subgroup G) V hV _ _).1 hfy'
    have hval : ((IntMod.mk hV ⟨y, hyV⟩ : IntMod V hV)).val = y := rfl
    rw [actStab_apply_val, hval] at hmem
    have hconj : t * y * t⁻¹ = y :=
      mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)
    calc t * y = (t * y * t⁻¹) * t := by group
      _ = y * t := by rw [hconj]
  refine ⟨?_, ?_⟩
  · rcases hmain.1 with ⟨hfixA, hleA⟩ | ⟨hfixB, hleB⟩
    · exact Or.inl ⟨key hfixA, by
        rw [← hC]
        exact c23a_bridgeo_preTil_mono hV hleA⟩
    · exact Or.inr ⟨key hfixB, by
        rw [← hC]
        exact c23a_bridgeo_preTil_mono hV hleB⟩
  · rw [hmSub]
    exact hmain.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
