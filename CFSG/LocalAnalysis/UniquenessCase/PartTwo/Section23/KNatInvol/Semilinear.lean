module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def SemilinearNormalizer (Γ : Subgroup (GL ι K)) : Prop :=
  ∀ σ : (ι → K) ≃+ (ι → K),
    (∀ γ ∈ Γ, ∃ γ' ∈ Γ, ∀ v : ι → K,
      (γ : Matrix ι ι K) *ᵥ σ v = σ ((γ' : Matrix ι ι K) *ᵥ v)) →
    ∀ c : K, ∃ c' : K, ∀ v : ι → K, σ (c • v) = c' • σ v

theorem semilinearNormalizer_of_addCommutantScalar {Γ : Subgroup (GL ι K)}
    (h : CFSG.RankThree.GF2n.Stroth80.AddCommutantScalar Γ) : SemilinearNormalizer Γ := by
  intro σ hσ c
  let f : (ι → K) →+ (ι → K) :=
    { toFun := fun v => σ (c • σ.symm v)
      map_zero' := by simp
      map_add' := fun v w => by simp [smul_add] }
  have hfv : ∀ v : ι → K, f v = σ (c • σ.symm v) := fun _ => rfl
  have hf : ∀ A ∈ Γ, ∀ v : ι → K,
      f ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v := by
    intro A hA v
    obtain ⟨A', -, hA'v⟩ := hσ A hA
    have hs : (A' : Matrix ι ι K) *ᵥ σ.symm v = σ.symm ((A : Matrix ι ι K) *ᵥ v) := by
      have hv : (A : Matrix ι ι K) *ᵥ v = σ ((A' : Matrix ι ι K) *ᵥ σ.symm v) := by
        simpa using hA'v (σ.symm v)
      rw [hv, AddEquiv.symm_apply_apply]
    calc f ((A : Matrix ι ι K) *ᵥ v)
        = σ (c • ((A' : Matrix ι ι K) *ᵥ σ.symm v)) := by rw [hfv, ← hs]
      _ = σ ((A' : Matrix ι ι K) *ᵥ (c • σ.symm v)) := by rw [Matrix.mulVec_smul]
      _ = (A : Matrix ι ι K) *ᵥ σ (c • σ.symm v) := by rw [hA'v (c • σ.symm v)]
      _ = (A : Matrix ι ι K) *ᵥ f v := by rw [hfv]
  obtain ⟨c', hc'⟩ := h f hf
  refine ⟨c', fun v => ?_⟩
  have h := hc' (σ v)
  rwa [hfv, AddEquiv.symm_apply_apply] at h

theorem semilinearNormalizer_of_card_eq_two [Finite K] (hK : Nat.card K = 2)
    (Γ : Subgroup (GL ι K)) : SemilinearNormalizer Γ := by
  classical
  have hc : ∀ c : K, c = 0 ∨ c = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : (Finset.univ : Finset K).card = ({0, 1} : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      simp
    have heq : ({0, 1} : Finset K) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (le_of_eq hcard)
    intro c
    have hmem : c ∈ ({0, 1} : Finset K) := by rw [heq]; exact Finset.mem_univ c
    simpa using hmem
  intro σ _ c
  refine ⟨c, fun v => ?_⟩
  rcases hc c with rfl | rfl <;> simp

private theorem card_le_index_of_forall_smul [Finite K] (σ : (ι → K) ≃+ (ι → K))
    (h : ∀ (c : K) (v : ι → K), σ (c • v) = c • σ v) {v₀ : ι → K} (hv₀ : σ v₀ ≠ v₀)
    (C : AddSubgroup (ι → K)) (hC : ∀ v, v ∈ C ↔ σ v = v) : Nat.card K ≤ C.index := by
  have hCsmul : ∀ (c : K) {v : ι → K}, v ∈ C → c • v ∈ C := by
    intro c v hv
    rw [hC (c • v), h c v, (hC v).mp hv]
  have hinj : Function.Injective
      (fun c : K => (QuotientAddGroup.mk (c • v₀) : (ι → K) ⧸ C)) := by
    intro c c' hcc'
    have hmem : c • v₀ - c' • v₀ ∈ C := QuotientAddGroup.eq_iff_sub_mem.mp hcc'
    rw [← sub_smul] at hmem
    by_contra hne
    have hd : c - c' ≠ 0 := sub_ne_zero.mpr hne
    have hvC : v₀ ∈ C := by
      have hc := hCsmul (c - c')⁻¹ hmem
      rwa [inv_smul_smul₀ hd] at hc
    exact hv₀ ((hC v₀).mp hvC)
  have hle := Nat.card_le_card_of_injective _ hinj
  simpa only [AddSubgroup.index_eq_card] using hle

private theorem card_sq_le_card_of_not_forall_smul [Finite K] (σ : (ι → K) ≃+ (ι → K))
    (hsemi : ∀ c : K, ∃ c' : K, ∀ v : ι → K, σ (c • v) = c' • σ v)
    (h : ¬ ∀ (c : K) (v : ι → K), σ (c • v) = c • σ v) (C : AddSubgroup (ι → K))
    (hC : ∀ v, v ∈ C ↔ σ v = v) : Nat.card C * Nat.card C ≤ Nat.card (ι → K) := by
  obtain ⟨θ, hθ⟩ := not_forall.mp h
  obtain ⟨v₁, hθv₁⟩ := not_forall.mp hθ
  obtain ⟨θ', hθ'⟩ := hsemi θ
  have hθ'ne : θ' ≠ θ := by
    intro heq
    exact hθv₁ (by rw [hθ' v₁, heq])
  have hinj : Function.Injective
      (fun p : C × C => (p.1 : ι → K) + θ • (p.2 : ι → K)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ heq
    have heq' : a + θ • b = a' + θ • b' := heq
    have hw : (b' - b : ι → K) ∈ C := C.sub_mem hb' hb
    have h1 : θ • (b' - b : ι → K) = a - a' := by
      rw [smul_sub, sub_eq_sub_iff_add_eq_add, heq', add_comm]
    have h1C : θ • (b' - b : ι → K) ∈ C := by
      rw [h1]
      exact C.sub_mem ha ha'
    have h3 : σ (θ • (b' - b : ι → K)) = θ • (b' - b : ι → K) := (hC _).mp h1C
    have hθw : θ • (b' - b : ι → K) = θ' • (b' - b : ι → K) := by
      rw [← h3, hθ' (b' - b), (hC (b' - b)).mp hw]
    have h4 : (θ - θ') • (b' - b : ι → K) = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact hθw
    have hθd : θ - θ' ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ'ne)
    have hw0 : b' - b = 0 := by
      have hc := congrArg (fun x : ι → K => (θ - θ')⁻¹ • x) h4
      simpa [inv_smul_smul₀ hθd] using hc
    have hb_eq : b' = b := sub_eq_zero.mp hw0
    have ha_eq : a = a' := by
      have hh := heq'
      rw [hb_eq] at hh
      exact add_right_cancel hh
    exact Prod.ext (Subtype.ext ha_eq) (Subtype.ext hb_eq.symm)
  have hle := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at hle

theorem card_le_index_of_semilinear [Finite K] (hι : 2 ≤ Fintype.card ι)
    (σ : (ι → K) ≃+ (ι → K)) (hsemi : ∀ c : K, ∃ c' : K, ∀ v : ι → K, σ (c • v) = c' • σ v)
    {v₀ : ι → K} (hv₀ : σ v₀ ≠ v₀) (C : AddSubgroup (ι → K)) (hC : ∀ v, v ∈ C ↔ σ v = v) :
    Nat.card K ≤ C.index := by
  by_cases h : ∀ (c : K) (v : ι → K), σ (c • v) = c • σ v
  · exact card_le_index_of_forall_smul σ h hv₀ C hC
  · have hcard := card_sq_le_card_of_not_forall_smul σ hsemi h C hC
    have hN : Nat.card (ι → K) = Nat.card K ^ Fintype.card ι := by
      haveI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hqpos : 0 < Nat.card K := Nat.card_pos
    have hq2 : Nat.card K ^ 2 ≤ Nat.card (ι → K) := by
      rw [hN]
      exact Nat.pow_le_pow_right hqpos hι
    have hI : C.index * Nat.card C = Nat.card (ι → K) := AddSubgroup.index_mul_card C
    have hdpos : 0 < Nat.card C := by
      haveI : Nonempty C := ⟨0, C.zero_mem⟩
      exact Nat.card_pos
    have hdI : Nat.card C ≤ C.index := by
      rw [← hI] at hcard
      exact Nat.le_of_mul_le_mul_right hcard hdpos
    have hI2 : Nat.card K ^ 2 ≤ C.index ^ 2 := by
      calc Nat.card K ^ 2 ≤ Nat.card (ι → K) := hq2
        _ = C.index * Nat.card C := hI.symm
        _ ≤ C.index * C.index := Nat.mul_le_mul_left _ hdI
        _ = C.index ^ 2 := (pow_two _).symm
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hI2

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatInvol
