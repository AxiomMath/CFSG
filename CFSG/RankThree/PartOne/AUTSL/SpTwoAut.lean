module

public import CFSG.RankThree.PartOne.AUTSL.SpTwoCenter
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public noncomputable section

namespace CFSG.RankThree.PartOne.AUTSL.SpTwo

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.OutStructure

variable {K : Type} [Field K]

theorem exists_pointEquiv_two [Finite K] (h2 : (2 : K) ≠ 0)
    (α : MulAut (StatedProj (StatedSp 2 K))) :
    ∃ f : SpPoint 2 K ≃ SpPoint 2 K, ∀ L : SpPoint 2 K,
      (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K (f L).line := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ 2)
  have hη : Function.Injective fun L : SpPoint 2 K => projStabilizer 2 K L.line :=
    fun L M h => SpPoint.ext (hinj _ _ L.line_ne_bot (isTotallyIsotropic_line L)
      M.line_ne_bot (isTotallyIsotropic_line M) h)
  choose f₀ hf₀ using map_projStabilizer_point h2 α
  have hinj' : Function.Injective f₀ := fun L₁ L₂ h => by
    have h1 : (projStabilizer 2 K L₁.line).map α.toMonoidHom =
        (projStabilizer 2 K L₂.line).map α.toMonoidHom := by
      rw [hf₀, hf₀, h]
    exact hη (Subgroup.map_injective (f := α.toMonoidHom) α.injective h1)
  exact ⟨Equiv.ofBijective f₀ ⟨hinj', Finite.injective_iff_surjective.mp hinj'⟩, hf₀⟩

theorem automorphism_orthogonality_two [Finite K]
    (α : MulAut (StatedProj (StatedSp 2 K))) (f : SpPoint 2 K ≃ SpPoint 2 K)
    (hf : ∀ L : SpPoint 2 K,
      (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K (f L).line)
    (L M : SpPoint 2 K) : SpOrth L M ↔ SpOrth (f L) (f M) := by
  classical
  by_cases hLM : L = M
  · subst hLM
    exact ⟨fun _ => spOrth_self _, fun _ => spOrth_self _⟩
  have hfLM : f L ≠ f M := fun h => hLM (f.injective h)
  obtain ⟨hor, hnor, hlt⟩ := point_suborbit_indices (K := K) rfl (by omega : 2 ≤ 2)
  have hidx : (projStabilizer 2 K (f L).line ⊓ projStabilizer 2 K (f M).line).relIndex
      (projStabilizer 2 K (f L).line) =
      (projStabilizer 2 K L.line ⊓ projStabilizer 2 K M.line).relIndex
        (projStabilizer 2 K L.line) := by
    rw [← hf, ← hf, ← Subgroup.map_inf _ _ _ α.injective,
      Subgroup.relIndex_map_map_of_injective _ _ α.injective]
  have hlt' := (hlt (Nat.card K) Finite.one_lt_card).2
  constructor
  · intro h
    by_contra h'
    have e1 := hor L M hLM h
    have e2 := hnor (f L) (f M) hfLM h'
    rw [hidx, e1] at e2
    linarith
  · intro h
    by_contra h'
    have e1 := hor (f L) (f M) hfLM h
    have e2 := hnor L M hLM h'
    rw [hidx, e2] at e1
    linarith

theorem automorphism_generation_two [Finite K] (h2 : (2 : K) ≠ 0) :
    spSemilinearAutGroup 2 K = ⊤ ∧
      ∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃ (A : gsp 2 K) (σ : K ≃+* K),
        α = conjAut 2 K A * fieldAut 2 K σ := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) p (by omega : 1 ≤ 2)
  have hη : Function.Injective fun L : SpPoint 2 K => projStabilizer 2 K L.line :=
    fun L M h => SpPoint.ext (hinj _ _ L.line_ne_bot (isTotallyIsotropic_line L)
      M.line_ne_bot (isTotallyIsotropic_line M) h)
  have hform : ∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃ (A : gsp 2 K) (σ : K ≃+* K),
      α = conjAut 2 K A * fieldAut 2 K σ := by
    intro α
    obtain ⟨f, hf⟩ := exists_pointEquiv_two h2 α
    obtain ⟨A, σ, μ, hA, hfL⟩ :=
      geometric_semilinear_realization (by omega : 2 ≤ 2) f
        (automorphism_orthogonality_two α f hf)
    refine ⟨⟨A, μ, hA⟩, σ, LinearFlag.equivariant_subgroup_rigidity
      (fun L : SpPoint 2 K => projStabilizer 2 K L.line) hη projStabilizer_smul α _ f
      f.bijective hf fun L => ?_⟩
    rw [map_projStabilizer_conjAut_mul_fieldAut, ← hfL L]
  refine ⟨eq_top_iff.mpr fun α _ => ?_, hform⟩
  obtain ⟨A, σ, rfl⟩ := hform α
  exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
    (fieldAut_mem_spSemilinearAutGroup σ)

theorem outPNice_StatedSp_two_odd {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : OutPNice p (StatedProj (StatedSp 2 K)) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hgenTop, -⟩ := automorphism_generation_two (K := K) h2
  obtain ⟨hID, -, hDn, -, ⟨g, -, hg⟩, -⟩ := standard_outer_quotient (K := K) (r := 2) (by omega)
  have hDnorm : (spLinearAutGroup 2 K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ spSemilinearAutGroup 2 K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ spSemilinearAutGroup 2 K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  obtain ⟨m, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hdvd := relIndex_inner_spLinearAutGroup_dvd (r := 2) hℓ m.pos hK
  have hD2 : ∀ δ ∈ spLinearAutGroup 2 K, ∀ k : ℕ,
      δ ^ (p ^ k) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 K)) →
      δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) := by
    intro δ hδ k hk
    set D := spLinearAutGroup 2 K with hD
    set I := CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 K)) with hI
    set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
    have hxk : x ^ (p ^ k) = 1 := by
      rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
    have hcard2 : Nat.card (D ⧸ I.subgroupOf D) ∣ 2 := by
      have h1 : Nat.card (D ⧸ I.subgroupOf D) = I.relIndex D := (Subgroup.index_eq_card _).symm
      rw [h1]
      exact hdvd.trans (Nat.gcd_dvd_left 2 _)
    have hdvd1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    have hdvd2 : orderOf x ∣ 2 := (orderOf_dvd_natCard x).trans hcard2
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have : x = 1 := orderOf_eq_one_iff.mp hx1
    have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
    exact Subgroup.mem_subgroupOf.mp hmem
  have hgE : ∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃ k : ℤ, g ^ k * α ∈ spLinearAutGroup 2 K :=
    fun α => hg α (hgenTop ▸ Subgroup.mem_top α)
  exact outPNice_of_tower hp g (E := ⊤) hID hD2 (fun α _ => trivial)
    (fun γ α _ => commutator_mem_of_cyclic_quotient g hgE γ α) (fun α _ => hgE α)

theorem outPNice_PSp_two_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {ℓ f : ℕ} (hℓ : ℓ ≠ 2) (h : StatedClassicalModel X .PSp 2 ℓ f) : OutPNice p X := by
  obtain ⟨⟨hℓp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hchar : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K ℓ] at h1
    exact hℓ ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_two).mp h1)
  exact OutPNice.of_mulEquiv e (outPNice_StatedSp_two_odd h2 hp hp2)

end CFSG.RankThree.PartOne.AUTSL.SpTwo
