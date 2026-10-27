module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147cMat
public import CFSG.LocalAnalysis.StandardType.GGLangSixRoot
public import CFSG.LocalAnalysis.StandardType.GGLangSmallLat

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem isSolvable_rationalComponent_of_latSolv
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ f p : ℕ} (S : LangSetup τ L p₀)
    (hq : S.D.q = 2 ^ f) (hp : p.Prime) (hpL : (p : L) ≠ 0) (π : Equiv.Perm (Fin τ.rank))
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hpε : (p : ℤ) ∣ (S.D.q : ℤ) - ε)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hsolv : LatSolv (f = 1) π (rationalRoots S.ρ (rootCharHom a) i)) :
    Group.IsSolvable ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hf1, hcases⟩ := hsolv
  have hq2 : S.D.q = 2 := by rw [hq, hf1, pow_one]
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  have hCO : ∀ γ ∈ componentRoots (rootCharHom a) i,
      γ ∈ rationalRoots S.ρ (rootCharHom a) i := fun γ hγ => ⟨0, γ, hγ, rfl⟩
  have hs1 : (∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i) →
      (componentRoots (rootCharHom a) i).Finite → s = 1 := by
    intro hmaps hfin
    have himg : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i := by
      rw [Function.iterate_one]
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
      · rintro _ ⟨γ, hγ, rfl⟩
        exact hmaps γ hγ
      · exact (Set.ncard_image_of_injective _ S.ρ.injective).ge
    by_contra hne
    exact hmin 1 one_pos (by omega) himg
  rcases hcases with ⟨α, hO⟩ | ⟨h6, hfix⟩
  ·
    obtain ⟨a', ha'⟩ := Quotient.exists_rep i
    have hx : a'.1 ∈ componentRoots (rootCharHom a) i := ⟨a'.2, ha'⟩
    have hxO : a'.1 ∈ ({α, -α} : Set (Fin τ.rank → ℤ)) := by
      rw [← hO]
      exact hCO _ hx
    have hαC : α ∈ componentRoots (rootCharHom a) i ∧
        -α ∈ componentRoots (rootCharHom a) i := by
      rcases hxO with h | h
      · rw [h] at hx
        exact ⟨hx, hΨ.neg_mem _ hx⟩
      · rw [Set.mem_singleton_iff] at h
        rw [h] at hx
        exact ⟨by simpa using hΨ.neg_mem _ hx, hx⟩
    have hCeq : componentRoots (rootCharHom a) i = {α, -α} := by
      refine Set.Subset.antisymm (fun γ hγ => ?_) ?_
      · rw [← hO]
        exact hCO γ hγ
      · rintro γ (rfl | rfl)
        · exact hαC.1
        · exact hαC.2
    have hmaps : ∀ γ ∈ componentRoots (rootCharHom a) i,
        S.ρ γ ∈ componentRoots (rootCharHom a) i := by
      intro γ hγ
      have h1 : S.ρ γ ∈ rationalRoots S.ρ (rootCharHom a) i := ⟨1, γ, hγ, rfl⟩
      rw [hO, ← hCeq] at h1
      exact h1
    have hfin : (componentRoots (rootCharHom a) i).Finite := by
      rw [hCeq]
      exact Set.toFinite _
    have hs1' : s = 1 := hs1 hmaps hfin
    have hrank : ∀ x ∈ componentRoots (rootCharHom a) i, ∀ y ∈ componentRoots (rootCharHom a) i,
        y = x ∨ y = -x := by
      intro x hx y hy
      rw [hCeq] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
    have hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
      rw [hs1', Function.iterate_one]
      have hαr : IsRoot τ α := hΨ.isRoot α hαC.1
      have hρα : S.ρ α = α ∨ S.ρ α = -α := by
        have h1 := hmaps α hαC.1
        rw [hCeq] at h1
        exact h1
      rcases hρα with h | h
      · refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
        rw [hCeq] at hγ
        rcases hγ with hγ | hγ
        · rw [hγ, h, one_smul]
        · rw [Set.mem_singleton_iff] at hγ
          rw [hγ, S.frob.neg_eq, h, one_smul]
      · refine ⟨rootReflection α, Subgroup.subset_closure ⟨α, hαC.1, rfl⟩, fun γ hγ => ?_⟩
        rw [hCeq] at hγ
        rcases hγ with hγ | hγ
        · rw [hγ, h, rootReflection_smul_self hαr]
        · rw [Set.mem_singleton_iff] at hγ
          rw [hγ, S.frob.neg_eq, h, smul_neg, rootReflection_smul_self hαr]
    obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
    obtain ⟨r, e, hr, hchar, he, hqr⟩ := exists_char_pow S
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hqr, ← pow_mul]
    obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
    have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
      ext c
      show c ∈ fixSubfield σ ↔ _
      rw [mem_fixSubfield, hσ']
      rfl
    haveI hfinK : Finite (fixSubfield σ) := by
      have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
      exact h1.to_subtype
    have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
      have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
        Nat.card_coe_set_eq (fixSubfield σ : Set L)
      rw [h1, hset, hcardset]
    have hKle : Nat.card (fixSubfield σ) ≤ 3 := by
      rw [hKcard, pow_mul, ← hqr, hq2, hs1']
      norm_num
    have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
      obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
      have hc0 : c ≠ 0 := fun h => hc (by simp [h])
      refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
      have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
      have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · simp [sub_eq_zero.1 h]
      · simp [eq_neg_of_add_eq_zero_left h]
    obtain ⟨f₁, hf₁1, -, -⟩ :=
      rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
    haveI : Group.IsSolvable ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
      isSolvable_componentRootSpan_of_rank_one hKle i hrank
    haveI : Group.IsSolvable ↥f₁.range :=
      Group.isSolvable_of_surjective f₁.rangeRestrict_surjective
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hf₁1)
      (Subgroup.inclusion_injective hf₁1)
  ·
    have hε1 : ε = -1 := by
      rcases hε with h | h
      · exfalso
        have h1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
          have := hpε
          rw [h, hq2] at this
          simpa using this
        exact hp.one_lt.ne' (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h1))
      · exact h
    have hρC : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -γ := by
      intro γ hγ
      rw [hρ γ (hΨ.isRoot γ hγ), hfix γ (hCO γ hγ), hε1, neg_one_smul ℤ]
    have hmaps : ∀ γ ∈ componentRoots (rootCharHom a) i,
        S.ρ γ ∈ componentRoots (rootCharHom a) i := by
      intro γ hγ
      rw [hρC γ hγ]
      exact hΨ.neg_mem γ hγ
    have hO : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i :=
      rationalRoots_eq_componentRoots_of_mapsTo S.ρ (rootCharHom a) i hmaps
    rw [hO] at h6
    have hfin : (componentRoots (rootCharHom a) i).Finite := Set.finite_of_ncard_pos (by omega)
    have hs1' : s = 1 := hs1 hmaps hfin
    have hrk : compRank (componentRoots (rootCharHom a) i) = 2 :=
      compRank_eq_two_of_ncard_eq_six hΨ h6
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨσ⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i (by omega)
        (by rw [hrk]; omega)
    have hν3 : ν = 3 := by
      have hc := kd147c_frameRoots_ncard hψ hκ hnorm
      rw [← hΨσ, h6] at hc
      by_contra hne
      have h4 : 4 ≤ ν := by omega
      have h12 : 4 * 3 ≤ ν * (ν - 1) := Nat.mul_le_mul h4 (by omega)
      omega
    subst hν3
    have hπ : ∀ x y : Fin 3, x ≠ y →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) =
          σ ((1 : Equiv.Perm (Fin 3)) y) ((1 : Equiv.Perm (Fin 3)) x) := by
      intro x y hxy
      have hσ : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨσ]
        exact ⟨x, y, hxy, rfl⟩
      rw [hs1', Function.iterate_one, hρC _ hσ]
      exact (hψ.neg x y).symm
    obtain ⟨-, h216⟩ := rationalComponent_of_unitary_frame_T S hT i hν hψ hΨσ
      (1 : Equiv.Perm (Fin 3)) hπ
    refine isSolvable_of_card_dvd_216 (h216 ?_)
    have h2 : S.D.q ^ s = 2 := by rw [hs1', pow_one, hq2]
    exact Prod.ext rfl h2

end CFSG.StandardType.LangRat
