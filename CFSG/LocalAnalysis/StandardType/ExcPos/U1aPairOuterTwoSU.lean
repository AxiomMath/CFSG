module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGFamTameSuN
public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.StandardType.TableCRes
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.MaxRankE8FixedCover
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups


private theorem u1aO3_mem_of_frame {τ : Tag} {Δ : LangDatum τ GGL}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {S : LangSetup τ GGL 5}
    (hSD : S.D = Δ) (hSρ : S.ρ = ρ) (hq : Δ.q = 2)
    {a : Fin 2 → Fin τ.rank → GGLˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a)) {Ψ : Set (Fin τ.rank → ℤ)}
    (hfam : componentRoots (famCharHom a) i = Ψ)
    (hb : componentOrbitLength ρ Ψ = 1) (houter : ¬ twistInner Ψ ρ)
    (hqs : CFSG.Assembly.IsQuasisimple ↥(LieCore.ratComp ρ Δ.Γ Ψ))
    {b : Fin τ.rank → GGLˣ} {j : KernelComponent (rootCharHom b)}
    (hbΨ : componentRoots (rootCharHom b) j = Ψ)
    {g : ModGL τ GGL} (hg : g ∈ rootSpan τ GGL Ψ ⊓ Δ.model) (hg2 : g * g = 1)
    {ν : ℕ} {ψ : SL(ν, GGL) →* ModGL τ GGL}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hν : 3 ≤ ν) (hψ : IsSLFrame ψ σ)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1)
    (hΨb : componentRoots (rootCharHom b) j = frameRoots σ) :
    g ∈ LieCore.ratComp ρ Δ.Γ Ψ := by
  classical
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom b) j) with hsdef
  have hs1 : s = 1 := by
    rw [hsdef, hbΨ, hSρ]
    exact hb
  have hne : {k : ℕ | 0 < k ∧ (ρ : (Fin τ.rank → ℤ) → _)^[k] '' Ψ = Ψ}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hb' : componentOrbitLength ρ Ψ = 1 := hb
    simp only [componentOrbitLength] at hb'
    rw [h] at hb'
    simp at hb'
  have himg : (ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ := by
    have h := (Nat.sInf_mem hne).2
    have hb' : sInf {k : ℕ | 0 < k ∧ (ρ : (Fin τ.rank → ℤ) → _)^[k] '' Ψ = Ψ} = 1 := by
      simpa only [componentOrbitLength] using hb
    rw [hb'] at h
    simpa [Function.iterate_one] using h
  have hmaps : ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ Ψ := by
      rw [← hbΨ, hΨb]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ := ⟨σ x y, h1, rfl⟩
    have hst : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ := by
      rw [hs1, Function.iterate_one, hSρ]
      exact himg
    rw [hst] at h2
    rw [← hΨb, hbΨ]
    exact h2
  have hneg : ∀ (k : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] (-γ) =
        -(S.ρ : (Fin τ.rank → ℤ) → _)^[k] γ := by
    intro k
    induction k with
    | zero => exact fun γ => rfl
    | succ k ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν (one_ne_zero : (1 : ℤ) ≠ 0) hnorm
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s) (iform_rho_iterate S s) with
    ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply houter
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm (one_ne_zero : (1 : ℤ) ≠ 0) hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [← hbΨ, hΨb]
      exact hw
    · rw [← hbΨ, hΨb] at hγ
      obtain ⟨x, y, hxy, rfl⟩ := hγ
      have h := hπ x y hxy
      rw [hs1, Function.iterate_one, hSρ] at h
      rw [h, hwσ]
  ·
    have hΨ_fam : componentRoots (famCharHom a) i = frameRoots σ := by
      rw [hfam, ← hbΨ]
      exact hΨb
    have hfamOrbit : componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 := by
      rw [hfam, hSρ]
      exact hb
    have hπ_fam : ∀ x y, x ≠ y →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (famCharHom a) i)] (σ x y) = σ (π y) (π x) := by
      intro x y hxy
      simpa [hfamOrbit, hs1, Function.iterate_one] using hπ x y hxy
    have hρ_fam : ∀ γ ∈ kernelRoots (famCharHom a),
        S.ρ γ ∈ kernelRoots (famCharHom a) :=
      fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
    have hνq : (ν, 2) ≠ (3, 2) := by
      intro hν3
      have hν_eq : ν = 3 := (Prod.mk.injEq ν 2 3 2).mp hν3 |>.1
      obtain ⟨r, e, hr, hchar, he, hqrp⟩ := exists_char_pow S
      haveI : Fact r.Prime := ⟨hr⟩
      haveI : CharP GGL r := hchar
      have hQ32 : (ν, r ^ (e * componentOrbitLength S.ρ
          (componentRoots (famCharHom a) i))) = (3, 2) := by
        rw [hν_eq, hfamOrbit, Nat.mul_one, ← hqrp, hSD, hq]
      obtain ⟨σQ, hσQ, f, hf1, -, -⟩ :=
        fam_two_suN_exists_hom S hρ_fam i hν hψ hΨ_fam π hπ_fam hr hchar he hqrp
      obtain ⟨-, -, hcardC⟩ :=
        stdUnitary_fixSubgroup hr (Nat.mul_pos he (by rw [hfamOrbit]; exact one_pos))
          σQ hσQ hν
      have h216 := hcardC hQ32
      have hsol_fam : Group.IsSolvable ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_of_card_dvd_216
          (by
            rw [← h216]
            exact (Subgroup.card_dvd_of_le hf1).trans (Subgroup.card_range_dvd f))
      have hEq : rationalComponentM S.ρ S.Γ (famCharHom a) i
          = LieCore.ratComp ρ Δ.Γ Ψ := by
        rw [← LieCore.ratComp_eq_rationalComponentM]
        rw [hfam, hSρ, LangSetup.Γ, hSD]
      have hsol : Group.IsSolvable ↥(LieCore.ratComp ρ Δ.Γ Ψ) := by
        rw [← hEq]
        exact hsol_fam
      haveI : Group.IsSolvable ↥(LieCore.ratComp ρ Δ.Γ Ψ) := hsol
      haveI : Nontrivial
          (↥(LieCore.ratComp ρ Δ.Γ Ψ) ⧸
            Subgroup.center ↥(LieCore.ratComp ρ Δ.Γ Ψ)) := hqs.2.toNontrivial
      haveI : Nontrivial ↥(LieCore.ratComp ρ Δ.Γ Ψ) :=
        Function.Surjective.nontrivial
          (QuotientGroup.mk'_surjective
            (Subgroup.center ↥(LieCore.ratComp ρ Δ.Γ Ψ)))
      have hlt : commutator ↥(LieCore.ratComp ρ Δ.Γ Ψ) < ⊤ :=
        Group.IsSolvable.commutator_lt_top_of_nontrivial
          ↥(LieCore.ratComp ρ Δ.Γ Ψ)
      exact hlt.ne hqs.1
    have hνq' : (ν, 2 ^ 1) ≠ (3, 2) := by simpa using hνq
    have hq' : S.D.q = 2 ^ 1 := by
      rw [hSD, hq]
      norm_num
    obtain ⟨F', hcomm, hperf⟩ :=
      exists_unitary_source_perfect S j hν hψ π (by simpa [hsdef] using hπ)
        (by simpa [hsdef] using hs1) (k' := ZMod 2) Nat.prime_two (e := 1) one_pos hq'
        hνq'
    have hker : ψ.ker ≠ ⊤ :=
      frame_ker_ne_top (τ := τ) (L := GGL) (ν := ν) (by omega) hψ
    have hkercenter : ψ.ker ≤ Subgroup.center SL(ν, GGL) := by
      intro X hX
      refine mem_center_SL_of_commute hν ψ hker (fun Y => ?_)
      rw [MonoidHom.mem_ker.mp hX, one_mul, mul_one]
    have hodd : Odd (Nat.card ψ.ker) :=
      odd_card_ker_of_frame (hν := hν) hψ hker
    have hg' : g ∈ rootSpan τ GGL (frameRoots σ) := by
      rw [← hΨb, hbΨ]
      exact hg.1
    have hgD : g ∈ S.D.model := by
      rw [hSD]
      exact hg.2
    have hgfix : S.D.step g = g := by
      have h := (S.D.mem_model.mp hgD).2
      simpa [LangDatum.step, MulAut.conj_apply] using h
    have hg2' : g ^ 2 = 1 := by
      rw [pow_two]
      exact hg2
    have hmem : g ∈ rationalComponent S.ρ S.Γ (rootCharHom b) j :=
      map_eqLocus_le_rationalComponent S j hψ hΨb hkercenter hodd F' hcomm hperf
        hg' hgfix hg2'
    have hEq : rationalComponent S.ρ S.Γ (rootCharHom b) j
        = LieCore.ratComp ρ Δ.Γ Ψ := by
      rw [LieCore.rationalComponent_eq_ratComp, hbΨ, hSρ, LangSetup.Γ, hSD]
    rw [hEq] at hmem
    exact hmem

theorem outerTwo_mem_ratComp_suN {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (Δ : LangDatum τ GGL) (hq : Δ.q = 2) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap Δ ρ) (hfin : Finite Δ.model) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a₁ a₂ : Fin τ.rank → GGLˣ} (ha₁ : rootDiagUnit τ a₁ ∈ Δ.torus)
    (ha₂ : rootDiagUnit τ a₂ ∈ Δ.torus) (hap₁ : ∀ j, a₁ j ^ p = 1)
    (hap₂ : ∀ j, a₂ j ^ p = 1) (iJ : KernelComponent (LieCore.jointChar a₁ a₂))
    (hb : componentOrbitLength ρ (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1)
    (houter : ¬ twistInner (componentRoots (LieCore.jointChar a₁ a₂) iJ) ρ)
    (hA : 2 ≤ compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) ∧
      (componentRoots (LieCore.jointChar a₁ a₂) iJ).ncard =
        compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) *
          (compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) + 1))
    (hqs : CFSG.Assembly.IsQuasisimple
      ↥(LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ)))
    {g : ModGL τ GGL}
    (hg : g ∈ rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model)
    (hg2 : g * g = 1) :
    g ∈ LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
  classical
  set Ψ : Set (Fin τ.rank → ℤ) :=
    componentRoots (LieCore.jointChar a₁ a₂) iJ with hΨdef
  obtain ⟨S, hSD, hSρ⟩ :=
    LieCore.exists_langSetup_of_datum Δ ρ hρ hfin (f := 1) le_rfl (by rw [hq]; norm_num)
  let a : Fin 2 → Fin τ.rank → GGLˣ := ![a₁, a₂]
  have hT : ∀ u : Fin 2, rootDiagUnit τ (a u) ∈ S.D.torus := by
    intro u
    rw [hSD]
    fin_cases u
    · simpa [a] using ha₁
    · simpa [a] using ha₂
  have hap : ∀ u j, a u j ^ p = 1 := by
    intro u
    fin_cases u
    · simpa [a] using hap₁
    · simpa [a] using hap₂
  obtain ⟨i, hi⟩ := LieCore.exists_famComponent_of_jointChar a₁ a₂ iJ
  have hfam : componentRoots (famCharHom a) i = Ψ := by
    rw [hΨdef]
    exact hi.symm
  obtain ⟨N, b, j, hNprime, hN2, hTpb, hroots⟩ :=
    exists_isolating_element hτ a hp hp2 hap i
  have hbΨ : componentRoots (rootCharHom b) j = Ψ := by
    rw [hroots, hfam]
  have h2b : 2 ≤ compRank (componentRoots (rootCharHom b) j) := by
    rw [hbΨ]
    exact hA.1
  have hnb : (componentRoots (rootCharHom b) j).ncard =
      compRank (componentRoots (rootCharHom b) j) *
        (compRank (componentRoots (rootCharHom b) j) + 1) := by
    rw [hbΨ]
    exact hA.2
  have hNL : (N : GGL) ≠ 0 := by
    intro h
    exact hN2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hNprime).1
      ((CharP.cast_eq_zero_iff GGL 2 N).1 h)).symm
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨb⟩ :=
      exists_frame_of_typeA_E6_T_of_prime S hNprime hNL hTpb j h2b hnb
    exact u1aO3_mem_of_frame (S := S) (i := i) (Ψ := Ψ) hSD hSρ hq hT hfam hb houter
      hqs hbΨ hg hg2 hν hψ hnorm hΨb
  · obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨb⟩ :=
      exists_frame_of_typeA_E7_T_of_prime S hNprime hNL hTpb j h2b hnb
    exact u1aO3_mem_of_frame (S := S) (i := i) (Ψ := Ψ) hSD hSρ hq hT hfam hb houter
      hqs hbΨ hg hg2 hν hψ hnorm hΨb
  · obtain ⟨ν, ψ, σ, hν, hψ, hnorm, hΨb⟩ :=
      exists_frame_of_typeA_E8_T_of_prime S hNprime hNL hTpb j h2b hnb
    exact u1aO3_mem_of_frame (S := S) (i := i) (Ψ := Ψ) hSD hSρ hq hT hfam hb houter
      hqs hbΨ hg hg2 hν hψ hnorm hΨb

end CFSG.StandardType.LieKnownR2.ExcPos
