module

public import CFSG.LocalAnalysis.StandardType.GGLangRatFixedChassis
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open scoped TensorProduct

@[expose] def LangRatLocalNorm
    (k : TwistKind) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → S.IsAlgebraic → ∀ w : WeylGroup τ,
    S.D.n = canonicalRep (coxeterSystem τ) L w →
    ∀ b : Fin τ.rank → Lˣ, rootDiagUnit τ b ∈ S.D.torus → ∀ i : KernelComponent (rootCharHom b),
      twistKind S.ρ (rootCharHom b) i = k →
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) →
      ∀ γ ∈ componentRoots (rootCharHom b) i, ∀ (u : Lˣ) (r : ℕ), 0 < r →
        (w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) • γ = γ →
        u ^ (S.D.q ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r)) = u →
        rootDiagUnit τ (∏ j ∈ Finset.range
            (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * r),
          Hchar ((w ^ j) • γ) (u ^ (S.D.q ^ j))) ∈
          rationalComponent S.ρ S.Γ (rootCharHom b) i

theorem langRatLN_norm_sum_mem
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {w : WeylGroup τ} {b : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom b)) {s : ℕ}
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom b) i =
      componentRoots (rootCharHom b) i)
    (hρ : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → S.ρ γ = w • γ)
    (hloc : ∀ γ ∈ componentRoots (rootCharHom b) i, ∀ (u : Lˣ) (r : ℕ), 0 < r →
      (w ^ (s * r)) • γ = γ → u ^ (S.D.q ^ (s * r)) = u →
      rootDiagUnit τ (∏ k ∈ Finset.range (s * r), Hchar ((w ^ k) • γ) (u ^ S.D.q ^ k)) ∈
        rationalComponent S.ρ S.Γ (rootCharHom b) i)
    (e : ℕ) (hqe : S.D.q = 2 ^ e) {ψ : Fin τ.rank → ℤ}
    (hψ : ψ ∈ rationalRoots S.ρ (rootCharHom b) i) (v : Lˣ) (r : ℕ) (hr : 0 < r)
    (hwr : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, (w ^ (s * r)) • γ = γ)
    (hvr : v ^ (S.D.q ^ (s * r)) = v) :
    rootDiagUnit τ (∏ k ∈ Finset.range (s * r), Hchar ((w ^ k) • ψ) (v ^ S.D.q ^ k)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom b) i := by
  obtain ⟨kk, δ, hδ, rfl⟩ := hψ
  obtain ⟨δ', hδ'₁, j, hj⟩ : ∃ δ' ∈ componentRoots (rootCharHom b) i, ∃ j : ℕ,
      (S.ρ : (Fin τ.rank → ℤ) → _)^[kk] δ = (S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ' := by
    refine ⟨(S.ρ : (Fin τ.rank → ℤ) → _)^[s * (kk / s)] δ, ?_, kk % s, ?_⟩
    · have hmaps : Set.MapsTo ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])
          (componentRoots (rootCharHom b) i) (componentRoots (rootCharHom b) i) :=
        fun x hx => hs.subset (Set.mem_image_of_mem _ hx)
      rw [Function.iterate_mul]
      exact hmaps.iterate (kk / s) hδ
    · rw [← Function.iterate_add_apply, Nat.mod_add_div]
  have hδ'Ψ : δ' ∈ rationalRoots S.ρ (rootCharHom b) i := ⟨0, δ', hδ'₁, rfl⟩
  have hiter : ∀ j : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ' = (w ^ j) • δ' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hroot : IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ') :=
        langRatFC_isRoot_of_mem_rationalRoots S i ⟨j, δ', hδ'₁, rfl⟩
      rw [Function.iterate_succ_apply', hρ _ hroot, ih, pow_succ', mul_smul]
  obtain ⟨u, huv, hur⟩ := langRatFC_exists_unit_root_fixed e hqe v j (s * r) hvr
  have hprod : ∏ k ∈ Finset.range (s * r), Hchar ((w ^ k) • ((w ^ j) • δ')) (v ^ S.D.q ^ k) =
      ∏ k ∈ Finset.range (s * r), Hchar ((w ^ k) • δ') (u ^ S.D.q ^ k) := by
    have hper : ∀ k, (fun k => Hchar ((w ^ k) • δ') (u ^ S.D.q ^ k)) (k + s * r) =
        (fun k => Hchar ((w ^ k) • δ') (u ^ S.D.q ^ k)) k := by
      intro k
      show Hchar ((w ^ (k + s * r)) • δ') (u ^ S.D.q ^ (k + s * r)) =
        Hchar ((w ^ k) • δ') (u ^ S.D.q ^ k)
      rw [pow_add, mul_smul, hwr δ' hδ'Ψ, pow_add, mul_comm (S.D.q ^ k), pow_mul, hur]
    calc ∏ k ∈ Finset.range (s * r), Hchar ((w ^ k) • ((w ^ j) • δ')) (v ^ S.D.q ^ k)
        = ∏ k ∈ Finset.range (s * r),
            (fun k => Hchar ((w ^ k) • δ') (u ^ S.D.q ^ k)) (k + j) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          show Hchar ((w ^ k) • ((w ^ j) • δ')) (v ^ S.D.q ^ k) =
            Hchar ((w ^ (k + j)) • δ') (u ^ S.D.q ^ (k + j))
          rw [← mul_smul, ← pow_add, ← huv, ← pow_mul, ← pow_add, add_comm j k]
      _ = ∏ k ∈ Finset.range (s * r), Hchar ((w ^ k) • δ') (u ^ S.D.q ^ k) :=
          langRatFC_prod_range_shift_period (fun k => Hchar ((w ^ k) • δ') (u ^ S.D.q ^ k))
            (s * r) hper j
  rw [hj, hiter j, hprod]
  exact hloc δ' hδ'₁ u r hr (hwr δ' hδ'Ψ) hur

theorem langRatTorusFixedMemKind_of_localNorm
    (k : TwistKind) (hnorm : LangRatLocalNorm k) : LangRatTorusFixedMemKind k := by
  intro τ L _ _ _ p₀ S hτ hAlg w hn b hb i hk hqs hw x hx
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    intro t
    rcases hτ with rfl | rfl <;> cases t <;> decide
  obtain ⟨e, hqe⟩ : ∃ e : ℕ, S.D.q = 2 ^ e := by
    obtain ⟨ℓ, e, -, hchar, -, hqe'⟩ := exists_char_pow S
    exact ⟨e, by rw [hqe', CharP.eq L hchar ‹CharP L 2›]⟩
  obtain ⟨hm0, hs, hmin⟩ := outer_componentOrbitLength_spec S hb i
  have hq2 : 2 ≤ S.D.q := by
    have := S.hqpow.1.one_lt
    omega
  have hρ : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → S.ρ γ = w • γ := fun γ hγ =>
    S.rho_eq_smul hτ' hn hγ
  have hloc := hnorm τ L p₀ S hτ hAlg w hn b hb i hk hqs
  have hN0 : 0 < orderOf w := (isOfFinOrder_of_finite w).orderOf_pos
  have hwN : ∀ γ : Fin τ.rank → ℤ,
      (w ^ (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * orderOf w)) • γ = γ := by
    intro γ
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, one_smul]
  obtain ⟨l, hl, hxl⟩ := langRatNormGeneration (rationalRoots S.ρ (rootCharHom b) i) w hw S.D.q
    hq2 (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * orderOf w)
    (Nat.mul_pos hm0 hN0) (fun γ _ => hwN γ) x hx
  have hfac : ∀ p ∈ l, rootDiagUnit τ (Additive.toMul (langRatPiT _ L
      (∑ j ∈ Finset.range
          (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * orderOf w),
        ((langRatSigmaT (rationalRoots S.ρ (rootCharHom b) i) L w hw S.D.q :
          Module.End ℤ (TSc (rationalRoots S.ρ (rootCharHom b) i) L)) ^ j)
          (p.1 ⊗ₜ[ℤ] p.2)))) ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hl p hp
    have e1 : Additive.toMul (langRatPiT _ L
        (∑ j ∈ Finset.range
            (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * orderOf w),
          ((langRatSigmaT (rationalRoots S.ρ (rootCharHom b) i) L w hw S.D.q :
            Module.End ℤ (TSc (rationalRoots S.ρ (rootCharHom b) i) L)) ^ j)
            (p.1 ⊗ₜ[ℤ] p.2))) =
        ∏ j ∈ Finset.range
            (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * orderOf w),
          Hchar ((w ^ j) • (p.1 : Fin τ.rank → ℤ)) (Additive.toMul p.2 ^ S.D.q ^ j) := by
      rw [map_sum, toMul_sum]
      exact Finset.prod_congr rfl fun j _ =>
        langRatFC_toMul_piT_sigma_pow_tmul _ w hw S.D.q j p.1 p.2
    rw [e1]
    exact langRatLN_norm_sum_mem S i hs hρ hloc e hqe hp1
      (Additive.toMul p.2) (orderOf w)
      hN0 (fun γ _ => hwN γ) hp2
  have key : ∀ l' : List (↥(Submodule.span ℤ (rationalRoots S.ρ (rootCharHom b) i)) ×
      Additive Lˣ), (∀ p ∈ l', rootDiagUnit τ (Additive.toMul (langRatPiT _ L
      (∑ j ∈ Finset.range
          (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * orderOf w),
        ((langRatSigmaT (rationalRoots S.ρ (rootCharHom b) i) L w hw S.D.q :
          Module.End ℤ (TSc (rationalRoots S.ρ (rootCharHom b) i) L)) ^ j)
          (p.1 ⊗ₜ[ℤ] p.2)))) ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i) →
      rootDiagUnit τ (Additive.toMul (langRatPiT _ L
        ((l'.map fun p => ∑ j ∈ Finset.range
          (componentOrbitLength S.ρ (componentRoots (rootCharHom b) i) * orderOf w),
        ((langRatSigmaT (rationalRoots S.ρ (rootCharHom b) i) L w hw S.D.q :
          Module.End ℤ (TSc (rationalRoots S.ρ (rootCharHom b) i) L)) ^ j)
          (p.1 ⊗ₜ[ℤ] p.2)).sum))) ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i := by
    intro l'
    induction l' with
    | nil =>
      intro _
      simpa [CFSG.LieType.Chevalley.rootDiagUnit_one] using
        (rationalComponent S.ρ S.Γ (rootCharHom b) i).one_mem
    | cons p l' ih =>
      intro h
      rw [List.map_cons, List.sum_cons, map_add, toMul_add,
        CFSG.LieType.Chevalley.rootDiagUnit_mul]
      exact Subgroup.mul_mem _ (h p (List.mem_cons_self ..))
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
  rw [hxl]
  exact key l hfac

theorem langRatTorusFixedMem_of_localNorm
    (h : ∀ k, LangRatLocalNorm k) : LangRatTorusFixedMem :=
  langRatTorusFixedMem_of_kinds
    (langRatTorusFixedMemKind_of_localNorm .inner (h .inner))
    (langRatTorusFixedMemKind_of_localNorm .suN (h .suN))
    (langRatTorusFixedMemKind_of_localNorm .twoD (h .twoD))
    (langRatTorusFixedMemKind_of_localNorm .exc (h .exc))

end CFSG.StandardType.LangRat
