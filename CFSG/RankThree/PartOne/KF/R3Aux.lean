module

public import CFSG.RankThree.PartOne.KF.D4Wctx
public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.KF.G2Sylow

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {G : Type} [Group G]

theorem exists_r3ctx_aux
    [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 3) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (σ : K →+* K), D4Param p f K σ ∧
      (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∀ τ : Fin TwistTag.D4.foldedTag.rank → MulAut (Fin 2 → rootsOfUnity p K),
        (∀ a b, tp3Hom p K (τ a b) =
          canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
            tp3Hom p K b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
              (TwistTag.D4.orbitReflection a))⁻¹) →
        Nonempty (WCtx (Subgroup.closure (Set.range τ)).subtype L F) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  have hp := h.prime
  have h5 := h.five_le
  rcases hmod with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, hKf, hKfin, hK, σ, hσ, ⟨e⟩⟩ := hexc
    have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
    have hP : D4Param p f K σ := ⟨hp, h5, hf1, hK3, hσ, hpq⟩
    have hpK : p ∣ Nat.card K - 1 := by
      rw [hK3]
      exact hpq.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 3)
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    refine ⟨f, K, hKf, σ, hP, hζ, fun τ hτ => ?_⟩
    obtain ⟨SM⟩ := exists_wctx_d4 hP τ hτ
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e hcop
    have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
    have hΓ := (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hf1 K hK σ hσ).2.2.1
    let q : ↥(graphFixedRootGroup TwistTag.D4 K σ) →*
        DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ) :=
      (QuotientGroup.mk' (Subgroup.center ↥⁅twistedFixedGroup TwistTag.D4 K σ,
        twistedFixedGroup TwistTag.D4 K σ⁆)).comp (Subgroup.inclusion hΓ.ge)
    have hq : IsCentralPQuot p q := by
      have hcenter : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ) = ⊥ :=
        center_graphFixedRootGroup_eq_bot hσs
      have hker : q.ker ≤ Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ) := by
        intro x hx
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hx
        rw [Subgroup.mem_center_iff]
        intro y
        have h2 := congrArg Subtype.val (hx (Subgroup.inclusion hΓ.ge y))
        exact Subtype.ext h2
      refine ⟨?_, hker, ?_⟩
      · intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
        exact ⟨⟨x.1, hΓ.le x.2⟩, rfl⟩
      · have hk0 : q.ker = ⊥ := by
          rw [← le_bot_iff, ← hcenter]
          exact hker
        rw [hk0]
        simp
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot q hq _ hε₀ (fun t ht => Tp3_exp hP t ht)
      (fun s hs t ht => Tp3_comm hP s t hs ht) (fun X hexp _ => exists_conj_into_Tp3 hP X hexp)
      h.F_le h.F_exp h.F_comm h.maximal
    have hVexp : ∀ d : Fin 2 → rootsOfUnity p K, d ^ p = 1 := fun d =>
      funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
    exact WCtx.ofCentralQuot hVexp SM q hq ε hε h.F_le h.F_exp hFT₁ hFT₂
  · exact absurd hrt (by decide)
  · exact absurd ht (by decide)

end CFSG.RankThree.PartOne
