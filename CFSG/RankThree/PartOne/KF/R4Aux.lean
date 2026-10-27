module

public import CFSG.RankThree.PartOne.KF.F4Wctx
public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.KF.G2Sylow
public import CFSG.RankThree.PartOne.KF.F4Sylow
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.SectionRank.LargeRee


variable {G : Type} [Group G]

theorem exists_r4ctx_aux
    [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 4) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      F4Param p a K ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∀ τ : Fin 2 → MulAut (Fin 2 → rootsOfUnity p K),
        (∀ i b, tp4Hom p a K (τ i b) =
          ((nGamma (blockGen i) : ↥(F4.reeGamma K a)) : ModGL F4.tag K) * tp4Hom p a K b *
            ((nGamma (blockGen i) : ↥(F4.reeGamma K a)) : ModGL F4.tag K)⁻¹) →
        Nonempty (WCtx (Subgroup.closure (Set.range τ)).subtype L F) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  have hp := h.prime
  have h5 := h.five_le
  rcases hmod with ⟨hcl, -⟩ | ⟨-, hex, -⟩ | ⟨-, -, hree⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hex (by decide)
  · have hS := ReeTag.large_Ree_model_Schreier (L ⧸ Subgroup.center L) 2 f hree
    obtain ⟨-, a, hfa, K, hKf, hKfin, hK, ⟨e⟩⟩ := hree
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : CharP K ReeTag.F4.prime := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [Fintype.card_eq_nat_card]
        exact hK)
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hP : F4Param p a K := ⟨hp, h5, hK', by rw [← hfa]; exact hpq⟩
    have hpK : p ∣ Nat.card K - 1 := by rw [hK']; exact hP.dvd
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    refine ⟨a, K, hKf, hKfin, hchar, hP, hζ, fun τ hτ => ?_⟩
    obtain ⟨SM⟩ := exists_wctx_f4 hP τ hτ
    obtain ⟨e'⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e' hcop
    have hq : IsCentralPQuot p (MonoidHom.id ↥(F4.reeGamma K a)) :=
      SymCtx.isCentralPQuot_of_bijective _ Function.bijective_id p
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (MonoidHom.id ↥(F4.reeGamma K a)) hq _ hε₀
      (fun t ht => Tp4_exp hP t ht) (fun s hs t ht => Tp4_comm hP s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp4 hP X hexp) h.F_le h.F_exp h.F_comm h.maximal
    have hVexp : ∀ d : Fin 2 → rootsOfUnity p K, d ^ p = 1 := fun d =>
      funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
    exact WCtx.ofCentralQuot hVexp SM _ hq ε hε h.F_le h.F_exp hFT₁ hFT₂
  · exact absurd ht (by decide)

end CFSG.RankThree.PartOne
