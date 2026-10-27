module

public import CFSG.RankThree.PartOne.KF.G2Wctx
public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {G : Type} [Group G]

theorem exists_r2ctx_aux
    [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      p ∣ Nat.card K - 1 ∧
      ∀ σ : Fin Tag.G2.rank → MulAut (Fin Tag.G2.rank → rootsOfUnity p K),
        (∀ i b, tpHom p K (σ i b) =
          weylElt .G2 K i 1 * tpHom p K b * (weylElt .G2 K i 1)⁻¹) →
        Nonempty (WCtx (Subgroup.closure (Set.range σ)).subtype L F) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  have hp := h.prime
  have h5 := h.five_le
  rcases hmod with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hexc
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    refine ⟨K, hKf, hKfin, hζ, hpK, fun σ hσ => ?_⟩
    obtain ⟨SM⟩ := exists_wctx_g2 σ hσ
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e hcop
    let q : ↥(adjointGroup .G2 K) →* AdjointQuotient .G2 K :=
      QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .G2 K))
    have hq : IsCentralPQuot p q := by
      have hker : q.ker = Subgroup.center ↥(adjointGroup .G2 K) := QuotientGroup.ker_mk' _
      refine ⟨QuotientGroup.mk'_surjective _, hker.le, ?_⟩
      rw [hker, center_adjointGroup_eq_bot]
      simp
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot q hq _ hε₀ (fun t ht => Tp_exp t ht)
      (fun s hs t ht => Tp_comm s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp hp h5 hpK X hexp) h.F_le h.F_exp h.F_comm h.maximal
    have hVexp : ∀ d : Fin Tag.G2.rank → rootsOfUnity p K, d ^ p = 1 := fun d =>
      funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
    exact WCtx.ofCentralQuot hVexp SM q hq ε hε h.F_le h.F_exp hFT₁ hFT₂
  · exact absurd hrt (by decide)
  · exact absurd ht (by decide)

end CFSG.RankThree.PartOne
