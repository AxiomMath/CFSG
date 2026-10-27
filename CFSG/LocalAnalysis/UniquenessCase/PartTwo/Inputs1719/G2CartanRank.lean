module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieBorelTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.HardMathSupport.Seitz.ExceptionsTransport.G2SplitTorusPlane
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcTorus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QTor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

noncomputable def g2TorusEquivUnits (K : Type) [Field K] :
    CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K ≃* Kˣ × Kˣ where
  toFun x := CFSG.AGLEmbedding.KFactProofs.G2Q.coord x
  invFun p := ⟨⟨CFSG.AGLEmbedding.KFactProofs.G2Q.tz p.1 p.2,
      CFSG.AGLEmbedding.KFactProofs.G2Q.tz_mem_adjointGroup p.1 p.2⟩, by
    rw [CFSG.AGLEmbedding.KFactProofs.G2Q.mem_torusSub]
    exact CFSG.AGLEmbedding.KFactProofs.G2Q.tz_mem_torusGroup p.1 p.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord x).symm
  right_inv p := by
    obtain ⟨s, t⟩ := p
    have h := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord
      (⟨⟨CFSG.AGLEmbedding.KFactProofs.G2Q.tz s t,
        CFSG.AGLEmbedding.KFactProofs.G2Q.tz_mem_adjointGroup s t⟩, by
        rw [CFSG.AGLEmbedding.KFactProofs.G2Q.mem_torusSub]
        exact CFSG.AGLEmbedding.KFactProofs.G2Q.tz_mem_torusGroup s t⟩ :
        CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K)
    obtain ⟨h1, h2⟩ := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_injective h
    exact Prod.ext h1.symm h2.symm
  map_mul' x y := by
    apply Prod.ext
    · have hx := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord x
      have hy := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord y
      have hxy := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord (x * y)
      have hmul : ((x * y : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) : ModGL .G2 K) =
          ((x : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) : ModGL .G2 K) *
            ((y : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) : ModGL .G2 K) := rfl
      rw [hmul, hx, hy, CFSG.AGLEmbedding.KFactProofs.G2Q.tz_mul] at hxy
      exact (CFSG.AGLEmbedding.KFactProofs.G2Q.tz_injective hxy).1.symm
    · have hx := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord x
      have hy := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord y
      have hxy := CFSG.AGLEmbedding.KFactProofs.G2Q.tz_coord (x * y)
      have hmul : ((x * y : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) : ModGL .G2 K) =
          ((x : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) : ModGL .G2 K) *
            ((y : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) : ModGL .G2 K) := rfl
      rw [hmul, hx, hy, CFSG.AGLEmbedding.KFactProofs.G2Q.tz_mul] at hxy
      exact (CFSG.AGLEmbedding.KFactProofs.G2Q.tz_injective hxy).2.symm

noncomputable def g2TorusSubCongr (K : Type) [Field K] :
    CFSG.LieType.Chevalley.torusSub Tag.G2 K ≃*
      CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K :=
  MulEquiv.subgroupCongr rfl

theorem g2Torus_comm {K : Type} [Field K]
    (x y : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) : x * y = y * x := by
  apply (g2TorusEquivUnits K).injective
  rw [map_mul, map_mul, mul_comm]

theorem g2Torus_card {K : Type} [Field K] :
    Nat.card (CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) = (Nat.card K - 1) ^ 2 := by
  rw [Nat.card_congr (g2TorusEquivUnits K).toEquiv, Nat.card_prod, Nat.card_units]
  ring

theorem g2Torus_rtorsion {K : Type} [Field K] [Finite K]
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card K - 1) :
    Nat.card {x : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K // x ^ r = 1} = r ^ 2 := by
  have h1 : Nat.card {x : Kˣ // x ^ r = 1} = r :=
    CFSG.LocalAnalysis.RankFourTheoremC.card_units_pow_eq_one hdvd
  have hprod : Nat.card {p : Kˣ × Kˣ // p ^ r = 1} = r ^ 2 := by
    have h2 : Nat.card {p : Kˣ × Kˣ // p ^ r = 1} =
        Nat.card ({x : Kˣ // x ^ r = 1} × {y : Kˣ // y ^ r = 1}) := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun p => (⟨p.1.1, by
              have := congrArg Prod.fst p.2
              simpa using this⟩,
            ⟨p.1.2, by
              have := congrArg Prod.snd p.2
              simpa using this⟩)
          invFun := fun p => ⟨(p.1.1, p.2.1), by
              simp [Prod.pow_def, p.1.2, p.2.2]⟩
          left_inv := fun p => by
              apply Subtype.ext
              exact Prod.ext rfl rfl
          right_inv := fun p => by
              apply Prod.ext <;> apply Subtype.ext <;> rfl }
    rw [h2, Nat.card_prod, h1]
    ring
  have h3 : Nat.card {x : CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K // x ^ r = 1} =
      Nat.card {p : Kˣ × Kˣ // p ^ r = 1} := by
    let e := g2TorusEquivUnits K
    refine Nat.card_congr ?_
    exact Equiv.subtypeEquiv e.toEquiv (fun a => by
      change a ^ r = 1 ↔ (e a) ^ r = 1
      rw [← map_pow]
      exact (MulEquiv.map_eq_one_iff e).symm)
  rw [h3, hprod]


theorem k_G2CartanRank_holds : K_G2CartanRank := by
  intro Y _ _ n hY hq S hS r hr hr2 hdvd
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hCE
  letI := hF
  letI := hFin
  letI := hcp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hU : IsSylowTwoOf (posUnipotentSub Tag.G2 K) ⊤ :=
    CFSG.Quasithin.H13.Sec53F.G2.g2_sylow
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf (S := S)
    (S' := posUnipotentSub Tag.G2 K) e hS hU
  obtain ⟨eC⟩ := normalizerQuotient_equiv_of_complement
    (U := posUnipotentSub Tag.G2 K) (H := torusSub Tag.G2 K)
    (CFSG.Quasithin.H13.Sec53F.G2.g2_H_le)
    (CFSG.Quasithin.H13.Sec53F.G2.g2_U_inf_H)
    (CFSG.Quasithin.H13.Sec53F.G2.g2_B_eq)
  let eT : normalizerQuotient S ≃* CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K :=
    eN.trans (eC.trans (g2TorusSubCongr K))
  have hcardT : Nat.card (CFSG.AGLEmbedding.KFactProofs.G2Q.torusSub K) =
      (Nat.card K - 1) ^ 2 := g2Torus_card
  have hcardN : Nat.card (normalizerQuotient S) = (Nat.card K - 1) ^ 2 := by
    rw [Nat.card_congr eT.toEquiv, hcardT]
  have hcardY : Nat.card Y = ordG2 (Nat.card K) := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hCE.2
    rwa [← hK] at h
  have hdvdK : r ∣ Nat.card K - 1 := by
    rw [hK]
    exact hdvd
  have hfac : r ≠ 3 → (Nat.card Y).factorization r =
      (Nat.card (normalizerQuotient S)).factorization r := by
    intro hr3
    have hfacq : (ordG2 (Nat.card K)).factorization r = 2 * (Nat.card K - 1).factorization r := by
      rw [Nat.factorization_def _ hr, Nat.factorization_def _ hr]
      exact CFSG.HardMathSupport.Seitz.ExceptionsTransport.padicValNat_ordG2_of_dvd_sub_one
        (by omega) hr (hr.five_le_of_ne_two_of_ne_three hr2 hr3) hdvdK
    have hne : Nat.card K - 1 ≠ 0 := by omega
    rw [hcardY, hcardN, show (Nat.card K - 1) ^ 2 = (Nat.card K - 1) * (Nat.card K - 1)
      by ring, Nat.factorization_mul hne hne, Finsupp.add_apply, hfacq]
    ring
  have hcomm : ∀ a b : normalizerQuotient S, a * b = b * a := by
    intro a b
    apply eT.injective
    rw [map_mul, map_mul]
    exact g2Torus_comm (eT a) (eT b)
  have hkA : Nat.card {a : normalizerQuotient S // a ^ r = 1} = r ^ 2 := by
    rw [← g2Torus_rtorsion (K := K) hr hdvdK]
    exact Nat.card_congr
      { toFun := fun a => ⟨eT a.1, by rw [← map_pow, a.2, map_one]⟩
        invFun := fun b => ⟨eT.symm b.1, by rw [← map_pow, b.2, map_one]⟩
        left_inv := fun a => Subtype.ext (eT.symm_apply_apply a.1)
        right_inv := fun b => Subtype.ext (eT.apply_symm_apply b.1) }
  obtain ⟨hp, ho⟩ := pRank_and_card_Omega1p_of_comm hcomm hr hkA
  have hp' : CFSG.pRank r (↥(⊤ : Subgroup (normalizerQuotient S))) = 2 := by
    rw [CFSG.pRank_congr_of_mulEquiv
      (Subgroup.topEquiv (G := normalizerQuotient S)) r,
      CFSG.SectionRank.pRank_eq_open_pRank_top, hp]
  exact ⟨hp', ho, hfac⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
