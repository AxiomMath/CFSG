module

public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.G2Sylow
public import CFSG.RankThree.PartOne.KF.D4Sylow
public import CFSG.RankThree.PartOne.KF.F4Sylow
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

variable {G : Type} [Group G]

@[expose] noncomputable def g2Q (K : Type) [Field K] :
    ↥(adjointGroup .G2 K) →* AdjointQuotient .G2 K :=
  QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .G2 K))

theorem isCentralPQuot_g2Q (p : ℕ) (K : Type) [Field K] [Finite K] :
    IsCentralPQuot p (g2Q K) := by
  have hker : (g2Q K).ker = Subgroup.center ↥(adjointGroup .G2 K) := QuotientGroup.ker_mk' _
  refine ⟨QuotientGroup.mk'_surjective _, hker.le, ?_⟩
  rw [hker, center_adjointGroup_eq_bot]
  simp

theorem exists_r2frame [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 2) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      Nat.card K = 2 ^ f ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧ CharP K 2 ∧
      ∃ ε : ↥L →* AdjointQuotient .G2 K, IsCentralPQuot p ε ∧
        (∀ t ∈ Tp p K, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = g2Q K t) ∧
        ∀ x : F, ∃ t ∈ Tp p K, ε (Subgroup.inclusion h.F_le x) = g2Q K t := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  have hp := h.prime
  have h5 := h.five_le
  rcases hmod with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hrt, -⟩ | ⟨-, ht, -⟩
  · exact absurd hcl (by decide)
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hexc
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
    have hζ := exists_isPrimitiveRoot_of_dvd_card_sub_one hp hpK
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f)
        (by rw [Fintype.card_eq_nat_card]; exact hK)
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e hcop
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (g2Q K) (isCentralPQuot_g2Q p K) _ hε₀
      (fun t ht => Tp_exp t ht) (fun s hs t ht => Tp_comm s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp hp h5 hpK X hexp) h.F_le h.F_exp h.F_comm h.maximal
    exact ⟨f, K, hKf, hKfin, hf1, hpq, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩
  · exact absurd hrt (by decide)
  · exact absurd ht (by decide)

theorem fixedD4_derived {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}
    (h : D4Param p f K σ) :
    ⁅twistedFixedGroup TwistTag.D4 K σ, twistedFixedGroup TwistTag.D4 K σ⁆ =
      graphFixedRootGroup TwistTag.D4 K σ :=
  (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two h.one_le K h.card σ h.frob).2.2.1

@[expose] noncomputable def d4Q {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}
    (h : D4Param p f K σ) : ↥(graphFixedRootGroup TwistTag.D4 K σ) →*
      DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ) :=
  (QuotientGroup.mk' (Subgroup.center ↥⁅twistedFixedGroup TwistTag.D4 K σ,
    twistedFixedGroup TwistTag.D4 K σ⁆)).comp (Subgroup.inclusion (fixedD4_derived h).ge)

theorem isCentralPQuot_d4Q {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}
    (h : D4Param p f K σ) : IsCentralPQuot p (d4Q h) := by
  have hΓ := fixedD4_derived h
  have : Finite K := h.finite
  have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hcenter : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot hσs
  have hker : (d4Q h).ker ≤ Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    change (QuotientGroup.mk (Subgroup.inclusion hΓ.ge x) :
      ↥⁅twistedFixedGroup TwistTag.D4 K σ, twistedFixedGroup TwistTag.D4 K σ⁆ ⧸ _) = 1 at hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := congrArg Subtype.val (hx (Subgroup.inclusion hΓ.ge y))
    exact Subtype.ext h2
  refine ⟨?_, hker, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨⟨x.1, hΓ.le x.2⟩, rfl⟩
  · have hk0 : (d4Q h).ker = ⊥ := by
      rw [← le_bot_iff, ← hcenter]
      exact hker
    rw [hk0]
    simp

theorem exists_r3frame [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 3) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hP : D4Param p f K σ),
      (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ),
        IsCentralPQuot p ε ∧
        (∀ t ∈ Tp3 hP, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = d4Q hP t) ∧
        ∀ x : F, ∃ t ∈ Tp3 hP, ε (Subgroup.inclusion h.F_le x) = d4Q hP t := by
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
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e hcop
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (d4Q hP) (isCentralPQuot_d4Q hP) _ hε₀
      (fun t ht => Tp3_exp hP t ht) (fun s hs t ht => Tp3_comm hP s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp3 hP X hexp) h.F_le h.F_exp h.F_comm h.maximal
    exact ⟨f, K, hKf, hKfin, σ, hP, hζ, ε, hε, hFT₁, hFT₂⟩
  · exact absurd hrt (by decide)
  · exact absurd ht (by decide)

theorem isCentralPQuot_id (p : ℕ) (M : Type) [Group M] : IsCentralPQuot p (MonoidHom.id M) := by
  refine ⟨Function.surjective_id, ?_, ?_⟩
  · rw [MonoidHom.ker_id]
    exact bot_le
  · rw [MonoidHom.ker_id]
    simp

theorem exists_r4frame [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 4) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime)
      (hP : F4Param p a K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* ↥(F4.reeGamma K a), IsCentralPQuot p ε ∧
        (∀ t ∈ Tp4 hP, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = t) ∧
        ∀ x : F, ∃ t ∈ Tp4 hP, ε (Subgroup.inclusion h.F_le x) = t := by
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
    obtain ⟨e'⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
    have hε₀ := isCentralPQuot_center e' hcop
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (MonoidHom.id ↥(F4.reeGamma K a))
      (isCentralPQuot_id p _) _ hε₀ (fun t ht => Tp4_exp hP t ht)
      (fun s hs t ht => Tp4_comm hP s t hs ht)
      (fun X hexp _ => exists_conj_into_Tp4 hP X hexp) h.F_le h.F_exp h.F_comm h.maximal
    exact ⟨a, K, hKf, hKfin, hchar, hP, hζ, ε, hε, hFT₁, hFT₂⟩
  · exact absurd ht (by decide)

end CFSG.RankThree.PartOne.KLAY
