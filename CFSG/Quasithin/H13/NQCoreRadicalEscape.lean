module

public import CFSG.Quasithin.H13.NQCoreIntrinsicAction
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

@[expose] def StmtOriginalWitnessSingleton : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ (p : ℕ) (X : Subgroup G), p.Prime → 5 ≤ p →
      X ≤ (CFSG.solvableRadical ↥L).map L.subtype → (X.subgroupOf L).Characteristic →
      CFSG.pCore 2 X ≠ ⊥ → NoPQuotient 2 X → IsPGroup p (X ⧸ CFSG.pCore 2 X) →
      Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p → CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 →
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      (∀ W : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ W, normalizerFrattiniConj X l w ∈ W) →
        W = ⊥ ∨ W = ⊤) →
      U3.UniqueMaxTwoLocal (X ⊔ T) M

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_of_irreducible {W : Type*} [Group W] [Finite W] {p : ℕ} (hp : p.Prime)
    (hpW : ∀ w : W, w ^ p = 1) (hW : Nat.card W = p ^ 2) (S : Set (MulAut W))
    (hirr : ∀ Y : Subgroup W, (∀ f ∈ S, ∀ y ∈ Y, f y ∈ Y) → Y = ⊥ ∨ Y = ⊤) :
    ∃ f ∈ S, f ≠ 1 := by
  by_contra hS
  push Not at hS
  have : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hW]
    exact Nat.one_lt_pow two_ne_zero hp.one_lt
  obtain ⟨w, hw⟩ := exists_ne (1 : W)
  have hord : orderOf w = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hpW w)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw
    · exact h1
  rcases hirr (zpowers w) fun f hf y hy => by rw [hS f hf]; exact hy with h1 | h1
  · exact hw ((mem_bot).mp (h1 ▸ mem_zpowers w))
  · have h2 := Nat.card_zpowers w
    rw [h1, Subgroup.card_top, hW, hord] at h2
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem stmtOriginalRadicalEscape_of
    (hsing : StmtOriginalWitnessSingleton) : StmtOriginalRadicalEscape := by
  intro G _ _ T L M h
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (CFSG.solvableRadical ↥L).map L.subtype with hNdef
  obtain ⟨hNc, hNs, -, -⟩ := Setup.Offender.solvableRadical_characterization ↥L
  have hNL : N ≤ L := map_subtype_le _
  have hNsolv : Group.IsSolvable ↥N := by
    have := hNs
    exact Group.isSolvable_of_surjective (f := ((CFSG.solvableRadical ↥L).equivMapOfInjective
      L.subtype L.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hTN : T ≤ normalizer (N : Set G) :=
    h.t_le.trans (h.eq_normalizer.le.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _))
  have hTsolv : Group.IsSolvable ↥T := by
    have : Group.IsNilpotent ↥T := h.sylow.1.isNilpotent
    infer_instance
  have hSsolv : Group.IsSolvable ↥(N ⊔ T) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hTN hNsolv hTsolv
  have hSM : N ⊔ T ≤ M := sup_le (hNL.trans h.l_le) h.t_le
  have hO2M : pCoreOf 2 M ≠ ⊥ := by
    have h1 := NQRigid.pCore_map_ne_bot_of_qtnq h
    assumption
  have hMT : pCoreOf 2 M ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowIn_of_quasithin h.sylow h.t_le)
  have hMS : pCoreOf 2 M ≤ pCoreOf 2 (N ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hMT.trans le_sup_right)
      (hSM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hwit : ∀ (p₀ : ℕ) (X₀ : Subgroup G), p₀.Prime → 5 ≤ p₀ →
      X₀ ≤ N → (X₀.subgroupOf L).Characteristic →
      CFSG.pCore 2 X₀ ≠ ⊥ → NoPQuotient 2 X₀ → IsPGroup p₀ (X₀ ⧸ CFSG.pCore 2 X₀) →
      Monoid.exponent (X₀ ⧸ CFSG.pCore 2 X₀) = p₀ → CFSG.pRank p₀ (X₀ ⧸ CFSG.pCore 2 X₀) = 2 →
      Nat.card ((X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)) = p₀ ^ 2 →
      (∃ l : normalizer (X₀ : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X₀ l ≠ 1) →
      (∀ W : Subgroup ((X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)),
        (∀ l : normalizer (X₀ : Set G), (l : G) ∈ L → ∀ w ∈ W,
          normalizerFrattiniConj X₀ l w ∈ W) → W = ⊥ ∨ W = ⊤) →
      U3.UniqueMaxTwoLocal (X₀ ⊔ T) M ∧
        ∀ J : Subgroup G, quasithinIsMaxTwoLocal J → T ≤ J → J ≠ M → ¬ X₀ ⊔ T ≤ J := by
    intro p₀ X₀ hp₀ hp₀5 hX₀R hX₀c hX₀2 hX₀no hpg hexp hrk hW hLW hirr
    have hU := hsing G T L M h p₀ X₀ hp₀ hp₀5 hX₀R hX₀c hX₀2 hX₀no hpg hexp hrk hW hLW hirr
    exact ⟨hU, fun J hJ _ hJM hXJ => hJM (hU.2.2 J hJ hXJ)⟩
  obtain ⟨p₀, hp₀, hp₀5, X₀, -, hX₀c, hX₀R, hX₀no, hexp, hrk, hX₀2, -, hW, hirr, -, -⟩ :=
    NQRigid.configuration_centralizer_conjugate_rigidity_witness h
  have : Fact p₀.Prime := ⟨hp₀⟩
  have hpg : IsPGroup p₀ (X₀ ⧸ CFSG.pCore 2 X₀) := fun g =>
    ⟨1, by rw [pow_one, ← hexp]; exact Monoid.pow_exponent_eq_one g⟩
  have hLW : ∃ l : normalizer (X₀ : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X₀ l ≠ 1 := by
    obtain ⟨f, ⟨l, hlL, rfl⟩, hf⟩ := exists_ne_one_of_irreducible hp₀
      (fun w => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
        rw [← QuotientGroup.mk_pow, ← hexp, Monoid.pow_exponent_eq_one, QuotientGroup.mk_one])
      hW {f | ∃ l : normalizer (X₀ : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X₀ l = f}
      (fun Y hY => hirr Y fun l hl y hy => hY _ ⟨l, hl, rfl⟩ y hy)
    exact ⟨l, hlL, hf⟩
  have hX₀ := hwit p₀ X₀ hp₀ hp₀5 hX₀R hX₀c hX₀2 hX₀no hpg hexp hrk hW hLW hirr
  refine ⟨hSsolv, le_sup_right, hSM, hO2M, hMS, fun J hJ hTJ hJM => ?_, hwit⟩
  have hNJ : ¬ N ≤ J := fun hNJ => hX₀.2 J hJ hTJ hJM (sup_le (hX₀R.trans hNJ) hTJ)
  exact ⟨hNJ, fun hSJ => hNJ (le_sup_left.trans hSJ)⟩

end CFSG.Quasithin.H13.NQCore
