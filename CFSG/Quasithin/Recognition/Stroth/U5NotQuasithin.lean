module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5
public import CFSG.ClassicalGroups.UnitaryFlag.PointStabilizerRank
public import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LocalAnalysis.EvenBN.U5

private theorem pRank_eq_of_subgroupMulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {A : Subgroup G} {B : Subgroup H} (e : ↥A ≃* ↥B) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p A = CFSG.Open.pRank p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← CFSG.Quasithin.pRank_top_subtype A, ← CFSG.Quasithin.pRank_top_subtype B]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e

private theorem pRank_map_of_injective {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {A : Subgroup G} (f : G →* H) (hf : Function.Injective f) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (A.map f) = CFSG.Open.pRank p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← CFSG.Quasithin.pRank_top_subtype (A.map f), ← CFSG.Quasithin.pRank_top_subtype A]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
    (Subgroup.equivMapOfInjective A f hf)).symm

private theorem pCoreOf_eq_bot_iff_of_mulEquiv {G H : Type*} [Group G] [Group H]
    {A : Subgroup G} {B : Subgroup H} (e : ↥A ≃* ↥B) (p : ℕ) :
    pCoreOf p A = ⊥ ↔ pCoreOf p B = ⊥ := by
  have h1 : Nat.card (pCoreOf p A) = Nat.card (pCoreOf p B) :=
    card_pCoreOf_of_mulEquiv e p
  rw [← Subgroup.card_eq_one (H := pCoreOf p A), ← Subgroup.card_eq_one (H := pCoreOf p B), h1]

section Model

variable {n : ℕ} {K : Type} [Field K]

theorem exists_prime_three_le_pRank_u5PtP (h : UnitaryFieldData 2 n K) (hn : n ≠ 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ p ∣ 2 ^ n + 1 ∧ 3 ≤ CFSG.Open.pRank p (u5PtP h) :=
  CFSG.ClassicalGroups.UnitaryFlag.exists_prime_three_le_pRank_projIsoStabilizer h hn

theorem pCoreOf_u5PtP_ne_bot (h : UnitaryFieldData 2 n K) : pCoreOf 2 (u5PtP h) ≠ ⊥ := by
  have hZle : ZPsub h ≤ u5PtStab h :=
    (ZPsub_le_U (h := h)).trans ((hypUnitriangular_le_hypBorel h).trans
      (hypBorel_le_isoStabilizer h (by norm_num) (by norm_num)))
  have hNle : (ZPsub h).map (hypProj h 2 1) ≤ u5PtP h := Subgroup.map_mono hZle
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hNle
    (u5PtP_le_normalizer (h := h)) (isPGroup_map_ZPsub (h := h))
  intro hbot
  refine map_ZPsub_ne_bot (h := h) (le_antisymm ?_ bot_le)
  rwa [hbot] at hle

end Model

theorem false_of_three_le_pRank_parabolic {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hPle : P ≤ L1 ⊔ L2 ⊔ S) (h3 : 3 ≤ CFSG.Open.pRank p P)
    (hO : pCoreOf 2 P ≠ ⊥) : False := by
  have hR2 : IsPGroup 2 (pCoreOf 2 P) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).map P.subtype
  have hnorm : P ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) P
  have hq := hF.2.1 p hp hp2 (pCoreOf 2 P)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans hPle) hO hR2
  have hmono : CFSG.Open.pRank p P ≤ CFSG.Open.pRank p ((L1 ⊔ L2 ⊔ S) ⊓
      Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt (le_inf hPle hnorm)
  exact absurd (le_trans h3 (le_trans hmono hq)) (by norm_num)

theorem eq_two_of_isAmalgamOfGroup_psu5 {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112Hyp L1 L2 S) (hn : 1 ≤ n)
    (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 5 n)) : n = 2 := by
  by_contra hn2
  obtain ⟨Y, _, hY, T, ⟨M₁, M₂, hpair, ⟨iso⟩⟩⟩ := hA
  let e1 := iso.φ1
  let e2 := iso.φ2
  rcases hY with ⟨-, hc⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
  swap
  · exact absurd hn0 (by norm_num)
  swap
  · exact absurd hn0 (by norm_num)
  swap
  · exact absurd hn0 (by norm_num)
  obtain ⟨hadm, K, _, _, hK, ⟨eS⟩⟩ := hc
  have hcard : Nat.card K = 2 ^ (2 * n) := by
    rw [hK, ← pow_mul, Nat.mul_comm n 2]
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, hcard⟩
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  let e' : hypPSU h 2 1 ≃* Y := (hypPSUEquivStatedProj h hR (by norm_num)).trans eS.symm
  haveI : Finite Y := Finite.of_injective e'.symm.toMonoidHom e'.symm.injective
  obtain ⟨c, -, hPc⟩ := (u5_yamStd (h := h)).pair e'.symm hpair
  obtain ⟨p, hp, hp2, hp5, hpd, h3⟩ := exists_prime_three_le_pRank_u5PtP h hn2
  have hconj : ∀ A : Subgroup (hypPSU h 2 1),
      CFSG.Open.pRank p (A.map (MulAut.conj c).toMonoidHom) = CFSG.Open.pRank p A := fun A =>
    pRank_map_of_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective hp
  have hOu5 : pCoreOf 2 (u5PtP h) ≠ ⊥ := pCoreOf_u5PtP_ne_bot h
  have hcinj : Function.Injective (MulAut.conj c).toMonoidHom := fun x y h =>
    (MulAut.conj c).injective h
  have hOconj : pCoreOf 2 ((u5PtP h).map (MulAut.conj c).toMonoidHom) ≠ ⊥ := by
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (r := 2) (MulAut.conj c) (u5PtP h)]
    exact fun hq => hOu5
      ((Subgroup.map_eq_bot_iff_of_injective (pCoreOf 2 (u5PtP h)) hcinj).mp hq)
  have hP1eq : CFSG.Open.pRank p (L1 ⊔ bigB L1 L2 S) = CFSG.Open.pRank p M₁ :=
    pRank_eq_of_subgroupMulEquiv e1 hp
  have hP2eq : CFSG.Open.pRank p (L2 ⊔ bigB L1 L2 S) = CFSG.Open.pRank p M₂ :=
    pRank_eq_of_subgroupMulEquiv e2 hp
  have hP1le : L1 ⊔ bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S := parabolic_le_sup L1 L2 S
  have hP2le : L2 ⊔ bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
    rw [← bigB_comm L1 L2 S, sup_comm L1 L2]
    exact parabolic_le_sup L2 L1 S
  rcases hPc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hO1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≠ ⊥ := by
      intro hbot
      have hM : pCoreOf 2 M₁ = ⊥ := (pCoreOf_eq_bot_iff_of_mulEquiv e1 2).mp hbot
      apply hOconj
      have hM' : pCoreOf 2 (M₁.map e'.symm.toMonoidHom) = ⊥ :=
        (pCoreOf_eq_bot_iff_of_mulEquiv
          (Subgroup.equivMapOfInjective M₁ e'.symm.toMonoidHom e'.symm.injective) 2).mp hM
      rwa [h1] at hM'
    have hrank : CFSG.Open.pRank p (L1 ⊔ bigB L1 L2 S) = CFSG.Open.pRank p (u5PtP h) := by
      rw [hP1eq, ← pRank_map_of_injective e'.symm.toMonoidHom e'.symm.injective hp, h1, hconj]
    exact false_of_three_le_pRank_parabolic hF hp hp2 hP1le (by rw [hrank]; exact h3) hO1
  ·
    have hO2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≠ ⊥ := by
      intro hbot
      have hM : pCoreOf 2 M₂ = ⊥ := (pCoreOf_eq_bot_iff_of_mulEquiv e2 2).mp hbot
      apply hOconj
      have hM' : pCoreOf 2 (M₂.map e'.symm.toMonoidHom) = ⊥ :=
        (pCoreOf_eq_bot_iff_of_mulEquiv
          (Subgroup.equivMapOfInjective M₂ e'.symm.toMonoidHom e'.symm.injective) 2).mp hM
      rwa [h2] at hM'
    have hrank : CFSG.Open.pRank p (L2 ⊔ bigB L1 L2 S) = CFSG.Open.pRank p (u5PtP h) := by
      rw [hP2eq, ← pRank_map_of_injective e'.symm.toMonoidHom e'.symm.injective hp, h2, hconj]
    exact false_of_three_le_pRank_parabolic hF hp hp2 hP2le (by rw [hrank]; exact h3) hO2

end CFSG.Quasithin.Stroth
