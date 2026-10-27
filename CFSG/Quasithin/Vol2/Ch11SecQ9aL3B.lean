module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3A
public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X6

theorem isCComponent_self {G : Type} [Group G] [Finite G] {X : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hs : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X)) : quasithinIsCComponent X X := by
  refine ⟨?_, hX, IsSubnormal.refl X, ?_⟩
  · rintro rfl
    have hss : Subsingleton (↥(⊥ : Subgroup G) ⧸ CFSG.pCore 2 ↥(⊥ : Subgroup G)) :=
      ⟨fun a b => by
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        congr 1
        exact Subsingleton.elim _ _⟩
    exact not_nontrivial_iff_subsingleton.mpr hss hs.toNontrivial
  · intro L hLX hL hLp hLsub
    have hpc := CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥X
    obtain ⟨P, hPX, hPn, hLP⟩ := CFSG.Quasithin.A3.subnormal_exists_normal_of_lt hLsub hLX
    have : (P.subgroupOf X).Normal := hPn
    have hNs : Group.IsSolvable ↥(pCoreOf 2 X) := isSolvable_pCoreOf_two X
    rcases Subgroup.Normal.eq_bot_or_eq_top
        ((P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) with h | h
    · have hPN : P.subgroupOf X ≤ CFSG.pCore 2 ↥X := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
        exact h
      have hLO : L ≤ pCoreOf 2 X := by
        intro k hk
        have hkX : k ∈ X := hLX.le hk
        exact ⟨⟨k, hkX⟩, hpc ▸ hPN (show (⟨k, hkX⟩ : ↥X) ∈ P.subgroupOf X from hLP hk), rfl⟩
      have hLs : Group.IsSolvable ↥L :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLO)
          (Subgroup.inclusion_injective hLO)
      have := (isSolvable_iff_perfectCore_eq_bot L).mp hLs
      rw [perfectCore_eq_self_of_perfect hLp] at this
      exact hL this
    · have hXeq : X = P ⊔ pCoreOf 2 X := by
        refine le_antisymm ?_ (sup_le hPX.le (Subgroup.map_subtype_le _))
        intro x hx
        have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hx⟩ ∈
            (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
          rw [h]; exact Subgroup.mem_top _
        obtain ⟨p, hp, hpx⟩ := hmem
        have hpn : p⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥X := QuotientGroup.eq.mp hpx
        have hx' : x = (p : G) * ((p⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
        rw [hx']
        exact Subgroup.mul_mem_sup hp ⟨p⁻¹ * ⟨x, hx⟩, hpc ▸ hpn, rfl⟩
      have hle := perfectCore_le_of_sup_solvable hPX.le hPn hXeq hNs
      rw [perfectCore_eq_self_of_perfect hX] at hle
      exact hPX.not_ge hle

variable {Q : Type} [Group Q]

theorem eq_of_le_of_card_eq_960 [Finite Q] [IsSimpleGroup Q] (hQ : Nat.card Q = 20160)
    {B P : Subgroup Q} (hBP : B ≤ P) (hP : P ≠ ⊤) (hB : Nat.card ↥B = 960) : B = P := by
  have hBi : B.index = 21 := by
    have h := B.card_mul_index
    rw [hB, hQ] at h
    omega
  have hdvd : P.index ∣ 21 := hBi ▸ Subgroup.index_dvd_of_le hBP
  have hcore : P.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ P.normalCore_le)) hP
  have hfact := P.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot, hQ] at hfact
  have hPi : P.index = 21 := by
    have hmem : P.index ∈ Nat.divisors 21 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 21 = {1, 3, 7, 21} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd (Subgroup.index_eq_one.mp h) hP
    · rw [h] at hfact
      exact absurd hfact (by norm_num [Nat.factorial])
    · rw [h] at hfact
      exact absurd hfact (by norm_num [Nat.factorial])
    · exact h
  apply Subgroup.eq_of_le_of_card_ge hBP
  have h1 := P.card_mul_index
  have h2 := B.card_mul_index
  rw [hPi] at h1
  rw [hBi] at h2
  omega

structure L34Parabs (S : Subgroup Q) (P : Fin 2 → Subgroup Q) : Prop where
  ne : P 0 ≠ P 1
  covBy : ∀ j, P j ⋖ ⊤
  le : ∀ j, S ≤ P j
  perfect : ∀ j, ⁅P j, P j⁆ = P j
  card : ∀ j, Nat.card ↥(P j) = 960
  levi : ∀ j, ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥(P j) ⧸ CFSG.pCore 2 ↥(P j) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  simple : ∀ j, IsSimpleGroup (↥(P j) ⧸ CFSG.pCore 2 ↥(P j))
  normalizer_le : ∀ j, Subgroup.normalizer (S : Set Q) ≤ P j
  classify : ∀ X : Subgroup Q, X ≠ ⊥ → ⁅X, X⁆ = X → S ≤ Subgroup.normalizer (X : Set Q) →
    X = P 0 ∨ X = P 1 ∨ X = ⊤

abbrev pm34 {K : Type} [Field K] (φ : Q ≃* projectiveSL 3 K) (j : Fin 2) : Subgroup Q :=
  (parab34 K j).map φ.symm.toMonoidHom

theorem exists_l34Parabs [Finite Q] (hQ : IsPSL 3 2 2 Q) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) : ∃ P : Fin 2 → Subgroup Q, L34Parabs S P := by
  have hsimp : IsSimpleGroup Q := (CFSG.LieType.Simplicity.fam_PSL_simplicity Q 3 2 2 hQ).2
  obtain ⟨K, _, _, _, φ, hK, hφS, hres, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hQ hS
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hres' : ResidualOvergroupsAt Q S (pm34 φ) := hres
  obtain ⟨hne, hSP, hmax, -, hC2, -⟩ := hres'
  have hQc : Nat.card Q = 20160 := by
    rw [Nat.card_congr φ.toEquiv, card_projectiveSL_four hK4]
  have hcov : ∀ j, pm34 φ j ⋖ ⊤ := fun j => (hmax (pm34 φ j) (hSP j)).mpr ⟨j, rfl⟩
  have hcard : ∀ j, Nat.card ↥(dInf (pm34 φ j)) = 960 := by
    intro j
    rw [pm34, dInf_map_equiv, Subgroup.card_map_of_injective φ.symm.injective,
      (parab34_structure hK4 j).1]
  have hdP : ∀ j, dInf (pm34 φ j) = pm34 φ j := fun j =>
    eq_of_le_of_card_eq_960 hQc (dInf_le _) (hcov j).lt.ne (hcard j)
  have hlevi : ∀ j, Nonempty (↥(pm34 φ j) ⧸ CFSG.pCore 2 ↥(pm34 φ j) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro j
    obtain ⟨-, -, ⟨e⟩⟩ := parab34_structure hK4 j
    have hPj : pm34 φ j = (dInf (parab34 K j)).map φ.symm.toMonoidHom := by
      rw [← dInf_map_equiv, ← pm34, hdP j]
    let f : ↥(pm34 φ j) ≃* ↥(dInf (parab34 K j)) :=
      (MulEquiv.subgroupCongr hPj).trans
        (Subgroup.equivMapOfInjective _ _ φ.symm.injective).symm
    exact ⟨(QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)).trans e⟩
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple
      (CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hK4.ge)
  refine ⟨pm34 φ, hne, hcov, hSP, fun j => ?_, fun j => ?_, fun j => ⟨K, inferInstance,
    inferInstance, hK4, hlevi j⟩, fun j => ?_, fun j => ?_, ?_⟩
  · have h := Subgroup.isPerfect_iff.mp (dInf_isPerfect (pm34 φ j))
    rwa [hdP j] at h
  · rw [← hdP j, hcard j]
  · obtain ⟨e⟩ := hlevi j
    exact e.isSimpleGroup
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : (Subgroup.normalizer (S : Set Q)).map φ.toMonoidHom ≤ parab34 K j := by
      rw [Subgroup.map_equiv_normalizer_eq, hφS]
      exact normalizer_le_parab34 j
    intro x hx
    exact ⟨φ x, h1 ⟨x, hx, rfl⟩, by simp⟩
  · intro X hX1 hXp hSX
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSs : Group.IsSolvable ↥S := by
      have := hS.2.1.isNilpotent
      infer_instance
    have hcore : perfectCore (X ⊔ S) = X := perfectCore_sup_eq hXp hSs hSX
    by_cases htop : X ⊔ S = ⊤
    · right; right
      have hXn : X.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
        exact sup_le Subgroup.le_normalizer hSX
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal X).resolve_left hX1
    · have hns : ¬ Group.IsSolvable ↥(X ⊔ S) := by
        intro hsol
        have hXs : Group.IsSolvable ↥X :=
          Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion le_sup_left)
            (Subgroup.inclusion_injective (le_sup_left : X ≤ X ⊔ S))
        apply hX1
        rw [← perfectCore_eq_self_of_perfect hXp]
        exact (isSolvable_iff_perfectCore_eq_bot X).mp hXs
      obtain ⟨j, -, hdj⟩ := hC2 (X ⊔ S) le_sup_right htop hns
      rw [CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, hcore, hdP j] at hdj
      fin_cases j
      · exact Or.inl hdj
      · exact Or.inr (Or.inl hdj)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
