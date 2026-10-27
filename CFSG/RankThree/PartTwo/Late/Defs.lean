module

public import CFSG.RankThree.PartTwo.Setup
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type*} [Group G]

@[expose] def IsE27 (A : Subgroup G) : Prop :=
  CFSG.Assembly.IsElemAbelian 3 A ∧ Nat.card A = 27

theorem isE27_of_mem_partTwoE {A : Subgroup G} (hA : A ∈ partTwoE G) : IsE27 A :=
  ⟨hA.1, hA.2.1⟩

theorem IsE27.map {G' : Type*} [Group G'] {A : Subgroup G} (hA : IsE27 A) (φ : G ≃* G') :
    IsE27 (A.map φ.toMonoidHom) :=
  ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 φ.toMonoidHom A hA.1,
    by rw [Subgroup.card_map_of_injective φ.injective, hA.2]⟩

theorem IsE27.pRank_eq [Finite G] {A : Subgroup G} (hA : IsE27 A) :
    CFSG.Open.pRank 3 A = 3 := by
  apply le_antisymm
  · have hle := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three A
    rwa [hA.2, show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.log_pow (by norm_num)] at hle
  · exact le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three A)
      ⟨A, le_rfl, hA.1, by rw [hA.2]; norm_num⟩

theorem IsE27.isPGroup {A : Subgroup G} (hA : IsE27 A) : IsPGroup 3 A :=
  IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)

theorem IsE27.le_gamma [Finite G] {A : Subgroup G} (hA : IsE27 A) : A ≤ gamma 2 A :=
  Subgroup.le_normalizer.trans (normalizer_le_gamma le_rfl (by rw [hA.pRank_eq]; norm_num))

@[expose] def scriptH (A M : Subgroup G) : Set (Subgroup G) :=
  {H | H ≠ ⊤ ∧ H = inSubgroup perfectResidual H ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧
    inSubgroup perfectResidual H ∈ oTwoComponentsIn H ∧
    CFSG.Open.pCoreOf 2 H ≠ CFSG.Open.pCoreOf 2 (H ⊓ M)}

@[expose] def scriptHStar (A M : Subgroup G) : Set (Subgroup G) :=
  {H | Maximal (· ∈ scriptH A M) H}

theorem mem_scriptH_iff {A M H : Subgroup G} :
    H ∈ scriptH A M ↔ H ≠ ⊤ ∧
      H = inSubgroup perfectResidual H ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧
      inSubgroup perfectResidual H ∈ oTwoComponentsIn H ∧
      CFSG.Open.pCoreOf 2 H ≠ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
  Iff.rfl

theorem scriptHStar_subset (A M : Subgroup G) : scriptHStar A M ⊆ scriptH A M :=
  fun _ hH => hH.prop

@[expose] def scriptJ (M H : Subgroup G) : Set (Subgroup G) :=
  {K | K ∈ oTwoComponentsIn M ∧ ¬ K ≤ H}

theorem mem_scriptJ_iff {M H K : Subgroup G} :
    K ∈ scriptJ M H ↔ K ∈ oTwoComponentsIn M ∧ ¬ K ≤ H :=
  Iff.rfl

noncomputable abbrev gammaOne [Finite G] (D : Subgroup G) : Subgroup G :=
  gamma 1 D

theorem one_le_pRank_three_iff [Finite G] {X : Subgroup G} (hX : IsPGroup 3 X) :
    1 ≤ CFSG.Open.pRank 3 X ↔ X ≠ ⊥ := by
  constructor
  · rintro h rfl
    have hle := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three
      (⊥ : Subgroup G)
    rw [Subgroup.card_bot, Nat.log_one_right] at hle
    omega
  · intro hne
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hnt : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' (by simpa using hn)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3
      (by rw [hn]; exact dvd_pow_self 3 hn0)
    refine le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three X)
      ⟨Subgroup.zpowers (x : G), ?_, ?_, ?_⟩
    · exact (Subgroup.zpowers_le).mpr x.2
    · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
        change (a : G) * b = b * a
        rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      · intro y hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hx3 : (x : G) ^ 3 = 1 := by
          rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, pow_one]

theorem gammaOne_le_iff [Finite G] {D M : Subgroup G} (hD : IsPGroup 3 D) :
    gammaOne D ≤ M ↔
      ∀ X : Subgroup G, X ≤ D → X ≠ ⊥ → Subgroup.normalizer (X : Set G) ≤ M := by
  rw [gammaOne, gamma_le_iff]
  refine forall_congr' fun X => imp_congr_right fun hXD => ?_
  rw [one_le_pRank_three_iff (hD.to_le hXD)]

@[expose] def Hyp191 (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ A M H : Subgroup G, IsE27 A → M ∈ scriptM (gamma 2 A : Set G) → A ≤ H →
    CFSG.Open.pCoreOf 2 H ≠ ⊥ → CFSG.Open.pCoreOf 2 (H ⊓ M) = CFSG.Open.pCoreOf 2 H

structure Sec18Std (G : Type) [Group G] [Finite G] (A M : Subgroup G) : Prop
    extends PartTwoStanding G where
  partTwoS_eq : partTwoS G = ∅
  mem_partTwoE : A ∈ partTwoE G
  mem_scriptM : M ∈ scriptM (gamma 2 A : Set G)

structure Sec19Std (G : Type) [Group G] [Finite G] : Prop extends PartTwoStanding G where
  partTwoS_eq : partTwoS G = ∅
  hyp191 : Hyp191 G

structure Hyp1921 (G : Type) [Group G] [Finite G] (A M N L : Subgroup G) : Prop
    extends Sec19Std G where
  mem_partTwoE : A ∈ partTwoE G
  mem_scriptM : M ∈ scriptM (gamma 2 A : Set G)
  mem_scriptM_N : N ∈ scriptM (A : Set G)
  ne : N ≠ M
  mem_oTwoComponentsIn : L ∈ oTwoComponentsIn N
  quotient_iso :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))

@[expose] def sectionCentralizer (A X Y : Subgroup G) : Set G :=
  {a | a ∈ A ∧ ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ Y}

@[expose] def normalClosureIn (M : Subgroup G) (c : G) : Subgroup G :=
  Subgroup.closure {x | ∃ m ∈ M, x = m * c * m⁻¹}

structure Hyp201 (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) : Prop
    extends PartTwoStanding G where
  partTwoS_eq : partTwoS G = ∅
  mem_partTwoE : A ∈ partTwoE G
  mem_scriptM : M ∈ scriptM (gamma 2 A : Set G)
  cases :
    (∃ H ∈ scriptHStar A M, CFSG.Open.pCoreOf 2 H ≠ ⊥ ∧ L = inSubgroup perfectResidual H ∧
      N = Subgroup.normalizer (L : Set G) ∧
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer {c}) ≠ ⊥ →
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ N)) ∨
    Hyp1921 G A M N L
  centralizer_eq :
    sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)

section MaximalTwoLocal

variable [Finite G] {M : Subgroup G}

omit [Finite G] in
theorem pCoreOf_ne_bot_of_isMaximalTwoLocal (hM : IsMaximalTwoLocal M) :
    CFSG.Open.pCoreOf 2 M ≠ ⊥ := by
  obtain ⟨P, hP, hP2, hMP⟩ := hM.1
  intro hbot
  apply hP
  rw [eq_bot_iff, ← hbot]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ hP2
  · rw [hMP]
    exact Subgroup.le_normalizer
  · rw [hMP]

theorem normalizer_pCoreOf_of_isMaximalTwoLocal (hM : IsMaximalTwoLocal M) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G)) :=
    ⟨_, pCoreOf_ne_bot_of_isMaximalTwoLocal hM, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  by_contra hne
  exact hM.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) hloc

theorem normalizer_self_of_isMaximalTwoLocal (hM : IsMaximalTwoLocal M) :
    Subgroup.normalizer (M : Set G) = M := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  calc Subgroup.normalizer (M : Set G)
      ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M
    _ = M := normalizer_pCoreOf_of_isMaximalTwoLocal hM

theorem mem_of_map_conj_eq_of_isMaximalTwoLocal (hM : IsMaximalTwoLocal M) {g : G}
    (hg : M.map (MulAut.conj g).toMonoidHom = M) : g ∈ M := by
  rw [← normalizer_self_of_isMaximalTwoLocal hM, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hg]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hg] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    have : y = x := mul_left_cancel (mul_right_cancel h1)
    rwa [← this]

end MaximalTwoLocal

theorem isPLocal_two_map {G' : Type*} [Group G'] {H : Subgroup G} (hH : IsPLocal 2 H)
    (φ : G ≃* G') : IsPLocal 2 (H.map φ.toMonoidHom) := by
  obtain ⟨P, hP, hP2, hHP⟩ := hH
  refine ⟨P.map φ.toMonoidHom,
    fun h => hP ((Subgroup.map_eq_bot_iff_of_injective P φ.injective).mp h), hP2.map _, ?_⟩
  rw [hHP, Subgroup.map_equiv_normalizer_eq]

theorem isMaximalTwoLocal_map {G' : Type*} [Group G'] {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) (φ : G ≃* G') : IsMaximalTwoLocal (M.map φ.toMonoidHom) := by
  refine ⟨isPLocal_two_map hM.1 φ, fun H hlt hH => ?_⟩
  have hH' := isPLocal_two_map hH φ.symm
  have hback : (H.map φ.symm.toMonoidHom).map φ.toMonoidHom = H := by
    rw [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G' from
      MonoidHom.ext φ.apply_symm_apply, Subgroup.map_id]
  have hlt' : M < H.map φ.symm.toMonoidHom := by
    rw [← hback] at hlt
    exact (MulEquiv.mapSubgroup φ).lt_iff_lt.mp hlt
  exact hM.2 _ hlt' hH'

theorem map_conj_mem_scriptM_gamma [Finite G] {A M : Subgroup G}
    (hM : M ∈ scriptM (gamma 2 A : Set G)) (g : G) :
    M.map (MulAut.conj g).toMonoidHom ∈
      scriptM (gamma 2 (A.map (MulAut.conj g).toMonoidHom) : Set G) := by
  refine ⟨isMaximalTwoLocal_map hM.1 (MulAut.conj g), ?_⟩
  rw [← map_gamma (MulAut.conj g) 2 A]
  exact Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hM.2

@[expose] def scriptH₀ (A M : Subgroup G) : Set (Subgroup G) :=
  {H | H = inSubgroup perfectResidual H ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧
    inSubgroup perfectResidual H ∈ oTwoComponentsIn H ∧
    CFSG.Open.pCoreOf 2 H ≠ CFSG.Open.pCoreOf 2 (H ⊓ M)}

theorem mem_scriptH₀_iff {A M H : Subgroup G} :
    H ∈ scriptH₀ A M ↔ H = inSubgroup perfectResidual H ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧
      inSubgroup perfectResidual H ∈ oTwoComponentsIn H ∧
      CFSG.Open.pCoreOf 2 H ≠ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
  Iff.rfl

theorem mem_scriptH_iff_mem_scriptH₀ {A M H : Subgroup G} :
    H ∈ scriptH A M ↔ H ∈ scriptH₀ A M ∧ H ≠ ⊤ :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h2, h3, h4⟩, h1⟩, fun ⟨⟨h2, h3, h4⟩, h1⟩ => ⟨h1, h2, h3, h4⟩⟩

end CFSG.RankThree.PartTwo.Late
