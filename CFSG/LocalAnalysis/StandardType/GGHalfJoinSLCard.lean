module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfCentralizer
public import CFSG.LocalAnalysis.StandardType.GGHalfNumberTheory
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

private lemma card_SL_eq_one_of_le_one {k : ℕ} (hk : k ≤ 1) (K : Type) [Field K] :
    Nat.card (SpecialLinearGroup (Fin k) K) = 1 := by
  haveI : Subsingleton (SpecialLinearGroup (Fin k) K) := by
    interval_cases k
    · refine ⟨fun A B => Subtype.ext (Matrix.ext ?_)⟩
      intro i j
      exact Fin.elim0 i
    · haveI : Subsingleton (Fin 1) := ⟨fun i j => Fin.ext (by omega)⟩
      refine ⟨fun A B => Subtype.ext (Matrix.ext ?_)⟩
      intro i j
      have hA : (A : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
        rw [← Matrix.det_fin_one (A : Matrix (Fin 1) (Fin 1) K)]
        exact A.2
      have hB : (B : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
        rw [← Matrix.det_fin_one (B : Matrix (Fin 1) (Fin 1) K)]
        exact B.2
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0, hA, hB]
  exact Nat.card_of_subsingleton (1 : SpecialLinearGroup (Fin k) K)

private lemma card_SL_zmod_two_eq_card_SL_f2 (N : ℕ) :
    Nat.card (SpecialLinearGroup (Fin N) (ZMod 2)) =
      Nat.card (SpecialLinearGroup (Fin N) F2) := by
  have : Fintype F2 := Fintype.ofFinite _
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  let ε : F2 ≃+* ZMod 2 :=
    FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hcard, ZMod.card])
  let μ : SpecialLinearGroup (Fin N) F2 →* SpecialLinearGroup (Fin N) (ZMod 2) :=
    SpecialLinearGroup.map ε.toRingHom
  let μ' : SpecialLinearGroup (Fin N) (ZMod 2) →* SpecialLinearGroup (Fin N) F2 :=
    SpecialLinearGroup.map ε.symm.toRingHom
  have hμμ' : ∀ g, μ (μ' g) = g := by
    intro g
    ext i j
    simp [μ, μ']
  have hμ'μ : ∀ g, μ' (μ g) = g := by
    intro g
    ext i j
    simp [μ, μ']
  let μe : SpecialLinearGroup (Fin N) F2 ≃* SpecialLinearGroup (Fin N) (ZMod 2) :=
    MonoidHom.toMulEquiv μ μ' (MonoidHom.ext hμ'μ) (MonoidHom.ext hμμ')
  exact (Nat.card_congr μe.toEquiv).symm

theorem GGHalfJoin.card_eq_of_hasLabel_typeA {G : Type} [Group G] {J : Subgroup G} {m : ℕ}
    (hm : 2 ≤ m) (hZ : Subgroup.center ↥J = ⊥)
    (hlab : GGHasLabel ⟨.A, m, 1⟩ (↥J ⧸ Subgroup.center ↥J)) :
    Nat.card ↥J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) := by
  have hΛ : LargeEvenInLambda2 ⟨.A, m, 1⟩ := by
    show 1 ≤ 1 ∧ (1 ≤ m ∧ (m = 1 → 2 ≤ 1))
    exact ⟨le_rfl, by omega, fun h => by omega⟩
  have hmod : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL (m + 1) 2 1 :=
    statedClassicalModel_of_hasLabel_typeA hΛ hlab
  obtain ⟨θ⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hmod
  have hquot : Nat.card ↥J = Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  rw [hquot, Nat.card_congr θ.toEquiv]
  exact card_SL_zmod_two_eq_card_SL_f2 (m + 1)

theorem GGHalfJoin.supp_eq_two_of_component {m : ℕ} (hm : 3 ≤ m)
    {a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2} (ha : orderOf a = 3)
    {J : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)}
    (hJ : IsComponentOf J
      (Subgroup.centralizer ({a} : Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))))
    (hcard : Nat.card ↥J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2)) :
    GGHalf.supp a = 2 := by
  have ha3 : a ^ 3 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  obtain ⟨Z, Λ, hZc, hΛc, -, -, -, hcomp⟩ := centralizer_blocks (n := m + 1 + 1) ha3
  have hsupp_le : GGHalf.supp a ≤ m + 1 + 1 + 1 := by
    unfold GGHalf.supp
    exact Matrix.rank_le_height _
  have hbase : 1 < Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) := by
    have hmono := card_sl_two_strictMono (k := 2) (l := m + 1) (by norm_num) (by omega)
    have hpos : 1 ≤ Nat.card (SpecialLinearGroup (Fin 2) F2) := by
      have := Nat.card_pos (α := SpecialLinearGroup (Fin 2) F2)
      omega
    exact lt_of_le_of_lt hpos hmono
  rcases hcomp J hJ with rfl | rfl
  ·
    rw [hZc] at hcard
    have hk2 : 2 ≤ m + 1 + 1 + 1 - GGHalf.supp a := by
      by_contra h
      have h1 : m + 1 + 1 + 1 - GGHalf.supp a ≤ 1 := by
        have := not_le.mp h
        omega
      have hc1 := card_SL_eq_one_of_le_one h1 F2
      rw [hc1] at hcard
      omega
    have hkeq : m + 1 + 1 + 1 - GGHalf.supp a = m + 1 := by
      rcases lt_trichotomy (m + 1 + 1 + 1 - GGHalf.supp a) (m + 1) with h | h | h
      · exfalso
        have hlt := card_sl_two_strictMono
          (k := m + 1 + 1 + 1 - GGHalf.supp a) (l := m + 1) hk2 h
        omega
      · exact h
      · exfalso
        have hlt := card_sl_two_strictMono
          (k := m + 1) (l := m + 1 + 1 + 1 - GGHalf.supp a) (by omega) h
        omega
    omega
  ·
    rw [hΛc] at hcard
    have hrle : 2 * (GGHalf.supp a / 2) ≤ m + 1 + 1 + 1 := by
      have hdiv : GGHalf.supp a / 2 * 2 ≤ GGHalf.supp a := Nat.mul_le_of_le_div 2 _ _ le_rfl
      omega
    by_cases hr : GGHalf.supp a / 2 ≤ 1
    · exfalso
      have hc1 := card_SL_eq_one_of_le_one hr (GaloisField 2 2)
      rw [hc1] at hcard
      omega
    · exfalso
      have hr2 : 2 ≤ GGHalf.supp a / 2 := by omega
      exact (card_sl_four_ne_card_sl_two (r := GGHalf.supp a / 2) (m := m + 1)
        hr2 (by omega) (by omega)) hcard

end CFSG.StandardType

end
