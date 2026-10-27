module

public import CFSG.RankThree.PartOne.KFCL.GenDefs
public import CFSG.RankThree.PartOne.K1320.L4Frame
public import CFSG.RankThree.PartOne.K159.RowFourLayer
public import CFSG.RankThree.PartOne.K1214.SylowSL2
public import CFSG.RankThree.PartOne.K133.KillL2
public import CFSG.RankThree.PartOne.KF.ClsPSLSmall
public import CFSG.RankThree.PartOne.S12.Sec15Lemmas

public section

namespace CFSG.RankThree.PartOne.KFR4

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFCL
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped MatrixGroups

theorem pRank_le_one_of_equiv_sl2 {X F : Type} [Group X] [Finite X] [Field F] [Finite F]
    [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) : CFSG.pRank p X ≤ 1 := by
  have hpF : NeZero (p : F) := ⟨fun h0 => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp ((CharP.cast_eq_zero_iff F 2 p).mp h0)).symm⟩
  refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le hp.one_lt fun A hA => ?_
  have hpow : ∀ x : A, x ^ p = 1 := fun x =>
    Subtype.ext (CFSG.elemPow_eq_one_of_isElementaryAbelian (x : X) x.2)
  let A' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := A.map e.toMonoidHom
  have hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpow' : ∀ x ∈ A', x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show e x ^ p = 1
    have h1 : x ^ p = 1 := by simpa using congrArg Subtype.val (hpow ⟨x, hx⟩)
    rw [← map_pow, h1, map_one]
  have hcyc : IsCyclic A' := K133.isCyclic_of_commuting_pow_eq_one_sl2 hp A' hcomm hpow'
  have hexp : Monoid.exponent A' ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hpow' x x.2)
  have hcard : Nat.card A' ≤ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos hexp
  rw [pow_one]
  calc Nat.card A = Nat.card A' := (Subgroup.card_map_of_injective e.injective).symm
    _ ≤ p := hcard

theorem localRank_le_one_of_equiv_sl2 {X F : Type} [Group X] [Finite X] [Field F] [Finite F]
    [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) : localRank p X ≤ 1 :=
  (KFU.localRank_le_open_pRank hp).trans
    (by rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact pRank_le_one_of_equiv_sl2 hp hp2 e)

theorem card_center_eq_one_of_equiv {X Y : Type} [Group X] [Group Y] (hY : Subgroup.center Y = ⊥)
    (e : X ≃* Y) : Nat.card (Subgroup.center X) = 1 := by
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hY]
  exact Subgroup.card_bot

theorem kfAtRow_four
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS13 : S15K.Sec13Avail) (hN156 : Node156) : KFAtRow 4 := by
  intro G _ _ p A c L E h15 hF hF13 hout t ht
  have hout4 : Outcome152Four p E A (lieGenerated p E) := hout
  have h := h15.h12
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hEA : E = A := by
    obtain ⟨-, -, -, -, -, hEA, -⟩ := hout4
    exact hEA
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨X, hX, htX⟩ := ht.2
  have hXI : X ≤ lieGenerated p E :=
    hN156 G p A c L E h15 hF (Or.inr (Or.inr (Or.inr (Or.inl hout4)))) X hX
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate X hX
  have hEB : E = B := (Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hB.2.2.1, hE3])).symm
  have hp34 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hnot5' : ¬ Outcome152Five p E B (lieGenerated p E) := by
    rintro ⟨-, -, -, -, -, hE4, -, -⟩
    rw [hE3] at hE4
    omega
  have hF13' : Sec13Facts G p B c' X E := hS13 G p B c' X E h' hnot5'
  obtain ⟨b, hbE, hb1, hXb⟩ := S15K.exists_mem_thetaComponentsAt_of_mem_thetaCompZeroE hX.1
  have hBM := K159.kf158BlocksFourModel_of_sec13 hS13 G p A c L E h15 hF hout4 b hbE hb1 X hX.1
    hXb hXI
  rcases hBM with ⟨F, _, _, _, -, ⟨e⟩⟩ | ⟨K, _, _, _, hpK, ⟨e⟩⟩
  · exfalso
    rcases hF'.two with hgen | hsu5
    · have h1 := hgen.localRank_eq
      have h2 := localRank_le_one_of_equiv_sl2 hp hp2 e
      omega
    · have h1 := hsu5.center_card
      have h2 := card_center_eq_one_of_equiv (K1214.center_SL2_eq_bot (K := F)) e
      omega
  · have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [← Nat.card_eq_fintype_card] at hn; exact hn
    have hpq : p ∣ 2 ^ (n : ℕ) + 1 := by rw [hK] at hpK; exact hpK
    have hn1 : 1 ≤ (n : ℕ) := n.pos
    have hn2 : 2 ≤ (n : ℕ) := by
      by_contra hlt
      have hn1' : (n : ℕ) = 1 := by omega
      rw [hn1'] at hpq
      have := Nat.le_of_dvd (by norm_num) hpq
      omega
    have hmod : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 4 2 n :=
      S15K.statedClassicalModel_psl_of_sl hK hn2 (by norm_num) e
    obtain ⟨-, hAt, -⟩ := K1320.row8Frame_of hGA h' hF' hF13' hEB hn1 hpq hmod
    rcases hAt t ht htX with hk | hk
    · exact ⟨n, hk⟩
    · exact ⟨2 * n, hk⟩

end CFSG.RankThree.PartOne.KFR4
