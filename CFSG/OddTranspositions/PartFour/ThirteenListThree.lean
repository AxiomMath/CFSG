module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListCorrected
import CFSG.OddTranspositions.PartFour.ThirteenList
import CFSG.OddTranspositions.PartFour.ThirteenThreeSimple
import CFSG.OddTranspositions.PartFour.ThirteenThreeTwo
import CFSG.Fischer.Classification.Orthogonal3.MinusFive.Cases

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Timmesfeld.Bridge.Asc72 Matrix

variable {X : Type} [Group X] [Finite X] {s : X}

theorem hyp_quotient_center (hodd : IsOddTransp {x : X | IsConj s x})
    (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤) (hO2 : CFSG.pCore 2 X = ⊥)
    (hOZ : fusionOddCore X ≤ Subgroup.center X)
    (hder : derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2)
    (h3 : ∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
      ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    Pair (X ⧸ Subgroup.center X) {x | IsConj (QuotientGroup.mk s) x} ∧
      Subgroup.center (X ⧸ Subgroup.center X) = ⊥ ∧
      IsSimpleGroup (commutator (X ⧸ Subgroup.center X)) := by
  have hS := setup_quotient_center hodd hncl hO2
  have hsolv := eq_bot_of_normal_isSolvable_quotient_center hO2 hOZ
  have hP : Pair (X ⧸ Subgroup.center X) {x | IsConj (QuotientGroup.mk s) x} :=
    ⟨inferInstance, hS.isClass, hS.oddT.1, h3, hS.gen⟩
  exact ⟨hP, hsolv _ inferInstance inferInstance,
    isSimpleGroup_commutator_of_derivedSeries hP hsolv hder⟩

omit [Finite X] in
theorem fusionOddCore_eq_center [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    (hOZ : fusionOddCore X ≤ Subgroup.center X) : fusionOddCore X = Subgroup.center X := by
  refine le_antisymm hOZ (le_sSup ⟨inferInstance, ?_⟩)
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 2
    (even_iff_two_dvd.mp hev)
  have hz2 : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hn : (Subgroup.zpowers (z : X)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2)
  have hp : IsPGroup 2 (Subgroup.zpowers (z : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hle : Subgroup.zpowers (z : X) ≤ CFSG.pCore 2 X := le_sSup ⟨hn, hp⟩
  rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hz2
  exact absurd hz2 (by decide)

theorem oddTranspListAlt_of_perm (hO2 : CFSG.pCore 2 X = ⊥)
    (hOZ : fusionOddCore X ≤ Subgroup.center X) {m : ℕ}
    (φ : X ⧸ Subgroup.center X ≃* Equiv.Perm (Fin m))
    (hφ : ∀ g, g ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x} ↔ (φ g).IsSwap) :
    OddTranspListAlt X s := by
  refine Or.inr (Or.inl ⟨m, (QuotientGroup.quotientMulEquivOfEq
    (fusionOddCore_eq_center hO2 hOZ)).trans φ, ?_⟩)
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  exact (hφ _).mp (IsConj.refl _)

omit [Finite X] in
theorem oddTranspListAlt_of_fischerSp {m : ℕ}
    (b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)) (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : fischerLinearModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
      (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
        ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    OddTranspListAlt X s := by
  obtain ⟨φ, hφ⟩ := hM
  obtain ⟨e, he⟩ := exists_fischerSp_equiv_statedSp b halt hnd
  obtain ⟨v, hv, hgv⟩ := (hφ (QuotientGroup.mk s)).mp (IsConj.refl _)
  have hx₀ : ∃ x, b.flip v x ≠ 0 := by
    by_contra h
    push Not at h
    refine hv (hnd v fun x => ?_)
    have h2 : b x v = 0 := by simpa using h x
    rw [← (show b.IsAlt from halt).neg_eq x v, h2, neg_zero]
  obtain ⟨x₀, hx₀⟩ := hx₀
  have hrank := rank_sub_one_eq_one_of_transvection (b.flip v) hgv hv hx₀
  have hcard : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  refine Or.inl ⟨2 * m, 1, Or.inl ⟨⟨m, rfl, ZMod 2, inferInstance, inferInstance, hcard,
    ⟨φ.trans e⟩⟩, ⟨m, rfl, ZMod 2, inferInstance, inferInstance, hcard, φ.trans e, ?_⟩⟩⟩
  show Matrix.rank _ = 1
  rw [MulEquiv.trans_apply, he, hrank]

omit [Finite X] in
theorem oddTranspListAlt_of_fischerOrth {m : ℕ} (hm : 2 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hex : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hM : fischerLinearModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
      (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
        ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    OddTranspListAlt X s := by
  obtain ⟨φ, hφ⟩ := hM
  obtain ⟨v, hv, hgv⟩ := (hφ (QuotientGroup.mk s)).mp (IsConj.refl _)
  have hv0 : v ≠ 0 := fun h => by
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hx₀ : ∃ x, (QuadraticMap.polarBilin Q).flip v x ≠ 0 := by
    by_contra h
    push Not at h
    refine hv0 (hnd v fun y => ?_)
    rw [QuadraticMap.polar_comm]
    simpa using h y
  obtain ⟨x₀, hx₀⟩ := hx₀
  have hrank := rank_sub_one_eq_one_of_transvection ((QuadraticMap.polarBilin Q).flip v) hgv hv0
    hx₀
  have hcard : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  rcases exists_fischerOrth_equiv hm Q hnd hex with ⟨h3, e, he⟩ | ⟨e, he⟩
  · refine Or.inl ⟨2 * m, 1, Or.inr (Or.inr (Or.inl (Or.inl ⟨m, by omega, rfl, ZMod 2,
      inferInstance, inferInstance, hcard, φ.trans e, ?_⟩)))⟩
    show Matrix.rank _ = 1
    rw [MulEquiv.trans_apply, he, hrank]
  · refine Or.inl ⟨2 * m, 1, Or.inr (Or.inr (Or.inl (Or.inr ⟨m - 1, by omega, by omega, ZMod 2,
      inferInstance, inferInstance, hcard, 1, 1, by decide, φ.trans e, ?_⟩)))⟩
    show Matrix.rank _ = 1
    rw [MulEquiv.trans_apply, he, hrank]

private noncomputable def hermLeft (m : ℕ) (v : Fin m → GaloisField 2 2) :
    (Fin m → GaloisField 2 2) →ₗ[GaloisField 2 2] GaloisField 2 2 where
  toFun x := fischerHermitianF4 m x v
  map_add' x y := by
    simp only [fischerHermitianF4, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [fischerHermitianF4, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      mul_assoc]

omit [Finite X] in
theorem oddTranspListAlt_of_fischerSU {m : ℕ} (hm : 4 ≤ m)
    (hM : fischerCentralQuotientModel
      {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
      (fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
        A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    OddTranspListAlt X s := by
  obtain ⟨φ, hφ⟩ := hM
  obtain ⟨h, ⟨v, ⟨hv0, -⟩, hgv⟩, hφh⟩ := (hφ (QuotientGroup.mk s)).mp (IsConj.refl _)
  have hSU : (fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
      A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y) =
      StatedSU m (2 ^ 1) (GaloisField 2 2) :=
    (CFSG.Fischer.Classification.Unitary.SUm_eq m).trans
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU CFSG.Fischer.Classification.Unitary.card_K m)
  have hnq : (m, 2 ^ 1) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  obtain ⟨-, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    CFSG.Fischer.Classification.Unitary.card_K (by omega) hnq
  let ψ : ↥(fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
        A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y) ⧸
      Subgroup.center ↥(fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
        A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y) ≃*
      StatedProj (StatedSU m (2 ^ 1) (GaloisField 2 2)) :=
    QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hSU) (by
      rw [← hZ]
      exact Subgroup.map_center_eq (MulEquiv.subgroupCongr hSU))
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hv0 (funext hne)
  have hx₀ : hermLeft m v (Pi.single i 1) ≠ 0 := by
    change fischerHermitianF4 m (Pi.single i 1) v ≠ 0
    rw [fischerHermitianF4, Finset.sum_eq_single i (fun j _ hj => by
      rw [Pi.single_eq_of_ne hj, zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
      Pi.single_eq_same, one_mul]
    exact pow_ne_zero 2 hi
  have hrank := rank_sub_one_eq_one_of_transvection (hermLeft m v) hgv hv0 hx₀
  have hM : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by omega, hnq⟩, GaloisField 2 2, inferInstance, inferInstance,
      CFSG.Fischer.Classification.Unitary.card_K, ⟨φ.trans ψ⟩⟩
  refine Or.inl ⟨m, 1, Or.inr (Or.inl ⟨Or.inl ⟨by decide, hM⟩, GaloisField 2 2, inferInstance,
    inferInstance, CFSG.Fischer.Classification.Unitary.card_K, φ.trans ψ,
    MulEquiv.subgroupCongr hSU h, ?_, hrank⟩)⟩
  rw [MulEquiv.trans_apply, hφh]
  rfl

omit [Finite X] in
theorem oddTranspListAlt_of_f3Five {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hM : fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    OddTranspListAlt X s := by
  rcases CFSG.Fischer.Classification.orth_or_unitary_of_reflection_five hsymm hnd hM with
    ⟨Q, hQ, hMQ⟩ | hMU
  · exact oddTranspListAlt_of_fischerOrth (m := 3) (by norm_num) Q hQ (by omega) hMQ
  · exact oddTranspListAlt_of_fischerSU (m := 4) le_rfl hMU

end CFSG.OddTranspositions.PartFour
