module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Cent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Pure
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.D4ThreeBCentralizer


open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LieType.AlgebraicGroups
open scoped MatrixGroups

section Basics

variable {L : Type} [Field L]

private theorem neg_one_eq_one_of_charP_two [CharP L 2] : (-1 : SL2 L) = 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h2' : (1 : L) + 1 = 0 := by
    rw [show (1 : L) + 1 = (2 : L) by ring]
    exact h2
  have hneg : (-1 : L) = 1 := neg_eq_of_add_eq_zero_left h2'
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hneg]

variable [IsAlgClosed L]

private theorem exists_unit_sq_eq (x : Lˣ) : ∃ a : Lˣ, a ^ 2 = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) (n := 2) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    have hx0 : (x : L) = 0 := by simpa using hz.symm
    exact x.ne_zero hx0
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

end Basics

section Map

variable {L : Type} [Field L]


private theorem outerTriple_injective [CharP L 2] : Function.Injective (outerTriple L) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B, C⟩ h
  obtain ⟨hA, hB, hC, -⟩ := outerTriple_ker h
  have hA1 : A = 1 := by
    rcases hA with h' | h'
    · exact h'
    · rw [h', neg_one_eq_one_of_charP_two]
  have hB1 : B = 1 := by
    rcases hB with h' | h'
    · exact h'
    · rw [h', neg_one_eq_one_of_charP_two]
  have hC1 : C = 1 := by
    rcases hC with h' | h'
    · exact h'
    · rw [h', neg_one_eq_one_of_charP_two]
  exact Prod.ext hA1 (Prod.ext hB1 hC1)

private noncomputable def outerThetaHom :
    (SL2 L × SL2 L × SL2 L) × SL2 L →* ModGL TwistTag.D4.tag L :=
  (outerTriple L).noncommCoprod (thetaHom L) fun A B =>
    (commute_iff_eq (outerTriple L A) (thetaHom L B)).2 (commute_outerTriple_thetaHom A B)

private theorem outerThetaHom_apply (A : SL2 L × SL2 L × SL2 L) (B : SL2 L) :
    outerThetaHom (A, B) = outerTriple L A * thetaHom L B := by
  rw [outerThetaHom, MonoidHom.noncommCoprod_apply]

private theorem outerThetaHom_injective [CharP L 2] :
    Function.Injective (outerThetaHom (L := L)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨X, B⟩ h
  rw [outerThetaHom_apply] at h
  have hΨ : outerTriple L X = (thetaHom L B)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hcomm : ∀ Y : SL2 L × SL2 L × SL2 L, X * Y = Y * X := by
    intro Y
    apply outerTriple_injective
    rw [map_mul, map_mul, hΨ]
    have hBY : Commute (thetaHom L B) (outerTriple L Y) :=
      (commute_outerTriple_thetaHom Y B).symm
    exact hBY.inv_left.eq
  have central_eq_one : ∀ A : SL2 L, (∀ D : SL2 L, A * D = D * A) → A = 1 := by
    intro A hA
    rcases eq_one_or_neg_one_of_commute n0 (fun D => by
      simpa only [map_mul] using congrArg (rankOneHom TwistTag.D4 L n0) (hA D)) with hA1 | hAm
    · exact hA1
    · rw [hAm, neg_one_eq_one_of_charP_two]
  have hX : X = 1 := Prod.ext
    (central_eq_one X.1 (fun D => congrArg Prod.fst (hcomm (D, 1, 1))))
    (Prod.ext
      (central_eq_one X.2.1 (fun D => congrArg (fun Y => Y.2.1) (hcomm (1, D, 1))))
      (central_eq_one X.2.2 (fun D => congrArg (fun Y => Y.2.2) (hcomm (1, 1, D)))))
  have hθ : thetaHom L B = 1 := by simpa [hX] using h
  have hB : B = 1 := thetaHom_injective (hθ.trans (map_one (thetaHom L)).symm)
  exact Prod.ext hX hB

private theorem outerTriple_range_le_outerThetaHom_range : (outerTriple L).range ≤ (outerThetaHom (L := L)).range := by
  rintro y ⟨X, rfl⟩
  exact ⟨(X, 1), by rw [outerThetaHom_apply, map_one, mul_one]⟩

end Map

section Torus

variable {L : Type} [Field L] [IsAlgClosed L]


private theorem torusGroup_le_range_outerThetaHom :
    torusGroup TwistTag.D4.tag L ≤ (outerThetaHom (L := L)).range := by
  intro t ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨a0, ha0⟩ := exists_unit_sq_eq (b n0)
  obtain ⟨a1, ha1⟩ := exists_unit_sq_eq (b n1)
  obtain ⟨a3, ha3⟩ := exists_unit_sq_eq (b n3)
  refine ⟨((HSL a0, HSL a1, HSL a3), HSL (b n2 * a0 * a1 * a3)), ?_⟩
  rw [outerThetaHom_apply, outerTriple_HSL_units, thetaHom_HSL, ← rootDiagUnit_mul]
  congr 1
  funext j
  rw [Pi.mul_apply]
  fin_cases j
  · rw [show TwistTag.D4.tag.cartan n0 ⟨0, by decide⟩ = 2 by decide,
        show TwistTag.D4.tag.cartan n1 ⟨0, by decide⟩ = 0 by decide,
        show TwistTag.D4.tag.cartan n3 ⟨0, by decide⟩ = 0 by decide,
        Pi.mulSingle_apply, if_neg (by decide)]
    simp [zpow_ofNat, ha0]
  · rw [show TwistTag.D4.tag.cartan n0 ⟨1, by decide⟩ = 0 by decide,
        show TwistTag.D4.tag.cartan n1 ⟨1, by decide⟩ = 2 by decide,
        show TwistTag.D4.tag.cartan n3 ⟨1, by decide⟩ = 0 by decide,
        Pi.mulSingle_apply, if_neg (by decide)]
    simp [zpow_ofNat, ha1]
  · rw [show TwistTag.D4.tag.cartan n0 ⟨2, by decide⟩ = -1 by decide,
        show TwistTag.D4.tag.cartan n1 ⟨2, by decide⟩ = -1 by decide,
        show TwistTag.D4.tag.cartan n3 ⟨2, by decide⟩ = -1 by decide,
        Pi.mulSingle_apply, if_pos rfl]
    have hmiddle : a0⁻¹ * a1⁻¹ * a3⁻¹ * (b n2 * a0 * a1 * a3) = b n2 := by
      have h1 : a0⁻¹ * a1⁻¹ * a3⁻¹ = (a0 * a1 * a3)⁻¹ := by
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
        ac_rfl
      have h2 : b n2 * a0 * a1 * a3 = (a0 * a1 * a3) * b n2 := by ac_rfl
      rw [h1, h2, inv_mul_cancel_left]
    rw [_root_.zpow_neg_one, _root_.zpow_neg_one, _root_.zpow_neg_one]
    exact hmiddle
  · rw [show TwistTag.D4.tag.cartan n0 ⟨3, by decide⟩ = 0 by decide,
        show TwistTag.D4.tag.cartan n1 ⟨3, by decide⟩ = 0 by decide,
        show TwistTag.D4.tag.cartan n3 ⟨3, by decide⟩ = 2 by decide,
        Pi.mulSingle_apply, if_neg (by decide)]
    simp [zpow_ofNat, ha3]

end Torus

section Centralizer

variable {L : Type} [Field L] [IsAlgClosed L]


private theorem graphCentralizer_gB_le_range_outerThetaHom {ω : Lˣ} (hω : orderOf ω = 3) :
    graphCentralizer TwistTag.D4.tag L (rootDiagUnit TwistTag.D4.tag (tup ω gB)) ≤
      (outerThetaHom (L := L)).range := by
  rw [graphCentralizer_gB hω]
  exact sup_le torusGroup_le_range_outerThetaHom
    (rootSpan_sigmaB_le.trans outerTriple_range_le_outerThetaHom_range)

end Centralizer


open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar

private theorem factorization_three_sl2_cube_mul_sl2_lt_triality {q : ℕ}
    (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) :
    ((q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1))).factorization 3 <
      (ordTrialityD4 q).factorization 3 := by
  have hq0 : q ≠ 0 := by omega
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hq3 : 0 < q ^ 3 := pow_pos (by omega) _
  have hq6 : 1 < (q ^ 3) ^ 2 := by
    have hq3' : 2 ≤ q ^ 3 := (Nat.le_self_pow (by norm_num) q).trans' hq
    nlinarith
  have hS : q ^ 3 * ((q ^ 3) ^ 2 - 1) ≠ 0 :=
    mul_ne_zero hq3.ne' (by omega)
  have hC : q * (q ^ 2 - 1) ≠ 0 := mul_ne_zero hq0 (by omega)
  rw [Nat.factorization_mul hS hC, Finsupp.add_apply,
    factorization_card_SL2_cube hq h3, Nat.factorization_mul hq0 (by omega),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h3,
    factorization_ordTrialityD4 hq h3]
  omega

private theorem card_sup_dvd_card_mul {G : Type} [Group G] [Finite G]
    (A B : Subgroup G) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card A * Nat.card B := by
  exact ⟨Nat.card ↥(A ⊓ B),
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcomm).1.symm⟩

private theorem not_le_sup_of_isSylowOf_three_of_triality_order
    {G : Type} [Group G] [Finite G] {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q)
    (hG : Nat.card G = ordTrialityD4 q) {P S C : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hS : Nat.card S = q ^ 3 * ((q ^ 3) ^ 2 - 1))
    (hC : Nat.card C = q * (q ^ 2 - 1))
    (hcomm : ∀ s ∈ S, ∀ c ∈ C, s * c = c * s) : ¬ P ≤ S ⊔ C := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hle
  have hdiv : Nat.card P ∣ (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) := by
    simpa [hS, hC] using
      (Subgroup.card_dvd_of_le hle).trans (card_sup_dvd_card_mul S C hcomm)
  have hcard : Nat.card P = 3 ^ (ordTrialityD4 q).factorization 3 := by
    simpa [Subgroup.card_top, hG] using hP.card_eq
  rw [hcard] at hdiv
  have hq0 : q ≠ 0 := by omega
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hq3 : 2 ≤ q ^ 3 := (Nat.le_self_pow (by norm_num) q).trans' hq
  have hq6 : 1 < (q ^ 3) ^ 2 := by nlinarith
  have hN : (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ hq0) (by omega)
    · exact mul_ne_zero hq0 (by omega)
  have hle3 := (Nat.prime_three.pow_dvd_iff_le_factorization hN).mp hdiv
  exact (not_le_of_gt (factorization_three_sl2_cube_mul_sl2_lt_triality hq h3)) hle3


open Matrix Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.RankThree.PartTwo.Sec11
  CFSG.LieType.AlgebraicGroups
open scoped MatrixGroups


section Descent


variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L]
  [IsAlgClosed L]
  [CharP L 2] {n : ℕ} {σ : K ≃+* K} {Fr : L →+* L}

omit [IsAlgClosed L] in
private theorem fixed_factors {X : SL2 L × SL2 L × SL2 L} {B : SL2 L}
    (hθ : twistHom TwistTag.D4 L Fr (thetaConj L) = thetaConj L)
    (hfix : twistHom TwistTag.D4 L Fr (outerTriple L X * thetaHom L B) =
      outerTriple L X * thetaHom L B) :
    twistHom TwistTag.D4 L Fr (outerTriple L X) = outerTriple L X ∧
      twistHom TwistTag.D4 L Fr (thetaHom L B) = thetaHom L B := by
  have h : outerThetaHom
      ((Matrix.SpecialLinearGroup.map Fr X.2.2, Matrix.SpecialLinearGroup.map Fr X.1,
        Matrix.SpecialLinearGroup.map Fr X.2.1), Matrix.SpecialLinearGroup.map Fr B) =
      outerThetaHom (X, B) := by
    rw [outerThetaHom_apply,
      outerThetaHom_apply]
    rw [map_mul, twistHom_outerTriple, twistHom_thetaHom Fr hθ] at hfix
    exact hfix
  have heq := outerThetaHom_injective h
  constructor
  · rw [twistHom_outerTriple]
    exact congrArg (outerTriple L) (congrArg Prod.fst heq)
  · rw [twistHom_thetaHom Fr hθ]
    exact congrArg (thetaHom L) (congrArg Prod.snd heq)

omit [IsAlgClosed L] in
private theorem mem_sup_of_triEmb_eq_mul (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    {X : SL2 L × SL2 L × SL2 L} {B : SL2 L}
    (hx : triEmb K σ L x = outerTriple L X * thetaHom L B) :
    x ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ⊔
      centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) := by
    ext c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hFr,
      map_pow]
  have hθ := twistHom_thetaConj σ Fr hcomm
  have hfix := triEmb_fixed Fr hcomm x
  rw [hx] at hfix
  obtain ⟨hXfix, hBfix⟩ := fixed_factors hθ hfix
  have hXr : outerTriple L X ∈ (triEmb K σ L).range := by
    rw [triEmb_range Nat.prime_two hn hK hσ Fr hFr]
    exact ⟨outerTriple_mem_adjointGroup X, hXfix⟩
  have hBr : thetaHom L B ∈ (triEmb K σ L).range := by
    rw [triEmb_range Nat.prime_two hn hK hσ Fr hFr]
    exact ⟨thetaHom_mem_adjointGroup B, hBfix⟩
  obtain ⟨s, hs⟩ := hXr
  obtain ⟨c, hc⟩ := hBr
  have hsS : s ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
    mem_short_of_triEmb_eq_outerTriple hK hσ hFr hs
  have hcC : c ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mem_centralizer_of_triEmb_mem (L := L) (hc ▸ thetaHom_mem_thetaPair B)
  have hsc : s * c = x := by
    apply triEmb_injective (L := L)
    rw [map_mul, hs, hc, hx]
  exact hsc ▸ Subgroup.mul_mem_sup hsS hcC

theorem centralizer_le_short_sup_centralizer (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
      KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ⊔
        centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have hd : 2 ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).mp h
    norm_num at hd
  obtain ⟨μ, hμ⟩ := exists_units_orderOf_nine L h3L
  have hζ : orderOf (μ ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hμ]; norm_num), hμ]
  obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hn (by norm_num) hK hσ L hFr hzS
  have hZ3 : Z ^ 3 = 1 := thetaHom_injective (by
    rw [map_pow, hZ, ← map_pow, hz3, map_one, map_one])
  have hZ1 : Z ≠ 1 := fun h => hz1 (triEmb_injective (L := L)
    (by rw [← hZ, h, map_one, map_one]))
  obtain ⟨P, m, hm, hPZ⟩ := exists_conj_HSL_of_pow_three hζ hZ3 hZ1
  have hω : orderOf ((μ ^ 3) ^ m) = 3 := by
    rcases hm with rfl | rfl
    · rw [pow_one, hζ]
    · rw [Nat.Coprime.orderOf_pow (by rw [hζ]; norm_num), hζ]
  let k := thetaHom L P
  let d := rootDiagUnit TwistTag.D4.tag (tup ((μ ^ 3) ^ m) gB)
  have hιz : triEmb K σ L z = k * d * k⁻¹ := by
    dsimp only [k, d]
    rw [← hZ, hPZ, map_mul, map_mul, map_inv, thetaHom_HSL,
      tup_gB_eq_mulSingle]
  intro x hx
  have hcent : k⁻¹ * triEmb K σ L x * k ∈
      graphCentralizer TwistTag.D4.tag L d := by
    change k⁻¹ * triEmb K σ L x * k ∈ adjointGroup TwistTag.D4.tag L ⊓
      Subgroup.centralizer ({d} : Set (ModGL TwistTag.D4.tag L))
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (thetaHom_mem_adjointGroup P))
      (triEmb_mem_adjointGroup x)) (thetaHom_mem_adjointGroup P), ?_⟩
    change k⁻¹ * triEmb K σ L x * k ∈
      Subgroup.centralizer ({d} : Set (ModGL TwistTag.D4.tag L))
    rw [mem_centralizer_singleton_iff]
    have hd : d = k⁻¹ * triEmb K σ L z * k := by rw [hιz]; group
    rw [hd]
    have hxz := mem_centralizer_singleton_iff.mp hx
    calc
      k⁻¹ * triEmb K σ L x * k * (k⁻¹ * triEmb K σ L z * k) =
          k⁻¹ * triEmb K σ L (x * z) * k := by rw [map_mul]; group
      _ = k⁻¹ * triEmb K σ L (z * x) * k := by rw [hxz]
      _ = k⁻¹ * triEmb K σ L z * k * (k⁻¹ * triEmb K σ L x * k) := by
          rw [map_mul]; group
  obtain ⟨⟨X, B⟩, hXB⟩ := graphCentralizer_gB_le_range_outerThetaHom hω
    hcent
  rw [outerThetaHom_apply] at hXB
  have hdec : triEmb K σ L x = outerTriple L X * thetaHom L (P * B * P⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    change triEmb K σ L x = outerTriple L X * (k * thetaHom L B * k⁻¹)
    have hXP := commute_outerTriple_thetaHom X P
    calc
      triEmb K σ L x = k * (k⁻¹ * triEmb K σ L x * k) * k⁻¹ := by group
      _ = k * (outerTriple L X * thetaHom L B) * k⁻¹ := by rw [hXB]
      _ = outerTriple L X * (k * thetaHom L B * k⁻¹) := by
          change thetaHom L P * (outerTriple L X * thetaHom L B) *
              (thetaHom L P)⁻¹ =
            outerTriple L X * (thetaHom L P * thetaHom L B * (thetaHom L P)⁻¹)
          rw [← mul_assoc (thetaHom L P), ← hXP]
          group
  exact mem_sup_of_triEmb_eq_mul hn hK hσ hFr hdec


end Descent

section Exclusion


theorem not_le_centralizer_of_threeB_triality_two
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ¬ P ≤ centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := n * 3)
    (by omega) (by rw [hK, pow_mul])
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  have hcent := centralizer_le_short_sup_centralizer
    (L := L) hn hK hσ hFr hzS hz3 hz1
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    simpa [pow_succ] using ringEquiv_cube_apply_eq hK hσ c
  have hS : Nat.card (KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 3) ^ 2 - 1) := by
    rw [KS11Lie4Proof.card_d4ShortSL2 hσ3, hK]
  obtain ⟨F, hFfield, hFfin, _, hFcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.nonempty_mulEquiv_centralizer_d4ShortSL2
      (ℓ := 2) (f := n) hn (by norm_num) hK hσ
  have hC : Nat.card (centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFcard]
  have hq : 2 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hn
  have h3 : ¬ 3 ∣ 2 ^ n := by
    intro h
    have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hG := CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hn hK
    σ.toRingHom hσ
  have hnot := not_le_sup_of_isSylowOf_three_of_triality_order hq h3 hG hP hS hC
    (fun s hs c hc => Subgroup.mem_centralizer_iff.mp hc s hs)
  exact fun hle => hnot (hle.trans hcent)

theorem exists_conj_mem_short_of_central_sylow_three_triality_two
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzc : ∀ p ∈ P, p * z = z * p) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      g * z * g⁻¹ ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ 2 ^ n := by
    intro h
    have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  obtain ⟨g, hgS | hgC⟩ := KS11Lie6Proof.d4ThreeConj_holds
    (K := K) (q := 2 ^ n) (σ := σ) hK hσ h3 z hz3 hz1
  · exact ⟨g, hgS⟩
  · let P' := P.map (MulAut.conj g).toMonoidHom
    have hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' ⊤ := by
      apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
      rw [show Nat.card P' = Nat.card P from
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective]
      exact hP.card_eq
    have hle : P' ≤ centralizer ({g * z * g⁻¹} :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (g * p * g⁻¹) * (g * z * g⁻¹) = (g * z * g⁻¹) * (g * p * g⁻¹)
      have h := congrArg (MulAut.conj g) (hzc p hp)
      simpa only [map_mul, MulAut.conj_apply] using h
    have hw3 : (g * z * g⁻¹) ^ 3 = 1 := by
      simpa only [map_pow, MulAut.conj_apply, map_one] using congrArg (MulAut.conj g) hz3
    have hw1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      apply (MulAut.conj g).injective
      change g * z * g⁻¹ = (MulAut.conj g) 1
      rw [map_one]
      exact h
    exact (not_le_centralizer_of_threeB_triality_two hn hK σ hσ hP' hgC hw3 hw1 hle).elim

end Exclusion


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.D4ThreeBCentralizer
