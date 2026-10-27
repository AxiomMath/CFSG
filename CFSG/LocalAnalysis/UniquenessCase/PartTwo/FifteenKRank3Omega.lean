module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK
public import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.Open.StatedZModTwo
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartOne.KF.SymTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open Matrix

theorem s15k_om6_model {X : Type} [Group X] (h : IsOmegaMinus X 6 1) :
    ∃ (F : Type) (_ : Field F), UnitaryFieldData 2 1 F ∧ Nonempty (X ≃* unitarySU 2 1 F 4) := by
  obtain ⟨-, K, _, _, b, c, hK, hirr, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK2])
  obtain ⟨F, _, _, hF, ⟨e'⟩⟩ :=
    CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_three_mulEquiv
      (K := K) (b := b) (c := c) (f := 1) hK hirr
  have hbot : (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 3 K b c)) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK2, Subgroup.bot_subgroupOf]
  let e0 : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 K b c)) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨F, inferInstance, ⟨Nat.prime_two, le_rfl, by simpa using hF⟩,
    ⟨(e.trans e0).trans e'⟩⟩

theorem s15k_om6_conj_inner {F : Type} [Field F] (hU : UnitaryFieldData 2 1 F)
    (P : primeFormUnitary hU (idGram F 4)) :
    ∃ s : unitarySU 2 1 F 4, ∀ g : unitarySU 2 1 F 4,
      ((s * g * s⁻¹ : unitarySU 2 1 F 4) : GL (Fin 4) F) =
        (P : GL (Fin 4) F) * (g : GL (Fin 4) F) * (P : GL (Fin 4) F)⁻¹ := by
  classical
  have hP : (((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map hU.bar)ᵀ *
      ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have := mem_primeFormUnitary.mp P.2
    simpa [idGram] using this
  set d : F := ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det with hd
  have hbar : ∀ c : F, hU.bar c = c ^ 2 := fun c => by rw [hU.bar_apply]; simp
  have hdet : (((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map hU.bar).det = hU.bar d := by
    rw [hd, RingHom.map_det, RingHom.mapMatrix_apply]
  have hd3 : d ^ 3 = 1 := by
    have h1 := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_transpose, hdet, Matrix.det_one, hbar] at h1
    calc d ^ 3 = d ^ 2 * d := by ring
      _ = 1 := h1
  have hd0 : d ≠ 0 := fun h0 => by rw [h0] at hd3; simp at hd3
  have hi3 : d⁻¹ ^ 3 = 1 := by rw [inv_pow, hd3, inv_one]
  let c : Fˣ := (Units.mk0 d hd0)⁻¹
  have hcc : (c : F) = d⁻¹ := rfl
  have hz : (GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) ∈
      primeFormUnitary hU (idGram F 4) := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    simp only [idGram, Units.val_one]
    rw [Matrix.diagonal_map (map_zero hU.bar), Matrix.diagonal_transpose,
      Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    have : hU.bar (c : F) * (c : F) = 1 := by
      rw [hbar, hcc]
      calc d⁻¹ ^ 2 * d⁻¹ = d⁻¹ ^ 3 := by ring
        _ = 1 := hi3
    simp [this]
  have hs : (GeneralLinearGroup.scalar (Fin 4) c * (P : GL (Fin 4) F) : GL (Fin 4) F) ∈
      unitarySU 2 1 F 4 := by
    rw [unitarySU_eq_gramSU hU, mem_gramSU_iff_unitary]
    refine ⟨mul_mem hz P.2, ?_⟩
    rw [Units.val_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcc]
    show d⁻¹ ^ 4 * d = 1
    calc d⁻¹ ^ 4 * d = d⁻¹ ^ 3 * (d⁻¹ * d) := by ring
      _ = 1 := by rw [hi3, inv_mul_cancel₀ hd0, one_mul]
  let s : unitarySU 2 1 F 4 := ⟨GeneralLinearGroup.scalar (Fin 4) c * (P : GL (Fin 4) F), hs⟩
  refine ⟨s, fun g => ?_⟩
  have hsv : (s : GL (Fin 4) F) = GeneralLinearGroup.scalar (Fin 4) c * (P : GL (Fin 4) F) := rfl
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hsv]
  set Q : GL (Fin 4) F := (P : GL (Fin 4) F) * (g : GL (Fin 4) F) * (P : GL (Fin 4) F)⁻¹ with hQ
  have h1 : GeneralLinearGroup.scalar (Fin 4) c * (P : GL (Fin 4) F) * (g : GL (Fin 4) F) *
      (GeneralLinearGroup.scalar (Fin 4) c * (P : GL (Fin 4) F))⁻¹ =
      GeneralLinearGroup.scalar (Fin 4) c * Q * (GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by
    rw [hQ]; group
  rw [h1, ← (commute_scalar c Q).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem s15k_om6_conj_diag {F : Type} [Field F] (hU : UnitaryFieldData 2 1 F)
    (E : Subgroup (unitarySU 2 1 F 4)) (hE : IsElemAbelian 3 E) :
    ∃ P : primeFormUnitary hU (idGram F 4), ∀ g ∈ E,
      (P : GL (Fin 4) F)⁻¹ * (g : GL (Fin 4) F) * (P : GL (Fin 4) F) ∈ torusSU 3 4 F := by
  classical
  have hle := unitarySU_le_primeFormUnitary (n := 4) hU
  set G' : Subgroup (primeFormUnitary hU (idGram F 4)) := E.map (Subgroup.inclusion hle) with hG'
  have hG'mem : ∀ x ∈ G', ∃ x₀ ∈ E, Subgroup.inclusion hle x₀ = x := fun x hx => by
    obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.mp hx
    exact ⟨x₀, hx₀, hx⟩
  have hGcomm : ∀ x ∈ G', ∀ y ∈ G', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hG'mem y hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact hE.comm hx₀ hy₀
  have hGpow : ∀ x ∈ G', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    rw [← map_pow, hE.2 x₀ hx₀, map_one]
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag hU Nat.prime_three hpq G' hGcomm hGpow
  refine ⟨P, fun g hg => ?_⟩
  have hdiag := hP _ (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  have hco : (((P⁻¹ * Subgroup.inclusion hle g * P : primeFormUnitary hU (idGram F 4)) :
      GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (((P : GL (Fin 4) F)⁻¹ * (g : GL (Fin 4) F) * (P : GL (Fin 4) F) : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) := rfl
  rw [hco] at hdiag
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hdiag
  have hg3 : (g : GL (Fin 4) F) ^ 3 = 1 := by
    have h2 := congrArg (fun x : unitarySU 2 1 F 4 => (x : GL (Fin 4) F)) (hE.2 g hg)
    simpa using h2
  have hgp : ((P : GL (Fin 4) F)⁻¹ * (g : GL (Fin 4) F) * (P : GL (Fin 4) F)) ^ 3 = 1 := by
    have h := conj_pow (a := (P : GL (Fin 4) F)⁻¹) (b := (g : GL (Fin 4) F)) (i := 3)
    rw [inv_inv] at h
    rw [h, hg3]
    group
  refine mem_torusSU_iff.mpr ⟨d, fun i => ?_, ?_, hd⟩
  · have h1 : diagU (d ^ 3) = 1 := by rw [← diagU_pow, hd, hgp]
    have h2 : d ^ 3 = 1 := diagU_injective (h1.trans diagU_one.symm)
    exact congrFun h2 i
  · have hmem := conj_mem_unitarySU hU (inv_mem P.2) g.2
    have hdet := ((mem_unitarySU_iff hU).mp hmem).1
    rw [inv_inv, ← hd, det_diagU] at hdet
    exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)

theorem s15k_om6_torus {F : Type} [Field F] (hU : UnitaryFieldData 2 1 F) :
    IsElemAbelian 3 ((torusSU 3 4 F).subgroupOf (unitarySU 2 1 F 4)) ∧
      Nat.card ((torusSU 3 4 F).subgroupOf (unitarySU 2 1 F 4)) = 27 := by
  haveI := hU.finite
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hle : torusSU 3 4 F ≤ unitarySU 2 1 F 4 := torusSU_le_unitarySU hU h3
  have hζ : ∃ ζ : Fˣ, IsPrimitiveRoot ζ 3 := by
    obtain ⟨z, hz⟩ := exists_isPrimitiveRoot hU Nat.prime_three h3
    have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
    exact ⟨Units.mk0 z hz0, IsPrimitiveRoot.coe_units_iff.mp (by simpa using hz)⟩
  have hel : IsElemAbelian 3 (torusVec 3 4 F) :=
    ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun d hd => by
      funext i
      rw [Pi.pow_apply, hd.1 i, Pi.one_apply]⟩
  refine ⟨(hel.map diagUHom).subgroupOf _, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, torusSU,
    Subgroup.card_map_of_injective diagU_injective, card_torusVec_eq (by norm_num) hζ 3]
  norm_num

theorem s15k_om6_conj_torus {F : Type} [Field F] (hU : UnitaryFieldData 2 1 F)
    (E : Subgroup (unitarySU 2 1 F 4)) (hE : IsElemAbelian 3 E) :
    ∃ s : unitarySU 2 1 F 4, ∀ g ∈ E,
      ((s * g * s⁻¹ : unitarySU 2 1 F 4) : GL (Fin 4) F) ∈ torusSU 3 4 F := by
  obtain ⟨P, hP⟩ := s15k_om6_conj_diag hU E hE
  obtain ⟨s, hs⟩ := s15k_om6_conj_inner hU P⁻¹
  refine ⟨s, fun g hg => ?_⟩
  rw [hs g]
  simpa using hP g hg

theorem s15k_om6_card_le {X : Type} [Group X] (hX : IsOmegaMinus X 6 1) (E : Subgroup X)
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  obtain ⟨F, _, hU, ⟨e⟩⟩ := s15k_om6_model hX
  haveI := hU.finite
  obtain ⟨-, hT⟩ := s15k_om6_torus hU
  haveI : Finite ((torusSU 3 4 F).subgroupOf (unitarySU 2 1 F 4)) :=
    Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have hE' : IsElemAbelian 3 (E.map e.toMonoidHom) := hE.map _
  obtain ⟨s, hs⟩ := s15k_om6_conj_torus hU _ hE'
  have hle : (E.map e.toMonoidHom).map (MulAut.conj s).toMonoidHom ≤
      (torusSU 3 4 F).subgroupOf (unitarySU 2 1 F 4) := by
    rintro y ⟨z, hz, rfl⟩
    exact hs z hz
  calc Nat.card E = Nat.card (E.map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card ((E.map e.toMonoidHom).map (MulAut.conj s).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj s).injective).symm
    _ ≤ Nat.card ((torusSU 3 4 F).subgroupOf (unitarySU 2 1 F 4)) := Subgroup.card_le_of_le hle
    _ = 27 := hT

theorem s15k_om6_exists_e27 {X : Type} [Group X] (hX : IsOmegaMinus X 6 1) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨F, _, hU, ⟨e⟩⟩ := s15k_om6_model hX
  obtain ⟨hel, hcard⟩ := s15k_om6_torus hU
  refine ⟨((torusSU 3 4 F).subgroupOf (unitarySU 2 1 F 4)).map e.symm.toMonoidHom, hel.map _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem s15k_om6_conj_into {X : Type} [Group X] (hX : IsOmegaMinus X 6 1) (A B : Subgroup X)
    (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 27) (hB : IsElemAbelian 3 B) :
    ∃ x : X, B.map (MulAut.conj x).toMonoidHom ≤ A := by
  obtain ⟨F, _, hU, ⟨e⟩⟩ := s15k_om6_model hX
  haveI := hU.finite
  obtain ⟨-, hT⟩ := s15k_om6_torus hU
  set T := (torusSU 3 4 F).subgroupOf (unitarySU 2 1 F 4) with hTdef
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  obtain ⟨sA, hsA⟩ := s15k_om6_conj_torus hU (A.map e.toMonoidHom) (hA.map _)
  obtain ⟨sB, hsB⟩ := s15k_om6_conj_torus hU (B.map e.toMonoidHom) (hB.map _)
  have hAT : (A.map e.toMonoidHom).map (MulAut.conj sA).toMonoidHom = T := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      exact hsA z hz
    · rw [Subgroup.card_map_of_injective (MulAut.conj sA).injective,
        Subgroup.card_map_of_injective e.injective, hAc, hT]
  refine ⟨e.symm (sA⁻¹ * sB), ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hmem : sB * e b * sB⁻¹ ∈ T := hsB (e b) ⟨b, hb, rfl⟩
  rw [← hAT] at hmem
  obtain ⟨a', ⟨a, ha, rfl⟩, hy⟩ := hmem
  have hy' : sA * e a * sA⁻¹ = sB * e b * sB⁻¹ := hy
  have key : (MulAut.conj (e.symm (sA⁻¹ * sB))) b = a := by
    apply e.injective
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    calc (sA⁻¹ * sB) * e b * (sA⁻¹ * sB)⁻¹ = sA⁻¹ * (sB * e b * sB⁻¹) * sA := by group
      _ = sA⁻¹ * (sA * e a * sA⁻¹) * sA := by rw [hy']
      _ = e a := by group
  change (MulAut.conj (e.symm (sA⁻¹ * sB))) b ∈ A
  rw [key]
  exact ha

theorem rRank3Omega153_holds : RRank3Omega153 := by
  intro X _ _ hX
  obtain ⟨E₀, hE₀, hc₀⟩ := s15k_om6_exists_e27 hX
  have hmem : 3 ∈ {k | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} :=
    ⟨E₀, le_top, hE₀, by rw [hc₀]; norm_num⟩
  have hub : ∀ k ∈ {k | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k},
      k ≤ 3 := by
    rintro k ⟨E, -, hE, hc⟩
    have h27 := s15k_om6_card_le hX E hE
    rw [hc] at h27
    by_contra hk
    have h4 : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (not_le.mp hk)
    omega
  exact le_antisymm (csSup_le ⟨3, hmem⟩ hub) (le_csSup ⟨3, hub⟩ hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
