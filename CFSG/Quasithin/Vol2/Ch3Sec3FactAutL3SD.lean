module

public import CFSG.Quasithin.Vol2.Ch3Sec3FactAutL3Red
public import CFSG.GH74.KGroups.L3EpsUniSyl
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBQPrimeLinearThreeSylowInner
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowSemidihedral
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSylowNormalizer

public section

namespace CFSG.Quasithin.H13.L3Eps

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.GH74.KGroups.L3Eps
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.Steinberg CFSG.BrauerLinearThree

theorem isPGroup_mulAut_of_semidihedral {G : Type*} [Group G] {m : ℕ} (hm : 2 ≤ m) {h t : G}
    (hh : orderOf h = 2 ^ (m + 1)) (ht : t ^ 2 = 1) (hconj : t * h * t⁻¹ = h ^ (2 ^ m - 1)) :
    IsPGroup 2 (MulAut ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers t)) := by
  obtain ⟨-, e, -, -⟩ := semidihedral_sup_zpowers hm hh ht hconj
  exact (CFSG.Semidihedral.FieldFactorOne.semidihedral_automorphism_isPGroup (n := m + 2)
    (by omega)).of_equiv (MulAut.congr e)

theorem card_sup_zpowers_of_semidihedral {G : Type*} [Group G] {m : ℕ} (hm : 2 ≤ m) {h t : G}
    (hh : orderOf h = 2 ^ (m + 1)) (ht : t ^ 2 = 1) (hconj : t * h * t⁻¹ = h ^ (2 ^ m - 1)) :
    Nat.card ↥(Subgroup.zpowers h ⊔ Subgroup.zpowers t) = 2 ^ (m + 2) :=
  (semidihedral_sup_zpowers hm hh ht hconj).1

section Linear

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem blockGammaHom_injective :
    Function.Injective (SteinbergBQ.PrimeLinearThree.blockGammaHom : GL (Fin 2) F →* _) := by
  intro g g' hg
  have h : (blockGamma g : Matrix (Fin 3) (Fin 3) F) = blockGamma g' :=
    congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hg
  rw [coe_blockGamma, coe_blockGamma] at h
  exact Units.ext (bdiag_injective h).1

theorem exists_sylow_projectiveSL_sd (hF4 : Nat.card F % 4 = 3) :
    ∃ P : Sylow 2 (projectiveSL 3 F), IsPGroup 2 (MulAut ↥(P : Subgroup (projectiveSL 3 F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set m := (Nat.card F + 1).factorization 2 with hm
  obtain ⟨hm2, ⟨j, hj⟩, hdvd, -⟩ := semidihedral_arith hF4
  rw [← hm] at hm2 hj hdvd
  obtain ⟨A, hAord, -, hAconj⟩ := exists_nonsplit_element hF4 hdvd
  set γ := (SteinbergBQ.PrimeLinearThree.blockGammaHom : GL (Fin 2) F →* _) with hγ
  set B : GL (Fin 2) F := CFSG.DesarguesianPlanes.diagGL 1 (-1) with hB
  have hB2 : B ^ 2 = 1 := by
    rw [hB, sq, CFSG.DesarguesianPlanes.diagGL_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CFSG.DesarguesianPlanes.diagGL]
  set h := γ A with hh
  set t := γ B with ht
  have hhord : orderOf h = 2 ^ (m + 1) := by
    rw [hh, orderOf_injective γ blockGammaHom_injective A, hAord]
  have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, hB2, map_one]
  have hconj : t * h * t⁻¹ = h ^ (2 ^ m - 1) := by
    have e1 : t * h * t⁻¹ = h ^ Nat.card F := by
      rw [ht, hh, ← map_inv, ← map_mul, ← map_mul, hB, hAconj, map_pow]
    rw [e1, hj, pow_add, pow_mul, ← hhord, pow_orderOf_eq_one, one_pow, one_mul]
  set Pt := Subgroup.zpowers h ⊔ Subgroup.zpowers t with hPt
  have hcard : Nat.card Pt = 2 ^ (m + 2) := card_sup_zpowers_of_semidihedral hm2 hhord ht2 hconj
  have hPt2 : IsPGroup 2 Pt := IsPGroup.of_card hcard
  have hAut : IsPGroup 2 (MulAut ↥Pt) := isPGroup_mulAut_of_semidihedral hm2 hhord ht2 hconj
  have hD3 : ∀ d ∈ scalars 3 F, d ^ 3 = 1 := fun d hd =>
    SteinbergBQ.PrimeLinearThree.pow_three_eq_one_of_mem_scalars hd
  have hinj : Set.InjOn (QuotientGroup.mk' (scalars 3 F)) (Pt : Set _) :=
    injOn_mk'_of_isPGroup_two hD3 hPt2
  let e : ↥Pt ≃* ↥(Pt.map (QuotientGroup.mk' (scalars 3 F))) :=
    equivMapOfInjOn (QuotientGroup.mk' (scalars 3 F)) Pt hinj
  have hF2 : Nat.card F % 2 = 1 := by omega
  have hcardP : Nat.card ↥(Pt.map (QuotientGroup.mk' (scalars 3 F))) =
      ordProj[2] (Nat.card (projectiveSL 3 F)) := by
    rw [← Nat.card_congr e.toEquiv, hcard, projectiveSL_card_two_part hF2,
      ordProj_two_sub_one_of_mod_four_eq_three hF4, ← hm]
    ring
  exact ⟨⟨Pt.map (QuotientGroup.mk' (scalars 3 F)), IsPGroup.of_card (by rw [hcardP]),
    fun {Q} hQ hle => le_antisymm (isMax_of_card hcardP Q hQ hle) hle⟩,
    hAut.of_equiv (MulAut.congr e)⟩

theorem exists_sylow_sd_of_isPSL {W : Type} [Group W] {p : ℕ} (h3 : p % 4 = 3)
    (hX : IsPSL 3 p 1 W) : ∃ P : Sylow 2 W, IsPGroup 2 (MulAut ↥(P : Subgroup W)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  exact exists_sylow_of_mulEquiv e
    (exists_sylow_projectiveSL_sd (by rw [hF, pow_one]; exact h3))

end Linear

section Unitary

variable {K : Type} [Field K] {p : ℕ}

theorem zpow_neg_eq_pow_of_factorization {G : Type*} [Group G] {q m : ℕ} (hq1 : 1 < q)
    (hm : m = (q - 1).factorization 2) (hq : q % 4 = 1) {u : G} (hu : orderOf u = 2 ^ (m + 1)) :
    u ^ (-(q : ℤ)) = u ^ (2 ^ m - 1) := by
  obtain ⟨w, hw, hqw⟩ := exists_odd_eq_two_pow_factorization_mul (n := q - 1) (by omega)
  rw [← hm] at hqw
  obtain ⟨k, rfl⟩ := hw
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have hqn : q = 2 ^ m * (2 * k + 1) + 1 := by rw [← hqw]; omega
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hu, Int.modEq_iff_dvd]
  refine ⟨k + 1, ?_⟩
  rw [hqn]
  push_cast [Nat.cast_sub h1]
  ring

theorem exists_sylow_SUgram_sd (hU : UnitaryFieldData p 1 K) (hp2 : p ≠ 2) (h1 : p ^ 1 % 4 = 1) :
    ∃ P : Sylow 2 (↥(SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)) ⧸
        (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))),
      IsPGroup 2 (MulAut ↥P.toSubgroup) := by
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K p := hU.charP
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  set D := (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))
    with hD
  have hmodels := odd_unitary_three_exact_coordinate_and_Sylow_models hU hp2 (G₀ := 1)
    (bar_one_apply' hU) hdet D le_rfl
  obtain ⟨-, -, -, -, -, h1part⟩ := hmodels
  obtain ⟨⟨z, hz⟩, ⟨M, hM⟩, hall⟩ := h1part h1
  obtain ⟨u, τ, -, -, hou, hτ2, hτu, -, -, -, -, hinj, hWbar2, hWbarcard⟩ := hall M hM z hz
  set m := (p ^ 1 - 1).factorization 2 with hm
  have hp1 : p ^ 1 = p := pow_one p
  have h1' : p % 4 = 1 := hp1 ▸ h1
  have hpp := hU.prime.two_le
  have hm2 : 2 ≤ m := by
    rw [hm, hp1, ← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)]
    exact Nat.dvd_of_mod_eq_zero (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; omega)
  have hu : orderOf u = 2 ^ (m + 1) := by rw [hou]; ring
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left (by rw [← sq, hτ2])
  have hconj : τ * u * τ⁻¹ = u ^ (2 ^ m - 1) := by
    calc τ * u * τ⁻¹ = τ⁻¹ * u * τ := by rw [hτi]
      _ = u ^ (-((p ^ 1 : ℕ) : ℤ)) := hτu
      _ = u ^ (2 ^ m - 1) := zpow_neg_eq_pow_of_factorization (by omega) hm h1 hu
  have hW : Subgroup.closure ({u, τ} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))) =
      Subgroup.zpowers u ⊔ Subgroup.zpowers τ := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hAut : IsPGroup 2 (MulAut ↥(Subgroup.closure
      ({u, τ} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))))) := by
    rw [hW]
    exact isPGroup_mulAut_of_semidihedral hm2 hu hτ2 hconj
  let e := equivMapOfInjOn (QuotientGroup.mk' D)
    (Subgroup.closure ({u, τ} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)))) hinj
  exact ⟨⟨_, hWbar2, fun {Q} hQ hle => le_antisymm (isMax_of_card hWbarcard Q hQ hle) hle⟩,
    hAut.of_equiv (MulAut.congr e)⟩

theorem exists_sylow_sd_of_isPSU {W : Type} [Group W] (hp2 : p ≠ 2) (h1 : p % 4 = 1)
    (hX : IsPSU 3 p 1 W) : ∃ P : Sylow 2 W, IsPGroup 2 (MulAut ↥(P : Subgroup W)) := by
  obtain ⟨K, _, hU, ⟨ψ⟩⟩ := exists_unitary_quotient_equiv hX
  have := hU.finite
  exact exists_sylow_of_mulEquiv ψ (exists_sylow_SUgram_sd hU hp2 (by rw [pow_one]; exact h1))

end Unitary

end CFSG.Quasithin.H13.L3Eps
