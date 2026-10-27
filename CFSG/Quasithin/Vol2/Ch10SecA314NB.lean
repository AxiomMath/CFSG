module

public import CFSG.Quasithin.Vol2.Ch10SecA314NA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.A5N

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a CFSG.Assembly.LowTwoRank

section Three

variable {K : Type} [Field K] [Finite K]

theorem injOn_perfectCore_Q3 [CharP K 2] {S : Type} [Group S]
    (π : SpecialLinearGroup (Fin 3) K →* S) (hker : π.ker ≤ scalars 3 K) (j : Fin 2) :
    ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j), π x = π y → x = y := by
  intro x hx y hy hxy
  have hz : x⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
  have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ (hker hz)
  exact inv_mul_eq_one.mp (congrArg Subtype.val h1)

theorem not_isAlt_five_perfectCore_Q3 [CharP K 2] (j : Fin 2) :
    ¬ IsAlt 5 ↥(perfectCore (Q3 K j)) := by
  have hP : CharTwo ((Q3 K j).map (proj 3 K)) :=
    CFSG.QuasithinUnique.B113Lie.Lin.charTwo_projStabilizer (n := 3) (by omega)
      (by have := j.isLt; omega)
  intro hA
  exact not_isAlt_five_perfectCore_of_charTwo hP (IsAlt.of_mulEquiv
    (perfectCoreMapEquiv (proj 3 K) (Q3 K j) (injOn_perfectCore_Q3 _ (ker_proj 3 K).le j)) hA)

theorem not_isAlt_five_perfectCore_of_cover [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    {S : Type} [Group S] [Finite S] (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K)
    (hSyl : IsSylowTwoOf ((unitriangular 3 K).map π) ⊤) {Pa : Subgroup S}
    (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsAlt 5 ↥(perfectCore Pa) := by
  have hres := linear_three_residual_of_cover ⟨f, hf⟩ π hπ hker
  refine not_isAlt_five_perfectCore_parabolic hSyl hres (fun j h => ?_) hpar hne
  exact not_isAlt_five_perfectCore_Q3 j
    (IsAlt.of_mulEquiv (perfectCoreMapEquiv π (Q3 K j) (injOn_perfectCore_Q3 π hker j)).symm h)

end Three

theorem not_isAlt_five_perfectCore_l3 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 1 ≤ f) (hL : IsPSL 3 2 f ↥L ∨ IsSL3 (2 ^ f) ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsAlt 5 ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isAlt_five_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  rcases hL with hX | hX
  · obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* projectiveSL 3 K := e.trans (statedSLEquivProjectiveSL 3 K)
    obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine not_isAlt_five_perfectCore_of_equiv e' ?_
    exact not_isAlt_five_perfectCore_of_cover hcard (proj 3 K) (proj_surjective 3 K)
      (ker_proj 3 K).le hT₀ (isParabolic2_top_map_equiv e' hpa) (A5.G3.map_ne_top_of_equiv e' hna)
  · obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* SpecialLinearGroup (Fin 3) K :=
      φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
    obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : IsSylowTwoOf (unitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    refine not_isAlt_five_perfectCore_of_equiv e' ?_
    exact not_isAlt_five_perfectCore_of_cover hcard (MonoidHom.id _) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le) (by rw [Subgroup.map_id]; exact hT₀)
      (isParabolic2_top_map_equiv e' hpa) (A5.G3.map_ne_top_of_equiv e' hna)

section Sp4

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K] [Finite K]

theorem not_isAlt_five_perfectCore_of_projSp4 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    {Pa : Subgroup (StatedProj (StatedSp 2 K))}
    (hpar : IsParabolic2 (⊤ : Subgroup (StatedProj (StatedSp 2 K))) Pa) (hne : Pa ≠ ⊤) :
    ¬ IsAlt 5 ↥(perfectCore Pa) := by
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt ⟨f, hf⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine not_isAlt_five_perfectCore_parabolic hU hres (fun j => ?_) hpar hne
  refine not_isAlt_five_perfectCore_of_charTwo ?_
  fin_cases j
  · exact CFSG.QuasithinUnique.B113Lie.Sp.charTwo_projStabilizer_flag_one (r := 2) (K := K)
      (by norm_num)
  · exact CFSG.QuasithinUnique.B113Lie.Sp.charTwo_projStabilizer_flag_self (r := 2) (K := K)
      (by norm_num)

end Sp4

theorem not_isAlt_five_perfectCore_sp4 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 2 ≤ f) (hL : IsPSp4 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    ¬ IsAlt 5 ↥(perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine not_isAlt_five_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  exact not_isAlt_five_perfectCore_of_equiv e
    (not_isAlt_five_perfectCore_of_projSp4 hcard (isParabolic2_top_map_equiv e hpa)
      (A5.G3.map_ne_top_of_equiv e hna))

end CFSG.Quasithin.Vol2.Ch10.SecF.A5N
