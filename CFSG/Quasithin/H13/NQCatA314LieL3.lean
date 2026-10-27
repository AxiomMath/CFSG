module

public import CFSG.Quasithin.H13.NQCatA314LieGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3L3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Three

variable {K : Type} [Field K] [Finite K]

theorem lieP_perfectCore_Q3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (j : Fin 2) : LieP (Nat.card K = 4) (perfectCore (Q3 K j)) := by
  by_cases h4 : 4 ≤ Nat.card K
  · have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
    exact lieP_of_sl2 h4 (blk3 j) (blk3_surjective (exists_finset_card_four h4) j)
      (blk3_ker_isPGroup hK j) fun _ h => ⟨CFSG.Quasithin.Rk2.charTwo_perfectCore_Q3 j, h⟩
  · have hf1' : f = 1 := by
      by_contra hne
      apply h4
      rw [hf]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    subst hf1'
    have hK2 : Nat.card K = 2 := by rw [hf]; norm_num
    rw [CFSG.QuasithinUnique.A5.G3.perfectCore_Q3_eq_bot_of_card_two hK2 j]
    exact lieP_bot _

theorem lieP_perfectCore_of_cover [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    {S : Type} [Group S] [Finite S] (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf ((unitriangular 3 K).map π) ⊤) {Pa : Subgroup S}
    (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    LieP (Nat.card K = 4) (perfectCore Pa) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres := linear_three_residual_of_cover hK π hπ hker
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      π x = π y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ (hker hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  refine lieP_perfectCore_parabolic hSyl hres (fun j => ?_) hpar hne
  exact (lieP_perfectCore_Q3 hf hf1 j).of_equiv (perfectCoreMapEquiv π (Q3 K j) (hinj j))

end Three

theorem ne_top_of_map_ne_top {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {Pa : Subgroup X}
    (h : Pa ≠ ⊤) : Pa.map e.toMonoidHom ≠ ⊤ :=
  CFSG.QuasithinUnique.A5.G3.map_ne_top_of_equiv e h

theorem lieP_l3 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ) (hf : 1 ≤ f)
    (hL : IsPSL 3 2 f ↥L ∨ IsSL3 (2 ^ f) ↥L) (hP : IsMaxParabolic2 L P) :
    LieP (f = 2) (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine lieP_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  rcases hL with hX | hX
  · obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* projectiveSL 3 K := e.trans (statedSLEquivProjectiveSL 3 K)
    obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine lieP_perfectCore_of_equiv e' ?_
    exact (lieP_perfectCore_of_cover hcard hf (proj 3 K) (proj_surjective 3 K)
      (ker_proj 3 K).le hT₀ (isParabolic2_top_map_equiv e' hpa)
      (ne_top_of_map_ne_top e' hna)).mono (eq_two_of_card_eq_four hcard)
  · obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hX
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
    let e' : ↥L ≃* SpecialLinearGroup (Fin 3) K :=
      φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
    obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
    have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ :=
      hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
    refine lieP_perfectCore_of_equiv e' ?_
    exact (lieP_perfectCore_of_cover hcard hf (MonoidHom.id _) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le) (by rw [Subgroup.map_id]; exact hT₀)
      (isParabolic2_top_map_equiv e' hpa) (ne_top_of_map_ne_top e' hna)).mono
      (eq_two_of_card_eq_four hcard)

end CFSG.Quasithin.H13.NQCat.A314D
