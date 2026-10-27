module

public import CFSG.Quasithin.H13.NQCatA314LieL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParSp4

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Sp4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem lieP_perfectCore_projQ2 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (j : Fin 2) :
    LieP (Nat.card K = 4) (perfectCore ((Q2 K j).map (proj 2 K))) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have h4 : 4 ≤ Nat.card K := by
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN := perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)
  refine lieP_of_sl2 h4 ((blkN j).comp eN.symm.toMonoidHom)
    ((blkN_surjective (exists_finset_card_four h4) j).comp eN.symm.surjective) ?_
    fun _ h => ⟨CFSG.Quasithin.Rk2.charTwo_perfectCore_projQ2 j, h⟩
  intro z
  obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨eN.symm z.1, z.2⟩
  have h1 : (eN.symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k, Subtype.ext ?_⟩
  show z.1 ^ 2 ^ k = 1
  have : eN.symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
  exact (map_eq_one_iff _ eN.symm.injective).mp this

theorem lieP_perfectCore_of_projSp4 {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    {Pa : Subgroup (StatedProj (StatedSp 2 K))}
    (hpar : IsParabolic2 (⊤ : Subgroup (StatedProj (StatedSp 2 K))) Pa) (hne : Pa ≠ ⊤) :
    LieP (Nat.card K = 4) (perfectCore Pa) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  exact lieP_perfectCore_parabolic hU hres (fun j => lieP_perfectCore_projQ2 hf hf2 j) hpar hne

end Sp4

theorem lieP_sp4 {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ) (hf : 2 ≤ f)
    (hL : IsPSp4 2 f ↥L) (hP : IsMaxParabolic2 L P) : LieP (f = 2) (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine lieP_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  exact (lieP_perfectCore_of_equiv e (lieP_perfectCore_of_projSp4 hcard hf
    (isParabolic2_top_map_equiv e hpa) (ne_top_of_map_ne_top e hna))).mono
    (eq_two_of_card_eq_four hcard)

end CFSG.Quasithin.H13.NQCat.A314D
