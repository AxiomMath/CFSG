module

public import CFSG.Quasithin.Vol2.Ch11SecSSym5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

theorem eq_of_modO2Image_eq_of_perfect {J A B : Subgroup G} (hA : A ≤ J) (hB : B ≤ J)
    (hAp : ⁅A, A⁆ = A) (hBp : ⁅B, B⁆ = B) (hQA : pCoreOf 2 J ≤ Subgroup.normalizer (A : Set G))
    (hQB : pCoreOf 2 J ≤ Subgroup.normalizer (B : Set G))
    (h : modO2Image J A = modO2Image J B) : A = B := by
  have h1 := sup_eq_of_modO2Image_eq hA hB h
  rw [← perfectCore_sup_eq hAp (isSolvable_pCoreOf_two J) hQA, h1,
    perfectCore_sup_eq hBp (isSolvable_pCoreOf_two J) hQB]

theorem le_of_card_four {U C : Subgroup G} (hU : Nat.card ↥U = 4) {z y : G} (hz : z ∈ U)
    (hy : y ∈ U) (hz1 : z ≠ 1) (hy1 : y ≠ 1) (hzy : z ≠ y) (hzC : z ∈ C) (hyC : y ∈ C) :
    U ≤ C := by
  classical
  have hle : U ⊓ C ≤ U := inf_le_left
  have hd : Nat.card ↥(U ⊓ C) ∣ 2 ^ 2 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hU] at this
  have h3 : 3 ≤ Nat.card ↥(U ⊓ C) := by
    have : Fintype ↥(U ⊓ C) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    have hs : ({1, ⟨z, hz, hzC⟩, ⟨y, hy, hyC⟩} : Finset ↥(U ⊓ C)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h
        exact hzy (congrArg Subtype.val h)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => hz1 (congrArg Subtype.val h).symm,
          fun h => hy1 (congrArg Subtype.val h).symm⟩
    exact hs ▸ Finset.card_le_univ _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hk2 : k = 2 := by
    interval_cases k <;> simp_all
  have hW : U ⊓ C = U :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hU, hk', hk2]; norm_num)
  rw [← hW]
  exact inf_le_right

omit [Finite G] in
theorem card_vi_one {T J I' U : Subgroup G} (hU : IsVi T J I' 2 1 U)
    (hCV : fsuV T I' ⊓ Subgroup.centralizer (J : Set G) = ⊥) : Nat.card ↥U = 4 := by
  have h := hU.1.2.2.2.1
  rw [hCV, Subgroup.relIndex_bot_left] at h
  rw [h]
  norm_num

theorem exists_omegaOneCenter_fsuV {T J I' : Subgroup G} {n : ℕ} (hJ : Hyp11 G T J I' n) :
    ∃ z ∈ fsuV T I' ⊓ quasithinOmegaOneCenter T, z ≠ 1 :=
  (Subgroup.bot_or_exists_ne_one _).resolve_left
    (inf_omegaOneCenter_ne_bot' hJ.fsu.sylow.1 (isElemAbelian_fsuV hJ) (fsuV_le_T hJ)
      (T_le_normalizer_fsuV T I') (fsuV_ne_bot hJ))

theorem lOf_ne_of_cartanL {J U₁ U₂ X : Subgroup G} (cJ : CartanL J U₁ U₂ X)
    (hX : Nat.card ↥X = 9) : LOf J U₁ ≠ LOf J U₂ := by
  intro heq
  have hle : X ≤ X ⊓ LOf J U₁ := by
    have := cJ.b
    rwa [← heq, sup_idem] at this
  have := Subgroup.card_le_of_le hle
  rw [hX, cJ.card₁] at this
  omega

end CFSG.Quasithin.Vol2.Ch11.SecS
