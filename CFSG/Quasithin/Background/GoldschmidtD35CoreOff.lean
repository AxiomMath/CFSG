module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreInv
public import CFSG.Quasithin.Background.GoldschmidtD35CoreField
public import CFSG.Quasithin.Background.GoldschmidtD35CoreSetup

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin
open scoped Matrix

variable {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}

theorem card_valentiner (hval : IsValentiner K Γ) : Nat.card Γ = 1080 := by
  obtain ⟨-, -, ⟨-, hZ, ⟨e⟩⟩, -⟩ := hval
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Γ),
    Nat.card_congr e.toEquiv, hA, hZ]

@[expose] def fixSubΓ (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) (B : Subgroup Γ) :
    Submodule K (Fin 3 → K) where
  carrier := fixNat Γ B
  add_mem' := fun {x y} hx hy γ hγ => by
    rw [Matrix.mulVec_add, hx γ hγ, hy γ hγ]
  zero_mem' := fun γ _ => by simp
  smul_mem' := fun c x hx γ hγ => by rw [Matrix.mulVec_smul, hx γ hγ]

theorem exists_card_fixNat (B : Subgroup Γ) :
    ∃ d : ℕ, d ≤ 3 ∧ Nat.card (fixNat Γ B) = Nat.card K ^ d := by
  refine ⟨Module.finrank K (fixSubΓ Γ B), ?_, ?_⟩
  · simpa using Submodule.finrank_le (fixSubΓ Γ B)
  · exact Module.natCard_eq_pow_finrank (K := K) (V := ↥(fixSubΓ Γ B))

theorem card_fixNat_bot (hK : Nat.card K = 4) : Nat.card (fixNat Γ ⊥) = 64 := by
  have : fixNat Γ ⊥ = Set.univ := by
    ext w
    simp only [fixNat, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro γ hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp
  rw [this, Nat.card_univ, Nat.card_fun, hK, Nat.card_fin]
  norm_num

theorem fixNat_subset {B : Subgroup Γ} {t : Γ} (ht : t ∈ B) :
    fixNat Γ B ⊆ {w | ((t : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      w = w} := fun _ hw => hw t ht

theorem card_fix_elt [Finite K] (hval : IsValentiner K Γ) {t : Γ} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Nat.card {w : Fin 3 → K | ((t : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ w = w} = 16 := by
  have hK := hval.1
  have := charP_two_of_card_four hK
  have hg2 : ∀ v, glLin t.1 (glLin t.1 v) = v := fun v => by
    have h := congrArg (fun γ : Γ => glLin γ.1 v) ht2
    simpa [map_mul] using h
  have hg1 : glLin t.1 ≠ 1 := fun h =>
    ht1 (Subtype.ext (glLin.injective (h.trans (map_one glLin).symm)))
  have := card_fix_involution (Module.finrank_fin_fun K) hg2 hg1
  rw [hK] at this
  exact this

end CFSG.Quasithin.D35Core
