module

public import CFSG.RankThree.Classical.SiegelRadical

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {F : Type} [Field F] {n : ℕ}

@[expose] def projSiegelHom (n : ℕ) (F : Type) [Field F] :
    Multiplicative (symMatrices n F) →* StatedProj (StatedSp n F) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F))).comp
    (siegelSpHom n F)

@[expose] def projSiegelRadical (n : ℕ) (F : Type) [Field F] :
    Subgroup (StatedProj (StatedSp n F)) :=
  (projSiegelHom n F).range

theorem projSiegelHom_injective : Function.Injective (projSiegelHom n F) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  rw [projSiegelHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hB
  obtain ⟨c, hc⟩ := hB
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  ext i j
  have h := congrArg (fun g : GL (Fin n ⊕ Fin n) F =>
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl i) (Sum.inr j)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ Sum.inl_ne_inr] at h
  change 0 = siegelMat _ (Sum.inl i) (Sum.inr j) at h
  rw [siegelMat, Matrix.fromBlocks_apply₁₂] at h
  rw [toAdd_one, ZeroMemClass.coe_zero, Matrix.zero_apply]
  exact h.symm

theorem symplectic_Siegel_root_central_preimage_abelian {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    [Finite F] (hF : Nat.card F = p ^ f) :
    IsElemAbelian p (projSiegelRadical n F) ∧
      Nat.card (projSiegelRadical n F) = p ^ (f * (n * (n + 1) / 2)) ∧
      ∀ {Y : Type*} [Group Y] (φ : Y →* StatedProj (StatedSp n F)), Function.Surjective φ →
        φ.ker ≤ Subgroup.center Y → ∀ a ∈ (projSiegelRadical n F).comap φ,
          ∀ b ∈ (projSiegelRadical n F).comap φ, a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  refine ⟨isElemAbelian_range (nsmul_char_eq_zero _) _, ?_, ?_⟩
  · rw [projSiegelRadical, ← Nat.card_congr (MonoidHom.ofInjective projSiegelHom_injective).toEquiv,
      Nat.card_congr Multiplicative.toAdd, card_symMatrices, hF, ← pow_mul]
  · intro Y _ φ hφ hZ a ha b hb
    set π := QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F))
    let E : Subgroup (Y × StatedSp n F) := MonoidHom.eqLocus
      (φ.comp (MonoidHom.fst Y (StatedSp n F))) (π.comp (MonoidHom.snd Y (StatedSp n F)))
    let πE : E →* StatedSp n F := (MonoidHom.snd Y (StatedSp n F)).comp E.subtype
    have hπE : Function.Surjective πE := by
      intro s
      obtain ⟨y, hy⟩ := hφ (π s)
      exact ⟨⟨(y, s), hy⟩, rfl⟩
    have hZE : πE.ker ≤ Subgroup.center E := by
      rintro ⟨⟨y, s⟩, hys⟩ hx
      change s = 1 at hx
      subst hx
      have hy : y ∈ φ.ker := by
        change φ y = π 1 at hys
        rw [MonoidHom.mem_ker, hys, map_one]
      rw [Subgroup.mem_center_iff]
      rintro ⟨⟨y', s'⟩, -⟩
      apply Subtype.ext
      change (y' * y, s' * 1) = (y * y', 1 * s')
      rw [Subgroup.mem_center_iff.mp (hZ hy) y', mul_one, one_mul]
    have hcomm := siegel_radical_sp_preimage_comm hp hp3 hF n πE hπE hZE
    obtain ⟨B, hBa⟩ := Subgroup.mem_comap.mp ha
    obtain ⟨C, hCb⟩ := Subgroup.mem_comap.mp hb
    let a' : E := ⟨(a, siegelSpHom n F B), hBa.symm⟩
    let b' : E := ⟨(b, siegelSpHom n F C), hCb.symm⟩
    have h := hcomm a' ⟨B, rfl⟩ b' ⟨C, rfl⟩
    exact congrArg (fun x : E => (x : Y × StatedSp n F).1) h

end CFSG.RankThree.Classical
