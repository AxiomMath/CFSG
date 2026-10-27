module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52TorusPerm

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

private theorem mem_torusSU_of_isDiag_of_mem_unitarySU {K : Type} [Field K]
    (hU : UnitaryFieldData 2 1 K) {w : GL (Fin 5) K} (hw : w ∈ unitarySU 2 1 K 5)
    (hdiag : ((w : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag) : w ∈ torusSU 3 5 K := by
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag hdiag
  obtain ⟨hdet, hunit⟩ := (mem_unitarySU_iff hU).1 hw
  rw [← hd, diagU_val, Matrix.diagonal_map (map_zero hU.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] at hunit
  rw [← hd, det_diagU] at hdet
  refine mem_torusSU_iff.2 ⟨d, fun i => ?_, Units.ext (by rw [Units.coe_prod]; exact hdet), hd⟩
  have h1 := congrFun (congrFun hunit i) i
  rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hU.bar_apply] at h1
  exact Units.ext (by simpa [pow_succ, mul_comm, mul_assoc] using h1)

theorem centralizer_torus_le_of_U52 {G : Type} [Group G] {X T : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) (hT : IsElemAbelian 3 T) (hTX : T ≤ X)
    (hcard : Nat.card T = 3 ^ 4) :
    X ⊓ centralizer (T : Set G) ≤ T := by
  obtain ⟨K, _, hU, ψ, hψ⟩ := exists_torusFrame_of_U52 hX hT hTX hcard
  intro x hx
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
  set g := ψ.symm ⟨x, hxX⟩ with hg
  have hgx : ((ψ g : X) : G) = x := by simp [hg]
  rw [← hgx, hψ g]
  have hTS : torusSU 3 5 K ≤ unitarySU 2 1 K 5 := torusSU_le_unitarySU hU (by norm_num)
  have hcomm : ∀ h ∈ torusSU 3 5 K, (g : GL (Fin 5) K) * h = h * (g : GL (Fin 5) K) := by
    intro h hh
    have h1 := Subgroup.mem_centralizer_iff.1 hxC ((ψ ⟨h, hTS hh⟩ : X) : G) ((hψ ⟨h, hTS hh⟩).2 hh)
    rw [← hgx] at h1
    have h2 : g * ⟨h, hTS hh⟩ = ⟨h, hTS hh⟩ * g :=
      ψ.injective (Subtype.ext (by simpa using h1.symm))
    exact congrArg Subtype.val h2
  have hdist := torusSU_three_char_distinct hU
  have hw : ∀ x ∈ torusSU 3 5 K, (g : GL (Fin 5) K) * x * (g : GL (Fin 5) K)⁻¹ = x :=
    fun x hx => by rw [hcomm x hx, mul_inv_cancel_right]
  obtain ⟨σ, -, hσ2, hσ3⟩ := exists_perm_of_normalizes (torusSU 3 5 K)
    (fun x hx => isDiag_of_mem_torusSU hx) hdist (w := (g : GL (Fin 5) K))
    (fun x hx => by rw [hw x hx]; exact hx)
    (fun x hx => by rw [mul_assoc, ← hcomm x hx, inv_mul_cancel_left]; exact hx)
  have hσ : ∀ i, σ i = i := by
    intro i
    by_contra hne
    obtain ⟨x, hx, hxne⟩ := hdist (σ i) i hne
    exact hxne (by simpa [hw x hx] using hσ3 x hx i)
  refine mem_torusSU_of_isDiag_of_mem_unitarySU hU g.2 fun i j hij => ?_
  by_contra hne
  exact hij ((hσ2 j i hne).trans (hσ j))

theorem le_ncard_conj_torus_of_U52 {G : Type} [Group G] {X T : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) (hT : IsElemAbelian 3 T) (hTX : T ≤ X)
    (hcard : Nat.card T = 3 ^ 4) :
    120 ≤ ((fun y : G => fun b : T => y * (b : G) * y⁻¹) ''
      ((X ⊓ normalizer (T : Set G) : Subgroup G) : Set G)).ncard := by
  obtain ⟨K, _, hU, ψ, hψ⟩ := exists_torusFrame_of_U52 hX hT hTX hcard
  have : Finite K := hU.finite
  have : Finite X := Finite.of_equiv _ ψ.toEquiv
  have hfin : ((X ⊓ normalizer (T : Set G) : Subgroup G) : Set G).Finite :=
    (Set.toFinite (X : Set G)).subset fun y hy => hy.1
  set Φ : Equiv.Perm (Fin 5) → T → G := fun σ b =>
    U52TorusCarried.torusPermElt hU ψ σ * (b : G) * (U52TorusCarried.torusPermElt hU ψ σ)⁻¹ with hΦ
  have hinj : Function.Injective Φ := fun σ₁ σ₂ h =>
    hψ.torusPermElt_conj_inj hU hTX fun b => congrFun h b
  have hsub : Set.range Φ ⊆ (fun y : G => fun b : T => y * (b : G) * y⁻¹) ''
      ((X ⊓ normalizer (T : Set G) : Subgroup G) : Set G) := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨_, hψ.torusPermElt_mem hU hTX σ, rfl⟩
  calc 120 = (Set.univ : Set (Equiv.Perm (Fin 5))).ncard := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
    _ = (Set.range Φ).ncard := by rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj]
    _ ≤ _ := Set.ncard_le_ncard hsub (hfin.image _)

end CFSG.GGQ2Prime
