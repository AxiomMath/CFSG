module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHL4Blocks
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofProj
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHLift

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

theorem l4_good429_of_mulEquiv {S : Type} [Group S] (φ : S ≃* S) {P : Subgroup S}
    (hP : ∀ g, g ∈ P ↔ φ g ∈ P) {x : S} (h : Good429 (Subgroup.centralizer ({x} : Set S) ⊓ P)) :
    Good429 (Subgroup.centralizer ({φ x} : Set S) ⊓ P) := by
  have hmap : (Subgroup.centralizer ({x} : Set S) ⊓ P).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set S) ⊓ P := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      exact ⟨by rw [← map_mul, ← map_mul, hzc], (hP z).mp hzP⟩
    · rintro ⟨hwc, hwP⟩
      refine ⟨φ.symm w, ⟨φ.injective ?_, (hP _).mpr (by rwa [MulEquiv.apply_symm_apply])⟩,
        MulEquiv.apply_symm_apply φ w⟩
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hwc
  rw [← hmap]
  exact h.map_mulEquiv φ

theorem l4_pattern : ∀ a : Fin 4 → ZMod 3, (∃ i j, a i ≠ a j) →
    (a 0 ≠ a 2 ∧ a 0 ≠ a 3 ∧ a 1 ≠ a 2 ∧ a 1 ≠ a 3) ∨
    (a 0 ≠ a 1 ∧ a 0 ≠ a 3 ∧ a 2 ≠ a 1 ∧ a 2 ≠ a 3) ∨
    (a 0 ≠ a 2 ∧ a 0 ≠ a 1 ∧ a 3 ≠ a 2 ∧ a 3 ≠ a 1) ∨
    (a 0 = a 1 ∧ a 1 = a 2 ∧ a 2 ≠ a 3) ∨
    (a 3 = a 1 ∧ a 1 = a 2 ∧ a 2 ≠ a 0) ∨
    (a 0 = a 3 ∧ a 3 = a 2 ∧ a 2 ≠ a 1) ∨
    (a 0 = a 1 ∧ a 1 = a 3 ∧ a 3 ≠ a 2) := by
  decide +kernel

section Diag

variable
  {K : Type} [Field K]

theorem l4_good429_diag [Finite K] (h3 : (3 : K) ≠ 0) {ω : K} (hω : IsPrimitiveRoot ω 3)
    {G : Subgroup (GL (Fin 4) K)} {Q : Subgroup (GL (Fin 3) K)} (hQ : IsQuasisimple Q)
    (hGdet : ∀ g ∈ G, (g : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hGσ : ∀ (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) K),
      g ∈ G ↔ Sec21.Tables.reindexGL σ g ∈ G)
    (hE : ∀ B ∈ Q, l4BlkGL3 B ∈ G)
    (hβ : ∀ M ∈ G, ∀ B : GL (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc →
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
        (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0) →
      (B : Matrix (Fin 3) (Fin 3) K).det = 1 → B ∈ Q)
    {D : GL (Fin 4) K} (hDG : D ∈ G) (hD3 : D ^ 3 = 1) {a : Fin 4 → ZMod 3}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal (fun i => ω ^ (a i).val))
    (ha : ∃ i j, a i ≠ a j) :
    Good429 (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
  set d : Fin 4 → K := fun i => ω ^ (a i).val with hd
  have hne : ∀ i j, a i ≠ a j → d i ≠ d j := fun i j hij h =>
    hij (ZMod.val_injective 3 (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have heq : ∀ i j, a i = a j → d i = d j := fun i j hij => by
    simp only [hd, hij]
  have hT : ∀ σ : Equiv.Perm (Fin 4),
      Good429 (Subgroup.centralizer ({Sec21.Tables.reindexGL σ D} : Set (GL (Fin 4) K)) ⊓ G) →
      Good429 (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
    intro σ h
    have h' := l4_good429_of_mulEquiv (Sec21.Tables.reindexGL σ).symm (P := G)
      (fun g => by rw [hGσ σ ((Sec21.Tables.reindexGL σ).symm g), MulEquiv.apply_symm_apply]) h
    rwa [MulEquiv.symm_apply_apply] at h'
  have hσD : ∀ σ : Equiv.Perm (Fin 4),
      ((Sec21.Tables.reindexGL σ D : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal (d ∘ σ) := by
    intro σ
    rw [Sec21.Tables.coe_reindexGL, hD, submatrix_diagonal_equiv]
  have two : ∀ (σ : Equiv.Perm (Fin 4)) (i₀ i₁ i₂ i₃ : Fin 4), σ 0 = i₀ → σ 1 = i₁ →
      σ 2 = i₂ → σ 3 = i₃ → a i₀ ≠ a i₂ → a i₀ ≠ a i₃ → a i₁ ≠ a i₂ → a i₁ ≠ a i₃ →
      Good429 (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
    intro σ i₀ i₁ i₂ i₃ e0 e1 e2 e3 h02 h03 h12 h13
    apply hT σ
    intro L hLC hLp _
    haveI := hLp
    refine l4_not_isType429_two_blocks h3 (hσD σ) ?_ ?_ ?_ ?_ (hLC.trans inf_le_left)
    · simp only [Function.comp_apply, e0, e2]; exact hne _ _ h02
    · simp only [Function.comp_apply, e0, e3]; exact hne _ _ h03
    · simp only [Function.comp_apply, e1, e2]; exact hne _ _ h12
    · simp only [Function.comp_apply, e1, e3]; exact hne _ _ h13
  have three : ∀ (σ : Equiv.Perm (Fin 4)) (i₀ i₁ i₂ i₃ : Fin 4), σ 0 = i₀ → σ 1 = i₁ →
      σ 2 = i₂ → σ 3 = i₃ → a i₀ = a i₁ → a i₁ = a i₂ → a i₂ ≠ a i₃ →
      Good429 (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
    intro σ i₀ i₁ i₂ i₃ e0 e1 e2 e3 h01 h12 h23
    apply hT σ
    have hDσG : Sec21.Tables.reindexGL σ D ∈ G := (hGσ σ D).mp hDG
    refine l4_good429_three_one hQ hE hβ hDσG (hσD σ) ?_ ?_ ?_ (hGdet _ hDσG)
      (by rw [← map_pow, hD3, map_one])
    · simp only [Function.comp_apply, e0, e1]; exact heq _ _ h01
    · simp only [Function.comp_apply, e1, e2]; exact heq _ _ h12
    · simp only [Function.comp_apply, e2, e3]; exact hne _ _ h23
  rcases l4_pattern a ha with h | h | h | h | h | h | h
  · exact two 1 0 1 2 3 rfl rfl rfl rfl h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact two (Equiv.swap 1 2) 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
      h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact two (Equiv.swap 1 3) 0 3 2 1 (by decide) (by decide) (by decide) (by decide)
      h.1 h.2.1 h.2.2.1 h.2.2.2
  · exact three 1 0 1 2 3 rfl rfl rfl rfl h.1 h.2.1 h.2.2
  · exact three (Equiv.swap 0 3) 3 1 2 0 (by decide) (by decide) (by decide) (by decide)
      h.1 h.2.1 h.2.2
  · exact three (Equiv.swap 1 3) 0 3 2 1 (by decide) (by decide) (by decide) (by decide)
      h.1 h.2.1 h.2.2
  · exact three (Equiv.swap 2 3) 0 1 3 2 (by decide) (by decide) (by decide) (by decide)
      h.1 h.2.1 h.2.2

theorem l4_good429_of_conj [Finite K] (h3 : (3 : K) ≠ 0) {ω : K} (hω : IsPrimitiveRoot ω 3)
    {G : Subgroup (GL (Fin 4) K)} {Q : Subgroup (GL (Fin 3) K)} (hQ : IsQuasisimple Q)
    (hGdet : ∀ g ∈ G, (g : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hGσ : ∀ (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) K),
      g ∈ G ↔ Sec21.Tables.reindexGL σ g ∈ G)
    (hE : ∀ B ∈ Q, l4BlkGL3 B ∈ G)
    (hβ : ∀ M ∈ G, ∀ B : GL (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc →
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
        (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0) →
      (B : Matrix (Fin 3) (Fin 3) K).det = 1 → B ∈ Q)
    (hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 3 = 1 → u = 1)
    {A : GL (Fin 4) K} (hAG : A ∈ G) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) {g : GL (Fin 4) K}
    (hg : ∀ h, h ∈ G ↔ g * h * g⁻¹ ∈ G) {a : Fin 4 → ZMod 3}
    (hD : ((g * A * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun i => ω ^ (a i).val)) :
    Good429 (Subgroup.centralizer ({A} : Set (GL (Fin 4) K)) ⊓ G) := by
  set D : GL (Fin 4) K := g * A * g⁻¹ with hDdef
  have hDG : D ∈ G := (hg A).mp hAG
  have hD3 : D ^ 3 = 1 := by rw [hDdef, conj_pow, hA3, mul_one, mul_inv_cancel]
  have ha : ∃ i j, a i ≠ a j := by
    by_contra hcon
    push Not at hcon
    set c : Kˣ := Units.mk0 (ω ^ (a 0).val) (pow_ne_zero _ (hω.ne_zero (by norm_num))) with hc
    have hDs : D = GeneralLinearGroup.scalar (Fin 4) c := by
      apply Units.ext
      rw [hD, GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hc, hcon i 0]
      · simp [diagonal_apply_ne _ hij, hij]
    have hcen : ∀ x : GL (Fin 4) K, x * GeneralLinearGroup.scalar (Fin 4) c =
        GeneralLinearGroup.scalar (Fin 4) c * x := fun x =>
      Subgroup.mem_center_iff.mp (by
        rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨c, rfl⟩) x
    have hAs : A = GeneralLinearGroup.scalar (Fin 4) c := by
      have e : A = g⁻¹ * D * g := by rw [hDdef]; group
      rw [e, hDs, mul_assoc, ← hcen g, ← mul_assoc, inv_mul_cancel, one_mul]
    have hc3 : c ^ 3 = 1 := by
      have e := hA3
      rw [hAs, ← map_pow] at e
      exact (Sec21.Item228Census3Proof.scalar_eq_one_iff (ι := Fin 4)).mp e
    exact hA1 (by rw [hAs, hZ3 c (hAs ▸ hAG) hc3, map_one])
  have h := l4_good429_diag h3 hω hQ hGdet hGσ hE hβ hDG hD3 hD ha
  have h' := Good429.conj_of_normalizes (k := g⁻¹) (fun h => by
    rw [hg (g⁻¹ * h * g⁻¹⁻¹), show g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ = h by group]) h
  rwa [show g⁻¹ * D * g⁻¹⁻¹ = A by rw [hDdef]; group] at h'

end Diag

section Proj

open Sec21.Item228Census3Proof

theorem l4_good429_proj {K : Type} [Field K] [Finite K] (G : Subgroup (GL (Fin 4) K))
    (hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 4 = 1)
    (hgood : ∀ A : G, A ^ 3 = 1 → A ≠ 1 →
      Good429 (Subgroup.centralizer ({(A : GL (Fin 4) K)} : Set (GL (Fin 4) K)) ⊓ G))
    (y : projImage G) (hy : orderOf y = 3) :
    Good429 (Subgroup.centralizer ({y} : Set (projImage G))) := by
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 3 = 1 → u = 1 :=
    fun u hu h3 => by
      calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
        _ = 1 := by rw [hZ4 u hu, h3, inv_one, one_mul]
  obtain ⟨A, hAy, hA3, hA1⟩ := exists_lift_cube G hZ4 y hy
  rw [← hAy, centralizer_projRestrict G A hA3 hZ3]
  have hcen : ∀ g : G, g ∈ (projRestrict G).ker → ∃ u : Kˣ,
      GeneralLinearGroup.scalar (Fin 4) u = (g : GL (Fin 4) K) := fun g hg =>
    (projRestrict_eq_one_iff G).mp hg
  have hcomm : ∀ (u : Kˣ) (x : GL (Fin 4) K), x * GeneralLinearGroup.scalar (Fin 4) u =
      GeneralLinearGroup.scalar (Fin 4) u * x := fun u x =>
    Subgroup.mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩) x
  have hZ : (projRestrict G).ker ≤ Subgroup.center G := by
    intro g hg
    obtain ⟨u, hu⟩ := hcen g hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hu]
    exact hcomm u h
  have h2 : IsPGroup 2 (projRestrict G).ker := by
    intro g
    obtain ⟨u, hu⟩ := hcen g g.2
    refine ⟨2, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hu4 : u ^ 4 = 1 := hZ4 u (hu ▸ (g : G).2)
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hu, ← map_pow, show 2 ^ 2 = 4 by norm_num, hu4, map_one]
  have hC : (projRestrict G).ker ≤ Subgroup.centralizer ({A} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hZ hg) A).symm
  refine Good429.map_of_central (projRestrict G) (projRestrict_surjective G) hZ h2 hC ?_
  apply Good429.of_map G.subtype G.subtype_injective
  rw [map_centralizer_singleton G.subtype G.subtype_injective A, Subgroup.range_subtype]
  exact hgood A hA3 hA1

end Proj

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
