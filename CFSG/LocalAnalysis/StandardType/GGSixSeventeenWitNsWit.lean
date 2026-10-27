module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitNsBasic

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType

namespace WitNs

open CoordSL Multiplicative

theorem supp_units_mul {s p : ℕ} (η : Fin s → (ZMod p)ˣ) (t : Fin s → ZMod p) :
    supp (fun i => (η i : ZMod p) * t i) = supp t := by
  ext i
  rw [mem_supp, mem_supp, Ne, Ne, (η i).isUnit.mul_right_eq_zero]

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [Fact p.Prime] {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ p = 1}

theorem exists_aligned_frame (hζ : AdjoinRoot.root g ^ p = 1) (t : Fin s → ZMod p) :
    ∃ (A₁ : Matrix.SpecialLinearGroup (Fin n) K) (η : Fin s → (ZMod p)ˣ),
      Aligned hζ (fun i => (η i : ZMod p) * t i) ∧
      (∀ u : Fin s → ZMod p, frameHom ψ A₁ ε hC hCp (ofAdd fun i => (η i : ZMod p) * u i) =
        frameHom ψ A₀ ε hC hCp (ofAdd u)) ∧
      (frameHom ψ A₁ ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range := by
  obtain ⟨η, hηO, hal⟩ := exists_aligned hζ t
  obtain ⟨M, hM⟩ := exists_conj_frameHom g ψ A₀ ε hC hCp hζ (Equiv.refl _) η hηO
  set w := SLRep.ggFrame ψ A₀ M with hwdef
  have hw : ∀ u : Fin s → ZMod p, frameHom ψ (A₀ * M) ε hC hCp (ofAdd u) =
      w * frameHom ψ A₀ ε hC hCp (ofAdd u) * w⁻¹ := by
    intro u
    simp only [hwdef, frameHom_apply, SLRep.ggFrame_apply, ← map_inv, ← map_mul]
    congr 1
    group
  have hι' : ∀ u : Fin s → ZMod p,
      frameHom ψ (A₀ * M) ε hC hCp (ofAdd fun i => (η i : ZMod p) * u i) =
        frameHom ψ A₀ ε hC hCp (ofAdd u) := by
    intro u
    have h := hM u
    simp only [Equiv.refl_apply] at h
    rw [hw, ← h]
    group
  refine ⟨A₀ * M, η, hal, hι', ?_⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨ofAdd fun i => ((η i)⁻¹ : (ZMod p)ˣ) * toAdd u i, ?_⟩
    rw [← hι']
    congr 1
    apply toAdd.injective
    funext i
    simp only [toAdd_ofAdd]
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  · rintro ⟨u, rfl⟩
    exact ⟨_, hι' (toAdd u)⟩

variable [CharP K 2]

theorem exists_comp_of_supp_le_two (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hgd : g ∣ cyclotomic p K) (hζ : AdjoinRoot.root g ^ p = 1) {B Bs G₀ : Subgroup G}
    (hc : SLNS.NSCtx ε hC p B Bs G₀ ψ A₀) (hrange : (frameHom ψ A₀ ε hC hCp).range = Bs)
    {t : Fin s → ZMod p} (ht0 : t ≠ 0) (ht2 : (supp t).card ≤ 2)
    (h3 : 3 ≤ (SLNS.fixS ε (supp t)).card) :
    ∃ L₂ : Subgroup G, CFSG.Assembly.IsComponentOf L₂
        (G₀ ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd t)}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2 := by
  obtain ⟨A₁, η, hal, hι', hrange'⟩ :=
    exists_aligned_frame (ψ := ψ) (A₀ := A₀) (ε := ε) (hC := hC) (hCp := hCp) hζ t
  have hsupp := supp_units_mul η t
  have hc' : SLNS.NSCtx ε hC p B Bs G₀ ψ A₁ :=
    { hc with
      frame := fun b hb => by
        rw [← hrange, ← hrange'] at hb
        obtain ⟨a, rfl⟩ := hb
        exact ⟨fun i => (toAdd a i).val, rfl⟩ }
  obtain ⟨i₀, hi₀⟩ : ∃ i, t i ≠ 0 := by
    by_contra h
    push Not at h
    exact ht0 (funext h)
  set x₀ : Fin n := ε.symm (Sum.inl (⟨0, rootPB_dim_pos g⟩, i₀)) with hx₀
  have hx₀Z : x₀ ∉ zeroCoords ε (fun i => (η i : ZMod p) * t i) := by
    rw [mem_zeroCoords_inl (by rw [hx₀, Equiv.apply_symm_apply]),
      (η i₀).isUnit.mul_right_eq_zero]
    exact hi₀
  have h3' : 3 ≤ (zeroCoords ε (fun i => (η i : ZMod p) * t i)).card := by
    rwa [zeroCoords_eq_fixS, hsupp]
  have hcomp := isComponentOf_zeroBlock (A₀ := A₁) (hC := hC) (hCp := hCp) hp2 hpK hc.ker hgd
    hal h3' hx₀Z
  rw [zeroCoords_eq_fixS, hsupp, hι' t, hc.range] at hcomp
  refine ⟨_, hcomp, ?_⟩
  exact (hc'.card_centralizer_le (supp t) (by omega) (rootPB_dim_pos g)).trans
    (Nat.pow_le_pow_right hc.prime.pos ht2)

end WitNs

end CFSG.StandardType
