module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual

public section

namespace CFSG.Quasithin.QA21

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

structure BorelPkg (X : Type) [Group X] (U : Subgroup X) (P : Fin 2 → Subgroup X) : Prop where
  res : ResidualOvergroupsAt X U P
  norm : ∀ j, Subgroup.normalizer (U : Set X) ≤ P j
  solv : ∀ A : Subgroup X, U ≤ A → Group.IsSolvable ↥A → A ≤ Subgroup.normalizer (U : Set X)

theorem BorelPkg.exists_index {X : Type} [Group X] [Finite X] {U : Subgroup X}
    {P : Fin 2 → Subgroup X} (h : BorelPkg X U P) {M D : Subgroup X} (hUM : U ≤ M) (hM : M ≠ ⊤)
    (hMs : ¬ Group.IsSolvable ↥M) (hUD : U ≤ D) (hD : Group.IsSolvable ↥D) :
    ∃ j : Fin 2, M ≤ P j ∧ D ≤ P j ∧ U ≤ P j ∧ P j ≠ ⊤ ∧
      ∀ α : MulAut X, U.map α.toMonoidHom = U → M.map α.toMonoidHom = M →
        (P j).map α.toMonoidHom = P j := by
  obtain ⟨-, hUP, hmax, -, hC2, -⟩ := h.res
  obtain ⟨j, hjk, -⟩ := hC2 M hUM hM hMs
  have hMj : M ≤ P j := (hjk j).2 rfl
  have hcovj : P j ⋖ ⊤ := (hmax (P j) (hUP j)).2 ⟨j, rfl⟩
  refine ⟨j, hMj, (h.solv D hUD hD).trans (h.norm j), hUP j, hcovj.ne, ?_⟩
  intro α hαU hαM
  have hcov : (P j).map α.toMonoidHom ⋖ ⊤ := by
    have h1 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup α)).2 hcovj
    rwa [show (MulEquiv.mapSubgroup α) (⊤ : Subgroup X) = ⊤ from
      Subgroup.map_top_of_surjective _ α.surjective] at h1
  have hU' : U ≤ (P j).map α.toMonoidHom := by
    rw [← hαU]
    exact Subgroup.map_mono (hUP j)
  obtain ⟨k, hk⟩ := (hmax _ hU').1 hcov
  have hMk : M ≤ P k := by
    rw [← hk]
    exact le_trans (le_of_eq hαM.symm) (Subgroup.map_mono hMj)
  have hkj : k = j := (hjk k).1 hMk
  rw [hk, hkj]

structure BorelAmbient (W : Type) [Group W] (C V B : Subgroup W) (Q : Fin 2 → Subgroup W) :
    Prop where
  V_le : V ≤ C
  B_le_normalizer : B ≤ Subgroup.normalizer (V : Set W)
  normalizer_le : C ⊓ Subgroup.normalizer (V : Set W) ≤ B
  B_le_Q : ∀ j, B ≤ Q j
  solv : ∀ A : Subgroup W, A ≤ C → V ≤ A → Group.IsSolvable ↥A → A ≤ B

theorem BorelAmbient.borelPkg {W X : Type} [Group W] [Group X] {C V B : Subgroup W}
    {Q : Fin 2 → Subgroup W} (h : BorelAmbient W C V B Q) (φ : X ≃* ↥C) {U : Subgroup X}
    (hU : U.map φ.toMonoidHom = V.subgroupOf C)
    (hres : ResidualOvergroupsAt X U (fun j => ((Q j).subgroupOf C).map φ.symm.toMonoidHom)) :
    BorelPkg X U (fun j => ((Q j).subgroupOf C).map φ.symm.toMonoidHom) := by
  have hN : (Subgroup.normalizer (U : Set X)).map φ.toMonoidHom =
      (Subgroup.normalizer (V : Set W)).subgroupOf C := by
    rw [Subgroup.map_equiv_normalizer_eq U φ, hU,
      ← Subgroup.subgroupOf_normalizer_eq h.V_le]
  have hnormφ : ∀ n : X, n ∈ Subgroup.normalizer (U : Set X) →
      (φ n : W) ∈ B := by
    intro n hn
    have h1 : φ n ∈ (Subgroup.normalizer (U : Set X)).map φ.toMonoidHom := ⟨n, hn, rfl⟩
    rw [hN] at h1
    exact h.normalizer_le ⟨(φ n).2, h1⟩
  refine ⟨hres, fun j n hn => ?_, fun A hUA hA a ha => ?_⟩
  · refine ⟨φ n, ?_, by simp⟩
    exact Subgroup.mem_subgroupOf.2 (h.B_le_Q j (hnormφ n hn))
  ·
    set ψ : X →* W := C.subtype.comp φ.toMonoidHom with hψ
    have hψinj : Function.Injective ψ := C.subtype_injective.comp φ.injective
    set A' : Subgroup W := A.map ψ with hA'
    have hA'C : A' ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact (φ x).2
    have hVA' : V ≤ A' := by
      have h1 : U.map φ.toMonoidHom ≤ A.map φ.toMonoidHom := Subgroup.map_mono hUA
      rw [hU] at h1
      have h2 := Subgroup.map_mono (f := C.subtype) h1
      rw [Subgroup.map_subgroupOf_eq_of_le h.V_le, Subgroup.map_map] at h2
      exact h2
    have hsolv' : Group.IsSolvable ↥A' :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective A ψ hψinj).symm.toMonoidHom)
        (Subgroup.equivMapOfInjective A ψ hψinj).symm.injective
    have hAB : A' ≤ B := h.solv A' hA'C hVA' hsolv'
    have h1 : (φ a : W) ∈ B := hAB ⟨a, ha, rfl⟩
    have h2 : φ a ∈ (Subgroup.normalizer (V : Set W)).subgroupOf C :=
      Subgroup.mem_subgroupOf.2 (h.B_le_normalizer h1)
    rw [← hN] at h2
    obtain ⟨n, hn, hna⟩ := h2
    have : n = a := φ.injective hna
    rwa [← this]

end CFSG.Quasithin.QA21
