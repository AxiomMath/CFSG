module

public import CFSG.Quasithin.Background.SmithB42SL3Trace
public import CFSG.Quasithin.Background.SmithB42SL3Base

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.QuasithinUnique.Setup.X7a CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open CFSG.Quasithin.B42SL3 (trZ cast_trZ trZ_add trZ_cast_mul trZ_zero trZ_sum)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

noncomputable abbrev PFrep (ρ : Representation (ZMod 2) SL(3, F) U) {n : ℕ}
    (bas : Module.Basis (Fin n) (ZMod 2) U) : SL(3, F) →* Matrix (Fin n) (Fin n) F :=
  matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas)

theorem exists_traceHom (hF : Fintype.card F = 2 ^ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (W₀ : Subrepresentation (matRep (PFrep ρ bas))) {κ : Type} [Fintype κ] [DecidableEq κ]
    [Nonempty κ] {R : SL(3, F) →* Matrix κ κ F} (e₀ : W₀.toRepresentation.Equiv (matRep R)) :
    ∃ H : (κ → F) →+ U, (∀ g v, H (R g *ᵥ v) = ρ g (H v)) ∧ ∃ v, H v ≠ 0 := by
  classical
  let ι : (κ → F) →ₗ[F] (Fin n → F) := W₀.toSubmodule.subtype ∘ₗ e₀.symm.toLinearMap
  have hι : ∀ g v, ι (R g *ᵥ v) = PFrep ρ bas g *ᵥ ι v := by
    intro g v
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e₀.symm.toIntertwiningMap g v
    show ((e₀.symm (R g *ᵥ v) : W₀.toSubmodule) : Fin n → F) = _
    have h2 : R g *ᵥ v = matRep R g v := rfl
    rw [h2]
    have h3 : e₀.symm (matRep R g v) = W₀.toRepresentation g (e₀.symm v) := h1
    rw [h3]
    rfl
  have hιinj : Function.Injective ι := fun v w h => e₀.symm.injective (Subtype.ext h)
  let h : (κ → F) →+ (Fin n → ZMod 2) :=
    { toFun := fun v k => trZ f (ι v k)
      map_zero' := by
        funext k
        simp [trZ_zero hF]
      map_add' := fun v w => by
        funext k
        simp [trZ_add hF] }
  have hh : ∀ g v, h (R g *ᵥ v) = toMatRep ρ bas g *ᵥ h v := by
    intro g v
    funext k
    show trZ f (ι (R g *ᵥ v) k) = (toMatRep ρ bas g *ᵥ fun k => trZ f (ι v k)) k
    rw [hι]
    simp only [matMap_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [trZ_sum hF]
    exact Finset.sum_congr rfl fun l _ => trZ_cast_mul hF _ _
  let H : (κ → F) →+ U := bas.equivFun.symm.toAddEquiv.toAddMonoidHom.comp h
  refine ⟨H, fun g v => ?_, ?_⟩
  · show bas.equivFun.symm (h (R g *ᵥ v)) = ρ g (bas.equivFun.symm (h v))
    rw [hh]
    apply bas.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    have := Representation.IntertwiningMap.isIntertwining _ _
      (CFSG.QuasithinUnique.Setup.X7b.matRepEquiv ρ bas).toIntertwiningMap g
      (bas.equivFun.symm (h v))
    have e1 : (CFSG.QuasithinUnique.Setup.X7b.matRepEquiv ρ bas).toIntertwiningMap
        (bas.equivFun.symm (h v)) = h v := by
      show bas.equivFun (bas.equivFun.symm (h v)) = h v
      rw [LinearEquiv.apply_symm_apply]
    rw [e1] at this
    exact this.symm
  · obtain ⟨b, hb⟩ := trace_exists hF
    obtain ⟨k₀⟩ := (inferInstance : Nonempty κ)
    have hne : ι (Pi.single k₀ 1) ≠ 0 := by
      intro h0
      have := hιinj (h0.trans (map_zero ι).symm)
      have h1 := congrFun this k₀
      simp at h1
    obtain ⟨k, hk⟩ : ∃ k, ι (Pi.single k₀ 1) k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (funext hcon)
    refine ⟨(b / ι (Pi.single k₀ 1) k) • Pi.single k₀ 1, fun h0 => ?_⟩
    have h1 : h ((b / ι (Pi.single k₀ 1) k) • Pi.single k₀ 1) = 0 := by
      apply bas.equivFun.symm.injective
      rw [map_zero]
      exact h0
    have h2 := congrFun h1 k
    change trZ f (ι ((b / ι (Pi.single k₀ 1) k) • Pi.single k₀ 1) k) = 0 at h2
    rw [map_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ b hk] at h2
    apply hb
    rw [← cast_trZ hF, h2, map_zero]

omit [CharP F 2] [Fintype F] in
theorem traceHom_surjective {ρ : Representation (ZMod 2) SL(3, F) U} (hirr : ρ.IsIrreducible)
    {κ : Type} [Fintype κ] [DecidableEq κ] {R : SL(3, F) →* Matrix κ κ F} {H : (κ → F) →+ U}
    (hH : ∀ g v, H (R g *ᵥ v) = ρ g (H v)) (hH0 : ∃ v, H v ≠ 0) : Function.Surjective H := by
  let Rg : Submodule (ZMod 2) U :=
    { carrier := Set.range H
      add_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨v + w, map_add H v w⟩
      zero_mem' := ⟨0, map_zero H⟩
      smul_mem' := by
        rintro c _ ⟨v, rfl⟩
        fin_cases c
        · exact ⟨0, by rw [map_zero]; exact (zero_smul _ _).symm⟩
        · exact ⟨v, (one_smul _ _).symm⟩ }
  have hR : ∀ g, ∀ u ∈ Rg, ρ g u ∈ Rg := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨R g *ᵥ v, hH g v⟩
  rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 Rg hR with h0 | h1
  · exfalso
    obtain ⟨v, hv⟩ := hH0
    have : H v ∈ Rg := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact hv this
  · intro u
    have : u ∈ Rg := by rw [h1]; exact Submodule.mem_top
    exact this

theorem two_pow_le_card_of_stable {κ : Type} [Fintype κ] [DecidableEq κ]
    {R : SL(3, F) →* Matrix κ κ F} (hR : (matRep R).IsIrreducible) (K : AddSubgroup (κ → F))
    (hK : ∀ g, ∀ v ∈ K, R g *ᵥ v ∈ K) (hne : K ≠ ⊥) : 2 ^ Fintype.card κ ≤ Nat.card K := by
  classical
  set S := Submodule.span F (K : Set (κ → F)) with hS
  have hSinv : ∀ g, ∀ u ∈ S, matRep R g u ∈ S := by
    intro g u hu
    induction hu using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hK g x hx)
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact S.smul_mem c hx
  have hStop : S = ⊤ := by
    rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hR).2 S hSinv with h0 | h1
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ S := Submodule.subset_span hx
      rw [h0, Submodule.mem_bot] at this
      exact (AddSubgroup.mem_bot).mpr this
    · exact h1
  obtain ⟨b, hbK, hbspan, hbli⟩ := exists_linearIndependent F (K : Set (κ → F))
  have : Fintype b := Fintype.ofFinite b
  have hbcard : Fintype.card b = Fintype.card κ := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hbli, Subtype.range_coe, Set.finrank,
      hbspan, ← hS, hStop, finrank_top, Module.finrank_fintype_fun_eq_card]
  let φ : (b → ZMod 2) → (κ → F) := fun c =>
    ∑ i : b, (ZMod.castHom (dvd_refl 2) F (c i)) • (i : κ → F)
  have hφK : ∀ c, φ c ∈ K := fun c => AddSubgroup.sum_mem _ fun i _ => by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (c i) with h | h
    · rw [h, map_zero, zero_smul]
      exact K.zero_mem
    · rw [h, map_one, one_smul]
      exact hbK i.2
  have hcast : Function.Injective (ZMod.castHom (dvd_refl 2) F) := (ZMod.castHom _ F).injective
  have hφinj : Function.Injective φ := by
    intro c c' h
    have h1 : ∑ i : b, (ZMod.castHom (dvd_refl 2) F (c i) - ZMod.castHom (dvd_refl 2) F (c' i)) •
        (i : κ → F) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr h
    have h2 := Fintype.linearIndependent_iff.mp hbli _ h1
    funext i
    exact hcast (sub_eq_zero.mp (h2 i))
  have hle : Nat.card (b → ZMod 2) ≤ Nat.card K :=
    Nat.card_le_card_of_injective (fun c => (⟨φ c, hφK c⟩ : K)) fun c c' h =>
      hφinj (congrArg Subtype.val h)
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, hbcard] at hle
  exact hle

end CFSG.Quasithin.H13.Ch4.B414
