module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.Sp62S6Over

public section

namespace CFSG.Quasithin.H13.U3

namespace S6Out

open Equiv

@[expose] def syn (a b c d e f : Fin 6) : Perm (Fin 6) := swap a b * swap c d * swap e f

@[expose] def tot : Fin 6 → Finset (Perm (Fin 6)) := ![
  {syn 0 1 2 4 3 5, syn 0 2 1 5 3 4, syn 0 3 1 2 4 5, syn 0 4 1 3 2 5, syn 0 5 1 4 2 3},
  {syn 0 1 2 5 3 4, syn 0 2 1 4 3 5, syn 0 3 1 2 4 5, syn 0 4 1 5 2 3, syn 0 5 1 3 2 4},
  {syn 0 1 2 4 3 5, syn 0 2 1 3 4 5, syn 0 3 1 4 2 5, syn 0 4 1 5 2 3, syn 0 5 1 2 3 4},
  {syn 0 1 2 5 3 4, syn 0 2 1 3 4 5, syn 0 3 1 5 2 4, syn 0 4 1 2 3 5, syn 0 5 1 4 2 3},
  {syn 0 1 2 3 4 5, syn 0 2 1 5 3 4, syn 0 3 1 4 2 5, syn 0 4 1 2 3 5, syn 0 5 1 3 2 4},
  {syn 0 1 2 3 4 5, syn 0 2 1 4 3 5, syn 0 3 1 5 2 4, syn 0 4 1 3 2 5, syn 0 5 1 2 3 4}]

@[expose] def cs (σ : Perm (Fin 6)) (S : Finset (Perm (Fin 6))) : Finset (Perm (Fin 6)) :=
  S.image fun p => σ * p * σ⁻¹

theorem tot_injective : ∀ i j : Fin 6, tot i = tot j → i = j := by
  decide +kernel

theorem cs_swap : cs (swap 0 1) (tot 0) = tot 2 ∧ cs (swap 0 1) (tot 1) = tot 3 ∧
    cs (swap 0 1) (tot 2) = tot 0 ∧ cs (swap 0 1) (tot 3) = tot 1 ∧
    cs (swap 0 1) (tot 4) = tot 5 ∧ cs (swap 0 1) (tot 5) = tot 4 := by
  decide +kernel

theorem cs_finRotate : cs (finRotate 6) (tot 0) = tot 3 ∧ cs (finRotate 6) (tot 1) = tot 0 ∧
    cs (finRotate 6) (tot 2) = tot 4 ∧ cs (finRotate 6) (tot 3) = tot 1 ∧
    cs (finRotate 6) (tot 4) = tot 2 ∧ cs (finRotate 6) (tot 5) = tot 5 := by
  decide +kernel

theorem cs_mul (σ τ : Perm (Fin 6)) (S : Finset (Perm (Fin 6))) :
    cs (σ * τ) S = cs σ (cs τ S) := by
  simp only [cs, Finset.image_image]
  congr 1

theorem cs_one (S : Finset (Perm (Fin 6))) : cs 1 S = S := by
  simp [cs]

theorem cs_injective (σ : Perm (Fin 6)) : Function.Injective (cs σ) := by
  intro S S' h
  have := congrArg (cs σ⁻¹) h
  rwa [← cs_mul, ← cs_mul, inv_mul_cancel, cs_one, cs_one] at this

@[expose] def presSub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | ∀ i, ∃ j, cs σ (tot i) = tot j}
  one_mem' := fun i => ⟨i, cs_one _⟩
  mul_mem' := fun {σ τ} hσ hτ i => by
    obtain ⟨j, hj⟩ := hτ i
    obtain ⟨k, hk⟩ := hσ j
    exact ⟨k, by rw [cs_mul, hj, hk]⟩
  inv_mem' := fun {σ} hσ i => by
    choose f hf using hσ
    have hinj : Function.Injective f := fun a b hab =>
      tot_injective a b (cs_injective σ (by rw [hf, hf, hab]))
    obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 hinj) i
    refine ⟨j, ?_⟩
    rw [← hj, ← hf, ← cs_mul, inv_mul_cancel, cs_one]

theorem presSub_eq_top : presSub = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 4))
    support_finRotate (0 : Fin 6)
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  rintro σ (rfl | rfl)
  · intro i
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cs_finRotate
    fin_cases i
    exacts [⟨3, h0⟩, ⟨0, h1⟩, ⟨4, h2⟩, ⟨1, h3⟩, ⟨2, h4⟩, ⟨5, h5⟩]
  · intro i
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := cs_swap
    have e : swap (0 : Fin 6) (finRotate (4 + 2) 0) = swap 0 1 := rfl
    rw [e]
    fin_cases i
    exacts [⟨2, h0⟩, ⟨3, h1⟩, ⟨0, h2⟩, ⟨1, h3⟩, ⟨5, h4⟩, ⟨4, h5⟩]

theorem pres (σ : Perm (Fin 6)) (i : Fin 6) : ∃ j, cs σ (tot i) = tot j := by
  have : σ ∈ presSub := presSub_eq_top ▸ Subgroup.mem_top σ
  exact this i

@[expose] def phiF (σ : Perm (Fin 6)) (i : Fin 6) : Fin 6 :=
  ((List.finRange 6).find? fun j => decide (cs σ (tot i) = tot j)).getD i

theorem phiF_spec (σ : Perm (Fin 6)) (i : Fin 6) : cs σ (tot i) = tot (phiF σ i) := by
  obtain ⟨j, hj⟩ := pres σ i
  have hsome : ((List.finRange 6).find? fun j => decide (cs σ (tot i) = tot j)).isSome := by
    rw [List.find?_isSome]
    exact ⟨j, List.mem_finRange j, by simp [hj]⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hsome
  have := List.find?_some hk
  simp only [phiF, hk, Option.getD_some]
  simpa using this

theorem phiF_one (i : Fin 6) : phiF 1 i = i :=
  tot_injective _ _ (by rw [← phiF_spec, cs_one])

theorem phiF_mul (σ τ : Perm (Fin 6)) (i : Fin 6) : phiF (σ * τ) i = phiF σ (phiF τ i) :=
  tot_injective _ _ (by rw [← phiF_spec, cs_mul, phiF_spec, phiF_spec])

@[expose] def phi : Perm (Fin 6) →* Perm (Fin 6) where
  toFun σ :=
    { toFun := phiF σ
      invFun := phiF σ⁻¹
      left_inv := fun i => by rw [← phiF_mul, inv_mul_cancel, phiF_one]
      right_inv := fun i => by rw [← phiF_mul, mul_inv_cancel, phiF_one] }
  map_one' := Equiv.ext phiF_one
  map_mul' σ τ := Equiv.ext (phiF_mul σ τ)

@[expose] def cc : Perm (Fin 6) := swap 0 3 * swap 0 1 * swap 0 2 * swap 4 5

theorem phi_phi_gens : phi (phi (swap 0 1)) = cc * swap 0 1 * cc⁻¹ ∧
    phi (phi (finRotate 6)) = cc * finRotate 6 * cc⁻¹ := by
  decide +kernel

theorem closure_gens : Subgroup.closure {finRotate 6, swap (0 : Fin 6) 1} = ⊤ :=
  Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 4)) support_finRotate 0

theorem phi_phi (σ : Perm (Fin 6)) : phi (phi σ) = cc * σ * cc⁻¹ := by
  have h : phi.comp phi = (MulAut.conj cc).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_gens ?_
    rintro g (rfl | rfl)
    · exact phi_phi_gens.2
    · exact phi_phi_gens.1
  exact DFunLike.congr_fun h σ

@[expose] noncomputable def phiEquiv : Perm (Fin 6) ≃* Perm (Fin 6) :=
  MulEquiv.ofBijective phi ⟨fun a b hab => by
      have := congrArg phi hab
      rw [phi_phi, phi_phi] at this
      simpa using this,
    fun y => ⟨phi (cc⁻¹ * y * cc), by rw [phi_phi]; group⟩⟩

theorem phi_inv_eq (τ : Perm (Fin 6)) : phiEquiv.symm τ = phi (cc⁻¹ * τ * cc) := by
  rw [MulEquiv.symm_apply_eq]
  show τ = phi (phi (cc⁻¹ * τ * cc))
  rw [phi_phi]
  group

theorem sign_phi_gens : Perm.sign (phi (swap 0 1)) = Perm.sign (swap (0 : Fin 6) 1) ∧
    Perm.sign (phi (finRotate 6)) = Perm.sign (finRotate 6) := by
  decide +kernel

theorem sign_phi (σ : Perm (Fin 6)) : Perm.sign (phi σ) = Perm.sign σ := by
  have h : Perm.sign.comp phi = Perm.sign := by
    refine MonoidHom.eq_of_eqOn_dense closure_gens ?_
    rintro g (rfl | rfl)
    · exact sign_phi_gens.2
    · exact sign_phi_gens.1
  have := DFunLike.congr_fun h σ
  rwa [MonoidHom.comp_apply] at this

theorem phi_mem_alternatingGroup {σ : Perm (Fin 6)} (h : σ ∈ alternatingGroup (Fin 6)) :
    phi σ ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, sign_phi]
  exact h

theorem phi_P1 : ∀ σ : Perm (Fin 6), A6.InP1 σ → A6.InP2 (phi σ) := by
  decide +kernel

theorem phi_inv_D6 : ∀ σ : Perm (Fin 6), A6.InD6 σ → A6.InP1 (phi (cc⁻¹ * σ * cc)) := by
  decide +kernel

end S6Out

end CFSG.Quasithin.H13.U3
