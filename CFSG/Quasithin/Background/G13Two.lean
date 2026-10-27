module

public import CFSG.Quasithin.Background.G13Core
public import CFSG.Quasithin.Background.G1HalfSum

public section

open Matrix CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F]

section Two

variable [CharP F 2]

omit [CharP F 2] in
theorem actSub_eq_of_lower_left_zero {k : SL(2, F)} (hk : k.1 1 0 = 0) :
    actSub k (Vi F 2 0) = Vi F 2 0 := by
  have hle : actSub k (Vi F 2 0) ≤ Vi F 2 0 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_actSub.1 hv
    rw [mem_Vi] at hw ⊢
    intro j hj
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    have h0 : w 1 = 0 := hw 1 (by decide)
    show ((k : Matrix (Fin 2) (Fin 2) F) *ᵥ w) 1 = 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hk, h0]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 := isPoint_actSub k (isPoint_Vi (F := F) (n := 2) 0)
  have h2 := isPoint_Vi (F := F) (n := 2) 0
  unfold IsPoint at h1 h2
  omega

omit [CharP F 2] in
theorem Vi_zero_ne_Vi_one : Vi F 2 0 ≠ Vi F 2 1 := by
  intro h
  have h1 : (Pi.single 0 1 : Fin 2 → F) ∈ Vi F 2 1 := by
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  have h2 := mem_Vi.1 h1 0 (by decide)
  simp at h2

theorem actSub_wmat_Vi_zero : actSub (wmat F) (Vi F 2 0) = Vi F 2 1 := by
  refine actSub_Vi_eq_of_smul (v := (Pi.single 1 1 : Fin 2 → F)) ?_ ?_
  · rw [wmat_smul]
    funext i
    fin_cases i <;> simp
  · intro w
    unfold Vi
    rw [Submodule.mem_span_singleton]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

omit [CharP F 2] in
theorem e12_mem_rootGroup (c : F) : e12 c ∈ rootGroup (Vi F 2 0) (Vhat F 2 1) := by
  have h := e12_mem_Rg (F := F) c
  rw [← Rij_zero_one_eq_Rg] at h
  exact h

variable {U : Type*} [AddCommGroup U] [DistribMulAction SL(2, F) U]

theorem G13Hyp.halves {φ : Submodule F (Fin 2 → F) → AddSubgroup U} (hφ : G13Hyp F 2 U φ) :
    G13Halves F (φ (Vi F 2 0)) where
  stab d y hy := by
    have hk : (dgm d : SL(2, F)).1 1 0 = 0 := by simp
    have h1 := hφ.equivariant (dgm d) (Vi F 2 0) (isPoint_Vi 0)
    rw [actSub_eq_of_lower_left_zero hk] at h1
    rw [h1]
    exact ⟨y, hy, rfl⟩
  fix c y hy :=
    hφ.le_fixU (Vi F 2 0) (Vhat F 2 1) (isFlag_Vi_Vhat zero_ne_one) (Vi F 2 0) (isPoint_Vi 0)
      (by rw [Vhat_one_eq]) hy (e12 c) (e12_mem_rootGroup c)
  comm c u :=
    hφ.commU_le (Vi F 2 0) (Vhat F 2 1) (isFlag_Vi_Vhat zero_ne_one)
      (AddSubgroup.subset_closure ⟨e12 c, e12_mem_rootGroup c, u, rfl⟩)
  disj z hz hwz := by
    have h1 := hφ.equivariant (wmat F) (Vi F 2 0) (isPoint_Vi 0)
    rw [actSub_wmat_Vi_zero] at h1
    have h2 : wmat F • z ∈ φ (Vi F 2 1) := by
      rw [h1]
      exact ⟨z, hz, rfl⟩
    have h3 := hφ.disjoint (Vi F 2 0) (Vi F 2 1) (isPoint_Vi 0) (isPoint_Vi 1) Vi_zero_ne_Vi_one
    have h4 : wmat F • z ∈ φ (Vi F 2 0) ⊓ φ (Vi F 2 1) := ⟨hwz, h2⟩
    rw [h3] at h4
    have h5 : wmat F • z = 0 := AddSubgroup.mem_bot.1 h4
    have h6 : wmat F • wmat F • z = wmat F • (0 : U) := by rw [h5]
    rwa [wmat_smul_smul, smul_zero] at h6
  sup u := by
    have h1 := hφ.equivariant (wmat F) (Vi F 2 0) (isPoint_Vi 0)
    rw [actSub_wmat_Vi_zero] at h1
    have h2 : (⊤ : AddSubgroup U) ≤ φ (Vi F 2 0) ⊔ φ (Vi F 2 1) := by
      rw [← iSup_phi_Vi_eq_top (le_refl 2) hφ]
      refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    have h3 := h2 (AddSubgroup.mem_top u)
    obtain ⟨y₁, hy₁, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 h3
    rw [h1] at hz
    obtain ⟨y₂, hy₂, rfl⟩ := hz
    exact ⟨y₁, hy₁, y₂, hy₂, rfl⟩

omit [CharP F 2] in
theorem exists_decomp_of_equiv {s : ℕ} (Θ : (Fin s → Fin 2 → F) ≃+ U)
    (hΘ : ∀ (k : SL(2, F)) (x : Fin s → Fin 2 → F), Θ (fun j => k • x j) = k • Θ x) :
    ∃ W : Fin s → AddSubgroup U, iSupIndep W ∧ ⨆ j, W j = ⊤ ∧ ∀ j,
      (∀ (g : SL(2, F)) (w : U), w ∈ W j → g • w ∈ W j) ∧
      ∃ f : (Fin 2 → F) →+ U, Function.Injective f ∧ f.range = W j ∧
        ∀ (g : SL(2, F)) (v : Fin 2 → F), f (g • v) = g • f v := by
  let ι : Fin s → ((Fin 2 → F) →+ U) := fun j =>
    Θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin s => Fin 2 → F) j)
  have hι : ∀ (j : Fin s) (v : Fin 2 → F), ι j v = Θ (Pi.single j v) := fun j v => rfl
  have hsingle : ∀ (g : SL(2, F)) (j : Fin s) (v : Fin 2 → F),
      (fun i => g • (Pi.single j v : Fin s → Fin 2 → F) i) = Pi.single j (g • v) := by
    intro g j v
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hequiv : ∀ (g : SL(2, F)) (j : Fin s) (v : Fin 2 → F), ι j (g • v) = g • ι j v := by
    intro g j v
    rw [hι, hι, ← hΘ g, hsingle]
  refine ⟨fun j => (ι j).range, ?_, ?_, fun j => ⟨?_, ι j, ?_, rfl, fun g v => hequiv g j v⟩⟩
  · intro i
    rw [AddSubgroup.disjoint_def]
    intro u hu hu'
    obtain ⟨v, rfl⟩ := hu
    have hQ : (⨆ (j) (_ : j ≠ i), (ι j).range) ≤
        (Pi.evalAddMonoidHom (fun _ : Fin s => Fin 2 → F) i).ker.map Θ.toAddMonoidHom := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v', rfl⟩
      refine ⟨Pi.single j v', ?_, rfl⟩
      simp [Pi.single_eq_of_ne (Ne.symm hj)]
    obtain ⟨x, hx, hxv⟩ := hQ hu'
    have hx' : x = Pi.single i v := Θ.injective hxv
    have hxi : x i = 0 := hx
    rw [hx'] at hxi
    simp only [Pi.single_eq_same] at hxi
    rw [hι, hxi]
    simp
  · rw [eq_top_iff]
    intro u _
    obtain ⟨x, rfl⟩ := Θ.surjective u
    have hsum : x = ∑ j : Fin s, Pi.single j (x j) := (Finset.univ_sum_single x).symm
    rw [hsum, map_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    exact AddSubgroup.mem_iSup_of_mem j ⟨x j, rfl⟩
  · rintro g w ⟨v, rfl⟩
    exact ⟨g • v, hequiv g j v⟩
  · intro v v' hvv
    exact Pi.single_injective j (Θ.injective hvv)

end Two

theorem theorem_G_1_3_two [Finite F] [CharP F 2] : Theorem_G_1_3 F 2 (le_refl 2) := by
  intro U _ _ _ hsq φ hφ
  obtain ⟨s, Θ, hΘ, hcard, -⟩ := exists_equiv_of_halves_core hsq hφ.halves
  exact ⟨s, hcard, exists_decomp_of_equiv Θ hΘ⟩

end CFSG.Quasithin.G1
