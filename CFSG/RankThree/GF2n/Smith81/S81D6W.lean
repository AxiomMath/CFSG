module

public import CFSG.RankThree.GF2n.Smith81.S81E7Form
public import CFSG.RankThree.GF2n.Smith81.S81E7Lam

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

abbrev Idx0 : Type := ↥idx0

abbrev W (K : Type) [Field K] : Type := Idx0 →₀ K

variable {K : Type} [Field K]

@[expose] def emb (K : Type) [Field K] : W K →ₗ[K] V K :=
  Finsupp.lmapDomain K K (Subtype.val : Idx0 → Fin e7Data.d)

theorem emb_injective : Function.Injective (emb K) := fun w w' h =>
  Finsupp.mapDomain_injective Subtype.val_injective h

theorem emb_apply_coe (w : W K) (a : Idx0) : emb K w (a : Fin e7Data.d) = w a :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective w a

theorem emb_apply_of_not_mem (w : W K) {b : Fin e7Data.d} (hb : b ∉ idx0) : emb K w b = 0 :=
  Finsupp.mapDomain_of_notMem_range w b (by rintro ⟨a, rfl⟩; exact hb a.2)

theorem emb_single (a : Idx0) (c : K) :
    emb K (Finsupp.single a c) = Finsupp.single (a : Fin e7Data.d) c :=
  Finsupp.mapDomain_single

theorem emb_mem_V0 (w : W K) : emb K w ∈ V0 K :=
  mem_V0.2 fun _ hb => emb_apply_of_not_mem w hb

theorem exists_emb_eq {v : V K} (hv : v ∈ V0 K) : ∃ w : W K, emb K w = v := by
  refine ⟨Finsupp.equivFunOnFinite.symm fun a : Idx0 => v (a : Fin e7Data.d), ?_⟩
  ext b
  by_cases hb : b ∈ idx0
  · have := emb_apply_coe (Finsupp.equivFunOnFinite.symm fun a : Idx0 => v (a : Fin e7Data.d))
      ⟨b, hb⟩
    simpa using this
  · rw [emb_apply_of_not_mem _ hb, (mem_V0.1 hv) b hb]

@[expose] def Induces (g : (Module.End K (W K))ˣ) (l : (Module.End K (V K))ˣ) : Prop :=
  ∀ w : W K, emb K ((g : Module.End K (W K)) w) = (l : Module.End K (V K)) (emb K w)

theorem Induces.mul {g g' : (Module.End K (W K))ˣ} {l l' : (Module.End K (V K))ˣ}
    (h : Induces g l) (h' : Induces g' l') : Induces (g * g') (l * l') := fun w => by
  simp only [Units.val_mul, Module.End.mul_apply]
  rw [h, h']

theorem induces_one : Induces (1 : (Module.End K (W K))ˣ) 1 := fun w => by simp

theorem Induces.inv {g : (Module.End K (W K))ˣ} {l : (Module.End K (V K))ˣ} (h : Induces g l) :
    Induces g⁻¹ l⁻¹ := fun w => by
  have h1 := h (((g⁻¹ : (Module.End K (W K))ˣ) : Module.End K (W K)) w)
  have h2 : (g : Module.End K (W K)) (((g⁻¹ : (Module.End K (W K))ˣ) : Module.End K (W K)) w) = w := by
    simp [← Module.End.mul_apply, ← Units.val_mul]
  rw [h2] at h1
  rw [h1]
  simp [← Module.End.mul_apply, ← Units.val_mul]

theorem Induces.unique {g g' : (Module.End K (W K))ˣ} {l : (Module.End K (V K))ˣ}
    (h : Induces g l) (h' : Induces g' l) : g = g' := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  exact emb_injective ((h w).trans (h' w).symm)

@[expose] def inducedSubgroup (H : Subgroup (Module.End K (V K))ˣ) :
    Subgroup (Module.End K (W K))ˣ where
  carrier := {g | ∃ l ∈ H, Induces g l}
  mul_mem' := by
    rintro g g' ⟨l, hl, h⟩ ⟨l', hl', h'⟩
    exact ⟨l * l', mul_mem hl hl', h.mul h'⟩
  one_mem' := ⟨1, one_mem H, induces_one⟩
  inv_mem' := by
    rintro g ⟨l, hl, h⟩
    exact ⟨l⁻¹, inv_mem hl, h.inv⟩

abbrev LamW (K : Type) [Field K] : Subgroup (Module.End K (W K))ˣ := inducedSubgroup (Lam K)

@[expose] def IsRootEltW (x : (Module.End K (W K))ˣ) : Prop :=
  ∃ l ∈ Lam K, ∃ β ∈ Perp, ∃ c : K, c ≠ 0 ∧ Induces x (l * e7Data_valid.xu K β c * l⁻¹)

@[expose] def betaW (x y : W K) : K := beta (emb K x) (emb K y)

@[expose] def vAut0 (K : Type) [Field K] : (Module.End K (W K))ˣ ≃* (W K ≃ₗ[K] W K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (W K)

theorem vAut0_apply (g : (Module.End K (W K))ˣ) (x : W K) :
    vAut0 K g x = (g : Module.End K (W K)) x := rfl

@[expose] def EAut0 (K : Type) [Field K] : Subgroup (W K ≃ₗ[K] W K) :=
  (LamW K).map (vAut0 K).toMonoidHom

@[expose] def a0 : Idx0 :=
  ⟨⟨8, by decide⟩, mem_idx0.2 (by unfold pr; decide +kernel)⟩

@[expose] def p0 (K : Type) [Field K] : W K := Finsupp.single a0 1

@[expose] def rootSet0 (K : Type) [Field K] : Set (W K ≃ₗ[K] W K) :=
  {g | ∃ γ ∈ Perp, pr (a0 : Fin e7Data.d) γ = 1 ∧ ∃ c : K, ∀ w : W K,
    emb K (g w) = (e7Data_valid.xu K γ c : Module.End K (V K)) (emb K w)}

@[expose] def rootRad0 (K : Type) [Field K] : Subgroup (W K ≃ₗ[K] W K) :=
  Subgroup.closure (rootSet0 K)

end CFSG.RankThree.GF2n.Smith81.D6Spin
