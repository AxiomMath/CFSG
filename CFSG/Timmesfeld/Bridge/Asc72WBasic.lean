module

public import CFSG.Timmesfeld.Bridge.Asc72WreathL2
public import CFSG.Timmesfeld.Bridge.Asc72WreathStruct

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open Equiv

namespace WreathData

variable {G : Type} [Group G] {D : Set G} {M : Subgroup G} (W : WreathData G D M)

theorem S_ne_bot (i : Fin W.r) : W.S i ≠ ⊥ := (Subgroup.isSimpleGroup_iff.mp (W.simple i)).1

theorem S_injective : Function.Injective W.S :=
  WreathStruct.injective_of_ne_bot W.e_single W.S_ne_bot

private theorem mulSingle_conj (y : (j : Fin W.r) → W.S j) (i : Fin W.r) (x : W.S i) :
    y * Pi.mulSingle i x * y⁻¹ = Pi.mulSingle i (y i * x * (y i)⁻¹) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Pi.mulSingle_eq_of_ne hj]

theorem conj_mem_of_mem {m x : G} (hm : m ∈ M) {i : Fin W.r} (hx : x ∈ W.S i) :
    m * x * m⁻¹ ∈ W.S i := by
  obtain ⟨y, hy⟩ := W.e.surjective ⟨m, hm⟩
  have h := congrArg (fun z => ((W.e z : M) : G)) (W.mulSingle_conj y i ⟨x, hx⟩)
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hy, W.e_mulSingle] at h
  rw [h]
  exact (y i * ⟨x, hx⟩ * (y i)⁻¹).2

theorem π_apply_of_mem {m : G} (hm : m ∈ M) (i : Fin W.r) : W.π m i = i := by
  apply W.S_injective
  rw [← W.conj m i]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact W.conj_mem_of_mem hm hx
  · intro x hx
    refine ⟨m⁻¹ * x * m, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa using W.conj_mem_of_mem (M.inv_mem hm) hx

theorem π_eq_one_of_mem {m : G} (hm : m ∈ M) : W.π m = 1 :=
  Equiv.ext fun i => W.π_apply_of_mem hm i

theorem π_surjective (hS : Setup G D) : Function.Surjective W.π := by
  classical
  have hsw : ∀ σ ∈ W.π '' D, σ.IsSwap := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨i, j, hij, hπ, -⟩ := W.swap u hu
    exact ⟨i, j, hij, hπ⟩
  have hrange : Subgroup.closure (W.π '' D) = W.π.range := by
    rw [← MonoidHom.map_closure, hS.gen, ← MonoidHom.range_eq_map]
  intro σ
  have hσ : σ ∈ Subgroup.closure (W.π '' D) := by
    rw [mem_closure_isSwap hsw]
    refine ⟨Set.toFinite _, fun x => ?_⟩
    obtain ⟨g, hg⟩ := W.transitive x (σ x)
    exact ⟨⟨W.π g, hrange ▸ ⟨g, rfl⟩⟩, hg⟩
  rw [hrange] at hσ
  exact hσ

theorem exists_mem_swap (hS : Setup G D) {i j : Fin W.r} (hij : i ≠ j) :
    ∃ u ∈ D, W.π u = Equiv.swap i j := by
  obtain ⟨d, hd⟩ := hS.nonempty
  obtain ⟨a, b, hab, hπd, -⟩ := W.swap d hd
  obtain ⟨σ, hσ⟩ := isConj_iff.mp (Perm.isConj_swap hab hij)
  obtain ⟨g, rfl⟩ := W.π_surjective hS σ
  exact ⟨g * d * g⁻¹, hS.conj_mem g hd, by rw [map_mul, map_mul, map_inv, hπd, hσ]⟩

@[expose] def InnerOn (i : Fin W.r) (g : G) : Prop :=
  ∃ m ∈ W.S i, ∀ x ∈ W.S i, g * x * g⁻¹ = m * x * m⁻¹

theorem innerOn_of_commute {i : Fin W.r} {g : G} (h : ∀ x ∈ W.S i, Commute g x) :
    W.InnerOn i g :=
  ⟨1, (W.S i).one_mem, fun x hx => by rw [(h x hx).eq, mul_inv_cancel_right]; group⟩

variable {W} in
theorem InnerOn.mul {i : Fin W.r} {g g' : G} (hg : W.InnerOn i g) (hg' : W.InnerOn i g') :
    W.InnerOn i (g * g') := by
  obtain ⟨m, hm, h⟩ := hg
  obtain ⟨m', hm', h'⟩ := hg'
  refine ⟨m * m', (W.S i).mul_mem hm hm', fun x hx => ?_⟩
  have e1 : g * g' * x * (g * g')⁻¹ = g * (g' * x * g'⁻¹) * g⁻¹ := by group
  rw [e1, h' x hx]
  have e2 : g * (m' * x * m'⁻¹) * g⁻¹ =
      (g * m' * g⁻¹) * (g * x * g⁻¹) * (g * m' * g⁻¹)⁻¹ := by group
  rw [e2, h m' hm', h x hx]
  group

@[expose] def restr (i : Fin W.r) (g : G) (hg : W.π g i = i) : MulAut (W.S i) :=
  ((MulAut.conj g).subgroupMap (W.S i)).trans (MulEquiv.subgroupCongr
    ((show (W.S i).map (MulAut.conj g : G →* G) = (W.S i).map (MulAut.conj g).toMonoidHom
      from rfl).trans ((W.conj g i).trans (by rw [hg]))))

theorem restr_apply (i : Fin W.r) (g : G) (hg : W.π g i = i) (x : W.S i) :
    ((W.restr i g hg x : W.S i) : G) = g * x * g⁻¹ := rfl

end WreathData

end CFSG.Timmesfeld.Bridge.Asc72
