module

public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame
import CFSG.LocalAnalysis.StandardType.GGB48OmReduce

public section

namespace CFSG.StandardType


theorem bstar_split_of_torus_action {U V G : Type} [Group U] [Group V] [Group G]
    {Bs X : Subgroup G} (hBs : IsMulCommutative Bs) (ψ : U →* G) (hrange : ψ.range = X)
    (T : V →* U) (v : Bs →* V)
    (hact : ∀ (b : Bs) (u : U), (b : G)⁻¹ * ψ u * (b : G) =
      ψ (T (v b) * u * (T (v b))⁻¹)) (hT : T.range.map ψ ≤ Bs ⊓ X) :
    ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ X, g⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  let : IsMulCommutative Bs := hBs
  intro b hb
  let t := ψ (T (v ⟨b, hb⟩))
  have ht : t ∈ Bs ⊓ X := hT (Subgroup.mem_map_of_mem ψ (MonoidHom.mem_range.mpr ⟨v ⟨b, hb⟩, rfl⟩))
  have hbt : b * t = t * b := congrArg Subtype.val
    (IsMulCommutative.is_comm.comm (⟨b, hb⟩ : Bs) (⟨t, ht.1⟩ : Bs))
  refine ⟨t⁻¹, Subgroup.inv_mem _ ht, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ hy)
  have ha := hact ⟨b, hb⟩ u
  rw [map_mul, map_mul, map_inv] at ha
  change b⁻¹ * ψ u * b = t * ψ u * t⁻¹ at ha
  simp only [inv_inv]
  rw [← hbt]
  calc
    ψ u * (b * t) = b * (b⁻¹ * ψ u * b) * t := by group
    _ = b * (t * ψ u * t⁻¹) * t := by rw [ha]
    _ = (b * t) * ψ u := by group

theorem conj_eq_self_iff_of_innerAction {U G : Type} [Group U] [Group G]
    (ψ : U →* G) (hψ : Function.Injective ψ) {b : G} {u n : U}
    (ha : b⁻¹ * ψ n * b = ψ (u * n * u⁻¹)) :
    ψ n * b * (ψ n)⁻¹ = b ↔ n * u * n⁻¹ = u := by
  constructor
  · intro h
    have hb : b⁻¹ * ψ n * b = ψ n := by
      calc
        b⁻¹ * ψ n * b = b⁻¹ * (ψ n * b * (ψ n)⁻¹) * ψ n := by group
        _ = ψ n := by rw [h]; group
    have hu : u * n * u⁻¹ = n := hψ (ha.symm.trans hb)
    have hcomm : u * n = n * u := by
      calc
        u * n = (u * n * u⁻¹) * u := by group
        _ = n * u := by rw [hu]
    rw [← hcomm]
    group
  · intro h
    have hcomm : n * u = u * n := by
      calc
        n * u = (n * u * n⁻¹) * n := by group
        _ = u * n := by rw [h]
    have hu : u * n * u⁻¹ = n := by rw [← hcomm]; group
    have hb : b⁻¹ * ψ n * b = ψ n := by rw [ha, hu]
    calc
      ψ n * b * (ψ n)⁻¹ = b * (b⁻¹ * ψ n * b) * (ψ n)⁻¹ := by group
      _ = b := by rw [hb]; group

theorem exists_markedWeyl_bstar_of_split {N : ℕ} {M : CoxeterMatrix (Fin N)}
    {U G : Type} [Group U] [Group G] (E : Subgroup U) (Bs X : Subgroup G)
    (ψ : U →* G) (hψ : Function.Injective ψ) (hrange : ψ.range = X)
    (hE : E.map ψ = Bs ⊓ X)
    (hsplit : ∀ b ∈ Bs, ∃ g ∈ Bs ⊓ X, g⁻¹ * b ∈ Subgroup.centralizer (X : Set G))
    (ν : M.Group →* U)
    (εN : M.Group ≃* ↥(ggAutomizer (⊤ : Subgroup U) E))
    (hεN : ∀ (w : M.Group) (a : E), ((εN w : MulAut ↥E) a : U) =
      ν w * (a : U) * (ν w)⁻¹) :
    ∃ ε : M.Group ≃* ↥(ggAutomizer X Bs),
      ∀ (w : M.Group) (b : Bs), ((ε w : MulAut ↥Bs) b : G) =
        ψ (ν w) * (b : G) * (ψ (ν w))⁻¹ := by
  subst X
  have hconj (w : M.Group) (a : U) (ha : a ∈ E) : ν w * a * (ν w)⁻¹ ∈ E := by
    rw [← hεN w ⟨a, ha⟩]
    exact ((εN w : MulAut ↥E) ⟨a, ha⟩).2
  have hnE (w : M.Group) : ν w ∈ Subgroup.normalizer (E : Set U) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact hconj w a
    · intro ha
      have h := hconj w⁻¹ (ν w * a * (ν w)⁻¹) ha
      have he : ν w⁻¹ * (ν w * a * (ν w)⁻¹) * (ν w⁻¹)⁻¹ = a := by
        rw [map_inv]
        group
      exact he ▸ h
  have hεs (i : Fin N) : (εN (M.simple i) : MulAut ↥E) =
      ggConjAut E (hnE (M.simple i)) := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [ggConjAut_apply]
    exact hεN (M.simple i) a
  obtain ⟨hnT, εT, hεT⟩ := markedWeyl_map E ψ hψ hE (fun i => ν (M.simple i))
    (fun i => hnE (M.simple i)) εN hεs
  have hnBs (i : Fin N) : ψ (ν (M.simple i)) ∈ Subgroup.normalizer (Bs : Set G) :=
    B48Om.mem_normalizer_of_split hsplit (MonoidHom.mem_range.mpr ⟨ν (M.simple i), rfl⟩) (hnT i)
  let r := B48Om.ggAutomizer_restrictEquiv_of_split hsplit
  let ε := εT.trans r.symm
  let α (i : Fin N) : ggAutomizer ψ.range Bs :=
    ⟨ggConjAut Bs (hnBs i), ggConjAut_mem_ggAutomizer
      (MonoidHom.mem_range.mpr ⟨ν (M.simple i), rfl⟩) (hnBs i)⟩
  have hrα (i : Fin N) : r (α i) = εT (M.simple i) := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [B48Om.ggAutomizer_restrictEquiv_of_split_apply_coe]
    change (ggConjAut Bs (hnBs i) (Subgroup.inclusion inf_le_left a) : G) =
      ((εT (M.simple i) : MulAut ↥(Bs ⊓ ψ.range)) a : G)
    rw [hεT i, ggConjAut_apply, ggConjAut_apply]
    rfl
  have hεsBs (i : Fin N) : (ε (M.simple i) : MulAut ↥Bs) = ggConjAut Bs (hnBs i) := by
    have he : ε (M.simple i) = α i := r.injective (by
      change r (r.symm (εT (M.simple i))) = r (α i)
      rw [r.apply_symm_apply, hrα i])
    exact congrArg Subtype.val he
  refine ⟨ε, ?_⟩
  exact markedWeyl_apply Bs (ψ.comp ν) ε hnBs hεsBs

end CFSG.StandardType
