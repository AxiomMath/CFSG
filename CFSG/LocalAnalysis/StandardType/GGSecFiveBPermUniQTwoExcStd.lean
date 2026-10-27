module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.Mathlib.GroupTheory.ConjCentralizer
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem mem_normalizer_of_isComponentOf_of_not_isCyclic {G : Type} [Group G] [Finite G] {p : ℕ}
    {M E : Subgroup G} {a z : G}
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({a} : Set G)))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (M : Set G) → IsPGroup p S → IsCyclic S)
    (hEM : E ≤ M) (hEp : IsPGroup p E) (hEc : ¬ IsCyclic E)
    (hza : z ∈ Subgroup.centralizer ({a} : Set G)) (hzE : ∀ e ∈ E, z * e = e * z) :
    z ∈ Subgroup.normalizer (M : Set G) := by
  have hza' : z * a * z⁻¹ = a := by
    have h := Subgroup.mem_centralizer_iff.mp hza a (Set.mem_singleton a)
    rw [show z * a = a * z from h.symm, mul_inv_cancel_right]
  have hC : (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj z).toMonoidHom =
      Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.map_conj_centralizer_singleton, hza']
  have hM' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hM z
  rw [hC] at hM'
  have hEz : E ≤ M.map (MulAut.conj z).toMonoidHom := by
    intro e he
    refine ⟨e, hEM he, ?_⟩
    change z * e * z⁻¹ = e
    rw [hzE e he, mul_inv_cancel_right]
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hM hM' with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
  · exfalso
    apply hEc
    refine hcyc E (fun e he => ?_) hEp
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hmC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hm
    exact (Subgroup.mem_centralizer_iff.mp hmC e (hEz he)).symm

theorem largeEvenSStar_map_conj_of_mem_normalizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L : Subgroup G} (hS : LargeEvenSStar p B x L) {t : G}
    (ht : t ∈ Subgroup.normalizer (B : Set G)) :
    LargeEvenSStar p B (t * x * t⁻¹) (L.map (MulAut.conj t).toMonoidHom) := by
  have h := shapeConj_largeEvenSStar_map_conj hS t
  have hB : B.map (MulAut.conj t).toMonoidHom = B := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  simpa only [hB] using h

theorem sgnAut_mem_bSignedFull {n p : ℕ} (i : Fin n) : SpCoord.sgnAut i ∈ bSignedFull n p :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

theorem exists_ggConjAut_eq_of_mem_bSignedFull {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)} {n p : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {σ : MulAut (Fin n → Multiplicative (ZMod p))} (hσ : σ ∈ bSignedFull n p) :
    ∃ t : G, ∃ ht : t ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs ht) = σ ∧ ∀ b : ↥Bs, eta (ggConjAut Bs ht b) = σ (eta b) := by
  rw [← hJoin] at hσ
  obtain ⟨φ, hφ, rfl⟩ := hσ
  have hφT : φ ∈ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top) hφ
  obtain ⟨t, -, ht, hφt⟩ := mem_ggAutomizer_iff.mp hφT
  have hφ' : φ = ggConjAut Bs ht := MulEquiv.ext fun b => Subtype.ext (hφt b)
  subst hφ'
  refine ⟨t, ht, rfl, fun b => ?_⟩
  change eta (ggConjAut Bs ht b) = eta (ggConjAut Bs ht (eta.symm (eta b)))
  rw [MulEquiv.symm_apply_apply]

end CFSG.StandardType

end
