module

public import CFSG.Quasithin.AppendixH.H9.ConjTransport
public import CFSG.Quasithin.Background.FixVZPowers
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {V : Type*} [CommGroup V]

theorem isSymNatural_conjAut (g : MulAut V) {X : Subgroup (MulAut V)} {W : Subgroup V} {n : ℕ}
    (h : G6.IsSymNatural X W n) :
    G6.IsSymNatural (conjAut g X) (W.map (g : MulAut V).toMonoidHom) n := by
  obtain ⟨θ, β, hβ, hrange, hker⟩ := h
  let φ : ↥X ≃* ↥(conjAut g X) :=
    Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hφ : ∀ x : ↥X, ((φ x : ↥(conjAut g X)) : MulAut V) = g * (x : MulAut V) * g⁻¹ :=
    fun x => (Subgroup.coe_equivMapOfInjective_apply X _ _ x).trans (MulAut.conj_apply g _)
  refine ⟨φ.symm.trans θ, (g : MulAut V).toMonoidHom.comp β, ?_, ?_, ?_⟩
  · intro y u
    have hy : ((y : ↥(conjAut g X)) : MulAut V) = g * ((φ.symm y : ↥X) : MulAut V) * g⁻¹ := by
      rw [← hφ, MulEquiv.apply_symm_apply]
    have h1 := hβ (φ.symm y) u
    simp only [MonoidHom.comp_apply, MulEquiv.coe_trans, Function.comp_apply]
    rw [h1, hy]
    simp [MulAut.mul_apply]
  · rw [MonoidHom.range_comp, hrange]
  · rw [MonoidHom.ker_comp_of_injective _ _ (g : MulAut V).injective, hker]

theorem conjAut_eq_self_of_conj_mem {L : Subgroup (MulAut V)} {g : MulAut V}
    (h : ∀ l ∈ L, g * l * g⁻¹ ∈ L) (h' : ∀ l ∈ L, g⁻¹ * l * g ∈ L) : conjAut g L = L := by
  ext x
  rw [mem_conjAut]
  refine ⟨fun hx => ?_, fun hx => h' x hx⟩
  have h2 := h _ hx
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h2

theorem centralizer_conj_singleton (g s : MulAut V) :
    Subgroup.centralizer ({g * s * g⁻¹} : Set (MulAut V)) =
      conjAut g (Subgroup.centralizer ({s} : Set (MulAut V))) := by
  ext x
  rw [mem_conjAut, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc s * (g⁻¹ * x * g) = g⁻¹ * (g * s * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * s * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * x * g * s := by group
  · intro h
    calc g * s * g⁻¹ * x = g * (s * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g * s) * g⁻¹ := by rw [h]
      _ = x * (g * s * g⁻¹) := by group

theorem inf_centralizer_conj_singleton {L : Subgroup (MulAut V)} (g s : MulAut V)
    (hL : conjAut g L = L) :
    L ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set (MulAut V)) =
      conjAut g (L ⊓ Subgroup.centralizer ({s} : Set (MulAut V))) := by
  rw [conjAut_inf, hL, centralizer_conj_singleton]

theorem isSymNatural_conj_centralizer {L : Subgroup (MulAut V)} (g s : MulAut V) {n : ℕ}
    (hL : conjAut g L = L)
    (h : G6.IsSymNatural (L ⊓ Subgroup.centralizer ({s} : Set (MulAut V)))
      (commOn (fixV (Subgroup.zpowers s)) (L ⊓ Subgroup.centralizer ({s} : Set (MulAut V)))) n) :
    G6.IsSymNatural (L ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set (MulAut V)))
      (commOn (fixV (Subgroup.zpowers (g * s * g⁻¹)))
        (L ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set (MulAut V)))) n := by
  rw [inf_centralizer_conj_singleton g s hL, fixV_zpowers_conj, commOn_conjAut]
  exact isSymNatural_conjAut g h

theorem exists_vec_conjAut (g : MulAut V) (F : Subgroup V) (X : Subgroup (MulAut V))
    (q : V → ZMod 2) (hq : ∀ x, q (g x) = q x)
    (h : ∃ v ∈ F, q v = 1 ∧ (∀ x ∈ X, x v = v) ∧ F = Subgroup.zpowers v ⊔ commOn F X ∧
      Subgroup.zpowers v ⊓ commOn F X = ⊥) :
    ∃ v ∈ F.map (g : MulAut V).toMonoidHom, q v = 1 ∧ (∀ x ∈ conjAut g X, x v = v) ∧
      F.map (g : MulAut V).toMonoidHom =
        Subgroup.zpowers v ⊔ commOn (F.map (g : MulAut V).toMonoidHom) (conjAut g X) ∧
      Subgroup.zpowers v ⊓ commOn (F.map (g : MulAut V).toMonoidHom) (conjAut g X) = ⊥ := by
  obtain ⟨v, hvF, hqv, hX, hF, hinf⟩ := h
  refine ⟨g v, Subgroup.mem_map_of_mem _ hvF, (hq v).trans hqv, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : (g⁻¹ * x * g) v = v := hX _ (mem_conjAut.mp hx)
    have h2 : g⁻¹ (x (g v)) = v := by simpa [MulAut.mul_apply] using h1
    calc x (g v) = g (g⁻¹ (x (g v))) := (MulAut.apply_inv_self V g _).symm
      _ = g v := by rw [h2]
  · rw [commOn_conjAut, ← map_zpowers, ← map_sup_subgroup, ← hF]
  · rw [commOn_conjAut, ← map_zpowers, ← map_inf_subgroup, hinf, Subgroup.map_bot]

theorem exists_vec_conj_centralizer {L : Subgroup (MulAut V)} (g s : MulAut V) (q : V → ZMod 2)
    (hq : ∀ x, q (g x) = q x) (hL : conjAut g L = L)
    (h : ∃ v ∈ fixV (Subgroup.zpowers s), q v = 1 ∧
      (∀ x ∈ L ⊓ Subgroup.centralizer ({s} : Set (MulAut V)), x v = v) ∧
      fixV (Subgroup.zpowers s) = Subgroup.zpowers v ⊔
        commOn (fixV (Subgroup.zpowers s)) (L ⊓ Subgroup.centralizer ({s} : Set (MulAut V))) ∧
      Subgroup.zpowers v ⊓
        commOn (fixV (Subgroup.zpowers s)) (L ⊓ Subgroup.centralizer ({s} : Set (MulAut V))) = ⊥) :
    ∃ v ∈ fixV (Subgroup.zpowers (g * s * g⁻¹)), q v = 1 ∧
      (∀ x ∈ L ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set (MulAut V)), x v = v) ∧
      fixV (Subgroup.zpowers (g * s * g⁻¹)) = Subgroup.zpowers v ⊔
        commOn (fixV (Subgroup.zpowers (g * s * g⁻¹)))
          (L ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set (MulAut V))) ∧
      Subgroup.zpowers v ⊓ commOn (fixV (Subgroup.zpowers (g * s * g⁻¹)))
        (L ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set (MulAut V))) = ⊥ := by
  rw [inf_centralizer_conj_singleton g s hL, fixV_zpowers_conj]
  exact exists_vec_conjAut g _ _ q hq h

end CFSG.ASVolI.ChH
