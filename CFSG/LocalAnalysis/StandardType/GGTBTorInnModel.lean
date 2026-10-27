module

public import CFSG.LocalAnalysis.StandardType.GGTBTorTransport
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {R : Type} [Group R]

theorem exists_innModel_of_tbGroup {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, ∃ x : R, φ = MulAut.conj x) (hcenter : Subgroup.center R = ⊥)
    {p r : ℕ} {L : Type} [Group L] [Finite L] (ψ : L →* R) (hψinj : Function.Injective ψ)
    (A : Subgroup (MulAut L)) (hTB : GGTorusTBGroup p r R I L ψ A) :
    ∃ e : L ≃* R, (∀ l, e l = ψ l) ∧
      ∃ E : Subgroup R, IsElemAbelian p E ∧ Nat.card E = Nat.card A ∧
        (∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) ∧
        A.map (MulAut.congr e).toMonoidHom = E.map (MulAut.conj : R →* MulAut R) := by
  obtain ⟨hψ, -, -, hA, hAI, -, -, hSC⟩ := hTB
  let e : L ≃* R := MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩
  have heq : ∀ l, e l = ψ l := fun _ => rfl
  let B : Subgroup (MulAut R) := A.map (MulAut.congr e).toMonoidHom
  let j : R →* MulAut R := MulAut.conj
  have hj : Function.Injective j := CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  have hBinn : B ≤ j.range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨φ, hφ, hφeq⟩ := hAI a ha
    obtain ⟨x, rfl⟩ := hI φ hφ
    refine ⟨x, ?_⟩
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := e.surjective y
    change MulAut.conj x (e l) = MulAut.congr e a (e l)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, heq, heq]
    exact hφeq l
  let E : Subgroup R := B.comap j
  have hEB : E.map j = B := Subgroup.map_comap_eq_self hBinn
  have hB : IsElemAbelian p B := TableB.isElemAbelian_map hA _
  have hE : IsElemAbelian p E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hj ?_)⟩⟩, fun x hx => hj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hB x.2 y.2
    · rw [map_pow, map_one]
      exact hB.2 _ hx
  have hcard : Nat.card E = Nat.card A := by
    rw [← Subgroup.card_map_of_injective hj, hEB, Subgroup.card_map_of_injective
      (MulAut.congr e).injective]
  have hESC : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hn3 : (e.symm g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have hfix : ∀ a ∈ A, a (e.symm g) = e.symm g := by
      intro a ha
      obtain ⟨x, hx⟩ := hBinn (Subgroup.mem_map_of_mem _ ha)
      have hxE : x ∈ E := by
        change j x ∈ B
        exact hx ▸ Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom ha
      apply e.injective
      have hax : MulAut.congr e a g = x * g * x⁻¹ := by
        exact (congrArg (fun f : MulAut R => f g) hx).symm
      have hconj : x * g * x⁻¹ = g := by rw [← hg x hxE, mul_inv_cancel_right]
      simpa [MulAut.congr_apply, MulEquiv.trans_apply] using hax.trans hconj
    have hmem := hSC (e.symm g) hfix hn3
    change j g ∈ B
    have h := Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom hmem
    have hc : MulAut.congr e (MulAut.conj (e.symm g)) = MulAut.conj g := by
      ext y
      simp [MulAut.congr_apply]
    change MulAut.congr e (MulAut.conj (e.symm g)) ∈ B at h
    rwa [hc] at h
  exact ⟨e, heq, E, hE, hcard, hESC, hEB.symm⟩

theorem torData_of_innModel {L : Type} [Group L] (e : L ≃* R)
    {A : Subgroup (MulAut L)} {E : Subgroup R}
    (hA : A.map (MulAut.congr e).toMonoidHom = E.map (MulAut.conj : R →* MulAut R))
    {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (h : GGTorusTorData m N C M R (E.map (MulAut.conj : R →* MulAut R))) :
    GGTorusTorData m N C M L A := by
  have hback : (E.map (MulAut.conj : R →* MulAut R)).map
      (MulAut.congr e.symm).toMonoidHom = A := by
    rw [← hA, Subgroup.map_map]
    have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
        MonoidHom.id (MulAut L) := by
      ext a x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hcomp, Subgroup.map_id]
  exact h.transport_eq e.symm hback.symm

theorem torData_of_mulEquiv_map {L : Type} [Group L] {E : Subgroup L} {E' : Subgroup R}
    (e : L ≃* R) (hE : E.map e.toMonoidHom = E')
    {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (h : GGTorusTorData m N C M R (E'.map (MulAut.conj : R →* MulAut R))) :
    GGTorusTorData m N C M L (E.map (MulAut.conj : L →* MulAut L)) := by
  have hA : (E.map (MulAut.conj : L →* MulAut L)).map (MulAut.congr e).toMonoidHom =
      E'.map (MulAut.conj : R →* MulAut R) := by
    rw [← hE, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x y
    simp [MulAut.congr_apply]
  exact torData_of_innModel e hA h

theorem torData_of_conj_eq {E E' : Subgroup R} (e : R ≃* R) (hE : E.map e.toMonoidHom = E')
    {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (h : GGTorusTorData m N C M R (E'.map (MulAut.conj : R →* MulAut R))) :
    GGTorusTorData m N C M R (E.map (MulAut.conj : R →* MulAut R)) :=
  torData_of_mulEquiv_map e hE h

end CFSG.StandardType
