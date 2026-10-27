module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpan

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

namespace SpUFixGeom

variable {L : Type} [Group L] {R : Subgroup L} {F V : Type} [Field F] [AddCommGroup V]
  [Module F V]

theorem le_of_mem_rootSpan [Finite L] (G : SpUFixGeom L R F V) {Sy : Subgroup L}
    (hSy : ∃ P : Sylow 2 L, (P : Subgroup L) = Sy) {s : V} (hs : s ∈ G.rootSpan Sy)
    (hs0 : s ≠ 0) : G.X s ≤ Sy := by
  obtain ⟨P, rfl⟩ := hSy
  have hSy2 : IsPGroup 2 (P : Subgroup L) := P.isPGroup'
  let T : Set L := {x | ∃ v ∈ G.rootSpan (P : Subgroup L), v ≠ 0 ∧ x ∈ G.X v}
  let E : Subgroup L := Subgroup.closure T
  have hgen_comm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro x ⟨v, hv, _, hxv⟩ y ⟨w, hw, _, hyw⟩
    exact G.X_comm v w (G.form_eq_zero_of_mem_rootSpan hSy2 hv hv)
      (G.form_eq_zero_of_mem_rootSpan hSy2 hw hw)
      (G.form_eq_zero_of_mem_rootSpan hSy2 hv hw) x hxv y hyw
  have hgen_invol : ∀ x ∈ T, x * x = 1 := by
    rintro x ⟨v, hv, _, hxv⟩
    exact G.X_invol v (G.form_eq_zero_of_mem_rootSpan hSy2 hv hv) x hxv
  have hcomm : IsMulCommutative E :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hgen_comm x hx y hy)
  have hcomm' : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hgen_invol y hy
    | one => simp
    | mul y z hy hz ihy ihz =>
        have hyz : Commute y z := hcomm' y hy z hz
        calc (y * z) * (y * z) = (y * y) * (z * z) := (hyz.mul_mul_mul_comm y z).symm
          _ = 1 := by rw [ihy, ihz, one_mul]
    | inv y hy ihy => rw [← mul_inv_rev y y, ihy, inv_one]
  have hsqE : ∀ x : E, x * x = 1 := fun x => Subtype.ext (hsq x.1 x.2)
  have hEp : IsPGroup 2 E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    exact ⟨1, by simpa [pow_two] using hsqE g⟩
  have hconjT : ∀ y ∈ (P : Subgroup L), ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    rintro y hy t ⟨v, hv, hv0, hvt⟩
    obtain ⟨M, hMi, hMβ, hMX, -⟩ := G.conj y
    refine ⟨M v, G.mem_rootSpan_of_conj hy hMi hMβ hMX hv, ?_, ?_⟩
    · intro h
      exact hv0 (hMi (by simpa using h))
    · rw [← hMX v (G.form_eq_zero_of_mem_rootSpan hSy2 hv hv)]
      exact Subgroup.mem_map.mpr ⟨t, hvt, by simp [MulAut.conj_apply]⟩
  have hnorm : (P : Subgroup L) ≤ Subgroup.normalizer (E : Set L) :=
    Subgroup.le_normalizer_closure_iff.mpr fun h hh g hg =>
      Subgroup.subset_closure (hconjT h hh g hg)
  have hsup : IsPGroup 2 ↥((P : Subgroup L) ⊔ E) :=
    IsPGroup.to_sup_of_normal_right' hSy2 hEp hnorm
  have hmax : (P : Subgroup L) ⊔ E = (P : Subgroup L) := P.is_maximal' hsup le_sup_left
  have hE_le : E ≤ (P : Subgroup L) := sup_eq_left.mp hmax
  intro x hx
  exact hE_le (Subgroup.subset_closure ⟨s, hs, hs0, hx⟩)

end SpUFixGeom

end CFSG.LocalAnalysis.WeakClosure81

end
