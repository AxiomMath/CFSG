module

public import CFSG.LocalAnalysis.WeakClosure81.InFMulEquiv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F12

open CFSG.Quasithin Subgroup

theorem inFFor_top_map_conj {Q : Type} [Group Q] [Finite Q] {j : ℕ} {T : Subgroup Q}
    (h : InFFor j (⊤ : Subgroup Q) T) (g : Q) :
    InFFor j (⊤ : Subgroup Q) (T.map (MulAut.conj g).toMonoidHom) := by
  intro Ω hΩ hne hbot
  have hΩmap : Subgroup.map (MulAut.conj g).toMonoidHom '' Ω = Ω := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro A ⟨B, hB, rfl⟩
      exact hΩ.conj B hB g (Subgroup.mem_top g)
    · intro A hA
      refine ⟨A.map (MulAut.conj g⁻¹).toMonoidHom, hΩ.conj A hA g⁻¹ (Subgroup.mem_top g⁻¹), ?_⟩
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id Q := by
        ext x
        simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
        change (MulAut.conj g) ((MulAut.conj g⁻¹) x) = x
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [hcomp, Subgroup.map_id]
  have hE : eGenP j (⊤ : Subgroup Q) (T.map (MulAut.conj g).toMonoidHom) Ω =
      (eGenP j (⊤ : Subgroup Q) T Ω).map (MulAut.conj g).toMonoidHom := by
    have h1 := eGenP_map_mulEquiv (MulAut.conj g) j (⊤ : Subgroup Q) T Ω
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective, hΩmap] at h1
  have hprod := h Ω hΩ hne hbot
  have himg := congrArg (fun s : Set Q => (MulAut.conj g).toMonoidHom '' s) hprod
  have hsurj : Function.Surjective ⇑(MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  rw [Set.image_mul, Subgroup.coe_top, Set.image_univ_of_surjective hsurj,
    ← Subgroup.coe_map (MulAut.conj g).toMonoidHom
      (eGenP j (⊤ : Subgroup Q) T Ω),
    ← Subgroup.coe_map (MulAut.conj g).toMonoidHom T] at himg
  rw [hE]
  simpa only [Subgroup.coe_top] using himg

theorem inF_top_of_inFFor {Q : Type} [Group Q] [Finite Q] {j : ℕ} {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) (h : InFFor j (⊤ : Subgroup Q) T) : InF j (⊤ : Subgroup Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T' hT'
  have hTof : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  obtain ⟨k, -, hk⟩ := hTof.exists_mem_conj hT'
  have hT'eq : T' = T.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    exact hk x
  rw [hT'eq]
  exact inFFor_top_map_conj h k

end CFSG.LocalAnalysis.UniquenessCase.UC22.F12
