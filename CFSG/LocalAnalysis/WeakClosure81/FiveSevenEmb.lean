module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenPhi

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 Equiv

variable {G : Type} [Group G] [Finite G]

theorem exists_embedding_of_forall_mem_range {H A : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (hHA : H = Fstar H ⊔ A)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n))
    (φ : ↥H →* MulAut (alternatingGroup (Fin n))) (hφinj : Function.Injective φ)
    (hφ : ∀ (l : ↥H) (hl : (l : G) ∈ Fstar H), φ l = MulAut.conj (e ⟨(l : G), hl⟩))
    (hA : ∀ a : ↥H, (a : G) ∈ A →
      φ a ∈ (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n))).range) :
    ∃ ι : ↥H →* Perm (Fin n), Function.Injective ι ∧
      ((Fstar H).subgroupOf H).map ι = alternatingGroup (Fin n) := by
  set R : Subgroup (MulAut (alternatingGroup (Fin n))) :=
    (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n))).range with hR
  have hFR : ∀ (l : ↥H) (hl : (l : G) ∈ Fstar H), φ l ∈ R := by
    intro l hl
    rw [hφ l hl, ← MulAut.conjNormal_val]
    exact ⟨_, rfl⟩
  have hAH : A ≤ H := hHA ▸ le_sup_right
  have hHR : ∀ x : ↥H, φ x ∈ R := by
    have hle' : Fstar H ⊔ A ≤ (R.comap φ).map H.subtype := by
      refine sup_le ?_ ?_
      · intro f hf
        exact Subgroup.mem_map.2 ⟨⟨f, fstar_le_group H hf⟩, hFR _ hf, rfl⟩
      · intro a ha
        exact Subgroup.mem_map.2 ⟨⟨a, hAH ha⟩, hA _ ha, rfl⟩
    have hle : H ≤ (R.comap φ).map H.subtype := hHA.le.trans hle'
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hle x.2)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hcj : Function.Injective
      (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
  let ceq : ↥R ≃* Perm (Fin n) := (MonoidHom.ofInjective hcj).symm
  have hceq : ∀ τ : Perm (Fin n), ceq ⟨MulAut.conjNormal τ, τ, rfl⟩ = τ := by
    intro τ
    rw [MulEquiv.symm_apply_eq]
    rfl
  have key : ∀ (l : ↥H) (hl : (l : G) ∈ Fstar H),
      ceq (φ.codRestrict R hHR l) =
        ((e ⟨(l : G), hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro l hl
    have hval : φ l = MulAut.conjNormal
        ((e ⟨(l : G), hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) := by
      rw [hφ l hl, MulAut.conjNormal_val]
    have h1 : (φ.codRestrict R hHR l : ↥R) = ⟨MulAut.conjNormal
        ((e ⟨(l : G), hl⟩ : alternatingGroup (Fin n)) : Perm (Fin n)), _, rfl⟩ :=
      Subtype.ext hval
    rw [h1, hceq]
  refine ⟨ceq.toMonoidHom.comp (φ.codRestrict R hHR),
    ceq.injective.comp (fun x y hxy => hφinj (congrArg Subtype.val hxy)), ?_⟩
  ext p
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, key l hl]
    exact (e ⟨(l : G), hl⟩).2
  · intro hp
    refine ⟨⟨(e.symm ⟨p, hp⟩ : G), fstar_le_group H (e.symm ⟨p, hp⟩).2⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact (e.symm ⟨p, hp⟩).2
    · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, key _ (e.symm ⟨p, hp⟩).2]
      simp

theorem exists_embedding_of_ne_six {H : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) :
    ∃ ι : ↥H →* Perm (Fin n), Function.Injective ι ∧
      ((Fstar H).subgroupOf H).map ι = alternatingGroup (Fin n) := by
  obtain ⟨φ, hφinj, hφ, -⟩ := exists_injective_conj_apply_of_fstar_alt hn e
  exact exists_embedding_of_forall_mem_range (A := H) (by omega)
    (sup_eq_right.2 (fstar_le_group H)).symm e φ hφinj hφ
    (fun a _ => (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
      hn6).2 (φ a))

end CFSG.LocalAnalysis.WeakClosure81
