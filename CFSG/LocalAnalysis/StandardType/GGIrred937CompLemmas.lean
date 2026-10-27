module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace Irred937

private def ggCompBad {L : Type} [Group L] (p : ℕ) (K J₁ : Subgroup L) : Subgroup L :=
  ⨆ (J₂ : Subgroup L) (_ : IsComponentOf J₂ K ∧ J₂ ≠ J₁ ∧ p ∣ Nat.card J₂), J₂

private theorem ggCompBad_eq_sSup {L : Type} [Group L] (p : ℕ) (K J₁ : Subgroup L) :
    ggCompBad p K J₁ =
      sSup {J₂ : Subgroup L | IsComponentOf J₂ K ∧ J₂ ≠ J₁ ∧ p ∣ Nat.card J₂} := by
  unfold ggCompBad
  rw [iSup_subtype']
  exact (iSup_subtype'' {J₂ : Subgroup L | IsComponentOf J₂ K ∧ J₂ ≠ J₁ ∧ p ∣ Nat.card J₂}
    id).trans (sSup_eq_iSup).symm

private theorem map_ggFix_conj_mulEquiv {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (e : G) :
    ggFix (MulAut.conj (f e) : MulAut H) =
      (ggFix (MulAut.conj e : MulAut G)).map f.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_ggFix, mem_ggFix]
  constructor
  · intro h
    simpa [MulAut.conj_apply, map_mul] using congrArg f.symm h
  · intro h
    simpa [MulAut.conj_apply, map_mul] using congrArg f h

private theorem ggCompBad_map_mulEquiv {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (p : ℕ) {K : Subgroup G} {J₁ : Subgroup G} :
    (ggCompBad p K J₁).map f.toMonoidHom =
      ggCompBad p (K.map f.toMonoidHom) (J₁.map f.toMonoidHom) := by
  let S : Set (Subgroup G) := {J₂ | IsComponentOf J₂ K ∧ J₂ ≠ J₁ ∧ p ∣ Nat.card J₂}
  let S' : Set (Subgroup H) :=
    {J₂ | IsComponentOf J₂ (K.map f.toMonoidHom) ∧ J₂ ≠ J₁.map f.toMonoidHom ∧
      p ∣ Nat.card J₂}
  have hset : f.mapSubgroup '' S = S' := by
    ext J'
    constructor
    · rintro ⟨J, hJ, rfl⟩
      change IsComponentOf J K ∧ J ≠ J₁ ∧ p ∣ Nat.card J at hJ
      obtain ⟨hcomp, hne, hdvd⟩ := hJ
      change IsComponentOf (f.mapSubgroup J) (K.map f.toMonoidHom) ∧
        f.mapSubgroup J ≠ J₁.map f.toMonoidHom ∧ p ∣ Nat.card (f.mapSubgroup J)
      refine ⟨?_, ?_, ?_⟩
      · exact isComponentOf_map_of_injective f.toMonoidHom f.injective hcomp
      · intro heq
        exact hne (f.mapSubgroup.injective heq)
      · change p ∣ Nat.card (J.map f.toMonoidHom)
        rwa [Subgroup.card_map_of_injective (K := J) f.injective]
    · rintro ⟨hcomp, hne, hdvd⟩
      refine ⟨f.mapSubgroup.symm J', ?_, f.mapSubgroup.apply_symm_apply J'⟩
      have hsymmJ : f.mapSubgroup.symm J' = J'.map f.symm.toMonoidHom := by
        rw [MulEquiv.symm_mapSubgroup]
        rfl
      have hsymmK : (K.map f.toMonoidHom).map f.symm.toMonoidHom = K := by
        rw [Subgroup.map_map]
        have hcompHom : (f.symm.toMonoidHom).comp f.toMonoidHom = MonoidHom.id G := by
          ext x
          simp
        rw [hcompHom, Subgroup.map_id]
      change IsComponentOf (f.mapSubgroup.symm J') K ∧ f.mapSubgroup.symm J' ≠ J₁ ∧
        p ∣ Nat.card (f.mapSubgroup.symm J')
      refine ⟨?_, ?_, ?_⟩
      · have h := isComponentOf_map_of_injective f.symm.toMonoidHom f.symm.injective hcomp
        rw [← hsymmJ] at h
        rwa [hsymmK] at h
      · intro heq
        apply hne
        calc J' = f.mapSubgroup (f.mapSubgroup.symm J') := (f.mapSubgroup.apply_symm_apply J').symm
          _ = f.mapSubgroup J₁ := by rw [heq]
          _ = J₁.map f.toMonoidHom := rfl
      · have hc : Nat.card (f.mapSubgroup.symm J') = Nat.card J' := by
          rw [hsymmJ]
          exact Subgroup.card_map_of_injective (K := J') f.symm.injective
        rwa [hc]
  have hmain : f.mapSubgroup (sSup S) = sSup (f.mapSubgroup '' S) :=
    (OrderIso.map_sSup f.mapSubgroup S).trans (sSup_image).symm
  rw [ggCompBad_eq_sSup, ggCompBad_eq_sSup]
  change f.mapSubgroup (sSup S) = sSup S'
  rw [hmain, hset]

private theorem ggFixCompCyclic_map_conj_mulEquiv {p : ℕ} {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (e : G) :
    GGFixCompCyclic p (MulAut.conj e : MulAut G) →
      GGFixCompCyclic p (MulAut.conj (f e) : MulAut H) := by
  intro h
  unfold GGFixCompCyclic at h ⊢
  obtain ⟨J₁, hJ₁, hcyc⟩ := h
  refine ⟨J₁.map f.toMonoidHom, ?_, ?_⟩
  · have hJ₁' := isComponentOf_map_of_injective f.toMonoidHom f.injective hJ₁
    rw [← map_ggFix_conj_mulEquiv f e] at hJ₁'
    exact hJ₁'
  · intro P hP hle
    have hBad : (ggCompBad p (ggFix (MulAut.conj e)) J₁).map f.toMonoidHom =
        ggCompBad p (ggFix (MulAut.conj (f e))) (J₁.map f.toMonoidHom) := by
      rw [ggCompBad_map_mulEquiv f p, ← map_ggFix_conj_mulEquiv f e]
    let P₀ : Subgroup G := P.comap f.toMonoidHom
    have hP₀ : IsPGroup p P₀ := IsPGroup.comap_of_injective hP f.toMonoidHom f.injective
    have hpeq : P₀.map f.toMonoidHom = P :=
      Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr f.surjective]; exact le_top)
    have hle₀ : P₀ ≤ ggCompBad p (ggFix (MulAut.conj e)) J₁ := by
      have hm : P₀.map f.toMonoidHom ≤
          (ggCompBad p (ggFix (MulAut.conj e)) J₁).map f.toMonoidHom := by
        rw [hBad, hpeq]
        exact hle
      rw [Subgroup.map_le_iff_le_comap] at hm
      rwa [Subgroup.comap_map_eq_self_of_injective f.injective] at hm
    haveI : IsCyclic P₀ := hcyc P₀ hP₀ hle₀
    rw [← hpeq]
    exact isCyclic_of_surjective (f.subgroupMap P₀) (f.subgroupMap P₀).surjective

theorem not_ggFixCompCyclic_of_solvable {p : ℕ} {H : Type} [Group H] [Finite H] (a : MulAut H)
    (hs : IsSolvable (ggFix a)) : ¬ GGFixCompCyclic p a := by
  rintro ⟨J₁, hJ₁, -⟩
  haveI : Group.IsSolvable ↥(ggFix a) := hs
  have hsol : Group.IsSolvable ↥J₁ :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hJ₁.1)
      (Subgroup.inclusion_injective hJ₁.1)
  haveI : Group.IsSolvable ↥J₁ := hsol
  haveI : Nontrivial ↥J₁ := by
    haveI : IsSimpleGroup (↥J₁ ⧸ Subgroup.center ↥J₁) := hJ₁.2.2.2
    exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J₁))
  have hlt : commutator ↥J₁ < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J₁
  exact (ne_of_lt hlt) hJ₁.2.2.1

theorem ggFixCompCyclic_conj_of_mulEquiv {p : ℕ} {G H : Type} [Group G] [Group H]
    (f : G ≃* H) (e : G) :
    GGFixCompCyclic p (MulAut.conj e : MulAut G) ↔ GGFixCompCyclic p (MulAut.conj (f e) : MulAut H) := by
  constructor
  · exact ggFixCompCyclic_map_conj_mulEquiv f e
  · intro h
    have h' := ggFixCompCyclic_map_conj_mulEquiv f.symm (f e) h
    simpa using h'

end Irred937

end CFSG.StandardType

end
