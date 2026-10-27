module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.InspA312

open CFSG.QuasithinUnique CFSG.Quasithin

section Radical

variable {P B W S : Type*} [Group P] [Group B] [Group W] [Group S]

theorem false_of_isSolvable_of_simple [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (hsol : Group.IsSolvable S) : False := by
  obtain ⟨a, b, hab⟩ := hS
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)

theorem map_eq_bot_of_isSolvable (δ : P →* S) (hδ : Function.Surjective δ) [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (N : Subgroup P) [N.Normal] (hN : Group.IsSolvable N) :
    N.map δ = ⊥ := by
  have hn : (N.map δ).Normal := Subgroup.Normal.map inferInstance δ hδ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map δ) with h | h
  · exact h
  · exfalso
    refine false_of_isSolvable_of_simple hS ?_
    have hsurj : Function.Surjective (δ.comp N.subtype) := by
      intro s
      have hs : s ∈ N.map δ := by rw [h]; trivial
      obtain ⟨n, hn, rfl⟩ := hs
      exact ⟨⟨n, hn⟩, rfl⟩
    exact Group.isSolvable_of_surjective hsurj

theorem ker_le_ker_of_isSolvable (δ : P →* S) (hδ : Function.Surjective δ) [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (β : P →* W) (hβk : Group.IsSolvable β.ker) :
    β.ker ≤ δ.ker := by
  intro x hx
  have h := map_eq_bot_of_isSolvable δ hδ hS β.ker hβk
  have : δ x ∈ β.ker.map δ := ⟨x, hx, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem isSolvable_ker_comp (α : P →* B) (hαk : Group.IsSolvable α.ker) (γ : B →* S)
    (hγk : Group.IsSolvable γ.ker) :
    Group.IsSolvable (γ.comp α).ker := by
  let f : α.ker →* (γ.comp α).ker :=
    { toFun := fun x => ⟨x, by simp [MonoidHom.mem_ker.mp x.2]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g : (γ.comp α).ker →* γ.ker :=
    { toFun := fun x => ⟨α (x : P), MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩
      map_one' := Subtype.ext (map_one α)
      map_mul' := fun x y => Subtype.ext (map_mul α (x : P) (y : P)) }
  refine Group.isSolvable_of_ker_le_range f g fun x hx => ?_
  have hx' : α x = 1 := congrArg Subtype.val hx
  exact ⟨⟨x, hx'⟩, rfl⟩

theorem nonempty_mulEquiv_of_solvable_kernels (α : P →* B) (hα : Function.Surjective α)
    (hαk : Group.IsSolvable α.ker) (β : P →* W) (hβ : Function.Surjective β)
    (hβk : Group.IsSolvable β.ker) [IsSimpleGroup W] (hW : ∃ a b : W, a * b ≠ b * a)
    (γ : B →* S) (hγ : Function.Surjective γ) (hγk : Group.IsSolvable γ.ker) [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : Nonempty (W ≃* S) := by
  set δ := γ.comp α with hδdef
  have hδ : Function.Surjective δ := hγ.comp hα
  have hδk := isSolvable_ker_comp α hαk γ hγk
  have hker : β.ker = δ.ker :=
    le_antisymm (ker_le_ker_of_isSolvable δ hδ hS β hβk)
      (ker_le_ker_of_isSolvable β hβ hW δ hδk)
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective β hβ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective δ hδ)⟩

end Radical

section Quotient

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}

theorem subgroupOf_solvRad_eq (N : Subgroup ↥L) [N.Normal] (hN : Group.IsSolvable N)
    (hs : IsSimpleGroup (↥L ⧸ N)) (hnc : ∃ a b : ↥L ⧸ N, a * b ≠ b * a) :
    (solvRad L).subgroupOf L = N := by
  apply le_antisymm
  · have : ((solvRad L).subgroupOf L).Normal := solvRad_normal L
    have hsol : Group.IsSolvable ↥((solvRad L).subgroupOf L) := by
      have := solvRad_isSolvable L
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).injective
    have h := map_eq_bot_of_isSolvable (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hnc
      ((solvRad L).subgroupOf L) hsol
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · have hNN : (N.map L.subtype).subgroupOf L = N :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective N
    have hmap : N.map L.subtype ≤ solvRad L := by
      refine le_solvRad (Subgroup.map_subtype_le N) (by rw [hNN]; infer_instance) ?_
      exact Group.isSolvable_of_isSolvable_injective
        (f := (N.equivMapOfInjective L.subtype L.subtype_injective).symm.toMonoidHom)
        (N.equivMapOfInjective L.subtype L.subtype_injective).symm.injective
    intro x hx
    exact hmap ⟨x, hx, rfl⟩

theorem nonempty_mulEquiv_quotient {W : Type} [Group W] (f : ↥L →* W)
    (hf : Function.Surjective f) (hker : f.ker = (solvRad L).subgroupOf L) (N : Subgroup ↥L)
    [N.Normal] (hN : Group.IsSolvable N) (hs : IsSimpleGroup (↥L ⧸ N))
    (hnc : ∃ a b : ↥L ⧸ N, a * b ≠ b * a) : Nonempty (W ≃* ↥L ⧸ N) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (hker.trans (subgroupOf_solvRad_eq N hN hs hnc)))⟩

theorem nonempty_mulEquiv_of_simple {W : Type} [Group W] (f : ↥L →* W)
    (hf : Function.Surjective f) (hker : f.ker = (solvRad L).subgroupOf L) [IsSimpleGroup ↥L]
    (hnc : ∃ a b : ↥L, a * b ≠ b * a) : Nonempty (W ≃* ↥L) := by
  have : ((solvRad L).subgroupOf L).Normal := solvRad_normal L
  have hsol : Group.IsSolvable ↥((solvRad L).subgroupOf L) := by
    have := solvRad_isSolvable L
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).injective
  have h := map_eq_bot_of_isSolvable (MonoidHom.id ↥L) Function.surjective_id hnc
    ((solvRad L).subgroupOf L) hsol
  rw [Subgroup.map_id] at h
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, h]
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hf⟩).symm⟩

theorem nonempty_mulEquiv_of_quasisimple {W : Type} [Group W] (f : ↥L →* W)
    (hf : Function.Surjective f) (hker : f.ker = (solvRad L).subgroupOf L)
    (hq : CFSG.IsQuasisimple ↥L) : Nonempty (W ≃* ↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨-, hs, hnc⟩ := hq
  exact nonempty_mulEquiv_quotient f hf hker _ inferInstance hs hnc

end Quotient

end CFSG.Quasithin.H13.InspA312
