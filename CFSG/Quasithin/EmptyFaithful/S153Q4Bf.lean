module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Ba

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4B

open Equiv

section Alternating

theorem alt_not_isSolvable (α : Type) [Fintype α] [DecidableEq α] (h : 5 ≤ Fintype.card α) :
    ¬ Group.IsSolvable (alternatingGroup α) := by
  intro hs
  refine Equiv.Perm.not_isSolvable α (by simpa using h) ?_
  exact Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign (by
    intro g hg
    exact ⟨⟨g, hg⟩, rfl⟩)

theorem mem_stabilizer_iff (k : Fin 6) (σ : ↥(alternatingGroup (Fin 6))) :
    σ ∈ MulAction.stabilizer ↥(alternatingGroup (Fin 6)) k ↔ (σ : Perm (Fin 6)) k = k :=
  Iff.rfl

theorem stabilizer_not_isSolvable (k : Fin 6) :
    ¬ Group.IsSolvable ↥(MulAction.stabilizer ↥(alternatingGroup (Fin 6)) k) := by
  intro hs
  let s : Finset (Fin 6) := Finset.univ.erase k
  have hcard : 5 ≤ Fintype.card ↥s := by
    simp [s]
  refine alt_not_isSolvable ↥s hcard ?_
  refine Group.isSolvable_of_isSolvable_injective
    (f := MonoidHom.codRestrict (alternatingGroup.ofSubtype s)
      (MulAction.stabilizer ↥(alternatingGroup (Fin 6)) k) ?_) ?_
  · intro σ
    rw [mem_stabilizer_iff, alternatingGroup.coe_ofSubtype]
    exact Perm.ofSubtype_apply_of_not_mem (p := (· ∈ s)) σ.1 (by simp [s])
  · intro a b hab
    apply alternatingGroup.ofSubtype_injective
    exact congrArg Subtype.val hab

end Alternating

section Conclusion

variable {W : Type} [CommGroup W] {z : MulAut W}

theorem perm_unique [Finite W] (C : ZCtx W z) {Ah : Subgroup (MulAut W)}
    {lab : Fin 6 → Subgroup W} (hO : OvalData0 Ah z lab) {g : MulAut W} {σ σ' : Perm (Fin 6)}
    (h : ∀ k, ∀ w ∈ lab k, g w ∈ lab (σ k)) (h' : ∀ k, ∀ w ∈ lab k, g w ∈ lab (σ' k)) :
    σ = σ' := by
  refine Equiv.ext fun l => ?_
  obtain ⟨w, hw, hw1⟩ := pt_exists_ne_one (hO.pt l)
  have hgw1 : g w ≠ 1 := fun h1 => hw1 (EmbeddingLike.map_eq_one_iff.1 h1)
  exact hO.inj (C.pt_eq_of_mem (hO.pt _) (hO.pt _) (h l w hw) (h' l w hw) hgw1)

theorem exists_hom [Finite W] (C : ZCtx W z) {Ah : Subgroup (MulAut W)}
    {lab : Fin 6 → Subgroup W} (hO : OvalData0 Ah z lab) :
    ∃ Ψ : ↥Ah →* ↥(alternatingGroup (Fin 6)), Function.Surjective Ψ ∧
      ∀ (g : ↥Ah) (k : Fin 6), ∀ w ∈ lab k, (g : MulAut W) w ∈ lab ((Ψ g : Perm (Fin 6)) k) := by
  choose σ hσ hσ' using fun g : ↥Ah => hO.equiv g g.2
  have huniq : ∀ (g : ↥Ah) (τ : Perm (Fin 6)),
      (∀ k, ∀ w ∈ lab k, (g : MulAut W) w ∈ lab (τ k)) → σ g = τ :=
    fun g τ h => perm_unique C hO (hσ' g) h
  have h1 : σ 1 = 1 := huniq 1 1 (fun k w hw => by simpa using hw)
  have hm : ∀ g h : ↥Ah, σ (g * h) = σ g * σ h := fun g h =>
    huniq (g * h) (σ g * σ h) (fun k w hw => by simpa using hσ' g (σ h k) _ (hσ' h k w hw))
  refine ⟨{ toFun := fun g => ⟨σ g, hσ g⟩
            map_one' := Subtype.ext h1
            map_mul' := fun g h => Subtype.ext (hm g h) }, ?_, fun g k w hw => hσ' g k w hw⟩
  intro s
  obtain ⟨g, hg, hgs⟩ := hO.surj s s.2
  exact ⟨⟨g, hg⟩, Subtype.ext (huniq ⟨g, hg⟩ s hgs)⟩

theorem mem_stab_iff [Finite W] (C : ZCtx W z) {Ah : Subgroup (MulAut W)}
    {lab : Fin 6 → Subgroup W} (hO : OvalData0 Ah z lab) {Ψ : ↥Ah →* ↥(alternatingGroup (Fin 6))}
    (hΨ : ∀ (g : ↥Ah) (k : Fin 6), ∀ w ∈ lab k,
      (g : MulAut W) w ∈ lab ((Ψ g : Perm (Fin 6)) k))
    (g : ↥Ah) (k : Fin 6) : (g : MulAut W) ∈ stab (lab k) ↔ (Ψ g : Perm (Fin 6)) k = k := by
  constructor
  · intro hs
    have hs' : ∀ v ∈ lab k, (g : MulAut W) v ∈ lab k ∧ (g : MulAut W)⁻¹ v ∈ lab k := hs
    obtain ⟨w, hw, hw1⟩ := pt_exists_ne_one (hO.pt k)
    have hgw1 : (g : MulAut W) w ≠ 1 := fun h1 => hw1 (EmbeddingLike.map_eq_one_iff.1 h1)
    exact (hO.inj (C.pt_eq_of_mem (hO.pt _) (hO.pt _) (hs' w hw).1 (hΨ g k w hw) hgw1)).symm
  · intro hk
    show ∀ v ∈ lab k, (g : MulAut W) v ∈ lab k ∧ (g : MulAut W)⁻¹ v ∈ lab k
    intro v hv
    refine ⟨by simpa [hk] using hΨ g k v hv, ?_⟩
    have hk' : ((Ψ g⁻¹ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) k = k := by
      rw [map_inv]
      exact Perm.inv_eq_iff_eq.2 hk.symm
    have h2 := hΨ g⁻¹ k v hv
    rw [hk'] at h2
    exact h2

theorem conclusion [Finite W] (C : ZCtx W z) {Ah : Subgroup (MulAut W)}
    {lab : Fin 6 → Subgroup W} (hO : OvalData0 Ah z lab) {X : Subgroup (MulAut W)}
    (hAX : Ah ≤ X) (k : Fin 6) : ¬ Group.IsSolvable ↥(X ⊓ stab (lab k)) := by
  intro hS
  obtain ⟨Ψ, hΨs, hΨ⟩ := exists_hom C hO
  have hle : Ah ⊓ stab (lab k) ≤ X ⊓ stab (lab k) := inf_le_inf_right _ hAX
  have hT : Group.IsSolvable ↥(Ah ⊓ stab (lab k)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  let φ : ↥(Ah ⊓ stab (lab k)) →*
      ↥(MulAction.stabilizer ↥(alternatingGroup (Fin 6)) k) :=
    MonoidHom.codRestrict (Ψ.comp (Subgroup.inclusion inf_le_left))
      (MulAction.stabilizer ↥(alternatingGroup (Fin 6)) k)
      (fun t => (mem_stab_iff C hO hΨ ⟨t, t.2.1⟩ k).1 t.2.2)
  have hφ : Function.Surjective φ := by
    intro s
    obtain ⟨g, hg⟩ := hΨs s.1
    have hgk : (Ψ g : Perm (Fin 6)) k = k := by rw [hg]; exact s.2
    exact ⟨⟨g, g.2, (mem_stab_iff C hO hΨ g k).2 hgk⟩, Subtype.ext hg⟩
  exact stabilizer_not_isSolvable k (Group.isSolvable_of_surjective (f := φ) hφ)

end Conclusion

end Q4B

end S153Q

end CFSG.Quasithin
