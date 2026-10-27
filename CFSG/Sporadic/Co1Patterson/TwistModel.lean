module

public import CFSG.Sporadic.Co1Patterson.GlueTwist
public import CFSG.Sporadic.Co1Patterson.GlueForm
public import CFSG.Sporadic.Co1Patterson.TwistOuter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

theorem card_ker_eq_two {E L' : Type*} [Group E] [Group L'] (f : E →* L') {ζ : E}
    (hker : ∀ e, f e = 1 ↔ e = 1 ∨ e = ζ) (hζ1 : ζ ≠ 1) : Nat.card f.ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨ζ, (hker ζ).2 (Or.inr rfl)⟩, fun h => hζ1 (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨e, he⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases (hker e).1 he with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H₀ : Type} [Group H₀]

@[expose] noncomputable def wPlusMap
    (ι : L ≃* omegaT) (k : Fin 3) : wPlus →* L :=
  ι.symm.toMonoidHom.comp (((trialityAut ^ (k : ℕ)).toMonoidHom.comp
    omegaRestrictEquiv.symm.toMonoidHom).comp pOnto)

theorem wPlusMap_apply
    (ι : L ≃* omegaT) (k : Fin 3) (w : wPlus) :
    wPlusMap ι k w = ι.symm ((trialityAut ^ (k : ℕ)) (omegaRestrictEquiv.symm (pOnto w))) :=
  rfl

theorem pOnto_eq_one_iff
    {w : wPlus} : pOnto w = 1 ↔ w = 1 ∨ w = zPlus := by
  rw [← MonoidHom.mem_ker, ker_pOnto, mem_ker_pPlus]

theorem wPlusMap_eq_one_iff
    (ι : L ≃* omegaT) (k : Fin 3) {w : wPlus} : wPlusMap ι k w = 1 ↔ w = 1 ∨ w = zPlus := by
  rw [wPlusMap_apply, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff,
    MulEquiv.map_eq_one_iff, pOnto_eq_one_iff]

theorem wPlusMap_zPlus
    (ι : L ≃* omegaT) (k : Fin 3) : wPlusMap ι k zPlus = 1 :=
  (wPlusMap_eq_one_iff ι k).2 (Or.inr rfl)

theorem wPlusMap_surjective
    (ι : L ≃* omegaT) (k : Fin 3) : Function.Surjective (wPlusMap ι k) :=
  ι.symm.surjective.comp (((trialityAut ^ (k : ℕ)).surjective.comp
    omegaRestrictEquiv.symm.surjective).comp pOnto_surjective)

abbrev twistModel
    (S₀ : ExtraspecialTypeSystem n L act qf bil H₀) (ι : L ≃* omegaT) (k : Fin 3) : Type :=
  Twist S₀ (wPlusMap ι k) zPlus (wPlusMap_zPlus ι k)

theorem exists_mulEquiv_wPlus_of_perfect
    (ι : L ≃* omegaT) {E : Type*} [Group E]
    (hE : commutator E = ⊤) (π : E →* L) (hπ : Function.Surjective π) {ζ : E}
    (hζc : ζ ∈ Subgroup.center E) (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) (hζ1 : ζ ≠ 1) :
    ∃ θ : E ≃* wPlus, θ ζ = zPlus := by
  have : Group.IsPerfect E := ⟨hE⟩
  have hqker : ∀ e, (ι.toMonoidHom.comp π) e = 1 ↔ e = 1 ∨ e = ζ := fun e => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hker]
  have hq'ker : ∀ w, (omegaRestrictEquiv.symm.toMonoidHom.comp pOnto) w = 1 ↔
      w = 1 ∨ w = zPlus := fun w => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      pOnto_eq_one_iff]
  obtain ⟨θ⟩ := Cover.nonempty_mulEquiv_of_double_covers_omegaT (ι.toMonoidHom.comp π)
    (ι.surjective.comp hπ)
    (fun e he => by
      rcases (hqker e).1 he with rfl | rfl
      · exact one_mem _
      · exact hζc)
    (card_ker_eq_two _ hqker hζ1) (omegaRestrictEquiv.symm.toMonoidHom.comp pOnto)
    (omegaRestrictEquiv.symm.surjective.comp pOnto_surjective)
    (fun w hw => by
      rcases (hq'ker w).1 hw with rfl | rfl
      · exact one_mem _
      · exact zPlus_mem_center)
    (card_ker_eq_two _ hq'ker zPlus_ne_one)
  refine ⟨θ, ?_⟩
  have hc : θ ζ ∈ Subgroup.center wPlus := by
    rw [Subgroup.mem_center_iff]
    intro w
    rw [← θ.apply_symm_apply w, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hζc]
  rcases mem_center_wPlus.1 hc with h | h
  · exact absurd (θ.map_eq_one_iff.1 (Subtype.ext h)) hζ1
  · exact Subtype.ext h

theorem exists_twistModel_of_perfect
    (S₀ : ExtraspecialTypeSystem n L act qf bil H₀)
    (ι : L ≃* omegaT) {E : Type*} [Group E] (hE : commutator E = ⊤) (π : E →* L)
    (hπ : Function.Surjective π) {ζ : E} (hζ : π ζ = 1) (hζc : ζ ∈ Subgroup.center E)
    (hker : ∀ e, π e = 1 ↔ e = 1 ∨ e = ζ) (hζ1 : ζ ≠ 1) :
    ∃ k : Fin 3, Nonempty (Twist S₀ π ζ hζ ≃* twistModel S₀ ι k) := by
  obtain ⟨θ, hθζ⟩ := exists_mulEquiv_wPlus_of_perfect ι hE π hπ hζc hker hζ1
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq (π.comp θ.symm.toMonoidHom) (wPlusMap ι 0)
    (hπ.comp θ.symm.surjective) (wPlusMap_surjective ι 0) (by
      ext w
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, wPlusMap_eq_one_iff, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, hker, MulEquiv.symm_apply_eq, MulEquiv.symm_apply_eq, map_one,
        hθζ])
  obtain ⟨x, k, ε, hβ⟩ := exists_eq_conj_mul_triality_mul_graph ((ι.symm.trans α).trans ι)
  have key : ∀ w : wPlus, π (θ.symm w) =
      ι.symm x * wPlusMap ι k ((rAut ^ (ε : ℕ)) w) * (ι.symm x)⁻¹ := by
    intro w
    have h1 := hα w
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    rw [h1]
    have h2 : α (wPlusMap ι 0 w) =
        ι.symm (((ι.symm.trans α).trans ι) (omegaRestrictEquiv.symm (pOnto w))) := by
      simp only [MulEquiv.trans_apply, wPlusMap_apply, Fin.val_zero, pow_zero, MulAut.one_apply,
        MulEquiv.symm_apply_apply]
    rw [h2, hβ, MulAut.mul_apply, MulAut.mul_apply, graphAut_pow_pOnto, MulAut.conj_apply,
      map_mul, map_mul, map_inv, wPlusMap_apply]
  obtain ⟨h₀, hh₀⟩ := S₀.φ_surj (ι.symm x)⁻¹
  refine ⟨k, ⟨twistEquiv S₀ π (wPlusMap ι k) hζ (wPlusMap_zPlus ι k)
    (θ.trans (rAut ^ (ε : ℕ))) h₀ (fun e => ?_) ?_⟩⟩
  · have h := key (θ e)
    rw [MulEquiv.symm_apply_apply] at h
    rw [MulEquiv.trans_apply, hh₀, inv_inv, h]
    group
  · rw [MulEquiv.trans_apply, hθζ, rAut_pow_zPlus]

theorem centralizer_cases_of_nondeg
    (hb : Nondeg bil) {H : Type} [Group H] [Finite H] [Finite H₀]
    (S : ExtraspecialTypeSystem n L act qf bil H) (S₀ : ExtraspecialTypeSystem n L act qf bil H₀)
    (ι : L ≃* omegaT) :
    Nonempty (H ≃* H₀) ∨ ∃ k : Fin 3, Nonempty (H ≃* twistModel S₀ ι k) := by
  obtain ⟨G⟩ := exists_glue hb.exists_eq_one S₀ S
  have : Group.IsPerfect omegaT := Cover.isPerfect_omegaT
  have : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := ι.symm.toMonoidHom) ι.symm.surjective
  rcases split_or_perfect G.π (G.π_surj hb) (fun _ => G.π_eq_one_iff) with ⟨K, hζK, hK⟩ | hE
  · obtain ⟨e⟩ := exists_mulEquiv_of_split hb G K hζK hK
    exact Or.inl ⟨e.symm⟩
  · obtain ⟨k, ⟨e⟩⟩ := exists_twistModel_of_perfect S₀ ι hE G.π (G.π_surj hb) G.π_ζ
      G.ζ_mem_center (fun _ => G.π_eq_one_iff) G.ζ_ne_one
    obtain ⟨e'⟩ := nonempty_mulEquiv_twist hb G
    exact Or.inr ⟨k, ⟨e'.trans e⟩⟩

theorem centralizer_cases
    {H H₀ : Type} [Group H] [Group H₀] [Finite H] [Finite H₀]
    (S : ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀ H)
    (S₀ : ExtraspecialTypeSystem 8 L₀ L₀.subtype q₀ bil₀ H₀) (ι : L₀ ≃* omegaT) :
    Nonempty (H ≃* H₀) ∨ ∃ k : Fin 3, Nonempty (H ≃* twistModel S₀ ι k) :=
  centralizer_cases_of_nondeg nondeg_bil₀ S S₀ ι

end CFSG.Sporadic.Co1Patterson
