module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJExcl
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] def CentralNoncentral3 (W : Type) [Group W] : Prop :=
  3 ∣ Nat.card (Subgroup.center W) ∧ ∃ x : W, x ^ 3 = 1 ∧ x ∉ Subgroup.center W

theorem centralNoncentral_congr {W W' : Type} [Group W] [Group W'] (e : W ≃* W')
    (h : CentralNoncentral3 W) : CentralNoncentral3 W' := by
  obtain ⟨h3, x, hx3, hxZ⟩ := h
  have hc : (Subgroup.center W).map e.toMonoidHom = Subgroup.center W' := Subgroup.map_center_eq e
  refine ⟨?_, e x, by rw [← map_pow, hx3, map_one], fun hex => hxZ ?_⟩
  · rw [← hc, Subgroup.card_map_of_injective e.injective]
    exact h3
  · rw [← hc] at hex
    obtain ⟨y, hy, hyx⟩ := hex
    have : y = x := e.injective hyx
    exact this ▸ hy

theorem exists_noncentral_of_le_tripleCover {W : Type} [Group W] {U : Subgroup W}
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6))) :
    ∃ x : W, x ^ 3 = 1 ∧ x ∉ Subgroup.center W := by
  obtain ⟨x, hx3, hxZ⟩ := Sec19.Item19Res4Proof.exists_noncentral_of_isTripleA6 hU
  refine ⟨x, by simpa using congrArg Subtype.val hx3, fun hc => hxZ ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.mp hc) g)

theorem IsCentralProductA6Covers.central_noncentral {W : Type} [Group W] [Finite W]
    (h : IsCentralProductA6Covers W) : CentralNoncentral3 W := by
  obtain ⟨U, V, -, -, hUV, hc, h3, hU, -⟩ := h
  refine ⟨?_, exists_noncentral_of_le_tripleCover hU⟩
  have hle : U ⊓ V ≤ Subgroup.center W := by
    intro x hx
    have hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
      have := Subgroup.commutator_mem_commutator hu hv
      rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hcen : (⊤ : Subgroup W) ≤ Subgroup.centralizer ({x} : Set W) := by
      rw [← hUV]
      refine sup_le (fun u hu => ?_) (fun v hv => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcomm u hu x hx.2
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm x hx.1 v hv).symm
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcen (Subgroup.mem_top g))
  rw [← h3]
  exact Subgroup.card_dvd_of_le hle

theorem IsA6CoverTimesA5.central_noncentral {W : Type} [Group W] [Finite W]
    (h : IsA6CoverTimesA5 W) : CentralNoncentral3 W := by
  obtain ⟨U, V, hUn, hVn, hint, hUV, hU, -⟩ := h
  refine ⟨?_, exists_noncentral_of_le_tripleCover hU⟩
  have hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
    have h1 : ⁅U, V⁆ ≤ U ⊓ V := Subgroup.commutator_le_inf U V
    have := h1 (Subgroup.commutator_mem_commutator hu hv)
    rw [hint, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  set ZU : Subgroup W := (Subgroup.center ↥U).map U.subtype with hZU
  have hle : ZU ≤ Subgroup.center W := by
    rintro _ ⟨z, hz, rfl⟩
    have hcen : (⊤ : Subgroup W) ≤ Subgroup.centralizer ({(z : W)} : Set W) := by
      rw [← hUV]
      refine sup_le (fun u hu => ?_) (fun v hv => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨u, hu⟩)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm z z.2 v hv).symm
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcen (Subgroup.mem_top g))
  have h3 : Nat.card ZU = 3 := by
    rw [hZU, Subgroup.card_map_of_injective U.subtype_injective]
    exact hU.1
  rw [← h3]
  exact Subgroup.card_dvd_of_le hle

theorem false_of_centralNoncentral_of_le {Γ : Type} [Group Γ] [Finite Γ] {Aq C E Z : Subgroup Γ}
    (hAp : IsPGroup 3 Aq)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (Aq : Set Γ) → w ^ 3 = 1 → w ∈ Aq)
    (hC3 : Nat.card C = 3) (hAeq : C ⊔ E = Aq)
    (hEZ : E ≤ Subgroup.centralizer (Z : Set Γ)) (hAZ : Aq ⊓ Z ≤ C)
    (hAN : Aq ≤ Subgroup.normalizer (Z : Set Γ)) (hZ : CentralNoncentral3 ↥Z) : False := by
  obtain ⟨h3, x, hx3, hxZ⟩ := hZ
  have key := forall_commute_of_three_dvd_card_center hAp hF3 hC3 hAeq hEZ hAZ hAN h3
  apply hxZ
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx3' : (x : Γ) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
  exact (key x x.2 hx3' y y.2).symm

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
