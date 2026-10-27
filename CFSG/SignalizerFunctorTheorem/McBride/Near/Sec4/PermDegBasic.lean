module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Defs

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {H : Type*} [Group H]

theorem exists_injective_perm_fin (H : Type*) [Group H] [Finite H] :
    ∃ n, ∃ f : H →* Equiv.Perm (Fin n), Function.Injective f := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin H
  exact ⟨n, e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H H),
    e.permCongrHom.injective.comp (MulAction.toPerm_injective (α := H) (β := H))⟩

theorem nontrivial_of_not_isMulCommutative {J : Type*} [Group J] (h : ¬ IsMulCommutative J) :
    Nontrivial J := by
  by_contra hJ
  rw [not_nontrivial_iff_subsingleton] at hJ
  exact h inferInstance

theorem permDeg_le_of_injective {X : Type*} [Finite X] (f : H →* Equiv.Perm X)
    (hf : Function.Injective f) : permDeg H ≤ Nat.card X := by
  let e : X ≃ Fin (Nat.card X) := Finite.equivFin X
  exact Nat.sInf_le ⟨e.permCongrHom.toMonoidHom.comp f, e.permCongrHom.injective.comp hf⟩

theorem exists_injective_permDeg [Finite H] :
    ∃ f : H →* Equiv.Perm (Fin (permDeg H)), Function.Injective f := by
  obtain ⟨n, hn⟩ := exists_injective_perm_fin H
  exact Nat.sInf_mem (s := {n : ℕ | ∃ f : H →* Equiv.Perm (Fin n), Function.Injective f})
    ⟨n, hn⟩

theorem permDeg_congr {H' : Type*} [Group H'] [Finite H] [Finite H'] (e : H ≃* H') :
    permDeg H = permDeg H' := by
  refine le_antisymm ?_ ?_
  · obtain ⟨f, hf⟩ := exists_injective_permDeg (H := H')
    simpa using permDeg_le_of_injective (f.comp e.toMonoidHom) (hf.comp e.injective)
  · obtain ⟨f, hf⟩ := exists_injective_permDeg (H := H)
    simpa using permDeg_le_of_injective (f.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)

theorem permDeg_pi_le {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, Group (G i)]
    [∀ i, Finite (G i)] : permDeg (∀ i, G i) ≤ ∑ i, permDeg (G i) := by
  choose f hf using fun i => exists_injective_permDeg (H := G i)
  let F : (∀ i, G i) →* Equiv.Perm (Σ i, Fin (permDeg (G i))) :=
    (Equiv.Perm.sigmaCongrRightHom (fun i => Fin (permDeg (G i)))).comp
      (MonoidHom.pi fun i => (f i).comp (Pi.evalMonoidHom G i))
  have hF : Function.Injective F := by
    intro x y h
    have h' := Equiv.Perm.sigmaCongrRightHom_injective h
    funext i
    exact hf i (congrFun h' i)
  simpa [Nat.card_sigma] using permDeg_le_of_injective F hF

theorem two_mul_permDeg_le_card (J : Type*) [Group J] [Finite J] [IsSimpleGroup J]
    (hnc : ¬ IsMulCommutative J) : 2 * permDeg J ≤ Nat.card J := by
  have hne : Nat.card J ≠ 1 := by
    intro h
    have : Subsingleton J := (Nat.card_eq_one_iff_unique.mp h).1
    exact hnc inferInstance
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpd
  set A : Subgroup J := Subgroup.zpowers g with hA
  have hAcard : Nat.card A = p := by rw [hA, Nat.card_zpowers, hg]
  have hAtop : A ≠ ⊤ := by
    intro htop
    refine hnc (IsMulCommutative.of_comm fun x y => ?_)
    have hx : x ∈ A := htop ▸ Subgroup.mem_top x
    have hy : y ∈ A := htop ▸ Subgroup.mem_top y
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self g a b).eq
  have hker : (MulAction.toPermHom J (J ⧸ A)).ker = ⊥ := by
    rw [← Subgroup.normalCore_eq_ker]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ A.normalCore_le)) hAtop
  have hinj : Function.Injective (MulAction.toPermHom J (J ⧸ A)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have h1 := permDeg_le_of_injective _ hinj
  have h2 : Nat.card (J ⧸ A) = A.index := A.index_eq_card.symm
  have h3 := A.card_mul_index
  rw [hAcard] at h3
  have h4 : 2 ≤ p := hp.two_le
  calc 2 * permDeg J ≤ p * A.index := Nat.mul_le_mul h4 (h2 ▸ h1)
    _ = Nat.card J := h3

end CFSG.SignalizerFunctorTheorem.McBride.Near
