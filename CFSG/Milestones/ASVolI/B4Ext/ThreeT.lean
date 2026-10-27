module

public import CFSG.Milestones.ASVolI.B4Natural

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

section ThreeT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(CFSG.Open.StatedSL 3 K) →* ↥G}

@[expose] def burnsideB49x_hat (C : burnsideB49_Coord3 G U K π) (A : Subgroup (MulAut V)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  A.comap (burnsideB49_rhoHat C)

theorem burnsideB49x_card_hat (C : burnsideB49_Coord3 G U K π)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    (hπ : ∀ g : ↥G, ∃ γ, π γ = g) {A : Subgroup (MulAut V)} (hAG : A ≤ G) :
    Nat.card (burnsideB49x_hat C A) = Nat.card A := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun s : ↥(burnsideB49x_hat C A) => (⟨burnsideB49_rhoHat C s, s.2⟩ : ↥A)) ⟨?_, ?_⟩)
  · intro s t h
    have h' := congrArg (fun x : ↥A => (x : MulAut V)) h
    exact Subtype.ext (burnsideB49_rhoHat_injective C hreal h')
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := burnsideB49_rhoHat_surj C hπ a (hAG ha)
    refine ⟨⟨s, ?_⟩, Subtype.ext hs⟩
    show burnsideB49_rhoHat C s ∈ A
    rw [hs]
    exact ha

theorem burnsideB49x_hat_comm (C : burnsideB49_Coord3 G U K π)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    ∀ b ∈ burnsideB49x_hat C A, ∀ b' ∈ burnsideB49x_hat C A, b * b' = b' * b := by
  intro b hb b' hb'
  apply burnsideB49_rhoHat_injective C hreal
  rw [map_mul, map_mul]
  exact hA.1 _ hb _ hb'

theorem burnsideB49x_hat_sq (C : burnsideB49_Coord3 G U K π)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    ∀ b ∈ burnsideB49x_hat C A, b * b = 1 := by
  intro b hb
  apply burnsideB49_rhoHat_injective C hreal
  rw [map_mul, map_one, ← pow_two]
  exact hA.2 _ hb

theorem burnsideB49x_hat_ne_bot (C : burnsideB49_Coord3 G U K π)
    (hπ : ∀ g : ↥G, ∃ γ, π γ = g) {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA : A ≠ ⊥) :
    burnsideB49x_hat C A ≠ ⊥ := by
  intro h
  apply hA
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨s, hs⟩ := burnsideB49_rhoHat_surj C hπ a (hAG ha)
  have hs' : s ∈ burnsideB49x_hat C A := by
    show burnsideB49_rhoHat C s ∈ A
    rw [hs]
    exact ha
  rw [h, Subgroup.mem_bot] at hs'
  rw [Subgroup.mem_bot, ← hs, hs', map_one]

theorem burnsideB49x_card_fixU_le [Finite K] (C : burnsideB49_Coord3 G U K π)
    (A : Subgroup (MulAut V)) :
    Nat.card ↥(fixV A ⊓ U) ≤ Nat.card {x : Fin 3 → K // ∀ s ∈ burnsideB49x_hat C A,
      ((C.σ s : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x = x} := by
  refine Nat.card_le_card_of_injective
    (fun u => ⟨Multiplicative.toAdd (C.β₀ ⟨(u : V), (Subgroup.mem_inf.1 u.2).2⟩), ?_⟩) ?_
  · intro s hs
    have hu : (burnsideB49_rhoHat C s) (u : V) = u := (Subgroup.mem_inf.1 u.2).1 _ hs
    have hmem : ((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) (u : V) ∈ U := by
      rw [← burnsideB49_rhoHat_apply, hu]
      exact (Subgroup.mem_inf.1 u.2).2
    have h1 := C.hβe (C.σ s) ⟨(u : V), (Subgroup.mem_inf.1 u.2).2⟩ hmem
    have h2 : (⟨((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) (u : V), hmem⟩ :
        ↥U) = ⟨(u : V), (Subgroup.mem_inf.1 u.2).2⟩ := Subtype.ext hu
    rw [h2] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at h3
    exact h3.symm
  · intro u u' h
    have h' := congrArg Subtype.val h
    have h'' := C.hβb.1 (Multiplicative.toAdd.injective h')
    exact Subtype.ext (congrArg (fun x : ↥U => (x : V)) h'')

theorem burnsideB49x_card_fixV_le [Finite V] [Finite K] (C : burnsideB49_Coord3 G U K π)
    (A : Subgroup (MulAut V)) :
    Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV A ⊓ U) * Nat.card {x : Fin 3 → K //
      ∀ s ∈ burnsideB49x_hat C A, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x} := by
  let f : ↥(fixV A) →* Multiplicative (Fin 3 → K) := C.qV.comp (fixV A).subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : f.ker = U.subgroupOf (fixV A) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact C.hker _
  have hker2 : Nat.card f.ker = Nat.card ↥(fixV A ⊓ U) := by
    rw [hker, ← Subgroup.card_map_of_injective (f := (fixV A).subtype)
      (Subgroup.subtype_injective _), Subgroup.subgroupOf_map_subtype, inf_comm]
  have hrange : Nat.card f.range ≤ Nat.card {x : Fin 3 → K //
      ∀ s ∈ burnsideB49x_hat C A, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x} := by
    refine Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd (y : _), ?_⟩) ?_
    · intro s hs
      obtain ⟨v, hv⟩ := y.2
      rw [← hv]
      show (s : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (C.qV (v : V))) =
        Multiplicative.toAdd (C.qV (v : V))
      have hfix : burnsideB49_rhoHat C s (v : V) = v := v.2 _ hs
      have h2 := burnsideB49_qV_rhoHat C s (v : V)
      rw [hfix] at h2
      have h3 := congrArg Multiplicative.toAdd h2
      rw [toAdd_ofAdd] at h3
      exact h3.symm
    · intro y y' h
      have h' := congrArg (fun x : {x : Fin 3 → K //
        ∀ s ∈ burnsideB49x_hat C A, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x} =>
          (x : Fin 3 → K)) h
      exact Subtype.ext (Multiplicative.toAdd.injective h')
  calc Nat.card ↥(fixV A) = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ _ := by
      rw [hker2]
      exact Nat.mul_le_mul_left _ hrange

theorem burnsideB49x_card_V [Finite V] [Finite K] (C : burnsideB49_Coord3 G U K π)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π) :
    Nat.card V = Nat.card K ^ 6 := by
  have h1 := Subgroup.card_ker_mul_card_range C.qV
  have hker : C.qV.ker = U := by
    ext v
    rw [MonoidHom.mem_ker]
    exact C.hker v
  have hrange : C.qV.range = ⊤ := MonoidHom.range_eq_top.2 C.hqs
  rw [hker, hrange, Subgroup.card_top, burnsideB49_card_U hreal] at h1
  rw [← h1]
  change Nat.card K ^ 3 * Nat.card (Fin 3 → K) = _
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_add]

end ThreeT

end CFSG.ASVolI
