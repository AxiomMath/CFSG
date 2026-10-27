module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralCoverBilinear

public noncomputable section

open scoped commutatorElement IsMulCommutative Pointwise

namespace CFSG.ShultStronglyClosedTI

@[expose] def CoverDerivedIrreducible {J : Type*} [Group J] (Q T : Subgroup J)
    (hT : T ≤ Subgroup.normalizer (Q : Set J)) : Prop :=
  ∀ R : Subgroup (commutator Q),
    (∀ (t : T) (w : commutator Q), w ∈ R → coverDerivedAction Q T hT t w ∈ R) →
    R = ⊥ ∨ R = ⊤

@[expose] def centralCoverMixedRadical {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G)
    (hc : f.ker ≤ Subgroup.center G) (hq : commutator H ≤ Subgroup.center H) :
    Subgroup (commutator H) := by
  let := subgroup_commutative_of_le_center ((centralCover_third_le_ker f hq).trans hc)
  exact (centralCoverMixedPairing f hf hk hc hq).ker

theorem centralCoverMixedRadical_mem {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G)
    (hc : f.ker ≤ Subgroup.center G) (hq : commutator H ≤ Subgroup.center H)
    (w : commutator H) : w ∈ centralCoverMixedRadical f hf hk hc hq ↔
      ∀ v : Abelianization H, centralCoverMixedPairing f hf hk hc hq w v = 1 := by
  change (centralCoverMixedPairing f hf hk hc hq w = 1) ↔ _
  exact ⟨fun h v => congrArg (fun k => k v) h, fun h => MonoidHom.ext h⟩

theorem centralCoverMixedRadical_invariant {E J : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] [Group J] (η : E →* J) (hη : Function.Surjective η)
    (hc : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) (Q : Sylow 2 J)
    (hq : commutator (Q : Subgroup J) ≤ Subgroup.center (Q : Subgroup J))
    (T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) :
    let f := coverPreimageMap η (Q : Subgroup J)
    let hf := coverPreimageMap_surjective η hη (Q : Subgroup J)
    let hk := coverPreimageMap_ker_le_derived η hη hp Q hc
    let hfc := coverPreimageMap_ker_central η (Q : Subgroup J) hc
    ∀ (t : T) (w : commutator (Q : Subgroup J)),
      w ∈ centralCoverMixedRadical f hf hk hfc hq →
      coverDerivedAction (Q : Subgroup J) T hT t w ∈ centralCoverMixedRadical f hf hk hfc hq := by
  dsimp only
  intro t w hw
  rw [centralCoverMixedRadical_mem] at hw ⊢
  intro v
  let a := coverNormalizerAction (Q : Subgroup J) T hT
  let v' := coverAbelianAction (Q : Subgroup J) T hT t⁻¹ v
  have hv : coverAbelianAction (Q : Subgroup J) T hT t v' = v := by
    change (coverAbelianAction (Q : Subgroup J) T hT t *
      coverAbelianAction (Q : Subgroup J) T hT t⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hv]
  have heq := centralCoverMixedPairing_invariant
    (coverPreimageMap η (Q : Subgroup J)) (coverPreimageMap_surjective η hη (Q : Subgroup J))
    (coverPreimageMap_ker_le_derived η hη hp Q hc)
    (coverPreimageMap_ker_central η (Q : Subgroup J) hc) hq
    (centralCoverLiftAction η hη hc (Q : Subgroup J) T hT t) (a t)
    (centralCoverLiftAction_equivariant η hη hc (Q : Subgroup J) T hT t)
    (fun x hx => centralCoverLiftAction_fixes_kernel η hη hc (Q : Subgroup J) T hT t ⟨x, hx⟩) w v'
  exact heq.trans (hw v')

theorem centralCover_classTwo_of_radical_top {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ commutator G)
    (hc : f.ker ≤ Subgroup.center G) (hq : commutator H ≤ Subgroup.center H)
    (hR : centralCoverMixedRadical f hf hk hc hq = ⊤) :
    commutator G ≤ Subgroup.center G := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  apply le_bot_iff.mp
  apply Subgroup.commutator_le.mpr
  intro r hr s _
  have hmem : derivedHom f ⟨r, hr⟩ ∈ centralCoverMixedRadical f hf hk hc hq := by
    rw [hR]
    trivial
  have h := (centralCoverMixedRadical_mem f hf hk hc hq _).mp hmem (coverAbelianProjection f s)
  exact (centralCoverMixedPairing_apply f hf hk hc hq ⟨r, hr⟩ s).symm.trans (congrArg Subtype.val h)

theorem cover_centralizer_image_mem {E J : Type*} [Group E] [Group J]
    (η : E →* J) (hη : Function.Surjective η) (Q : Subgroup J) {x : E}
    (hx : x ∈ Subgroup.centralizer (Q.comap η : Set E)) :
    η x ∈ Subgroup.centralizer (Q : Set J) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  obtain ⟨z, hz⟩ := hη y
  have hzp : z ∈ Q.comap η := by change η z ∈ Q; rw [hz]; exact hy
  have h := congrArg η (Subgroup.mem_centralizer_iff.mp hx z hzp)
  simpa [hz] using h

theorem centralCover_centralizer_eq_of_radical_bot {E J : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] [Group J] (η : E →* J) (hη : Function.Surjective η)
    (hc : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) (Q : Sylow 2 J)
    (hq : commutator (Q : Subgroup J) ≤ Subgroup.center (Q : Subgroup J))
    (hcent : Subgroup.centralizer (Q : Set J) =
      (commutator (Q : Subgroup J)).map (Q : Subgroup J).subtype) :
    let f := coverPreimageMap η (Q : Subgroup J)
    let hf := coverPreimageMap_surjective η hη (Q : Subgroup J)
    let hk := coverPreimageMap_ker_le_derived η hη hp Q hc
    let hfc := coverPreimageMap_ker_central η (Q : Subgroup J) hc
    centralCoverMixedRadical f hf hk hfc hq = ⊥ →
      Subgroup.centralizer ((Q : Subgroup J).comap η : Set E) = η.ker := by
  dsimp only
  intro hR
  let P := (Q : Subgroup J).comap η
  let f := coverPreimageMap η (Q : Subgroup J)
  have hf := coverPreimageMap_surjective η hη (Q : Subgroup J)
  have hk := coverPreimageMap_ker_le_derived η hη hp Q hc
  have hfc := coverPreimageMap_ker_central η (Q : Subgroup J) hc
  have hR' : centralCoverMixedRadical f hf hk hfc hq = ⊥ := hR
  apply le_antisymm
  · intro x hx
    have himage := cover_centralizer_image_mem η hη (Q : Subgroup J) hx
    change η x ∈ Subgroup.centralizer (Q : Set J) at himage
    rw [hcent] at himage
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp himage
    obtain ⟨r, hfr⟩ := derivedHom_surjective f hf ⟨w, hw⟩
    have hrη : η r.val.val = η x := (congrArg (fun z : commutator (Q : Subgroup J) =>
      z.val.val) hfr).trans hwx
    have hxP : x ∈ P := by
      change η x ∈ (Q : Subgroup J)
      rw [← hrη]
      exact r.val.property
    let xp : P := ⟨x, hxP⟩
    have hxp : xp ∈ commutator P := by
      have hker : r.val⁻¹ * xp ∈ f.ker := by
        change f (r.val⁻¹ * xp) = 1
        apply Subtype.ext
        simp only [map_mul, map_inv]
        change (η r.val.val)⁻¹ * η x = 1
        rw [hrη, inv_mul_cancel]
      have hmult := (commutator P).mul_mem r.property (hk hker)
      simpa [mul_assoc] using hmult
    let rp : commutator P := ⟨xp, hxp⟩
    have hrad : derivedHom f rp ∈ centralCoverMixedRadical f hf hk hfc hq := by
      rw [centralCoverMixedRadical_mem]
      intro v
      obtain ⟨s, rfl⟩ := coverAbelianProjection_surjective f hf v
      apply Subtype.ext
      rw [centralCoverMixedPairing_apply]
      apply Subtype.ext
      have hcomm : Commute x s.val := (Subgroup.mem_centralizer_iff.mp hx s.val s.property).symm
      exact hcomm.commutator_eq
    have hz : derivedHom f rp = 1 := by simpa [hR'] using hrad
    exact congrArg (fun z : commutator (Q : Subgroup J) => z.val.val) hz
  · exact hc.trans (Subgroup.center_le_centralizer _)

theorem all_Sylow_centralizers_of_one {E : Type*} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime] (C : Subgroup E) (hc : C ≤ Subgroup.center E)
    (P : Sylow p E) (hP : Subgroup.centralizer (P : Set E) = C) :
    ∀ S : Sylow p E, Subgroup.centralizer (S : Set E) = C := by
  intro S
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq E P S
  apply le_antisymm
  · intro x hx
    have hconj : g⁻¹ * x * g ∈ Subgroup.centralizer (P : Set E) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      have hy' : g * y * g⁻¹ ∈ (g • P : Sylow p E) := by
        change g * y * g⁻¹ ∈ ((g • P : Sylow p E) : Subgroup E)
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P : Subgroup E) hy
      have h := Subgroup.mem_centralizer_iff.mp hx _ hy'
      have heq := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using heq
    rw [hP] at hconj
    have hz := hc hconj
    have hcomm : (g⁻¹ * x * g) * g⁻¹ = g⁻¹ * (g⁻¹ * x * g) :=
      (Subgroup.mem_center_iff.mp hz g⁻¹).symm
    have hxeq : x = g⁻¹ * x * g := by
      have heq := congrArg (fun z => g * z) hcomm
      simpa [mul_assoc] using heq
    exact hxeq ▸ hconj
  · exact hc.trans (Subgroup.center_le_centralizer _)

theorem central_two_cover_irreducible_derived_Sylow_centralizer {E J : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] [Group J] [Finite J]
    (η : E →* J) (hη : Function.Surjective η)
    (hc : η.ker ≤ Subgroup.center E) (hp : IsPGroup 2 η.ker) (hne : η.ker ≠ ⊥)
    (Q : Sylow 2 J) (hq : commutator (Q : Subgroup J) ≤ Subgroup.center (Q : Subgroup J))
    [IsElementaryAbelian 2 (commutator (Q : Subgroup J))]
    [IsElementaryAbelian 2 (Abelianization (Q : Subgroup J))]
    (_hW : commutator (Q : Subgroup J) ≠ ⊥)
    (hcent : Subgroup.centralizer (Q : Set J) =
      (commutator (Q : Subgroup J)).map (Q : Subgroup J).subtype)
    (T : Subgroup J) (hT : T ≤ Subgroup.normalizer (Q : Set J)) (hodd : Odd (Nat.card T))
    (hirr : CoverDerivedIrreducible (Q : Subgroup J) T hT)
    (habelian : ∀ b : Additive (Abelianization (Q : Subgroup J)) →+
      Additive (Abelianization (Q : Subgroup J)) →+ ZMod 2,
      CoverAbelianInvariant (Q : Subgroup J) T hT b → b = 0) :
    (∀ P : Sylow 2 E, Subgroup.centralizer (P : Set E) = η.ker) ∧
      η.ker = Subgroup.center E := by
  let f := coverPreimageMap η (Q : Subgroup J)
  have hf := coverPreimageMap_surjective η hη (Q : Subgroup J)
  have hk := coverPreimageMap_ker_le_derived η hη hp Q hc
  have hfc := coverPreimageMap_ker_central η (Q : Subgroup J) hc
  let R := centralCoverMixedRadical f hf hk hfc hq
  have hRinv := centralCoverMixedRadical_invariant η hη hc hp Q hq T hT
  have hRbot : R = ⊥ := by
    rcases hirr R hRinv with h | h
    · exact h
    · exact False.elim (hne (centralCover_classTwo_abelian_obstruction η hη hc hp Q T hT
        hodd habelian (centralCover_classTwo_of_radical_top f hf hk hfc hq h)))
  have hP := centralCover_centralizer_eq_of_radical_bot η hη hc hp Q hq hcent hRbot
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨all_Sylow_centralizers_of_one η.ker hc (centralCoverPreimageSylow η hη hp Q) hP, ?_⟩
  apply le_antisymm hc
  rw [← hP]
  exact Subgroup.center_le_centralizer _

end CFSG.ShultStronglyClosedTI
