module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import Mathlib.GroupTheory.Complement
public import Mathlib.Data.Set.Card.Arithmetic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2, Proposition (2.1)

This file proves Peterfalvi (2.1).  No result from BG is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2

universe u

private theorem centralizerIn_le_left {G : Type u} [Group G] (H : Subgroup G) (g : G) :
    centralizerIn H g ≤ H := by
  intro x hx
  exact (Subgroup.mem_inf.mp hx).1

private theorem mem_elementCentralizer_commute {G : Type u} [Group G] {g c : G}
    (hc : c ∈ elementCentralizer g) : g * c = c * g := by
  unfold elementCentralizer at hc
  rw [Subgroup.mem_centralizer_iff] at hc
  exact hc g (by simp)

private theorem conjugateCosetPiece_subset_Hg {G : Type u} [Group G]
    {H : Subgroup G} {g x : G}
    (hnorm : normalizesSet (H : Set G) g) (hxH : x ∈ H) :
    conjugateCosetPiece H g x ⊆ subgroupCosetByElement H g := by
  intro z hz
  rcases hz with ⟨s, hs, rfl⟩
  rcases hs with ⟨c, hcC, rfl⟩
  refine ⟨x * c * (g * x⁻¹ * g⁻¹), ?_, ?_⟩
  · have hcH : c ∈ H := (Subgroup.mem_inf.mp hcC).1
    have hxinvH : x⁻¹ ∈ H := H.inv_mem hxH
    have hgx : g * x⁻¹ * g⁻¹ ∈ H := (hnorm x⁻¹).2 hxinvH
    exact H.mul_mem (H.mul_mem hxH hcH) hgx
  · simp [conjBy, mul_assoc]


private theorem exists_multiple_card_pow_eq_self {G : Type u} [Group G]
    (H : Subgroup G) (g : G) (hcoprime : Nat.Coprime (orderOf g) (Nat.card H)) :
    ∃ n : ℕ, Nat.card H ∣ n ∧ g ^ n = g := by
  rcases exists_pow_eq_self_of_coprime (x := g) (n := Nat.card H) hcoprime.symm with
    ⟨m, hm⟩
  refine ⟨Nat.card H * m, ⟨m, rfl⟩, ?_⟩
  simpa [pow_mul] using hm

private theorem conjugate_eq_of_piece_inter {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {g x y : G}
    (hcoprime : Nat.Coprime (orderOf g) (Nat.card H))
    (_hxH : x ∈ H) (_hyH : y ∈ H)
    (hz : (conjugateCosetPiece H g x ∩ conjugateCosetPiece H g y).Nonempty) :
    conjBy x g = conjBy y g := by
  rcases hz with ⟨z, hzx, hzy⟩
  rcases hzx with ⟨sx, hsx, hzsx⟩
  rcases hzy with ⟨sy, hsy, hzsy⟩
  rcases hsx with ⟨u, huC, hsx⟩
  rcases hsy with ⟨v, hvC, hsy⟩
  subst sx
  subst sy
  have heq : conjBy x (u * g) = conjBy y (v * g) := hzsx.symm.trans hzsy
  rcases exists_multiple_card_pow_eq_self H g hcoprime with ⟨n, hn_dvd, hgn⟩
  have hun : u ^ n = 1 := by
    rcases hn_dvd with ⟨k, rfl⟩
    have huH : u ∈ H := (Subgroup.mem_inf.mp huC).1
    have hu_sub : (⟨u, huH⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    have huG : u ^ Nat.card H = 1 := by
      exact Subtype.ext_iff.mp hu_sub
    rw [pow_mul, huG, one_pow]
  have hvn : v ^ n = 1 := by
    rcases hn_dvd with ⟨k, rfl⟩
    have hvH : v ∈ H := (Subgroup.mem_inf.mp hvC).1
    have hv_sub : (⟨v, hvH⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    have hvG : v ^ Nat.card H = 1 := by
      exact Subtype.ext_iff.mp hv_sub
    rw [pow_mul, hvG, one_pow]
  have hcommu : Commute u g := (mem_elementCentralizer_commute (Subgroup.mem_inf.mp huC).2).symm
  have hcommv : Commute v g := (mem_elementCentralizer_commute (Subgroup.mem_inf.mp hvC).2).symm
  have hpow := congrArg (fun t : G => t ^ n) heq
  have hxpow : (conjBy x (u * g)) ^ n = conjBy x g := by
    simp [conjBy, hcommu.mul_pow, hun, hgn]
  have hypow : (conjBy y (v * g)) ^ n = conjBy y g := by
    simp [conjBy, hcommv.mul_pow, hvn, hgn]
  simpa [hxpow, hypow] using hpow

private theorem left_coset_mem_centralizer_of_piece_inter {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {g x y : G}
    (hcoprime : Nat.Coprime (orderOf g) (Nat.card H))
    (hxH : x ∈ H) (hyH : y ∈ H)
    (hz : (conjugateCosetPiece H g x ∩ conjugateCosetPiece H g y).Nonempty) :
    x⁻¹ * y ∈ centralizerIn H g := by
  have hxy : conjBy x g = conjBy y g :=
    conjugate_eq_of_piece_inter hcoprime hxH hyH hz
  have hH : x⁻¹ * y ∈ H := H.mul_mem (H.inv_mem hxH) hyH
  have hcent : x⁻¹ * y ∈ elementCentralizer g := by
    unfold elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    simp [conjBy, mul_assoc] at hxy
    calc
      g * (x⁻¹ * y) = x⁻¹ * (x * (g * x⁻¹)) * y := by simp [mul_assoc]
      _ = x⁻¹ * (y * (g * y⁻¹)) * y := by rw [hxy]
      _ = x⁻¹ * y * g := by simp [mul_assoc]
  exact Subgroup.mem_inf.mpr ⟨hH, hcent⟩

private theorem conjugateCosetPiece_card {G : Type u} [Group G]
    (H : Subgroup G) (g x : G) :
    (conjugateCosetPiece H g x).ncard = Nat.card (centralizerIn H g) := by
  classical
  let e1 : G ≃ G := Equiv.mulRight g
  let e2 : G ≃ G := MulAut.conj x
  calc
    (conjugateCosetPiece H g x).ncard =
        (e2 '' (e1 '' (centralizerIn H g : Set G))).ncard := by
          congr
          ext z
          constructor
          · rintro ⟨s, hs, rfl⟩
            rcases hs with ⟨c, hc, rfl⟩
            exact ⟨c * g, ⟨c, hc, rfl⟩, rfl⟩
          · rintro ⟨s, ⟨c, hc, rfl⟩, rfl⟩
            exact ⟨c * g, ⟨c, hc, rfl⟩, rfl⟩
    _ = (e1 '' (centralizerIn H g : Set G)).ncard :=
      Set.ncard_image_of_injective _ e2.injective
    _ = (centralizerIn H g : Set G).ncard :=
      Set.ncard_image_of_injective _ e1.injective
    _ = Nat.card (centralizerIn H g) := rfl

private theorem subgroupCosetByElement_card {G : Type u} [Group G] (H : Subgroup G) (g : G) :
    (subgroupCosetByElement H g).ncard = Nat.card H := by
  classical
  let e : G ≃ G := Equiv.mulRight g
  calc
    (subgroupCosetByElement H g).ncard = (e '' (H : Set G)).ncard := by
      congr
      ext z
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, rfl⟩
    _ = (H : Set G).ncard := Set.ncard_image_of_injective _ e.injective
    _ = Nat.card H := rfl

private theorem natCard_centralizerIn_comap {G : Type u} [Group G]
    (H : Subgroup G) (g : G) :
    Nat.card ((centralizerIn H g).comap H.subtype) =
      Nat.card (centralizerIn H g) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨((x : H) : G), x.2⟩
      invFun := fun x =>
        ⟨⟨x.1, centralizerIn_le_left H g x.2⟩, x.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    ext
    rfl
  · intro x
    ext
    rfl

public theorem proposition_2_1 {G : Type u} [Group G] [Finite G]
    (g : G) (H : Subgroup G) :
    normalizesSet (H : Set G) g →
      Nat.Coprime (orderOf g) (Nat.card H) →
        finiteDisjointUnionOfConjugatePieces
          (subgroupCosetByElement H g) H g
          (Nat.card H / Nat.card (centralizerIn H g)) := by
  intro hnorm hcoprime
  classical
  let Csub : Subgroup H := (centralizerIn H g).comap H.subtype
  rcases Csub.exists_isComplement_left 1 with ⟨S, hScomp, hSone⟩
  let repsH : Finset H := (Set.toFinite S).toFinset
  let incl : H ↪ G := ⟨fun x => (x : G), Subtype.val_injective⟩
  let reps : Finset G := repsH.map incl
  have hCsub_card : Nat.card Csub = Nat.card (centralizerIn H g) := by
    simpa [Csub] using natCard_centralizerIn_comap H g
  have hS_card : Nat.card S = Nat.card H / Nat.card (centralizerIn H g) := by
    have hCsub_ne : Nat.card Csub ≠ 0 := by
      have hnonempty : Nonempty Csub := ⟨⟨1, by simp [Csub]⟩⟩
      have hpos : 0 < Nat.card Csub := Finite.card_pos_iff.mpr hnonempty
      exact Nat.ne_of_gt hpos
    have hmul : Nat.card Csub * Nat.card S = Nat.card H := by
      have := hScomp.card_mul_card
      simpa [mul_comm] using this
    have hS_card' : Nat.card S = Nat.card H / Nat.card Csub :=
      Nat.eq_div_of_mul_eq_right hCsub_ne hmul
    rw [hCsub_card] at hS_card'
    exact hS_card'
  have hdiv : Nat.card (centralizerIn H g) ∣ Nat.card H := by
    rw [← hCsub_card]
    refine ⟨Nat.card S, ?_⟩
    calc
      Nat.card H = Nat.card S * Nat.card Csub := by
        simpa [mul_comm] using hScomp.card_mul_card.symm
      _ = Nat.card Csub * Nat.card S := by rw [mul_comm]
  have hSfin : repsH.card = Nat.card S := by
    simp [repsH]
  have hReps_card : reps.card = Nat.card H / Nat.card (centralizerIn H g) := by
    dsimp [reps]
    rw [Finset.card_map, hSfin, hS_card]
  refine ⟨reps, ?_ , ?_ , ?_ , ?_⟩
  · exact hReps_card
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨xH, hxH, rfl⟩
    exact xH.2
  · intro x hx y hy hxy
    rcases Finset.mem_map.mp hx with ⟨xH, hxH, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨yH, hyH, rfl⟩
    refine Set.disjoint_left.2 ?_
    intro z hz hz'
    have hinter : (conjugateCosetPiece H g (xH : G) ∩ conjugateCosetPiece H g (yH : G)).Nonempty :=
      ⟨z, hz, hz'⟩
    have hcent : ((xH : G)⁻¹ * (yH : G)) ∈ centralizerIn H g :=
      left_coset_mem_centralizer_of_piece_inter hcoprime xH.2 yH.2 hinter
    have hxS : (xH : H) ∈ S := by
      simpa [repsH] using hxH
    have hyS : (yH : H) ∈ S := by
      simpa [repsH] using hyH
    have huniq := (Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hScomp) (yH : H)
    have hxprop : ((⟨xH, hxS⟩ : S) : H)⁻¹ * (yH : H) ∈ Csub := by
      change ((xH : G)⁻¹ * (yH : G)) ∈ centralizerIn H g
      exact hcent
    have hyprop : ((⟨yH, hyS⟩ : S) : H)⁻¹ * (yH : H) ∈ Csub := by
      simp [Csub]
    have hEqS : (⟨xH, hxS⟩ : S) = ⟨yH, hyS⟩ := huniq.unique hxprop hyprop
    have hEqH : (xH : H) = yH := by
      exact congrArg (fun s : S => (s : H)) hEqS
    exact hxy (by simpa using congrArg (fun z : H => (z : G)) hEqH)
  ·
    -- `K` is the union of the pieces indexed by the chosen representatives.
    let K : Set G := ⋃ x ∈ (reps : Set G), conjugateCosetPiece H g x
    have hpair : (reps : Set G).PairwiseDisjoint (fun x => conjugateCosetPiece H g x) := by
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨xH, hxH, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨yH, hyH, rfl⟩
      refine Set.disjoint_left.2 ?_
      intro z hz hz'
      have hinter : (conjugateCosetPiece H g (xH : G) ∩ conjugateCosetPiece H g (yH : G)).Nonempty :=
        ⟨z, hz, hz'⟩
      have hcent : ((xH : G)⁻¹ * (yH : G)) ∈ centralizerIn H g :=
        left_coset_mem_centralizer_of_piece_inter hcoprime xH.2 yH.2 hinter
      have hxS : (xH : H) ∈ S := by
        simpa [repsH] using hxH
      have hyS : (yH : H) ∈ S := by
        simpa [repsH] using hyH
      have huniq := (Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hScomp) (yH : H)
      have hxprop : ((⟨xH, hxS⟩ : S) : H)⁻¹ * (yH : H) ∈ Csub := by
        change ((xH : G)⁻¹ * (yH : G)) ∈ centralizerIn H g
        exact hcent
      have hyprop : ((⟨yH, hyS⟩ : S) : H)⁻¹ * (yH : H) ∈ Csub := by
        simp [Csub]
      have hEqS : (⟨xH, hxS⟩ : S) = ⟨yH, hyS⟩ := huniq.unique hxprop hyprop
      have hEqH : (xH : H) = yH := by
        exact congrArg (fun s : S => (s : H)) hEqS
      exact hxy (by simpa using congrArg (fun z : H => (z : G)) hEqH)
    have hKcard : K.ncard = reps.card * Nat.card (centralizerIn H g) := by
      rw [show K = ⋃ x ∈ (reps : Set G), conjugateCosetPiece H g x by rfl]
      rw [Set.Finite.ncard_biUnion (Set.toFinite (reps : Set G))
        (fun x _ => Set.toFinite (conjugateCosetPiece H g x)) hpair]
      rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite (reps : Set G))]
      rw [show ((↑reps : Set G).toFinite).toFinset = reps by
        exact Finset.finite_toSet_toFinset reps]
      exact Finset.sum_const_nat (s := reps)
        (f := fun x => (conjugateCosetPiece H g x).ncard)
        (m := Nat.card (centralizerIn H g)) (by
          intro x hx
          simpa using conjugateCosetPiece_card H g x)
    have hKcard' : K.ncard = Nat.card H := by
      simpa [hKcard, hReps_card] using (Nat.div_mul_cancel hdiv)
    have hHgcard : (subgroupCosetByElement H g).ncard = Nat.card H := by
      exact subgroupCosetByElement_card H g
    have hsubset : K ⊆ subgroupCosetByElement H g := by
      intro z hz
      simp [K] at hz
      rcases hz with ⟨x, hx, hz⟩
      exact conjugateCosetPiece_subset_Hg hnorm (by
        rcases Finset.mem_map.mp hx with ⟨xH, hxH, rfl⟩
        exact xH.2) hz
    have hEq : K = subgroupCosetByElement H g := by
      apply Set.eq_of_subset_of_ncard_le hsubset
      rw [hKcard', hHgcard]
    calc
      subgroupCosetByElement H g = K := hEq.symm
      _ = {z | ∃ x ∈ reps, z ∈ conjugateCosetPiece H g x} := by
        ext z
        simp [K]

end CFSG.Section2
