module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Tspec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Xbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ATwoConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Input

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

private theorem s16h_map_conj_one {G : Type*} [Group G] (L : Subgroup G) :
    L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
  ext x
  simp [Subgroup.mem_map]

theorem s16h_z3_exists_xbar_irr {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hc : Conc4_136W A t L)
    (hind : sSupIndep (conjSubs A (commSub (⊤ : Subgroup W) L)))
    (hs : Set.ncard {X : Subgroup (MulAut W) |
      ∃ φ ∈ A, X = L.map (MulAut.conj φ).toMonoidHom} = 2)
    (hL : Nat.card ↥L = 3) (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥) (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3)
    (htL : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) {T : Subgroup (MulAut W)} (hT : IsSylowIn 2 T A) :
    ∃ Xb : Subgroup (MulAut W), (∀ q ∈ A, ∀ y ∈ Xb, q * y * q⁻¹ ∈ Xb) ∧ IsElemAbelian 3 Xb ∧
      Xb ≤ ⁅A, A⁆ ∧ Nat.card ↥Xb = 3 ^ 2 ∧
      ∀ Y : Subgroup (MulAut W), Y ≤ Xb → T ≤ normalizer (Y : Set (MulAut W)) →
        Y = ⊥ ∨ Y = Xb := by
  classical
  obtain ⟨⟨x, hxA, hxL⟩, hpermAll⟩ :=
    c23a_two_conj (A := MulAut W) (Mb := A) (L := L) hs
  have hperm := (hpermAll x hxA hxL).2
  let L₂ : Subgroup (MulAut W) := L.map (MulAut.conj x).toMonoidHom
  have hmap_one : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L :=
    s16h_map_conj_one L
  have hne : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom ≠
      L.map (MulAut.conj x).toMonoidHom := by
    rw [hmap_one]
    exact hxL.symm
  obtain ⟨hcomm₀, hinf₀⟩ := s16h_conj_comm_inf_of_conc hc A.one_mem hxA hne
  rw [hmap_one] at hcomm₀ hinf₀
  have hcomm : ⁅L, L₂⁆ = ⊥ := hcomm₀
  have hinf : L ⊓ L₂ = ⊥ := hinf₀
  have hB : s16h_Z3Blocks A L L₂ x := s16h_z3_blocks hc hind hxA hxL hperm
  have hts := s16h_z3_t_spec hW hB hL hrk hfix htA htr htL
  have htinv : ∀ l ∈ L, t * l * t⁻¹ = l⁻¹ := hts.1
  have htc : ∀ l ∈ L₂, t * l = l * t := hts.2
  have hL3 : ∀ y ∈ L, y ^ 3 = 1 := by
    intro y hy
    have h := pow_card_eq_one' (x := (⟨y, hy⟩ : ↥L))
    rw [hL] at h
    simpa using congrArg Subtype.val h
  have hLder : L ≤ ⁅A, A⁆ :=
    s16h_bl_le_commutator_of_inverted htA (Conc4_136W.le hc) hL3 htinv
  obtain ⟨hder, hnorm, hEA, hcard⟩ :=
    s16h_z3_xbar hxA hB.eq hL hLder hB.perm hcomm hinf
  refine ⟨L ⊔ L₂, hnorm, hEA, hder, hcard, ?_⟩
  exact s16h_z3_xbar_irr hB.mem hB.eq hB.ne hL hB.perm hcomm hinf htA ht2 htinv htc hT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
