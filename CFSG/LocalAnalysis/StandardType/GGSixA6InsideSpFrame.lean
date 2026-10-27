module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoBstar
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.A6InsideSp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Polynomial Module CFSG.RankThree.Classical

theorem exists_elemAbelian_le_selfCentralizing {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {B : Subgroup G} (hB : IsElemAbelian p B) :
    ∃ E : Subgroup G, B ≤ E ∧ IsElemAbelian p E ∧
      ∀ Z : G, (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ p = 1 → Z ∈ E := by
  classical
  let S : Set (Subgroup G) := {E | B ≤ E ∧ IsElemAbelian p E}
  have hSne : S.Nonempty := ⟨B, le_rfl, hB⟩
  obtain ⟨E, hES, hEmax⟩ := Set.exists_max_image S (fun E => Nat.card E) (Set.toFinite S) hSne
  obtain ⟨hBE, hE⟩ := hES
  refine ⟨E, hBE, hE, fun Z hZ hZp => ?_⟩
  let E' : Subgroup G := E ⊔ Subgroup.zpowers Z
  have hEE' : E ≤ E' := le_sup_left
  have hE' : IsElemAbelian p E' := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hE
      (CFSG.Open.isElemAbelian_zpowers hZp) ?_
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Commute.zpow_right (hZ a ha).symm k
  have hE'S : E' ∈ S := ⟨hBE.trans hEE', hE'⟩
  have hcard : Nat.card E' ≤ Nat.card E := hEmax E' hE'S
  have hEq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
  have hZmem : Z ∈ E' := Subgroup.mem_sup_right (Subgroup.mem_zpowers Z)
  rw [hEq]
  exact hZmem

theorem exists_frame_two {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2) {E : Subgroup (StatedSp n K)} (hE : IsElemAbelian 3 E)
    (hEsc : ∀ Z : StatedSp n K, (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L) (ζ : L),
      Module.finrank K L = 2 ∧ IsPrimitiveRoot ζ 3 ∧ Nonempty (ChoiceTwo.SpFrame K n ζ E) := by
  classical
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hne : ¬ IsUnit (cyclotomic 3 K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero 3 K),
      natDegree_cyclotomic, Nat.totient_prime Nat.prime_three]
    norm_num
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero 3 K)
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hE3 : ∀ Y ∈ E, Y ^ 3 = 1 := fun Y hY => hE.2 Y hY
  have hEc : ∀ Y ∈ E, ∀ Y' ∈ E, Y * Y' = Y' * Y := fun Y hY Y' hY' =>
    CFSG.Open.IsElemAbelian.comm hE hY hY'
  obtain ⟨F⟩ := ChoiceTwo.exists_frame hK hgd hE3 hEc hEsc
  refine ⟨AdjoinRoot g, inferInstance, inferInstance, (CoordSL.rootPB g).finite,
    AdjoinRoot.root g, ?_, ?_, ⟨F⟩⟩
  · rw [(CoordSL.rootPB g).finrank]
    exact SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) hpK hgd (by rw [hK])
  · exact NSFrame.root_isPrimitiveRoot Nat.prime_three hpK hgd

theorem card_eq_card_exps {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type}
    [Field L] [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)
    (hζo : IsPrimitiveRoot ζ 3) {B : Subgroup (StatedSp n K)} (hBE : B ≤ E) :
    Nat.card B = Nat.card {f : Fin F.s → ZMod 3 // F.tor f ∈ B} := by
  classical
  let e : {f : Fin F.s → ZMod 3 // F.tor f ∈ B} → B := fun f => ⟨F.tor f.1, f.2⟩
  have hinj : Function.Injective e := by
    intro f f' hff'
    have htor : F.tor f.1 = F.tor f'.1 := congrArg Subtype.val hff'
    have hfun : ∀ d, ChoiceTwo.torE ζ f.1 d = ChoiceTwo.torE ζ f'.1 d := by
      intro d
      have h1 := F.tor_acts f.1 d
      have h2 := F.tor_acts f'.1 d
      rw [← htor] at h2
      exact F.Φ.injective (h1.symm.trans h2)
    exact Subtype.ext (ChoiceTwo.torE_injective hζo hfun)
  have hsurj : Function.Surjective e := by
    intro b
    obtain ⟨f, hf⟩ := F.mem_tor b.1 (hBE b.2)
    refine ⟨⟨f, ?_⟩, ?_⟩
    · rw [hf]
      exact b.2
    · exact Subtype.ext hf
  exact (Nat.card_eq_of_bijective e ⟨hinj, hsurj⟩).symm

end CFSG.StandardType.A6InsideSp
