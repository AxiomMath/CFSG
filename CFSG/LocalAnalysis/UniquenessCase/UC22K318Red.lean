module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (le_or_eq_top_of_normal
  exists_pCore_not_le_centralizer le_centralizer_of_isPGroup_range pRank_le_of_le
  le_four_of_card_frattini)
open scoped commutatorElement Matrix

variable {L : Type} [Group L] [Finite L]

@[expose] def CriticalSection (X : Subgroup L) (q d : ℕ) (φ : L →* GL (Fin d) (ZMod q)) : Prop :=
  ∃ Q : Subgroup L, Q.Normal ∧ Q ≤ X ∧ IsPGroup q Q ∧ ¬ (⊤ : Subgroup L) ≤ centralizer (Q : Set L) ∧
    ∃ D : Subgroup Q, ∃ _ : D.Characteristic, D ≠ ⊥ ∧ (∀ x ∈ D, x ^ q = 1) ∧
      ⁅D, (⊤ : Subgroup Q)⁆ ≤ D ⊓ centralizer (D : Set Q) ∧
      (∀ x ∈ centralizer (D : Set Q), orderOf x = q → x ∈ D) ∧
      IsPGroup q (frattiniAction D).ker ∧ commutator D ≤ center D ∧ CFSG.pRank q D ≤ 3 ∧
      Nat.card (D ⧸ frattini D) = q ^ d ∧
      ∃ e : D ⧸ frattini D ≃* Multiplicative (Fin d → ZMod q),
        ∀ (g : L) (x y : D), ((y : Q) : L) = g * ((x : Q) : L) * g⁻¹ →
          (φ g : Matrix (Fin d) (Fin d) (ZMod q)) *ᵥ Multiplicative.toAdd (e (x : D ⧸ frattini D)) =
            Multiplicative.toAdd (e (y : D ⧸ frattini D))

theorem exists_criticalSection [Group.IsPerfect L] (X : Subgroup L) [X.Normal]
    (hXs : Group.IsSolvable X) (hX2 : CFSG.Open.pCoreOf 2 X = ⊥)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q X ≤ 3)
    (hcent : centralizer (X : Set L) ≤ X) (hs : IsSimpleGroup (L ⧸ X)) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card X ∧ ∃ d : ℕ, d ≤ 4 ∧
      ∃ φ : L →* GL (Fin d) (ZMod q), φ.ker ≤ X ∧ CriticalSection X q d φ := by
  classical
  have hXtop : X ≠ ⊤ := by
    intro hX
    obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial : Nontrivial (L ⧸ X)).exists_pair_ne
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [QuotientGroup.eq, hX]
    exact mem_top _
  obtain ⟨q, hqX, hnc⟩ := exists_pCore_not_le_centralizer hXs hcent hXtop
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqX
  have hqdvd : q ∣ Nat.card X := Nat.dvd_of_mem_primeFactors hqX
  have hq2 : q ≠ 2 := by
    rintro rfl
    apply hnc
    have hQ : ((CFSG.pCore 2 X).map X.subtype : Subgroup L) = ⊥ := hX2
    rw [hQ]
    intro g _
    rw [mem_centralizer_iff]
    intro x hx
    rw [SetLike.mem_coe, mem_bot] at hx
    rw [hx, one_mul, mul_one]
  haveI : Fact q.Prime := ⟨hq⟩
  let Q : Subgroup L := (CFSG.pCore q X).map X.subtype
  haveI : Q.Normal := ConjAct.normal_of_characteristic_of_normal
  have hQp : IsPGroup q Q := (CFSG.pCore_isPGroup (p := q) (G := X)).map X.subtype
  have hQX : Q ≤ X := map_subtype_le _
  have hQnt : Nontrivial Q := by
    rw [nontrivial_iff_ne_bot]
    intro hbot
    apply hnc
    intro g _
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Q := hx
    rw [hbot, mem_bot] at hx'
    rw [hx', one_mul, mul_one]
  obtain ⟨D, hDc, hDne, hDp, hDZ, hDΩ, hker⟩ := supercritical_witness hq2 hQp
  set α : L →* MulAut (D ⧸ frattini D) :=
    (frattiniAction D).comp (MulAut.conjNormal (H := Q)) with hα
  have hαX : α.ker ≤ X := by
    rcases le_or_eq_top_of_normal hXs hs α.ker with h | h
    · exact h
    exfalso
    apply hnc
    apply le_centralizer_of_isPGroup_range (q := q)
    refine hker.to_le ?_
    rintro _ ⟨g, rfl⟩
    have hg : α g = 1 := MonoidHom.mem_ker.1 (h ▸ mem_top g)
    exact MonoidHom.mem_ker.2 hg
  have hDq : IsPGroup q D := hQp.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDq
  obtain ⟨k, hk⟩ := (hDq.to_quotient (frattini D)).exists_card_eq
  have hexp : ∀ x : D, x ^ q = 1 := fun x => Subtype.ext (by simpa using hDp x x.2)
  have hclass : commutator D ≤ center D := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [mem_center_iff]
    intro z
    have hab : ⁅(a : Q), (b : Q)⁆ ∈ centralizer (D : Set Q) :=
      (hDZ (commutator_mem_commutator a.2 (mem_top (b : Q)))).2
    apply Subtype.ext
    have h1 := mem_centralizer_iff.1 hab (z : Q) z.2
    simpa [commutatorElement_def] using h1
  have hDrank : CFSG.pRank q D ≤ 3 := (pRank_le_of_le hq.one_lt hQX D).trans (hrank q hq hq2)
  have hk4 : k ≤ 4 := le_four_of_card_frattini hDq hexp hclass hDrank hk
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  refine ⟨q, hq, hq2, hqdvd, k, hk4, (elemAutEquivGL e).toMonoidHom.comp α, ?_, Q, inferInstance,
    hQX, hQp, hnc, D, hDc, hDne, hDp, hDZ, hDΩ, hker, hclass, hDrank, hk, e, ?_⟩
  · intro g hg
    apply hαX
    rw [MonoidHom.mem_ker] at hg ⊢
    apply (elemAutEquivGL e).injective
    rw [map_one]
    exact hg
  · intro g x y hxy
    have h1 := elemAutEquivGL_mulVec e (α g) (x : D ⧸ frattini D)
    rw [hα, MonoidHom.comp_apply, frattiniAction_mk] at h1
    have hy : (⟨MulAut.conjNormal g (x : Q),
        (MulAut.characteristic D (MulAut.conjNormal g) x).2⟩ : D) = y :=
      Subtype.ext (Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hxy.symm))
    rw [hy] at h1
    exact h1

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
