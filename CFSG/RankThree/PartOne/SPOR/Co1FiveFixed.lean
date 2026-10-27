module

public import CFSG.RankThree.PartOne.S11c.SporadicFiveFixed
public import CFSG.RankThree.PartOne.SPOR.SylowCentre
public import CFSG.RankThree.PartOne.SPOR.Co1SylowSound
public import CFSG.RankThree.PartOne.SPOR.Co1SylowCheck
public import CFSG.RankThree.PartOne.SPOR.Co1Planes
public import CFSG.ClassicalGroups.Unitary.Simple

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.RankThree.PartOne.HNRed

theorem co1_sylow_centre :
    ∃ (P : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1))
      (x : CFSG.Blueprint.NativeSporadic.Carrier .Co1),
      Nat.card P = 625 ∧ x ^ 5 = 1 ∧
        ∀ z ∈ P, (∀ y ∈ P, z * y = y * z) → z ∈ Subgroup.zpowers x := by
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1) :=
    CFSG.Sporadic.Co1.fam_co1_simplicity.1
  exact co1Sylow_sound co1Iota co1Iota_injective co1_base_rep co1_base_mem co1_sylow_check

theorem exists_conj_of_allInner {A T : Type} [Group A] [Group T] (e : T ≃* A)
    (hin : ∀ α : MulAut A, ∃ g : A, α = MulAut.conj g) (β : MulAut T) :
    ∃ b : T, MulAut.conj b = β := by
  obtain ⟨g, hg⟩ := hin ((e.symm.trans β).trans e)
  refine ⟨e.symm g, ?_⟩
  ext x
  have h1 := congrArg (fun φ : MulAut A => φ (e x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem co1FiveFixed :
    Co1FiveFixed := by
  have hfin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1) :=
    CFSG.Sporadic.Co1.fam_co1_simplicity.1
  obtain ⟨P, x, hP, hx, hZ⟩ := co1_sylow_centre
  intro T _ _ hs hnab ⟨eT⟩ Λ _ _ β _ K hfix
  have := hs
  obtain ⟨hord, ⟨hKle, -⟩, hmodel⟩ := hfix
  obtain ⟨b, hb⟩ := exists_conj_of_allInner eT (fun α => allInner_Co1 α) β
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) :=
    conj_injective_of_trivial_center (trivial_center_of_simple hnab)
  have hbord : orderOf b = 5 := by
    have h1 := orderOf_injective (MulAut.conj : T →* MulAut T) hinj b
    rw [hb] at h1
    rw [← h1]
    exact hord
  have hKc : ∀ y ∈ K, b * y = y * b := by
    refine commute_of_conj_fixed fun y hy => ?_
    rw [hb]
    exact hKle hy
  have hKcard : Nat.card K = 126000 :=
    (CFSG.RankThree.Classical.unitary_three_five_model K hmodel).1
  have hKs : IsSimpleGroup K := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity K 3 5 1 hmodel).2
  have hKcen : ∀ k ∈ K, (∀ l ∈ K, k * l = l * k) → k = 1 := by
    have hnabK : ∃ a b : K, a * b ≠ b * a :=
      not_commutative_of_simple_of_not_prime (by rw [hKcard]; norm_num)
    intro k hk hkc
    have := trivial_center_of_simple hnabK ⟨k, hk⟩ (fun l => Subtype.ext (hkc l l.2))
    exact congrArg Subtype.val this
  have hcardT : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Co1) =
      5 ^ 4 * 6652442890469376 := by
    have h : Nat.card CFSG.Blueprint.NativeSporadic.Co1 = 4157776806543360000 :=
      CFSG.Sporadic.Co1.card_Co1
    exact h.trans (by norm_num)
  have hbo : orderOf (eT b) = 5 := (orderOf_injective eT.toMonoidHom eT.injective b).trans hbord
  refine no_sylow_five_centre (T := CFSG.Blueprint.NativeSporadic.Carrier .Co1)
    (m := 6652442890469376) hcardT (by norm_num) hP hx hZ (b := eT b) hbo
    (K := K.map eT.toMonoidHom) ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    show eT b * eT y = eT y * eT b
    rw [← map_mul, ← map_mul, hKc y hy]
  · rw [Subgroup.card_map_of_injective eT.injective, hKcard]
    norm_num
  · rintro _ ⟨k, hk, rfl⟩ hkc
    have h1 : k = 1 := by
      apply hKcen k hk
      intro l hl
      apply eT.injective
      rw [map_mul, map_mul]
      exact hkc (eT l) ⟨l, hl, rfl⟩
    rw [h1, map_one]

end CFSG.RankThree.PartOne.SPOR
