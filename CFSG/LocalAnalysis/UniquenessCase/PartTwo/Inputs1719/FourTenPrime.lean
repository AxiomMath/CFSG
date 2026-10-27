module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenBasic
import CFSG.LocalAnalysis.WeakClosure81.GenEiConj
import CFSG.LocalAnalysis.WeakClosure81.PGLTwoPrimePrintedRelativeGeneration
import CFSG.LocalAnalysis.WeakClosure81.PSLTwoPrimeE1Generation
import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompL2
import CFSG.Quasithin.Background.F918K2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 CFSG.GorensteinWalter
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem fourTenPrime_cover_of_pgl
    {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime] {T A : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hAne : A ≠ ⊥)
    (hp5 : 5 < p) (φ : Q ≃* PGL2 (ZMod p)) :
    (⊤ : Subgroup Q) ≤ T ⊔ ⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A J}, J := by
  have htau : E1.tauOf (⊤ : Subgroup Q) T A ≤ T ⊓ (⊤ : Subgroup Q) :=
    le_inf (E1.tauOf_le ⊤ T A) le_top
  have hsyl : IsSylowIn 2 (T ⊓ (⊤ : Subgroup Q)) ⊤ := by simpa using hT
  let e : ↥(⊤ : Subgroup Q) ≃* PGL2 (ZMod p) := (Subgroup.topEquiv (G := Q)).trans φ
  let π : ↥(⊤ : Subgroup Q) →* PGL2 (ZMod p) := e.toMonoidHom
  have hπinj : Function.Injective π := by simpa [π] using e.injective
  have hπsurj : Function.Surjective π := by simpa [π] using e.surjective
  have hker : IsPGroup 2 π.ker := by
    rw [(MonoidHom.ker_eq_bot_iff π).mpr hπinj]
    exact IsPGroup.of_bot
  have hne : (A.subgroupOf (⊤ : Subgroup Q)).map π ≠ ⊥ := by
    intro hbot
    have hsub := (Subgroup.map_eq_bot_iff_of_injective
      (A.subgroupOf (⊤ : Subgroup Q)) hπinj).mp hbot
    rw [Subgroup.subgroupOf_eq_bot, disjoint_top] at hsub
    exact hAne hsub
  exact relative_generation_printed_of_pgl2_prime
    (F := ZMod p) (D := ⊤) (Nat.card_zmod p) hp5
    hT hAT hA htau hsyl π hπsurj hker hne

private theorem fourTenPrime_psl_setup
    {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {p : ℕ} [Fact p.Prime]
    (hset : FourTenSetting Q L p 1) (hL2 : F6.IsL2 p 1 ↥L) (hp7 : 7 ≤ p)
    {A : Subgroup Q} (hA4le : 4 ≤ Nat.card A) (hA : IsElemAbelian 2 A)
    (φ : Q ≃* PSL2 (ZMod p)) : 11 ≤ p ∧ Nat.card A = 4 := by
  have hoddZ : IsOddPrimePower (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact ⟨p, 1, hset.prime, hset.prime.odd_of_ne_two hset.ne_two, le_rfl, (pow_one p).symm⟩
  have h5Z : 5 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  have : IsSimpleGroup (PSL2 (ZMod p)) :=
    (EmptyFaithfulMultiple.F618Comp.psl2_facts (ZMod p) hoddZ h5Z).1
  have : IsSimpleGroup Q := φ.isSimpleGroup
  have : L.Normal := hset.normal
  have hLne : L ≠ ⊥ := by
    intro hbot
    have : IsSimpleGroup ↥L := hset.isSimpleGroup
    have h2 : 2 ≤ Nat.card ↥L :=
      Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial ↥L)
    rw [hbot] at h2
    simp at h2
  have hLtop : L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
    · exact absurd h hLne
    · exact h
  have hQl2 : F6.IsL2 p 1 Q := by
    refine CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ?_ hL2
    exact (MulEquiv.subgroupCongr hLtop).trans (Subgroup.topEquiv (G := Q))
  have hpne7 : p ≠ 7 := by
    intro hp7eq
    subst hp7eq
    exact hset.not_small (Or.inl hQl2)
  have hp11 : 11 ≤ p := by
    obtain ⟨k, hk⟩ := hset.prime.odd_of_ne_two hset.ne_two
    have hp9 : p ≠ 9 := by
      rintro rfl
      have hp := hset.prime
      norm_num at hp
    rcases lt_or_ge p 11 with hp | hp
    · omega
    · exact hp
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun _ ha _ hb => hA.comm ha hb
  have hcard4 : Nat.card A ≤ 4 :=
    card_le_four_of_isPSL_two hset.prime hset.ne_two hQl2 A hcommA hA.2
  have hA4 : Nat.card A = 4 := by omega
  exact ⟨hp11, hA4⟩

private theorem fourTenPrime_cover_of_psl
    {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime] {T A : Subgroup Q}
    (hA4 : Nat.card A = 4) (hp11 : 11 ≤ p)
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (φ : Q ≃* PSL2 (ZMod p)) :
    (⊤ : Subgroup Q) ≤ T ⊔ ⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A J}, J := by
  have htau : E1.tauOf (⊤ : Subgroup Q) T A ≤ T ⊓ (⊤ : Subgroup Q) :=
    le_inf (E1.tauOf_le ⊤ T A) le_top
  have hsyl : IsSylowIn 2 (T ⊓ (⊤ : Subgroup Q)) ⊤ := by simpa using hT
  let e : ↥(⊤ : Subgroup Q) ≃* PSL2 (ZMod p) := (Subgroup.topEquiv (G := Q)).trans φ
  let π : ↥(⊤ : Subgroup Q) →* PSL2 (ZMod p) := e.toMonoidHom
  have hπinj : Function.Injective π := by simpa [π] using e.injective
  have hπsurj : Function.Surjective π := by simpa [π] using e.surjective
  have hker : IsPGroup 2 π.ker := by
    rw [(MonoidHom.ker_eq_bot_iff π).mpr hπinj]
    exact IsPGroup.of_bot
  let B : Subgroup (PSL2 (ZMod p)) := (A.subgroupOf (⊤ : Subgroup Q)).map π
  let Sbar : Subgroup (PSL2 (ZMod p)) := (T.subgroupOf (⊤ : Subgroup Q)).map π
  have hBelem : IsElemAbelian 2 B := (hA.subgroupOf (⊤ : Subgroup Q)).map π
  have hBcard : Nat.card B = 4 := by
    have h1 : Nat.card ↥(A.subgroupOf (⊤ : Subgroup Q)) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
    have h2 : Nat.card B = Nat.card ↥(A.subgroupOf (⊤ : Subgroup Q)) :=
      Subgroup.card_map_of_injective hπinj
    omega
  have hBKlein : IsKleinFour ↥B :=
    CFSG.Quasithin.FFC.isKleinFour_of_card_four hBcard
      (fun u => Subtype.ext (hBelem.2 u.val u.2))
  have hBS : B ≤ Sbar :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono (⊤ : Subgroup Q) hAT)
  have hSylS : IsSylowIn 2 Sbar ⊤ := by
    have hSylD : IsSylowIn 2 (T.subgroupOf (⊤ : Subgroup Q)) ⊤ := by
      have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T)
        (K := (⊤ : Subgroup Q)) (H := (⊤ : Subgroup Q)) le_top le_rfl).mpr hT
      simpa [Subgroup.subgroupOf_self] using h
    simpa [Sbar] using E1.isSylowIn_two_map_top hπsurj hSylD
  have hgenStub := psl2_prime_sup_isE_one_and_eOne_eq_top
    (K := ZMod p) (p := p) (Nat.card_zmod p) hp11 hSylS hBS hBKlein
  exact relative_generation_printed_of_eOne
    (G := Q) (Γ := PSL2 (ZMod p)) (T := T) (A := A) (K := ⊤)
    hT hAT hA htau hsyl π hπsurj hker (by simpa [Sbar, B] using hgenStub)

theorem fourTenPrime_holds :
    FourTenPrime := by
  intro Q _ _ L p e hset hP T hT Ω hΩ hcard
  obtain ⟨rfl, hp7⟩ := hP
  have : Fact p.Prime := ⟨hset.prime⟩
  have hL2 : F6.IsL2 p 1 ↥L := by simpa using hset.isL2
  have hgf : CFSG.generalizedFitting Q = L := by
    rw [← fstar_top_eq_generalizedFitting Q, hset.fstar_eq]
  have hF : IsPSL 2 p 1 ↥(CFSG.generalizedFitting Q) := by
    refine CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ?_ hL2
    exact (MulEquiv.subgroupCongr hgf).symm
  obtain ⟨A, hAΩ, hAT⟩ := hΩ.exists_mem_le hT
  have hA : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have hA4le : 4 ≤ Nat.card A := hcard A hAΩ hAT
  have finish : (⊤ : Subgroup Q) ≤ T ⊔ ⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A J}, J →
      genEi 1 T Ω ⊔ T = ⊤ := by
    intro hgen
    have hle : (⨆ J ∈ {J : Subgroup Q | InCalEi 1 T A J}, J) ≤ genEi 1 T Ω :=
      iSup_inCalEi_le_genEi hAΩ hAT
    have hsup : (⊤ : Subgroup Q) ≤ T ⊔ genEi 1 T Ω := hgen.trans (sup_le_sup_left hle T)
    rw [sup_comm]
    exact eq_top_iff.mpr hsup
  rcases CFSG.Quasithin.E22L2.psl2_prime_transport hp7 hF with h | h
  · obtain ⟨φ⟩ := h
    obtain ⟨hp11, hA4⟩ := fourTenPrime_psl_setup hset hL2 hp7 hA4le hA φ
    exact finish (fourTenPrime_cover_of_psl hA4 hp11 hT hAT hA φ)
  · obtain ⟨φ⟩ := h
    exact finish (fourTenPrime_cover_of_pgl hT hAT hA
      (hΩ.ne_bot A hAΩ) (by omega : 5 < p) φ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
