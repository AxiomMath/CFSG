module

public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTheta
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem412
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec11.Item119Used

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)


section Certs


@[expose] def Item417SL3PiTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → CFSG.pCore 2 G = ⊥ →
    ∀ L : Subgroup G, IsComponent L →
    ∀ (A E : Subgroup G) (c : G), IsQuad417 L A E c 3 →
      A ≤ Subgroup.normalizer (L : Set G) →
      (¬ ∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) →
      ∀ n : ℕ, 1 ≤ n → (IsSLThreePiAt ↥L (2 ^ n) ∨ IsoLThreePi ↥L 2 n) →
        (∃ n : ℕ, 0 < n ∧ Even n ∧
          ((Nonempty (L ≃* projSL 3 (GaloisField 2 n)) ∧ IsTypeCOn A L) ∨
            (IsSLThreePiAt ↥L (2 ^ n) ∧ IsTypeCOnSL A L))) ∧
          Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))

namespace Res417

variable {G : Type} [Group G] [Finite G]

omit
  [Finite G] in
theorem inf_centralizer_subgroupOf {L A : Subgroup G} {c : G}
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) :
    A.subgroupOf (Subgroup.normalizer (L : Set G)) ⊓
        Subgroup.centralizer ((L.subgroupOf (Subgroup.normalizer (L : Set G)) :
          Subgroup (Subgroup.normalizer (L : Set G))) : Set (Subgroup.normalizer (L : Set G))) =
      Subgroup.zpowers (⟨c, hcN⟩ : Subgroup.normalizer (L : Set G)) := by
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  ext x
  constructor
  · rintro ⟨hxA, hxC⟩
    have hxC' : (x : G) ∈ A ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hxC ⟨l, hLN hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
      exact congrArg Subtype.val this
    rw [hAc] at hxC'
    obtain ⟨k, hk⟩ := hxC'
    refine ⟨k, Subtype.ext ?_⟩
    simpa using hk
  · rintro ⟨k, rfl⟩
    have hck : c ^ k ∈ A ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hAc]
      exact ⟨k, rfl⟩
    refine ⟨Subgroup.mem_subgroupOf.mpr (by simpa using hck.1),
      Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hck.2 (y : G) (Subgroup.mem_subgroupOf.mp hy)
    simpa using this

theorem card_eq_or_field (hG : SectionFourHyp G) {L : Subgroup G} (hLq : IsQuasisimple L)
    (hSL : IsSLThreePi L ∨ ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi L p e)
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (h27 : 27 ≤ Nat.card A) {c : G}
    (hc3 : orderOf c = 3) (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) :
    Nat.card A = 27 ∨ ∃ σ ∈ A, InducesStdKind L σ .field := by
  set N := Subgroup.normalizer (L : Set G) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hcA : c ∈ A := by
    have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
    exact this.1
  have hN : SectionFourHyp N := sectionFourHyp_subgroup hG N
  set L' : Subgroup N := L.subgroupOf N with hL'def
  have hL'n : L'.Normal := Subgroup.normal_in_normalizer
  let eL : L' ≃* L := Subgroup.subgroupOfEquivOfLe hLN
  have hLq' : IsQuasisimple L' := LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq
  have hA' : Maximal (fun B : Subgroup N => CFSG.Assembly.IsElemAbelian 3 B) (A.subgroupOf N) :=
    Sec11.maximal_subgroupOf_of_le (fun B hB hAB => hA.eq_of_ge hB hAB) hA.prop hAL
  have hcardA : Nat.card (A.subgroupOf N) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have h27' : 27 ≤ Nat.card (A.subgroupOf N) := hcardA ▸ h27
  have hc3' : orderOf (⟨c, hAL hcA⟩ : N) = 3 := by rw [Subgroup.orderOf_mk]; exact hc3
  have hAc' := inf_centralizer_subgroupOf hAc (hAL hcA)
  have hLL : L'.map N.subtype = L := by
    rw [hL'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLN]
  have hk : ∀ σ : N, InducesStdKind L' σ .field → InducesStdKind L σ .field := by
    intro σ hσ
    have h1 := Sec13.inducesStdKind_sub N L' hσ
    rwa [hLL] at h1
  have hfield : ∀ σ : N, σ ∈ A.subgroupOf N → InducesStdKind L' σ .field →
      ∃ σ ∈ A, InducesStdKind L σ .field :=
    fun σ hσ hσf => ⟨σ, Subgroup.mem_subgroupOf.mp hσ, hk σ hσf⟩
  rcases hSL with ⟨q, hq⟩ | ⟨p, e, hp, he, hiso⟩
  · have hSL' : IsSLThreePi L' := ⟨q, isSLThreePiAt_congr eL hq⟩
    rcases rank3II_4_11 N hN L' hL'n hSL' hLq' (A.subgroupOf N) hA' h27' _ hc3' hAc' with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, σ, hσ, hσf, -⟩ | ⟨-, σ, hσ, hσf, -⟩ | ⟨-, σ, hσ, hσf, -⟩
    · exact Or.inl (hcardA ▸ h)
    · exact Or.inl (hcardA ▸ h)
    · exact Or.inl (hcardA ▸ h)
    · exact Or.inr (hfield σ hσ hσf)
    · exact Or.inr (hfield σ hσ hσf)
    · exact Or.inr (hfield σ hσ hσf)
  · have hiso' : ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi L' p e :=
      ⟨p, e, hp, he, isoLThreePi_congr eL hiso⟩
    rcases rank3II_4_12 N hN L' hL'n hiso' hLq' (A.subgroupOf N) hA' h27' _ hc3' hAc' with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, σ, hσ, hσf, -⟩
    · exact Or.inl (hcardA ▸ h)
    · exact Or.inl (hcardA ▸ h)
    · exact Or.inl (hcardA ▸ h)
    · exact Or.inr (hfield σ hσ hσf)

end Res417

open Res417

theorem item4_17SL3Pi_of (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hTwo : Item417SL3PiTwo) : Item4_17SL3Pi := by
  intro G _ _ hG h2 L hL _ A E c m hq hAL h1 hSL
  have hθ := theta_eq_bot hGA h2 hL hSL
  obtain ⟨p, e, hpf, he, h⟩ := hSL
  have hq3 : p ^ e % 3 ≠ 0 := by
    rcases h with ⟨K, _, _, ⟨-, h3, -⟩ | ⟨-, h3, -⟩⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hq3 (Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega)))
  let eθ := thetaQuotEquivOfEqBot hθ
  have hL' : IsSLThreePiAt ↥L (p ^ e) ∨ IsoLThreePi ↥L p e := by
    rcases h with h | h
    · exact Or.inl (isSLThreePiAt_congr eθ.symm h)
    · exact Or.inr (isoLThreePi_congr eθ.symm h)
  have hq' := hq
  obtain ⟨hAmax, hcard, hAc, hc3, hE, hEA, -⟩ := hq'
  have h27 : 27 ≤ Nat.card A := hE.2 ▸ Subgroup.card_le_of_le hEA
  have hSL' : IsSLThreePi L ∨ ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi L p e := by
    rcases hL' with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr ⟨p, e, hpf, he, h⟩
  rcases card_eq_or_field hG hL.1 hSL' hAmax hAL h27 hc3 hAc with h27' | ⟨σ, hσ, hσf⟩
  swap
  · exact (h1 ⟨σ, hσ, Or.inl hσf⟩).elim
  have hm : m = 3 := by
    have h33 : 3 ^ m = 3 ^ 3 := by rw [← hcard, h27']; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h33
  subst hm
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨hn, hS3⟩ := hTwo G hG h2 L hL A E c hq hAL h1 e he hL'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, hn, hS3⟩))))))))
  · have hp : 3 < p := by
      have := hpf.out.two_le
      have : p ≠ 3 := hp3
      omega
    exact Or.inr (Or.inr (Or.inl ⟨rfl, p, hpf, hp, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨e, he, hL'⟩)))⟩))

end Certs

end CFSG.RankThree.PartTwo.Sec4
