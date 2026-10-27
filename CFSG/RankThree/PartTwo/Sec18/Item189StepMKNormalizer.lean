module

public import CFSG.RankThree.PartTwo.Sec18.Item189Steps
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofStatements
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
import CFSG.RankThree.PartTwo.Sec18.SylowFusion
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemTools

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def NormalizerLeN189OfO2Trivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    H ∈ scriptHStar A M → CFSG.Open.pCoreOf 2 H ≠ ⊥ →
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ n189 H

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mem_oTwoComponentsIn_of_isPerfect_le {X K₁ K₂ P : Subgroup G}
    (h₁ : K₁ ∈ oTwoComponentsIn X) (h₂ : K₂ ∈ oTwoComponentsIn X) (hP : ⁅P, P⁆ = P)
    (hP1 : P ≠ ⊥) (hP₁ : P ≤ K₁) (hP₂ : P ≤ K₂) : K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hcomm : ⁅P, P⁆ ≤ CFSG.Open.pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro p hp p' hp'
    exact Sec19.Step1910Proof.commutator_mem_pCoreOf h₁ h₂ hne (hP₁ hp) (hP₂ hp')
  rw [hP] at hcomm
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hcomm
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have : Group.IsPerfect P := (Subgroup.isPerfect_iff).mpr hP
  exact Group.IsPerfect.not_isNilpotent P hP2.isNilpotent

section Certified

theorem normalizerLeN189OfO2Trivial_of_alt1C (h1812 : Item181_2) (hAlt : Item182Alt1C)
    (h1841 : Item184_1) (h1842 : Item184_2) : NormalizerLeN189OfO2Trivial := by
  intro G _ _ A M H c hHc hHmax hO2H hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : Sec18Std G A M := hHc.toSec18Std
  have : IsSimpleGroup G := h.isSimpleGroup
  have hA : IsE27 A := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH : H ∈ scriptH A M := hHc.mem_scriptH
  have hHmax' : Maximal (· ∈ scriptH A M) H := hHmax
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  set L := inSubgroup perfectResidual H with hLdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set Z := Subgroup.zpowers c with hZdef
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hHc).1
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hCZ : C ≤ Subgroup.normalizer (Z : Set G) :=
    Rem187QProof.centralizer_le_normalizer_zpowers c
  set Lc := lc H c with hLcdef
  have hLc₀ : Lc = inSubgroup perfectResidual (L ⊓ C) := by
    rw [hLcdef]
    show inSubgroup perfectResidual (L ⊓ C ⊔ CFSG.Open.pCoreOf 2 C) = _
    rw [hO, sup_bot_eq]
  have hLcL : Lc ≤ L := by
    rw [hLc₀]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hLLc : L ≤ Lc ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [hLc₀]
    exact (le_sup_and_inf_le_of_sec18H hHc).1
  have hLcp : ⁅Lc, Lc⁆ = Lc := commutator_inSubgroup_perfectResidual _
  have hLc1 : Lc ≠ ⊥ := by
    obtain ⟨-, h3, -⟩ := h1842 G A M H c hHc
    have h3' : 3 ∣ Nat.card Lc := h3
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3'
    norm_num at h3'
  have hNZLc : Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (Lc : Set G) :=
    normalizer_zpowers_le_normalizer_lc h1842 hHc
  set B := A ⊓ L with hBdef
  have hBSyl : CFSG.ABGLocalTools.IsSylowOf 3 B (Lc ⊓ C) := by
    rw [inf_eq_left.mpr (SylowFusion.lc_le_centralizer H c)]
    exact SylowFusion.isSylowOf_lc h1812 h1841 hHc
  have hABZ : A = B ⊔ Z := by
    rw [sup_comm]
    exact eq_zpowers_sup_of_sec18H h1812 h1841 hHc
  set 𝓕 : Set (Subgroup G) := {H' : Subgroup G | H' ∈ scriptH A M ∧ Lc ≤ H'} with h𝓕
  set R : Subgroup G := ⨆ H' ∈ 𝓕, CFSG.Open.pCoreOf 2 H' with hRdef
  set X := Subgroup.normalizer (R : Set G) with hXdef
  have hRM : R ≤ M := iSup₂_le fun H' hH'𝓕 =>
    le_of_le_normalizer_of_isPGroup_two h (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H')
      ((le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH'𝓕.1).1).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H'))
  have hH𝓕 : H ∈ 𝓕 := ⟨hH, hLcL.trans (Subgroup.map_subtype_le _)⟩
  have hO2HR : CFSG.Open.pCoreOf 2 H ≤ R :=
    le_iSup₂ (f := fun H' (_ : H' ∈ 𝓕) => CFSG.Open.pCoreOf 2 H') H hH𝓕
  have hR1 : R ≠ ⊥ := fun hb => hO2H (le_bot_iff.mp (hb ▸ hO2HR))
  have hMtop : M ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot h.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM.1)
  have hXtop : X ≠ ⊤ := by
    intro htop
    have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with hb | ht
    · exact hR1 hb
    · exact hMtop (top_le_iff.mp (ht ▸ hRM))
  have hLcX : Lc ≤ X := fun y hy => Rem187QProof.mem_normalizer_iSup h (Or.inl hy)
  have hNZX : Subgroup.normalizer (Z : Set G) ≤ X := by
    intro g hg
    obtain ⟨y, hy, w, hwA, hwZ, rfl⟩ :=
      Rem187QProof.exists_mul_of_frattini hNZLc hBSyl hABZ hg
    exact Subgroup.mul_mem _ (hLcX hy.1)
      (Rem187QProof.mem_normalizer_iSup h (Or.inr ⟨hwA, hNZLc hwZ⟩))
  have hHX : H ≤ X := by
    obtain ⟨s, ⟨-, hsA, -⟩, hseq, -⟩ := h1812 G A M h H hH
    have hO2X : CFSG.Open.pCoreOf 2 H ≤ X := hO2HR.trans Subgroup.le_normalizer
    have hLX : L ≤ X := hLLc.trans
      (sup_le hLcX ((Rem187QProof.pCoreOf_perfectResidual_le H).trans hO2X))
    have hAX : A ≤ X := fun a ha => hNZX (hCZ (hAC ha))
    have hsX : s ∈ X := hNZX (hCZ (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hsA c hcA).symm))
    have hSX : S ≤ X := by
      rw [hSdef, hseq]
      exact sup_le (Subgroup.zpowers_le.mpr hsX) hO2X
    exact hH₀.1.le.trans (sup_le (sup_le hLX hAX) hSX)
  have hcS : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hHc.centralizer_eq]
    exact Subgroup.mem_zpowers c
  have hc1 : c ≠ 1 := by
    intro hc
    have h3 := orderOf_eq_three_of_sec18H h1841 hHc
    rw [hc, orderOf_one] at h3
    norm_num at h3
  obtain ⟨K₁, hK₁, hK₁eq⟩ := hAlt G A M h H hH X hHX hXtop c hcA hc1 (hCZ.trans hNZX) hcS
  have hK₁mem := mem_scriptH_of_eq_sup h hH hHX hXtop hK₁ hK₁eq
  have hLK₁ : L ≤ K₁ := hK₁eq ▸ le_sup_left
  have hHle : H ≤ K₁ ⊔ A ⊔ S :=
    hH₀.1.le.trans (sup_le (sup_le (hLK₁.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)) le_sup_right)
  have hge : K₁ ⊔ A ⊔ S ≤ H := hHmax'.le_of_ge hK₁mem hHle
  have hK₁L : K₁ ≤ L := le_inSubgroup_perfectResidual
    (commutator_eq_of_mem_oTwoComponentsIn hK₁) ((le_sup_left.trans le_sup_left).trans hge)
  have hLX : L ∈ oTwoComponentsIn X := (le_antisymm hLK₁ hK₁L) ▸ hK₁
  intro g hg
  show g ∈ Subgroup.normalizer (L : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hLg := map_conj_mem_oTwoComponentsIn hLX (hNZX hg)
  have hLcg : Lc ≤ L.map (MulAut.conj g).toMonoidHom := by
    rw [← Late.map_conj_eq_of_mem_normalizer (hNZLc hg)]
    exact Subgroup.map_mono hLcL
  exact (eq_of_mem_oTwoComponentsIn_of_isPerfect_le hLX hLg hLcp hLc1 hLcL hLcg).symm

end Certified

end CFSG.RankThree.PartTwo.Sec18
