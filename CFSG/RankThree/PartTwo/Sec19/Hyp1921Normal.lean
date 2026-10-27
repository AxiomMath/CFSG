module

public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec18.Item186Rank
import CFSG.RankThree.PartTwo.Sec18.Item186Three

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

private theorem toSec18Std' (h : Hyp1921 G A M N L) : Sec18Std G A M :=
  { toPartTwoStanding := h.toSec19Std.toPartTwoStanding
    partTwoS_eq := h.partTwoS_eq
    mem_partTwoE := h.mem_partTwoE
    mem_scriptM := h.mem_scriptM }

theorem Hyp1921.le_normalizer_of (h : Hyp1921 G A M N L)
    (hF : ∃ F : Subgroup G, F ≤ L ∧ CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 9)
    (hZ : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      x ∈ CFSG.Open.pCoreOf 2 L) :
    N ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hFL, hFe, hF9⟩ := hF
  have hLN : L ≤ N := le_of_mem_oTwoComponentsIn h.mem_oTwoComponentsIn
  have hQ : CFSG.Open.pCoreOf 2 N ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM_N.1
  have hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f := fun f hf f' hf' =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨f, hf⟩ ⟨f', hf'⟩)
  have h3 := h.toSec19Std.toPartTwoStanding.toTheoremFourHyp.localRank_three
  intro x hx
  by_contra hxN
  set J := L.map (MulAut.conj x).toMonoidHom with hJdef
  have hJ : J ∈ oTwoComponentsIn N :=
    Sec18.map_conj_mem_oTwoComponentsIn h.mem_oTwoComponentsIn hx
  have hJL : J ≠ L := fun heq => hxN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  have hconj : ∀ g : G, (MulAut.conj x).toMonoidHom g = x * g * x⁻¹ := fun g => rfl
  have hQx : ∀ q ∈ CFSG.Open.pCoreOf 2 N, x⁻¹ * q * x ∈ CFSG.Open.pCoreOf 2 N := fun q hq => by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hx)) q).mp hq
    rwa [inv_inv] at h1
  have hF'e : ∀ f ∈ F.map (MulAut.conj x).toMonoidHom, f ^ 3 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hconj, conj_pow, hFe.2 b hb, mul_one, mul_inv_cancel]
  have hF'c : ∀ f ∈ F.map (MulAut.conj x).toMonoidHom,
      ∀ f' ∈ F.map (MulAut.conj x).toMonoidHom, f * f' = f' * f := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    simp only [hconj]
    calc x * b * x⁻¹ * (x * b' * x⁻¹) = x * (b * b') * x⁻¹ := by group
      _ = x * (b' * b) * x⁻¹ := by rw [hFc b hb b' hb']
      _ = x * b' * x⁻¹ * (x * b * x⁻¹) := by group
  have hF'9 : 9 ≤ Nat.card (F.map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hF9.ge
  have hF'f : ∀ f ∈ F.map (MulAut.conj x).toMonoidHom,
      (∀ j ∈ J, f * j * f⁻¹ * j⁻¹ ∈ CFSG.Open.pCoreOf 2 N) → f = 1 := by
    rintro _ ⟨b, hb, rfl⟩ hcomm
    have hbO : b ∈ CFSG.Open.pCoreOf 2 L := by
      refine hZ b (hFL hb) fun l hl => ?_
      have h1 := hcomm (x * l * x⁻¹) ⟨l, hl, rfl⟩
      simp only [hconj] at h1
      have h2 := hQx _ h1
      have e : x⁻¹ * (x * b * x⁻¹ * (x * l * x⁻¹) * (x * b * x⁻¹)⁻¹ * (x * l * x⁻¹)⁻¹) * x =
          b * l * b⁻¹ * l⁻¹ := by group
      rw [e] at h2
      exact Sec18.Item186Proof.pCoreOf_inf_le hLN
        ⟨h2, L.mul_mem (L.mul_mem (L.mul_mem (hFL hb) hl) (L.inv_mem (hFL hb))) (L.inv_mem hl)⟩
    have hb1 : b = 1 := by
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨b, hbO⟩
      have h2k : b ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hg := pow_gcd_eq_one.mpr ⟨h2k, hFe.2 b hb⟩
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      rwa [hcop.gcd_eq_one, pow_one] at hg
    rw [hconj, hb1, mul_one, mul_inv_cancel]
  have h4 := Sec18.Item186Proof.four_le_localRank_of_pair hQ h.mem_oTwoComponentsIn hJ hJL hFL
    hFe.2 hFc hF9.ge (Subgroup.map_mono hFL) hF'e hF'c hF'9 hF'f
  omega

theorem Hyp1921.normalizer_eq_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) : Subgroup.normalizer (L : Set G) = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : CFSG.Open.pCoreOf 2 L ≠ ⊥ :=
    pCoreOf_ne_bot_of_mem_oTwoComponentsIn h.charTwoType h.mem_scriptM_N.1.1
      h.mem_oTwoComponentsIn
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 L, hL2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L, rfl⟩
  have hNK : N ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hNL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hKN : Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) ≤ N := by
    rcases hNK.lt_or_eq with hlt | heq
    · exact absurd hloc (h.mem_scriptM_N.1.2 _ hlt)
    · exact le_of_eq heq.symm
  exact le_antisymm ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L).trans hKN) hNL

theorem Hyp1921.pCoreOf_le_M_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) : CFSG.Open.pCoreOf 2 L ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : A ≤ N := h.mem_scriptM_N.2
  exact Sec18.le_of_le_normalizer_of_isPGroup_two (toSec18Std' h)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    ((hAN.trans hNL).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))

end CFSG.RankThree.PartTwo.Late
