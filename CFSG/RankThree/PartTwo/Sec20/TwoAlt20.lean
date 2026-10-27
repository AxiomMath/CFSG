module

public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
public import CFSG.RankThree.PartTwo.Sec19.Item1922Full
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Inner
import CFSG.RankThree.PartTwo.Sec18.SylowTop
import CFSG.RankThree.PartTwo.Sec18.Item1810Group
import CFSG.RankThree.PartTwo.Sec15.Item1510ProofTools
import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec11.Item116R1LemP

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

private theorem card_eq_of_sup_inf {M N L : Subgroup G} (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hsup : L ⊔ (N ⊓ M) = N)
    (hidx : (L ⊓ M).relIndex L = 280) :
    Nat.card N = 280 * Nat.card (N ⊓ M : Subgroup G) := by
  have h1 := relIndex_sup_eq_of_le_normalizer (H := N ⊓ M) (N := L) (inf_le_left.trans hNL)
  rw [sup_comm, hsup] at h1
  have h2 := Subgroup.relIndex_mul_card L N
  rw [inf_eq_left.mpr hLN] at h2
  have h3 := Subgroup.relIndex_mul_card L (N ⊓ M)
  rw [show L ⊓ (N ⊓ M) = L ⊓ M by rw [← inf_assoc, inf_eq_left.mpr hLN]] at h3
  have h4 := Subgroup.relIndex_mul_card (L ⊓ M) L
  rw [show L ⊓ M ⊓ L = L ⊓ M by rw [inf_comm, ← inf_assoc, inf_idem], hidx] at h4
  rw [← h2, ← h4, ← h3, ← h1]
  ring

theorem alt20_of_hyp1921
    (h1912 : Item1912) (h194 : Sec19.Item194UsedWide3) (h23 : Item1923)
    {A M N L : Subgroup G} {c : G} (h : Hyp1921 G A M N L)
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    Alt20 G A M L N c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hET := h1912 G h.toSec19Std
  obtain ⟨hNL, hNeq, ⟨c', hc'3, hc', -⟩, hsyl, hcard, -, hsup, hLM, hO2, -⟩ :=
    item1922Full_of_item1912 h1912 G A M N L h
  have hz : Subgroup.zpowers c = Subgroup.zpowers c' := SetLike.coe_injective (hc.symm.trans hc')
  have hc3 : orderOf c = 3 := by rw [← Nat.card_zpowers, hz, Nat.card_zpowers, hc'3]
  have hidx := h.relIndex_inf_eq hET
  obtain ⟨K, hK⟩ := (h194 G h.toSec19Std A M N h.isE27 h.mem_scriptM h.mem_scriptM_N h.ne).1
  obtain ⟨-, -, -, ⟨n, hn, hiso, -⟩, hcK, hAK, hKM, hKeq, hpar, hC, hBO2, h6, h7⟩ :=
    h23 G A M N L c h hc K hK
  subst hKeq
  have hKleM : normalClosureIn M c ≤ M := le_of_mem_oTwoComponentsIn hK.1
  have hO2KM : CFSG.Open.pCoreOf 2 (normalClosureIn M c) ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKleM)
      (hKM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hCK : ∀ q ∈ M, (∀ k ∈ normalClosureIn M c,
      q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (normalClosureIn M c)) → q ∈ N :=
    fun q hq hqk => hC q hq fun k hk => hO2KM (hqk k hk)
  have hNAM : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [h.isE27.pRank_eq]; norm_num)).trans h.mem_scriptM.2
  refine
    { eq_normalizer := hNeq.symm
      le_normalizer := h.le_N.trans hNL
      quotient_iso := h.quotient_iso
      not_le := hLM
      pCoreOf_le := hO2
      sylow_inf := hsyl
      card_inf := hcard
      orderOf_c := hc3
      sup_inf_eq := hsup
      relIndex_inf := hidx
      card_eq := card_eq_of_sup_inf h.L_le_N hNL hsup hidx
      K_mem := hK.1
      K_not_le := hK.2
      K_type := Or.inl ⟨n, hn, hiso, by
        rw [Subgroup.inf_subgroupOf_left]
        exact hpar⟩
      pCoreOf_K_le := fun q hq => hCK q
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKleM hq) fun k hk => by
          have hn : CFSG.Open.pCoreOf 2 (normalClosureIn M c) ≤
              Subgroup.normalizer (normalClosureIn M c : Set G) :=
            (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans Subgroup.le_normalizer
          have h1 : k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (normalClosureIn M c) :=
            (Subgroup.mem_normalizer_iff.mp
              (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hk) _).mp
              (Subgroup.inv_mem _ hq)
          have : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
          rw [this]
          exact Subgroup.mul_mem _ hq h1
      normal_inf_sup := hBO2
      centralizer_le := fun _ => hCK
      sylow_top := ?_ }
  intro P hP
  obtain ⟨P₀, hP₀, hAP₀⟩ :=
    exists_isSylowOf_le h.isE27.isPGroup (le_inf h.le_M h.le_N : A ≤ M ⊓ N)
  obtain ⟨hP₀M, -, hΩ₀, -⟩ := h6 P₀ hP₀ hAP₀
  have hP₀A : P₀ ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer.trans (Sec15.Proof1510.normalizer_le_of_eq_omegaOneThree hΩ₀.symm)
  have hP₀N : IsSylowOf 3 P₀ (Subgroup.normalizer (A : Set G)) := hP₀M.of_le hP₀A hNAM
  obtain ⟨g, hg, rfl⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hP₀N hP
  have hgA : A.map (MulAut.conj g).toMonoidHom = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hΩ : Sec18.omegaOneThree (P₀.map (MulAut.conj g).toMonoidHom) = A := by
    rw [Sec18.Item1810Proof.omegaOneThree_map_conj, hΩ₀, hgA]
  have hPM : IsSylowOf 3 (P₀.map (MulAut.conj g).toMonoidHom) M := isSylowOf_map_conj hP₀M (hNAM hg)
  have hAP : A ≤ P₀.map (MulAut.conj g).toMonoidHom := hgA ▸ Subgroup.map_mono hAP₀
  have hcA : c ∈ A := by
    have : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
      rw [hc]; exact Subgroup.mem_zpowers c
    exact this.1
  refine ⟨Sec18.SylowTop.isSylowOf_top_of_normalizer_le hPM
      ((Sec15.Proof1510.normalizer_le_of_eq_omegaOneThree hΩ.symm).trans hNAM),
    h7 _ hPM (hAP hcA), ?_⟩
  have hAe := h.isE27.1
  have hΦ : frattini ↥A = ⊥ := Sec11.lemPc_frattini_eq_bot Nat.prime_three
    (fun a b => Subtype.ext (hAe.1.is_comm.comm a b ▸ rfl))
    (fun x => Subtype.ext (by simpa using hAe.2 x x.2))
  rw [hΩ, hΦ, Subgroup.map_bot, Subgroup.mem_bot]
  intro hc1
  rw [hc1, orderOf_one] at hc3
  exact absurd hc3 (by norm_num)

end CFSG.RankThree.PartTwo.Sec20
