module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMPrimeC_model {B L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (h3 : ¬ 3 ∣ m) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hMul : PSUTrivialMultiplier m) :
    ∃ (R : Type) (_ : Group R) (_ : ↥L ≃* R), GGTorusPermEltSC 3 m R := by
  have hm4 := qTwoLMFrameC_four_le hL
  have hZ := qTwoLMFrameC_center_bot hG hL hMul
  obtain ⟨-, K, hKf, hKfin, hK, ⟨θ⟩⟩ := hL.statedClassicalModel_of_ne_zero (by omega)
  letI := hKf
  letI := hKfin
  refine ⟨StatedProj (StatedSU m (2 ^ 1) K), inferInstance,
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans θ),
    ?_⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK
  exact UModel.ggTorusPermEltSC_unitary hK' le_rfl (by omega) Nat.prime_three (by norm_num)
    (by norm_num) h3

@[expose] def qTwoLMPrimeC_imgT (Bs L : Subgroup G) {R : Type} [Group R] (eL : ↥L ≃* R) :
    Subgroup R :=
  ((Bs ⊓ L).subgroupOf L).map eL.toMonoidHom

theorem qTwoLMPrimeC_imgT_props {Bs L : Subgroup G} {R : Type} [Group R] (eL : ↥L ≃* R)
    (hab : IsElemAbelian 3 (Bs ⊓ L)) (hcard : 3 ^ 3 ≤ Nat.card ↥(Bs ⊓ L))
    (hsc : ∀ n ∈ L, (∀ t ∈ Bs ⊓ L, n * t = t * n) → n ^ 3 = 1 → n ∈ Bs ⊓ L) :
    IsElemAbelian 3 (qTwoLMPrimeC_imgT Bs L eL) ∧
      3 ^ 3 ≤ Nat.card ↥(qTwoLMPrimeC_imgT Bs L eL) ∧
      ∀ g : R, (∀ e ∈ qTwoLMPrimeC_imgT Bs L eL, g * e = e * g) → g ^ 3 = 1 →
        g ∈ qTwoLMPrimeC_imgT Bs L eL := by
  unfold qTwoLMPrimeC_imgT
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.Open.IsElemAbelian.map
      (CFSG.Open.IsElemAbelian.subgroupOf hab L) eL.toMonoidHom
  · have h1 : Nat.card ↥(((Bs ⊓ L).subgroupOf L).map eL.toMonoidHom)
        = Nat.card ↥((Bs ⊓ L).subgroupOf L) :=
      Subgroup.card_map_of_injective eL.injective
    have h2 : Nat.card ↥((Bs ⊓ L).subgroupOf L) = Nat.card ↥(Bs ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1, h2]
    exact hcard
  · intro g hgcomm hg3
    set n : ↥L := eL.symm g with hn_def
    have hen : eL n = g := by
      simpa [hn_def] using eL.apply_symm_apply g
    have hn3 : n ^ 3 = 1 := by
      apply eL.injective
      rw [map_pow, map_one, hen, hg3]
    have hnG3 : (n : G) ^ 3 = 1 := by
      have h := congrArg (fun z : ↥L => (z : G)) hn3
      simpa using h
    have hcentral : ∀ t ∈ Bs ⊓ L, (n : G) * t = t * (n : G) := by
      intro t ht
      have htl : (⟨t, ht.2⟩ : ↥L) ∈ (Bs ⊓ L).subgroupOf L := ht
      have hmem : eL ⟨t, ht.2⟩ ∈ ((Bs ⊓ L).subgroupOf L).map eL.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨⟨t, ht.2⟩, htl, rfl⟩
      have hgt := hgcomm _ hmem
      have h' : n * (⟨t, ht.2⟩ : ↥L) = (⟨t, ht.2⟩ : ↥L) * n := by
        have h := congrArg eL.symm hgt
        simpa [map_mul, hn_def] using h
      have hval := congrArg (fun z : ↥L => (z : G)) h'
      simpa using hval
    have hnT : (n : G) ∈ Bs ⊓ L := hsc (n : G) n.2 hcentral hnG3
    refine Subgroup.mem_map.mpr ⟨n, ?_, hen⟩
    exact Subgroup.mem_subgroupOf.mpr hnT

end CFSG.StandardType.QTwo

end
