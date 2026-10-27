module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKeySetup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndNineSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace A10Perm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10
open scoped Pointwise

theorem not_forall_map_tBlock_eq {U : Subgroup (Equiv.Perm (Fin 10))}
    (hU : Nat.card U = 81) (k : Fin 3) :
    ¬ ∀ u ∈ U, (tBlock k).map (u : Equiv.Perm (Fin 10)).toEmbedding = tBlock k := by
  classical
  intro h
  let s : ↑(Set.powersetCard (Fin 10) 4) := ⟨tBlock k, by
    simpa [Set.powersetCard] using card_tBlock k⟩
  let S : Set (Fin 10) := (tBlock k : Finset (Fin 10))
  have hScoe : (↑s : Set (Fin 10)) = S := rfl
  have hUle : U ≤ MulAction.stabilizer (Equiv.Perm (Fin 10)) S := by
    intro u huU
    rw [MulAction.mem_stabilizer_iff]
    show u '' S = S
    have himg : u '' S = ↑(Finset.map (Equiv.toEmbedding u) (tBlock k)) := by
      rw [Finset.coe_map]
      rfl
    rw [himg, h u huU]
  have hdvd : Nat.card U ∣ Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 10)) S) :=
    Subgroup.card_dvd_of_le hUle
  haveI : MulAction.IsPretransitive (Equiv.Perm (Fin 10)) (↑(Set.powersetCard (Fin 10) 4)) :=
    Set.powersetCard.isPretransitive
  have hstab : MulAction.stabilizer (Equiv.Perm (Fin 10)) S =
      MulAction.stabilizer (Equiv.Perm (Fin 10)) s := by
    rw [Set.powersetCard.stabilizer_coe, hScoe]
  have hidx : (MulAction.stabilizer (Equiv.Perm (Fin 10)) S).index = 210 := by
    rw [hstab, MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ,
      Set.powersetCard.card, Nat.card_fin]
    norm_num [Nat.choose]
  have hcard : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 10)) S) = 17280 := by
    have hh := Subgroup.card_mul_index (MulAction.stabilizer (Equiv.Perm (Fin 10)) S)
    rw [hidx, Nat.card_perm, Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    have hh' : Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin 10)) S) * 210 = 3628800 := by
      rw [Nat.card_eq_fintype_card]
      simpa using hh
    omega
  rw [hU, hcard] at hdvd
  norm_num at hdvd

end A10Perm

namespace Ctx82E3.A10Frame

open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {c : Ctx82E3 D}

theorem isSylowOf_top_of_isSylowOf (F : A10Frame c) (hF : A10Facts F) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤ := by
  classical
  refine CFSG.ABGLocalTools.isSylowOf_of_card (p := 3) (P := Q) (K := ⊤) le_top ?_
  rw [hQ.card_eq, ← F.sylow.card_eq]
  exact (F.isSylowOf_top hF.normalizer_A).card_eq

private theorem card_map_phiA_of_isSylowOf (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) :
    Nat.card ↥((Q.subgroupOf D.M).map F.phiA) = 81 := by
  have hJcard : Nat.card ↥(Q.subgroupOf D.M) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.le).toEquiv
  obtain ⟨e⟩ := F.nonempty_mulEquiv_zwr hQ
  have hQ81 : Nat.card ↥Q = 81 := by
    calc Nat.card ↥Q = Nat.card (UC326.ZWr 1) := Nat.card_congr e.toEquiv
      _ = 81 := by
        simpa using (UC326.zwr_card_center_Zwr (n := 1) (by norm_num)).1
  have hJ81 : Nat.card ↥(Q.subgroupOf D.M) = 81 := by rw [hJcard, hQ81]
  have hker_bot : (Q.subgroupOf D.M : Subgroup ↥D.M) ⊓ F.phiA.ker = ⊥ := by
    have hcop : Nat.Coprime (Nat.card ↥((Q.subgroupOf D.M : Subgroup ↥D.M) ⊓ F.phiA.ker)) 3 :=
      Nat.Coprime.of_dvd_left
        (Subgroup.card_dvd_of_le
          (inf_le_right : (Q.subgroupOf D.M : Subgroup ↥D.M) ⊓ F.phiA.ker ≤ F.phiA.ker))
        F.coprime_card_ker_phiA
    have hdiv : Nat.card ↥((Q.subgroupOf D.M : Subgroup ↥D.M) ⊓ F.phiA.ker) ∣ 3 ^ 4 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : (Q.subgroupOf D.M : Subgroup ↥D.M) ⊓ F.phiA.ker ≤ Q.subgroupOf D.M)
      rw [hJ81] at h
      norm_num at h ⊢
      exact h
    exact Subgroup.eq_bot_of_card_eq
      ((Q.subgroupOf D.M : Subgroup ↥D.M) ⊓ F.phiA.ker)
      ((hcop.pow_right 4).eq_one_of_dvd hdiv)
  rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot F.phiA hker_bot, hJ81]

theorem map_phiA_eq_bot (F : A10Frame c) {Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q D.M) (hAQ : F.A ≤ Q) {S : Subgroup G} (hSM : S ≤ D.M)
    (hS : IsPGroup 2 S) (hQS : Q ≤ Subgroup.normalizer (S : Set G)) :
    (S.subgroupOf D.M).map F.phiA = ⊥ := by
  classical
  have hU81 := card_map_phiA_of_isSylowOf F hQ
  obtain ⟨k, hWV⟩ := F.exists_map_le_kleinV hSM hS (hAQ.trans hQS)
  have hJnorm : (Q.subgroupOf D.M : Subgroup ↥D.M) ≤
      Subgroup.normalizer ((S.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hQS (Subgroup.mem_subgroupOf.mp hq)) (s : G))
  have hUnorm : (Q.subgroupOf D.M).map F.phiA ≤
      Subgroup.normalizer (((S.subgroupOf D.M).map F.phiA : Subgroup (Equiv.Perm (Fin 10))) :
        Set (Equiv.Perm (Fin 10))) :=
    CoprimeImage.map_le_normalizer_map F.phiA hJnorm
  by_contra hWne
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hvW : (v : Equiv.Perm (Fin 10)) ∈ (S.subgroupOf D.M).map F.phiA := v.2
  have hv1' : (v : Equiv.Perm (Fin 10)) ≠ 1 := fun hv => hv1 (Subtype.ext hv)
  have hsupp : (v : Equiv.Perm (Fin 10)).support = A10Perm.tBlock k :=
    ((A10Perm.mem_kleinV_iff.mp (hWV hvW)).resolve_left hv1').2
  refine (A10Perm.not_forall_map_tBlock_eq hU81 k) fun u hu => ?_
  have hWu : u * (v : Equiv.Perm (Fin 10)) * u⁻¹ ∈ (S.subgroupOf D.M).map F.phiA :=
    (Subgroup.mem_normalizer_iff.mp (hUnorm hu) (v : Equiv.Perm (Fin 10))).mp hvW
  have hne : u * (v : Equiv.Perm (Fin 10)) * u⁻¹ ≠ 1 := by
    intro hh
    apply hv1'
    have hc := congrArg (fun w : Equiv.Perm (Fin 10) => u⁻¹ * w * u) hh
    simpa [mul_assoc] using hc
  have hsupp' : (u * (v : Equiv.Perm (Fin 10)) * u⁻¹).support = A10Perm.tBlock k :=
    ((A10Perm.mem_kleinV_iff.mp (hWV hWu)).resolve_left hne).2
  rw [Equiv.Perm.support_conj, hsupp] at hsupp'
  exact hsupp'

theorem L_le_normalizer (F : A10Frame c) {S : Subgroup G} (hSM : S ≤ D.M)
    (hS1 : (S.subgroupOf D.M).map F.phiA = ⊥) (hOS : CFSG.Open.pCoreOf 2 c.L ≤ S) :
    c.L ≤ Subgroup.normalizer (S : Set G) := by
  classical
  have hphiS : ∀ (x : G) (hx : x ∈ S), F.phiA ⟨x, hSM hx⟩ = 1 := by
    intro x hx
    have hmem : F.phiA ⟨x, hSM hx⟩ ∈ (S.subgroupOf D.M).map F.phiA :=
      Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr hx)
    rw [hS1] at hmem
    simpa using hmem
  have hconj : ∀ (l : G), l ∈ c.L → ∀ x ∈ S, l * x * l⁻¹ ∈ S := by
    intro l hlL x hxS
    have hlM : l ∈ D.M := c.hyp81.1 hlL
    have hxM : x ∈ D.M := hSM hxS
    have hkM : l * x * l⁻¹ * x⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hlM hxM) (D.M.inv_mem hlM)) (D.M.inv_mem hxM)
    have hkL : l * x * l⁻¹ * x⁻¹ ∈ c.L := by
      have h1 : x * l⁻¹ * x⁻¹ ∈ c.L :=
        (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hxM) l⁻¹).mp
          (Subgroup.inv_mem _ hlL)
      have h2 : l * (x * l⁻¹ * x⁻¹) ∈ c.L := c.L.mul_mem hlL h1
      simpa [show l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) by group] using h2
    have hphik : F.phiA ⟨l * x * l⁻¹ * x⁻¹, hkM⟩ = 1 := by
      have heq : (⟨l * x * l⁻¹ * x⁻¹, hkM⟩ : ↥D.M) =
          ⟨l, hlM⟩ * ⟨x, hxM⟩ * ⟨l, hlM⟩⁻¹ * ⟨x, hxM⟩⁻¹ := rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hphiS x hxS]
      group
    have hkcore : l * x * l⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
      (F.phiA_eq_one_iff hkL).mp hphik
    have hprod : l * x * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x := by group
    rw [hprod]
    exact S.mul_mem (hOS hkcore) hxS
  intro l hlL
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj l hlL x
  · intro hx
    have hmem : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ ∈ S :=
      hconj l⁻¹ (Subgroup.inv_mem _ hlL) (l * x * l⁻¹) hx
    simpa [mul_assoc] using hmem

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
