module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.PCore.RelPPrimeCoreMap
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoStepZero
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLemmaA
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem center_eq_bot_of_isPGroup_two (hG : IsCharTwoType G) (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {b : G} {L Bs : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hb : orderOf b = 3) (hLb : L ≤ Subgroup.centralizer {b})
    (hN : (L.subgroupOf (Subgroup.centralizer {b})).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    (hBs : IsElemAbelian 3 Bs) (hbBs : b ∈ Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hmap : ((Bs ⊓ L).subgroupOf L).map
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) = USixTwo.torU K)
    (hconj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * b * n⁻¹ ∈ L,
      θ (QuotientGroup.mk (⟨n * b * n⁻¹, h⟩ : L)) = USixTwo.threeA hω) :
    Subgroup.center L = ⊥ := by
  classical
  obtain ⟨n, hnBs, heL, hθe⟩ := hconj
  let e : G := n * b * n⁻¹
  let c : MulAut G := MulAut.conj n
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let Ce : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let C : Subgroup G := Subgroup.centralizer (Bs : Set G)
  let R : Subgroup G := relPPrimeCore 3 Cb
  let Oe : Subgroup G := relPPrimeCore 3 Ce
  let Z : Subgroup G := (Subgroup.center L).map L.subtype
  have he3 : orderOf e = 3 := by
    have hsc : SemiconjBy n b e := by
      show n * b = e * n
      rw [show e = n * b * n⁻¹ from rfl]
      group
    exact (SemiconjBy.orderOf_eq n hsc).symm.trans hb
  have heBs : e ∈ Bs := by
    have := (Subgroup.mem_normalizer_iff.mp hnBs) b
    exact this.mp hbBs
  have hBsm : Bs.map c.toMonoidHom = Bs :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnBs
  let π : ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    have hkerEq : π.ker = Subgroup.center L := by
      show (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = _
      rw [MonoidHom.ker_comp_of_injective _ _ θ.injective, QuotientGroup.ker_mk']
    rw [hkerEq]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZ2
    rw [hm]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have he : ∃ u, u * π ⟨e, heL⟩ * u⁻¹ = USixTwo.threeA hω := by
    refine ⟨1, ?_⟩
    simpa [π, MonoidHom.comp_apply, QuotientGroup.mk'_apply, e] using hθe
  have hCb_map : Cb.map c.toMonoidHom = Ce := by
    apply le_antisymm
    · have h := Subgroup.map_centralizer_le_centralizer_image ({b} : Set G) c.toMonoidHom
      have himg : c.toMonoidHom '' ({b} : Set G) = ({e} : Set G) := by
        simpa [c, e, MulAut.conj_apply]
      rw [himg] at h
      simpa [Cb, Ce] using h
    · intro y hy
      refine ⟨c.symm y, ?_, c.apply_symm_apply y⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hy' : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      have h := congrArg (fun t => n⁻¹ * t * n) hy'
      simpa [e, c, MulAut.conj_symm_apply, mul_assoc] using h
  have hC_map : C.map c.toMonoidHom = C := by
    apply le_antisymm
    · have h := Subgroup.map_centralizer_le_centralizer_image (Bs : Set G) c.toMonoidHom
      have hBsimage : c.toMonoidHom '' (Bs : Set G) = Bs := by
        rw [← Subgroup.coe_map, hBsm]
      rw [hBsimage] at h
      simpa [C] using h
    · intro y hy
      refine ⟨c.symm y, ?_, c.apply_symm_apply y⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      have hy := Subgroup.mem_centralizer_iff.mp hy
      intro z hz
      have hcz : c z ∈ Bs := by
        have hBsimage : c.toMonoidHom '' (Bs : Set G) = Bs := by
          rw [← Subgroup.coe_map, hBsm]
        have hmem : c z ∈ c.toMonoidHom '' (Bs : Set G) := ⟨z, hz, rfl⟩
        rwa [hBsimage] at hmem
      have hy' := hy (c z) hcz
      have h := congrArg c.symm hy'
      simpa using h
  have hOe_eq : Oe = R.map c.toMonoidHom := by
    have h := CFSG.Open.relPPrimeCore_map_mulEquiv c Cb 3
    rw [hCb_map] at h
    exact h
  have hStep := relPPrimeCore_le_and_not_two_dvd_index (K := K) hK hω θ hperf hZ2 hb hLb hN
    hcyc hBs hbBs hcard hmap ⟨n, hnBs, heL, hθe⟩
  have hRC : R ≤ C := hStep.1
  have hRoddIdx : ¬ 2 ∣ (R.subgroupOf C).index := hStep.2
  have hRL : R ≤ Subgroup.centralizer (L : Set G) :=
    relPPrimeCore_le_centralizer_L (K := K) hK θ hperf hLb hN
  have hCe : C ≤ Ce := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hg e heBs
  have hKC : Oe ≤ C := by
    rw [hOe_eq, ← hC_map]
    exact Subgroup.map_mono hRC
  have hKodd : ¬ 2 ∣ (Oe.subgroupOf C).index := by
    rw [hOe_eq]
    have hri := Subgroup.relIndex_map_map_of_injective (f := c.toMonoidHom) R C c.injective
    rw [hC_map] at hri
    have hri' : ((R.map c.toMonoidHom).subgroupOf C).index = (R.subgroupOf C).index := by
      simpa [Subgroup.relIndex] using hri
    rw [hri']
    exact hRoddIdx
  have hO2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Ce →
      ((Q ⊔ Oe).subgroupOf Ce).Normal → Q ≤ Oe := by
    intro Q hQ2 hQCe hQN
    have hOeN : (Oe.subgroupOf Ce).Normal :=
      relPPrimeCore_normal (p := 3) (by norm_num) Ce
    haveI : (Oe.subgroupOf Ce).Normal := hOeN
    have hOele : Oe ≤ Ce := relPPrimeCore_le Ce
    have hNle : Q ⊔ Oe ≤ Ce := sup_le hQCe hOele
    have hQnorm : Q.subgroupOf Ce ≤ Subgroup.normalizer ((Oe.subgroupOf Ce) : Set ↥Ce) :=
      Subgroup.le_normalizer_of_normal
    have hcardmul :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (G := ↥Ce) (H := Q.subgroupOf Ce) (K := Oe.subgroupOf Ce) hQnorm
    have hsup : (Q.subgroupOf Ce) ⊔ (Oe.subgroupOf Ce) = (Q ⊔ Oe).subgroupOf Ce :=
      (Subgroup.subgroupOf_sup hQCe hOele).symm
    have hcardN : Nat.card ↥((Q ⊔ Oe).subgroupOf Ce) = Nat.card ↥(Q ⊔ Oe) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
    have hcardQ : Nat.card ↥(Q.subgroupOf Ce) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQCe).toEquiv
    have hcardO : Nat.card ↥(Oe.subgroupOf Ce) = Nat.card Oe :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOele).toEquiv
    have hdvd : Nat.card ↥(Q ⊔ Oe) ∣ Nat.card Oe * Nat.card Q := by
      have hdvd' : Nat.card ↥((Q.subgroupOf Ce) ⊔ (Oe.subgroupOf Ce)) ∣
          Nat.card ↥(Q.subgroupOf Ce) * Nat.card ↥(Oe.subgroupOf Ce) := ⟨_, hcardmul.symm⟩
      rw [hsup, hcardN, hcardQ, hcardO, Nat.mul_comm] at hdvd'
      exact hdvd'
    have hOecop : Nat.Coprime 3 (Nat.card Oe) :=
      coprime_card_relPPrimeCore Nat.prime_three Ce
    have hQcop : Nat.Coprime 3 (Nat.card Q) := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
      rw [hm]
      simpa using Nat.coprime_pow_primes 1 m Nat.prime_three Nat.prime_two (by norm_num)
    have hNcop : Nat.Coprime 3 (Nat.card ↥(Q ⊔ Oe)) :=
      (Nat.Coprime.mul_right hOecop hQcop).of_dvd_right hdvd
    have hNmem : Q ⊔ Oe ≤ Oe :=
      le_sSup (s := {N : Subgroup G | N ≤ Ce ∧ (N.subgroupOf Ce).Normal ∧
        Nat.Coprime 3 (Nat.card N)}) ⟨hNle, hQN, hNcop⟩
    exact le_sup_left.trans hNmem
  have hRoddCard : Odd (Nat.card R) :=
    USixTwo.odd_card_of_le_centralizer_threeA (G := G) (K := K) hG hK hω π hπ hker he3 heL he
      hO2 hCe hKC hKodd hRC hRoddIdx hRL
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hZLc : Z ≤ Cb := hZL.trans hLb
  have hLnorm : Cb ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLb).mp hN
  have hconjZ : ∀ g ∈ Cb, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hz
    have hxL : g * (v : G) * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hLnorm hg) (v : G)).mp v.2
    refine Subgroup.mem_map.mpr ⟨⟨g * (v : G) * g⁻¹, hxL⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hgl : g⁻¹ * (l : G) * g ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem (hLnorm hg)) (l : G)).mp l.2
    have hcomm : (g⁻¹ * (l : G) * g) * (v : G) =
        (v : G) * (g⁻¹ * (l : G) * g) := by
      simpa using congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hv (⟨g⁻¹ * (l : G) * g, hgl⟩ : ↥L))
    calc (l : G) * (g * (v : G) * g⁻¹)
        = g * ((g⁻¹ * (l : G) * g) * (v : G)) * g⁻¹ := by group
      _ = g * ((v : G) * (g⁻¹ * (l : G) * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * (v : G) * g⁻¹) * (l : G) := by group
  have hZnorm : Cb ≤ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨hconjZ g hg z, fun hz => by
      have h := hconjZ g⁻¹ (Cb.inv_mem hg) (g * z * g⁻¹) hz
      rw [show g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z from by group] at h
      exact h⟩
  have hZnormal : (Z.subgroupOf Cb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZLc).mpr hZnorm
  have hZ2' : IsPGroup 2 Z :=
    hZ2.of_equiv (Subgroup.equivMapOfInjective (Subgroup.center L) L.subtype
      L.subtype_injective)
  have hZcop : Nat.Coprime 3 (Nat.card Z) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZ2'
    rw [hm]
    simpa using Nat.coprime_pow_primes 1 m Nat.prime_three Nat.prime_two (by norm_num)
  have hZR : Z ≤ R :=
    le_sSup (s := {N : Subgroup G | N ≤ Cb ∧ (N.subgroupOf Cb).Normal ∧
      Nat.Coprime 3 (Nat.card N)}) ⟨hZLc, hZnormal, hZcop⟩
  have hZodd : Odd (Nat.card Z) :=
    hRoddCard.of_dvd_nat (Subgroup.card_dvd_of_le hZR)
  have hZcard : Nat.card Z = 1 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZ2'
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm, hm0, pow_zero]
    · exfalso
      exact hZodd.not_two_dvd_nat (by rw [hm]; exact dvd_pow_self 2 hmpos.ne')
  have hcenterCard : Nat.card (Subgroup.center L) = 1 := by
    rw [← Subgroup.card_map_of_injective (f := L.subtype)
      (K := Subgroup.center L) L.subtype_injective]
    exact hZcard
  exact (Subgroup.card_eq_one (H := Subgroup.center L)).mp hcenterCard

end CFSG.StandardType.E6QTwo

end
