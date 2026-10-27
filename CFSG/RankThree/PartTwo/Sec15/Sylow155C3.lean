module

import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Frattini

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Sylow155C3

theorem not_dvd_index_oPrimeResidual (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q] [Finite Q] :
    ¬ p ∣ (oPrimeResidual p Q).index := by
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  have hP : (P : Subgroup Q) ≤ oPrimeResidual p Q := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    simpa using congrArg Subtype.val hk
  exact fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hP))

theorem isPGroup_of_sylow_le_center {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : pPrimeCore p Q = ⊥) (P : Sylow p Q) (hP : (P : Subgroup Q) ≤ Subgroup.center Q) :
    IsPGroup p Q := by
  have hNC : Subgroup.normalizer ((P : Subgroup Q) : Set Q) ≤
      Subgroup.centralizer ((P : Subgroup Q) : Set Q) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_center_iff.mp (hP hx) g).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hN : (MonoidHom.transferSylow P hNC).ker ≤ pPrimeCore p Q :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hNC)⟩
  rw [hQ, le_bot_iff] at hN
  have htop := hcomp.sup_eq_top
  rw [hN, bot_sup_eq] at htop
  intro g
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, htop ▸ Subgroup.mem_top g⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem isPGroup_of_le_center {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hQ : pPrimeCore p Q = ⊥) {B : Subgroup Q} [B.Normal] (hidx : ¬ p ∣ B.index)
    (hB : B ≤ Subgroup.center Q) : IsPGroup p Q := by
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  refine isPGroup_of_sylow_le_center hQ P (le_trans ?_ hB)
  have hmap : IsPGroup p ((P : Subgroup Q).map (QuotientGroup.mk' B)) := P.isPGroup'.map _
  have hbot : (P : Subgroup Q).map (QuotientGroup.mk' B) = ⊥ := by
    rcases hmap.card_eq_or_dvd with h1 | hdvd
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (hdvd.trans (Subgroup.card_subgroup_dvd_card _)) hidx
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem le_pPrimeCore_of_le_sup {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {U : Type*} [Group U] [Finite U] {B Z R : Subgroup U} [B.Normal] (hidx : ¬ p ∣ B.index)
    (hBZ : B ≤ Z ⊔ pPrimeCore p U) (hZ : ⁅Z, (⊤ : Subgroup U)⁆ ≤ pPrimeCore p U)
    (hR : IsPGroup q R) : R ≤ pPrimeCore p U := by
  let f := QuotientGroup.mk' (pPrimeCore p U)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hNf : (pPrimeCore p U).map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hZc : Z.map f ≤ Subgroup.center (U ⧸ pPrimeCore p U) := by
    have h1 : ⁅Z.map f, (⊤ : Subgroup (U ⧸ pPrimeCore p U))⁆ = ⊥ := by
      rw [← Subgroup.map_top_of_surjective f hf, ← Subgroup.map_commutator, eq_bot_iff, ← hNf]
      exact Subgroup.map_mono hZ
    rwa [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ] at h1
  have hBc : B.map f ≤ Subgroup.center (U ⧸ pPrimeCore p U) := by
    refine le_trans ?_ hZc
    calc B.map f ≤ (Z ⊔ pPrimeCore p U).map f := Subgroup.map_mono hBZ
      _ = Z.map f ⊔ (pPrimeCore p U).map f := Subgroup.map_sup _ _ f
      _ = Z.map f := by rw [hNf, sup_bot_eq]
  haveI : (B.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hidx' : ¬ p ∣ (B.map f).index := fun h => hidx (h.trans (Subgroup.index_map_dvd B hf))
  have hQ : IsPGroup p (U ⧸ pPrimeCore p U) :=
    isPGroup_of_le_center (pPrimeCore_quotient_pPrimeCore_eq_bot p) hidx' hBc
  have hRf : R.map f = ⊥ :=
    (IsPGroup.disjoint_of_ne q p hpq.symm (R.map f) ⊤ (hR.map f) (hQ.to_subgroup ⊤)).eq_bot_of_le
      le_top
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hRf

variable {G : Type} [Group G] [Finite G]

theorem r_le_pPrimeCoreOf_u155 {A X K Y M T P : Subgroup G} (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hBXW : b155 A M X ≤ X ⊔ w155 A M X)
    (hW : w155 A M X ≤ pPrimeCoreOf 3 (u155 A M X)) :
    CFSG.Open.pCoreOf 2 Y ≤ pPrimeCoreOf 3 (u155 A M X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUC : u155 A M X ≤ centralizerSection X (CFSG.Open.pCoreOf 2 X) := inf_le_right
  have hV : (CFSG.Open.pCoreOf 2 X).subgroupOf (u155 A M X) ≤ pPrimeCore 3 ↥(u155 A M X) := by
    have hV2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 X).subgroupOf (u155 A M X)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_of_injective _ Subtype.coe_injective
    haveI : ((CFSG.Open.pCoreOf 2 X).subgroupOf (u155 A M X)).Normal := by
      refine ⟨fun a ha u => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      obtain ⟨-, hu, -⟩ := hUC u.2
      simpa using (Subgroup.mem_normalizer_iff.mp hu a).mp ha
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hZ : ⁅X.subgroupOf (u155 A M X), (⊤ : Subgroup ↥(u155 A M X))⁆ ≤
      pPrimeCore 3 ↥(u155 A M X) := by
    rw [Subgroup.commutator_le]
    intro z hz u _
    apply hV
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨-, -, hu⟩ := hUC u.2
    simpa [commutatorElement_def] using hu z (Subgroup.mem_subgroupOf.mp hz)
  have hWX : w155 A M X ≤ Subgroup.normalizer (X : Set G) := fun w hw =>
    (hUC (Proof155Wx.w155_le_u155 A M X hw)).1
  have hBZ : oPrimeResidual 3 ↥(u155 A M X) ≤
      X.subgroupOf (u155 A M X) ⊔ pPrimeCore 3 ↥(u155 A M X) := by
    intro b hb
    have hbG : (b : G) ∈ b155 A M X := by
      show (b : G) ∈ (oPrimeResidual 3 ↥(u155 A M X)).map (u155 A M X).subtype
      exact Subgroup.mem_map_of_mem _ hb
    have hmem : (b : G) ∈ ((X ⊔ w155 A M X : Subgroup G) : Set G) := hBXW hbG
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X (w155 A M X) hWX] at hmem
    obtain ⟨x, hx, w, hw, hxw⟩ := Set.mem_mul.mp hmem
    have hw2 : w ∈ (pPrimeCore 3 ↥(u155 A M X)).map (u155 A M X).subtype := hW hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw2
    have hxU : x ∈ u155 A M X := by
      rw [eq_mul_inv_of_mul_eq hxw]
      exact (u155 A M X).mul_mem b.2 ((u155 A M X).inv_mem w'.2)
    have hb' : b = ⟨x, hxU⟩ * w' := Subtype.ext hxw.symm
    rw [hb']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hx) hw'
  have hR2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 Y).subgroupOf (u155 A M X)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).comap_of_injective _ Subtype.coe_injective
  haveI := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 3 ↥(u155 A M X)
  have hRU' : (CFSG.Open.pCoreOf 2 Y).subgroupOf (u155 A M X) ≤ pPrimeCore 3 ↥(u155 A M X) :=
    le_pPrimeCore_of_le_sup (p := 3) (q := 2) (by norm_num)
      (not_dvd_index_oPrimeResidual 3 ↥(u155 A M X)) hBZ hZ hR2
  rw [← Subgroup.map_subgroupOf_eq_of_le (Sylow155F.r_le_u155 hE hRP)]
  exact Subgroup.map_mono hRU'

theorem w155_le_pPrimeCoreOf_of_coprime {A M X : Subgroup G}
    (hcop : Nat.Coprime 3 (Nat.card (w155 A M X))) :
    w155 A M X ≤ pPrimeCoreOf 3 (u155 A M X) := by
  have hUC : u155 A M X ≤ centralizerSection X (CFSG.Open.pCoreOf 2 X) := inf_le_right
  exact le_pPrimeCoreOf (Proof155Wx.w155_le_u155 A M X)
    (Proof155Wx.le_normalizer_w155 (inf_le_left.trans Subgroup.le_normalizer)
      (fun _ hu => (hUC hu).1)) hcop

end Sylow155C3

end CFSG.RankThree.PartTwo.Sec15
