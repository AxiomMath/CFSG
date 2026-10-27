module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofKb
import CFSG.RankThree.PartTwo.Sec17.Item1713
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
public import CFSG.RankThree.PartTwo.Sec17.C174Base
public import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofSolv

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem zpowers_not_mem_omegaA_of_mem_inf
    (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {b : G} (hb : b ∈ A ⊓ L) :
    Subgroup.zpowers b ∉ omegaA A := by
  intro hbΩ
  have hbc : Subgroup.zpowers b = Subgroup.zpowers c := by
    rw [hΩ] at hbΩ
    exact hbΩ
  have hcL : c ∈ L := by
    have hcb : c ∈ Subgroup.zpowers b := by
      rw [hbc]
      exact Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hb).2) hcb
  have hcen : ∀ x ∈ L, c * x = x * c := by
    intro x hx
    have hC : x ∈ Subgroup.centralizer {c} :=
      CFSG.RankThree.PartTwo.Sec14.le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1 hx
    exact (Subgroup.mem_centralizer_iff.mp hC) c (Set.mem_singleton c)
  obtain ⟨ĉ, hĉ⟩ : ∃ ĉ : ↥L, (ĉ : G) = c := ⟨⟨c, hcL⟩, rfl⟩
  have hcomm : ∀ x : ↥L, Commute x ĉ := by
    intro x
    show x * ĉ = ĉ * x
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hĉ]
    exact (hcen x.1 x.2).symm
  have hN : (Subgroup.zpowers ĉ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hk : g * ĉ ^ k = ĉ ^ k * g := (Commute.zpow_right (hcomm g) k).eq
    rw [hk, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  haveI hNmap : ((Subgroup.zpowers ĉ).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  have hsimple := (lBar_simple_and_pRank h.toSec14Std).1
  have hna := lBar_nonabelian h.toSec14Std
  rcases hsimple.eq_bot_or_eq_top_of_normal
      ((Subgroup.zpowers ĉ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) with hbot | htop
  ·
    have hmem : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ĉ ∈
        (Subgroup.zpowers ĉ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers ĉ)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hĉθ : ĉ ∈ aschbacherSolvableCore 3 ↥L := (QuotientGroup.eq_one_iff ĉ).mp hmem
    have hc3 : orderOf c = 3 := by
      rw [← Nat.card_zpowers]
      exact (CFSG.RankThree.PartTwo.Sec13.mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1
    have hord : orderOf ĉ = 3 := by
      have e : orderOf c = orderOf ĉ := by
        rw [← hĉ, Subgroup.orderOf_coe]
      rw [← e]
      exact hc3
    have hdvd : 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) := by
      have := orderOf_dvd_natCard (⟨ĉ, hĉθ⟩ : aschbacherSolvableCore 3 ↥L)
      rwa [Subgroup.orderOf_mk, hord] at this
    exact CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore hdvd
  ·
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ (Subgroup.zpowers ĉ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
      rw [htop]
      exact Subgroup.mem_top a
    have hb' : b ∈ (Subgroup.zpowers ĉ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
      rw [htop]
      exact Subgroup.mem_top b
    obtain ⟨n1, hn1, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨n2, hn2, rfl⟩ := Subgroup.mem_map.mp hb'
    apply hab
    rw [← map_mul, ← map_mul]
    obtain ⟨k1, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn1
    obtain ⟨k2, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn2
    rw [(Commute.zpow_zpow_self ĉ k1 k2).eq]

theorem not_isSolvable_delta_centralizer (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hXQ : X ∈ scriptQ A (lB A)) {K : Subgroup G}
    (hθ : CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K)
    (hcen : (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKq : K ∈ thetaComponentsIn X) {b : G} (hb : b ∈ A ⊓ L) (hb1 : b ≠ 1) :
    ¬ Group.IsSolvable ↥(delta A (lB A) (Subgroup.centralizer ({b} : Set G))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKX : K ≤ X := le_of_mem_thetaComponentsIn hKq
  intro hD
  have hX3 : Nat.Coprime 3 (Nat.card X) := coprime_three_card_of_mem_scriptQ hXQ
  have hK3 : ¬ 3 ∣ Nat.card K :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKX) hX3)
  have hbA : b ∈ A := hb.1
  have hbY : b ∈ Y₀ := h.le_y0 hb.2
  have hb3 : orderOf b = 3 := orderOf_eq_prime (HeadProof.pow_three_of_std h hbA) hb1
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hbA)
  have hzK : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (hAK hbA)
  have hzY : Subgroup.zpowers b ≤ Y₀ := Subgroup.zpowers_le.mpr hbY
  have hzP : IsPGroup 3 (Subgroup.zpowers b) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hb3, pow_one]
  have hK0 : (K : Set G) ⊆ Subgroup.normalizer (Y₀ : Set G) := fun k hk => (hcen hk).1
  have hQnorm : ∀ x ∈ Subgroup.normalizer (Y₀ : Set G), ∀ q ∈ CFSG.Open.pCoreOf 2 Y₀,
      x * q * x⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀ hx) q).mp hq
  have hQp : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y₀) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  let N : Subgroup ↥K := (CFSG.Open.pCoreOf 2 Y₀).comap K.subtype
  have hNn : N.Normal := ⟨fun n hn g => hQnorm (g : G) (hK0 g.2) (n : G) hn⟩
  have hNp : IsPGroup 2 N := hQp.comap_of_injective K.subtype K.subtype_injective
  have hNpc : N ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hNn, hNp⟩
  have hNθ : N ≤ aschbacherSolvableCore 3 ↥K := hNpc.trans hθ.le
  have hcomm : ⁅K, Subgroup.zpowers b⁆ ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype := by
    rw [Subgroup.commutator_le]
    intro k hk y hy
    have hyN : y ∈ Subgroup.normalizer (K : Set G) := hzK hy
    have hKmem : ⁅k, y⁆ ∈ K := by
      have hconj : y * k⁻¹ * y⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp hyN k⁻¹).mp (K.inv_mem hk)
      rw [commutatorElement_def, show k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) by group]
      exact K.mul_mem hk hconj
    have hQmem : ⁅k, y⁆ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
      rw [commutatorElement_def]
      exact (hcen hk).2 y (hzY hy)
    have hmemN : (⟨⁅k, y⁆, hKmem⟩ : ↥K) ∈ N := hQmem
    exact Subgroup.mem_map.mpr ⟨⟨⁅k, y⁆, hKmem⟩, hNθ hmemN, rfl⟩
  have hfact : K = ⁅K, Subgroup.zpowers b⁆ ⊔
      (K ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G)) :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three (Subgroup.zpowers b) K hzP hK3 hzK
  set M : Subgroup G := K ⊓ Subgroup.centralizer ({b} : Set G) with hM
  have hMK : M ≤ K := inf_le_left
  have hAM : A ≤ Subgroup.normalizer (M : Set G) :=
    CFSG.RankThree.PartTwo.Late.le_normalizer_inf hAK (hAb.trans Subgroup.le_normalizer)
  have hMQ : M ∈ scriptQ A (lB A) :=
    CFSG.RankThree.PartTwo.Sec14.mem_scriptQ_of_le hXQ (inf_le_left.trans hKX) hAM
  have hMD : M ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) :=
    CFSG.RankThree.PartTwo.Sec14.le_delta hMQ inf_le_right
  have hMsolv : Group.IsSolvable ↥M :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hMD).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMD).surjective
  have hKT : K ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype ⊔ M :=
    hfact.le.trans (sup_le_sup hcomm fun x hx =>
      ⟨hx.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers b)) hx.2⟩)
  have hMK' : (M.subgroupOf K).map K.subtype = M := Subgroup.map_subgroupOf_eq_of_le hMK
  have hTM : aschbacherSolvableCore 3 ↥K ⊔ M.subgroupOf K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hmap : (aschbacherSolvableCore 3 ↥K ⊔ M.subgroupOf K).map K.subtype
        = (aschbacherSolvableCore 3 ↥K).map K.subtype ⊔ M := by
      rw [Subgroup.map_sup, hMK']
    have hk : (k : G) ∈ (aschbacherSolvableCore 3 ↥K ⊔ M.subgroupOf K).map K.subtype := by
      rw [hmap]
      exact hKT k.2
    obtain ⟨w, hw, hwk⟩ := Subgroup.mem_map.mp hk
    have hwk' : w = k := Subtype.ext hwk
    rw [← hwk']
    exact hw
  let g : ↥M →* ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)).comp (Subgroup.inclusion hMK)
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥K) z
    have hk : k ∈ aschbacherSolvableCore 3 ↥K ⊔ M.subgroupOf K := by
      rw [hTM]
      exact Subgroup.mem_top k
    obtain ⟨y, hy, m, hm, hym⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    refine ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, ?_⟩
    have hy1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) y = 1 :=
      (QuotientGroup.eq_one_iff y).mpr hy
    show QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) m
        = QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K) k
    rw [← hym, map_mul, hy1, one_mul]
  have hKTsolv : Group.IsSolvable (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    Group.isSolvable_of_surjective (f := g) hgsurj
  obtain ⟨-, hQ0⟩ := mem_thetaComponentsIn_iff.mp hKq
  obtain ⟨-, -, hQ1⟩ := hQ0
  obtain ⟨hperf1, hsimp, -⟩ := hQ1
  have hnt1 : Nontrivial (↥(K.subgroupOf X) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf X)) :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center _))
  have hsolv1 : ¬ Group.IsSolvable
      (↥(K.subgroupOf X) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf X)) := by
    intro hs
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
      (G := ↥(K.subgroupOf X) ⧸ aschbacherSolvableCore 3 ↥(K.subgroupOf X))).ne
      hperf1.commutator_eq_top
  have e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have hθe := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  let e' := QuotientGroup.congr _ _ e hθe
  have hnot : ¬ Group.IsSolvable (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
    intro hs
    exact hsolv1 (Group.isSolvable_of_surjective (f := e'.symm.toMonoidHom) e'.symm.surjective)
  exact hnot hKTsolv

theorem conj_mem_thetaComponentsIn_of_mem_normalizer {H K : Subgroup G}
    (hK : K ∈ thetaComponentsIn H) {n : G} (hn : n ∈ Subgroup.normalizer (H : Set G)) :
    K.map (MulAut.conj n).toMonoidHom ∈ thetaComponentsIn H := by
  have hHn : H.map (MulAut.conj n).toMonoidHom = H := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hn h).mp hh
    · intro h hh
      refine ⟨n⁻¹ * h * n⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (inv_mem hn) h).mp hh, ?_⟩
      simp only [MulAut.conj_apply, inv_inv, MulEquiv.coe_toMonoidHom]
      group
  have := map_mem_thetaComponentsIn (MulAut.conj n) hK
  rwa [hHn] at this

open Proof17Res12 in
theorem delta_le_of_suzuki_member (h : Sec17Std G A c L Y₀)
    (h166 : Item166 A (lB A)) (h146 : Item146 A (lB A)) {D : Subgroup G} (hDtop : D ≠ ⊤)
    (hDΔ : D = delta A (lB A) D) (hD3 : ¬ 3 ∣ Nat.card D) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn D) {n : ℕ}
    (hn : CFSG.Blueprint.SuzukiModel (↥J ⧸ aschbacherSolvableCore 3 ↥J) 2 n)
    (hY3 : ∀ Y ∈ scriptY3 A (lB A), Y ≤ Subgroup.normalizer (Y₀ : Set G)) :
    D ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := CFSG.RankThree.PartTwo.Sec17.HeadProof.isE27_of_std h
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    rw [hDΔ]
    exact Sec14.le_normalizer_delta _
  have hDQ : D ∈ scriptQ A (lB A) :=
    CFSG.RankThree.PartTwo.Sec16.Proof165.mem_scriptQ_of_three hA h146 hDΔ hAD hD3
  have hD3' : Nat.Coprime 3 (Nat.card D) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3
  have hJD : J ≤ D := le_of_mem_thetaComponentsIn hJ
  have hHD : D ⊔ A ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer hAD
  have hconjSz : ∀ x : G, CFSG.Blueprint.SuzukiModel
      (↥(J.map (MulAut.conj x).toMonoidHom) ⧸
        aschbacherSolvableCore 3 ↥(J.map (MulAut.conj x).toMonoidHom)) 2 n := by
    intro x
    let e : ↥J ≃* ↥(J.map (MulAut.conj x).toMonoidHom) :=
      J.equivMapOfInjective _ (MulAut.conj x).injective
    have hθe : (aschbacherSolvableCore 3 ↥J).map e.toMonoidHom =
        aschbacherSolvableCore 3 ↥(J.map (MulAut.conj x).toMonoidHom) :=
      CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
    have e' := QuotientGroup.congr _ _ e hθe
    exact suzukiModel_of_mulEquiv' e'.symm hn
  have hconjM : ∀ x ∈ D ⊔ A,
      J.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (Y₀ : Set G) := by
    intro x hx
    have hJx : J.map (MulAut.conj x).toMonoidHom ∈ thetaComponentsIn D :=
      conj_mem_thetaComponentsIn_of_mem_normalizer hJ (hHD hx)
    obtain ⟨-, hcend⟩ :=
      (h166 Y₀ h.mem_y0Star).1 D ⟨hDtop, hAD⟩ hDΔ _ hJx ⟨n, hconjSz x⟩
    exact fun y hy => (hcend hy).1
  have hJxD : ∀ x ∈ D ⊔ A, J.map (MulAut.conj x).toMonoidHom ≤ D := by
    intro x hx
    rintro _ ⟨j, hj, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHD hx) j).mp (hJD hj)
  set E : Subgroup G := ⨆ x : (D ⊔ A : Subgroup G), J.map (MulAut.conj (x : G)).toMonoidHom
  have hmemE : ∀ x ∈ D ⊔ A, ∀ j ∈ J, x * j * x⁻¹ ∈ E := fun x hx j hj =>
    Subgroup.mem_iSup_of_mem (⟨x, hx⟩ : (D ⊔ A : Subgroup G)) ⟨j, hj, rfl⟩
  have hJE : J ≤ E := fun j hj => by simpa using hmemE 1 (D ⊔ A).one_mem j hj
  have hEM : E ≤ Subgroup.normalizer (Y₀ : Set G) := iSup_le fun x => hconjM x x.2
  have hED : E ≤ D := iSup_le fun x => hJxD x x.2
  have hHN : ∀ g ∈ D ⊔ A, g ∈ Subgroup.normalizer (E : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    refine Subgroup.iSup_induction (C := fun x => g * x * g⁻¹ ∈ E) _ hx ?_ ?_ ?_
    · rintro ⟨k, hk⟩ _ ⟨j, hj, rfl⟩
      have h1 := hmemE (g * k) ((D ⊔ A).mul_mem hg hk) j hj
      have key : g * k * j * (g * k)⁻¹ = g * (k * j * k⁻¹) * g⁻¹ := by group
      rw [key] at h1
      exact h1
    · simp only [mul_one, mul_inv_cancel]
      exact E.one_mem
    · intro x y hx hy
      have := E.mul_mem hx hy
      convert this using 1
      group
  have hDE : D ≤ Subgroup.normalizer (E : Set G) := fun g hg => hHN g (Subgroup.mem_sup_left hg)
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := fun a ha => hHN a (Subgroup.mem_sup_right ha)
  have hE3 : Nat.Coprime 3 (Nat.card E) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hED) hD3'
  have hEinv : E ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three E).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hE3), hAE⟩
  have hEQ : E ∈ scriptQ A (lB A) := mem_scriptQ_of_le hDQ hED hAE
  have hJ2 : 2 ∣ Nat.card J := by
    have h1 : 2 ∣ Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) :=
      CFSG.RankThree.PartTwo.KFacts.two_dvd_card_of_suzukiModel hn
    have h2 : Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) ∣ Nat.card ↥J :=
      Subgroup.index_dvd_card (H := aschbacherSolvableCore 3 ↥J)
    exact h1.trans h2
  have hE2 : 2 ∣ Nat.card E := hJ2.trans (Subgroup.card_dvd_of_le hJE)
  obtain ⟨T, hTA, hT1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 2
      Nat.prime_three Nat.prime_two A E hA.isPGroup hAE hE3 hE2
  set T' := (T : Subgroup E).map E.subtype with hT'
  have hT'syl : CFSG.ABGLocalTools.IsSylowOf 2 T' E := ⟨T, rfl⟩
  have hT'E : T' ≤ E := Subgroup.map_subtype_le _
  have hT'Q : T' ∈ scriptQ A (lB A) := mem_scriptQ_of_le hEQ hT'E hTA
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
  have hEtop : E ≠ ⊤ := fun htop => hDtop (eq_top_iff.mpr (htop ▸ hED))
  have hNT : delta A (lB A) (Subgroup.normalizer (T' : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G) :=
    hY3 _ (delta_normalizer_mem_scriptY3 h hT'Q hT'2 hT1 hT'E hEtop)
  rw [hDΔ]
  refine sSup_le fun Q hQ => ?_
  have hQD : Q ≤ D := hQ.2
  have hQE : Q ≤ Subgroup.normalizer (E : Set G) := hQD.trans hDE
  have hHinv : Q ⊔ E ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_piCompl_sup hQ.1.1.2.1 hEinv.2.1 hQE,
      Sec14.le_normalizer_sup hQ.1.1.2.2 hAE⟩
  have hHQ : Q ⊔ E ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hHinv
    rwa [le_antisymm (delta_le _)
      (sup_le (le_delta hQ.1 le_sup_left) (le_delta hEQ le_sup_right))] at this
  have hfr := le_sup_inf_normalizer (H := Q ⊔ E) le_sup_right
    (sup_le hQE Subgroup.le_normalizer) hT'syl
  have hAN : A ≤ Subgroup.normalizer ((Subgroup.normalizer (T' : Set G) : Subgroup G) : Set G) :=
    hTA.trans Subgroup.le_normalizer
  have hHNT : (Q ⊔ E) ⊓ Subgroup.normalizer (T' : Set G) ≤
      delta A (lB A) (Subgroup.normalizer (T' : Set G)) :=
    le_delta (mem_scriptQ_of_le hHQ inf_le_left (Late.le_normalizer_inf hHQ.1.2.2 hAN))
      inf_le_right
  exact (le_sup_left.trans hfr).trans (sup_le hEM (hHNT.trans hNT))

end CFSG.RankThree.PartTwo.Sec17.C174
