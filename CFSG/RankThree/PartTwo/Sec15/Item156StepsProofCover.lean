module

public import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item68Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXCover

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof152Gen
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_thetaQuotCentralizer_of_commutator_mem_center {A X : Subgroup G}
    {LB : Subgroup G → Subgroup G} {c : G} (hcA : c ∈ A) (hc3 : c ^ 3 = 1)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hXΔ : X = delta A LB X)
    (hXp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hcC : c ∈ Sec4.thetaQuotCentralizer X)
    (hW : ∀ Q ∈ collectionIn (scriptQ A LB) X, ∀ w ∈ Q ⊓ Subgroup.centralizer ({c} : Set G),
      ∀ a ∈ A, ∀ hm : ⁅w, a⁆ ∈ X,
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨⁅w, a⁆, hm⟩ ∈
          Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    A ≤ Sec4.thetaQuotCentralizer X := by
  intro a ha
  set Z := Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) with hZ
  set σ := Sec4.thetaQuotMulAut ↥X (X.normalizerMonoidHom ⟨a, hAX ha⟩) with hσ
  have hσmk : ∀ x : ↥X, σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (X.normalizerMonoidHom ⟨a, hAX ha⟩ x) :=
    fun x => rfl
  have hQ : ∀ (Q : Subgroup G) (hQ : Q ∈ collectionIn (scriptQ A LB) X) (q : G) (hq : q ∈ Q),
      (σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨q, hQ.2 hq⟩))⁻¹ *
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨q, hQ.2 hq⟩ ∈ Z := by
    intro Q hQ q hq
    have hQX : Q ≤ X := hQ.2
    have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.1.2.2
    have himg := map_inf_centralizer_eq hQX (hAQ hcA) hc3 hcC
    have hq' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨q, hQX hq⟩ ∈
        ((Q ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf X).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) := by
      rw [himg]
      exact ⟨_, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    obtain ⟨w, hwW, hwq⟩ := hq'
    rw [← hwq, hσmk]
    have hwW' : (w : G) ∈ Q ⊓ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_subgroupOf.mp hwW
    have hm : ⁅(w : G), a⁆ ∈ X := by
      rw [commutatorElement_def]
      have h1 : a * (w : G)⁻¹ * a⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hAX ha) _).mp (inv_mem w.2)
      have h2 := mul_mem w.2 h1
      rwa [← mul_assoc, ← mul_assoc] at h2
    have hc := hW Q hQ w hwW' a ha hm
    have he : (X.normalizerMonoidHom ⟨a, hAX ha⟩ w)⁻¹ * w =
        w⁻¹ * (⟨⁅(w : G), a⁆, hm⟩ : ↥X) * w := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe,
        commutatorElement_def]
      group
    rw [← map_inv, ← map_mul, he, map_mul, map_mul, map_inv]
    have hcz := (inferInstance : Z.Normal).conj_mem _ hc
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) w)⁻¹
    rwa [inv_inv] at hcz
  let f₁ : ↥X →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) ⧸ Z :=
    (QuotientGroup.mk' Z).comp ((σ : _ →* _).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)))
  let f₂ : ↥X →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) ⧸ Z :=
    (QuotientGroup.mk' Z).comp (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))
  have hE : ∀ x : ↥X, x ∈ f₁.eqLocus f₂ ↔
      (σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x))⁻¹ *
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x ∈ Z := by
    intro x
    change QuotientGroup.mk' Z (σ (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x)) =
      QuotientGroup.mk' Z (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x) ↔ _
    exact QuotientGroup.eq
  have hXE : X ≤ (f₁.eqLocus f₂).map X.subtype := by
    refine hXΔ.le.trans (sSup_le fun Q hQ' => ?_)
    intro q hq
    exact ⟨⟨q, hQ'.2 hq⟩, (hE _).mpr (hQ Q hQ' q hq), rfl⟩
  have hall : ∀ y : ↥X ⧸ aschbacherSolvableCore 3 ↥X, (σ y)⁻¹ * y ∈ Z := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) y
    obtain ⟨x', hx', hxx'⟩ := hXE x.2
    have hxeq : x' = x := Subtype.ext hxx'
    rw [← hxeq]
    exact (hE x').mp hx'
  have hσ1 : σ = 1 := eq_one_of_inv_mul_mem_center hXp σ hall
  exact ⟨⟨a, hAX ha⟩, MonoidHom.mem_ker.mpr hσ1, rfl⟩

theorem le_inf_sup_theta_of_item142 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A)
    {X : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hXΔ : X = delta A (lB A) X)
    (hXq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hX3 : 3 ∣ Nat.card ((↥X ⧸ aschbacherSolvableCore 3 ↥X) ⧸
      Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)))
    (hcC : c ∈ Sec4.thetaQuotCentralizer X) (hAnc : ¬ A ≤ Sec4.thetaQuotCentralizer X) :
    X ≤ (X ⊓ L) ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O := pPrimeCoreOf 3 H with hO
  have hcA : c ∈ A := hS13.mem_A
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hS13.commute ha hcA)
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H :=
    centralizer_singleton_le_normalizer_zpowers c
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_j2 h hJ
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 H
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 H)
  have hOc : O ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_invariantPiSubgroups hcA hS13.orderOf_eq
      ⟨pPrimeCoreOf_le 3 H, (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3,
        (hAC.trans hCH).trans hHO⟩
  have hOL : O ≤ Subgroup.normalizer (L : Set G) := hOc.trans hCL
  set N := X ⊓ (L ⊔ O) with hN
  have hLON : L ⊔ O ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hOL
  have hcovc : ((X ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
    refine map_inf_centralizer_eq_top le_rfl (hAX hcA) hc3 hcC ?_
    rw [Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hCN : X ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (N : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans (le_normalizer_sup hCL (hCH.trans hHO)))
  have hNn := map_subgroupOf_normal_of_le_normalizer hCN hcovc
  have hNtop : (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hNn with ht | hcen
    · exact ht
    · exfalso
      refine hAnc (le_thetaQuotCentralizer_of_commutator_mem_center hcA hc3 hAX hXΔ hXq.1 hcC ?_)
      intro Q hQ w hw b hb hm
      have hQ3 : ¬ 3 ∣ Nat.card Q :=
        (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
      have hWinv : Q ⊓ Subgroup.centralizer ({c} : Set G) ∈
          invariantPiSubgroups H A (piCompl 3) :=
        ⟨inf_le_right.trans hCH,
          fun r hr => hQ.1.1.2.1 r (hr.trans (Subgroup.card_dvd_of_le inf_le_left)),
          Late.le_normalizer_inf hQ.1.1.2.2 (hAC.trans Subgroup.le_normalizer)⟩
      have hwLO : ⁅w, b⁆ ∈ L ⊔ O := commutator_le_sup_of_item142 h hJ h142 hWinv
        (Subgroup.commutator_mem_commutator hw hb)
      exact hcen ⟨⟨⁅w, b⁆, hm⟩, Subgroup.mem_subgroupOf.mpr ⟨hm, hwLO⟩, rfl⟩
  have hMn := map_subgroupOf_normal_of_le_normalizer (V := X ⊓ L)
    (Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans hLON)) hNtop
  have hMtop : ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) =
      ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hMn with ht | hcen
    · exact ht
    · exfalso
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 hX3
      obtain ⟨xb, rfl⟩ := QuotientGroup.mk'_surjective _ y
      have hxbN : xb ∈ (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
        hNtop ▸ Subgroup.mem_top xb
      obtain ⟨m, hmN, rfl⟩ := hxbN
      have hm0 : orderOf m ≠ 0 := (orderOf_pos m).ne'
      obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
      have hmr : ((m ^ r : ↥X) : G) ^ (3 ^ e) = 1 := by
        rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one, Subgroup.coe_one]
      have hmLO : ((m ^ r : ↥X) : G) ∈ L ⊔ O := by
        rw [Subgroup.coe_pow]
        exact pow_mem (Subgroup.mem_subgroupOf.mp hmN).2 r
      have hmrL : ((m ^ r : ↥X) : G) ∈ L :=
        Sec6.mem_of_mem_sup_of_pow_eq_one hOL hO3 hmLO hmr
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (m ^ r) ∈
          ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
        ⟨_, Subgroup.mem_subgroupOf.mpr ⟨(m ^ r).2, hmrL⟩, rfl⟩
      have h2 : (QuotientGroup.mk' (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X))
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) m)) ^ r = 1 := by
        rw [← map_pow, ← map_pow]
        exact (QuotientGroup.eq_one_iff _).mpr (hcen h1)
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hy] at h3
      exact hr3 h3
  intro x hx
  have hq : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨x, hx⟩ ∈
      ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
    hMtop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hq
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have he : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy) ⟨_, hyx, rfl⟩

theorem not_le_thetaQuotCentralizer_of_subset_closure {A X : Subgroup G} (hA : Late.IsE27 A)
    {c d : G} (hcA : c ∈ A) (hdA : d ∈ A)
    (hsub : Late.sectionCentralizer A X (inSubgroup (aschbacherSolvableCore 3) X) ⊆
      (Subgroup.closure {c, d} : Set G)) :
    ¬ A ≤ Sec4.thetaQuotCentralizer X := by
  intro hAle
  have hAsub : A ≤ Subgroup.closure ({c, d} : Set G) := fun a ha =>
    hsub (mem_sectionCentralizer_of_mem_thetaQuotCentralizer ha (hAle ha))
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hcd : Subgroup.closure ({c, d} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hA.1.1.is_comm.comm
      ⟨x, Subgroup.zpowers_le.mpr hcA hx⟩ ⟨y, Subgroup.zpowers_le.mpr hdA hy⟩)
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hc' : Nat.card (Subgroup.zpowers c) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)
  have hd' : Nat.card (Subgroup.zpowers d) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
  have hpos : 0 < Nat.card (Subgroup.zpowers c ⊓ Subgroup.zpowers d : Subgroup G) :=
    Nat.card_pos
  have h9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) ≤ 9 := by
    have h2 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) ≤
        Nat.card (Subgroup.zpowers c) * Nat.card (Subgroup.zpowers d) := by
      rw [← h1]
      exact Nat.le_mul_of_pos_right _ hpos
    have h3 : Nat.card (Subgroup.zpowers c) * Nat.card (Subgroup.zpowers d) ≤ 3 * 3 :=
      Nat.mul_le_mul hc' hd'
    omega
  have hle := Subgroup.card_le_of_le hAsub
  rw [hcd, hA.2] at hle
  omega

end CFSG.RankThree.PartTwo.Sec15.Proof156
