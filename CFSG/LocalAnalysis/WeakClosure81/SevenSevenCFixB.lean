module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenCFix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

section FixB

variable {G : Type} [Group G] [Finite G]

variable {V H E J V₁ V₂ V₃ A B : Subgroup G}

lemma seven_seven_c_fix_b_iSub_elemAbelian (h : Hyp73 V H E J) :
    IsElemAbelian 2 (iSub V H E) :=
  seven_two_iSub_isElemAbelian_uncond h.elemAbelian h.ti h.abelian h.omega_le

lemma seven_seven_c_fix_b_mul_comm_of_le_iSub (h : Hyp73 V H E J) {A : Subgroup G}
    (hAle : A ≤ iSub V H E) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  haveI : IsMulCommutative ↥(iSub V H E) := (seven_seven_c_fix_b_iSub_elemAbelian h).1
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨a, hAle ha⟩ : ↥(iSub V H E)) ⟨b, hAle hb⟩)

lemma seven_seven_c_fix_b_exists_mem_not_mem_iSub (h : Hyp73 V H E J) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) : ∃ v ∈ U, v ∉ iSub V H E := by
  have hnot : ¬ U ≤ iSub V H E := by
    intro hle
    obtain ⟨g, -, -, hpc⟩ := mem_omegaSet.mp hU
    exact hpc (hle.trans (h.iSub_le.trans h.pcore_le))
  exact Set.not_subset.mp hnot

lemma seven_seven_c_fix_b_normalizer_of_three (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    V₁ ≤ Subgroup.normalizer (A : Set G) ∧ V₂ ≤ Subgroup.normalizer (A : Set G) ∧
      V₃ ≤ Subgroup.normalizer (A : Set G) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (le_sup_left : V₁ ≤ V₁ ⊔ V₂).trans
      ((le_sup_left : V₁ ⊔ V₂ ≤ V₁ ⊔ V₂ ⊔ V₃).trans hA.normalizes)
  · exact (le_sup_right : V₂ ≤ V₁ ⊔ V₂).trans
      ((le_sup_left : V₁ ⊔ V₂ ≤ V₁ ⊔ V₂ ⊔ V₃).trans hA.normalizes)
  · exact (le_sup_right : V₃ ≤ V₁ ⊔ V₂ ⊔ V₃).trans hA.normalizes

lemma seven_seven_c_fix_b_commutator_le_A (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ⁅A, V₁⁆ ≤ A ∧ ⁅A, V₂⁆ ≤ A ∧ ⁅A, V₃⁆ ≤ A := by
  obtain ⟨hN1, hN2, hN3⟩ := seven_seven_c_fix_b_normalizer_of_three hA
  exact ⟨(commutator_le_inf_of_mem_omegaSet h hc.mem₁ hA.le_iSub hN1).trans inf_le_left,
    (commutator_le_inf_of_mem_omegaSet h hc.mem₂ hA.le_iSub hN2).trans inf_le_left,
    (commutator_le_inf_of_mem_omegaSet h hc.mem₃ hA.le_iSub hN3).trans inf_le_left⟩

lemma seven_seven_c_fix_b_card_sup_A12 (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) = Nat.card ↥⁅A, V₁⁆ * Nat.card ↥⁅A, V₂⁆ := by
  obtain ⟨hA1le, hA2le, -⟩ := seven_seven_c_fix_b_commutator_le_A h hc hA
  exact card_sup_eq_mul_card_of_commute
    (fun p hp q hq =>
      seven_seven_c_fix_b_mul_comm_of_le_iSub h hA.le_iSub p (hA1le hp) q (hA2le hq))
    (commutator_inf_commutator_eq_bot h hc hA).1

lemma seven_seven_c_fix_b_card_A (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    Nat.card ↥A = Nat.card ↥⁅A, V₁⁆ * Nat.card ↥⁅A, V₂⁆ * Nat.card ↥⁅A, V₃⁆ := by
  obtain ⟨hA1le, hA2le, hA3le⟩ := seven_seven_c_fix_b_commutator_le_A h hc hA
  have hcommA := seven_seven_c_fix_b_mul_comm_of_le_iSub h hA.le_iSub
  have hsup : A = (⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) ⊔ ⁅A, V₃⁆ :=
    le_antisymm (le_sup_commutator h hc hA) (sup_le (sup_le hA1le hA2le) hA3le)
  have hS3 : Nat.card ↥((⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) ⊔ ⁅A, V₃⁆) =
      Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) * Nat.card ↥⁅A, V₃⁆ :=
    card_sup_eq_mul_card_of_commute
      (fun p hp q hq => hcommA p ((sup_le hA1le hA2le) hp) q (hA3le hq))
      (by rw [inf_comm]; exact (commutator_inf_commutator_eq_bot h hc hA).2)
  calc Nat.card ↥A = Nat.card ↥((⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) ⊔ ⁅A, V₃⁆) :=
        congrArg (fun X : Subgroup G => Nat.card ↥X) hsup
    _ = Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) * Nat.card ↥⁅A, V₃⁆ := hS3
    _ = (Nat.card ↥⁅A, V₁⁆ * Nat.card ↥⁅A, V₂⁆) * Nat.card ↥⁅A, V₃⁆ := by
        rw [seven_seven_c_fix_b_card_sup_A12 h hc hA]

lemma seven_seven_c_fix_b_B_le_sup_A12 (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) ≤
      ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := by
  calc A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)
      ≤ A ⊓ Subgroup.centralizer (V₁ : Set G) :=
        inf_le_inf le_rfl (Subgroup.centralizer_le (by
          intro x hx
          exact (le_sup_left : V₁ ≤ V₁ ⊔ V₂).trans
            (le_sup_left : V₁ ⊔ V₂ ≤ V₁ ⊔ V₂ ⊔ V₃) hx))
    _ = ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := (inf_centralizer_eq_sup_commutator h hc hA).1

lemma seven_seven_c_fix_b_inf_A1_eq_bot (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) ⊓ ⁅A, V₁⁆ = ⊥ := by
  refine le_bot_iff.mp (fun a ha => ?_)
  rw [Subgroup.mem_bot]
  by_contra ha1
  obtain ⟨g₁, hV1eq, -, -⟩ := mem_omegaSet.mp hc.mem₁
  have haA1 : a ∈ ⁅A, V₁⁆ := ha.2
  have haV1 : a ∈ V₁ := by
    rw [(commutator_eq_inf h hc hA).1] at haA1
    exact haA1.2
  have haC : a ∈ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) := ha.1.2
  obtain ⟨v₃, hv₃V3, hv₃I⟩ := seven_seven_c_fix_b_exists_mem_not_mem_iSub h hc.mem₃
  have hv₃X : v₃ ∈ V₁ ⊔ V₂ ⊔ V₃ := (le_sup_right : V₃ ≤ V₁ ⊔ V₂ ⊔ V₃) hv₃V3
  have hcomm : v₃ * a = a * v₃ := (Subgroup.mem_centralizer_iff.mp haC) v₃ hv₃X
  have hv₃C : v₃ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hcomm.symm)
  have hnorm : v₃ ∈ Subgroup.normalizer (conjSubgroup V g₁ : Set G) :=
    centralizer_le_normalizer_conj h.ti g₁ (hV1eq ▸ haV1) ha1 hv₃C
  rw [← hV1eq] at hnorm
  exact hv₃I (hc.norm₃₁ v₃ hv₃V3 hnorm)

lemma seven_seven_c_fix_b_inf_A2_eq_bot (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) ⊓ ⁅A, V₂⁆ = ⊥ := by
  refine le_bot_iff.mp (fun a ha => ?_)
  rw [Subgroup.mem_bot]
  by_contra ha1
  obtain ⟨g₂, hV2eq, -, -⟩ := mem_omegaSet.mp hc.mem₂
  have haA2 : a ∈ ⁅A, V₂⁆ := ha.2
  have haV2 : a ∈ V₂ := by
    rw [(commutator_eq_inf h hc hA).2.1] at haA2
    exact haA2.2
  have haC : a ∈ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) := ha.1.2
  obtain ⟨v₃, hv₃V3, hv₃I⟩ := seven_seven_c_fix_b_exists_mem_not_mem_iSub h hc.mem₃
  have hv₃X : v₃ ∈ V₁ ⊔ V₂ ⊔ V₃ := (le_sup_right : V₃ ≤ V₁ ⊔ V₂ ⊔ V₃) hv₃V3
  have hcomm : v₃ * a = a * v₃ := (Subgroup.mem_centralizer_iff.mp haC) v₃ hv₃X
  have hv₃C : v₃ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hcomm.symm)
  have hnorm : v₃ ∈ Subgroup.normalizer (conjSubgroup V g₂ : Set G) :=
    centralizer_le_normalizer_conj h.ti g₂ (hV2eq ▸ haV2) ha1 hv₃C
  rw [← hV2eq] at hnorm
  exact hv₃I (hc.norm₃₂ v₃ hv₃V3 hnorm)

lemma seven_seven_c_fix_b_inf_A3_eq_bot (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) ⊓ ⁅A, V₃⁆ = ⊥ := by
  have hBa := seven_seven_c_fix_b_B_le_sup_A12 h hc hA
  refine le_bot_iff.mp (fun a ha => ?_)
  have hmem : a ∈ (⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) ⊓ ⁅A, V₃⁆ := ⟨hBa ha.1, ha.2⟩
  rw [inf_comm, (commutator_inf_commutator_eq_bot h hc hA).2] at hmem
  exact hmem

lemma seven_seven_c_fix_b_B_eq_inf_centralizer_v3 (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) {v₃ : G}
    (hv₃V3 : v₃ ∈ V₃) (hv₃I : v₃ ∉ iSub V H E) :
    A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G) =
      (⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) ⊓ Subgroup.centralizer ({v₃} : Set G) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨seven_seven_c_fix_b_B_le_sup_A12 h hc hA hx,
      Subgroup.centralizer_le (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (le_sup_right : V₃ ≤ V₁ ⊔ V₂ ⊔ V₃) hv₃V3) hx.2⟩
  · intro x hx
    obtain ⟨hxP, hxCv3⟩ := hx
    obtain ⟨hA1le, hA2le, -⟩ := seven_seven_c_fix_b_commutator_le_A h hc hA
    have hxA : x ∈ A := (sup_le hA1le hA2le) hxP
    have hxCV1 : x ∈ Subgroup.centralizer (V₁ : Set G) := by
      have hx1 := hxP
      rw [← (inf_centralizer_eq_sup_commutator h hc hA).1] at hx1
      exact hx1.2
    have hxCV2 : x ∈ Subgroup.centralizer (V₂ : Set G) := by
      have hx2 := hxP
      rw [← (inf_centralizer_eq_sup_commutator h hc hA).2] at hx2
      exact hx2.2
    have hxCV3 : x ∈ Subgroup.centralizer (V₃ : Set G) := by
      have heq := inf_centralizer_singleton_eq_inf_centralizer h hc.mem₃ (hc.small V₃ hc.mem₃)
        hA.le_iSub hv₃V3 hv₃I
      have hx' : x ∈ A ⊓ Subgroup.centralizer ({v₃} : Set G) := ⟨hxA, hxCv3⟩
      rw [heq] at hx'
      exact hx'.2
    have hXle : (V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ((Subgroup.mem_centralizer_iff.mp hxCV1) y hy).symm)
      · intro y hy
        exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ((Subgroup.mem_centralizer_iff.mp hxCV2) y hy).symm)
      · intro y hy
        exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ((Subgroup.mem_centralizer_iff.mp hxCV3) y hy).symm)
    exact ⟨hxA, Subgroup.mem_centralizer_iff.mpr (fun y hy =>
      ((Subgroup.mem_centralizer_iff.mp (hXle hy)) x (Set.mem_singleton x)).symm)⟩

lemma seven_seven_c_fix_b_image_eq_A3 (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) {v₃ : G}
    (hv₃V3 : v₃ ∈ V₃) (hv₃I : v₃ ∉ iSub V H E) :
    {x : G | ∃ p ∈ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆, x = ⁅p, v₃⁆} =
      ((⁅A, V₃⁆ : Subgroup G) : Set G) := by
  have hV3Nle : V₃ ≤ Subgroup.normalizer (A : Set G) :=
    (le_sup_right : V₃ ≤ V₁ ⊔ V₂ ⊔ V₃).trans hA.normalizes
  have hV3N : v₃ ∈ Subgroup.normalizer (A : Set G) := hV3Nle hv₃V3
  have hcommA := seven_seven_c_fix_b_mul_comm_of_le_iSub h hA.le_iSub
  obtain ⟨hA1le, hA2le, hA3le⟩ := seven_seven_c_fix_b_commutator_le_A h hc hA
  have hPleA : ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ≤ A := sup_le hA1le hA2le
  ext x
  constructor
  · rintro ⟨p, hpP, rfl⟩
    exact Subgroup.commutator_mem_commutator (hPleA hpP) hv₃V3
  · intro hx
    have hx' : x ∈ {x : G | ∃ a ∈ A, x = ⁅a, v₃⁆} := by
      rw [← coe_commutator_eq_image h hc.mem₃ (hc.small V₃ hc.mem₃) hA.le_iSub hV3Nle hv₃V3
        hv₃I]
      exact hx
    obtain ⟨a, haA, hax⟩ := hx'
    obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, haeq⟩ :=
      exists_commutator_factorization h hc hA a haA
    refine ⟨a₁ * a₂, Subgroup.mul_mem_sup ha₁ ha₂, ?_⟩
    have ha₁A : a₁ ∈ A := hA1le ha₁
    have ha₂A : a₂ ∈ A := hA2le ha₂
    have ha₃A : a₃ ∈ A := hA3le ha₃
    have ha₃V3 : a₃ ∈ V₃ := by
      rw [(commutator_eq_inf h hc hA).2.2] at ha₃
      exact ha₃.2
    have h3 : ⁅a₃, v₃⁆ = 1 := by
      haveI : IsMulCommutative ↥V₃ := (isElemAbelian_of_mem_omegaSet h.elemAbelian hc.mem₃).1
      exact commutatorElement_eq_one_iff_commute.mpr
        (congrArg Subtype.val (mul_comm' (⟨a₃, ha₃V3⟩ : ↥V₃) ⟨v₃, hv₃V3⟩))
    rw [hax, haeq.symm,
      commutator_mul_of_mem_normalizer hcommA hV3N (mul_mem ha₁A ha₂A) ha₃A, h3, mul_one]

lemma seven_seven_c_fix_b_card_B (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) {v₃ : G}
    (hv₃V3 : v₃ ∈ V₃) (hv₃I : v₃ ∉ iSub V H E) :
    Nat.card ↥(A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) =
      Nat.card ↥⁅A, V₁⁆ := by
  have hcommA := seven_seven_c_fix_b_mul_comm_of_le_iSub h hA.le_iSub
  have hV3N : v₃ ∈ Subgroup.normalizer (A : Set G) :=
    hA.normalizes ((le_sup_right : V₃ ≤ V₁ ⊔ V₂ ⊔ V₃) hv₃V3)
  obtain ⟨hA1le, hA2le, -⟩ := seven_seven_c_fix_b_commutator_le_A h hc hA
  have hPleA : ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ≤ A := sup_le hA1le hA2le
  have hcardP := card_eq_card_inf_centralizer_mul_card_image (A := A)
    (P := ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) (v := v₃) hcommA hV3N hPleA
  have hBP := (seven_seven_c_fix_b_B_eq_inf_centralizer_v3 h hc hA hv₃V3 hv₃I).symm
  have himgcard : Nat.card ↥{x : G | ∃ p ∈ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆, x = ⁅p, v₃⁆} =
      Nat.card ↥⁅A, V₃⁆ :=
    congrArg (fun s : Set G => Nat.card ↥s)
      (seven_seven_c_fix_b_image_eq_A3 h hc hA hv₃V3 hv₃I)
  have hcardP' : Nat.card ↥(⁅A, V₁⁆ ⊔ ⁅A, V₂⁆) =
      Nat.card ↥(A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) *
        Nat.card ↥⁅A, V₃⁆ := by
    rw [hcardP, hBP, himgcard]
  have hkey : Nat.card ↥⁅A, V₁⁆ * Nat.card ↥⁅A, V₃⁆ =
      Nat.card ↥(A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) *
        Nat.card ↥⁅A, V₃⁆ := by
    rw [seven_seven_c_fix_b_card_sup_A12 h hc hA] at hcardP'
    rw [(card_commutator_eq_card_commutator_three h hc hA).2] at hcardP'
    exact hcardP'
  have hA3pos : 0 < Nat.card ↥⁅A, V₃⁆ := by
    refine Nat.card_pos_iff.mpr ⟨?_, inferInstance⟩
    exact ⟨1, Subgroup.one_mem _⟩
  exact (Nat.eq_of_mul_eq_mul_right hA3pos hkey).symm

lemma seven_seven_c_fix_b_sup_A1_B (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    ⁅A, V₁⁆ ⊔ (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) =
      ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := by
  have hBa := seven_seven_c_fix_b_B_le_sup_A12 h hc hA
  refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hBa) ?_
  have hcommA := seven_seven_c_fix_b_mul_comm_of_le_iSub h hA.le_iSub
  obtain ⟨hA1le, hA2le, -⟩ := seven_seven_c_fix_b_commutator_le_A h hc hA
  obtain ⟨v₃, hv₃V3, hv₃I⟩ := seven_seven_c_fix_b_exists_mem_not_mem_iSub h hc.mem₃
  have hbot : ⁅A, V₁⁆ ⊓
      (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) = ⊥ := by
    rw [inf_comm]
    exact seven_seven_c_fix_b_inf_A1_eq_bot h hc hA
  have hcard1 : Nat.card ↥(⁅A, V₁⁆ ⊔
      (A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G))) =
      Nat.card ↥⁅A, V₁⁆ *
        Nat.card ↥(A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) :=
    card_sup_eq_mul_card_of_commute
      (fun p hp q hq => hcommA p (hA1le hp) q hq.1) hbot
  have hBcard := seven_seven_c_fix_b_card_B h hc hA hv₃V3 hv₃I
  have h21 : Nat.card ↥⁅A, V₂⁆ = Nat.card ↥⁅A, V₁⁆ :=
    (card_commutator_eq_card_commutator_three h hc hA).2.trans
      (card_commutator_eq_card_commutator_three h hc hA).1.symm
  rw [seven_seven_c_fix_b_card_sup_A12 h hc hA, hcard1, hBcard, h21]

theorem card_eq_card_commutator_pow (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenModule V H E V₁ V₂ V₃ A) :
    Nat.card ↥A = Nat.card ↥⁅A, V₁⁆ ^ 3 := by
  have hcard := seven_seven_c_fix_b_card_A h hc hA
  have h31 := (card_commutator_eq_card_commutator_three h hc hA).1
  have h32 := (card_commutator_eq_card_commutator_three h hc hA).2
  have h21 : Nat.card ↥⁅A, V₂⁆ = Nat.card ↥⁅A, V₁⁆ := h32.trans h31.symm
  rw [hcard, h21, ← h31]
  ring

theorem inf_centralizer_properties (h : Hyp73 V H E J) (hc : SevenSevenCfg V H E V₁ V₂ V₃)
    (hA : SevenSevenModule V H E V₁ V₂ V₃ A)
    (hB : B = A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) :
    B ≤ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ∧ B ⊓ ⁅A, V₁⁆ = ⊥ ∧ B ⊓ ⁅A, V₂⁆ = ⊥ ∧ B ⊓ ⁅A, V₃⁆ = ⊥ ∧
      ⁅A, V₁⁆ ⊔ B = ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ ∧ Nat.card ↥B = Nat.card ↥⁅A, V₁⁆ := by
  subst hB
  obtain ⟨v₃, hv₃V3, hv₃I⟩ := seven_seven_c_fix_b_exists_mem_not_mem_iSub h hc.mem₃
  exact ⟨seven_seven_c_fix_b_B_le_sup_A12 h hc hA,
    seven_seven_c_fix_b_inf_A1_eq_bot h hc hA,
    seven_seven_c_fix_b_inf_A2_eq_bot h hc hA,
    seven_seven_c_fix_b_inf_A3_eq_bot h hc hA,
    seven_seven_c_fix_b_sup_A1_B h hc hA,
    seven_seven_c_fix_b_card_B h hc hA hv₃V3 hv₃I⟩

theorem mem_of_forall_commutator_mem_inf_centralizer (h : Hyp73 V H E J)
    (hc : SevenSevenCfg V H E V₁ V₂ V₃) (hA : SevenSevenModule V H E V₁ V₂ V₃ A)
    (hB : B = A ⊓ Subgroup.centralizer ((V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) : Set G)) :
    ∀ a ∈ A, (∀ x ∈ V₁ ⊔ V₂ ⊔ V₃, ⁅a, x⁆ ∈ B) → a ∈ B := by
  have hprops := inf_centralizer_properties h hc hA hB
  obtain ⟨-, hb1, hb2, hb3, -, -⟩ := hprops
  intro a ha hcomm
  obtain ⟨v₁, hv₁V1, hv₁I⟩ := seven_seven_c_fix_b_exists_mem_not_mem_iSub h hc.mem₁
  obtain ⟨v₃, hv₃V3, hv₃I⟩ := seven_seven_c_fix_b_exists_mem_not_mem_iSub h hc.mem₃
  obtain ⟨hN1, -, hN3⟩ := seven_seven_c_fix_b_normalizer_of_three hA
  have hv₁N : v₁ ∈ Subgroup.normalizer (A : Set G) := hN1 hv₁V1
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, haeq⟩ := exists_commutator_factorization h hc hA a ha
  obtain ⟨hA1le, hA2le, hA3le⟩ := seven_seven_c_fix_b_commutator_le_A h hc hA
  have hcommA := seven_seven_c_fix_b_mul_comm_of_le_iSub h hA.le_iSub
  have ha₁A : a₁ ∈ A := hA1le ha₁
  have ha₂A : a₂ ∈ A := hA2le ha₂
  have ha₃A : a₃ ∈ A := hA3le ha₃
  have ha₁V1 : a₁ ∈ V₁ := by
    rw [(commutator_eq_inf h hc hA).1] at ha₁
    exact ha₁.2
  have ha₂V2 : a₂ ∈ V₂ := by
    rw [(commutator_eq_inf h hc hA).2.1] at ha₂
    exact ha₂.2
  have h1 : ⁅a₁, v₁⁆ = 1 := by
    haveI : IsMulCommutative ↥V₁ := (isElemAbelian_of_mem_omegaSet h.elemAbelian hc.mem₁).1
    exact commutatorElement_eq_one_iff_commute.mpr
      (congrArg Subtype.val (mul_comm' (⟨a₁, ha₁V1⟩ : ↥V₁) ⟨v₁, hv₁V1⟩))
  have h2 : ⁅a₂, v₁⁆ = 1 := by
    have hv₁C : v₁ ∈ Subgroup.centralizer (V₂ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc.comm₁₂) hv₁V1
    exact commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_centralizer_iff.mp hv₁C) a₂ ha₂V2)
  have hcommut : ⁅a, v₁⁆ = ⁅a₃, v₁⁆ := by
    calc ⁅a, v₁⁆ = ⁅(a₁ * a₂) * a₃, v₁⁆ := by rw [← haeq]
      _ = ⁅a₁ * a₂, v₁⁆ * ⁅a₃, v₁⁆ :=
        commutator_mul_of_mem_normalizer hcommA hv₁N (mul_mem ha₁A ha₂A) ha₃A
      _ = (⁅a₁, v₁⁆ * ⁅a₂, v₁⁆) * ⁅a₃, v₁⁆ := by
        rw [commutator_mul_of_mem_normalizer hcommA hv₁N ha₁A ha₂A]
      _ = ⁅a₃, v₁⁆ := by rw [h1, h2, one_mul, one_mul]
  have hv₁X : v₁ ∈ V₁ ⊔ V₂ ⊔ V₃ := (le_sup_left : V₁ ≤ V₁ ⊔ V₂).trans
    (le_sup_left : V₁ ⊔ V₂ ≤ V₁ ⊔ V₂ ⊔ V₃) hv₁V1
  have hbot : ⁅a₃, v₁⁆ = 1 := by
    have hmem : ⁅a₃, v₁⁆ ∈ B ⊓ ⁅A, V₁⁆ :=
      ⟨hcommut ▸ hcomm v₁ hv₁X, Subgroup.commutator_mem_commutator ha₃A hv₁V1⟩
    rw [hb1] at hmem
    simpa using hmem
  have ha₃1 : a₃ = 1 :=
    (eq_one_of_mem_commutator_of_commute h hc hA).1 v₁ hv₁V1 hv₁I a₃ ha₃
      ((commute_iff_eq a₃ v₁).mp (commutatorElement_eq_one_iff_commute.mp hbot)).symm
  have ha_eq : a = a₁ * a₂ := by rw [← haeq, ha₃1, mul_one]
  have haP : a ∈ ⁅A, V₁⁆ ⊔ ⁅A, V₂⁆ := by
    rw [ha_eq]
    exact Subgroup.mul_mem_sup ha₁ ha₂
  have haCV3 : a ∈ Subgroup.centralizer (V₃ : Set G) := by
    have heq := inf_centralizer_singleton_eq_inf_centralizer h hc.mem₃ (hc.small V₃ hc.mem₃)
      hA.le_iSub hv₃V3 hv₃I
    have hmem : ⁅a, v₃⁆ ∈ B ⊓ ⁅A, V₃⁆ := by
      refine ⟨hcomm v₃ ((le_sup_right : V₃ ≤ V₁ ⊔ V₂ ⊔ V₃) hv₃V3), ?_⟩
      exact Subgroup.commutator_mem_commutator ha hv₃V3
    rw [hb3] at hmem
    have h1v : ⁅a, v₃⁆ = 1 := by simpa using hmem
    have haCv3 : a ∈ Subgroup.centralizer ({v₃} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact ((commute_iff_eq a v₃).mp (commutatorElement_eq_one_iff_commute.mp h1v)).symm)
    have hx' : a ∈ A ⊓ Subgroup.centralizer ({v₃} : Set G) := ⟨ha, haCv3⟩
    rw [heq] at hx'
    exact hx'.2
  have haCV1 : a ∈ Subgroup.centralizer (V₁ : Set G) := by
    have hx1 := haP
    rw [← (inf_centralizer_eq_sup_commutator h hc hA).1] at hx1
    exact hx1.2
  have haCV2 : a ∈ Subgroup.centralizer (V₂ : Set G) := by
    have hx2 := haP
    rw [← (inf_centralizer_eq_sup_commutator h hc hA).2] at hx2
    exact hx2.2
  have hXle : (V₁ ⊔ V₂ ⊔ V₃ : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((Subgroup.mem_centralizer_iff.mp haCV1) y hy).symm)
    · intro y hy
      exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((Subgroup.mem_centralizer_iff.mp haCV2) y hy).symm)
    · intro y hy
      exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((Subgroup.mem_centralizer_iff.mp haCV3) y hy).symm)
  rw [hB]
  exact ⟨ha, Subgroup.mem_centralizer_iff.mpr (fun y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hXle hy)) a (Set.mem_singleton a)).symm)⟩

end FixB

end CFSG.LocalAnalysis.WeakClosure81
