module

public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec17.Item171ProofKFact
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

namespace Proof1712

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ_of_commutator_eq_bot {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hMV : Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hVc : ⁅V, Subgroup.zpowers c⁆ = ⊥) : V ∈ scriptQ A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcopV : ∀ {N : Subgroup G}, N ≤ V → Nat.Coprime 3 (Nat.card N) := by
    intro N hNV
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hV2.to_le hNV)
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hV3 : ¬ 3 ∣ Nat.card V := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hcopV le_rfl)
  have hVC : V ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hVc
  have hAM : A ≤ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer.trans h.normalizer_le
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three V).mpr hV3,
    hAM.trans hMV, fun B hB => ?_⟩
  by_cases hcB : c ∈ B
  ·
    have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (V : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB)).trans
        ((centralizer_c_le_M h).trans hMV)
    have hle : V ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf hCB Subgroup.le_normalizer)
        (hcopV inf_le_left)
    exact hle.trans (le_sup_left.trans le_sup_left)
  ·
    have hB9 : Nat.card B = 9 := by
      have := hB.2
      rw [hA.2] at this
      omega
    obtain ⟨-, h27⟩ := isElemAbelian_zpowers_sup_of_card_nine (hA.1.2 c hcA) hcB le_rfl hB9
      (fun s hs => hA.1.2 s (hB.1 hs)) (fun y hy => h.toSec13Data.commute hcA (hB.1 hy))
    have hAeq : Subgroup.zpowers c ⊔ B = A :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcA) hB.1)
        (by rw [h27, hA.2])
    have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) :=
      (centralizer_le_M h).trans hMV
    have hVBA : V ⊓ Subgroup.centralizer (B : Set G) ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
      intro v hv
      refine ⟨hv.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have hAv : A ≤ Subgroup.centralizer ({v} : Set G) := by
        rw [← hAeq]
        refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr ?_)) ?_
        · exact Subgroup.mem_centralizer_iff.mp (hVC hv.1) c (Subgroup.mem_zpowers c)
        · intro b hb
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hv.2 b hb)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hAv ha)
    have hle : V ⊓ Subgroup.centralizer (A : Set G) ≤ xA A :=
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf hCA Subgroup.le_normalizer)
        (hcopV inf_le_left)
    exact hVBA.trans (hle.trans (le_sup_right.trans le_sup_left))

theorem eq_of_normal_of_mem {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) (hcL : c ∉ L)
    {N : Subgroup G} (hNL : N ≤ L) (hLN : L ≤ Subgroup.normalizer (N : Set G)) {f : G}
    (hfA : f ∈ A) (hfN : f ∈ N) (hf1 : f ≠ 1) : N = L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set N₀ : Subgroup ↥L := N.subgroupOf L with hN₀
  have hN₀n : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hLp := Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  refine le_antisymm hNL ?_
  rcases Proof171.normal_le_center_or_eq_top hq
      (hN₀n.map (QuotientGroup.mk' θ) (QuotientGroup.mk'_surjective θ)) with hZ | htop
  ·
    exfalso
    set f' : ↥L := ⟨f, hNL hfN⟩ with hf'
    have hf'Z : QuotientGroup.mk' θ f' ∈ Subgroup.center (↥L ⧸ θ) :=
      hZ ⟨f', Subgroup.mem_subgroupOf.mpr hfN, rfl⟩
    have hfsc : f ∈ Late.sectionCentralizer A L (θ.map L.subtype) := by
      refine ⟨hfA, fun x hx => ?_⟩
      have hcomm : QuotientGroup.mk' θ (f' * ⟨x, hx⟩ * f'⁻¹ * (⟨x, hx⟩ : ↥L)⁻¹) = 1 := by
        have hfx := Subgroup.mem_center_iff.mp hf'Z (QuotientGroup.mk' θ ⟨x, hx⟩)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hfx]
        group
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcomm
      exact ⟨_, hcomm, rfl⟩
    rw [hD.sectionCentralizer_eq] at hfsc
    have hfc : Subgroup.zpowers f ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hfsc
    have hdvd : Nat.card (Subgroup.zpowers f) ∣ 3 := by
      rw [← hD.card_zpowers]
      exact Subgroup.card_dvd_of_le hfc
    have hne1 : Nat.card (Subgroup.zpowers f) ≠ 1 := by
      rw [Nat.card_zpowers]
      exact fun h1 => hf1 (orderOf_eq_one_iff.mp h1)
    have h3 : Nat.card (Subgroup.zpowers f) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have heq : Subgroup.zpowers f = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge hfc (by rw [h3, hD.card_zpowers])
    exact hcL (Subgroup.zpowers_le.mpr (hNL hfN) (heq ▸ Subgroup.mem_zpowers c))
  ·
    have hsup : N₀ ⊔ θ = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N₀
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hsurj : Function.Surjective ((QuotientGroup.mk' N₀).comp θ.subtype) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₀ q
      have hx : x ∈ N₀ ⊔ θ := hsup ▸ Subgroup.mem_top x
      rw [Subgroup.mem_sup_of_normal_left] at hx
      obtain ⟨n, hn, t, ht, rfl⟩ := hx
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have : Group.IsSolvable θ :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
    have hsolv : Group.IsSolvable (↥L ⧸ N₀) := Group.isSolvable_of_surjective hsurj
    have hperf : Group.IsPerfect (↥L ⧸ N₀) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N₀) (QuotientGroup.mk'_surjective N₀)
    have hNtop : N₀ = ⊤ := by
      by_contra hne
      have : Nontrivial (↥L ⧸ N₀) := QuotientGroup.nontrivial_iff.mpr hne
      exact Group.IsPerfect.not_isSolvable (↥L ⧸ N₀) hsolv
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥L) ∈ N₀ := hNtop ▸ Subgroup.mem_top _
    exact hmem

theorem zpowers_sup_inf_eq {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hcL : c ∉ L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Subgroup.zpowers c ⊔ (A ⊓ L) = A := by
  have hA : IsE27 A := isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hcard := (isElemAbelian_zpowers_sup_of_card_nine (pow_three_of_std h hcA)
    (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl h9
    (fun b hb => hA.1.2 b hb.1) (fun b hb => h.toSec13Data.commute hcA hb.1)).2
  exact Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left)
    (by rw [hA.2, hcard])

theorem le_of_le_sup_pCoreOf {Y₀ N : Subgroup G} (hY : Y₀ = oPrimeResidualOf 3 Y₀)
    (hYN : Y₀ ≤ Subgroup.normalizer (N : Set G)) (hsup : Y₀ ≤ N ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    Y₀ ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : CFSG.Open.pCoreOf 2 Y₀ ≤ Subgroup.normalizer (N : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans hYN
  calc Y₀ = oPrimeResidualOf 3 Y₀ := hY
    _ ≤ N := by
      rw [Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
      rintro y ⟨hyY, a, hya⟩
      have hy : y ∈ ((N ⊔ CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) := hsup hyY
      rw [Subgroup.coe_mul_of_right_le_normalizer_left N _ hKN] at hy
      obtain ⟨n, hn, k, hk, rfl⟩ := hy
      obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀ ⟨k, hk⟩
      have hb' : k ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      exact mul_mem hn (Proof171.mem_of_mul_pow_eq_one hn (hKN hk)
        (Nat.Coprime.pow a b (by norm_num)) hya hb')

end Proof1712

@[expose] noncomputable def Step1712LV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ = ⊥ → ⁅V, L⁆ ≠ ⊥

section LV

theorem step1712LV_of (h310 : Sec6.Item3_10) (h9 : CardInfNineS17) : Step1712LV := by
  intro G _ _ A c L Y₀ h V hV hVc hVL
  have hD := h.toSec13Data
  have h9' := h9 G A c L Y₀ h
  obtain ⟨-, hMV, -⟩ := hV.prop
  have hLC : L ≤ Subgroup.centralizer (V : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hVL
  have hLY : L ≤ Y₀ := h.le_y0
  set N := Y₀ ⊓ Subgroup.centralizer (V : Set G) with hN
  have hYV : Y₀ ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
  have hYC : Y₀ ≤ Subgroup.normalizer
      ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun y hy =>
    Sec14.mem_normalizer_of_map_conj_eq (by
      rw [map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer (hYV hy)])
  have hYN : Y₀ ≤ Subgroup.normalizer (N : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer hYC
  have hY4 := h.mem_y0Star.prop.1
  have hsup : Y₀ ≤ N ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have hq : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := hY4.2.2.2
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀) with hπ
    set N₀ : Subgroup ↥Y₀ := N.subgroupOf Y₀ with hN₀
    have hN₀n : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hYN
    rcases Proof171.normal_le_center_or_eq_top hq
        (hN₀n.map π (QuotientGroup.mk'_surjective _)) with hZ | htop
    ·
      exfalso
      set ψ : ↥L →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ := π.comp (Subgroup.inclusion hLY) with hψ
      have hψZ : ∀ x : ↥L, ψ x ∈ Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := fun x =>
        hZ ⟨Subgroup.inclusion hLY x, Subgroup.mem_subgroupOf.mpr ⟨hLY x.2, hLC x.2⟩, rfl⟩
      have hLp : Group.IsPerfect ↥L :=
        Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
      have hker : ψ.ker = ⊤ := by
        rw [eq_top_iff, ← hLp.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
        intro g₁ _ g₂ _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp (hψZ g₁) (ψ g₂)).symm
      have hne : A ⊓ L ≠ ⊥ := fun hb => by
        rw [hb, Subgroup.card_bot] at h9'
        omega
      obtain ⟨⟨f, hfAL⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hf1' : f ≠ 1 := fun h1 => hf1 (Subtype.ext h1)
      have hfK : f ∈ CFSG.Open.pCoreOf 2 Y₀ := by
        have h1 : ψ ⟨f, hfAL.2⟩ = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top _)
        have h2 : Subgroup.inclusion hLY ⟨f, hfAL.2⟩ ∈ CFSG.pCore 2 ↥Y₀ := by
          rw [← QuotientGroup.eq_one_iff]
          exact h1
        exact (Step163Alt.mem_pCore_two_iff _).mp h2
      obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀ ⟨f, hfK⟩
      have hb' : f ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      exact hf1' (Step163Alt.eq_one_of_two_three (n := 1) hb'
        (by rw [pow_one]; exact pow_three_of_std h hfAL.1))
    · intro y hy
      have hmem : π ⟨y, hy⟩ ∈ N₀.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp hmem
      have hk : n⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥Y₀ := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hny
        exact hny
      have e : y = (n : G) * ((n⁻¹ * ⟨y, hy⟩ : ↥Y₀) : G) := by simp
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hn)
        ((Step163Alt.mem_pCore_two_iff _).mp hk)
  have hYle : Y₀ ≤ N := Proof1712.le_of_le_sup_pCoreOf hY4.2.1 hYN hsup
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer (V : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hVc
  refine rank3II_17_7_one_of h h310 hV (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    (sup_le (hYle.trans inf_le_right) ?_))
  rw [← Proof1712.zpowers_sup_inf_eq h hcL h9']
  exact sup_le hcC (inf_le_right.trans hLC)

end LV

@[expose] noncomputable def Step1712Faith : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ = ⊥ → ∀ a ∈ A, a ∉ Subgroup.zpowers c →
        ⁅V, Subgroup.zpowers a⁆ ≠ ⊥

section Faith

theorem step1712Faith_of (hLV : Step1712LV) (h9 : CardInfNineS17) : Step1712Faith := by
  intro G _ _ A c L Y₀ h V hV hVc a ha hac hVa
  have hD := h.toSec13Data
  have hA : IsE27 A := isE27_of_std h
  have hcA : c ∈ A := hD.mem_A
  obtain ⟨-, hMV, -⟩ := hV.prop
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hcard := (isElemAbelian_zpowers_sup_of_card_nine (pow_three_of_std h hcA)
    (fun hcB => hcL (Subgroup.mem_inf.mp hcB).2) le_rfl (h9 G A c L Y₀ h)
    (fun b hb => hA.1.2 b hb.1) (fun b hb => hD.commute hcA hb.1)).2
  have hAeq : Subgroup.zpowers c ⊔ (A ⊓ L) = A :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left)
      (by rw [hA.2, hcard])
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => hD.commute hb.1 hcA))
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer (V : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hVc
  have haC : a ∈ Subgroup.centralizer (V : Set G) := by
    have : Subgroup.zpowers a ≤ Subgroup.centralizer (V : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hVa
    exact this (Subgroup.mem_zpowers a)
  have ha' : a ∈ ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) := by
    rw [hAeq]
    exact ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at ha'
  obtain ⟨x, hx, f, hf, rfl⟩ := ha'
  have hfC : f ∈ Subgroup.centralizer (V : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hcC hx)) haC
    rwa [inv_mul_cancel_left] at this
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact hac (by simpa using hx)
  have hLV' : L ≤ Subgroup.normalizer (V : Set G) :=
    (h.le_y0.trans Subgroup.le_normalizer).trans hMV
  have hLC : L ≤ Subgroup.normalizer
      ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun l hl =>
    Sec14.mem_normalizer_of_map_conj_eq (by
      rw [map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer (hLV' hl)])
  have hN := Proof1712.eq_of_normal_of_mem hD hcL (N := L ⊓ Subgroup.centralizer (V : Set G))
    inf_le_left (Late.le_normalizer_inf Subgroup.le_normalizer hLC) hf.1 ⟨hf.2, hfC⟩ hf1
  apply hLV G A c L Y₀ h V hV hVc
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, ← hN]
  exact inf_le_right

theorem step1712Faith_of_items (h310 : Sec6.Item3_10) (h9 : CardInfNineS17) : Step1712Faith :=
  step1712Faith_of (step1712LV_of h310 h9) h9

end Faith

@[expose] noncomputable def Step1712Delta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ = ⊥ →
        (∃ R ∈ fourGroups A, R = ⁅R, Subgroup.zpowers c⁆ ∧ R ∈ scriptQ A (lB A) ∧
          R ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) ∨
        ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧
          CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) ≠ ⊥

theorem step1712Main_of (hF : Step1712Faith) (hD : Step1712Delta) : Step1712Main := by
  intro G _ _ A c L Y₀ h V hV hVc
  rcases hD G A c L Y₀ h V hV hVc with hR | ⟨a, ha, hac, hO2⟩
  · exact Or.inl hR
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ Subgroup.one_mem _)
  have hΔ3 : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∈ scriptY3 A (lB A) := by
    refine ⟨⟨⟨fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp ha1
      (top_le_iff.mp (htop ▸ delta_le _)), le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩, hO2⟩,
      (delta_delta _).symm⟩
  refine Or.inr ⟨a, ha, ha1, hΔ3, ?_⟩
  obtain ⟨-, hMV, hVab⟩ := hV.prop
  have hA : IsE27 A := isE27_of_std h
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.le_normalizer.trans h.normalizer_le).trans hMV
  have hVQ := Proof1712.mem_scriptQ_of_commutator_eq_bot h (Sec5.isPGroup_of_isElemAbelian hVab)
    hMV hVc
  have hAa : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := fun b hb =>
    centralizer_singleton_le_normalizer_zpowers a (Subgroup.mem_centralizer_singleton_iff.mpr
      (h.toSec13Data.commute hb ha))
  have hVaV : ⁅V, Subgroup.zpowers a⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hAV ha))
  obtain ⟨U, hU, hUW, hUa⟩ := Proof1712.exists_fourGroupsMinus_le_of_le_commutator hA ha hVab
    hAV (le_normalizer_commutator hAV hAa) le_rfl (hF G A c L Y₀ h V hV hVc a ha hac)
  exact ⟨U, hU.1, hUa, mem_scriptQ_of_le hVQ (hUW.trans hVaV) hU.1.1.2.2, hUW.trans hVaV⟩

theorem step1712Main_of_items
    (h310 : Sec6.Item3_10) (h9 : CardInfNineS17)
    (hD : Step1712Delta) : Step1712Main :=
  step1712Main_of (step1712Faith_of_items h310 h9) hD

end CFSG.RankThree.PartTwo.Sec17
