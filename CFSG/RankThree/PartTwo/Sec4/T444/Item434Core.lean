module

public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
import CFSG.RankThree.PartTwo.Sec4.Steps434
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

namespace Ctx434Core

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem rank3II_4_35 (h : Ctx434Core G A M Q) {x : G} (hx : x ∈ Subgroup.centralizer (A : Set G))
    (hx3 : x ^ 3 = 1) : x ∈ A :=
  mem_of_mem_centralizer_of_gamma_le h.isE27 h.gamma_le h.pRank_eq hx hx3

theorem rank3II_4_36 (h : Ctx434Core G A M Q) :
    inSubgroup generalizedFitting (Subgroup.centralizer (layer G : Set G)) = CFSG.pCore 3 G :=
  generalizedFitting_centralizer_layer h.theta_eq_bot

theorem rank3II_4_37 (h : Ctx434Core G A M Q) {H : Subgroup G} (hAH : A ≤ H)
    (hH : CFSG.HallHigman.IsPSolvable 3 H) :
    maxInvariantPiSubgroups H A (piCompl 3) = {inSubgroup (CFSG.pPrimeCore 3) H} :=
  maxInvariantPiSubgroups_eq_pPrimeCore hAH hH h.isE27.1 fun _ hx hx3 => h.rank3II_4_35 hx hx3

theorem card_inf_centralizer_layer_le (h : Ctx434Core G A M Q) :
    Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := A ⊓ Subgroup.centralizer (layer G : Set G) with hD
  obtain ⟨k, hk⟩ := (h.isE27.isPGroup.to_le (inf_le_left : D ≤ A)).exists_card_eq
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    interval_cases k <;> simp_all
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := D) (n := 2)
    (by rw [hk]; exact pow_dvd_pow 3 hk2)
  set B := K.map D.subtype with hB
  have hBD : B ≤ D := Subgroup.map_subtype_le K
  have hB9 : Nat.card B = 3 ^ 2 := by
    rw [hB, Subgroup.card_map_of_injective D.subtype_injective, hK]
  have hBA : B ≤ A := hBD.trans inf_le_left
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Source.isElemAbelian_of_le h.isE27.1 hBA
  have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
      ⟨B, le_rfl, hBe, hB9⟩
  apply h.not_le
  have hLB : layer G ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mp (hBD.trans inf_le_right)
  exact hLB.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((normalizer_le_gamma hBA hB2).trans h.gamma_le))

theorem rank3II_4_38 (h : Ctx434Core G A M Q) :
    (CFSG.pCore 3 G = ⊥ ∧ generalizedFitting G = layer G ∧ IsSimpleGroup (layer G)) ∨
      (A ⊓ CFSG.pCore 3 G = A ⊓ Subgroup.centralizer (layer G : Set G) ∧
        Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hO : CFSG.pCore 3 G = ⊥
  · left
    refine ⟨hO, ?_, isSimpleGroup_layer h.theta_eq_bot hO h.isQuasisimple⟩
    rw [generalizedFitting, fittingSubgroup_eq_bot h.theta_eq_bot hO, bot_sup_eq]
  · right
    have : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal
    have hne := inf_ne_bot_of_gamma_le h.isE27 h.gamma_le h.pRank_eq
      (CFSG.pCore_isPGroup (p := 3) (G := G)) hO
    have hle : A ⊓ CFSG.pCore 3 G ≤ A ⊓ Subgroup.centralizer (layer G : Set G) :=
      inf_le_inf_left _ pCore_three_le_centralizer_layer
    have hcard := h.card_inf_centralizer_layer_le
    have h3 : 3 ≤ Nat.card (A ⊓ CFSG.pCore 3 G : Subgroup G) := by
      rcases ((CFSG.pCore_isPGroup (p := 3) (G := G)).to_le (inf_le_right :
          A ⊓ CFSG.pCore 3 G ≤ CFSG.pCore 3 G)).card_eq_or_dvd with hc | hc
      · exact absurd (Subgroup.card_eq_one.mp hc) hne
      · exact Nat.le_of_dvd Nat.card_pos hc
    have heq : A ⊓ CFSG.pCore 3 G = A ⊓ Subgroup.centralizer (layer G : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (hcard.trans h3)
    exact ⟨heq, le_antisymm hcard (heq ▸ h3)⟩

theorem three_dvd_card_layer (h : Ctx434Core G A M Q) : 3 ∣ Nat.card (layer G) := by
  by_contra h3
  apply h.not_le
  have : (layer G).Characteristic := layer_characteristic
  have hAL : A ≤ Subgroup.normalizer (layer G : Set G) := by
    rw [Subgroup.normalizer_eq_top (layer G)]
    exact le_top
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three h.isE27.1
    (by rw [h.isE27.2]; norm_num) hAL ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    fun H hHA hH9 => ?_
  have hHe := Source.isElemAbelian_of_le h.isE27.1 hHA
  have hH2 : 2 ≤ CFSG.Open.pRank 3 H :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three H)
      ⟨H, le_rfl, hHe, hH9⟩
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((normalizer_le_gamma hHA hH2).trans h.gamma_le))

theorem center_layer_eq_bot (h : Ctx434Core G A M Q)
    (hZL : ¬ A ⊓ Subgroup.centralizer (layer G : Set G) ≤
      (Subgroup.center (layer G)).map (layer G).subtype) :
    (Subgroup.center (layer G)).map (layer G).subtype = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (layer G).Characteristic := layer_characteristic
  have hnorm : ((Subgroup.center (layer G)).map (layer G).subtype).Normal := inferInstance
  have hcomm : IsMulCommutative ((Subgroup.center (layer G)).map (layer G).subtype) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    change (a : G) * b = b * a
    rw [← ha, ← hb]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' b').symm
  have hF : (Subgroup.center (layer G)).map (layer G).subtype ≤ fittingSubgroup G :=
    le_sSup ⟨hnorm, inferInstance⟩
  have hZp : IsPGroup 3 ((Subgroup.center (layer G)).map (layer G).subtype) :=
    (CFSG.pCore_isPGroup (p := 3) (G := G)).to_le
      (hF.trans (fittingSubgroup_le_pCore_three h.theta_eq_bot))
  by_contra hne
  have hAZ := inf_ne_bot_of_gamma_le h.isE27 h.gamma_le h.pRank_eq hZp hne
  apply hZL
  have hZcC : (Subgroup.center (layer G)).map (layer G).subtype ≤
      Subgroup.centralizer (layer G : Set G) := by
    rw [← CFSG.GroupTheory.inf_centralizer_eq_map_center]
    exact inf_le_right
  have hle : A ⊓ (Subgroup.center (layer G)).map (layer G).subtype ≤
      A ⊓ Subgroup.centralizer (layer G : Set G) := inf_le_inf_left _ hZcC
  have hcard := h.card_inf_centralizer_layer_le
  have h3 : 3 ≤ Nat.card (A ⊓ (Subgroup.center (layer G)).map (layer G).subtype : Subgroup G) := by
    rcases (hZp.to_le (inf_le_right : A ⊓ (Subgroup.center (layer G)).map (layer G).subtype ≤
        (Subgroup.center (layer G)).map (layer G).subtype)).card_eq_or_dvd with hc | hc
    · exact absurd (Subgroup.card_eq_one.mp hc) hAZ
    · exact Nat.le_of_dvd Nat.card_pos hc
  have heq := Subgroup.eq_of_le_of_card_ge hle (hcard.trans h3)
  rw [← heq]
  exact inf_le_right

theorem rank3II_4_39 (h : Ctx434Core G A M Q)
    (hZ1 : A ⊓ Subgroup.centralizer (layer G : Set G) ≠ ⊥)
    (hZL : ¬ A ⊓ Subgroup.centralizer (layer G : Set G) ≤
      (Subgroup.center (layer G)).map (layer G).subtype) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3 ∧
      ((A ⊔ layer G = (A ⊓ Subgroup.centralizer (layer G : Set G)) ⊔ layer G ∧
          A ⊓ Subgroup.centralizer (layer G : Set G) ⊓ layer G = ⊥) ∨
        ∃ a ∈ A, InducesOuter a (layer G) ∧
          CFSG.Open.pRank 3 (layer G ⊓ Subgroup.centralizer {a}) = 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (layer G).Characteristic := layer_characteristic
  have hA35 : ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A :=
    fun x hx hx3 => h.rank3II_4_35 hx hx3
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLC : layer G ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center, h.center_layer_eq_bot hZL]
  have hZO : A ⊓ CFSG.pCore 3 G = A ⊓ Subgroup.centralizer (layer G : Set G) := by
    rcases h.rank3II_4_38 with ⟨-, hF, -⟩ | h2
    · exfalso
      apply hZ1
      have hCL : Subgroup.centralizer (layer G : Set G) ≤ layer G := by
        have h' := CFSG.centralizer_generalizedFitting_le G
        rwa [hF] at h'
      have hC : Subgroup.centralizer (layer G : Set G) = ⊥ := by
        rw [eq_bot_iff, ← hLC]
        exact le_inf hCL le_rfl
      rw [hC, inf_bot_eq]
    · exact h2.1
  obtain ⟨P, hAP⟩ := h.isE27.isPGroup.exists_le_sylow
  have hPp : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hCPA : Subgroup.centralizer ((P : Subgroup G) : Set G) ≤
      Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAP)
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer ((layer G ⊓ (P : Subgroup G) :
      Subgroup G) : Set G) := by
    refine (le_inf ?_ Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
    rw [Subgroup.normalizer_eq_top (layer G)]
    exact le_top
  have hO1 : CFSG.pCore 3 G ≠ ⊥ := by
    intro hO
    apply hZ1
    rw [← hZO, hO, inf_bot_eq]
  obtain ⟨z, hzO, hzP, hz3, hz1⟩ := exists_mem_centralizer_pow_three hPp
    (CFSG.pCore_isPGroup (p := 3) (G := G))
    (by rw [Subgroup.normalizer_eq_top (CFSG.pCore 3 G)]; exact le_top) hO1
  have hzA : z ∈ A := hA35 z (hCPA hzP) hz3
  have hzC : z ∈ Subgroup.centralizer (layer G : Set G) := by
    have hz : z ∈ A ⊓ CFSG.pCore 3 G := ⟨hzA, hzO⟩
    rw [hZO] at hz
    exact hz.2
  have hLP1 : layer G ⊓ (P : Subgroup G) ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := layer G) 3 h.three_dvd_card_layer
    have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have hxp : IsPGroup 3 (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxG, pow_one])
    obtain ⟨R, hR⟩ := hxp.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P R
    have hx' : (x : G) ∈ ((g • P : Sylow 3 G) : Set G) := hR (Subgroup.mem_zpowers _)
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem] at hx'
    simp only [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply] at hx'
    have hxP : g⁻¹ * x * g ∈ (P : Subgroup G) := hx'
    have hxL : g⁻¹ * x * g ∈ layer G := by
      have := (inferInstance : (layer G).Normal).conj_mem _ x.2 g⁻¹
      rwa [inv_inv] at this
    intro hbot
    have hmem : g⁻¹ * x * g ∈ layer G ⊓ (P : Subgroup G) := ⟨hxL, hxP⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hx1 : (x : G) = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) hmem
      simpa [mul_assoc] using this
    rw [hx1, orderOf_one] at hxG
    omega
  obtain ⟨u, huLP, huP, hu3, hu1⟩ :=
    exists_mem_centralizer_pow_three hPp (hPp.to_le inf_le_right) hPN hLP1
  have huA : u ∈ A := hA35 u (hCPA huP) hu3
  have huL : u ∈ layer G := huLP.1
  have hu_notin : u ∉ Subgroup.zpowers z := by
    intro hu
    have hmem : u ∈ layer G ⊓ Subgroup.centralizer (layer G : Set G) :=
      ⟨huL, Subgroup.zpowers_le.mpr hzC hu⟩
    rw [hLC] at hmem
    exact hu1 hmem
  have hzE : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers z) :=
    Source.isElemAbelian_of_le h.isE27.1 (Subgroup.zpowers_le.mpr hzA)
  obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hzE hu_notin hu3
    fun b hb => hAc _ (Subgroup.zpowers_le.mpr hzA hb) _ huA
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz3 hz1
  have hBA : Subgroup.zpowers z ⊔ Subgroup.zpowers u ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hzA) (Subgroup.zpowers_le.mpr huA)
  have hB2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers z ⊔ Subgroup.zpowers u) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨_, le_rfl, hBe, by rw [hBcard, hzcard]; norm_num⟩
  have hPM : (P : Subgroup G) ≤ M := by
    have hBP : Subgroup.zpowers z ⊔ Subgroup.zpowers u ≤
        Subgroup.centralizer ((P : Subgroup G) : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr hzP) (Subgroup.zpowers_le.mpr huP)
    exact (Subgroup.le_centralizer_iff.mp hBP).trans ((Subgroup.centralizer_le_normalizer _).trans
      ((normalizer_le_gamma hBA hB2).trans h.gamma_le))
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3 := by
    apply le_antisymm
    · exact (pRank_top_le_of_sylow_le hPM).trans h.pRank_eq.le
    · calc 3 = CFSG.Open.pRank 3 A := h.isE27.pRank_eq.symm
        _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three le_top
  refine ⟨hrank, ?_⟩
  by_cases hall : ∀ a ∈ A, ¬ InducesOuter a (layer G)
  ·
    left
    have hdec : ∀ a ∈ A, ∃ l ∈ layer G, ∃ c ∈ Subgroup.centralizer (layer G : Set G),
        a = l * c := fun a ha => by
      obtain ⟨l, hl, hc⟩ := exists_mem_centralizer_of_not_inducesOuter (hall a ha)
      exact ⟨l, hl, l⁻¹ * a, hc, by group⟩
    refine ⟨le_antisymm (sup_le ?_ le_sup_right) (sup_le_sup_right inf_le_left _), ?_⟩
    · intro a ha
      obtain ⟨l, hl, c, hc, rfl⟩ := hdec a ha
      have hcA : c ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a' ha'
        obtain ⟨l', hl', c', hc', rfl⟩ := hdec a' ha'
        have hcl' : l' * c = c * l' := Subgroup.mem_centralizer_iff.mp hc l' hl'
        have hc'l : l * c' = c' * l := Subgroup.mem_centralizer_iff.mp hc' l hl
        have haa := hAc _ ha _ ha'
        have hw : (l' * l)⁻¹ * (l * l') = c' * c * (c * c')⁻¹ := by
          have e1 : l * c * (l' * c') = l * l' * (c * c') := by
            calc l * c * (l' * c') = l * (c * l') * c' := by group
              _ = l * (l' * c) * c' := by rw [hcl']
              _ = l * l' * (c * c') := by group
          have e2 : l' * c' * (l * c) = l' * l * (c' * c) := by
            calc l' * c' * (l * c) = l' * (c' * l) * c := by group
              _ = l' * (l * c') * c := by rw [hc'l]
              _ = l' * l * (c' * c) := by group
          rw [e1, e2] at haa
          calc (l' * l)⁻¹ * (l * l') = (l' * l)⁻¹ * (l * l' * (c * c')) * (c * c')⁻¹ := by group
            _ = (l' * l)⁻¹ * (l' * l * (c' * c)) * (c * c')⁻¹ := by rw [haa]
            _ = c' * c * (c * c')⁻¹ := by group
        have hwmem : (l' * l)⁻¹ * (l * l') ∈
            layer G ⊓ Subgroup.centralizer (layer G : Set G) := by
          refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (mul_mem hl' hl)) (mul_mem hl hl'), ?_⟩
          rw [hw]
          exact mul_mem (mul_mem hc' hc) (inv_mem (mul_mem hc hc'))
        rw [hLC, Subgroup.mem_bot, hw, mul_inv_eq_one] at hwmem
        calc l' * c' * c = l' * (c' * c) := by group
          _ = l' * (c * c') := by rw [hwmem]
          _ = c * (l' * c') := by rw [← mul_assoc, hcl', mul_assoc]
      have hc3 : c ^ 3 = 1 := by
        have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
        have h3 := h.isE27.1.2 _ ha
        rw [(Commute.mul_pow hlc 3)] at h3
        have hmem : l ^ 3 ∈ layer G ⊓ Subgroup.centralizer (layer G : Set G) := by
          refine Subgroup.mem_inf.mpr ⟨pow_mem hl 3, ?_⟩
          rw [eq_inv_of_mul_eq_one_left h3]
          exact inv_mem (pow_mem hc 3)
        rw [hLC, Subgroup.mem_bot] at hmem
        rw [hmem, one_mul] at h3
        exact h3
      have hcZ : c ∈ A ⊓ Subgroup.centralizer (layer G : Set G) := ⟨hA35 c hcA hc3, hc⟩
      exact mul_mem (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left hcZ)
    · rw [eq_bot_iff, ← hLC]
      exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  ·
    right
    push Not at hall
    obtain ⟨a, ha, hout⟩ := hall
    have ha3 : a ^ 3 = 1 := h.isE27.1.2 a ha
    refine ⟨a, ha, hout, le_antisymm ?_ ?_⟩
    ·
      by_contra hgt
      push Not at hgt
      obtain ⟨E, hEle, hEe, hEcard⟩ :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three
          (layer G ⊓ Subgroup.centralizer {a})
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := E) (n := 2)
        (by rw [hEcard]; exact pow_dvd_pow 3 hgt)
      set E₂ := K.map E.subtype with hE₂
      have hE₂E : E₂ ≤ E := Subgroup.map_subtype_le K
      have hE₂card : Nat.card E₂ = 9 := by
        rw [hE₂, Subgroup.card_map_of_injective E.subtype_injective, hK]
        norm_num
      have hE₂e : CFSG.Assembly.IsElemAbelian 3 E₂ := Source.isElemAbelian_of_le hEe hE₂E
      have hE₂L : E₂ ≤ layer G := hE₂E.trans (hEle.trans inf_le_left)
      have hE₂a : E₂ ≤ Subgroup.centralizer {a} := hE₂E.trans (hEle.trans inf_le_right)
      have hz_notin : z ∉ E₂ := by
        intro hz
        have hmem : z ∈ layer G ⊓ Subgroup.centralizer (layer G : Set G) := ⟨hE₂L hz, hzC⟩
        rw [hLC] at hmem
        exact hz1 hmem
      obtain ⟨hB₂e, hB₂card⟩ := Sec5.isElemAbelian_sup_zpowers hE₂e hz_notin hz3
        fun b hb => Subgroup.mem_centralizer_iff.mp hzC b (hE₂L hb)
      have ha_notin : a ∉ E₂ ⊔ Subgroup.zpowers z := by
        intro haB
        refine not_inducesOuter_of_mem_sup ?_ hout
        exact (sup_le_sup hE₂L (Subgroup.zpowers_le.mpr hzC)) haB
      have hB₂a : E₂ ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer {a} :=
        sup_le hE₂a (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (hAc z hzA a ha)))
      obtain ⟨hFe, hFcard⟩ := Sec5.isElemAbelian_sup_zpowers hB₂e ha_notin ha3
        fun b hb => Subgroup.mem_centralizer_singleton_iff.mp (hB₂a hb)
      have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
        le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
          ⟨_, le_top, hFe, by rw [hFcard, hB₂card, hE₂card]; norm_num⟩
      omega
    ·
      have hap : IsPGroup 3 (Subgroup.zpowers a) :=
        h.isE27.isPGroup.to_le (Subgroup.zpowers_le.mpr ha)
      obtain ⟨v, hvLP, hvC, hv3, hv1⟩ := exists_mem_centralizer_pow_three hap
        (hPp.to_le inf_le_right) (Subgroup.zpowers_le.mpr (hPN (hAP ha))) hLP1
      have hva : v ∈ Subgroup.centralizer {a} :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hvC a (Subgroup.mem_zpowers a)).symm
      have hvE : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers v) := by
        refine ⟨inferInstance, fun x hx => ?_⟩
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv3, one_zpow]
      exact le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
        ⟨_, Subgroup.zpowers_le.mpr ⟨hvLP.1, hva⟩, hvE, by
          rw [Nat.card_zpowers, orderOf_eq_prime hv3 hv1, pow_one]⟩

end Ctx434Core

end CFSG.RankThree.PartTwo.Sec4
