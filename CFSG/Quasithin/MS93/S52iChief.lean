module

public import CFSG.Quasithin.MS93.S52iFaith
public import CFSG.Quasithin.MS93.S52iFF
public import CFSG.Quasithin.MS93.S52iMod

public section

namespace CFSG.Quasithin.MS93.S52i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_of_chief {M N W : Subgroup G} (hWM : W ≤ M)
    (hNn : M ≤ Subgroup.normalizer (N : Set G)) (hWn : M ≤ Subgroup.normalizer (W : Set G))
    (hNW : N ≤ W) (hne : N ≠ W) (hW2 : IsPGroup 2 ↥W)
    (hch : ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → N ≤ J → J ≤ W →
      J = N ∨ J = W) : ⁅W, W⁆ ≤ N := by
  have hJn : M ≤ Subgroup.normalizer ((⁅W, W⁆ ⊔ N : Subgroup G) : Set G) :=
    (le_inf (S38E.le_normalizer_comm_of hWn hWn) hNn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  rcases hch _ hJn le_sup_right (sup_le (Subgroup.commutator_le_self W) hNW) with h | h
  · exact h ▸ le_sup_left
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hNn' : (N.subgroupOf W).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).2 (hWM.trans hNn)
    set Q := ↥W ⧸ N.subgroupOf W
    have hQ2 : IsPGroup 2 Q := hW2.to_quotient _
    have hQnt : Nontrivial Q := by
      obtain ⟨w, hwW, hwN⟩ : ∃ w ∈ W, w ∉ N := by
        by_contra hall
        push Not at hall
        exact hne (le_antisymm hNW hall)
      refine ⟨⟨QuotientGroup.mk ⟨w, hwW⟩, 1, fun h1 => hwN ?_⟩⟩
      have := (QuotientGroup.eq_one_iff (⟨w, hwW⟩ : ↥W)).1 h1
      exact Subgroup.mem_subgroupOf.1 this
    have htopW : (⊤ : Subgroup ↥W).map W.subtype = W := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hcomm : ⁅W, W⁆ = (commutator ↥W).map W.subtype := by
      rw [commutator_def, Subgroup.map_commutator, htopW]
    have hC : commutator ↥W ⊔ N.subgroupOf W = ⊤ := by
      apply Subgroup.map_injective W.subtype_injective
      rw [Subgroup.map_sup, ← hcomm, Subgroup.map_subgroupOf_eq_of_le hNW, htopW]
      exact h
    have hmk : (commutator ↥W).map (QuotientGroup.mk' (N.subgroupOf W)) = ⊤ := by
      have := congrArg (Subgroup.map (QuotientGroup.mk' (N.subgroupOf W))) hC
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
    have hperf : Group.IsPerfect Q := by
      rw [Group.isPerfect_def, eq_top_iff, ← hmk, commutator_def, commutator_def,
        Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact Group.IsPerfect.not_isNilpotent (G := Q) hQ2.isNilpotent

theorem le_relIndex_of_chief
    (h14 : MS14AS) (hSQ : SQTKQuot) {M T L : Subgroup G} (h : PUHyp M T L) {k : ℕ} {F : Type}
    [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a)
    {V Y E : Subgroup G} (hVM : V ≤ M) (hV2 : IsPGroup 2 ↥V) (hEM : E ≤ M)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hbig : (2 ≤ k → (2 ^ k) ^ 2 ≤ Nat.card (S5.imSp a E)) ∧
      (k = 1 → ∃ z : ↥M, (z : G) ∈ E ∧ a z ≠ 1 ∧ a z ∈ commutator (MSP.Sp4 F)))
    {N W : Subgroup G} (hNn : M ≤ Subgroup.normalizer (N : Set G))
    (hWn : M ≤ Subgroup.normalizer (W : Set G)) (hNW : N ≤ W) (hWV : W ≤ V)
    (hWN : ¬ ⁅W, L⁆ ≤ N)
    (hch : ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → N ≤ J → J ≤ W →
      J = N ∨ J = W)
    (hYE : ∀ y ∈ W ⊓ Y, ∀ e ∈ E, e * y * e⁻¹ * y⁻¹ ∈ N) :
    (2 ^ k) ^ 2 ≤ ((W ⊓ Y) ⊔ N).relIndex W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hk1 := hd.1
  have hWM : W ≤ M := hWV.trans hVM
  have hWNn : W ≤ Subgroup.normalizer (N : Set G) := hWM.trans hNn
  have hne : N ≠ W := fun hNW' => hWN (by
    rw [← hNW']
    exact commutator_le_left_of_le_normalizer (h.L_le.trans (hNW' ▸ hNn)))
  have hW2 : IsPGroup 2 ↥W := hV2.to_le hWV
  have hcomm := commutator_le_of_chief hWM hNn hWn hNW hne hW2 hch
  obtain ⟨S, _, p, ρ, hs⟩ := S36E.exists_secMod hNW hWn hNn
    (fun x hx y hy => hcomm (Subgroup.commutator_mem_commutator hx hy))
  have hL : ∃ l ∈ L, ∃ w ∈ W, l * w * l⁻¹ * w⁻¹ ∉ N := by
    by_contra hall
    push Not at hall
    exact hWN (S36E.commutator_le_of_centralizes hWNn hall)
  have hρ := isIrrRep_of_max hs hNW h.L_le hW2 hch hL
  have : Finite S := Finite.of_surjective p hs.surj
  have hS2 : ∀ s : S, s ^ 2 = 1 := hρ.sq
  set Eb := (E.subgroupOf M).map ρ with hEb
  have hfixsec : (W ⊓ Y) ⊔ N ≤ S36E.fixSec W N E hWNn := by
    refine sup_le (fun y hy => S36E.mem_fixSec.2 ⟨hy.1, fun e he => hYE y hy e he⟩)
      (fun n hn => S36E.mem_fixSec.2 ⟨hNW hn, fun e he => ?_⟩)
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.1 (hNn (hEM he)) n).1 hn) (N.inv_mem hn)
  have hne0 : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K => by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hidx : (fixV Eb).index < (2 ^ k) ^ 2 := by
    rw [hs.index_fixV hEM hWNn]
    exact lt_of_le_of_lt (Subgroup.relIndex_le_of_le_left hfixsec (hne0 _ _)) hlt
  have hsmall : Nat.card S < (2 ^ k) ^ 2 * Nat.card (fixV Eb) := by
    rw [← (fixV Eb).index_mul_card]
    exact Nat.mul_lt_mul_of_pos_right hidx Nat.card_pos
  have hker := ker_le_ker_of_isIrrRep h hd hρ
  have hcardE := card_imSp_le h hd hρ E
  set K := S38E.IsIrrRep.imL L ρ with hK
  have hmemK : ∀ z : ↥M, a z ∈ S5.imSp a L → ρ z ∈ K := by
    intro z hz
    obtain ⟨l, hl, hlz⟩ := hz
    have hn : ((l⁻¹ * z : ↥M) : G) ∈ S5.kerG a :=
      ⟨l⁻¹ * z, by show a (l⁻¹ * z) = 1; rw [map_mul, map_inv, hlz, inv_mul_cancel], rfl⟩
    obtain ⟨q, hq, w, hw, hqw⟩ := S5.IsSp4Data.exists_mul_of_mem_kerG hd h hn
    have hqM : q ∈ M := pCoreOf_le' M hq
    have hwM : w ∈ M := h.L_le hw.1
    have hz : z = l * ⟨q, hqM⟩ * ⟨w, hwM⟩ := by
      apply Subtype.ext
      have e1 : (z : G) = (l : G) * ((l⁻¹ * z : ↥M) : G) := by simp
      rw [e1, hqw]
      simp [mul_assoc]
    have hρq : ρ ⟨q, hqM⟩ = 1 := hρ.pCore _ hq
    rw [hz, map_mul, map_mul, hρq, mul_one, ← map_mul]
    exact ⟨l * ⟨w, hwM⟩, Subgroup.mem_subgroupOf.2 (L.mul_mem
      (Subgroup.mem_subgroupOf.1 hl) hw.1), rfl⟩
  have hz1 : ∀ z : ↥M, ρ z = 1 → a z = 1 := fun z hz => hker hz
  have hkey2 : 2 ≤ k → Eb ≤ K ∧ (2 ^ k) ^ 2 ≤ Nat.card Eb := by
    intro hk
    refine ⟨?_, (hbig.1 hk).trans hcardE⟩
    rintro _ ⟨z, -, rfl⟩
    refine hmemK z ?_
    rw [S5.imSp, S5B.map_L_eq_top h hd hk]
    exact Subgroup.mem_top _
  have hkey1 : k = 1 → ∃ x ∈ Eb, x ∈ K ∧ x ≠ 1 := by
    rintro rfl
    obtain ⟨z, hzE, hza, hzD⟩ := hbig.2 rfl
    refine ⟨ρ z, ⟨z, Subgroup.mem_subgroupOf.2 hzE, rfl⟩, hmemK z ?_, fun h1 => hza (hz1 z h1)⟩
    rw [S5.imSp, S5Q2.map_L_eq_commutator h hd]
    exact hzD
  have hEb1 : Eb ≠ ⊥ := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      obtain ⟨x, hx, -, hx1⟩ := hkey1 rfl
      intro hb
      rw [hb] at hx
      exact hx1 hx
    · intro hb
      have := (hkey2 hk).2
      rw [hb, Subgroup.card_bot] at this
      have : 4 ≤ (2 ^ k) ^ 2 := by
        calc 4 = (2 ^ 1) ^ 2 := by norm_num
          _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hk1) 2
      omega
  have hEbab : IsElemAbelian2 Eb := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx hy
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEab _ hx _ hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hE2 _ hx)
      rw [this, map_one]
  have hidx2 : (fixV Eb).index ≤ Nat.card Eb := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      have hS2' : IsPGroup 2 S := hW2.of_surjective p hs.surj
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2'
      have hdvd : (fixV Eb).index ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
      obtain ⟨m, hm, hme⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hm1 : m ≤ 1 := by
        by_contra hm2
        push Not at hm2
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        rw [← hme] at this
        have h4 : (fixV Eb).index < 4 := by simpa using hidx
        omega
      have hEb2 : 2 ≤ Nat.card Eb := by
        have : 1 < Nat.card Eb := by
          rw [Subgroup.one_lt_card_iff_ne_bot]
          exact hEb1
        omega
      calc (fixV Eb).index = 2 ^ m := hme
        _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
        _ ≤ Nat.card Eb := by simpa using hEb2
    · exact hidx.le.trans (hkey2 hk).2
  have hFFmod : IsFFModule ρ.range := by
    refine ⟨Eb, Subgroup.map_le_range _ _, hEb1, hEbab, ?_⟩
    rw [← (fixV Eb).index_mul_card]
    exact Nat.mul_le_mul_right _ hidx2
  have hFF := hρ.ffHyp h hSQ hFFmod
  have htype : (k = 1 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 360) ∨
      (2 ≤ k ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = CFSG.Open.ordBC 2 (2 ^ k)) := by
    rw [S36E.card_quot_center_imL hρ h]
    exact card_lstar_of_sp4Data h hd
  exact false_of_small h14 hS2 hFF hk1 hsmall htype hkey2 hkey1

end CFSG.Quasithin.MS93.S52i
