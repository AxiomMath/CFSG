module

public import CFSG.Quasithin.H13.A6S13821zn
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.A6S13821zh

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_mem_KQ_13820a {H K : Subgroup G}
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : ¬ S.X13820 ≤ K) {c : G}
    (htri : ∀ y ∈ S.X13820, y ∈ pCoreOf 2 H ∨ y * c⁻¹ ∈ pCoreOf 2 H ∨ y * c ∈ pCoreOf 2 H)
    {k : G} (hk : k ∈ K) (hkc : k⁻¹ * c ∈ pCoreOf 2 H) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQ
  have hcKQ : c ∈ K ⊔ Q := by
    have e : c = k * (k⁻¹ * c) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hk hkc
  have hXKQ : S.X13820 ≤ K ⊔ Q := by
    intro y hy
    rcases htri y hy with h | h | h
    · exact Subgroup.mem_sup_right h
    · have e : y = (y * c⁻¹) * c := by group
      rw [e]
      exact (K ⊔ Q).mul_mem (Subgroup.mem_sup_right h) hcKQ
    · have e : y = (y * c) * c⁻¹ := by group
      rw [e]
      exact (K ⊔ Q).mul_mem (Subgroup.mem_sup_right h) ((K ⊔ Q).inv_mem hcKQ)
  apply hXK
  rw [S.plusData_X13820.eq]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxX, hodd⟩ := hx
  exact A5.mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 H) ((pCoreOf_le 2 H).trans hKn)
    (hXKQ hxX) hodd (pow_orderOf_eq_one x)

theorem false_of_rank_two_13820a
    {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n) (ha : S.Case13820aHyp H K)
    (h : IsPSp4 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
      IsG2 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
      (Even n ∧ IsPSL 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K))) ∨
      (Odd n ∧ IsPSU 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)))) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hS, hH, hK, hKn, -, -, -⟩ := hC
  obtain ⟨hXK, hXc, hHX, -⟩ := ha
  obtain ⟨c, hcX, hc3, -, hfpf, htri, -⟩ := S.exists_c_13820a' hS hH hHX
  obtain ⟨E, hE, hE9⟩ := A6E9.exists_nine_of_rank_two h
  have hF := (hS.hF H hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hcH : c ∈ H := (le_sup_left.trans hH.1.1) (S.plusData_X13820.le_L1 hcX)
  set φ := actH hV₁ hIH with hφ
  have hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [hφ, A6Tv.actH_eq_one_iff hV₁ hIHN hIH, hF.pCoreOf_eq_centralizerMod, mem_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hKSt : S.KSt H K = (K.subgroupOf H).map φ := autOn_tilde_eq_map_actH hV₁ hIH hKH
  set E' := E.map (S.KSt H K).subtype with hE'
  have hE'K : E' ≤ S.KSt H K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE9]
  have hE'ea : CFSG.Assembly.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      apply Subtype.ext
      show (S.KSt H K).subtype a' * (S.KSt H K).subtype b' =
        (S.KSt H K).subtype b' * (S.KSt H K).subtype a'
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow, hE.2 x' hx', map_one]
  set cs := φ ⟨c, hcH⟩ with hcs
  have hcs3 : cs ^ 3 = 1 := by
    have h1 : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [hcs, ← map_pow, h1, map_one]
  have hcomm : ∀ a ∈ E', a * cs = cs * a := by
    intro a ha
    have haK := hE'K ha
    rw [hKSt] at haK
    obtain ⟨k, hk, rfl⟩ := haK
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have h1 : φ (⟨c, hcH⟩ * k * (⟨c, hcH⟩ : ↥H)⁻¹ * k⁻¹) = 1 :=
      (hker _).mpr (hXc c hcX k hkK)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  have hcsE : cs ∉ E' := by
    intro hc
    have hcK := hE'K hc
    rw [hKSt] at hcK
    obtain ⟨k, hk, hkc⟩ := hcK
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have h1 : φ (k⁻¹ * ⟨c, hcH⟩) = 1 := by
      rw [map_mul, map_inv, hkc, hcs, inv_mul_cancel]
    exact S.not_mem_KQ_13820a hKn hXK htri hkK ((hker _).mp h1)
  obtain ⟨hF27, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE'ea hcsE hcs3
    hcomm
  have hFle : E' ⊔ Subgroup.zpowers cs ≤ φ.range := by
    refine sup_le (hE'K.trans ?_) ?_
    · rw [hKSt]
      rintro _ ⟨k, -, rfl⟩
      exact ⟨k, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
  have hrank := A6Tv.pRank_range_le_two hF S.h13.qtke φ hker
  have h3 : 3 ≤ CFSG.Open.pRank 3 φ.range := by
    refine le_csSup ⟨Nat.card (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))), ?_⟩
      ⟨E' ⊔ Subgroup.zpowers cs, hFle, ⟨hF27.1, hF27.2⟩, by rw [hcard, hE'9]; norm_num⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ _ := Subgroup.card_le_card_group B
  omega

end Setting4

end CFSG.Quasithin.H13.A6
