module

public import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
public import CFSG.RankThree.PartTwo.KFacts.KS18GL33
import CFSG.RankThree.PartTwo.Sec3.ThreeGroupCentralizer
import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.RankThree.PartTwo.Sec19.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18
open scoped Pointwise

@[expose] def Step1914E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M → Nat.card (E ⊓ L : Subgroup G) = 9

section Transvection

variable {V : Type*} [Group V]

theorem pow_apply_of_transvection {F : Subgroup V} {σ : MulAut V} (hF : ∀ f ∈ F, σ f = f)
    (hσ : ∀ v, σ v * v⁻¹ ∈ F) (v : V) (k : ℕ) : (σ ^ k) v = (σ v * v⁻¹) ^ k * v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hF _ (hσ v), pow_succ]
    group

end Transvection

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_pow_two_pow_of_pow_three_pow {x : G} {j k : ℕ} (h2 : x ^ (2 ^ j) = 1)
    (h3 : x ^ (3 ^ k) = 1) : x = 1 := by
  have hd : orderOf x ∣ Nat.gcd (2 ^ j) (3 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow j k (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  exact hd

theorem rank3II_19_19_O2_of (h1914 : Step1914) (h1914E : Step1914E) (hK : KFacts.KS18GL33) :
    Step1919O2 := by
  intro G _ _ A c L E M hctx hLM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := (h1914 G A c L E M hctx).2 hLM
  have h9 := h1914E G A c L E M hctx hLM
  set F := E ⊓ L with hFdef
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hFE : F ≤ E := inf_le_left
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
      (hctx.mem_partTwoE.1.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  set X := oUpperThreePrime (Sec4.autIn (Subgroup.normalizer (F : Set G)) E) with hXdef
  have hXle : X ≤ Sec4.autIn (Subgroup.normalizer (F : Set G)) E := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro σ ⟨hσ, -⟩
    exact hσ
  have hF'9 : Nat.card (F.subgroupOf E) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv]
    exact h9
  have hEab : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup E) := by
    have := (isE27_subgroupOf hE le_rfl).1
    rwa [Subgroup.subgroupOf_self] at this
  have hstab : ∀ σ ∈ X, (F.subgroupOf E).map σ.toMonoidHom = F.subgroupOf E := by
    intro σ hσ
    obtain ⟨g, hgN, hgF, hgσ⟩ := Sec4.mem_autIn_iff.mp (hXle hσ)
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective σ.injective])
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ F.subgroupOf E at hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [← hgσ]
    change ((E.normalizerMonoidHom ⟨g, hgN⟩ x : E) : G) ∈ F
    rw [Sec4.normalizerMonoidHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hgF _).mp hx
  obtain ⟨σ, hσX, hσF, hσE, hσmove⟩ := hK E hEab hE.2 (F.subgroupOf E) hF'9 X hstab hX
  obtain ⟨g, hgN, hgF, hgσ⟩ := Sec4.mem_autIn_iff.mp (hXle hσX)
  obtain ⟨a, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  set y := g ^ m with hy
  have hy3 : y ^ (3 ^ a) = 1 := by
    rw [hy, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hyN : y ∈ Subgroup.normalizer (E : Set G) := Subgroup.pow_mem _ hgN m
  have hyF : y ∈ Subgroup.normalizer (F : Set G) := Subgroup.pow_mem _ hgF m
  have hyσ : E.normalizerMonoidHom ⟨y, hyN⟩ = σ ^ m := by
    rw [← hgσ, ← map_pow]
    congr 1
  have hyact : ∀ e (he : e ∈ E), y * e * y⁻¹ = ((σ ^ m) ⟨e, he⟩ : G) := by
    intro e he
    rw [← hyσ, Sec4.normalizerMonoidHom_apply_coe]
  have hyFfix : ∀ f ∈ F, y * f * y⁻¹ = f := by
    intro f hf
    rw [hyact f (hFE hf), pow_apply_of_transvection hσF hσE,
      hσF ⟨f, hFE hf⟩ (Subgroup.mem_subgroupOf.mpr hf)]
    simp
  have hyE : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ F := by
    intro e he
    rw [hyact e he, pow_apply_of_transvection hσF hσE]
    have h1 := (F.subgroupOf E).pow_mem (hσE ⟨e, he⟩) m
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hcy : c * y ≠ y * c := by
    intro hcomm
    have hc' : (⟨c, hcE⟩ : E) ∉ F.subgroupOf E := by
      rw [Subgroup.mem_subgroupOf]
      exact fun h => hcL h.2
    have hmove := hσmove _ hc'
    obtain ⟨w, hw⟩ : ∃ w : E, w = σ ⟨c, hcE⟩ * (⟨c, hcE⟩ : E)⁻¹ := ⟨_, rfl⟩
    have hw1 : w ≠ 1 := fun h => hmove (by rw [← mul_inv_eq_one, ← hw]; exact h)
    have hw3 : w ^ 3 = 1 := Subtype.ext (by simpa using hE.1.2 _ w.2)
    have hwm : w ^ m ≠ 1 := by
      intro h
      have hd : orderOf w ∣ Nat.gcd 3 m :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one h)
      rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3),
        Nat.dvd_one, orderOf_eq_one_iff] at hd
      exact hw1 hd
    apply hwm
    have h1 := hyact c hcE
    rw [pow_apply_of_transvection hσF hσE, ← hw] at h1
    have h2 : y * c * y⁻¹ = c := by
      rw [← hcomm]
      group
    rw [h2] at h1
    apply Subtype.ext
    simp only [Subgroup.coe_mul] at h1
    simpa using h1
  set P := E ⊔ Subgroup.zpowers y with hPdef
  have hyP3 : IsPGroup 3 (Subgroup.zpowers y) := by
    rintro ⟨z, hz⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hyNE : Subgroup.zpowers y ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.zpowers_le.mpr hyN
  have hP3 : IsPGroup 3 P := by
    rw [hPdef, sup_comm]
    exact hyP3.to_sup_of_normal_right' hE.isPGroup hyNE
  have hFgam : Subgroup.normalizer (F : Set G) ≤ M := by
    have hFab : CFSG.Assembly.IsElemAbelian 3 F := Late.isElemAbelian_of_le hE.1 hFE
    exact (normalizer_le_gamma hFE (two_le_pRank_of_elemAbelian hFab h9.ge)).trans
      hctx.mem_scriptM.2
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  have hPM : P ≤ M := sup_le hEM (Subgroup.zpowers_le.mpr (hFgam hyF))
  have hFcen : ∀ f ∈ F, ∀ p ∈ P, f * p = p * f := by
    intro f hf p hp
    have hle : P ≤ Subgroup.centralizer ({f} : Set G) := by
      refine sup_le (le_centralizer_of_mem hE.1.1 (hFE hf)) (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hyFfix f hf
      calc y * f = y * f * y⁻¹ * y := by group
        _ = f * y := by rw [this]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hp)).symm
  have hcomm : ∀ p ∈ P, y * p * y⁻¹ * p⁻¹ ∈ F := by
    intro p hp
    have hp' : p ∈ ((E : Set G) * (Subgroup.zpowers y : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left E _ hyNE]
      exact hp
    obtain ⟨e, he, z, hz, rfl⟩ := hp'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 : y * (e * y ^ k) * y⁻¹ * (e * y ^ k)⁻¹ = y * e * y⁻¹ * e⁻¹ := by group
    rw [h1]
    exact hyE e he
  have hyZ2 : (⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩ : P) ∈
      Subgroup.upperCentralSeries P 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
      Subgroup.upperCentralSeries_one]
    intro p
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hFcen _ (hcomm p p.2) q q.2).symm
  have hM2 : CFSG.Assembly.IsTwoLocal M := hctx.mem_scriptM.1.1
  have hfaith : ∀ x ∈ P, (∀ s ∈ CFSG.Open.pCoreOf 2 M, x * s = s * x) → x = 1 := by
    intro x hx hxs
    have hxC : x ∈ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 M : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun s hs => (hxs s hs).symm
    have hxO : x ∈ CFSG.Open.pCoreOf 2 M := hctx.charTwoType M hM2 ⟨hPM hx, hxC⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨x, hxO⟩
    obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    exact eq_one_of_pow_two_pow_of_pow_three_pow (by simpa using congrArg Subtype.val hj)
      (by simpa using congrArg Subtype.val hk)
  rcases Sec3.rank3II_3_19 hP3 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
      (hPM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hfaith
      (Subgroup.mem_sup_left hcE) hc3 with h | h
  · exact absurd (h y ⟨_, hyZ2, rfl⟩) hcy
  · exact h

end CFSG.RankThree.PartTwo.Sec19
