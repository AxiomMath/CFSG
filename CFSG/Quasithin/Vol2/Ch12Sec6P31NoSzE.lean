module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzSet
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzOut
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoM22
public import CFSG.Quasithin.Vol2.Ch12Sec6L26d
public import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped IsMulCommutative

section Star

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

theorem star_not_isCyclic {P : Subgroup G} (hPH : P ≤ H) (hP3 : ∀ p ∈ P, p ^ 3 = 1)
    (hP9 : Nat.card P = 9) : ¬ IsCyclic ↥(star H P) := by
  intro hcyc
  let f : ↥P →* ↥(star H P) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (P.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hPH).symm.toMonoidHom
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨(a : G), hPH a.2⟩ : ↥H) = 1 :=
      congrArg Subtype.val ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, h1⟩
    have h2 : (⟨(a : G), hPH a.2⟩ : ↥H) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      exact Subtype.ext (by simpa using this)
    have h3 : (⟨(a : G), hPH a.2⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hP3 a a.2)
    have h4 := S126L26.eq_one_of_two_three' h2 h3
    rw [Subgroup.mem_bot]
    exact Subtype.ext (congrArg (Subtype.val : ↥H → G) h4)
  haveI : IsCyclic ↥P := isCyclic_of_injective f hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥P)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hP3 g g.2)
  have := orderOf_dvd_of_pow_eq_one hg3
  rw [hg, hP9] at this
  omega

end Star

section Main

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_odd_normal_fpf (h1222 : Stmt12_2_2)
    {F : Frame126 T L V} (hH : Hyp126 G T L V) {H K : Subgroup G} (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hKK : conjClosure K T = K) {n : ℕ}
    (hSz : IsSz n (starMod_w31 H K)) :
    ∃ E : Subgroup (HStar H), E.Normal ∧ Odd (Nat.card E) ∧ (∃ e ∈ E, e ≠ 1) ∧
      E ≤ star H (Li L F.V1 ⊔ T) ∧ E ≤ Subgroup.centralizer (star H K : Set (HStar H)) ∧
      ∀ w : ↥(UT F.V1 F.V5 H), (∀ e ∈ E, psiH h918.toHypF98.toHypF91 e w = w) → w = 1 := by
  have h91 := h918.toHypF98.toHypF91
  have hKc : K ∈ cComp H := h918.K_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hL1TH : Li L F.V1 ⊔ T ≤ H := h918.L₁T_le_H
  have hq : CFSG.IsQuasisimple ↥(star H K) :=
    CFSG.Quasithin.H13.P31Sec.isQuasisimple_star hKc h918.K_quasisimple
  have hNn : (star H K).Normal := normal_star (by simpa [hKK] using h918.K₀_normal)
  have hSzM : SuzukiModel (↥(star H K) ⧸ Subgroup.center ↥(star H K)) 2 n := hSz
  haveI : Group.IsPerfect ↥(star H K) := hq.1
  have hOut : IsCyclic (Outer ↥(star H K)) :=
    ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 n hSzM).2
      ↥(star H K) ⟨MulEquiv.refl _⟩).1
  have h3 : ∀ g : ↥(star H K) ⧸ Subgroup.center ↥(star H K), g ^ 3 = 1 → g = 1 := by
    obtain ⟨-, a, ha, K', _, _, hn, hK', ⟨α⟩⟩ := hSzM
    intro g hg
    by_contra hg1
    have hord : orderOf g = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hg) with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hg1
      · exact h
    have hdvd : 3 ∣ Nat.card (suzukiGroup a K') := by
      rw [← Nat.card_congr α.toEquiv, ← hord]
      exact orderOf_dvd_natCard g
    exact CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup (hn ▸ hK') hdvd
  obtain ⟨P, hPL1, hPel, hP9⟩ := S126L26.exists_E9 h1222 F hH
  have hPH : P ≤ H := hPL1.trans (le_sup_left.trans hL1TH)
  have hP3 : ∀ p ∈ star H P, p ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hPel.2 (a : G) (Subgroup.mem_subgroupOf.1 ha)
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a) ^ 3 = 1
    rw [← map_pow]
    have h2 : a ^ 3 = 1 := Subtype.ext (by simpa using h1)
    rw [h2, map_one]
  obtain ⟨x, hxP, hx1, hxC⟩ := exists_ne_one_centralizes (star H K) hOut h3 (star H P) hP3
    (star_not_isCyclic hPH hPel.2 hP9)
  set S : Subgroup (HStar H) := star H (Li L F.V1 ⊔ T) with hS
  have hxS : x ∈ S := star_mono (hPL1.trans le_sup_left) hxP
  let E₀ : Subgroup (HStar H) := Subgroup.closure {z | ∃ s ∈ S, z = s * x * s⁻¹}
  have hE₀S : E₀ ≤ S := by
    refine (Subgroup.closure_le S).2 ?_
    rintro _ ⟨s, hs, rfl⟩
    exact S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs)
  have hE₀C : E₀ ≤ Subgroup.centralizer (star H K : Set (HStar H)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro m hm
    have hm' : s⁻¹ * m * s ∈ star H K := by
      have := hNn.conj_mem m hm s⁻¹
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hxC _ hm'
    calc m * (s * x * s⁻¹) = s * ((s⁻¹ * m * s) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * m * s)) * s⁻¹ := by rw [hc]
      _ = s * x * s⁻¹ * m := by group
  have hS_conj : ∀ s ∈ S, ∀ z ∈ E₀, s * z * s⁻¹ ∈ E₀ := by
    intro s hs z hz
    induction hz using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨t, ht, rfl⟩ := hu
      exact Subgroup.subset_closure ⟨s * t, S.mul_mem hs ht, by group⟩
    | one => simpa using E₀.one_mem
    | mul a b _ _ ha hb =>
      have := E₀.mul_mem ha hb
      simpa [mul_assoc] using this
    | inv a _ ha =>
      have := E₀.inv_mem ha
      simpa [mul_assoc] using this
  have hHeq : H = K ⊔ (Li L F.V1 ⊔ T) := by
    have := hIs.2.2
    rwa [hKK] at this
  have hY : star H K ⊔ S = ⊤ := by
    rw [hS, ← star_sup hKH hL1TH, ← hHeq]
    exact star_self
  have hE₀n : E₀.Normal := by
    refine ⟨fun z hz y => ?_⟩
    have hy : y ∈ (star H K ⊔ S : Subgroup (HStar H)) := by rw [hY]; exact Subgroup.mem_top y
    have hyp := hy
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hyp
    obtain ⟨m, hm, s, hs, rfl⟩ := hyp
    have h1 := hS_conj s hs z hz
    have h2 : m * (s * z * s⁻¹) * m⁻¹ = s * z * s⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 (hE₀C h1) m hm
      rw [this]; group
    have : m * s * z * (m * s)⁻¹ = m * (s * z * s⁻¹) * m⁻¹ := by group
    rw [this, h2]
    exact h1
  have hEne : E₀ ≠ ⊥ := by
    intro hbot
    apply hx1
    have : x ∈ E₀ := Subgroup.subset_closure ⟨1, S.one_mem, by group⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hSsolv : Group.IsSolvable ↥S :=
    CFSG.Quasithin.H13.P31A.isSolvable_star
      (CFSG.Quasithin.H13.P31Sec.isSolvable_L1T h1222 hH)
  have hE₀solv : Group.IsSolvable ↥E₀ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hE₀S)
      (Subgroup.inclusion_injective _)
  obtain ⟨D, hDn, hDE, hDne, hDodd⟩ := exists_odd_normal_le
    (fun M hM hMp => eq_bot_of_isPGroup hM hMp) E₀ hE₀solv hEne
  obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  refine ⟨D, hDn, hDodd, ⟨d, hd, hd1'⟩, hDE.trans hE₀S, hDE.trans hE₀C, ?_⟩
  intro w hw
  exact fixed_eq_one_of_odd_normal h91 D hDodd ⟨d, hd, hd1'⟩ (hDE.trans hE₀S) hw

end Main

end CFSG.Quasithin.H13.P31Sz
