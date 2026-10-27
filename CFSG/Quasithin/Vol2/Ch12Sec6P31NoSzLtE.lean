module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtStar
public import CFSG.Quasithin.Vol2.Ch12Sec6D29
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzE
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtGrp

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.QuasithinUnique
open scoped IsMulCommutative

section Main

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem isSz_star_lt {F : Frame126 T L V} {H K : Subgroup G}
    (h918 : HypF918 T V L F.V1 F.V5 H K) {n : ℕ} (hSz : IsSz n (starMod_w31 H K)) :
    IsSz n ↥(star H K) := by
  have hq : CFSG.IsQuasisimple ↥(star H K) :=
    CFSG.Quasithin.H13.P31Sec.isQuasisimple_star h918.K_cComp h918.K_quasisimple
  haveI : Group.IsPerfect ↥(star H K) := hq.1
  exact suzukiModel_of_odd_center (P31A.odd_card_center_star_K F h918) hSz

theorem exists_odd_normal_fpf_lt (h1222 : Stmt12_2_2)
    {F : Frame126 T L V} (hH : Hyp126 G T L V) {H K : Subgroup G} (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hne : conjClosure K T ≠ K) (hHq : SQTKGroup ↥H)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) {n : ℕ} (hSz : IsSz n (starMod_w31 H K)) :
    ∃ E : Subgroup (HStar H), E.Normal ∧ Odd (Nat.card E) ∧ (∃ e ∈ E, e ≠ 1) ∧
      E ≤ star H (Li L F.V1 ⊔ T) ∧
      E ≤ Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) ∧
      ∀ w : ↥(UT F.V1 F.V5 H), (∀ e ∈ E, psiH h918.toHypF98.toHypF91 e w = w) → w = 1 := by
  have h91 := h918.toHypF98.toHypF91
  have hKc : K ∈ cComp H := h918.K_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hL1TH : Li L F.V1 ⊔ T ≤ H := h918.L₁T_le_H
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans hL1TH
  have hTH : T ≤ H := h918.T_le_H
  have hq : CFSG.IsQuasisimple ↥(star H K) :=
    CFSG.Quasithin.H13.P31Sec.isQuasisimple_star hKc h918.K_quasisimple
  have hNn : (star H (conjClosure K T)).Normal := normal_star h918.K₀_normal
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
  obtain ⟨t, htT, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hne
    apply le_antisymm
    · exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  obtain ⟨-, hdata⟩ := five_group_data h918 hHq h37 h38 hne
  obtain ⟨hKt, hK₀eq, hcomm, hdich⟩ := hdata t htT htK
  have htH : t ∈ H := hTH htT
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  set tt : HStar H := QuotientGroup.mk ⟨t, htH⟩ with htt
  have hcommK : ∀ a ∈ star H K, ∀ b ∈ star H (K.map (MulAut.conj t).toMonoidHom), a * b = b * a :=
    commute_star_of_commutator_le hKH hKtH hcomm
  have hK₀star : star H (conjClosure K T) =
      star H K ⊔ star H (K.map (MulAut.conj t).toMonoidHom) := by
    rw [hK₀eq, S126P31.star_sup hKH hKtH]
  obtain ⟨P, hPL1, hPel, hP9⟩ := S126L26.exists_E9 h1222 F hH
  have hPH : P ≤ H := hPL1.trans hL1H
  have hP3 : ∀ p ∈ star H P, p ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hPel.2 (a : G) (Subgroup.mem_subgroupOf.1 ha)
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥H) a) ^ 3 = 1
    rw [← map_pow]
    have h2 : a ^ 3 = 1 := Subtype.ext (by simpa using h1)
    rw [h2, map_one]
  have hL1K : Li L F.V1 ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_oTwoUpper h37 h38 hHq hKc hL1H (S126D29.oTwoUpper_L₁Of L F.V1)
  have hAN : star H (Li L F.V1) ≤ Subgroup.normalizer (star H K : Set (HStar H)) :=
    S126P31.star_le_normalizer_star hKH hL1H hL1K
  have hTL1 : T ≤ Subgroup.normalizer (Li L F.V1 : Set G) :=
    S126L19b.T_le_normalizer_L1 h1222 hH
  have hTA : ∀ x ∈ star H T, ∀ a ∈ star H (Li L F.V1), x * a * x⁻¹ ∈ star H (Li L F.V1) := by
    intro x hx a ha
    have hxN := S126P31.star_le_normalizer_star hL1H hTH hTL1 hx
    exact (Subgroup.mem_normalizer_iff.1 hxN a).1 ha
  have hAT : star H (Li L F.V1) ≤ ⁅star H (Li L F.V1), star H T⁆ := by
    rw [← P31A.star_commutator hL1H hTH, P31A.comm_L1_T h1222 F hH]
  have htTs : tt ∈ star H T := S126P31.mk_mem_star htT
  have htN : tt ∉ Subgroup.normalizer (star H K : Set (HStar H)) := fun h =>
    htK (mem_normalizer_of_mk_mem_normalizer_star hKc htH h)
  have hdichS : ∀ x ∈ star H T, x ∈ Subgroup.normalizer (star H K : Set (HStar H)) ∨
      tt⁻¹ * x ∈ Subgroup.normalizer (star H K : Set (HStar H)) := by
    rintro _ ⟨s, hs, rfl⟩
    rcases hdich (s : G) s.2 with h | h
    · exact Or.inl (mk_mem_normalizer_star hKH h)
    · right
      have hmem : (QuotientGroup.mk ⟨t⁻¹ * (s : G), H.mul_mem (H.inv_mem htH) s.2⟩ : HStar H) ∈
          Subgroup.normalizer (star H K : Set (HStar H)) := mk_mem_normalizer_star hKH h
      have e : tt⁻¹ * (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) s =
          (QuotientGroup.mk ⟨t⁻¹ * (s : G), H.mul_mem (H.inv_mem htH) s.2⟩ : HStar H) := by
        rw [htt, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [e]
      exact hmem
  obtain ⟨x, hxP, hx1, hxC, hxC'⟩ := exists_ne_one_centralizes_pair (star H K) hOut h3 tt
    (star H (Li L F.V1)) (star H P) (star H T) hAN htTs htN hdichS hTA hAT
    (S126P31.star_mono hPL1) hP3 (star_not_isCyclic hPH hPel.2 hP9)
  set S : Subgroup (HStar H) := star H (Li L F.V1 ⊔ T) with hS
  have hxS : x ∈ S := S126P31.star_mono (hPL1.trans le_sup_left) hxP
  have hxK₀ : star H (conjClosure K T) ≤ Subgroup.centralizer ({x} : Set (HStar H)) := by
    rw [hK₀star]
    refine sup_le ?_ ?_
    · intro a ha
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact (Subgroup.mem_centralizer_iff.1 hxC a ha).symm
    · intro a ha
      rw [star_map_conj htH] at ha
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact (Subgroup.mem_centralizer_iff.1 hxC' a ha).symm
  have hxCK₀ : x ∈ Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) := by
    refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hxK₀ ha) x (Set.mem_singleton x)).symm
  let E₀ : Subgroup (HStar H) := Subgroup.closure {z | ∃ s ∈ S, z = s * x * s⁻¹}
  have hE₀S : E₀ ≤ S := by
    refine (Subgroup.closure_le S).2 ?_
    rintro _ ⟨s, hs, rfl⟩
    exact S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs)
  have hE₀C : E₀ ≤ Subgroup.centralizer (star H (conjClosure K T) : Set (HStar H)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro m hm
    have hm' : s⁻¹ * m * s ∈ star H (conjClosure K T) := by
      have := hNn.conj_mem m hm s⁻¹
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hxCK₀ _ hm'
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
  have hHeq : H = conjClosure K T ⊔ (Li L F.V1 ⊔ T) := hIs.2.2
  have hY : star H (conjClosure K T) ⊔ S = ⊤ := by
    rw [hS, ← S126P31.star_sup h918.K₀_le_H hL1TH, ← hHeq]
    exact S126P31.star_self
  have hE₀n : E₀.Normal := by
    refine ⟨fun z hz y => ?_⟩
    have hy : y ∈ (star H (conjClosure K T) ⊔ S : Subgroup (HStar H)) := by
      rw [hY]; exact Subgroup.mem_top y
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
