module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineNormal
import CFSG.GroupTheory.SqMemSubgroup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KFieldGenerator
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem commutator_mem_innAut_of_gen {X : Type*} [Group X] {θ₀ : MulAut X}
    (hgen : ∀ θ : MulAut X, ∃ j : ℕ, ∃ x : X, θ = θ₀ ^ j * MulAut.conj x) :
    ∀ a b : MulAut X, a * b * a⁻¹ * b⁻¹ ∈
      (MulAut.conj : X →* MulAut X).range := by
  classical
  let Inn : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range
  haveI hInn : Inn.Normal := inferInstance
  have hcomm : IsMulCommutative (MulAut X ⧸ Inn) := by
    refine IsMulCommutative.mk ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H g =>
      induction b using QuotientGroup.induction_on with
      | H h =>
        obtain ⟨j, x, rfl⟩ := hgen g
        obtain ⟨l, y, rfl⟩ := hgen h
        have hg : QuotientGroup.mk' Inn (θ₀ ^ j * MulAut.conj x) =
            (QuotientGroup.mk' Inn θ₀) ^ j := by
          rw [map_mul, map_pow]
          have hx : QuotientGroup.mk' Inn (MulAut.conj x) = 1 := by
            rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
            exact ⟨x, rfl⟩
          rw [hx, mul_one]
        have hh : QuotientGroup.mk' Inn (θ₀ ^ l * MulAut.conj y) =
            (QuotientGroup.mk' Inn θ₀) ^ l := by
          rw [map_mul, map_pow]
          have hy : QuotientGroup.mk' Inn (MulAut.conj y) = 1 := by
            rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
            exact ⟨y, rfl⟩
          rw [hy, mul_one]
        change QuotientGroup.mk' Inn (θ₀ ^ j * MulAut.conj x) *
            QuotientGroup.mk' Inn (θ₀ ^ l * MulAut.conj y) =
          QuotientGroup.mk' Inn (θ₀ ^ l * MulAut.conj y) *
            QuotientGroup.mk' Inn (θ₀ ^ j * MulAut.conj x)
        rw [hg, hh, ← pow_add, ← pow_add, Nat.add_comm]
  have hle : _root_.commutator (MulAut X) ≤ Inn :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mp hcomm
  rw [_root_.commutator_def] at hle
  intro a b
  have h := (Subgroup.commutator_le.mp hle) a (Subgroup.mem_top a) b (Subgroup.mem_top b)
  simpa [commutatorElement_def, Inn] using h

private noncomputable def fieldT1 (D : Data G) (K : Subgroup G) (θ₀ : MulAut (Bar2 K))
    (hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x) : Subgroup G :=
  D.T ⊓ Subgroup.map (Subgroup.normalizer (K : Set G)).subtype
    (Subgroup.comap (UC6S846.rhoL K)
      (CFSG.GroupTheory.sqMemSubgroup
        (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range
        (commutator_mem_innAut_of_gen hgen)))

private theorem mem_fieldT1 {D : Data G} {K : Subgroup G} {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ fieldT1 D K θ₀ hgen ↔ t ∈ D.T ∧
      (UC6S846.rhoL K ⟨t, ht⟩) ^ 2 ∈
        (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
  rw [fieldT1, Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨htT, n, hn, hnt⟩
    have hn' : n = ⟨t, ht⟩ := Subtype.ext hnt
    rw [hn'] at hn
    rw [Subgroup.mem_comap] at hn
    exact ⟨htT, by simpa [CFSG.GroupTheory.mem_sqMemSubgroup] using hn⟩
  · rintro ⟨htT, hsq⟩
    refine ⟨htT, ⟨t, ht⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    simpa [CFSG.GroupTheory.mem_sqMemSubgroup] using hsq

private theorem fieldT1_le_T {D : Data G} {K : Subgroup G} {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x} :
    fieldT1 D K θ₀ hgen ≤ D.T :=
  inf_le_left

private theorem T_le_normalizer_fieldT1 {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x} :
    D.T ≤ Subgroup.normalizer (fieldT1 D K θ₀ hgen : Set G) := by
  haveI hInn : ((MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range).Normal :=
    inferInstance
  rw [Subgroup.le_normalizer_iff]
  intro t htT x hx
  have hxT : x ∈ D.T := fieldT1_le_T (K := K) (θ₀ := θ₀) (hgen := hgen) hx
  have htN : t ∈ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn htT
  have hxN : x ∈ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn hxT
  have hconjN : t * x * t⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).mul_mem htN hxN)
      ((Subgroup.normalizer (K : Set G)).inv_mem htN)
  rw [mem_fieldT1 hconjN]
  refine ⟨D.T.mul_mem (D.T.mul_mem htT hxT) (D.T.inv_mem htT), ?_⟩
  rw [mem_fieldT1 hxN] at hx
  obtain ⟨-, hxsq⟩ := hx
  have hrho : (⟨t * x * t⁻¹, hconjN⟩ :
      ↥(Subgroup.normalizer (K : Set G))) =
      ⟨t, htN⟩ * ⟨x, hxN⟩ * ⟨t, htN⟩⁻¹ := Subtype.ext rfl
  have hsq : (UC6S846.rhoL K ⟨t * x * t⁻¹, hconjN⟩) ^ 2 =
      UC6S846.rhoL K ⟨t, htN⟩ *
        (UC6S846.rhoL K ⟨x, hxN⟩) ^ 2 *
        (UC6S846.rhoL K ⟨t, htN⟩)⁻¹ := by
    rw [hrho]
    simp only [map_mul, map_inv, pow_two]
    group
  rw [hsq]
  exact hInn.conj_mem ((UC6S846.rhoL K ⟨x, hxN⟩) ^ 2) hxsq
    (UC6S846.rhoL K ⟨t, htN⟩)

private theorem T_le_sup_zpowers_fieldT1 {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x} {t₀ : G} (ht₀ : t₀ ∈ D.T)
    (hθ₀ : UC6S846.rhoL K
      ⟨t₀, T_le_normalizer_of_normal hK hKn ht₀⟩ = θ₀) :
    D.T ≤ fieldT1 D K θ₀ hgen ⊔ Subgroup.zpowers t₀ := by
  intro t htT
  have htN : t ∈ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn htT
  have ht₀N : t₀ ∈ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn ht₀
  obtain ⟨j, x, hx⟩ := hgen (UC6S846.rhoL K ⟨t, htN⟩)
  let u : G := (t₀ ^ j)⁻¹ * t
  have huT : u ∈ D.T :=
    D.T.mul_mem (D.T.inv_mem (D.T.pow_mem ht₀ j)) htT
  have huN : u ∈ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn huT
  have huT1 : u ∈ fieldT1 D K θ₀ hgen := by
    rw [mem_fieldT1 huN]
    refine ⟨huT, ?_⟩
    have hrho : UC6S846.rhoL K ⟨u, huN⟩ = MulAut.conj x := by
      have heq : (⟨u, huN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          (⟨t₀, ht₀N⟩ ^ j)⁻¹ * ⟨t, htN⟩ := Subtype.ext (by simp [u])
      rw [heq, map_mul, map_inv, map_pow, hθ₀, hx]
      group
    rw [hrho]
    exact ⟨x * x, by rw [map_mul, pow_two]⟩
  have ht_eq : t = t₀ ^ j * u := by
    simp [u]
  rw [ht_eq]
  simpa [sup_comm] using
    Subgroup.mul_mem_sup
      (Subgroup.pow_mem (Subgroup.zpowers t₀) (Subgroup.mem_zpowers t₀) j) huT1

private theorem inf_le_fieldT1 {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x} :
    D.T ⊓ K ≤ fieldT1 D K θ₀ hgen := by
  intro t ht
  obtain ⟨htT, htK⟩ := Subgroup.mem_inf.mp ht
  have htN : t ∈ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn htT
  rw [mem_fieldT1 htN]
  refine ⟨htT, ?_⟩
  have hinner : UC6S846.rhoL K ⟨t, htN⟩ =
      MulAut.conj (QuotientGroup.mk (⟨t, htK⟩ : ↥K)) := by
    simpa using UC6S846.rhoL_inner K t htK
  rw [hinner]
  exact ⟨QuotientGroup.mk (⟨t, htK⟩ : ↥K) * QuotientGroup.mk (⟨t, htK⟩ : ↥K),
    by rw [map_mul, pow_two]⟩

private theorem thompsonJ_le_fieldT1 {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x} :
    InS3.thompsonJ D.T ≤ fieldT1 D K θ₀ hgen := by
  change (CFSG.elemThompson ↥D.T 2).map D.T.subtype ≤ fieldT1 D K θ₀ hgen
  have hfam : CFSG.elemThompson ↥D.T 2 ≤
      (fieldT1 D K θ₀ hgen).subgroupOf D.T := by
    change sSup (CFSG.elemThompsonFamily ↥D.T 2) ≤
      (fieldT1 D K θ₀ hgen).subgroupOf D.T
    refine sSup_le ?_
    rintro A ⟨hAelem, -⟩ a ha
    rw [Subgroup.mem_subgroupOf]
    have ha2 : a ^ 2 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
    have haG2 : ((a : G)) ^ 2 = 1 := by
      have := congrArg (D.T.subtype) ha2
      simpa using this
    have haN : (a : G) ∈ Subgroup.normalizer (K : Set G) :=
      T_le_normalizer_of_normal hK hKn a.2
    rw [mem_fieldT1 haN]
    refine ⟨a.2, ?_⟩
    have hsq : (UC6S846.rhoL K ⟨(a : G), haN⟩) ^ 2 = 1 := by
      have heq : (⟨(a : G), haN⟩ :
          ↥(Subgroup.normalizer (K : Set G))) ^ 2 = 1 := by
        apply Subtype.ext
        simpa using haG2
      calc (UC6S846.rhoL K ⟨(a : G), haN⟩) ^ 2
          = UC6S846.rhoL K ((⟨(a : G), haN⟩ :
              ↥(Subgroup.normalizer (K : Set G))) ^ 2) := (map_pow _ _ 2).symm
        _ = UC6S846.rhoL K 1 := by rw [heq]
        _ = 1 := map_one _
    rw [hsq]
    exact Subgroup.one_mem _
  calc (CFSG.elemThompson ↥D.T 2).map D.T.subtype
      ≤ ((fieldT1 D K θ₀ hgen).subgroupOf D.T).map D.T.subtype :=
        Subgroup.map_mono hfam
    _ ≤ fieldT1 D K θ₀ hgen := by
      rw [Subgroup.map_subgroupOf_eq_of_le
        (fieldT1_le_T (K := K) (θ₀ := θ₀) (hgen := hgen))]

private theorem two_pow_div_two_eq {e : ℕ} (he : 2 ≤ e) :
    2 ^ e / 2 = 2 * 2 ^ (e - 2) := by
  have hdiv : 2 ^ e / 2 = 2 ^ (e - 1) := by
    rw [show e = (e - 1) + 1 by omega, pow_succ,
      Nat.mul_div_left _ (by norm_num : 0 < 2)]
    congr 1
  have htwo : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := by
    rw [show e - 1 = (e - 2) + 1 by omega, pow_succ]
    ring
  rw [hdiv, htwo]

private noncomputable def fieldTheta (D : Data G) (K : Subgroup G) (θ₀ : MulAut (Bar2 K))
    (hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x) : Subgroup (MulAut (Bar2 K)) :=
  Subgroup.map (UC6S846.rhoL K)
    ((fieldT1 D K θ₀ hgen).subgroupOf (Subgroup.normalizer (K : Set G)))

private theorem fieldTheta_sq_mem_inn {D : Data G} {K : Subgroup G}
    {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x} :
    ∀ θ ∈ fieldTheta D K θ₀ hgen,
      θ ^ 2 ∈ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
  intro θ hθ
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hθ
  have hrT1 : (r : G) ∈ fieldT1 D K θ₀ hgen := Subgroup.mem_subgroupOf.mp hr
  exact ((mem_fieldT1 r.2).mp hrT1).2

private theorem not_one_of_borelFixed {X : Type*} [Group X] {Θ : Subgroup (MulAut X)}
    {e m : ℕ}
    (hHnot : m = 1 → 2 ≤ 2 ^ e →
      ∃ θ ∈ Θ, ∀ x : X, θ ^ (2 ^ e / 2) ≠ MulAut.conj x)
    (hΘsq : ∀ θ ∈ Θ, θ ^ 2 ∈ (MulAut.conj : X →* MulAut X).range)
    (he : 2 ≤ e) (hm : m = 1) : False := by
  subst hm
  have h2e : 2 ≤ 2 ^ e := by
    have : 1 < 2 ^ e := Nat.one_lt_pow (by omega : e ≠ 0) (by norm_num : 1 < 2)
    omega
  obtain ⟨θ, hθ, hnotinner⟩ := hHnot rfl h2e
  have hθ2 : θ ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := hΘsq θ hθ
  have hpow : θ ^ (2 ^ e / 2) ∈ (MulAut.conj : X →* MulAut X).range := by
    rw [two_pow_div_two_eq (e := e) he, pow_mul]
    exact Subgroup.pow_mem _ hθ2 _
  obtain ⟨x, hx⟩ := hpow
  exact hnotinner x hx.symm

private theorem two_le_m_of_borelFixed {X : Type*} [Group X]
    {Θ : Subgroup (MulAut X)} {e e' m : ℕ}
    (hk : 2 ^ e = 2 ^ e' * m) (he : 2 ≤ e)
    (hHnot : m = 1 → 2 ≤ 2 ^ e →
      ∃ θ ∈ Θ, ∀ x : X, θ ^ (2 ^ e / 2) ≠ MulAut.conj x)
    (hΘsq : ∀ θ ∈ Θ, θ ^ 2 ∈ (MulAut.conj : X →* MulAut X).range) :
    2 ≤ m := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact pow_ne_zero e (by norm_num : (2 : ℕ) ≠ 0) hk
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · exact absurd (by omega : m = 1) (not_one_of_borelFixed hHnot hΘsq he)
  · exact hge

private theorem nontrivial_odd_of_borelFixed {X : Type*} [Group X]
    {m : ℕ} {H : Subgroup X} (hHcard : Nat.card H = 2 ^ m - 1)
    (hm1 : 1 ≤ m) (hm2 : 2 ≤ m) :
    H ≠ ⊥ ∧ Odd (Nat.card H) := by
  constructor
  · intro hbot
    have hcard1 : Nat.card H = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hHcard] at hcard1
    have h4le : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · rw [hHcard]
    exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hm1

private noncomputable def fieldXH (K : Subgroup G) (H Sbar : Subgroup (Bar2 K)) : Subgroup G :=
  (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (H ⊔ Sbar)).map K.subtype

private theorem fieldXH_le_K {K : Subgroup G} {H Sbar : Subgroup (Bar2 K)} :
    fieldXH K H Sbar ≤ K :=
  Subgroup.map_subtype_le
    (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (H ⊔ Sbar))

private theorem fieldXH_le_normalizer_inf {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {H Sbar : Subgroup (Bar2 K)}
    (hSbar : Sbar = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K))
    (hHnorm : H ≤ Subgroup.normalizer (Sbar : Set (Bar2 K))) :
    fieldXH K H Sbar ≤ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) := by
  subst hSbar
  rintro x ⟨xK, hxK, rfl⟩
  exact mem_normalizer_of_bar2_mem inf_le_right
    (bar2_comap_map_subgroupOf (K := K) (S := D.T ⊓ K) (pCoreOf_le_inf_sylow hK hKn))
    ((sup_le hHnorm Subgroup.le_normalizer) (Subgroup.mem_comap.mp hxK))

private theorem fieldXH_le_normalizer_fieldT1 {D : Data G} {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x}
    {H Sbar : Subgroup (Bar2 K)}
    (hSbar : Sbar = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K))
    (hHnorm : H ≤ Subgroup.normalizer (Sbar : Set (Bar2 K)))
    (hHcent : ∀ θ ∈ fieldTheta D K θ₀ hgen, ∀ h ∈ H, θ h * h⁻¹ ∈ Sbar) :
    fieldXH K H Sbar ≤ Subgroup.normalizer (fieldT1 D K θ₀ hgen : Set G) := by
  subst hSbar
  let S : Subgroup G := D.T ⊓ K
  let q : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := Subgroup.map q (S.subgroupOf K)
  have hT1_le_T : fieldT1 D K θ₀ hgen ≤ D.T := fieldT1_le_T
  have hcomap : Subgroup.comap q (Subgroup.map q (S.subgroupOf K)) = S.subgroupOf K :=
    bar2_comap_map_subgroupOf (K := K) (S := S) (pCoreOf_le_inf_sylow hK hKn)
  rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_le]
  intro r hr x hx
  rw [commutatorElement_def]
  obtain ⟨xK, hxK, rfl⟩ := Subgroup.mem_map.mp hx
  have hrT : r ∈ D.T := hT1_le_T hr
  have hrN : r ∈ Subgroup.normalizer (K : Set G) :=
    T_le_normalizer_of_normal hK hKn hrT
  have hcent : ∀ s (hs : s ∈ Subgroup.normalizer (K : Set G)), s ∈ fieldT1 D K θ₀ hgen →
      ∀ h ∈ H, UC6S846.rhoL K ⟨s, hs⟩ h * h⁻¹ ∈ Sbar := by
    intro s hs hsT1 h hh
    exact hHcent _ (Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr hsT1)) h hh
  have hfix : UC6S846.rhoL K ⟨r, hrN⟩ (q xK) * (q xK)⁻¹ ∈ Sbar :=
    rhoL_mul_inv_mem_of_mem_sup (K := K) (S := S) (R := fieldT1 D K θ₀ hgen)
      (H := H) (hRS := hT1_le_T.trans (T_le_normalizer_inf hK hKn))
      hHnorm hcent hrN hr (Subgroup.mem_comap.mp hxK)
  have hcommS : r * ↑xK * r⁻¹ * (↑xK)⁻¹ ∈ S :=
    commutator_mem_of_rhoL (K := K) (S := S) hcomap hrN xK.2 hfix
  exact (inf_le_fieldT1 hK hKn) hcommS

private theorem fieldXH_le_normalizer_Z {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {K : Subgroup G} (hK : K ∈ calC D.M) {H Sbar : Subgroup (Bar2 K)} :
    fieldXH K H Sbar ≤ Subgroup.normalizer (D.Z : Set G) := by
  intro x hx
  have hxK : x ∈ K := fieldXH_le_K hx
  have hKZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c
      (CFSG.Open.IsSubnormal.le hK.1) hK.2.1
  exact Subgroup.centralizer_le_normalizer (D.Z : Set G) (hKZ hxK)

private theorem fieldXH_le_N {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (hPush : Push2329 D Ch) (hOff : OffenderV2329 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : (K.subgroupOf D.M).Normal) {θ₀ : MulAut (Bar2 K)}
    {hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x}
    {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G)) (htT : t ∈ D.T)
    (hθ₀ : UC6S846.rhoL K ⟨t, ht⟩ = θ₀)
    {H Sbar : Subgroup (Bar2 K)}
    (hXH_le_T1 : fieldXH K H Sbar ≤
      Subgroup.normalizer (fieldT1 D K θ₀ hgen : Set G))
    (hXH_le_Z : fieldXH K H Sbar ≤ Subgroup.normalizer (D.Z : Set G)) :
    fieldXH K H Sbar ≤ c.N := by
  have hT1_le_T : fieldT1 D K θ₀ hgen ≤ D.T := fieldT1_le_T
  have hT_norm_T1 : D.T ≤ Subgroup.normalizer (fieldT1 D K θ₀ hgen : Set G) :=
    T_le_normalizer_fieldT1 hK hKn
  have hsup : D.T ≤ fieldT1 D K θ₀ hgen ⊔ Subgroup.zpowers t := by
    refine T_le_sup_zpowers_fieldT1 hK hKn htT ?_
    rw [show (⟨t, T_le_normalizer_of_normal hK hKn htT⟩ :
        ↥(Subgroup.normalizer (K : Set G))) = ⟨t, ht⟩ from Subtype.ext rfl]
    exact hθ₀
  have hJ : InS3.thompsonJ D.T ≤ fieldT1 D K θ₀ hgen :=
    thompsonJ_le_fieldT1 hK hKn
  have hV : c.V ≤ fieldT1 D K θ₀ hgen :=
    ((hOff h1930 c).2.1).trans hJ
  exact hPush h1930 c h3 (fieldT1 D K θ₀ hgen) hT1_le_T hT_norm_T1
    ⟨t, htT, hsup⟩ hV hJ (fieldXH K H Sbar) hXH_le_T1 hXH_le_Z

private theorem bar2_commutator_eq_rhoL_mul_inv {K : Subgroup G} {t x : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) (hx : x ∈ K) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥K)
        ⟨t * x * t⁻¹ * x⁻¹,
          K.mul_mem ((Subgroup.mem_normalizer_iff.mp ht x).mp hx) (K.inv_mem
            hx)⟩ =
      UC6S846.rhoL K ⟨t, ht⟩ (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hx⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hx⟩)⁻¹ := by
  let q : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have htxK : t * x * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp ht x).mp hx
  have hdecomp : (⟨t * x * t⁻¹ * x⁻¹,
      K.mul_mem htxK (K.inv_mem hx)⟩ : ↥K) =
      ⟨t * x * t⁻¹, htxK⟩ * ⟨x, hx⟩⁻¹ := Subtype.ext rfl
  rw [hdecomp, map_mul, map_inv, rhoL_apply_mk]

private theorem commutator_mem_inf_of_mem_fieldXH {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h208 : S20_8 D) (h847 : R847ThinCZ D)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {e : ℕ} (hX : IsL2 (Bar2 K) (2 ^ e)) {t : G} (htT : t ∈ D.T)
    {H Sbar : Subgroup (Bar2 K)} {xK : ↥K}
    (hxK : xK ∈ Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (H ⊔ Sbar))
    (hXH_le_N : fieldXH K H Sbar ≤ c.N)
    (hXH_le_S : fieldXH K H Sbar ≤
      Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G)) :
    t * (K.subtype xK) * t⁻¹ * (K.subtype xK)⁻¹ ∈ D.T ⊓ K := by
  let b : G := K.subtype xK
  have hbK : b ∈ K := xK.2
  have hbXH : b ∈ fieldXH K H Sbar := Subgroup.mem_map_of_mem K.subtype hxK
  have hbN : b ∈ c.N := hXH_le_N hbXH
  have hLN : (c.L.subgroupOf c.N).Normal := Ctx23L.normal_L_N D Ch h4 h23 h208 h1930 c
  have hthin : F08.Thin8 K := thin8_of_isL2_or_isSz (Or.inl hX)
  obtain ⟨i, hi⟩ := Ctx23L.exists_orderOf_conj_mul_inv_eq_two_pow D Ch c h1930
    h4 h23 h847 hLN hK hthin hKn htT hbK hbN
  have htK : t ∈ Subgroup.normalizer (K : Set G) := T_le_normalizer_of_normal hK hKn htT
  have hgK : t * b * t⁻¹ * b⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp htK b).mp hbK) (K.inv_mem hbK)
  have htS : t ∈ Subgroup.normalizer (D.T ⊓ K : Set G) := T_le_normalizer_inf hK hKn htT
  have hbS : b ∈ Subgroup.normalizer (D.T ⊓ K : Set G) := hXH_le_S hbXH
  have hgN : t * b * t⁻¹ * b⁻¹ ∈ Subgroup.normalizer (D.T ⊓ K : Set G) :=
    (Subgroup.normalizer (D.T ⊓ K : Set G)).mul_mem
      ((Subgroup.normalizer (D.T ⊓ K : Set G)).mul_mem
        ((Subgroup.normalizer (D.T ⊓ K : Set G)).mul_mem htS hbS)
        ((Subgroup.normalizer (D.T ⊓ K : Set G)).inv_mem htS))
      ((Subgroup.normalizer (D.T ⊓ K : Set G)).inv_mem hbS)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer (CFSG.Open.IsSubnormal.le hK.1)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.Open.IsSubnormal.le hK.1)).mp hKn)
  exact CFSG.RankThree.PartOne.mem_of_pElement_mem_normalizer hSyl hgK hgN ⟨i, hi⟩

private theorem H_le_Sbar {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    {K : Subgroup G} {t : G} {ht : t ∈ Subgroup.normalizer (K : Set G)}
    {H Sbar : Subgroup (Bar2 K)}
    (hSbar : Sbar = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K))
    (hHnorm : H ≤ Subgroup.normalizer (Sbar : Set (Bar2 K)))
    (hnorm : ∀ y ∈ Subgroup.normalizer (Sbar : Set (Bar2 K)),
      UC6S846.rhoL K ⟨t, ht⟩ y * y⁻¹ ∈ Sbar → y ∈ Sbar)
    (hcomm : ∀ (h : Bar2 K) (xK : ↥K),
      xK ∈ Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (H ⊔ Sbar) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) xK = h →
      t * (K.subtype xK) * t⁻¹ * (K.subtype xK)⁻¹ ∈ D.T ⊓ K) :
    H ≤ Sbar := by
  intro h hh
  obtain ⟨xK, hxq⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) h
  have hxK : xK ∈ Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (H ⊔ Sbar) := by
    rw [Subgroup.mem_comap]
    rw [hxq]
    exact Subgroup.mem_sup_left hh
  have hgS : t * (K.subtype xK) * t⁻¹ * (K.subtype xK)⁻¹ ∈ D.T ⊓ K :=
    hcomm h xK hxK hxq
  have hgK : t * (K.subtype xK) * t⁻¹ * (K.subtype xK)⁻¹ ∈ K :=
    (Subgroup.mem_inf.mp hgS).2
  have hqg : QuotientGroup.mk' (CFSG.pCore 2 ↥K)
      ⟨t * (xK : G) * t⁻¹ * (xK : G)⁻¹, hgK⟩ =
      UC6S846.rhoL K ⟨t, ht⟩ h * h⁻¹ := by
    rw [bar2_commutator_eq_rhoL_mul_inv (K := K) ht xK.2, hxq]
  have hqgS : QuotientGroup.mk' (CFSG.pCore 2 ↥K)
      ⟨t * (xK : G) * t⁻¹ * (xK : G)⁻¹, hgK⟩ ∈ Sbar := by
    rw [hSbar]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr hgS)
  rw [hqg] at hqgS
  exact hnorm h (hHnorm hh) hqgS

private theorem field_data_hnorm {D : Data G} {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) {θ₀ : MulAut (Bar2 K)}
    (hθ₀ : UC6S846.rhoL K ⟨t, ht⟩ = θ₀)
    (Syl : Sylow 2 (Bar2 K)) {Sbar : Subgroup (Bar2 K)}
    (hSyl : (Syl : Set (Bar2 K)) = (Sbar : Set (Bar2 K)))
    (hnorm : ∀ y ∈ Subgroup.normalizer (Syl : Set (Bar2 K)),
      θ₀ y * y⁻¹ ∈ (Syl : Subgroup (Bar2 K)) → y ∈ (Syl : Subgroup (Bar2 K))) :
    ∀ y ∈ Subgroup.normalizer (Sbar : Set (Bar2 K)),
      UC6S846.rhoL K ⟨t, ht⟩ y * y⁻¹ ∈ Sbar → y ∈ Sbar := by
  intro y hy hyS
  have hy' : y ∈ Subgroup.normalizer (Syl : Set (Bar2 K)) := by
    rw [hSyl]
    exact hy
  have hyS' : UC6S846.rhoL K ⟨t, ht⟩ y * y⁻¹ ∈ (Syl : Subgroup (Bar2 K)) := by
    change UC6S846.rhoL K ⟨t, ht⟩ y * y⁻¹ ∈ (Syl : Set (Bar2 K))
    rw [hSyl]
    exact hyS
  have h := hnorm y hy' (by simpa only [hθ₀] using hyS')
  have h' : y ∈ (Syl : Set (Bar2 K)) := h
  rw [hSyl] at h'
  exact h'

private structure FieldGenData (D : Data G) (K : Subgroup G) where
  θ₀ : MulAut (Bar2 K)
  Syl : Sylow 2 (Bar2 K)
  hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
    θ = θ₀ ^ j * MulAut.conj x
  hnorm : ∀ y ∈ Subgroup.normalizer (Syl : Set (Bar2 K)),
    θ₀ y * y⁻¹ ∈ (Syl : Subgroup (Bar2 K)) → y ∈ (Syl : Subgroup (Bar2 K))
  hS : (Syl : Subgroup (Bar2 K)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    ((D.T ⊓ K).subgroupOf K)

private noncomputable def fieldGen_data (D : Data G) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {e : ℕ} (he : 2 ≤ e)
    (hX : IsL2 (Bar2 K) (2 ^ e)) {t : G} (ht : t ∈ Subgroup.normalizer (K : Set G))
    (htT : t ∈ D.T)
    (hnot : ∀ x : Bar2 K,
      (UC6S846.rhoL K ⟨t, ht⟩) ^ (2 ^ (e - 1)) ≠ MulAut.conj x) :
    FieldGenData D K :=
  let θ₀ : MulAut (Bar2 K) := UC6S846.rhoL K ⟨t, ht⟩
  let Syl : Sylow 2 (Bar2 K) := Classical.choose (sylowImage_isSylow hK hKn)
  have hS : (Syl : Subgroup (Bar2 K)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K) := Classical.choose_spec (sylowImage_isSylow hK hKn)
  have hθ₀S : ∀ x ∈ (Syl : Subgroup (Bar2 K)), θ₀ x ∈ (Syl : Subgroup (Bar2 K)) := by
    intro x hx
    exact theta_maps_sylow hK hKn le_rfl hS θ₀
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htT)) x hx
  have hgenhnorm :=
    fieldGen_of_isL2 hX (by omega : 1 ≤ e) Syl (θ₀ := θ₀) hθ₀S hnot
  ⟨θ₀, Syl, hgenhnorm.1, hgenhnorm.2, hS⟩

private theorem borelFixed_2329 (D : Data G) {K : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) {e : ℕ} (he : 2 ≤ e)
    (hX : IsL2 (Bar2 K) (2 ^ e)) {θ₀ : MulAut (Bar2 K)}
    (hgen : ∀ θ : MulAut (Bar2 K), ∃ j : ℕ, ∃ x : Bar2 K,
      θ = θ₀ ^ j * MulAut.conj x)
    (Syl : Sylow 2 (Bar2 K))
    (hS : (Syl : Subgroup (Bar2 K)) = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K)) :
    ∃ (H : Subgroup (Bar2 K)) (m : ℕ),
      Nat.card H = 2 ^ m - 1 ∧ H ≤ Subgroup.normalizer (Syl : Set (Bar2 K)) ∧
      (∀ θ ∈ fieldTheta D K θ₀ hgen, ∀ h ∈ H,
        θ h * h⁻¹ ∈ (Syl : Subgroup (Bar2 K))) ∧
      H ≠ ⊥ ∧ Odd (Nat.card H) := by
  let Θ : Subgroup (MulAut (Bar2 K)) := fieldTheta D K θ₀ hgen
  have hT1_le_T : fieldT1 D K θ₀ hgen ≤ D.T := fieldT1_le_T
  have hΘ : IsPGroup 2 Θ := theta_isPGroup K hT1_le_T
  have hΘS : ∀ θ ∈ Θ, ∀ x ∈ (Syl : Subgroup (Bar2 K)),
      θ x ∈ (Syl : Subgroup (Bar2 K)) := theta_maps_sylow hK hKn hT1_le_T hS
  obtain ⟨e', m, hk, H, -, hHcard, hHnorm, hHcent, hHnot⟩ :=
    exists_borelFixed_of_isL2 hX Θ hΘ Syl hΘS
  have hΘsq : ∀ θ ∈ Θ, θ ^ 2 ∈
      (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
    intro θ hθ
    exact fieldTheta_sq_mem_inn (D := D) (K := K) (θ₀ := θ₀) (hgen := hgen) θ hθ
  have hm2 : 2 ≤ m := two_le_m_of_borelFixed hk he hHnot hΘsq
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hHne, hHodd⟩ := nontrivial_odd_of_borelFixed hHcard hm1 hm2
  exact ⟨H, m, hHcard, hHnorm, hHcent, hHne, hHodd⟩

theorem fieldGen2329_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h208 : S20_8 D) (h847 : R847ThinCZ D)
    (hPush : Push2329 D Ch) (hOff : OffenderV2329 D Ch) : FieldGen2329 D Ch := by
  intro h1930 c h3 K hK hKn e he hX t ht htT
  by_contra hnot
  push Not at hnot
  let data := fieldGen_data D hK hKn he hX ht htT hnot
  obtain ⟨H, m, hHcard, hHnorm, hHcent, hHne, hHodd⟩ :=
    borelFixed_2329 D hK hKn he hX data.hgen data.Syl data.hS
  let S : Subgroup G := D.T ⊓ K
  let q : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let Sbar : Subgroup (Bar2 K) := Subgroup.map q (S.subgroupOf K)
  have hSyl_coe : (data.Syl : Subgroup (Bar2 K)) = Sbar := data.hS
  have hSyl_set : (data.Syl : Set (Bar2 K)) = (Sbar : Set (Bar2 K)) :=
    congrArg (fun S : Subgroup (Bar2 K) => (S : Set (Bar2 K))) hSyl_coe
  have hHnorm' : H ≤ Subgroup.normalizer (Sbar : Set (Bar2 K)) := by
    rwa [← hSyl_coe]
  have hHcent' : ∀ θ ∈ fieldTheta D K data.θ₀ data.hgen, ∀ h ∈ H,
      θ h * h⁻¹ ∈ Sbar := by
    simpa only [hSyl_coe] using hHcent
  have hSbar : Sbar = Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      ((D.T ⊓ K).subgroupOf K) := rfl
  let XH : Subgroup G := fieldXH K H Sbar
  have hXH_le_S : XH ≤ Subgroup.normalizer (S : Set G) :=
    fieldXH_le_normalizer_inf hK hKn hSbar hHnorm'
  have hXH_le_T1 : XH ≤
      Subgroup.normalizer (fieldT1 D K data.θ₀ data.hgen : Set G) :=
    fieldXH_le_normalizer_fieldT1 hK hKn hSbar hHnorm' hHcent'
  have hXH_le_Z : XH ≤ Subgroup.normalizer (D.Z : Set G) :=
    fieldXH_le_normalizer_Z (c := c) h4 h1930 hK
  have hθ₀ : UC6S846.rhoL K ⟨t, ht⟩ = data.θ₀ := by
    simp [data, fieldGen_data]
  have hXH_le_N : XH ≤ c.N :=
    fieldXH_le_N hPush hOff h1930 h3 hK hKn ht htT hθ₀ hXH_le_T1 hXH_le_Z
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hS2 : IsPGroup 2 S := IsPGroup.to_inf_left (p := 2) (H := D.T) (K := K) hT2
  have hSbar2 : IsPGroup 2 Sbar := (hS2.comap_subtype (K := K)).map q
  have hnorm' : ∀ y ∈ Subgroup.normalizer (Sbar : Set (Bar2 K)),
      UC6S846.rhoL K ⟨t, ht⟩ y * y⁻¹ ∈ Sbar → y ∈ Sbar :=
    field_data_hnorm (D := D) (K := K) ht hθ₀ data.Syl hSyl_set data.hnorm
  have hH_le_Sbar : H ≤ Sbar :=
    H_le_Sbar (Ch := Ch) (c := c) hSbar hHnorm' hnorm'
      fun h xK hxK hxq =>
        commutator_mem_inf_of_mem_fieldXH (Ch := Ch) (c := c)
          h1930 h4 h23 h208 h847 hK hKn hX htT hxK hXH_le_N hXH_le_S
  have hHbot : H = ⊥ := by
    have hbot : Sbar ⊓ H = ⊥ :=
      CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hSbar2 hHodd
    rwa [inf_eq_right.mpr hH_le_Sbar] at hbot
  exact hHne hHbot

end CFSG.LocalAnalysis.UniquenessCase.UC22
