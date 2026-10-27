module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNa
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Br

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H13

private theorem isPGroup_quot_congr_dih {Y : Type} [Group Y] {A B N : Subgroup Y} (hAB : A = B)
    [(N.subgroupOf A).Normal] [(N.subgroupOf B).Normal]
    (h : IsPGroup 2 (↥A ⧸ N.subgroupOf A)) : IsPGroup 2 (↥B ⧸ N.subgroupOf B) := by
  subst hAB
  exact h

private theorem card_quot_congr_dih {Y : Type} [Group Y] {A B N : Subgroup Y} (hAB : A = B) :
    Nat.card (↥A ⧸ N.subgroupOf A) = Nat.card (↥B ⧸ N.subgroupOf B) := by
  subst hAB
  rfl

private theorem isPGroup_starQuot_of_isPGroup_star_dih {G : Type} [Group G] {H M I : Subgroup G}
    (hIH : I ≤ H) (hker : CFSG.Quasithin.kerIn (M ⊓ I) I = pCoreOf 2 I)
    [((E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I)).Normal]
    (hQ : IsPGroup 2 (↥(E2.star (H ⊓ M) H I) ⧸
      (E2.star (H ⊓ M) H (pCoreOf 2 I)).subgroupOf (E2.star (H ⊓ M) H I))) :
    IsPGroup 2 (E2.StarQuot (M ⊓ I) I) := by
  have hIJ : I ⊓ CFSG.Quasithin.kerIn (H ⊓ M) H ≤ pCoreOf 2 I := by
    rw [← hker]
    intro x hx
    rw [CFSG.Quasithin.mem_kerIn]
    intro b hb
    have h1 : b * x * b⁻¹ ∈ CFSG.Quasithin.kerIn (H ⊓ M) H :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.Quasithin.le_normalizer_kerIn (H ⊓ M) H (hIH hb)) x).mp hx.2
    exact ⟨(CFSG.Quasithin.kerIn_le h1).2, I.mul_mem (I.mul_mem hb hx.1) (I.inv_mem hb)⟩
  have hel : ∀ x : ↥I, ∃ k : ℕ, (x : G) ^ 2 ^ k ∈ pCoreOf 2 I := by
    intro x
    have hu : (QuotientGroup.mk (⟨(x : G), hIH x.2⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
        E2.star (H ⊓ M) H I :=
      mem_star_cs5.mpr ⟨⟨(x : G), hIH x.2⟩, x.2, rfl⟩
    obtain ⟨k, hk⟩ := hQ (QuotientGroup.mk (⟨_, hu⟩ : ↥(E2.star (H ⊓ M) H I)))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at hk
    have hk' : (QuotientGroup.mk ((⟨(x : G), hIH x.2⟩ : ↥H) ^ 2 ^ k) :
        E2.StarQuot (H ⊓ M) H) ∈ E2.star (H ⊓ M) H (pCoreOf 2 I) := by
      rw [QuotientGroup.mk_pow]
      exact hk
    obtain ⟨a, ha, hax⟩ := mem_star_cs5.mp hk'
    have hJ : (a : G)⁻¹ * (x : G) ^ 2 ^ k ∈ CFSG.Quasithin.kerIn (H ⊓ M) H :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hax)
    have haI : (a : G) ∈ I := CFSG.LieType.BorelTits.pCoreOf_le 2 I ha
    have hz : (a : G)⁻¹ * (x : G) ^ 2 ^ k ∈ pCoreOf 2 I :=
      hIJ (Subgroup.mem_inf.mpr ⟨I.mul_mem (I.inv_mem haI) (I.pow_mem x.2 _), hJ⟩)
    refine ⟨k, ?_⟩
    have h2 := (pCoreOf 2 I).mul_mem ha hz
    rwa [mul_inv_cancel_left] at h2
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ := hel x
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow, hker]
  exact hk

theorem l2_branch_dih {G : Type} [Group G] [Finite G] {H T M K V : Subgroup G} {h : G} {n : ℕ}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hVT : V ≤ T) (hVe : IsElemAbelian 2 V)
    (hVJ : ¬ V ≤ kerIn (H ⊓ M) H)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G)) (hh : h ∈ H)
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hD : ∃ m : ℕ, (m = 3 ∨ m = 5) ∧
      Nonempty (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h) ≃* DihedralGroup m))
    (hn : 2 ≤ n) (hKs : IsPSL 2 2 n ↥(E2.star (H ⊓ M) H K))
    (hBor : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) : False := by
  have hTH : T ≤ H := hT.1
  have hVH : V ≤ H := hVT.trans hTH
  have hIH : ch82I V h ≤ H := ch82I_le_829 hVH hh
  have hT2 : IsPGroup 2 T := hT.2.1
  haveI hXn : (E2.star (H ⊓ M) H K).Normal := star_normal_cs5 hHK hTK
  have hYX : IsPGroup 2 (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) :=
    isPGroup_starQuot_quotient_cs5 hT2 hHK hTK
  have hO2 : ∀ N : Subgroup (E2.StarQuot (H ⊓ M) H), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hN hN2 => by
      haveI := hN
      exact normal_twoGroup_starQuot_eq_bot_cs5 hT hTM N hN2
  have hC := eq_one_of_centralizes_normal_cs5 (center_eq_bot_of_isPSL_cs5 hn hKs) hYX hO2
  obtain ⟨S, hS, hB⟩ := hBor
  have hR := rankOneSyl_of_isPSL_two_cs5 hn hKs hS
  have hBsol : Group.IsSolvable ↥(E2.star (H ⊓ M) H K ⊓
      Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H))) := by
    have := C41Pf.isSolvable_of_isBorelIn
      (X := E2.star (H ⊓ M) H K) (B := E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) ⟨S, hS, hB⟩
    rwa [hB] at this
  obtain ⟨hZ', hC'⟩ := rankOne_L2_extra hn hKs ((isSylowTwoOf_top_iff_cs5 hS.1).mpr hS)
  have hSab : centerSub S = S := by
    rw [← centerSub_subgroupOf_cs5 hS.1, hZ', Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hS.1]
  have hCS : ∀ x ∈ E2.star (H ⊓ M) H K, (∀ s ∈ S, x * s = s * x) → x ∈ S := by
    intro x hx hc
    have h1 := hC' ⟨x, hx⟩ (fun s hs =>
      Subtype.ext (hc (s : E2.StarQuot (H ⊓ M) H) (Subgroup.mem_subgroupOf.mp hs)))
    exact Subgroup.mem_subgroupOf.mp h1
  set E := E2.star (H ⊓ M) H V
  have hE : IsElemAbelian 2 E := isElemAbelian_star_cs5 hVH hVe
  have hE1 : E ≠ ⊥ := by
    intro hbot
    apply hVJ
    intro v hv
    have h1 : (QuotientGroup.mk (⟨v, hVH hv⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈ E :=
      mem_star_cs5.mpr ⟨⟨v, hVH hv⟩, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hEB : E2.star (H ⊓ M) H K ⊓ Subgroup.normalizer (S : Set (E2.StarQuot (H ⊓ M) H)) ≤
      Subgroup.normalizer (E : Set (E2.StarQuot (H ⊓ M) H)) := by
    rw [← hB]
    exact star_le_normalizer_star_cs5 (inf_le_left.trans inf_le_left) hVH
      (inf_le_left.trans hP7)
  have hIstar : E2.star (H ⊓ M) H (ch82I V h) =
      E ⊔ B6.conjSub (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) E := by
    unfold ch82I
    obtain ⟨hconjH, hconj⟩ := star_conjSub_cs5 (M := H ⊓ M) hh hVH
    rw [star_sup_cs5 hVH hconjH, hconj]
  have hNnorm : ∀ i ∈ E2.star (H ⊓ M) H (ch82I V h),
      ∀ j ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)),
        i * j * i⁻¹ ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)) := by
    intro i hi j hj
    obtain ⟨a, ha, rfl⟩ := mem_star_cs5.mp hi
    obtain ⟨p, hp, rfl⟩ := mem_star_cs5.mp hj
    refine mem_star_cs5.mpr ⟨a * p * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ch82I V h) ha) (p : G)).mp hp
    · simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hN2 : IsPGroup 2 (E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h))) :=
    isPGroup_star_cs5 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hNnorm' : ∀ i ∈ E ⊔ B6.conjSub (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) E,
      ∀ j ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)),
        i * j * i⁻¹ ∈ E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)) := by
    intro i hi
    rw [← hIstar] at hi
    exact hNnorm i hi
  haveI hNI : ((E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h))).subgroupOf
      (E2.star (H ⊓ M) H (ch82I V h))).Normal :=
    ⟨fun j hj g => Subgroup.mem_subgroupOf.mpr
      (hNnorm (g : E2.StarQuot (H ⊓ M) H) g.2 (j : E2.StarQuot (H ⊓ M) H)
        (Subgroup.mem_subgroupOf.mp hj))⟩
  haveI hNI' : ((E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h))).subgroupOf
      (E ⊔ B6.conjSub (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) E)).Normal :=
    ⟨fun j hj g => Subgroup.mem_subgroupOf.mpr
      (hNnorm' (g : E2.StarQuot (H ⊓ M) H) g.2 (j : E2.StarQuot (H ⊓ M) H)
        (Subgroup.mem_subgroupOf.mp hj))⟩
  obtain ⟨m', hm', ⟨eD⟩⟩ := hD
  have hPcard : Nat.card (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) = 2 * m' := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hP10 : Nat.card (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h)) ≤ 10 := by
    rw [hPcard]
    rcases hm' with rfl | rfl <;> norm_num
  have hmI := (card_star_quot_le_cs5 (H := H) (M := M) hIH hker).trans hP10
  have hm : Nat.card (↥(E ⊔ B6.conjSub (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) E) ⧸
      (E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h))).subgroupOf
        (E ⊔ B6.conjSub (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) E)) ≤ 10 :=
    (card_quot_congr_dih (N := E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h))) hIstar.symm).trans_le
      hmI
  have h4 : 4 ≤ 2 ^ n := calc
    (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmq : 10 < 2 ^ n * 2 ^ n :=
    lt_of_lt_of_le (by norm_num : (10 : ℕ) < 4 * 4) (Nat.mul_le_mul h4 h4)
  refine rk1_dih (h := (QuotientGroup.mk (⟨h, hh⟩ : ↥H) : E2.StarQuot (H ⊓ M) H)) hR hC hYX
    hBsol hSab hCS hE hE1 hEB hNnorm' hN2 hm hmq ?_
  intro hQ
  have hQ' := isPGroup_quot_congr_dih (N := E2.star (H ⊓ M) H (pCoreOf 2 (ch82I V h)))
    hIstar.symm hQ
  have hP2 := isPGroup_starQuot_of_isPGroup_star_dih hIH hker hQ'
  have hdih : IsPGroup 2 (DihedralGroup m') := hP2.of_equiv eD
  obtain ⟨k, hk⟩ := hdih (DihedralGroup.r 1)
  have hdvd : m' ∣ 2 ^ k := by
    have := orderOf_dvd_of_pow_eq_one hk
    rwa [DihedralGroup.orderOf_r_one] at this
  have hcop : Nat.Coprime m' 2 := by
    rcases hm' with rfl | rfl <;> norm_num
  have h1 : m' = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
  rcases hm' with rfl | rfl <;> omega

end CFSG.Quasithin.H13.L829N
