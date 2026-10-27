module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Star
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Grp

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem nk_fork_inner {Q : Type} [Group Q] (Ks Vs Ms : Subgroup Q) [hKn : Ks.Normal]
    (hVsq : ∀ a ∈ Vs, a * a = 1) (hVne : Vs ≠ ⊥)
    (hMV : Ms ≤ Subgroup.normalizer (Vs : Set Q))
    (hcent : ∀ y : Q, (∀ x ∈ Ks, y * x = x * y) → y = 1)
    (hOut : UOut ↥Ks (Ms.subgroupOf Ks)) : ∃ a ∈ Vs, a ∈ Ks ∧ a ≠ 1 := by
  by_contra hI
  push Not at hI
  obtain ⟨a₀, ha₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hVne)
  set a : Q := (a₀ : Q) with ha_def
  have haV : a ∈ Vs := a₀.2
  have ha1 : a ≠ 1 := fun h => ha₀ (Subtype.ext h)
  have haK : a ∉ Ks := fun h => ha1 (hI a haV h)
  set y : MulAut ↥Ks := MulAut.conjNormal a with hy
  have hyy : y * y = 1 := by
    rw [hy, ← map_mul, hVsq a haV, map_one]
  have hfix : ∀ b ∈ Ms.subgroupOf Ks, y b = b := by
    intro b hb
    have hbM : (b : Q) ∈ Ms := Subgroup.mem_subgroupOf.mp hb
    have hbK : (b : Q) ∈ Ks := b.2
    have c1 : a * (b : Q) * a⁻¹ * (b : Q)⁻¹ ∈ Ks :=
      Ks.mul_mem (hKn.conj_mem _ hbK a) (Ks.inv_mem hbK)
    have c2 : a * (b : Q) * a⁻¹ * (b : Q)⁻¹ ∈ Vs := by
      have h1 : (b : Q) * a⁻¹ * (b : Q)⁻¹ ∈ Vs :=
        (Subgroup.mem_normalizer_iff.mp (hMV hbM) a⁻¹).mp (Vs.inv_mem haV)
      have e : a * (b : Q) * a⁻¹ * (b : Q)⁻¹ = a * ((b : Q) * a⁻¹ * (b : Q)⁻¹) := by group
      rw [e]
      exact Vs.mul_mem haV h1
    have h3 := hI _ c2 c1
    have h4 : a * (b : Q) * a⁻¹ = (b : Q) := by
      have := mul_inv_eq_one.mp h3
      exact this
    apply Subtype.ext
    rw [hy, MulAut.conjNormal_apply]
    exact h4
  obtain ⟨x, hx⟩ := hOut y hyy hfix
  have hcx : ∀ c ∈ Ks, ((x : Q)⁻¹ * a) * c = c * ((x : Q)⁻¹ * a) := by
    intro c hc
    have h1 := congrArg (fun m : MulAut ↥Ks => ((m ⟨c, hc⟩ : ↥Ks) : Q)) hx
    simp only [hy, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc (x : Q)⁻¹ * a * c = (x : Q)⁻¹ * (a * c * a⁻¹) * a := by group
      _ = (x : Q)⁻¹ * ((x : Q) * c * (x : Q)⁻¹) * a := by rw [h1]
      _ = c * ((x : Q)⁻¹ * a) := by group
  have h5 := hcent _ hcx
  apply haK
  have : a = (x : Q) := by
    have h6 : (x : Q)⁻¹ * a = 1 := h5
    calc a = (x : Q) * ((x : Q)⁻¹ * a) := by group
      _ = x := by rw [h6, mul_one]
  rw [this]
  exact x.2

theorem nk_fork_contra {Q : Type} [Group Q] (Ks Vs Ms : Subgroup Q) [hKn : Ks.Normal]
    (hVsq : ∀ a ∈ Vs, a * a = 1) (hVne : Vs ≠ ⊥)
    (hMV : Ms ≤ Subgroup.normalizer (Vs : Set Q))
    (hcent : ∀ y : Q, (∀ x ∈ Ks, y * x = x * y) → y = 1)
    (hstar : ∀ a ∈ Vs, ∀ b ∈ Ks, (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 ∨ (a * b * a⁻¹ * b⁻¹) ^ 4 = 1 ∨
      (a * b * a⁻¹ * b⁻¹) ^ 5 = 1)
    (hIn : UIn ↥Ks) (hOut : UOut ↥Ks (Ms.subgroupOf Ks)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haV, haK, ha1⟩ := nk_fork_inner Ks Vs Ms hVsq hVne hMV hcent hOut
  obtain ⟨hconj, z, g, hz, hzg⟩ := hIn
  set ak : ↥Ks := ⟨a, haK⟩ with hak
  have hak2 : ak * ak = 1 := Subtype.ext (hVsq a haV)
  have hak1 : ak ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hord : orderOf ak = 2 := orderOf_eq_prime (by rw [pow_two]; exact hak2) hak1
  obtain ⟨u, hu⟩ := isConj_iff.mp (hconj z ak hz hord)
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz, pow_two] at this
    exact this
  have hainv : ak⁻¹ = ak := inv_eq_of_mul_eq_one_right hak2
  set b : ↥Ks := u * g⁻¹ * u⁻¹ with hb
  have hcomm : ak * b * ak⁻¹ * b⁻¹ = u * (z * (g⁻¹ * z * g)) * u⁻¹ := by
    rw [hainv, hb]
    rw [← hu]
    group
  have hbound : (ak * b * ak⁻¹ * b⁻¹) ^ 3 = 1 ∨ (ak * b * ak⁻¹ * b⁻¹) ^ 4 = 1 ∨
      (ak * b * ak⁻¹ * b⁻¹) ^ 5 = 1 := by
    have key := hstar a haV (b : Q) b.2
    have e : ∀ m : ℕ, ((ak * b * ak⁻¹ * b⁻¹) ^ m : ↥Ks) = 1 ↔
        (a * (b : Q) * a⁻¹ * (b : Q)⁻¹) ^ m = 1 := by
      intro m
      rw [← Subtype.coe_inj]
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, hak]
    rw [e 3, e 4, e 5]
    exact key
  have hle : orderOf (ak * b * ak⁻¹ * b⁻¹) ≤ 5 := by
    rcases hbound with h | h | h
    · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)
    · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)
    · exact orderOf_le_of_pow_eq_one (by norm_num) h
  have hge : 6 ≤ orderOf (ak * b * ak⁻¹ * b⁻¹) := by
    rw [hcomm]
    have := orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective
      (z * (g⁻¹ * z * g))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this]
    exact hzg
  omega

theorem center_eq_bot_of_simple_nonab {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hna : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem nk_fork_star_data {G : Type} [Group G] [Finite G] {H T M K V : Subgroup G}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hs : IsSimpleGroup ↥(E2.star (H ⊓ M) H K))
    (hna : ∃ a b : ↥(E2.star (H ⊓ M) H K), a * b ≠ b * a)
    (hVH : V ≤ H) (hVe : IsElemAbelian 2 V) (hVJ : ¬ V ≤ kerIn (H ⊓ M) H)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G)) :
    (∀ a ∈ E2.star (H ⊓ M) H V, a * a = 1) ∧ E2.star (H ⊓ M) H V ≠ ⊥ ∧
      E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) ≤
        Subgroup.normalizer ((E2.star (H ⊓ M) H V : Subgroup (E2.StarQuot (H ⊓ M) H)) :
          Set (E2.StarQuot (H ⊓ M) H)) ∧
      ∀ y : E2.StarQuot (H ⊓ M) H, (∀ x ∈ E2.star (H ⊓ M) H K, y * x = x * y) → y = 1 := by
  haveI hKn : (E2.star (H ⊓ M) H K).Normal := star_normal_cs5 hHK hTK
  have hVs : IsElemAbelian 2 (E2.star (H ⊓ M) H V) := isElemAbelian_star_cs5 hVH hVe
  refine ⟨fun a ha => ?_, ?_, ?_, ?_⟩
  · have := hVs.2 a ha
    rwa [pow_two] at this
  · intro hbot
    apply hVJ
    intro v hv
    have h1 : (QuotientGroup.mk (⟨v, hVH hv⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
        E2.star (H ⊓ M) H V := mem_star_cs5.mpr ⟨⟨v, hVH hv⟩, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · exact star_le_normalizer_star_cs5 (inf_le_left.trans inf_le_left) hVH (inf_le_left.trans hP7)
  · have hYX : IsPGroup 2 (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) :=
      isPGroup_starQuot_quotient_cs5 hT.2.1 hHK hTK
    have hO2 : ∀ N : Subgroup (E2.StarQuot (H ⊓ M) H), N.Normal → IsPGroup 2 N → N = ⊥ :=
      fun N hN hN2 => by
        haveI := hN
        exact normal_twoGroup_starQuot_eq_bot_cs5 hT hTM N hN2
    exact eq_one_of_centralizes_normal_cs5 (center_eq_bot_of_simple_nonab hs hna) hYX hO2

theorem nk_fork_star {G : Type} [Group G] [Finite G] {H T M K V : Subgroup G}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hs : IsSimpleGroup ↥(E2.star (H ⊓ M) H K))
    (hna : ∃ a b : ↥(E2.star (H ⊓ M) H K), a * b ≠ b * a)
    (hVH : V ≤ H) (hVe : IsElemAbelian 2 V) (hVJ : ¬ V ≤ kerIn (H ⊓ M) H)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G))
    (hstar : ∀ a ∈ E2.star (H ⊓ M) H V, ∀ b ∈ E2.star (H ⊓ M) H K,
      (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 ∨ (a * b * a⁻¹ * b⁻¹) ^ 4 = 1 ∨ (a * b * a⁻¹ * b⁻¹) ^ 5 = 1)
    (hIn : UIn ↥(E2.star (H ⊓ M) H K))
    (hOut : UOut ↥(E2.star (H ⊓ M) H K)
      ((E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)).subgroupOf (E2.star (H ⊓ M) H K))) : False := by
  haveI hKn : (E2.star (H ⊓ M) H K).Normal := star_normal_cs5 hHK hTK
  obtain ⟨hVsq, hVne, hMV, hcent⟩ := nk_fork_star_data hT hTM hHK hTK hs hna hVH hVe hVJ hP7
  exact nk_fork_contra (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H V)
    (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) hVsq hVne hMV hcent hstar hIn hOut

theorem nk_fork_inner_star {G : Type} [Group G] [Finite G] {H T M K V : Subgroup G}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hs : IsSimpleGroup ↥(E2.star (H ⊓ M) H K))
    (hna : ∃ a b : ↥(E2.star (H ⊓ M) H K), a * b ≠ b * a)
    (hVH : V ≤ H) (hVe : IsElemAbelian 2 V) (hVJ : ¬ V ≤ kerIn (H ⊓ M) H)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G))
    (hOut : UOut ↥(E2.star (H ⊓ M) H K)
      ((E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)).subgroupOf (E2.star (H ⊓ M) H K))) :
    ∃ a ∈ E2.star (H ⊓ M) H V, a ∈ E2.star (H ⊓ M) H K ∧ a ≠ 1 := by
  haveI hKn : (E2.star (H ⊓ M) H K).Normal := star_normal_cs5 hHK hTK
  obtain ⟨hVsq, hVne, hMV, hcent⟩ := nk_fork_star_data hT hTM hHK hTK hs hna hVH hVe hVJ hP7
  exact nk_fork_inner (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H V)
    (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)) hVsq hVne hMV hcent hOut

end CFSG.Quasithin.H13.L829NK
