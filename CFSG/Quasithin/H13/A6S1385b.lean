module

public import CFSG.Quasithin.H13.A6S1385a
public import CFSG.Quasithin.Background.F918P3
public import CFSG.Quasithin.H13.A6S1372Fourteen
public import CFSG.Quasithin.H13.A6S1384a
public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

namespace A6Tv

section Act

variable {G : Type} [Group G] {V₁ IH H : Subgroup G}

theorem modMk_congr (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {a b : G} (ha : a ∈ IH)
    (hb : b ∈ IH) (h : a = b) : modMk hIHN a ha = modMk hIHN b hb := by
  subst h
  rfl

theorem modMk_eq_one_iff' (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {a : G} (ha : a ∈ IH) :
    modMk hIHN a ha = 1 ↔ a ∈ V₁ := by
  constructor
  · intro h
    have h1 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a, hIHN ha⟩ = 1 :=
      congrArg Subtype.val h
    exact secMk_eq_one_iff.mp h1
  · intro h
    exact Subtype.ext (secMk_eq_one_iff.mpr h)

theorem modMk_eq_modMk_iff' (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {a b : G}
    (ha : a ∈ IH) (hb : b ∈ IH) : modMk hIHN a ha = modMk hIHN b hb ↔ a⁻¹ * b ∈ V₁ := by
  constructor
  · intro h
    have h1 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a, hIHN ha⟩ =
        secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨b, hIHN hb⟩ := congrArg Subtype.val h
    exact secMk_eq_secMk_iff.mp h1
  · intro h
    exact Subtype.ext (secMk_eq_secMk_iff.mpr h)

theorem modMk_conj_eq_iff' (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {x u : G}
    (hu : u ∈ IH) (hxu : x * u * x⁻¹ ∈ IH) :
    modMk hIHN (x * u * x⁻¹) hxu = modMk hIHN u hu ↔ x * u * x⁻¹ * u⁻¹ ∈ V₁ := by
  rw [modMk_eq_modMk_iff' hIHN hxu hu]
  constructor
  · intro h1
    have h2 : u⁻¹ * (x * u * x⁻¹) ∈ V₁ := by
      have := V₁.inv_mem h1
      simpa [mul_assoc] using this
    have h3 : u * (u⁻¹ * (x * u * x⁻¹)) * u⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hIHN hu) _).mp h2
    have e : u * (u⁻¹ * (x * u * x⁻¹)) * u⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
    rwa [e] at h3
  · intro hc
    have h3 : u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * u⁻¹⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hIHN (IH.inv_mem hu)) _).mp (V₁.inv_mem hc)
    have e : (x * u * x⁻¹)⁻¹ * u = u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * u⁻¹⁻¹ := by group
    rw [e]
    exact h3

variable [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]

theorem actH_eq_one_iff (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    (x : ↥H) : actH hV₁ hIH x = 1 ↔ ∀ u ∈ IH, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ V₁ := by
  constructor
  · intro h1 u hu
    have h2 := congrArg (fun φ : MulAut ↥(tildeOf V₁ IH) => φ (modMk hIHN u hu)) h1
    simp only [MulAut.one_apply] at h2
    rw [actH_modMk hV₁ hIHN hIH x hu] at h2
    exact (modMk_conj_eq_iff' hIHN hu _).1 h2
  · intro h1
    refine MulEquiv.ext fun w => ?_
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
    have hw : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    rw [MulAut.one_apply, hw, actH_modMk hV₁ hIHN hIH x haIH]
    exact (modMk_conj_eq_iff' hIHN haIH _).2 (h1 _ haIH)

theorem isTransvection_actH (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    {h : G} (hh : h ∈ H) (htr : InducesTransvMod h IH V₁) :
    IsTransvection (actH hV₁ hIH ⟨h, hh⟩) := by
  obtain ⟨hnot, c, hc⟩ := htr
  push Not at hnot
  obtain ⟨x₀, hx₀, hd⟩ := hnot
  have hconj : ∀ u ∈ IH, h * u * h⁻¹ ∈ IH := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hIH hh) u).mp hu
  have hcomm : ∀ u (hu : u ∈ IH), h * u * h⁻¹ * u⁻¹ ∈ IH := fun u hu =>
    IH.mul_mem (hconj u hu) (IH.inv_mem hu)
  have hmul : ∀ u (hu : u ∈ IH), actH hV₁ hIH ⟨h, hh⟩ (modMk hIHN u hu) =
      modMk hIHN _ (hcomm u hu) * modMk hIHN u hu := by
    intro u hu
    rw [actH_modMk hV₁ hIHN hIH ⟨h, hh⟩ hu, ← modMk_mul hIHN (hcomm u hu) hu]
    exact modMk_congr hIHN _ _ (by group)
  have hdc : h * x₀ * h⁻¹ * x₀⁻¹ * c⁻¹ ∈ V₁ := (hc x₀ hx₀).resolve_left hd
  refine ⟨fun h1 => hd ((actH_eq_one_iff hV₁ hIHN hIH _).1 h1 x₀ hx₀),
    modMk hIHN _ (hcomm x₀ hx₀), fun h1 => hd ((modMk_eq_one_iff' hIHN _).1 h1), fun v => ?_⟩
  obtain ⟨⟨a, haN⟩, haIH, hau⟩ := exists_mk_of_mem_tilde v
  have haIH' : a ∈ IH := haIH
  have hv : v = modMk hIHN a haIH' := Subtype.ext hau.symm
  rw [hv, hmul _ haIH']
  rcases hc a haIH' with h1 | h1
  · left
    rw [(modMk_eq_one_iff' hIHN _).2 h1, one_mul]
  · right
    rw [mul_comm]
    congr 1
    rw [modMk_eq_modMk_iff']
    have hcN : c ∈ Subgroup.normalizer (V₁ : Set G) := by
      have e : c = (h * x₀ * h⁻¹ * x₀⁻¹ * c⁻¹)⁻¹ * (h * x₀ * h⁻¹ * x₀⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer (V₁.inv_mem hdc))
        (hIHN (hcomm x₀ hx₀))
    have h2 : c⁻¹ * ((h * a * h⁻¹ * a⁻¹ * c⁻¹)⁻¹ * (h * x₀ * h⁻¹ * x₀⁻¹ * c⁻¹)) * c⁻¹⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) _).mp
        (V₁.mul_mem (V₁.inv_mem h1) hdc)
    have e : (h * a * h⁻¹ * a⁻¹)⁻¹ * (h * x₀ * h⁻¹ * x₀⁻¹) =
        c⁻¹ * ((h * a * h⁻¹ * a⁻¹ * c⁻¹)⁻¹ * (h * x₀ * h⁻¹ * x₀⁻¹ * c⁻¹)) * c⁻¹⁻¹ := by group
    rw [e]
    exact h2

end Act

theorem isSylowTwoOf_map_range' {G : Type} [Group G] {H T : Subgroup G} {D : Type} [Group D]
    (α : ↥H →* D) (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf ((T.subgroupOf H).map α) α.range := by
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · have h2 : IsPGroup 2 (T.subgroupOf H) := by
      have : IsPGroup 2 ↥T := hT.2.1
      exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    exact h2.of_surjective (α.subgroupMap _) (α.subgroupMap_surjective _)
  · have heq : ((T.subgroupOf H).map α).subgroupOf α.range =
        (T.subgroupOf H).map α.rangeRestrict := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, Subtype.ext hty⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨t, ht, congrArg Subtype.val hty⟩
    rw [heq]
    intro hdvd
    exact hT.2.2 (hdvd.trans (Subgroup.index_map_dvd _ α.rangeRestrict_surjective))

section Range

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem range_o2_eq_bot (hF : HypF91 T V L V₁ Vp H) {M : Type*} [Group M] (φ : ↥H →* M)
    (hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) :
    ∀ Q : Subgroup M, Q ≤ φ.range → (Q.subgroupOf φ.range).Normal → IsPGroup 2 Q → Q = ⊥ := by
  intro Q hQX hQn hQ2
  have hmemD : ∀ x : ↥H, (x : G) ∈ (Q.comap φ).map H.subtype ↔ φ x ∈ Q := fun x => by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this, ← Subgroup.mem_comap]
      exact hy
    · intro hx
      exact ⟨x, Subgroup.mem_comap.2 hx, rfl⟩
  have hDH : (Q.comap φ).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hconj : ∀ x ∈ H, ∀ d ∈ (Q.comap φ).map H.subtype,
      x * d * x⁻¹ ∈ (Q.comap φ).map H.subtype := by
    intro x hx d hd
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hd
    have hy' : φ y ∈ Q := Subgroup.mem_comap.1 hy
    have h1 : φ (⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹) ∈ Q := by
      rw [map_mul, map_mul, map_inv]
      exact hQn.conj_mem ⟨φ y, hQX hy'⟩ hy' ⟨φ ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
    exact (hmemD (⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹)).2 h1
  have hHD : H ≤ Subgroup.normalizer (((Q.comap φ).map H.subtype : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨hconj x hx d, fun hd => ?_⟩
    have h1 := hconj x⁻¹ (H.inv_mem hx) _ hd
    have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
    rwa [e] at h1
  have hD2 : ∀ d ∈ (Q.comap φ).map H.subtype, ∃ k : ℕ, d ^ 2 ^ k ∈
      centralizerMod V₁ H (conjClosure Vp H) := by
    intro d hd
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hd
    obtain ⟨k, hk⟩ := hQ2 ⟨φ y, Subgroup.mem_comap.1 hy⟩
    refine ⟨k, ?_⟩
    have h1 : φ (y ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [← hF.pCoreOf_eq_centralizerMod]
    exact (hker _).1 h1
  have hle := hF.F92_1_reduced hDH hHD hD2
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨y, rfl⟩ := hQX hq
  have h1 := hle ((hmemD y).2 hq)
  rw [← hF.pCoreOf_eq_centralizerMod] at h1
  exact Subgroup.mem_bot.2 ((hker y).2 h1)

theorem pRank_range_le_two (hF : HypF91 T V L V₁ Vp H) (hK : quasithinIsQTKECat G)
    {M : Type*} [Group M] [Finite M] (φ : ↥H →* M)
    (hker : ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) : CFSG.Open.pRank 3 φ.range ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQne : pCoreOf 2 H ≠ ⊥ := fun h0 =>
    hF.V₁_ne_bot (le_bot_iff.1 (h0 ▸ hF.V₁_le_pCoreOf))
  have hkerEq : φ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker x
  let e : ↥φ.range ≃* ↥H ⧸ (pCoreOf 2 H).subgroupOf H :=
    (QuotientGroup.quotientKerEquivRange φ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerEq)
  have hN : ¬ 3 ∣ Nat.card ↥((pCoreOf 2 H).subgroupOf H) := by
    have hp : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf H) :=
      (pCoreOf_isPGroup 2 H).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).symm
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  rw [← pRank_top_subtype φ.range, CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
    CFSG.SectionRank.pRank_quotient_eq _ hN, pRank_top_subtype]
  exact pRank_le_two_of_pCoreOf_ne_bot hK hQne Nat.prime_three (by norm_num)

end Range

end A6Tv

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem no_transv_of_solvable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hsol : Group.IsSolvable ↥H) :
    ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V) := by
  intro h hh htr
  have hF := (hS.hF H hH).toHypF91
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF.isElemAbelian_tilde⟩
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hV1V3 : fsuV1 T V ≤ S.V3 := hF.V₁_le_Vp
  have hV3U : S.V3 ≤ conjClosure S.V3 H := le_conjClosure S.V3 H
  have hker : ∀ x : ↥H, actH hV₁ hIH x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hsolX : Group.IsSolvable ↥(actH hV₁ hIH).range :=
    Group.isSolvable_of_surjective (f := (actH hV₁ hIH).rangeRestrict)
      (actH hV₁ hIH).rangeRestrict_surjective
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_c012
  obtain ⟨e, m, hm3, hmo⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3
    (by norm_num)
  have hc₀L1 : ((g ^ (m ^ 2) : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.L1 := by
    rw [Subgroup.coe_pow]
    exact S.L1.pow_mem hgL1 _
  have hc₀H : ((g ^ (m ^ 2) : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ H :=
    hF.L₁T_le_H (Subgroup.mem_sup_left hc₀L1)
  have hρc₀ : S.frame.ρ (g ^ (m ^ 2)) = swap 0 1 * swap 1 2 := by
    have hm2 : m ^ 2 % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rw [Nat.pow_mod]
      rcases this with h | h <;> simp [h]
    rw [map_pow, hg, ← Nat.div_add_mod (m ^ 2) 3, hm2, pow_add, pow_mul, c012_facts.2.2,
      one_pow, one_mul, pow_one]
  have hc₀e : (⟨_, hc₀H⟩ : ↥H) ^ 3 ^ e = 1 := by
    have : (g ^ (m ^ 2)) ^ 3 ^ e = 1 := by
      rw [← pow_mul, show m ^ 2 * 3 ^ e = 3 ^ e * m * m by ring, pow_mul, ← hmo,
        pow_orderOf_eq_one, one_pow]
    apply Subtype.ext
    simpa using congrArg Subtype.val this
  have hcn : (actH hV₁ hIH ⟨_, hc₀H⟩) ^ 3 ^ e = 1 := by rw [← map_pow, hc₀e, map_one]
  have hcW : ∀ w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3,
      actH hV₁ hIH ⟨_, hc₀H⟩ w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 := by
    have hst := (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hV1V3 hV3U ⟨_, hc₀H⟩).2
      (hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hc₀L1))
    exact fun w hw => (hst w).2 hw
  have hfix : ∀ w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3,
      actH hV₁ hIH ⟨_, hc₀H⟩ w = w → w = 1 := by
    intro w hw hcw
    obtain ⟨⟨a, haN⟩, haU, hau⟩ := exists_mk_of_mem_tilde w
    have haU' : a ∈ conjClosure S.V3 H := haU
    have hwa : w = modMk hIHN a haU' := Subtype.ext hau.symm
    have haV3 : a ∈ S.V3 := by
      rw [← modMk_mem_subM_iff hIHN hV1V3 haU', ← hwa]
      exact hw
    rw [hwa, actH_modMk hV₁ hIHN hIH ⟨_, hc₀H⟩ haU'] at hcw
    have hcomm := (A6Tv.modMk_conj_eq_iff' hIHN haU' _).1 hcw
    rw [hwa]
    exact (A6Tv.modMk_eq_one_iff' hIHN haU').2 (mem_V1_of_c012 hρc₀ haV3 hcomm)
  have hTW : ∀ s ∈ (T.subgroupOf H).map (actH hV₁ hIH),
      ∀ w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3,
        s w ∈ subM (fsuV1 T V) (conjClosure S.V3 H) S.V3 := by
    intro s hs w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hs
    have hst := (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hV1V3 hV3U x).2
      (hF.L₁T_normalizes_Vp (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx)))
    exact (hst w).2 hw
  have hgen := iSup_actH_subM_eq_top hV₁ hIHN hIH hV1V3
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at hgen
  have hW4 : Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) S.V3) = 4 := by
    have h1 : Nat.card ↥(subM (fsuV1 T V) (conjClosure S.V3 H) S.V3) =
        Nat.card ↥(tildeOf (fsuV1 T V) S.V3) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (secImg_mono hV3U)).toEquiv
    have h2 := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V) (T := fsuV1 T V) (H := S.V3) le_rfl hV1V3 (hV3U.trans hIHN)
    rw [show secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ from
      tildeOf_eq_bot_of_le le_rfl, Subgroup.relIndex_bot_left] at h2
    have h3 := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := S.V3)
    rw [inf_of_le_left hV1V3, S.card_V3, hF.card_V₁] at h3
    rw [h1]
    change Nat.card ↥(secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) S.V3) = 4
    rw [h2]
    omega
  have hWtop := A6Tv.eq_top_of_transvection (fun v => Subtype.ext (hF.isElemAbelian_tilde.2 v v.2))
    hsolX (A6Tv.range_o2_eq_bot hF _ hker) (A6Tv.pRank_range_le_two hF S.h13.qtke _ hker)
    (A6Tv.isSylowTwoOf_map_range' _ hF.sylow_H) ⟨⟨h, hh⟩, rfl⟩
    (A6Tv.isTransvection_actH hV₁ hIHN hIH hh htr) hW4 ⟨⟨_, hc₀H⟩, rfl⟩ hcn hcW hfix hTW hgen
  have hHN : ∀ x ∈ H, x ∈ Subgroup.normalizer (S.V3 : Set G) := by
    intro x hx
    refine (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hV1V3 hV3U ⟨x, hx⟩).1 fun u => ?_
    rw [hWtop]
    exact ⟨fun _ => Subgroup.mem_top u, fun _ => Subgroup.mem_top _⟩
  exact hH.2.2 fun x hx => S.NV_le_M (hF.normalizer_le ⟨hx, hHN x hx⟩)

end Setting4

end CFSG.Quasithin.H13.A6

