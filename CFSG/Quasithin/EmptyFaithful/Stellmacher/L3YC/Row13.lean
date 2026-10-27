module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row13Common
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row13M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D CFSG.Blueprint
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

namespace Row13

section M23Data

variable {X : Type} [Group X]

theorem card_of_equiv_M23
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .M23)) : Nat.card X = 2 ^ 7 * 79695 := by
  obtain ⟨e⟩ := hX
  have e' : X ≃* NativeSporadic.M23 := e
  rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  norm_num

theorem center_trivial_M23
    {K : Type} [Group K] {N : Subgroup K} (hN : Nonempty (↥N ≃* NativeSporadic.Carrier .M23)) :
    ∀ z ∈ N, (∀ a ∈ N, z * a = a * z) → z = 1 := by
  obtain ⟨e⟩ := hN
  have e' : ↥N ≃* NativeSporadic.M23 := e
  intro z hz hzc
  have hc : e' ⟨z, hz⟩ ∈ Subgroup.center NativeSporadic.M23 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e' (Subtype.ext (hzc a a.2).symm)
  rw [CFSG.Sporadic.Schreier.m23_center_eq_bot', Subgroup.mem_bot] at hc
  have := e'.injective (hc.trans (map_one e').symm)
  exact congrArg Subtype.val this

end M23Data


variable {G : Type} [Group G] [Finite G]

theorem row13_false_of_rank
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀)
    {H : Subgroup G} (hH : H = Subgroup.centralizer ({c₀} : Set G))
    (hSyl : IsSylowTwoOf (Sgp153 T V₁) H) {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal) (hrk : CFSG.Open.pRank 3 H ≤ 2)
    (hrow : (IsExt ↥(modO2Image H L) (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 3 2 1 Y') ∨
        IsExt ↥(modO2Image H L) (fun V _ => IsE2 3 V) (fun Y' _ => IsPSL 3 2 1 Y')) ∧
      IsSporadic .M23 ↥(modO2Image H L₁)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, x, s₁, s₂, hyY, hy3, hxL, hx3, hxy, hxu, hxn, hs₁S, hs₂S, h2₁, h2₂, hs₁y, hs₁x, hs₂x,
      hs₂y, heYL, heL, he3, hx₂3, hcomm, hx₂c, hx₂nL, hs₁'S, -, hs₁'y, hs₁'x, -, -⟩ :=
    exists_e_x2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc hc₀1 hu₀ hu₀1
      hu₀S hsw
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ H := by
    rw [hH]
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  have hSH : Sgp153 T V₁ ≤ H := hSyl.1
  have heH : t'⁻¹ * y * t' ∈ H := hLH heL
  have hs₁'H : t'⁻¹ * s₁ * t' ∈ H := hSH hs₁'S
  have hx₂H : t'⁻¹ * x * t' ∈ H := by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    have := hx₂c
    calc (t'⁻¹ * x * t') * c₀ = ((t'⁻¹ * x * t') * c₀ * (t'⁻¹ * x * t')⁻¹) * (t'⁻¹ * x * t') := by
          group
      _ = c₀ * (t'⁻¹ * x * t') := by rw [hx₂c]
  let mk : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L₁ with hNdef
  set Lb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L with hLbdef
  have hNn : N.Normal := Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLbN : Lb ≤ N := Subgroup.map_mono fun _ hx => hLL₁ hx
  have hN' : Nonempty (↥N ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) := hrow.2
  obtain ⟨eN⟩ := hN'
  have eN' : ↥N ≃* NativeSporadic.M23 := eN
  have heb : mk ⟨t'⁻¹ * y * t', heH⟩ ∈ Lb := ⟨⟨t'⁻¹ * y * t', heH⟩, heL, rfl⟩
  have he3b := Row18.orderOf_mk_eq_three heH he3
  have hx3b := Row18.orderOf_mk_eq_three hx₂H hx₂3
  have hcommb : mk ⟨t'⁻¹ * y * t', heH⟩ * mk ⟨t'⁻¹ * x * t', hx₂H⟩ =
      mk ⟨t'⁻¹ * x * t', hx₂H⟩ * mk ⟨t'⁻¹ * y * t', heH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext hcomm)
  have hxbL : mk ⟨t'⁻¹ * x * t', hx₂H⟩ ∉ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    fun h => hx₂nL (mem_normalizer_of_mk_mem hSyl hSL hperf hLH hx₂H h)
  have hZ := center_trivial_M23 ⟨eN⟩
  have hinn : ∀ g : ↥H ⧸ CFSG.pCore 2 ↥H, ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹ :=
    fun g => haveI := hNn; conj_inner_of_equiv eN' CFSG.QuasithinUnique.Setup.X1.m23_autInner g
  have hxN : mk ⟨t'⁻¹ * x * t', hx₂H⟩ ∈ N :=
    haveI := hNn
    lemma2_trivial_center hLbN (le_nine_modO2_of_pRank_le H hrk) hZ
      (fun g _ => hinn g) heb he3b hx3b hcommb hxbL
  set Sb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := ((Sgp153 T V₁).subgroupOf H).map mk with hSbdef
  have hSb : IsSylowTwoOf Sb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSyl) mk
      (QuotientGroup.mk'_surjective _)
  have hSbL : Sb ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    Row18.bar_le_normalizer hSL
  have hS₀ : IsSylowTwoOf (Sb ⊓ N) N :=
    B6.isSylowTwoOf_inf_normal hSb le_top (by rw [Subgroup.normalizer_eq_top (H := N)])
  have hNc : Nat.card ↥N = 2 ^ 7 * 79695 := card_of_equiv_M23 ⟨eN⟩
  have hS₀c : Nat.card ↥(Sb ⊓ N) = 2 ^ 7 := Row18.card_eq_pow_of_isSylowTwoOf hS₀ hNc (by omega)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card Lb = 2 ^ a * 21 := by
    rcases row13_data hrow.1 with h | h
    · exact ⟨7, by rw [h]; norm_num⟩
    · exact ⟨6, by rw [h]; norm_num⟩
  have hS₀n : Sb ⊓ N ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    inf_le_left.trans hSbL
  obtain ⟨n₁, hn₁⟩ := card_sup_eq_two_pow_mul (L := Lb) hS₀.2.1 hS₀n
  have hYN : Lb ⊔ (Sb ⊓ N) ≤ N := sup_le hLbN inf_le_right
  have hYc : Nat.card ↥(Lb ⊔ (Sb ⊓ N)) = 2 ^ 7 * 21 := by
    refine nat_aux (m := n₁ + a) ?_ ?_ ?_
    · rw [hn₁, ha, pow_add]; ring
    · rw [← hS₀c]; exact Subgroup.card_dvd_of_le le_sup_right
    · rw [← hNc]; exact Subgroup.card_dvd_of_le hYN
  have hYnorm : Lb ⊔ (Sb ⊓ N) ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    sup_le Subgroup.le_normalizer hS₀n
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) := by
    have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
    exact Hyp153.T_le_normalizer_Sgp153 hh.hyp hh.decomp
  obtain ⟨Yb, hYbc, hSbY, hxbY⟩ := exists_bar_overgroup' (H := H) (L := L) (S := Sgp153 T V₁)
    (t' := t') (x := x) hSH hxL hx₂H
    (fun s hs => (Subgroup.mem_normalizer_iff.mp (hTS ht'T) s).mp hs)
  obtain ⟨n₂, hn₂⟩ := card_sup_eq_two_pow_mul (L := L) hSyl.2.1 hSL
  obtain ⟨c₂, hc₂⟩ := card_eq_modO2Image_mul hLH
  have hPc : ∃ K : ℕ, Nat.card ↥(Yb ⊓ N) ∣ 2 ^ K * 21 := by
    refine ⟨n₂ + c₂ + a, ?_⟩
    have h1 : Nat.card ↥(Yb ⊓ N) ∣ Nat.card ↥(L ⊔ Sgp153 T V₁) :=
      (Subgroup.card_dvd_of_le inf_le_left).trans hYbc
    rw [hn₂, hc₂, ← hLbdef, ha] at h1
    have e : 2 ^ n₂ * (2 ^ a * 21 * 2 ^ c₂) = 2 ^ (n₂ + c₂ + a) * 21 := by
      rw [pow_add, pow_add]; ring
    rwa [e] at h1
  have hs₁'b2 : ∃ k : ℕ, (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) ^ 2 ^ k = 1 := by
    have hmem : mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩ ∈ Sb := ⟨⟨t'⁻¹ * s₁ * t', hs₁'H⟩, hs₁'S, rfl⟩
    obtain ⟨k, hk⟩ := (hSb.2.1) ⟨_, hmem⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨k₀, hk₀⟩ := hs₁'b2
  obtain ⟨l, hlN, hl⟩ := hinn (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩)
  have hpow : ∀ m : ℕ, ∀ b ∈ N, (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) ^ m * b *
      ((mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) ^ m)⁻¹ = l ^ m * b * (l ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro b hb; simp
    | succ m ih =>
      intro b hb
      have hbm : l ^ m * b * (l ^ m)⁻¹ ∈ N :=
        N.mul_mem (N.mul_mem (N.pow_mem hlN _) hb) (N.inv_mem (N.pow_mem hlN _))
      calc (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) ^ (m + 1) * b * ((mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) ^ (m + 1))⁻¹
          = (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) * ((mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) ^ m * b *
              ((mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) ^ m)⁻¹) * (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩)⁻¹ := by
            rw [pow_succ']; group
        _ = (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩) * (l ^ m * b * (l ^ m)⁻¹) *
              (mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩)⁻¹ := by rw [ih b hb]
        _ = l * (l ^ m * b * (l ^ m)⁻¹) * l⁻¹ := hl _ hbm
        _ = l ^ (m + 1) * b * (l ^ (m + 1))⁻¹ := by rw [pow_succ']; group
  have hl2 : l ^ 2 ^ k₀ = 1 := by
    apply hZ _ (N.pow_mem hlN _)
    intro a' ha'
    have h1 := hpow (2 ^ k₀) a' ha'
    rw [hk₀, inv_one, one_mul, mul_one] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1.symm
  have hlnorm : ∀ a ∈ Sb ⊓ N, l * a * l⁻¹ ∈ Sb ⊓ N := by
    intro a ha
    rw [← hl a ha.2]
    have hsb : mk ⟨t'⁻¹ * s₁ * t', hs₁'H⟩ ∈ Sb := ⟨⟨t'⁻¹ * s₁ * t', hs₁'H⟩, hs₁'S, rfl⟩
    exact ⟨Sb.mul_mem (Sb.mul_mem hsb ha.1) (Sb.inv_mem hsb), hNn.conj_mem a ha.2 _⟩
  have hlS : l ∈ Sb ⊓ N := by
    have hA : IsPGroup 2 (Subgroup.zpowers l) := by
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hl2)
      exact IsPGroup.iff_card.mpr ⟨j, by rw [Nat.card_zpowers]; exact hj'⟩
    have hle : Subgroup.zpowers l ≤ Subgroup.normalizer ((Sb ⊓ N : Subgroup _) : Set _) :=
      (Subgroup.zpowers_le).mpr (Subgroup.mem_normalizer_fintype hlnorm)
    exact le_of_isPGroup_normalizes_sylow hS₀ ((Subgroup.zpowers_le).mpr hlN) hA hle
      (Subgroup.mem_zpowers l)
  have hconjb : ∀ (a b d : G) (ha : a ∈ H) (hb : b ∈ H) (hd : d ∈ H), a * b * a⁻¹ = d →
      mk ⟨a, ha⟩ * mk ⟨b, hb⟩ * (mk ⟨a, ha⟩)⁻¹ = mk ⟨d, hd⟩ := by
    intro a b d ha hb hd h
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg mk (Subtype.ext (by simpa using h))
  have hlinv : l * mk ⟨t'⁻¹ * y * t', heH⟩ * l⁻¹ = (mk ⟨t'⁻¹ * y * t', heH⟩)⁻¹ := by
    rw [← hl _ (hLbN heb), hconjb _ _ _ hs₁'H heH (H.inv_mem heH) hs₁'y, ← map_inv]
    rfl
  have hlcen : l * mk ⟨t'⁻¹ * x * t', hx₂H⟩ * l⁻¹ = mk ⟨t'⁻¹ * x * t', hx₂H⟩ := by
    rw [← hl _ hxN, hconjb _ _ _ hs₁'H hx₂H hx₂H hs₁'x]
  have hmemP : mk ⟨t'⁻¹ * x * t', hx₂H⟩ ∈ Yb ⊓ N := ⟨hxbY, hxN⟩
  refine m23_core (S₁ := ((Sb ⊓ N).subgroupOf N).map eN'.toMonoidHom)
    (Y := ((Lb ⊔ (Sb ⊓ N)).subgroupOf N).map eN'.toMonoidHom)
    (P := ((Yb ⊓ N).subgroupOf N).map eN'.toMonoidHom)
    (CFSG.QuasithinUnique.L246C127.isSylowTwoOf_top_map_subgroupOf eN' hS₀)
    (Subgroup.map_mono fun y hy => (le_sup_right : Sb ⊓ N ≤ Lb ⊔ (Sb ⊓ N)) hy)
    (Subgroup.map_mono fun y hy => ⟨hSbY hy.1, hy.2⟩)
    (by rw [card_map_subgroupOf eN' hYN]; exact hYc)
    (by obtain ⟨K, hK⟩ := hPc; exact ⟨K, by rw [card_map_subgroupOf eN' inf_le_right]; exact hK⟩)
    (e := eN' ⟨mk ⟨t'⁻¹ * y * t', heH⟩, hLbN heb⟩)
    (x := eN' ⟨mk ⟨t'⁻¹ * x * t', hx₂H⟩, hxN⟩)
    (σ := eN' ⟨l, hlN⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (mem_map_subgroupOf_iff eN' (hLbN heb)).mpr ((le_sup_left : Lb ≤ Lb ⊔ (Sb ⊓ N)) heb)
  · rw [orderOf_equiv_mk]; exact he3b
  · exact (mem_map_subgroupOf_iff eN' hxN).mpr hmemP
  · intro h
    exact hxbL (hYnorm ((mem_map_subgroupOf_iff eN' hxN).mp h))
  · rw [orderOf_equiv_mk]; exact hx3b
  · rw [← map_mul, ← map_mul]
    apply congrArg eN'
    apply Subtype.ext
    exact hcommb
  · exact (mem_map_subgroupOf_iff eN' hlN).mpr hlS
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    apply congrArg eN'
    apply Subtype.ext
    exact hlinv
  · rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg eN'
    apply Subtype.ext
    exact hlcen

theorem row13_false
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1)
    (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1) (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀) (hc₀2 : c₀ * c₀ = 1)
    {H : Subgroup G} (hH : H = Subgroup.centralizer ({c₀} : Set G))
    (hSyl : IsSylowTwoOf (Sgp153 T V₁) H) {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal) (hev : evenRank G ≤ 2)
    (hrow : (IsExt ↥(modO2Image H L) (fun V _ => IsE2 4 V) (fun Y' _ => IsPSL 3 2 1 Y') ∨
        IsExt ↥(modO2Image H L) (fun V _ => IsE2 3 V) (fun Y' _ => IsPSL 3 2 1 Y')) ∧
      IsSporadic .M23 ↥(modO2Image H L₁)) : False := by
  have hloc : IsTwoLocal H := by
    rw [hH]
    exact CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one
      (by rw [pow_two]; exact hc₀2) hc₀1
  have hrk := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc
  exact row13_false_of_rank h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4 hlabel hc₀ hc₀Vc
    hc₀1 hu₀ hu₀1 hu₀S hsw hH hSyl hLL₁ hN (hrk.trans hev) hrow

end Row13

end Stellmacher.L3YC

end CFSG.Quasithin
