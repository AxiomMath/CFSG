module

public import CFSG.Quasithin.H13.L32NInputs
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.Recognition.HSTypeModels
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma4

public section

namespace CFSG.Quasithin.H13.L32NSet14

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mul_mem_of_card_eq_two_mul {W X : Subgroup G} (hWX : W ≤ X)
    (hc : Nat.card X = 2 * Nat.card W) (hW : Nat.card W ≠ 0) {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) (hxW : x ∉ W) (hyW : y ∉ W) : x * y ∈ W := by
  have hidx : (W.subgroupOf X).index = 2 := by
    have h1 := (W.subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv, hc] at h1
    have : Nat.card W * (W.subgroupOf X).index = Nat.card W * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hW) this
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    ⟨fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hxW,
      fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hyW⟩
  exact Subgroup.mem_subgroupOf.mp this

section Inputs

variable [Finite G] {T L V : Subgroup G}

theorem hyp1223 (h1332 : Stmt13_3_2) (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) : Hyp1223 G T L V where
  simple := hH.simple
  nonabelian := hH.nonabelian
  qtke := hH.qtke
  sylow := hH.sylow
  notAlt := fun hA => hH.not_excluded (Hyp14310One.qt13Excluded_of_alt hA)
  maximal := (h1332 G T L hH L hH.faithful).2.1.2.1
  faithful := hH.faithful
  quasisimple := ((h1332 G T L hH L hH.faithful).2.2.1.2 V hV).2.2.1.quasisimple
  normalizes := (h1332 G T L hH L hH.faithful).2.1.1
  irrPlus := hV

theorem hyp1281One (h1332 : Stmt13_3_2) (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) [IsMulCommutative ↥V]
    (hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1) : Hyp1281One G T L V 3 where
  hyp := hyp1223 h1332 hH hV
  n_mem := Or.inl rfl
  quot := nonempty_equiv_SL32_of_lieModel hlin
  natural := ⟨inferInstance, hnat⟩
  not_linear := fun hL => hH.not_excluded (Or.inr (Or.inl (Or.inl hL)))
  not_alt9 := fun hA => hH.not_excluded (Or.inr (Or.inr (Or.inl hA)))
  not_m24 := fun hM => hH.not_excluded (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl hM))))))

theorem isTSub_V1 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥) : IsTSub T V (fsuV1 T V) 1 := by
  have hTV : T ≤ normalizer (V : Set G) := ((h1332 G T L hH L hH.faithful).2.2.1.2 V hV).2.1
  have hTZ : T ≤ normalizer (quasithinOmegaOneCenter T : Set G) := by
    have hZ : quasithinOmegaOneCenter T ≤ T ⊓ centralizer (T : Set G) :=
      (closure_le _).mpr fun _ hz => hz.1
    exact (le_centralizer_iff.mp (hZ.trans inf_le_right)).trans
      (centralizer_le_normalizer _)
  obtain ⟨⟨-, hV1, -⟩, -, -⟩ := h1334 G T L V hH hV
  refine ⟨inf_le_left, by rw [hV1, hZV, card_bot]; norm_num, fun t ht => ?_⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(mem_normalizer_iff.mp (hTV ht) x).mp hxV, (mem_normalizer_iff.mp (hTZ ht) x).mp hxZ⟩
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(mem_normalizer_iff.mp (hTV ht) x).mpr hxV,
      (mem_normalizer_iff.mp (hTZ ht) x).mpr hxZ⟩

end Inputs

theorem card_sup_mul_card_inf {X N : Subgroup G} (hXN : X ≤ normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring


theorem mem_span_pair_zmod2 {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {p r q : W}
    (hq : q ∈ (ZMod 2) ∙ p ⊔ (ZMod 2) ∙ r) : q = 0 ∨ q = p ∨ q = r ∨ q = p + r := by
  obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp hq
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy'
  have h01 : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  rcases h01 c with rfl | rfl <;> rcases h01 d with rfl | rfl <;> simp

theorem exists_four_pow (m : ℕ) : ∃ q : ℕ, 1 + 3 * q = 4 ^ m := by
  induction m with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨4 * q + 1, by rw [pow_succ, ← hq]; ring⟩

structure Setting (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G)
    [IsMulCommutative ↥V] : Prop where
  h1222 : Stmt12_2_2
  h1332 : Stmt13_3_2
  h1334 : A6.Stmt13_3_4
  hH : QTH13 G T L
  hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V
  hZV : V ⊓ centralizer (L : Set G) = ⊥
  hV2 : A6.IsV2 T V V₂
  hlin : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1

namespace Setting

variable [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V] (S : Setting G T L V V₂)
include S

theorem h1281 : Hyp1281One G T L V 3 := hyp1281One S.h1332 S.hH S.hV S.hlin S.hnat

theorem hV1 : IsTSub T V (fsuV1 T V) 1 := isTSub_V1 S.h1332 S.h1334 S.hH S.hV S.hZV

theorem card_V : Nat.card V = 8 := S.h1281.card_sq.1

theorem sq_V {v : G} (hv : v ∈ V) : v ^ 2 = 1 := S.h1281.card_sq.2.1 v hv

theorem mul_self_V {v : G} (hv : v ∈ V) : v * v = 1 := by rw [← sq]; exact S.sq_V hv

theorem comm_V {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  S.h1281.card_sq.2.2 x hx y hy

theorem TV : T ≤ normalizer (V : Set G) := ((S.h1332 G T L S.hH L S.hH.faithful).2.2.1.2 V S.hV).2.1

theorem VT : V ≤ T := ((S.h1332 G T L S.hH L S.hH.faithful).2.2.1.2 V S.hV).1

theorem TL : T ≤ normalizer (L : Set G) := (S.h1332 G T L S.hH L S.hH.faithful).2.1.1

theorem LV : L ≤ normalizer (V : Set G) := S.hV.2.2.1

theorem card_V1 : Nat.card (fsuV1 T V) = 2 := by simpa using S.hV1.2.1

theorem T_V1 : T ≤ normalizer (fsuV1 T V : Set G) := S.hV1.2.2

theorem card_L : Nat.card L = 168 * Nat.card (pCoreOf 2 L) := by
  obtain ⟨θ, hθ, hker⟩ := exists_surj_SL32_of_lieModel S.hlin
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv,
    HSType.card_SL_three_two, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).toEquiv] at h1
  exact h1

theorem card_autOn : Nat.card (autOn L V) = 168 := by
  rw [card_eq_of_binaryNaturalSL S.hnat (by norm_num)]
  decide

theorem cent_eq : L ⊓ centralizer (V : Set G) = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrel := Subgroup.relIndex_mul_card (L ⊓ centralizer (V : Set G)) L
  rw [← card_autOn_eq_relIndex S.LV, inf_right_comm, inf_idem, S.card_autOn, S.card_L] at hrel
  have hc : Nat.card ↥(L ⊓ centralizer (V : Set G)) = Nat.card (pCoreOf 2 L) := by omega
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
  have hp : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := IsPGroup.of_card (by rw [hc, hk])
  have hle : L ⊓ centralizer (V : Set G) ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => ?_) hp
    refine mem_normalizer_iff.mpr fun c => ⟨fun ⟨hcL, hcV⟩ => ?_, fun ⟨hcL, hcV⟩ => ?_⟩
    · refine ⟨L.mul_mem (L.mul_mem hl hcL) (L.inv_mem hl), mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hv' : l⁻¹ * v * l ∈ V := by
        have := (mem_normalizer_iff.mp (S.LV (L.inv_mem hl)) v).mp hv
        rwa [inv_inv] at this
      have := mem_centralizer_iff.mp hcV _ hv'
      calc v * (l * c * l⁻¹) = l * ((l⁻¹ * v * l) * c) * l⁻¹ := by group
        _ = l * (c * (l⁻¹ * v * l)) * l⁻¹ := by rw [this]
        _ = l * c * l⁻¹ * v := by group
    · have hcL' : c ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem hl) hcL) hl
        rwa [show l⁻¹ * (l * c * l⁻¹) * l = c by group] at this
      refine ⟨hcL', mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hv' : l * v * l⁻¹ ∈ V := (mem_normalizer_iff.mp (S.LV hl) v).mp hv
      have := mem_centralizer_iff.mp hcV _ hv'
      calc v * c = l⁻¹ * ((l * v * l⁻¹) * (l * c * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * c * l⁻¹) * (l * v * l⁻¹)) * l := by rw [this]
        _ = c * v := by group
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc])

theorem isPGroup_cent_sup : IsPGroup 2 ↥((L ⊔ T) ⊓ centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTV : L ⊔ T ≤ normalizer (V : Set G) := sup_le S.LV S.TV
  have hA : autOn (L ⊔ T) V = autOn L V := by
    have h1 : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One S.h1281
    rw [h1, eq_top_iff, ← h1]
    exact autOn_mono le_sup_left
  have hrel := Subgroup.relIndex_mul_card ((L ⊔ T) ⊓ centralizer (V : Set G)) (L ⊔ T)
  rw [← card_autOn_eq_relIndex hLTV, inf_right_comm, inf_idem, hA, S.card_autOn] at hrel
  have hsup := card_sup_mul_card_inf S.TL
  rw [sup_comm T L, S.card_L] at hsup
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
  obtain ⟨b, hb⟩ := S.hH.sylow.1.exists_card_eq
  rw [ha, hb] at hsup
  have hdvd : Nat.card ↥((L ⊔ T) ⊓ centralizer (V : Set G)) ∣ 2 ^ (b + a) := by
    refine ⟨Nat.card ↥(T ⊓ L), ?_⟩
    have : 168 * (Nat.card ↥((L ⊔ T) ⊓ centralizer (V : Set G)) * Nat.card ↥(T ⊓ L)) =
        168 * 2 ^ (b + a) := by
      rw [← mul_assoc, hrel, hsup, pow_add]
      ring
    omega
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact IsPGroup.of_card hk

theorem eq_of_mem_V1 {z v : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hv : v ∈ fsuV1 T V) :
    v = 1 ∨ v = z := by
  by_contra h
  push Not at h
  have hvz := mul_mem_of_card_eq_two_mul (W := (⊥ : Subgroup G)) (X := fsuV1 T V) bot_le
    (by rw [S.card_V1, card_bot]) (by rw [card_bot]; norm_num) hv hz
    (by rw [mem_bot]; exact h.1) (by rw [mem_bot]; exact hz1)
  rw [mem_bot] at hvz
  apply h.2
  calc v = v * z * z := by rw [mul_assoc, S.mul_self_V (Subgroup.mem_inf.mp hz).1, mul_one]
    _ = z := by rw [hvz, one_mul]

theorem mem_g1 {z g : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hg : g * z * g⁻¹ = z) :
    g ∈ normalizer (fsuV1 T V : Set G) := by
  rw [normalizer_eq_centralizer_of_card_eq_two S.card_V1, mem_centralizer_iff]
  intro v hv
  rcases S.eq_of_mem_V1 hz hz1 hv with rfl | rfl
  · group
  · calc v * g = g * v * g⁻¹ * g := by rw [hg]
      _ = g * v := by group

theorem mem_V2 {a v : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (hv : v ∈ V₂) :
    v ∈ fsuV1 T V ∨ a * v ∈ fsuV1 T V := by
  by_cases h : v ∈ fsuV1 T V
  · exact Or.inl h
  · exact Or.inr (mul_mem_of_card_eq_two_mul S.hV2.1 (by rw [S.hV2.2.2.2, S.card_V1])
      (by rw [S.card_V1]; norm_num) ha hv haV h)

theorem mem_V {b v : G} (hb : b ∈ V) (hbV : b ∉ V₂) (hv : v ∈ V) : v ∈ V₂ ∨ b * v ∈ V₂ := by
  by_cases h : v ∈ V₂
  · exact Or.inl h
  · exact Or.inr (mul_mem_of_card_eq_two_mul S.hV2.2.1 (by rw [S.card_V, S.hV2.2.2.2])
      (by rw [S.hV2.2.2.2]; norm_num) hb hv hbV h)

theorem exists_basis : ∃ z a b : G, z ∈ fsuV1 T V ∧ z ≠ 1 ∧ a ∈ V₂ ∧ a ∉ fsuV1 T V ∧ b ∈ V ∧
    b ∉ V₂ := by
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : fsuV1 T V = ⊥ := (eq_bot_iff_forall _).mpr h
    have h2 := S.card_V1
    rw [h1, card_bot] at h2
    omega
  obtain ⟨a, ha, haV⟩ : ∃ a ∈ V₂, a ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from h)
    rw [S.hV2.2.2.2, S.card_V1] at h1
    omega
  obtain ⟨b, hb, hbV⟩ : ∃ b ∈ V, b ∉ V₂ := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show V ≤ V₂ from h)
    rw [S.card_V, S.hV2.2.2.2] at h1
    omega
  exact ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩

theorem exists_lift [Module (ZMod 2) (Additive ↥V)] (β : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :
    ∃ l ∈ L, ∀ v (hv : v ∈ V),
      l * v * l⁻¹ = ((Additive.toMul (β (Additive.ofMul ⟨v, hv⟩)) : ↥V) : G) := by
  have hαL : mulAutOfLin β ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One S.h1281]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  refine ⟨l, Subgroup.mem_subgroupOf.1 hlL, fun v hv => ?_⟩
  rw [← mulAutOfLin_apply, ← hlα]
  rfl

theorem exists_odd_pow {l : G} (hl : l ∈ L) (h3 : ∀ v ∈ V, l ^ 3 * v * (l ^ 3)⁻¹ = v) :
    ∃ k : ℕ, (l ^ k) ^ 3 = 1 ∧ ∀ v ∈ V, l ^ k * v * (l ^ k)⁻¹ = l * v * l⁻¹ := by
  have hcV : l ^ 3 ∈ centralizer (V : Set G) := mem_centralizer_iff.mpr fun v hv => by
    calc v * l ^ 3 = (l ^ 3 * v * (l ^ 3)⁻¹) * l ^ 3 := by rw [h3 v hv]
      _ = l ^ 3 * v := by group
  have hc : l ^ 3 ∈ pCoreOf 2 L := by
    rw [← S.cent_eq]
    exact ⟨L.pow_mem hl 3, hcV⟩
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hc⟩
  have hm' : (l ^ 3) ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow] at this
  obtain ⟨q, hq⟩ := exists_four_pow m
  refine ⟨4 ^ m, ?_, fun v hv => ?_⟩
  · rw [← pow_mul, show 4 ^ m * 3 = 3 * 2 ^ m * 2 ^ m by
      rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]; ring, pow_mul, pow_mul, hm', one_pow]
  · have hcv : (l ^ 3) ^ q * v * ((l ^ 3) ^ q)⁻¹ = v := by
      have := mem_centralizer_iff.mp ((centralizer (V : Set G)).pow_mem hcV q) v hv
      rw [← this]
      group
    rw [← hq, pow_add, pow_one, pow_mul]
    calc l * (l ^ 3) ^ q * v * (l * (l ^ 3) ^ q)⁻¹ =
        l * ((l ^ 3) ^ q * v * ((l ^ 3) ^ q)⁻¹) * l⁻¹ := by group
      _ = l * v * l⁻¹ := by rw [hcv]

theorem exists_rot {p u w : G} (hp : p ∈ V) (hu : u ∈ V) (hw : w ∈ V)
    (hu1 : u ≠ 1) (hw1 : w ≠ 1) (hup : u ≠ p) (hwp : w ≠ p) (huw : u ≠ w) (hwpu : w ≠ p * u) :
    ∃ l ∈ L, l ^ 3 = 1 ∧ l * p * l⁻¹ = p ∧ l * u * l⁻¹ = w ∧ l * w * l⁻¹ = u * w := by
  let _ := zmodModuleOf (fun v hv => S.sq_V hv)
  let c : Additive ↥V → G := fun q => ((Additive.toMul q : ↥V) : G)
  set p' : Additive ↥V := Additive.ofMul ⟨p, hp⟩
  set u' : Additive ↥V := Additive.ofMul ⟨u, hu⟩
  set w' : Additive ↥V := Additive.ofMul ⟨w, hw⟩
  have hc0 : c 0 = 1 := rfl
  have hcadd : ∀ q r, c (q + r) = c q * c r := fun _ _ => rfl
  have hupw : u ≠ p * w := fun h => hwpu (by
    rw [h, ← mul_assoc, S.mul_self_V hp, one_mul])
  have h1 : u' ∉ (ZMod 2) ∙ p' ⊔ (ZMod 2) ∙ w' := fun h => by
    rcases mem_span_pair_zmod2 h with h | h | h | h
    · exact hu1 (congrArg c h)
    · exact hup (congrArg c h)
    · exact huw (congrArg c h)
    · exact hupw ((congrArg c h).trans (hcadd _ _))
  have h2 : w' ∉ (ZMod 2) ∙ p' ⊔ (ZMod 2) ∙ u' := fun h => by
    rcases mem_span_pair_zmod2 h with h | h | h | h
    · exact hw1 (congrArg c h)
    · exact hwp (congrArg c h)
    · exact huw (congrArg c h).symm
    · exact hwpu ((congrArg c h).trans (hcadd _ _))
  obtain ⟨ρ, hρ3, hρu, hρw, hρP⟩ := exists_rotation h1 h2
  obtain ⟨l₀, hl₀, hconj⟩ := S.exists_lift ρ
  have hconj' : ∀ v : ↥V, l₀ * (v : G) * l₀⁻¹ = c (ρ (Additive.ofMul v)) :=
    fun v => hconj v v.2
  have h3 : ∀ v ∈ V, l₀ ^ 3 * v * (l₀ ^ 3)⁻¹ = v := by
    intro v hv
    have e : l₀ ^ 3 * v * (l₀ ^ 3)⁻¹ = l₀ * (l₀ * (l₀ * v * l₀⁻¹) * l₀⁻¹) * l₀⁻¹ := by
      rw [pow_three]
      group
    rw [e, hconj v hv, hconj' (Additive.toMul (ρ (Additive.ofMul ⟨v, hv⟩))),
      hconj' (Additive.toMul (ρ (Additive.ofMul (Additive.toMul (ρ (Additive.ofMul ⟨v, hv⟩))))))]
    show c (ρ (ρ (ρ (Additive.ofMul ⟨v, hv⟩)))) = v
    rw [hρ3]
    rfl
  obtain ⟨k, hk3, hk⟩ := S.exists_odd_pow hl₀ h3
  refine ⟨l₀ ^ k, L.pow_mem hl₀ k, hk3, ?_, ?_, ?_⟩
  · rw [hk p hp, hconj p hp, hρP _ (Submodule.mem_span_singleton_self _)]
    rfl
  · rw [hk u hu, hconj u hu]
    show c (ρ u') = w
    rw [hρu]
    rfl
  · rw [hk w hw, hconj w hw]
    show c (ρ w') = u * w
    rw [hρw]
    show (((Additive.toMul u' : ↥V) : G))⁻¹ / ((Additive.toMul w' : ↥V) : G) = u * w
    show u⁻¹ / w = u * w
    rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right (S.mul_self_V hu),
      inv_eq_of_mul_eq_one_right (S.mul_self_V hw)]

end Setting

end CFSG.Quasithin.H13.L32NSet14
