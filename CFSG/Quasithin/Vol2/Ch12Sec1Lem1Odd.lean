module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Ns
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.B2FactorizationBaumannVar

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open scoped Matrix commutatorElement

namespace Sec1211Ns

variable {G : Type} [Group G]

theorem centralizer_zpowers_eq (v : G) :
    Subgroup.centralizer (Subgroup.zpowers v : Set G) = Subgroup.centralizer ({v} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h x (Subgroup.mem_zpowers x)
  · intro h x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hv : Commute v g := h v (Set.mem_singleton v)
    exact (Commute.zpow_left hv k).eq

theorem zpow_eq_one_or_self {v : G} (hv : v ^ 2 = 1) (k : ℤ) : v ^ k = 1 ∨ v ^ k = v := by
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · left
    rw [hj, _root_.zpow_mul, zpow_ofNat, hv, _root_.one_zpow]
  · right
    rw [hj, _root_.zpow_add, _root_.zpow_mul, zpow_ofNat, hv, _root_.one_zpow, one_mul, zpow_one]

theorem exists_perp_perp {n : ℕ} (hn : 3 ≤ n) (x₀ x : Fin n → ZMod 2) :
    ∃ y : Fin n → ZMod 2, y ≠ 0 ∧ x₀ ⬝ᵥ y = 0 ∧ x ⬝ᵥ y = 0 := by
  classical
  have hcard : Fintype.card (ZMod 2 × ZMod 2) < Fintype.card (Fin n → ZMod 2) := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    calc 2 * 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨y, y', hne, hyy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun y : Fin n → ZMod 2 => (x₀ ⬝ᵥ y, x ⬝ᵥ y)) hcard
  simp only [Prod.mk.injEq] at hyy
  refine ⟨y + y', fun h => hne (VecStab.eq_of_add_eq_zero h), ?_, ?_⟩
  · rw [dotProduct_add, hyy.1, CharTwo.add_self_eq_zero]
  · rw [dotProduct_add, hyy.2, CharTwo.add_self_eq_zero]

theorem mem_normalizer_sup {A B : Subgroup G} {l : G} (hA : l ∈ Subgroup.normalizer (A : Set G))
    (hB : l ∈ Subgroup.normalizer (B : Set G)) :
    l ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hA' : A.map (MulAut.conj l).toMonoidHom = A :=
    KGH91.map_conj_eq_iff.mpr fun a => Subgroup.mem_normalizer_iff.mp hA a
  have hB' : B.map (MulAut.conj l).toMonoidHom = B :=
    KGH91.map_conj_eq_iff.mpr fun a => Subgroup.mem_normalizer_iff.mp hB a
  have h := Subgroup.map_sup A B (MulAut.conj l).toMonoidHom
  rw [hA', hB'] at h
  rw [Subgroup.mem_normalizer_iff]
  exact KGH91.map_conj_eq_iff.mp h

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  (S : Setting T L V V₁ V₂ n a₀ c₀)
include S

theorem W_le_V : S.W₁ ⊔ S.W₂ ≤ V := sup_le (S.W₁_le.trans S.le₁) (S.W₂_le.trans S.le₂)

theorem exists_singular : ∃ u ∈ S.W₁ ⊔ S.W₂, u ∈ V ∧ u ≠ 1 ∧ ¬ (u ∈ V₁ ∨ u ∈ V₂) ∧
    ¬ IsNonsingular121 V₁ V₂ (KGH91.pairing S.C₁ S.C₂) u := by
  obtain ⟨x, hx, hx0, -⟩ := VecStab.exists_perp_ne S.three_le' S.y₀_ne 0
  have hx' : x ⬝ᵥ S.C₂.E c₀ = 0 := by rw [dotProduct_comm]; exact hx
  obtain ⟨y, hy0, hy, hxy⟩ := exists_perp_perp S.three_le' (S.C₁.E a₀) x
  have hw₁ := S.inv_mem_W₁ hx'
  have hw₂ := S.inv_mem_W₂ hy
  have hw₁1 : S.C₁.inv x ≠ 1 := fun h => hx0 (by rw [← S.C₁.E_inv x, h, S.C₁.E_one])
  have hw₂1 : S.C₂.inv y ≠ 1 := fun h => hy0 (by rw [← S.C₂.E_inv y, h, S.C₂.E_one])
  have hpair : KGH91.pairing S.C₁ S.C₂ (S.C₁.inv x) (S.C₂.inv y) = 0 := by
    rw [KGH91.pairing, S.C₁.E_inv, S.C₂.E_inv]
    exact hxy
  refine ⟨S.C₁.inv x * S.C₂.inv y, Subgroup.mul_mem_sup hw₁ hw₂,
    V.mul_mem (S.le₁ hw₁.1) (S.le₂ hw₂.1), fun h => ?_, ?_, ?_⟩
  · have := (S.mem_union_iff hw₁.1 hw₂.1).mp (Or.inl (h ▸ V₁.one_mem))
    rcases this with h1 | h1
    · exact hw₁1 h1
    · exact hw₂1 h1
  · rw [S.mem_union_iff hw₁.1 hw₂.1]
    rintro (h | h)
    · exact hw₁1 h
    · exact hw₂1 h
  · rw [S.nonsing_iff hw₁.1 hw₂.1, hpair]
    exact zero_ne_one

theorem sylow_top : IsSylowTwoOf T ⊤ := by
  refine ⟨le_top, S.hyp.sylow.1, ?_⟩
  show ¬ 2 ∣ T.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact S.hyp.sylow.2

theorem pairing_eq_zero {v₁ c : G}
    (hv₁ : V₁ ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) = Subgroup.zpowers v₁)
    (hc : c ∈ V₂) (hcT : ∀ t ∈ T ⊓ Subgroup.normalizer (V₁ : Set G), t * c * t⁻¹ = c) :
    KGH91.pairing S.C₁ S.C₂ v₁ c = 0 := by
  have := S.hVe.1
  have hβ := KGH91.isDualPairing S.C₁ S.C₂ S.dual
  have hv₁V : v₁ ∈ V₁ := (hv₁ ▸ Subgroup.mem_zpowers v₁ : v₁ ∈ V₁ ⊓ _).1
  by_cases hc1 : c = 1
  · rw [hc1]
    simp [KGH91.pairing, S.C₂.E_one]
  obtain ⟨K, hKV, hK, hcard⟩ := Sec1212.exists_ker (X := V₁)
    (fun a => KGH91.pairing S.C₁ S.C₂ a c) (fun a ha b hb => hβ.1 a ha b hb c hc)
  obtain ⟨a', ha', ha'c⟩ := hβ.2.2.2.1 c hc hc1
  have h2K := hcard a' ha' (by
    show KGH91.pairing S.C₁ S.C₂ a' c ≠ 0
    rw [ha'c]
    exact one_ne_zero)
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, S.card₁, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_fin] at h2K
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) S.three_le'
    omega
  have hT₁2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (V₁ : Set G)) :=
    S.hyp.sylow.1.to_le inf_le_left
  have hKT : K ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) := by
    intro a ha
    have haV := S.le₁ (hKV ha)
    refine ⟨Sec1215.le_of_hyp121 S.hyp S.hTL haV, ?_⟩
    exact S.hyp.norm₁.trans le_rfl |> fun _ =>
      Sec121Swap.mem_normalizer_of_conj_mem fun b hb => by
        rw [S.comm haV (S.le₁ hb), mul_inv_cancel_right]
        exact hb
  have hTK : T ⊓ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro t ht
    have htM := S.hTL ht.1
    have htV₂ : t ∈ Subgroup.normalizer (V₂ : Set G) := by
      rcases S.fix_or_swap htM with ⟨-, h⟩ | ⟨h₁, -⟩
      · exact h
      · exfalso
        obtain ⟨a, ha, ha1⟩ := S.exists_ne_one₁
        have h1 : t * a * t⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp ht.2 a).mp ha
        have h2 : t * a * t⁻¹ ∈ V₂ := (h₁ a).mp ha
        have h3 : t * a * t⁻¹ ∈ V₁ ⊓ V₂ := ⟨h1, h2⟩
        rw [S.hyp.inf, Subgroup.mem_bot] at h3
        exact ha1 (by
          calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
            _ = 1 := by rw [h3]; group)
    refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
    have haV : a ∈ V₁ := hKV ha
    have htaV : t * a * t⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp ht.2 a).mp haV
    refine (hK _ htaV).mpr ?_
    have h1 := S.pairing_conj htM ht.2 htV₂ a haV c hc
    rw [hcT t ht] at h1
    show KGH91.pairing S.C₁ S.C₂ (t * a * t⁻¹) c = 0
    rw [h1]
    exact (hK a haV).mp ha
  obtain ⟨a, haK, ha1, haC⟩ := Sec1215.exists_ne_one_mem_centralizer hT₁2 hKT hTK hK1
  have hav : a ∈ Subgroup.zpowers v₁ := by
    rw [← hv₁]
    exact ⟨hKV haK, haC⟩
  have hv₁2 : v₁ ^ 2 = 1 := S.hVe.2 v₁ (S.le₁ hv₁V)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hav
  rcases zpow_eq_one_or_self hv₁2 k with h | h
  · exact absurd h ha1
  · have h1 := (hK _ (hKV haK)).mp haK
    rwa [h] at h1

theorem exists_z₀ : ∃ z₀ ∈ V, z₀ ∈ Subgroup.centralizer (T : Set G) ∧ z₀ ≠ 1 ∧
    ¬ (z₀ ∈ V₁ ∨ z₀ ∈ V₂) ∧ ¬ IsNonsingular121 V₁ V₂ (KGH91.pairing S.C₁ S.C₂) z₀ := by
  have := S.hVe.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S.hTL.trans S.le_normalizer
  have hV1 : V ≠ ⊥ := fun h => S.a₀_ne (Subgroup.mem_bot.mp (h ▸ S.le₁ S.ha₀))
  obtain ⟨z₀, hz₀V, hz₀1, hz₀c⟩ := Sec1215.exists_ne_one_mem_centralizer S.hyp.sylow.1
    (Sec1215.le_of_hyp121 S.hyp S.hTL) hTV hV1
  obtain ⟨a, ha, c, hc, rfl⟩ := S.exists_decomp hz₀V
  have hfix : ∀ t ∈ T, t * (a * c) * t⁻¹ = a * c := fun t ht => by
    rw [Subgroup.mem_centralizer_iff.mp hz₀c t ht, mul_inv_cancel_right]
  obtain ⟨t, ht, ht1⟩ := Sec121Swap.exists_mem_not_normalizer S.hyp S.hTL
  obtain ⟨hs₁, hs₂⟩ := Sec121Swap.swap_of_hyp121 S.hyp (S.hTL ht) ht1
  have hswap : t * c * t⁻¹ = a ∧ t * a * t⁻¹ = c := by
    have e : t * c * t⁻¹ * (t * a * t⁻¹) = a * c := by
      calc t * c * t⁻¹ * (t * a * t⁻¹) = t * (c * a) * t⁻¹ := by group
        _ = t * (a * c) * t⁻¹ := by rw [S.comm (S.le₂ hc) (S.le₁ ha)]
        _ = a * c := hfix t ht
    exact S.decomp_unique (hs₂ c hc) ha (hs₁ a ha) hc e
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hz₀1
    have hc1 : c = 1 := by rw [← hswap.2]; group
    rw [hc1, mul_one]
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply ha1
    rw [← hswap.1]
    group
  have hT₁fix : ∀ t ∈ T ⊓ Subgroup.normalizer (V₁ : Set G), t * a * t⁻¹ = a ∧ t * c * t⁻¹ = c := by
    intro t ht
    have htM := S.hTL ht.1
    have htV₂ : t ∈ Subgroup.normalizer (V₂ : Set G) := by
      rcases S.fix_or_swap htM with ⟨-, h⟩ | ⟨h₁, -⟩
      · exact h
      · exfalso
        have h1 : t * a * t⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp ht.2 a).mp ha
        have h3 : t * a * t⁻¹ ∈ V₁ ⊓ V₂ := ⟨h1, (h₁ a).mp ha⟩
        rw [S.hyp.inf, Subgroup.mem_bot] at h3
        exact ha1 (by
          calc a = t⁻¹ * (t * a * t⁻¹) * t := by group
            _ = 1 := by rw [h3]; group)
    have e : t * a * t⁻¹ * (t * c * t⁻¹) = a * c := by
      calc t * a * t⁻¹ * (t * c * t⁻¹) = t * (a * c) * t⁻¹ := by group
        _ = a * c := hfix t ht.1
    exact S.decomp_unique ((Subgroup.mem_normalizer_iff.mp ht.2 a).mp ha) ha
      ((Subgroup.mem_normalizer_iff.mp htV₂ c).mp hc) hc e
  obtain ⟨v₁, hv₁⟩ := KGH91.exists_zpowers S.hyp S.hTL S.C₁
  have hav : a ∈ Subgroup.zpowers v₁ := by
    rw [← hv₁]
    refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have h1 := (hT₁fix t ht).1
    calc t * a = t * a * t⁻¹ * t := by group
      _ = a * t := by rw [h1]
  have hv₁V : v₁ ∈ V₁ := (hv₁ ▸ Subgroup.mem_zpowers v₁ : v₁ ∈ V₁ ⊓ _).1
  have hav₁ : a = v₁ := by
    have hv₁2 : v₁ ^ 2 = 1 := S.hVe.2 v₁ (S.le₁ hv₁V)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hav
    rcases zpow_eq_one_or_self hv₁2 k with h | h
    · exact absurd h ha1
    · exact h
  have hsing : KGH91.pairing S.C₁ S.C₂ a c = 0 := by
    rw [hav₁]
    exact S.pairing_eq_zero hv₁ hc fun t ht => (hT₁fix t ht).2
  refine ⟨a * c, hz₀V, hz₀c, hz₀1, ?_, ?_⟩
  · rw [S.mem_union_iff ha hc]
    rintro (h | h)
    · exact ha1 h
    · exact hc1 h
  · rw [S.nonsing_iff ha hc, hsing]
    exact zero_ne_one

theorem charTwo_centralizer {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) (huU : ¬ (u ∈ V₁ ∨ u ∈ V₂))
    (hus : ¬ IsNonsingular121 V₁ V₂ (KGH91.pairing S.C₁ S.C₂) u) :
    CharTwo (Subgroup.centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₀, hz₀V, hz₀c, hz₀1, hz₀U, hz₀s⟩ := S.exists_z₀
  obtain ⟨m, hm, hmu⟩ := (S.orbit_iff hz₀V hu hz₀1 hu1).mpr
    ⟨⟨fun h => absurd h hz₀U, fun h => absurd h huU⟩, ⟨fun h => absurd h hz₀s,
      fun h => absurd h hus⟩⟩
  have huo : orderOf u = 2 := orderOf_eq_prime (S.hVe.2 u hu) hu1
  have hT' : IsSylowTwoOf (cjSub m T) ⊤ := by
    have h1 := B2F.isSylowTwoOf_cjSub m S.sylow_top
    have h2 : cjSub m (⊤ : Subgroup G) = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj m).surjective
    rwa [h2] at h1
  have hle : cjSub m T ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hmu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have htz : t * z₀ = z₀ * t := Subgroup.mem_centralizer_iff.mp hz₀c t ht
    calc m * t * m⁻¹ * (m * z₀ * m⁻¹) = m * (t * z₀) * m⁻¹ := by group
      _ = m * (z₀ * t) * m⁻¹ := by rw [htz]
      _ = m * z₀ * m⁻¹ * (m * t * m⁻¹) := by group
  exact charTwo_of_isTwoLocal_of_isSylowTwoOf_le S.hyp.qtke.2.1 hT'
    (I4.isTwoLocal_centralizer huo) hle

theorem v_ne_one : a₀ * c₀ ≠ 1 := fun h => S.a₀_ne
  (S.decomp_unique S.ha₀ V₁.one_mem S.hc₀ V₂.one_mem (by rw [h, mul_one])).1

theorem orderOf_v : orderOf (a₀ * c₀) = 2 := orderOf_eq_prime (S.hVe.2 _ S.v_mem) S.v_ne_one

theorem isPGroup_zpowers_v : IsPGroup 2 (Subgroup.zpowers (a₀ * c₀)) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.orderOf_v, pow_one])

theorem charTwo_inf {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) (huU : ¬ (u ∈ V₁ ∨ u ∈ V₂))
    (hus : ¬ IsNonsingular121 V₁ V₂ (KGH91.pairing S.C₁ S.C₂) u) :
    CharTwo (Subgroup.centralizer ({u} : Set G) ⊓
      Subgroup.centralizer ({a₀ * c₀} : Set G)) := by
  have hle : Subgroup.zpowers (a₀ * c₀) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact S.comm S.v_mem hu
  have h := CharTwo.inf_centralizer (S.charTwo_centralizer hu hu1 huU hus) hle
    S.isPGroup_zpowers_v
  rwa [centralizer_zpowers_eq] at h

theorem zpowers_le_pCoreOf :
    Subgroup.zpowers (a₀ * c₀) ≤ pCoreOf 2 (Subgroup.centralizer ({a₀ * c₀} : Set G)) := by
  refine le_pCoreOf_of_le_normalizer ?_ ?_ S.isPGroup_zpowers_v
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rw [← I4.normalizer_zpowers_eq_centralizer S.orderOf_v]

theorem pCoreOf_ne_bot : pCoreOf 2 (Subgroup.centralizer ({a₀ * c₀} : Set G)) ≠ ⊥ := by
  intro h
  apply S.v_ne_one
  have : a₀ * c₀ ∈ (⊥ : Subgroup G) := h ▸ S.zpowers_le_pCoreOf (Subgroup.mem_zpowers _)
  exact Subgroup.mem_bot.mp this

theorem lv_le_normalizer_W :
    Sec1216Lv.lv L (a₀ * c₀) ≤ Subgroup.normalizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G) :=
  fun _ hl => mem_normalizer_sup
    (Sec121Swap.mem_normalizer_of_conj_mem fun _ ha => S.lv_conj_mem_W₁ hl ha)
    (Sec121Swap.mem_normalizer_of_conj_mem fun _ hc => S.lv_conj_mem_W₂ hl hc)

theorem commutator_eq :
    ⁅S.W₁ ⊔ S.W₂, Sec1216Lv.lv L (a₀ * c₀)⁆ = S.W₁ ⊔ S.W₂ := by
  refine le_antisymm ?_ ?_
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp S.lv_le_normalizer_W
  · refine sup_le (fun a ha => ?_) (fun c hc => ?_)
    · obtain ⟨b, hb, l, hl, rfl⟩ := S.exists_commutator₁ ha
      have e : b * (l * b * l⁻¹) = ⁅b, l⁆ := by
        rw [commutatorElement_def, S.inv_eq (S.le₁ hb.1)]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hb) hl
    · obtain ⟨d, hd, l, hl, rfl⟩ := S.exists_commutator₂ hc
      have e : d * (l * d * l⁻¹) = ⁅d, l⁆ := by
        rw [commutatorElement_def, S.inv_eq (S.le₂ hd.1)]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right hd) hl

theorem oddCoreIn_eq_bot : oddCoreIn (Subgroup.centralizer ({a₀ * c₀} : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a₀ * c₀} : Set G) with hH
  obtain ⟨u, huW, huV, hu1, huU, hus⟩ := S.exists_singular
  have hWH : S.W₁ ⊔ S.W₂ ≤ H := fun x hx => by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact S.comm (S.W_le_V hx) S.v_mem
  have hWe : IsElemAbelian 2 (S.W₁ ⊔ S.W₂) := Sec1216Gen.isElemAbelian_of_le S.hVe S.W_le_V
  have hW2 : IsPGroup 2 ↥(S.W₁ ⊔ S.W₂) := fun x =>
    ⟨1, Subtype.ext (by simpa using hWe.2 x x.2)⟩
  have hVO := a126_one (Sec1216Lv.lv_le_centralizer L (a₀ * c₀))
    (C2Nine.opResidual_eq_of_perfect (Sec1216Lv.lv_perfect L (a₀ * c₀))) hWH hW2 S.commutator_eq
    (fun p hp hp2 => (CFSG.SectionRank.pRank_mono hp.one_lt
      (CFSG.LieType.BorelTits.pCoreOf_le p H)).trans
        (pRank_le_two_of_pCoreOf_ne_bot S.hyp.qtke S.pCoreOf_ne_bot hp hp2))
    (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hWe)
  have hOu : oddCoreIn H ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hVO huW) y hy
  exact CharTwo.eq_bot_of_odd_card (S.charTwo_inf huV hu1 huU hus) (le_inf hOu (oddCoreIn_le H))
    (fun g hg => le_normalizer_oddCoreIn H hg.2) (odd_card_oddCoreIn H)

theorem not_le_centralizer {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) (huU : ¬ (u ∈ V₁ ∨ u ∈ V₂))
    (hus : ¬ IsNonsingular121 V₁ V₂ (KGH91.pairing S.C₁ S.C₂) u) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({a₀ * c₀} : Set G))) :
    ¬ K ≤ Subgroup.centralizer ({u} : Set G) := fun hle =>
  not_le_of_isComponentIn_of_charTwo (S.charTwo_inf hu hu1 huU hus) inf_le_right hK
    (le_inf hle hK.1)

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
