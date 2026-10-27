module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

theorem le_normalizer_of_abelian {G : Type*} [Group G] {V W : Subgroup G}
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hWV : W ≤ V) :
    V ≤ normalizer (W : Set G) := by
  intro v hv
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [hVab v hv w (hWV hw), mul_inv_cancel_right]
    exact hw
  · intro hw
    have hwV : w ∈ V := by
      have h1 : v⁻¹ * (v * w * v⁻¹) * v ∈ V :=
        V.mul_mem (V.mul_mem (V.inv_mem hv) (hWV hw)) hv
      rwa [show v⁻¹ * (v * w * v⁻¹) * v = w by group] at h1
    rwa [hVab v hv w hwV, mul_inv_cancel_right] at hw

theorem exists_tinv_step {G : Type*} [Group G] [Finite G] {T V W : Subgroup G}
    (hT : IsPGroup 2 T) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hTV : T ≤ normalizer (V : Set G)) (hWV : W ≤ V) (hTW : T ≤ normalizer (W : Set G))
    (hWlt : W < V) :
    ∃ W' : Subgroup G, W ≤ W' ∧ W' ≤ V ∧ T ≤ normalizer (W' : Set G) ∧ W.relIndex W' = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hV2 x x.2)⟩
  set P := V ⊔ T with hP
  have hPp : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hVp hT hTV
  have hVP : V ≤ P := le_sup_left
  have hWP : W ≤ P := hWV.trans hVP
  have hPW : P ≤ normalizer (W : Set G) := sup_le (le_normalizer_of_abelian hVab hWV) hTW
  have hPV : P ≤ normalizer (V : Set G) := sup_le le_normalizer hTV
  set W₀ := W.subgroupOf P with hW₀
  set V₀ := V.subgroupOf P with hV₀
  have hW₀n : W₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWP).2 hPW
  have hV₀n : V₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).2 hPV
  set f := QuotientGroup.mk' W₀ with hf
  have hQp : IsPGroup 2 (↥P ⧸ W₀) := hPp.to_quotient W₀
  have hnil : Group.IsNilpotent (↥P ⧸ W₀) := hQp.isNilpotent
  set N := V₀.map f with hN
  have hNn : N.Normal := hV₀n.map f (QuotientGroup.mk'_surjective W₀)
  obtain ⟨v, hvV, hvW⟩ := Set.exists_of_ssubset hWlt
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hvW
    have h1 : f ⟨v, hVP hvV⟩ ∈ N := ⟨⟨v, hVP hvV⟩, mem_subgroupOf.2 hvV, rfl⟩
    rw [hbot, mem_bot, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_subgroupOf.1 h1
  obtain ⟨⟨x, hxN, hxZ⟩, hx1⟩ := (ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNne)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx2 : x ^ 2 = 1 := by
    obtain ⟨y, hy, rfl⟩ := hxN
    rw [← map_pow]
    have : y ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hV2 _ (mem_subgroupOf.1 hy))
    rw [this, map_one]
  have hox : orderOf x = 2 := orderOf_eq_prime hx2 hx1'
  set C := zpowers x with hC
  have hCn : C.Normal := Subgroup.normal_of_le_center ((zpowers_le).2 hxZ)
  set C' := C.comap f with hC'
  have hC'n : C'.Normal := hCn.comap f
  refine ⟨C'.map P.subtype, ?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨⟨w, hWP hw⟩, ?_, rfl⟩
    show f ⟨w, hWP hw⟩ ∈ C
    rw [hf, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hw)]
    exact one_mem _
  · have hCN : C ≤ N := (zpowers_le).2 hxN
    have h1 : C' ≤ V₀ := by
      calc C' ≤ N.comap f := comap_mono hCN
        _ = V₀ ⊔ f.ker := comap_map_eq f V₀
        _ = V₀ := by
          rw [hf, QuotientGroup.ker_mk']
          exact sup_eq_left.2 (fun y hy => mem_subgroupOf.2 (hWV (mem_subgroupOf.1 hy)))
    rintro _ ⟨y, hy, rfl⟩
    exact mem_subgroupOf.1 (h1 hy)
  · refine le_trans ?_ (le_normalizer_map P.subtype)
    intro t ht
    refine ⟨⟨t, (le_sup_right : T ≤ P) ht⟩, ?_, rfl⟩
    show (⟨t, _⟩ : ↥P) ∈ normalizer (C' : Set ↥P)
    rw [normalizer_eq_top_iff.2 hC'n]
    trivial
  · have hW : W = W₀.map P.subtype := by
      rw [hW₀, subgroupOf_map_subtype, inf_eq_left.2 hWP]
    rw [hW, relIndex_map_map_of_injective _ _ P.subtype_injective]
    have hk : f.ker = W₀ := QuotientGroup.ker_mk' W₀
    rw [← hk, relIndex_ker, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective W₀),
      hC, Nat.card_zpowers, hox]

variable {G : Type} [Group G] [Finite G]

theorem exists_tsub_succ {T V W : Subgroup G} {i n : ℕ} (hT : IsPGroup 2 T)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hTV : T ≤ normalizer (V : Set G)) (hVn : Nat.card V = 2 ^ n) (hW : IsTSub T V W i)
    (hi : i < n) : ∃ W' : Subgroup G, IsTSub T V W' (i + 1) ∧ W ≤ W' := by
  obtain ⟨hWV, hWc, hTW⟩ := hW
  have hlt : W < V := by
    refine lt_of_le_of_ne hWV fun h => ?_
    have : 2 ^ i = 2 ^ n := by rw [← hWc, ← hVn, h]
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  obtain ⟨W', hWW', hW'V, hTW', hidx⟩ := exists_tinv_step hT hV2 hVab hTV hWV hTW hlt
  refine ⟨W', ⟨hW'V, ?_, hTW'⟩, hWW'⟩
  have h1 := relIndex_mul_card W W'
  rw [hidx, inf_eq_left.2 hWW', hWc] at h1
  rw [← h1, pow_succ, mul_comm]

theorem exists_tsub {T V : Subgroup G} {n : ℕ} (hT : IsPGroup 2 T)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hTV : T ≤ normalizer (V : Set G)) (hVn : Nat.card V = 2 ^ n) :
    ∀ i ≤ n, ∃ W : Subgroup G, IsTSub T V W i := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨⊥, bot_le, by rw [Subgroup.card_bot, pow_zero], ?_⟩
    rw [normalizer_eq_top_iff.2 inferInstance]
    exact le_top
  | succ i ih =>
    intro hi
    obtain ⟨W, hW⟩ := ih (by omega)
    obtain ⟨W', hW', -⟩ := exists_tsub_succ hT hV2 hVab hTV hVn hW (by omega)
    exact ⟨W', hW'⟩

theorem exists_tsub_two_of_one {T V V₁ : Subgroup G} {n : ℕ} (hT : IsPGroup 2 T)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hTV : T ≤ normalizer (V : Set G)) (hVn : Nat.card V = 2 ^ n) (hn : 2 ≤ n)
    (hV₁ : IsTSub T V V₁ 1) : ∃ V₂ : Subgroup G, IsTSub T V V₂ 2 ∧ V₁ ≤ V₂ :=
  exists_tsub_succ hT hV2 hVab hTV hVn hV₁ (by omega)

theorem card_and_sq_of_binaryNaturalSL {V : Type*} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {n : ℕ} (h : BinaryNaturalSL H ⊤ ⊥ n 1) :
    Nat.card V = 2 ^ n ∧ ∀ v : V, v ^ 2 = 1 := by
  obtain ⟨K, _, _, hK, π, -, -, -, -, -, -, -, β, hβs, hβ1, -⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβ1 u).1 hu
    exact Subtype.ext (by simpa using this)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hAmb : ∀ x : Multiplicative (Fin n → K), x ^ 2 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_smul]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hsq : ∀ y : ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL n K)).sec ⧸
      (FFModel.nat (Assembly.LowTwoRank.StatedSL n K)).ker.subgroupOf
        (FFModel.nat (Assembly.LowTwoRank.StatedSL n K)).sec, y ^ 2 = 1 := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_pow]
    have : m ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hAmb _)
    rw [this, QuotientGroup.mk_one]
  refine ⟨?_, fun v => ?_⟩
  · have e1 := Nat.card_eq_of_bijective β ⟨hβi, hβs⟩
    rw [Subgroup.card_top] at e1
    rw [e1]
    change Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤) = 2 ^ n
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top]
    change Nat.card (Fin n → K) = 2 ^ n
    rw [Nat.card_fun, Nat.card_fin, hK, pow_one]
  · have h1 : β (⟨v, trivial⟩ ^ 2) = 1 := by rw [map_pow, hsq]
    have h2 := hβi (h1.trans (map_one β).symm)
    have h3 := congrArg Subtype.val h2
    simpa using h3

theorem Hyp1281One.card_sq {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n) :
    Nat.card V = 2 ^ n ∧ (∀ v ∈ V, v ^ 2 = 1) ∧ ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  obtain ⟨hc, hnat⟩ := h.natural
  obtain ⟨hcard, hsq⟩ := card_and_sq_of_binaryNaturalSL hnat
  refine ⟨hcard, fun v hv => ?_, fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)⟩
  have := hsq ⟨v, hv⟩
  simpa using congrArg Subtype.val this

theorem Hyp1223.le_and_normalizes (h1222 : Stmt12_2_2) {T L V : Subgroup G}
    (h : Hyp1223 G T L V) : V ≤ T ∧ T ≤ normalizer (V : Set G) := by
  rcases h1222 G T h.simple h.nonabelian h.qtke h.sylow with hAlt | h3
  · exact absurd hAlt h.notAlt
  obtain ⟨-, -, hall⟩ := h3 L h.maximal h.faithful h.quasisimple
  exact ⟨(hall V h.irrPlus).1.1, (hall V h.irrPlus).1.2.1⟩

theorem exists_v1_of_hyp1281One (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) : ∃ V₁ : Subgroup G, IsTSub T V V₁ 1 := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hn : 1 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  exact exists_tsub h.hyp.sylow.1 hsq hab hTV hcard 1 hn

theorem exists_v2_of_hyp1281One (h1222 : Stmt12_2_2) {T L V V₁ : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hV₁ : IsTSub T V V₁ 1) :
    ∃ V₂ : Subgroup G, IsTSub T V V₂ 2 ∧ V₁ ≤ V₂ := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hn : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  exact exists_tsub_two_of_one h.hyp.sylow.1 hsq hab hTV hcard hn hV₁

@[expose] def Exist1282g : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ∃ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G)

end CFSG.Quasithin.H13
