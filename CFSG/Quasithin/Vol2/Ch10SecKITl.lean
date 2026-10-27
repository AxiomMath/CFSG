module

public import CFSG.Quasithin.Vol2.Ch10SecKITk
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieCoprime
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKITd

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L X X₁ X₂ : Subgroup G} {n : ℕ}

theorem mem_normalizer_of_map_le {W : Subgroup G} {x : G}
    (h : W.map (MulAut.conj x).toMonoidHom ≤ W) : x ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge h (by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])

theorem le_normalizer_sup (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M) (hX : X ∈ lFamily T)
    (hXL : X ≤ L) (h : IsNatBlock X n) (hB : X ⊓ pCoreOf 2 L = blockU X) {V : Subgroup G}
    (hVQ : V ≤ pCoreOf 2 L) : X ≤ Subgroup.normalizer ((blockU X ⊔ V : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_of_map_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_sup_left
      ((Subgroup.mem_normalizer_iff.mp (h.le_normalizer_blockU hx) u).mp hu)
  · rintro _ ⟨v, hv, rfl⟩
    have hc : ⁅v, x⁆ ∈ blockU X := by
      rw [← hB]
      exact commutator_le_inf hT hL hX hXL (Subgroup.commutator_mem_commutator (hVQ hv) hx)
    have e : (MulAut.conj x).toMonoidHom v = ⁅v, x⁆⁻¹ * v := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((blockU X).inv_mem hc))
      (Subgroup.mem_sup_right hv)

omit [Finite G] in
theorem le_centralizer_of_le_sup (h : IsNatBlock X n) {Q W : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQW : Q ≤ Subgroup.normalizer (W : Set G))
    (hle : X ≤ Subgroup.centralizer (W : Set G) ⊔ Q) :
    X ≤ Subgroup.centralizer (W : Set G) := by
  have hQC : Q ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
    hQW.trans (Vol2Native.L239.Lie.normalizer_le_normalizer_centralizer W)
  have hrep : ∀ x ∈ X, ∃ q ∈ Q, ∀ w ∈ W, x * w * x⁻¹ = q * w * q⁻¹ := by
    intro x hx
    have hx' : x ∈ ((Subgroup.centralizer (W : Set G) ⊔ Q : Subgroup G) : Set G) := hle hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hQC] at hx'
    obtain ⟨c, hc, q, hq, rfl⟩ := hx'
    refine ⟨q, hq, fun w hw => ?_⟩
    have hqw : q * w * q⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hQW hq) w).mp hw
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hqw
    calc c * q * w * (c * q)⁻¹ = c * (q * w * q⁻¹) * c⁻¹ := by group
      _ = q * w * q⁻¹ := by rw [← h1]; group
  have hpow : ∀ x q : G, q ∈ Q → (∀ w ∈ W, x * w * x⁻¹ = q * w * q⁻¹) →
      ∀ m : ℕ, ∀ w ∈ W, x ^ m * w * (x ^ m)⁻¹ = q ^ m * w * (q ^ m)⁻¹ := by
    intro x q hq hxq m
    induction m with
    | zero => intro w _; simp
    | succ m ih =>
      intro w hw
      have hqw : q * w * q⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hQW hq) w).mp hw
      calc x ^ (m + 1) * w * (x ^ (m + 1))⁻¹ = x ^ m * (x * w * x⁻¹) * (x ^ m)⁻¹ := by group
        _ = x ^ m * (q * w * q⁻¹) * (x ^ m)⁻¹ := by rw [hxq w hw]
        _ = q ^ m * (q * w * q⁻¹) * (q ^ m)⁻¹ := ih _ hqw
        _ = q ^ (m + 1) * w * (q ^ (m + 1))⁻¹ := by group
  have hXN : X ≤ Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
    hle.trans (sup_le Subgroup.le_normalizer hQC)
  set N : Subgroup ↥X := (Subgroup.centralizer (W : Set G)).subgroupOf X with hN
  have hNn : N.Normal := by
    constructor
    intro a ha g
    rw [hN, Subgroup.mem_subgroupOf] at ha ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hXN g.2) a).mp ha
    simpa using this
  have h2 : IsPGroup 2 (↥X ⧸ N) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨q, hq, hxq⟩ := hrep x x.2
    obtain ⟨e, he⟩ := hQ ⟨q, hq⟩
    have hq1 : q ^ 2 ^ e = 1 := congrArg Subtype.val he
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    intro w hw
    have h3 := hpow x q hq hxq (2 ^ e) w hw
    rw [hq1, one_mul, inv_one, mul_one] at h3
    simp only [SubgroupClass.coe_pow]
    calc w * (x : G) ^ 2 ^ e = (x : G) ^ 2 ^ e * w * ((x : G) ^ 2 ^ e)⁻¹ * (x : G) ^ 2 ^ e := by
          rw [h3]
      _ = (x : G) ^ 2 ^ e * w := by group
  have htop := h.1.1 N h2
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ N := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem modO2Image_sup (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L) :
    modO2Image L (X₁ ⊔ X₂) = modO2Image L X₁ ⊔ modO2Image L X₂ := by
  unfold modO2Image
  rw [Subgroup.subgroupOf_sup hX₁L hX₂L, Subgroup.map_sup]

omit [Finite G] in
theorem le_pCoreOf_of_modO2Image_eq_bot {K : Subgroup G} (hKL : K ≤ L)
    (h : modO2Image L K = ⊥) : K ≤ pCoreOf 2 L := by
  intro k hk
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨k, hKL hk⟩ ∈ modO2Image L K :=
    ⟨⟨k, hKL hk⟩, hk, rfl⟩
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (C1Pack.coe_mem_pCoreOf_iff L _).mpr h1

theorem false_of_typeB_pair (hT : IsSylowTwoOf T M) (hL : L ∈ cComp M)
    (hX₁ : X₁ ∈ lFamily T) (hX₂ : X₂ ∈ lFamily T) (hX₁L : X₁ ≤ L) (hX₂L : X₂ ≤ L)
    (h₁ : IsNatBlock X₁ 2) (h₂ : IsNatBlock X₂ 2)
    (hB₁ : X₁ ⊓ pCoreOf 2 L = blockU X₁) (hB₂ : X₂ ⊓ pCoreOf 2 L = blockU X₂)
    (hsimp : IsSimpleGroup ↥(modO2Image L X₁ ⊔ modO2Image L X₂))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrS : r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 17 ∧ r ≠ 31 ∧ r ≠ 127)
    (hrd : r ∣ Nat.card ↥(modO2Image L X₁ ⊔ modO2Image L X₂)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 L with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hU₁Q : blockU X₁ ≤ Q := by rw [← hB₁]; exact inf_le_right
  have hU₂Q : blockU X₂ ≤ Q := by rw [← hB₂]; exact inf_le_right
  set W := blockU X₁ ⊔ blockU X₂ with hWdef
  have hWQ : W ≤ Q := sup_le hU₁Q hU₂Q
  have hW2 : IsPGroup 2 ↥W := hQ2.to_le hWQ
  have hQN₂ : Q ≤ Subgroup.normalizer (blockU X₂ : Set G) := by
    have := (pCoreOf_le_normalizer hT hL hX₂ hX₂L).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) X₂)
    have e₂ : pCoreOf 2 X₂ = blockU X₂ := h₂.2.2.2
    rwa [e₂] at this
  have hQN₁ : Q ≤ Subgroup.normalizer (blockU X₁ : Set G) := by
    have := (pCoreOf_le_normalizer hT hL hX₁ hX₁L).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) X₁)
    have e₁ : pCoreOf 2 X₁ = blockU X₁ := h₁.2.2.2
    rwa [e₁] at this
  have hcW : Nat.card ↥W ≤ 2 ^ 8 := by
    have hc := C5.card_sup_mul_card_inf_of_le_normalizer (hU₁Q.trans hQN₂)
    rw [h₁.card_blockU, h₂.card_blockU] at hc
    have hpos : 0 < Nat.card ↥(blockU X₁ ⊓ blockU X₂) := Nat.card_pos
    have : Nat.card ↥W ≤ Nat.card ↥W * Nat.card ↥(blockU X₁ ⊓ blockU X₂) :=
      Nat.le_mul_of_pos_right _ hpos
    rw [hc] at this
    norm_num at this ⊢
    exact this
  have hQW : Q ≤ Subgroup.normalizer (W : Set G) := fun q hq =>
    Vol2Native.L239.Lie.mem_normalizer_sup (hQN₁ hq) (hQN₂ hq)
  have hX₁W : X₁ ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_sup hT hL hX₁ hX₁L h₁ hB₁ hU₂Q
  have hX₂W : X₂ ≤ Subgroup.normalizer (W : Set G) := by
    rw [hWdef, sup_comm]
    exact le_normalizer_sup hT hL hX₂ hX₂L h₂ hB₂ hU₁Q
  set H := X₁ ⊔ X₂ with hHdef
  have hHL : H ≤ L := sup_le hX₁L hX₂L
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := sup_le hX₁W hX₂W
  set C := Subgroup.centralizer (W : Set G) with hCdef
  have hmono : ∀ {A B : Subgroup G}, A ≤ B → modO2Image L A ≤ modO2Image L B := by
    intro A B hAB
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
  have hHK : H ≤ Subgroup.normalizer ((H ⊓ C : Subgroup G) : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hh,
      Vol2Native.L239.Lie.normalizer_le_normalizer_centralizer W (hHW hh)⟩
  have hHbe : modO2Image L H = modO2Image L X₁ ⊔ modO2Image L X₂ := modO2Image_sup hX₁L hX₂L
  have hKb : modO2Image L (H ⊓ C) ≤ modO2Image L X₁ ⊔ modO2Image L X₂ :=
    hHbe ▸ hmono inf_le_left
  have hKbn : ((modO2Image L (H ⊓ C)).subgroupOf (modO2Image L X₁ ⊔ modO2Image L X₂)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKb, ← hHbe]
    have h1 : H.subgroupOf L ≤
        Subgroup.normalizer (((H ⊓ C).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hHK (Subgroup.mem_subgroupOf.mp hx)) y
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
  have hKQ : H ⊓ C ≤ Q := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((modO2Image L (H ⊓ C)).subgroupOf (modO2Image L X₁ ⊔ modO2Image L X₂)) with hb | ht
    · apply le_pCoreOf_of_modO2Image_eq_bot (inf_le_left.trans hHL)
      rw [Subgroup.subgroupOf_eq_bot] at hb
      exact (disjoint_self.mp (hb.mono_right hKb))
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at ht
      have h1 : X₁ ≤ (H ⊓ C) ⊔ Q := le_sup_of_xbar_le hX₁L (le_sup_left.trans ht)
      have h2 : X₁ ≤ C ⊔ Q := h1.trans (sup_le_sup_right inf_le_right Q)
      have h3 := le_centralizer_of_le_sup h₁ hQ2 hQW h2
      have h4 : blockU X₁ ≤ blockZ X₁ := fun u hu => ⟨hu,
        Subgroup.mem_centralizer_iff.mpr fun x hx =>
          (Subgroup.mem_centralizer_iff.mp (h3 hx) u (Subgroup.mem_sup_left hu)).symm⟩
      exact absurd h₁.1.2.2.2.2.1 (not_lt_of_ge h4)
  have : Fact r.Prime := ⟨hr⟩
  have hrH : r ∣ Nat.card ↥H := by
    refine hrd.trans ?_
    rw [← hHbe]
    refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrH
  have hgr : orderOf (g : G) = r := by rw [Subgroup.orderOf_coe, hg]
  have hne : ∃ w ∈ W, (g : G) * w * (g : G)⁻¹ ≠ w := by
    by_contra hcon
    push Not at hcon
    have hgC : (g : G) ∈ C := Subgroup.mem_centralizer_iff.mpr fun w hw => by
      have := hcon w hw
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    obtain ⟨e, he⟩ := hQ2 ⟨g, hKQ ⟨g.2, hgC⟩⟩
    have h1 : (g : G) ^ 2 ^ e = 1 := congrArg Subtype.val he
    have h2 : r ∣ 2 ^ e := hgr ▸ orderOf_dvd_of_pow_eq_one h1
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  obtain ⟨k, hk1, hk2, hdvd⟩ := dvd_two_pow_sub_one_of_act hW2 hr hr2 hgr (hHW g.2) hne
  have hk8 : k ≤ 8 := (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk2.trans hcW)
  obtain ⟨h3, h5, h7, h17, h31, h127⟩ := hrS
  rcases prime_dvd_two_pow_sub_one hr hk1 hk8 hdvd with h | h | h | h | h | h <;> contradiction

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
