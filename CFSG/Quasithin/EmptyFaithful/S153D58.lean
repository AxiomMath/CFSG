module

public import CFSG.Quasithin.EmptyFaithful.S153D57
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCases2
public import CFSG.Quasithin.EmptyFaithful.S1421L11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.S14110
open scoped commutatorElement

namespace S153D

section Generic

variable {G : Type} [Group G]

theorem a4_orders : ∀ g : alternatingGroup (Fin 4), g ^ 2 = 1 ∨ g ^ 3 = 1 := by decide

theorem a4_center : ∀ g : alternatingGroup (Fin 4),
    (∀ l : alternatingGroup (Fin 4), g * l = l * g) → g = 1 := by decide

theorem a4_card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_sup_eq_mul {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hbij : Function.Bijective
      (fun p : A × B => (⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) := by
    constructor
    · intro p q h
      have h' : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val h
      have h1 : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
        calc (q.1 : G)⁻¹ * p.1 = (q.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
          _ = (q.1 : G)⁻¹ * (q.1 * q.2) * (p.2 : G)⁻¹ := by rw [h']
          _ = q.2 * (p.2 : G)⁻¹ := by group
      have hmem : (q.1 : G)⁻¹ * p.1 ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem q.1.2) p.1.2, h1 ▸ B.mul_mem q.2.2 (B.inv_mem p.2.2)⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have ha : (p.1 : G) = q.1 := by
        calc (p.1 : G) = (q.1 : G) * ((q.1 : G)⁻¹ * p.1) := by group
          _ = q.1 := by rw [hmem, mul_one]
      have hb : (p.2 : G) = q.2 := by
        have h2 : q.2 * (p.2 : G)⁻¹ = 1 := h1 ▸ hmem
        calc (p.2 : G) = (q.2 * (p.2 : G)⁻¹)⁻¹ * q.2 := by group
          _ = q.2 := by rw [h2, inv_one, one_mul]
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · rintro ⟨x, hx⟩
      have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right A B (le_normalizer_of_comm hAB)] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

theorem le_oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper X ≤ oTwoUpper (oTwoUpper X) := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxX, hxo⟩
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hxX hxo) hxo

theorem a4_mem_W_of_mem_centralizer {X W : Subgroup G} {c : G} (h : A4Data X W c) {x : G}
    (hx : x ∈ X) (hxc : x ∈ Subgroup.centralizer (W : Set G)) : x ∈ W := by
  obtain ⟨w, hw, k, rfl⟩ := h.mem_decomp hx
  have hck : ∀ u ∈ W, c ^ k * u * (c ^ k)⁻¹ = u := by
    intro u hu
    have h1 : w * c ^ k * u = u * (w * c ^ k) := (Subgroup.mem_centralizer_iff.1 hxc u hu).symm
    have h2 : w * u = u * w := h.comm w hw u hu
    calc c ^ k * u * (c ^ k)⁻¹ = w⁻¹ * (w * c ^ k * u) * (c ^ k)⁻¹ := by group
      _ = w⁻¹ * (u * (w * c ^ k)) * (c ^ k)⁻¹ := by rw [h1]
      _ = w⁻¹ * (u * w) * (c ^ k * (c ^ k)⁻¹) := by group
      _ = w⁻¹ * (w * u) := by rw [← h2, mul_inv_cancel, mul_one]
      _ = u := by group
  have h1 : c ^ k = 1 := h.zpow_c_eq_one_of_centralizes hck
  rw [h1, mul_one]
  exact hw

variable [Finite G]

theorem a4Data_of_isAlt {A W : Subgroup G} {c : G} (e : ↥A ≃* alternatingGroup (Fin 4))
    (hWA : W ≤ A) (hW4 : Nat.card W = 4) (hWsq : ∀ w ∈ W, w ^ 2 = 1)
    (hWc : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u) (hcA : c ∈ A) (hc3 : c ^ 3 = 1)
    (hcN : c ∈ Subgroup.normalizer (W : Set G)) (hfpf : ∀ w ∈ W, w ≠ 1 → c * w * c⁻¹ ≠ w) :
    A4Data A W c := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWfin : Finite W := Nat.finite_of_card_ne_zero (by rw [hW4]; norm_num)
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ W, u ≠ 1 := by
    have : 1 < Nat.card W := by rw [hW4]; norm_num
    have hnt : Nontrivial W := (Finite.one_lt_card_iff_nontrivial (α := W)).1 this
    obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : W)
    exact ⟨u, hu, fun h' => hu1 (Subtype.ext h')⟩
  have hc1 : c ≠ 1 := fun h' => hfpf u hu hu1 (by rw [h']; simp)
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcard12 : Nat.card A = 12 := by
    rw [Nat.card_congr e.toEquiv]
    exact a4_card
  have hsup : W ⊔ Subgroup.zpowers c ≤ A := sup_le hWA (Subgroup.zpowers_le.2 hcA)
  have h4 : 4 ∣ Nat.card ↥(W ⊔ Subgroup.zpowers c) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : W ≤ W ⊔ Subgroup.zpowers c)
    rwa [hW4] at this
  have h3 : 3 ∣ Nat.card ↥(W ⊔ Subgroup.zpowers c) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers c ≤ W ⊔ Subgroup.zpowers c)
    rwa [Nat.card_zpowers, hord] at this
  have h12 : 12 ∣ Nat.card ↥(W ⊔ Subgroup.zpowers c) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 3) h4 h3
  have hle : 12 ≤ Nat.card ↥(W ⊔ Subgroup.zpowers c) := Nat.le_of_dvd Nat.card_pos h12
  refine ⟨hWA, hW4, hWsq, hWc, hcA, hord, hcN, hfpf, ?_, hcard12, ?_⟩
  · exact (Subgroup.eq_of_le_of_card_ge hsup (by rw [hcard12]; exact hle)).symm
  · intro g hg hcen
    have h1 : e ⟨g, hg⟩ = 1 := by
      refine a4_center _ fun l => ?_
      obtain ⟨l', rfl⟩ := e.surjective l
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hcen l' l'.2))
    have h2 : (⟨g, hg⟩ : ↥A) = 1 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2

end Generic

theorem card_cj_153 {G : Type} [Group G] (g : G) (X : Subgroup G) :
    Nat.card ↥(cj g X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

end S153D

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

open S153D in
theorem pCoreOf_Y153_le_VZ_of_isAlt (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t)
    (hA : IsAlt 4 ↥(oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))) :
    pCoreOf 2 (Y153 Mc M) ≤ VZ T M := by
  classical
  obtain ⟨e⟩ := hA
  set Y : Subgroup G := Y153 Mc M with hYdef
  set V : Subgroup G := VZ T M with hVdef
  set C₁ : Subgroup G := Y ⊓ Subgroup.centralizer (V₁ : Set G) with hC₁def
  set A : Subgroup G := oTwoUpper C₁ with hAdef
  have hYM : Y ≤ M := Y153_le Mc M
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := h.le_normalizer
  have hMY : M ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_Y153 Mc M
  have hVY : V ≤ Y := h.VZ_le_Y153 h113
  have hVc : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
    have := h.elemAbelian.1.1.1 ⟨u, hu⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := h.elemAbelian.2
  obtain ⟨hYN₁, hYN₂⟩ := h.Y153_le_normalizer_V h113 D
  have hAC : A ≤ C₁ := oTwoUpper_le C₁
  have hAY : A ≤ Y := hAC.trans inf_le_left
  have hAC₁ : A ≤ Subgroup.centralizer (V₁ : Set G) := hAC.trans inf_le_right
  have ht : t ∈ M := D.t_mem
  have hcj₂ : cj t V₂ = V₁ := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_cj_153, D.card₂, D.card₁])
    obtain ⟨v, hv, rfl⟩ := mem_cj_iff.1 hx
    exact D.swap₂ v hv
  have hcj₁ : cj t V₁ = V₂ := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_cj_153, D.card₂, D.card₁])
    obtain ⟨v, hv, rfl⟩ := mem_cj_iff.1 hx
    exact D.swap₁ v hv
  have hV₂A : V₂ ≤ A := by
    have hV₂C : V₂ ≤ C₁ := fun u hu =>
      ⟨(D.le₂.trans hVY) hu, Subgroup.mem_centralizer_iff.2 fun v hv => hVc v (D.le₁ hv) u (D.le₂ hu)⟩
    have hcomm : ⁅V₂, A⁆ = V₂ := h.commutator_V₂_Yplus h113 D
    have hle : ⁅V₂, A⁆ ≤ A := by
      refine Subgroup.commutator_le.2 fun u hu a ha => ?_
      have hn : u ∈ Subgroup.normalizer (C₁ : Set G) := Subgroup.le_normalizer (hV₂C hu)
      have h1 : u * a * u⁻¹ ∈ A := conj_mem_oTwoUpper hn ha
      rw [commutatorElement_def]
      exact A.mul_mem h1 (A.inv_mem ha)
    exact hcomm ▸ hle
  obtain ⟨y, hyA, hy3C, hyfpf⟩ := h.exists_Yplus_fpf h113 D
  have hord : ∀ g ∈ A, g ^ 2 = 1 ∨ g ^ 3 = 1 := by
    intro g hg
    rcases a4_orders (e ⟨g, hg⟩) with h2 | h3
    · left
      have h4 : e (⟨g, hg⟩ ^ 2) = e 1 := by rw [map_pow, h2, map_one]
      have h5 := congrArg Subtype.val (e.injective h4)
      simpa using h5
    · right
      have h4 : e (⟨g, hg⟩ ^ 3) = e 1 := by rw [map_pow, h3, map_one]
      have h5 := congrArg Subtype.val (e.injective h4)
      simpa using h5
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u ∈ V₂, u ≠ 1 := by
    have hV₂fin : Finite V₂ := Nat.finite_of_card_ne_zero (by rw [D.card₂]; norm_num)
    have : 1 < Nat.card V₂ := by rw [D.card₂]; norm_num
    have hnt : Nontrivial V₂ := (Finite.one_lt_card_iff_nontrivial (α := V₂)).1 this
    obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : V₂)
    exact ⟨u, hu, fun h' => hu1 (Subtype.ext h')⟩
  have hy3 : y ^ 3 = 1 := by
    rcases hord y hyA with h2 | h3
    · exfalso
      have h3 : y ^ 3 = y := by rw [pow_succ, h2, one_mul]
      rw [h3] at hy3C
      apply hyfpf u₀ hu₀ hu₀1
      have h4 := Subgroup.mem_centralizer_iff.1 hy3C u₀ hu₀
      calc y * u₀ * y⁻¹ = (u₀ * y) * y⁻¹ := by rw [h4]
        _ = u₀ := by group
    · exact h3
  have hMC₂ : M ⊓ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (V₂ : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right V (M ⊓ Subgroup.centralizer (V₁ : Set G))
    rwa [D.comm₂] at this
  have hAN₂ : A ≤ Subgroup.normalizer (V₂ : Set G) := fun x hx => hMC₂ ⟨hYM (hAY hx), hAC₁ hx⟩
  have hAD : A4Data A V₂ y :=
    a4Data_of_isAlt e hV₂A D.card₂ (fun w hw => hVsq w (D.le₂ hw))
      (fun u hu v hv => hVc u (D.le₂ hu) v (D.le₂ hv)) hyA hy3 (hAN₂ hyA) hyfpf
  set B : Subgroup G := cj t A with hBdef
  have hBD : A4Data B V₁ (t * y * t⁻¹) := by
    have h1 : A4Data (cj t A) (cj t V₂) (t * y * t⁻¹) := hAD.map (MulAut.conj t)
    rwa [hcj₂] at h1
  have hBY : B ≤ Y := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_cj_iff.1 hx
    exact (Subgroup.mem_normalizer_iff.1 (hMY ht) a).1 (hAY ha)
  have hBC₂ : B ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_cj_iff.1 hx
    exact conj_mem_centralizer_of_cj hcj₁ (hAC₁ ha)
  have hYNA : Y ≤ Subgroup.normalizer (A : Set G) :=
    (S1421.le_normalizer_inf_centralizer hYN₁).trans (normalizer_le_normalizer_oTwoUpper C₁)
  have hYNB : Y ≤ Subgroup.normalizer (B : Set G) := by
    intro g hg
    have hg' : t⁻¹ * g * t ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.1 (hMY (M.inv_mem ht)) g).1 hg
      simpa using this
    have h1 : cj (t⁻¹ * g * t) A = A := mem_normalizer_iff_cj.1 (hYNA hg')
    rw [mem_normalizer_iff_cj]
    calc cj g (cj t A) = cj (g * t) A := cj_cj g t A
      _ = cj (t * (t⁻¹ * g * t)) A := by congr 1; group
      _ = cj t (cj (t⁻¹ * g * t) A) := cj_mul _ _ _
      _ = cj t A := by rw [h1]
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    have h1 : x ∈ V₂ := a4_mem_W_of_mem_centralizer hAD hxA (hBC₂ hxB)
    have h2 : x ∈ V₁ := a4_mem_W_of_mem_centralizer hBD hxB (hAC₁ hxA)
    have h3 : x ∈ V₁ ⊓ V₂ := ⟨h2, h1⟩
    rwa [D.inf] at h3
  have hABc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ A := by
      have h2 : b * a⁻¹ * b⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.1 (hYNA (hBY hb)) a⁻¹).1 (A.inv_mem ha)
      have h3 : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [h3]
      exact A.mul_mem ha h2
    have h3 : a * b * a⁻¹ * b⁻¹ ∈ B := by
      have h4 : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hYNB (hAY ha)) b).1 hb
      exact B.mul_mem h4 (B.inv_mem hb)
    have h5 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨h1, h3⟩
    rw [hinf, Subgroup.mem_bot] at h5
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h5, one_mul]
  have hcardP : Nat.card ↥(A ⊔ B) = 144 := by
    rw [card_sup_eq_mul hABc hinf, hAD.card_X, hBD.card_X]
  have hPY : A ⊔ B ≤ Y := sup_le hAY hBY
  have hcardY : Nat.card ↥Y = 9 * Nat.card ↥(Y ⊓ Subgroup.centralizer (V : Set G)) :=
    h.card_Y153 h113
  have hcardC₁ : Nat.card ↥C₁ = 3 * Nat.card ↥(Y ⊓ Subgroup.centralizer (V : Set G)) :=
    h.card_Yplus_base h113 D
  obtain ⟨k, hk⟩ := S1421.relIndex_oTwoUpper_two_pow C₁
  have h1 := Subgroup.relIndex_mul_card A C₁
  rw [inf_eq_left.2 hAC, hk, hAD.card_X] at h1
  have h2 := Subgroup.relIndex_mul_card (A ⊔ B) Y
  rw [inf_eq_left.2 hPY, hcardP] at h2
  have hr : (A ⊔ B).relIndex Y ∣ 2 ^ k := by
    refine Dvd.intro 4 ?_
    generalize 2 ^ k = X at *
    omega
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hr
  have hPn : Y ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_sup A B ⟨hYNA hg, hYNB hg⟩
  have hN : ((A ⊔ B).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).2 hPn
  have hYid : Y ≤ oTwoUpper Y := le_oTwoUpper_oTwoUpper _
  have hYP : Y ≤ A ⊔ B := by
    have hmem : ∀ x ∈ Y, ∃ m : ℕ, x ^ 2 ^ m ∈ A ⊔ B := by
      intro x hx
      refine ⟨j, ?_⟩
      have h3 : (⟨x, hx⟩ : ↥Y) ^ ((A ⊔ B).subgroupOf Y).index ∈ (A ⊔ B).subgroupOf Y :=
        Subgroup.pow_index_mem _ _
      rw [Subgroup.mem_subgroupOf] at h3
      have h4 : ((A ⊔ B).subgroupOf Y).index = 2 ^ j := hj
      rw [h4] at h3
      simpa using h3
    exact hYid.trans (oTwoUpper_le_of_pow_mem hmem)
  intro q hq
  have hqY : q ∈ Y := pCoreOf_le 2 Y hq
  have hq' : q ∈ ((A ⊔ B : Subgroup G) : Set G) := hYP hqY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B (le_normalizer_of_comm hABc)] at hq'
  obtain ⟨a, ha, b, hb, rfl⟩ := hq'
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 Y) ⟨a * b, hq⟩
  have hn' : (a * b) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hpow : a ^ 2 ^ n * b ^ 2 ^ n = 1 := by
    rw [← Commute.mul_pow (hABc a ha b hb)]
    exact hn'
  have h3 : a ^ 2 ^ n ∈ A ⊓ B := ⟨A.pow_mem ha _, by
    have : a ^ 2 ^ n = (b ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [this]
    exact B.inv_mem (B.pow_mem hb _)⟩
  rw [hinf, Subgroup.mem_bot] at h3
  have h4 : b ^ 2 ^ n = 1 := by
    rw [h3, one_mul] at hpow
    exact hpow
  have haW : a ∈ V₂ := hAD.mem_W_of_two_pow ha h3
  have hbW : b ∈ V₁ := hBD.mem_W_of_two_pow hb h4
  exact V.mul_mem (D.le₂ haW) (D.le₁ hbW)

end Hyp153

namespace S153D

theorem input15343NotA4_of_nine (h113 : StageLemma14113)
    (hnine : ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Hyp153 G T Mc M →
      VZ T M < pCoreOf 2 (Y153 Mc M)) : Input15343NotA4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hA
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have h2 : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := c.facts25.case_two.2
  rw [h2] at hA
  have hle : pCoreOf 2 (Y153 Mc M) ≤ VZ T M :=
    hh.hyp.pCoreOf_Y153_le_VZ_of_isAlt h113 hh.decomp hA
  exact lt_irrefl _ (lt_of_lt_of_le (hnine G T Mc M hh.hyp) hle)

end S153D

end CFSG.Quasithin
