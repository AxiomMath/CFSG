module

public import CFSG.Quasithin.H13.U3Basic
public import CFSG.Quasithin.SteinbergBMIntersectingConjugatesHulls
public import CFSG.Quasithin.SteinbergBMTIPairCalculus
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Module CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative Pointwise

variable {G : Type*} [Group G]

theorem conj_mem_normalizer_of_mem_normalizer_conjugate {V : Subgroup G} {g u : G}
    (hu : u ∈ normalizer (CFSG.conjugate V g : Set G)) :
    g * u * g⁻¹ ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff] at hu ⊢
  intro y
  have h1 := hu (g⁻¹ * y * g)
  rw [mem_conjugate_iff', mem_conjugate_iff'] at h1
  rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group,
    show g * (u * (g⁻¹ * y * g) * u⁻¹) * g⁻¹ = g * u * g⁻¹ * y * (g * u * g⁻¹)⁻¹ by group] at h1

theorem six_profile_conjugate_codimension_two_centralization [Finite G] (T : Sylow 2 G)
    {V : Subgroup G} [IsElementaryAbelian 2 V] (hV : Nat.card V = 64)
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (b : LinearMap.BilinForm (ZMod 2) (Additive V))
    (hprof : QTBinarySixProfile b (u3ConjLin V (normalizer (V : Set G)) le_rfl).range)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∀ y ∈ V, y ≠ 1 → ∃ n ∈ normalizer (V : Set G), n⁻¹ * x * n = y)
    {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hJ : ∀ x ∈ ⨆ h ∈ centralizer ({z} : Set G), CFSG.conjugate V h,
      ∀ y ∈ ⨆ h ∈ centralizer ({z} : Set G), CFSG.conjugate V h, x * y = y * x)
    (hcent : ∀ F : Subgroup G, F ≤ V → F.relIndex V ≤ 8 →
      centralizer (F : Set G) ≤ normalizer (V : Set G)) :
    (∀ (g : G) (A : Subgroup G), A ≤ (T : Subgroup G) ⊓ CFSG.conjugate V g →
      A.relIndex (CFSG.conjugate V g) ≤ 4 → ⁅A, V⁆ = ⊥) ∧
    ∀ W : Subgroup G, (∃ g : G, W = CFSG.conjugate V g) → W ≤ normalizer (V : Set G) →
      ⁅W, V⁆ = ⊥ := by
  classical
  set N := normalizer (V : Set G) with hN
  set φ := u3ConjLin V N le_rfl with hφ
  obtain ⟨-, hb, halt, hpres, hinv, hprofE⟩ := hprof
  obtain ⟨hVc, hV2⟩ := SteinbergBM.elementaryAbelian_two_facts (inferInstance :
    IsElementaryAbelian 2 V)
  have hV6 : Nat.card V = 2 ^ 6 := hV.trans (by norm_num)
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have hint : ∀ x : G, V ⊓ CFSG.conjugate V x ≠ ⊥ → ⁅V, CFSG.conjugate V x⁆ = ⊥ :=
    (SteinbergBS.element_centralizer_orbit_commuting_propagation le_rfl htrans hzV hz1).2 hJ
  have hcent' : ∀ E : Subgroup G, E ≤ V → E.relIndex V < 2 ^ 4 →
      centralizer (E : Set G) ≤ normalizer (V : Set G) := by
    intro E hEV hE
    obtain ⟨k, -, hk⟩ := exists_relIndex_eq_two_pow hEV hV6
    refine hcent E hEV ?_
    rw [hk] at hE ⊢
    by_contra h
    push Not at h
    have h1 : 2 ^ 4 ≤ 2 ^ k := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      by_contra h2
      push Not at h2
      have h3 : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h3
      omega
    omega
  have analysis : ∀ (g : G) (A : Subgroup G) (k : ℕ), A ≤ CFSG.conjugate V g → A ≤ N →
      A.relIndex (CFSG.conjugate V g) = 2 ^ k → k ≤ 2 → ⁅V, A⁆ ≠ ⊥ →
      V ⊓ normalizer (CFSG.conjugate V g : Set G) = V ⊓ centralizer (A : Set G) ∧
      IsElementaryAbelian 2 ((A.subgroupOf N).map φ) ∧
      Nat.card ((A.subgroupOf N).map φ) = 8 ∧
      Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) = 8 ∧
      linFix ((A.subgroupOf N).map φ) = linComm ((A.subgroupOf N).map φ) ∧
      (∃ e ∈ (A.subgroupOf N).map φ, e ≠ 1 ∧ linRank e = 2) ∧
      ∀ B ≤ A, B.relIndex A < 2 ^ (4 - k) →
        V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G) := by
    intro g A k hAW hAN hk hk2 hVA
    obtain ⟨-, hUA, -, hB, -⟩ := SteinbergBS.conjugate_normalizer_fixed_space_stability (p := 2)
      (r := 4) hcent' hint g hAW hAN hk (by omega) hVA
    set E := (A.subgroupOf N).map φ with hE
    have hfixE : linFix E = subOf V (centralizer (A : Set G)) := linFix_map_subgroupOf hAN
    obtain ⟨hWc, hW2⟩ := SteinbergBM.elementaryAbelian_two_facts
      (isElementaryAbelian_conjugate V g)
    have hEΓ : E ≤ φ.range := map_le_range φ _
    have hEbot : E ≠ ⊥ := by
      intro h
      apply hVA
      rw [commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [mem_centralizer_iff]
      intro a ha
      have h1 : φ ⟨a, hAN ha⟩ ∈ E := ⟨⟨a, hAN ha⟩, ha, rfl⟩
      rw [h, mem_bot, u3ConjLin_eq_one_iff] at h1
      exact (mem_centralizer_iff.1 h1 v hv).symm
    have hEab : IsElementaryAbelian 2 E := by
      refine SteinbergBM.isElementaryAbelian_two_of ?_ ?_
      · rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hWc _ (hAW (mem_subgroupOf.1 hs)) _ (hAW (mem_subgroupOf.1 hs')))
      · rintro _ ⟨s, hs, rfl⟩
        rw [← map_mul, show s * s = 1 from Subtype.ext (hW2 _ (hAW (mem_subgroupOf.1 hs))),
          map_one]
    have h2k : 2 < 2 ^ (4 - k) :=
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (4 - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hBA : ∀ B ≤ A, B.relIndex A < 2 ^ (4 - k) →
        V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G) :=
      fun B hBA hBidx => (hB B hBA hBidx).trans hUA
    have hidx : ∀ F ≤ E, F.relIndex E = 2 → linFix F = linFix E := by
      intro F hFE hFidx
      obtain ⟨B, hBA', hBidx, hBfix⟩ := exists_le_relIndex_linFix hAN hFE
      rw [hBfix, hfixE]
      exact subOf_congr (hBA B hBA' (by rw [hBidx, hFidx]; exact h2k))
    obtain ⟨hE8, hfc, hdim, he⟩ := hprofE E hEΓ hEbot hEab hidx
    have hcard : Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) = 8 := by
      rw [← card_subOf, ← hfixE, Module.natCard_eq_pow_finrank (K := ZMod 2), hdim,
        Nat.card_zmod]
      norm_num
    exact ⟨hUA, hEab, hE8, hcard, hfc, he, hBA⟩
  have hk1 : ∀ (g : G) (A : Subgroup G) (k : ℕ), A ≤ (T : Subgroup G) ⊓ CFSG.conjugate V g →
      A.relIndex (CFSG.conjugate V g) = 2 ^ k → k ≤ 1 → ⁅A, V⁆ = ⊥ := by
    intro g A k hA hk hk1
    by_contra hAV
    have hVA : ⁅V, A⁆ ≠ ⊥ := by rwa [commutator_comm]
    have hAN : A ≤ N := (hA.trans inf_le_left).trans hTN
    obtain ⟨-, hEab, hE8, -, -, ⟨e, heE, he1, herank⟩, hBc⟩ :=
      analysis g A k (hA.trans inf_le_right) hAN hk (by omega) hVA
    obtain ⟨F, hFE, hFidx, hlt⟩ := exists_linFix_lt_of_card_eq_eight b hb halt hEab
      (fun e he => hpres e (map_le_range _ _ he)) hE8 ⟨e, heE, he1, herank.le⟩
    obtain ⟨B, hBA, hBidx, hBfix⟩ := exists_le_relIndex_linFix hAN hFE
    have h48 : 4 < 2 ^ (4 - k) :=
      calc 4 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (4 - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : linFix F = linFix ((A.subgroupOf N).map φ) := by
      rw [hBfix, linFix_map_subgroupOf hAN]
      exact subOf_congr (hBc B hBA (by rw [hBidx]; exact lt_of_le_of_lt hFidx h48))
    exact hlt.ne h1.symm
  have hconjN : ∀ W : Subgroup G, (∃ g : G, W = CFSG.conjugate V g) → W ≤ N →
      ⁅W, V⁆ = ⊥ := by
    rintro W ⟨g, rfl⟩ hWN
    have hWp : IsPGroup 2 (CFSG.conjugate V g) :=
      IsPGroup.of_card ((card_conjugate V g).trans hV6)
    have hW' : IsPGroup 2 ((CFSG.conjugate V g).subgroupOf N) :=
      hWp.of_equiv (subgroupOfEquivOfLe hWN).symm
    obtain ⟨Q, hQ⟩ := hW'.exists_le_sylow
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N (T.subtype hTN) Q
    rw [Sylow.smul_subtype] at hn
    have hnT : ∀ w ∈ CFSG.conjugate V g, (n : G)⁻¹ * w * n ∈ (T : Subgroup G) := by
      intro w hw
      have h1 : (⟨w, hWN hw⟩ : N) ∈ (Q : Subgroup N) := hQ hw
      rw [← hn, Sylow.coe_subtype, mem_subgroupOf] at h1
      change w ∈ (((n : G) • T : Sylow 2 G) : Subgroup G) at h1
      rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h1
      simpa [MulAut.smul_def, MulAut.conj_apply] using h1
    have hA : CFSG.conjugate (CFSG.conjugate V g) n ≤ (T : Subgroup G) ⊓
        CFSG.conjugate V (g * n) := by
      intro x hx
      rw [mem_conjugate_iff'] at hx
      refine mem_inf.2 ⟨?_, ?_⟩
      · have h1 := hnT _ hx
        rwa [show (n : G)⁻¹ * (n * x * (n : G)⁻¹) * n = x by group] at h1
      · rw [mem_conjugate_iff']
        rw [mem_conjugate_iff'] at hx
        rwa [show g * n * x * (g * n)⁻¹ = g * (n * x * (n : G)⁻¹) * g⁻¹ by group]
    have hAeq : CFSG.conjugate (CFSG.conjugate V g) n = CFSG.conjugate V (g * n) := by
      rw [SteinbergBS.conjugate_mul]
    have h1 := hk1 (g * n) _ 0 hA (by rw [hAeq, relIndex_self, pow_zero]) zero_le_one
    rw [commutator_eq_bot_iff_commute] at h1 ⊢
    intro w hw v hv
    have h2 := h1 ((n : G)⁻¹ * w * n) (by rw [mem_conjugate_iff']; group; exact hw)
      ((n : G)⁻¹ * v * n) (by
        have h3 := (mem_normalizer_iff.1 (inv_mem n.2) v).1 hv
        rwa [inv_inv] at h3)
    calc w * v = n * (((n : G)⁻¹ * w * n) * ((n : G)⁻¹ * v * n)) * (n : G)⁻¹ := by group
      _ = n * (((n : G)⁻¹ * v * n) * ((n : G)⁻¹ * w * n)) * (n : G)⁻¹ := by rw [h2]
      _ = v * w := by group
  have hk2 : ∀ (g : G) (A : Subgroup G), A ≤ (T : Subgroup G) ⊓ CFSG.conjugate V g →
      A.relIndex (CFSG.conjugate V g) = 2 ^ 2 → ⁅A, V⁆ = ⊥ := by
    intro g A hA hk
    by_contra hAV
    have hVA : ⁅V, A⁆ ≠ ⊥ := by rwa [commutator_comm]
    have hAW : A ≤ CFSG.conjugate V g := hA.trans inf_le_right
    have hAN : A ≤ N := (hA.trans inf_le_left).trans hTN
    obtain ⟨hUA, -, hE8, hU8, hfc, -, -⟩ := analysis g A 2 hAW hAN hk le_rfl hVA
    set W := CFSG.conjugate V g with hWdef
    set U := V ⊓ centralizer (A : Set G) with hUdef
    set E := (A.subgroupOf N).map φ with hE
    have hA16 : Nat.card A = 16 := by
      have h1 := card_mul_relIndex hAW
      rw [hk, card_conjugate, hV] at h1
      omega
    have hCAV : A ⊓ centralizer (V : Set G) ≠ ⊥ := by
      intro hbot
      have hinj : Function.Injective (φ.comp (A.subgroupOf N).subtype) := by
        rw [injective_iff_map_eq_one]
        intro s hs
        have h1 : ((s : N) : G) ∈ A ⊓ centralizer (V : Set G) :=
          ⟨mem_subgroupOf.1 s.2, (u3ConjLin_eq_one_iff (s : N)).1 hs⟩
        rw [hbot, mem_bot] at h1
        exact Subtype.ext (Subtype.ext h1)
      have h2 : (φ.comp (A.subgroupOf N).subtype).range = E := by
        rw [MonoidHom.range_comp, range_subtype]
      have h3 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      rw [h2, hE8, Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv, hA16] at h3
      omega
    have hWV : W ⊓ centralizer (V : Set G) ≠ ⊥ := fun h =>
      hCAV (le_bot_iff.1 (h ▸ inf_le_inf_right _ hAW))
    have hUW : U ⊓ centralizer (W : Set G) ≠ ⊥ := by
      intro hbot
      have hmem : ∀ (K : Subgroup G) (x : G), x ∈ CFSG.conjugate K g⁻¹ ↔ g⁻¹ * x * g ∈ K := by
        intro K x
        rw [mem_conjugate_iff', inv_inv]
      set U' := CFSG.conjugate U g⁻¹ with hU'
      set A' := CFSG.conjugate A g⁻¹ with hA'
      have hA'V : A' ≤ V := by
        intro x hx
        rw [hmem] at hx
        have h1 := hAW hx
        rw [mem_conjugate_iff'] at h1
        rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
      have hU'N : U' ≤ N := by
        intro x hx
        rw [hmem] at hx
        have hu : g⁻¹ * x * g ∈ V ⊓ normalizer (W : Set G) := by
          rw [hUA]
          exact hx
        have h1 := conj_mem_normalizer_of_mem_normalizer_conjugate hu.2
        rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
      have hU'C : ∀ x ∈ U', x ∈ centralizer (V : Set G) → x = 1 := by
        intro x hx hxC
        rw [hmem] at hx
        have h1 : g⁻¹ * x * g ∈ U ⊓ centralizer (W : Set G) := by
          refine ⟨hx, mem_centralizer_iff.2 fun w hw => ?_⟩
          rw [SetLike.mem_coe, hWdef, mem_conjugate_iff'] at hw
          have h2 := mem_centralizer_iff.1 hxC _ hw
          calc w * (g⁻¹ * x * g) = g⁻¹ * ((g * w * g⁻¹) * x) * g := by group
            _ = g⁻¹ * (x * (g * w * g⁻¹)) * g := by rw [h2]
            _ = g⁻¹ * x * g * w := by group
        rw [hbot, mem_bot] at h1
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have hU'A' : ∀ x ∈ U', ∀ y ∈ A', x * y = y * x := by
        intro x hx y hy
        rw [hmem] at hx hy
        have h1 := mem_centralizer_iff.1 hx.2 _ hy
        calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
          _ = y * x := by group
      have hU'2 : ∀ x ∈ U', x * x = 1 := by
        intro x hx
        rw [hmem] at hx
        have h1 := hV2 _ hx.1
        calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = 1 := by rw [h1]; group
      have hU'c : ∀ x ∈ U', ∀ y ∈ U', x * y = y * x := by
        intro x hx y hy
        rw [hmem] at hx hy
        have h1 := hVc _ hx.1 _ hy.1
        calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
          _ = y * x := by group
      have hA'16 : Nat.card A' = 16 := (card_conjugate A g⁻¹).trans hA16
      set D := (U'.subgroupOf N).map φ with hD
      have hDinj : Function.Injective (φ.comp (U'.subgroupOf N).subtype) := by
        rw [injective_iff_map_eq_one]
        intro s hs
        exact Subtype.ext (Subtype.ext (hU'C _ (mem_subgroupOf.1 s.2)
          ((u3ConjLin_eq_one_iff (s : N)).1 hs)))
      have hD8 : Nat.card D = 8 := by
        have h2 : (φ.comp (U'.subgroupOf N).subtype).range = D := by
          rw [MonoidHom.range_comp, range_subtype]
        rw [← h2, ← Nat.card_congr (MonoidHom.ofInjective hDinj).toEquiv,
          Nat.card_congr (subgroupOfEquivOfLe hU'N).toEquiv, card_conjugate, hU8]
      have hDab : IsElementaryAbelian 2 D := by
        refine SteinbergBM.isElementaryAbelian_two_of ?_ ?_
        · rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
          rw [← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (hU'c _ (mem_subgroupOf.1 hs) _ (mem_subgroupOf.1 hs'))
        · rintro _ ⟨s, hs, rfl⟩
          rw [← map_mul, show s * s = 1 from Subtype.ext (hU'2 _ (mem_subgroupOf.1 hs)),
            map_one]
      have hDker : ∀ s : N, (s : G) ∈ U' → (s : G) ≠ 1 →
          linRank (φ s) = 2 ∧
            LinearMap.ker ((φ s : Additive V →ₗ[ZMod 2] Additive V) - LinearMap.id) =
              subOf V A' := by
        intro s hs hs1
        have hφs1 : φ s ≠ 1 := fun h => hs1 (hU'C _ hs ((u3ConjLin_eq_one_iff s).1 h))
        have hord : orderOf (φ s) = 2 := by
          refine orderOf_eq_prime ?_ hφs1
          rw [pow_two, ← map_mul, show s * s = 1 from Subtype.ext (hU'2 _ hs), map_one]
        have hr2 := hinv _ ⟨s, rfl⟩ hord
        have hA'le : A' ≤ V ⊓ centralizer ({(s : G)} : Set G) := fun y hy =>
          ⟨hA'V hy, mem_centralizer_singleton_iff.2 (hU'A' _ hs _ hy).symm⟩
        have h1 : 2 ^ linRank (φ s) *
            Nat.card (V ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) = Nat.card V :=
          two_pow_linRank_mul_card (hH := (le_rfl : N ≤ N)) s
        have h16 : 16 ≤ Nat.card (V ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) :=
          hA'16 ▸ card_le_of_le hA'le
        have hr : linRank (φ s) = 2 := by
          refine le_antisymm ?_ hr2
          by_contra h
          push Not at h
          have h2 : 8 ≤ 2 ^ linRank (φ s) :=
            le_of_eq_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)
          rw [hV] at h1
          have h3 := Nat.mul_le_mul h2 h16
          omega
        refine ⟨hr, ?_⟩
        rw [ker_u3ConjLin_sub_id]
        refine subOf_congr ?_
        rw [inf_of_le_right hA'V]
        refine (eq_of_le_of_card_ge hA'le ?_).symm
        rw [hr, hV] at h1
        rw [hA'16]
        omega
      have hDΓ : ∀ e ∈ D, ∀ x y, b (e x) (e y) = b x y :=
        fun e he => hpres e (map_le_range _ _ he)
      have hDbot : D ≠ ⊥ := by
        intro h
        rw [h, card_bot] at hD8
        omega
      obtain ⟨⟨d₀, hd₀⟩, hd₀1⟩ := ne_bot_iff_exists_ne_one.mp hDbot
      obtain ⟨s₀, hs₀, rfl⟩ := hd₀
      have hs₀1 : (s₀ : G) ≠ 1 := fun h => hd₀1 (Subtype.ext (by
        change φ s₀ = 1
        rw [show s₀ = 1 from Subtype.ext h, map_one]))
      obtain ⟨F, hFD, hFidx, hlt⟩ := exists_linFix_lt_of_card_eq_eight b hb halt hDab hDΓ hD8
        ⟨φ s₀, ⟨s₀, hs₀, rfl⟩, fun h => hs₀1 (hU'C _ hs₀ ((u3ConjLin_eq_one_iff s₀).1 h)),
          (hDker s₀ hs₀ hs₀1).1.le⟩
      have hF : F ≠ ⊥ := by
        intro h
        have h1 := relIndex_mul_card F D
        rw [inf_of_le_left hFD, h, card_bot, hD8] at h1
        rw [h] at hFidx
        omega
      obtain ⟨⟨f, hf⟩, hf1⟩ := ne_bot_iff_exists_ne_one.mp hF
      obtain ⟨s, hs, rfl⟩ := hFD hf
      have hs1 : (s : G) ≠ 1 := fun h => hf1 (Subtype.ext (by
        change φ s = 1
        rw [show s = 1 from Subtype.ext h, map_one]))
      have h1 : linFix F ≤ linFix D := by
        refine (linFix_le_ker hf).trans ?_
        rw [(hDker s hs hs1).2, hD, linFix_map_subgroupOf hU'N]
        exact subOf_le_subOf fun y hy =>
          mem_centralizer_iff.2 fun x hx => hU'A' x hx y hy.2
      exact hlt.not_ge h1
    have hVW : V ⊓ centralizer (W : Set G) ≠ ⊥ := fun h =>
      hUW (le_bot_iff.1 (h ▸ inf_le_inf_right _ inf_le_left))
    obtain ⟨-, -, -, -, -, -, -, hII, hXYZ⟩ :=
      SteinbergBM.intersecting_conjugates_two_hulls_class_two hint g hVW hWV
    have hUAV : U ≤ ⁅A, V⁆ := by
      intro u hu
      have h1 : Additive.ofMul (⟨u, hu.1⟩ : V) ∈ linFix E := by
        rw [hE, linFix_map_subgroupOf hAN]
        exact mem_subOf.2 hu.2
      rw [hfc] at h1
      have h2 := mem_subOf.1 (linComm_map_u3ConjLin_le _ h1)
      rwa [subgroupOf_map_subtype, inf_of_le_left hAN] at h2
    have hUZ : U ≤ (center ↥(V ⊔ W)).map (V ⊔ W).subtype :=
      hUAV.trans ((commutator_mono (hAW.trans le_sup_right) le_sup_left).trans
        (hII.trans hXYZ))
    have hWC : W ≤ centralizer (U : Set G) := by
      intro w hw
      rw [mem_centralizer_iff]
      intro u hu
      obtain ⟨c, hc, rfl⟩ := hUZ hu
      have h1 := mem_center_iff.1 hc ⟨w, (le_sup_right : W ≤ V ⊔ W) hw⟩
      exact (congrArg Subtype.val h1).symm
    have hUV : U.relIndex V ≤ 8 := by
      have h1 : Nat.card U * U.relIndex V = Nat.card V := card_mul_relIndex inf_le_left
      rw [hU8, hV] at h1
      omega
    have hWN : W ≤ N := hWC.trans (hcent U inf_le_left hUV)
    have h1 := hconjN W ⟨g, rfl⟩ hWN
    apply hAV
    exact le_bot_iff.1 (h1 ▸ commutator_mono hAW le_rfl)
  refine ⟨fun g A hA hidx => ?_, hconjN⟩
  obtain ⟨k, -, hk⟩ := exists_relIndex_eq_two_pow (hA.trans inf_le_right)
    ((card_conjugate V g).trans hV6)
  have hk2' : k ≤ 2 := by
    by_contra h
    push Not at h
    have h1 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    rw [hk] at hidx
    norm_num at h1
    omega
  rcases (show k ≤ 1 ∨ k = 2 by omega) with h | rfl
  · exact hk1 g A k hA hk h
  · exact hk2 g A hA hk

end CFSG.Quasithin.H13.U3
