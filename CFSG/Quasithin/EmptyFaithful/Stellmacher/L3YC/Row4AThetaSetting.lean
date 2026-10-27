module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row4ATheta
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.BadRows
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.SettingY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

section General

variable {G : Type} [Group G]

theorem mem_normalizer_conjSub_iff {A : Subgroup G} {t g : G} :
    g ∈ Subgroup.normalizer (B6.conjSub t A : Set G) ↔
      t⁻¹ * g * t ∈ Subgroup.normalizer (A : Set G) := by
  rw [← conjSub_eq_self_iff, ← conjSub_eq_self_iff]
  have e : B6.conjSub g (B6.conjSub t A) = B6.conjSub t (B6.conjSub (t⁻¹ * g * t) A) := by
    rw [← B6.conjSub_mul, ← B6.conjSub_mul]
    congr 1
    group
  rw [e]
  exact (B6.conjSub t).injective.eq_iff

theorem mem_S_or_of_index_two {T S : Subgroup G} (hidx : S.relIndex T = 2) {t' : G} (ht'T : t' ∈ T)
    (ht'S : t' ∉ S) {t : G} (ht : t ∈ T) : t ∈ S ∨ t'⁻¹ * t ∈ S := by
  by_cases hS : t ∈ S
  · exact Or.inl hS
  · right
    have h2 : (S.subgroupOf T).index = 2 := hidx
    have h3 := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨t'⁻¹, T.inv_mem ht'T⟩) (b := ⟨t, ht⟩)
    have hiff : (⟨t'⁻¹, T.inv_mem ht'T⟩ * ⟨t, ht⟩ : ↥T) ∈ S.subgroupOf T := by
      rw [h3]
      constructor
      · intro h
        exact absurd (S.inv_mem_iff.mp (Subgroup.mem_subgroupOf.mp h)) ht'S
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp h) hS
    exact Subgroup.mem_subgroupOf.mp hiff

theorem mul_self_mem_S {T S : Subgroup G} (hidx : S.relIndex T = 2) {t' : G} (ht'T : t' ∈ T) :
    t' * t' ∈ S := by
  have h2 : (S.subgroupOf T).index = 2 := hidx
  have h3 := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨t', ht'T⟩) (b := ⟨t', ht'T⟩)
  have hiff : (⟨t', ht'T⟩ * ⟨t', ht'T⟩ : ↥T) ∈ S.subgroupOf T := by
    rw [h3]
  exact hiff

theorem centralizes_of_swap {S : Subgroup G} {t' c₀ u₀ : G}
    (hTS : t' ∈ Subgroup.normalizer (S : Set G)) (hu₀S : ∀ s ∈ S, s * u₀ = u₀ * s)
    (hsw : t' * c₀ * t'⁻¹ = u₀) : ∀ s ∈ S, s * c₀ = c₀ * s := by
  intro s hs
  have hs' : t' * s * t'⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hTS s).mp hs
  have h := hu₀S _ hs'
  rw [← hsw] at h
  have : t' * (s * c₀) * t'⁻¹ = t' * (c₀ * s) * t'⁻¹ := by
    calc t' * (s * c₀) * t'⁻¹ = (t' * s * t'⁻¹) * (t' * c₀ * t'⁻¹) := by group
      _ = (t' * c₀ * t'⁻¹) * (t' * s * t'⁻¹) := h
      _ = t' * (c₀ * s) * t'⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel this)

theorem fixes_all_of_three [Finite G] {V : Subgroup G} (hV4 : Nat.card ↥V = 4)
    (hsq : ∀ v ∈ V, v * v = 1) {y : G} (hy3 : orderOf y = 3)
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) {c₀ : G} (hc₀ : c₀ ∈ V) (hc₀1 : c₀ ≠ 1)
    (hfix : y * c₀ * y⁻¹ = c₀) : ∀ v ∈ V, y * v * y⁻¹ = v := by
  intro v hv
  by_contra hne
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hne (by group)
  have hvc : v ≠ c₀ := by
    rintro rfl
    exact hne hfix
  have hc₀2 := hsq c₀ hc₀
  have hmul : c₀ * v ≠ 1 := by
    intro h
    apply hvc
    have h1 : v = c₀⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hc₀2
  have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hc₀comm : y * c₀ = c₀ * y := by
    have := congrArg (· * y) hfix
    simpa [mul_assoc] using this
  rcases SzC4.mem_of_card_four hV4 hc₀ hv hc₀1 hv1 hvc.symm hmul _ hyv with h | h | h | h
  · apply hv1
    have : y * v * y⁻¹ = 1 := h
    simpa using this
  · apply hvc
    have h1 : y * v * y⁻¹ = c₀ := h
    calc v = y⁻¹ * (y * v * y⁻¹) * y := by group
      _ = y⁻¹ * c₀ * y := by rw [h1]
      _ = y⁻¹ * (c₀ * y) := by group
      _ = y⁻¹ * (y * c₀) := by rw [hc₀comm]
      _ = c₀ := by group
  · exact hne h
  ·
    have h1 : y * v * y⁻¹ = c₀ * v := h
    have h2 : y * (c₀ * v) * y⁻¹ = v := by
      calc y * (c₀ * v) * y⁻¹ = (y * c₀ * y⁻¹) * (y * v * y⁻¹) := by group
        _ = c₀ * (c₀ * v) := by rw [hfix, h1]
        _ = (c₀ * c₀) * v := by group
        _ = v := by rw [hc₀2]; group
    have e3 : y ^ 3 = y * y * y := by rw [pow_succ, pow_two]
    have h3 : y ^ 3 * v * (y ^ 3)⁻¹ = c₀ * v := by
      calc y ^ 3 * v * (y ^ 3)⁻¹ = y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹ := by rw [e3]; group
        _ = y * (y * (c₀ * v) * y⁻¹) * y⁻¹ := by rw [h1]
        _ = y * v * y⁻¹ := by rw [h2]
        _ = c₀ * v := h1
    rw [hy3'] at h3
    apply hc₀1
    have : v = c₀ * v := by simpa using h3
    exact (mul_eq_right.mp this.symm)

end General

section Setting

variable {G : Type} [Group G] [Finite G]

theorem row4a_sylow (h11 : StageLemma14111) {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}
    (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) {t' : G} (ht'T : t' ∈ T)
    {Vc Vn : Subgroup G} {c₀ u₀ : G} (hlabel : (Vc = V₁ ∧ Vn = V₂) ∨ (Vc = V₂ ∧ Vn = V₁))
    (hc₀Vc : c₀ ∈ Vc) (hc₀1 : c₀ ≠ 1) (hu₀ : u₀ ∈ Vn) (hu₀1 : u₀ ≠ 1)
    (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s) (hsw : t' * c₀ * t'⁻¹ = u₀) :
    IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c₀} : Set G)) := by
  classical
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hD
  have hc₀S := centralizes_of_swap (hTS ht'T) hu₀S hsw
  have hS : ∀ s ∈ Sgp153 T V₁, s * c₀ = c₀ * s ∧ s * u₀ = u₀ * s := fun s hs => ⟨hc₀S s hs, hu₀S s hs⟩
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hD.relIndex_nS hyp
  have ht'2 : t' * t' ∈ Sgp153 T V₁ := mul_self_mem_S hidx ht'T
  have hsw' : t' * u₀ * t'⁻¹ = c₀ := by
    calc t' * u₀ * t'⁻¹ = t' * (t' * c₀ * t'⁻¹) * t'⁻¹ := by rw [hsw]
      _ = (t' * t') * c₀ * (t' * t')⁻¹ := by group
      _ = c₀ := by rw [hc₀S _ ht'2]; group
  have hsqV : ∀ a ∈ VZ T M, a * a = 1 := fun a ha => by
    have := hyp.elemAbelian.2 a ha
    rw [pow_two] at this
    exact this
  have hZ4 := (hyp.lemma_15_3_8 hD).2
  have hVcV : Vc ≤ VZ T M := by
    rcases hlabel with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact hD.le₁
    · exact hD.le₂
  have hVnV : Vn ≤ VZ T M := by
    rcases hlabel with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · exact hD.le₂
    · exact hD.le₁
  have hdisj : Vc ⊓ Vn = ⊥ := by
    rcases hlabel with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hD.inf
    · rw [h1, h2, inf_comm]; exact hD.inf
  have hc₀2 : c₀ * c₀ = 1 := hsqV c₀ (hVcV hc₀Vc)
  have hu₀2 : u₀ * u₀ = 1 := hsqV u₀ (hVnV hu₀)
  have hne : c₀ ≠ u₀ := by
    intro h
    have : c₀ ∈ Vc ⊓ Vn := ⟨hc₀Vc, h ▸ hu₀⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact hc₀1 this
  have hmul : c₀ * u₀ ≠ 1 := fun h =>
    hne ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hu₀2))
  have hcZ : c₀ ∈ VZ T M ⊓ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) :=
    ⟨hVcV hc₀Vc, Subgroup.mem_centralizer_iff.mpr hc₀S⟩
  have huZ : u₀ ∈ VZ T M ⊓ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) :=
    ⟨hVnV hu₀, Subgroup.mem_centralizer_iff.mpr hu₀S⟩
  have hZ : ∀ v ∈ VZ T M, (∀ s ∈ Sgp153 T V₁, s * v = v * s) →
      v = 1 ∨ v = c₀ ∨ v = u₀ ∨ v = c₀ * u₀ := fun v hv hvS =>
    SzC4.mem_of_card_four hZ4 hcZ huZ hc₀1 hu₀1 hne hmul v
      ⟨hv, Subgroup.mem_centralizer_iff.mpr hvS⟩
  have hcen : ∀ x : G, (∀ s ∈ Sgp153 T V₁, s * x = x * s) →
      x ∈ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun s hs => hx s hs
  rcases hlabel with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2
    have hcard := Stellmacher.CD.L3YC.card_inf_centralizer_eq_two (W := Vn) hc₀Vc hc₀1 hc₀2
      (fun s hs => (hS s hs).1) hD.inf hu₀ hu₀1 hD.le₁ (fun v hv hvS => by
        rcases hZ v hv hvS with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
    exact Stellmacher.CD.L3YC.isSylowTwoOf_centralizer_singleton h11 hyp hD hc₀Vc hc₀1
      (hcen c₀ fun s hs => (hS s hs).1) hcard
  · subst h1 h2
    have hinf : Vn ⊓ Vc = ⊥ := hD.inf
    have hcard := Stellmacher.CD.L3YC.card_inf_centralizer_eq_two (W := Vc) hu₀ hu₀1 hu₀2
      (fun s hs => (hS s hs).2) hinf hc₀Vc hc₀1 hD.le₁ (fun v hv hvS => by
        rcases hZ v hv hvS with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
    have hSylu := Stellmacher.CD.L3YC.isSylowTwoOf_centralizer_singleton h11 hyp hD hu₀ hu₀1
      (hcen u₀ fun s hs => (hS s hs).2) hcard
    have := Stellmacher.CD.L3YC.isSylowTwoOf_centralizer_conj hSylu (hTS ht'T)
    rwa [hsw'] at this

theorem row4a_moving_element (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ u₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L) (hc₀1 : c₀ ≠ 1)
    (hu₀S : ∀ s ∈ Sgp153 T V₁, s * u₀ = u₀ * s) (hsw : t' * c₀ * t'⁻¹ = u₀) :
    ∃ e : G, e ∈ YL153 Yp L ∧ e * u₀ * e⁻¹ ≠ u₀ := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hD := hh.decomp
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hD
  have hc₀S := centralizes_of_swap (hTS ht'T) hu₀S hsw
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hD.relIndex_nS hyp
  have ht'2 : t' * t' ∈ Sgp153 T V₁ := mul_self_mem_S hidx ht'T
  have hsw' : t' * u₀ * t'⁻¹ = c₀ := by
    calc t' * u₀ * t'⁻¹ = t' * (t' * c₀ * t'⁻¹) * t'⁻¹ := by rw [hsw]
      _ = (t' * t') * c₀ * (t' * t')⁻¹ := by group
      _ = c₀ := by rw [hc₀S _ ht'2]; group
  obtain ⟨y₀, hy₀Y, hy₀N, hy₀3, v, hv, hyv⟩ := exists_y_order_three h113 h37 h38 c hq c12 hV hYY
    hSL ht'T ht'S hswap h4
  obtain ⟨hC4, hCsq⟩ := c134CQ_card_four hq h4
  have hyV : y₀ ∈ Subgroup.normalizer ((c134CQ (L ⊔ Sgp153 T V₁) L : Subgroup G) : Set G) :=
    (N0_le_normalizer hSL h4 hy₀N).2
  have hmove : y₀ * c₀ * y₀⁻¹ ≠ c₀ := fun hfix =>
    hyv (fixes_all_of_three hC4 hCsq hy₀3 hyV hc₀ hc₀1 hfix v hv)
  have heY : t'⁻¹ * y₀ * t' ∈ YL153 Yp L := by
    rw [← hswap] at hy₀Y
    exact (B6.mem_conjSub).mp hy₀Y
  refine ⟨t'⁻¹ * y₀ * t', heY, fun h => hmove ?_⟩
  have hu₀c : t'⁻¹ * c₀ * t' = u₀ := by
    calc t'⁻¹ * c₀ * t' = t'⁻¹ * (t' * u₀ * t'⁻¹) * t' := by rw [hsw']
      _ = u₀ := by group
  have h1 : t'⁻¹ * (y₀ * c₀ * y₀⁻¹) * t' = u₀ := by
    calc t'⁻¹ * (y₀ * c₀ * y₀⁻¹) * t'
        = t'⁻¹ * y₀ * (t' * u₀ * t'⁻¹) * y₀⁻¹ * t' := by rw [hsw']; group
      _ = (t'⁻¹ * y₀ * t') * u₀ * (t'⁻¹ * y₀ * t')⁻¹ := by group
      _ = u₀ := h
  rw [← hu₀c] at h1
  exact mul_left_cancel (mul_right_cancel h1)

end Setting

end Stellmacher.L3YC

end CFSG.Quasithin
