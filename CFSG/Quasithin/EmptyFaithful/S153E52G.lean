module

public import CFSG.Quasithin.EmptyFaithful.S153E52F
public import CFSG.Quasithin.EmptyFaithful.S153E52D
public import CFSG.Quasithin.EmptyFaithful.S153EGen
public import CFSG.Quasithin.EmptyFaithful.S153Nine

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Fifty2G

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem pCoreOf_Y_le_T (cx : Ctx15350 T Mc M V₁ V₂ t) : pCoreOf 2 (Y153 Mc M) ≤ T := by
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    le_normalizer_pCoreOf 2 (Y153 Mc M)
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    ((T_le_M cx).trans (le_normalizer_Y153 Mc M)).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have h1 : pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 (Y153 Mc M ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_le 2 _ |>.trans le_sup_left) (sup_le hYN hTN)
      (pCoreOf_isPGroup 2 _)
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf cx.hF.sylow_LT)

theorem pCoreOf_Y_le_V (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hAV : ∀ x ∈ pCoreOf 2 (Y153 Mc M), ∀ y ∈ Y153 Mc M, x * y * x⁻¹ * y⁻¹ ∈ VZ T M) :
    pCoreOf 2 (Y153 Mc M) ≤ VZ T M := by
  by_contra hnot
  obtain ⟨x, hxA, hxV⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, -, hDY, hD3, hDi⟩ :=
    exists_sylow_ge (p := 3) (Q := (⊥ : Subgroup G)) (K := Y153 Mc M)
      (IsPGroup.of_card (p := 3) (n := 0) (by simp)) bot_le
  have hYD := Y_eq_sup_of_sylow cx hDY hD3 hDi
  have hCV := fixed_V_D_eq_one h113 cx hDY hD3 hYD
  have hVA : VZ T M ≤ pCoreOf 2 (Y153 Mc M) := cx.c.hyp.VZ_le_pCoreOf_Y153 h113
  have hAY : pCoreOf 2 (Y153 Mc M) ≤ Y153 Mc M := pCoreOf_le 2 _
  have hAC : pCoreOf 2 (Y153 Mc M) ≤ Subgroup.centralizer (VZ T M : Set G) := by
    rw [cx.r49.case_one.1]
    exact inf_le_right
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (Y153_le Mc M).trans cx.c.hyp.le_normalizer
  have hVe := cx.c.hyp.elemAbelian
  have hinv : ∀ d ∈ D, x⁻¹ * (d * x * d⁻¹) ∈ VZ T M := by
    intro d hd
    have := hAV x⁻¹ ((pCoreOf 2 (Y153 Mc M)).inv_mem hxA) d (hDY hd)
    simpa [mul_assoc] using this
  have hVD : ∀ d ∈ D, ∀ v ∈ VZ T M, d * v * d⁻¹ ∈ VZ T M := fun d hd v hv =>
    (Subgroup.mem_normalizer_iff.mp (hYN (hDY hd)) v).mp hv
  have hV16 : ¬ 3 ∣ Nat.card ↥(VZ T M) := by
    rw [cx.c.hyp.card_VZ]
    norm_num
  obtain ⟨x₁, hx₁V, hx₁D⟩ := exists_fixed_in_coset hD3 hV16 hinv hVD
  have hx₁A : x₁ ∈ pCoreOf 2 (Y153 Mc M) := by
    have e : x₁ = x * (x⁻¹ * x₁) := by group
    rw [e]
    exact (pCoreOf 2 (Y153 Mc M)).mul_mem hxA (hVA hx₁V)
  have hx₁V' : x₁ ∉ VZ T M := by
    intro h
    apply hxV
    have e : x = x₁ * (x⁻¹ * x₁)⁻¹ := by group
    rw [e]
    exact (VZ T M).mul_mem h ((VZ T M).inv_mem hx₁V)
  have hcentA : ∀ a ∈ pCoreOf 2 (Y153 Mc M), a * x₁ = x₁ * a := by
    intro a ha
    have hφV : a * x₁ * a⁻¹ * x₁⁻¹ ∈ VZ T M := hAV a ha x₁ (hAY hx₁A)
    have hfixed : ∀ d ∈ D, d * (a * x₁ * a⁻¹ * x₁⁻¹) * d⁻¹ = a * x₁ * a⁻¹ * x₁⁻¹ := by
      intro d hd
      have hc : d * a * d⁻¹ * a⁻¹ ∈ VZ T M := by
        have := hAV a ha d (hDY hd)
        have e : d * a * d⁻¹ * a⁻¹ = (a * d * a⁻¹ * d⁻¹)⁻¹ := by group
        rw [e]
        exact (VZ T M).inv_mem this
      have hda : d * a * d⁻¹ = (d * a * d⁻¹ * a⁻¹) * a := by group
      have h1 : d * (a * x₁ * a⁻¹ * x₁⁻¹) * d⁻¹ =
          (d * a * d⁻¹) * (d * x₁ * d⁻¹) * (d * a * d⁻¹)⁻¹ * (d * x₁ * d⁻¹)⁻¹ := by group
      rw [h1, hx₁D d hd, hda]
      set c := d * a * d⁻¹ * a⁻¹ with hcdef
      have h2 : c * a * x₁ * (c * a)⁻¹ * x₁⁻¹ =
          c * (a * x₁ * a⁻¹ * x₁⁻¹) * (x₁ * c⁻¹ * x₁⁻¹) := by group
      have h3 : x₁ * c⁻¹ * x₁⁻¹ = c⁻¹ := by
        have := Subgroup.mem_centralizer_iff.mp (hAC hx₁A) c⁻¹ ((VZ T M).inv_mem hc)
        calc x₁ * c⁻¹ * x₁⁻¹ = (x₁ * c⁻¹) * x₁⁻¹ := rfl
          _ = (c⁻¹ * x₁) * x₁⁻¹ := by rw [← this]
          _ = c⁻¹ := by group
      have h4 : c * (a * x₁ * a⁻¹ * x₁⁻¹) = (a * x₁ * a⁻¹ * x₁⁻¹) * c :=
        B2F.isElemAbelian_comm hVe hc hφV
      rw [h2, h3, h4]
      group
    have h1 := hCV _ hφV hfixed
    have : a * x₁ = x₁ * a := by
      have h2 : a * x₁ * a⁻¹ * x₁⁻¹ = 1 := h1
      calc a * x₁ = (a * x₁ * a⁻¹ * x₁⁻¹) * (x₁ * a) := by group
        _ = x₁ * a := by rw [h2, one_mul]
    exact this
  have hcentY : ∀ y ∈ Y153 Mc M, y * x₁ = x₁ * y := by
    have hle : Y153 Mc M ≤ Subgroup.centralizer ({x₁} : Set G) := by
      rw [hYD]
      refine sup_le (fun a ha => ?_) (fun d hd => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hcentA a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have := hx₁D d hd
        calc x₁ * d = (d * x₁ * d⁻¹) * d := by rw [this]
          _ = d * x₁ := by group
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) x₁ rfl).symm
  set Q : Subgroup G := pCoreOf 2 (Y153 Mc M) ⊓ Subgroup.centralizer (Y153 Mc M : Set G) with hQ
  have hx₁Q : x₁ ∈ Q := ⟨hx₁A, Subgroup.mem_centralizer_iff.2 fun y hy => hcentY y hy⟩
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hx₁Q
    exact hx₁V' (hx₁Q ▸ (VZ T M).one_mem)
  have hTNY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) := (T_le_M cx).trans (le_normalizer_Y153 Mc M)
  have hTNA : T ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    hTNY.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hconjQ : ∀ t' ∈ T, ∀ q ∈ Q, t' * q * t'⁻¹ ∈ Q := by
    intro t' ht' q hq
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hTNA ht') q).mp hq.1,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : t'⁻¹ * y * t'⁻¹⁻¹ ∈ Y153 Mc M :=
      (Subgroup.mem_normalizer_iff.mp (hTNY (T.inv_mem ht')) y).mp hy
    have hc := Subgroup.mem_centralizer_iff.mp hq.2 _ hy'
    have e1 : y * (t' * q * t'⁻¹) = t' * ((t'⁻¹ * y * t'⁻¹⁻¹) * q) * t'⁻¹ := by group
    have e2 : (t' * q * t'⁻¹) * y = t' * (q * (t'⁻¹ * y * t'⁻¹⁻¹)) * t'⁻¹ := by group
    rw [e1, e2, hc]
  have hTNQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    intro t' ht'
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconjQ t' ht' q, fun hq => ?_⟩
    have := hconjQ t'⁻¹ (T.inv_mem ht') _ hq
    have e : t'⁻¹ * (t' * q * t'⁻¹) * t'⁻¹⁻¹ = q := by group
    rwa [e] at this
  have hT2 : IsPGroup 2 T := cx.hF.sylow_H.2.1
  have hQT : Q ≤ T := inf_le_left.trans (pCoreOf_Y_le_T cx)
  obtain ⟨z₀, hz₀Q, hz₀1, hz₀c⟩ := exists_ne_one_mem_center_of_normalized hT2 hQT hQne hTNQ
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨z₀, hQT hz₀Q⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hz₀1 hj
  set z₁ := z₀ ^ 2 ^ (j - 1) with hz₁
  have hord : orderOf z₁ = 2 := by
    have hd : 2 ^ (j - 1) ∣ orderOf z₀ := by
      rw [hj]
      exact pow_dvd_pow 2 (Nat.sub_le j 1)
    rw [hz₁, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hd, hj]
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    simp [pow_succ]
  have hz₁Q : z₁ ∈ Q := Subgroup.pow_mem _ hz₀Q _
  have hz₁sq : z₁ ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
  have hz₁T : z₁ ∈ T := hQT hz₁Q
  have hz₁c : ∀ y ∈ T, y * z₁ = z₁ * y := fun y hy => (Commute.pow_right (hz₀c y hy : Commute y z₀) _).eq
  have hz₁Z : z₁ ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hz₁T, Subgroup.mem_centralizer_iff.mpr fun y hy => (hz₁c y hy)⟩, hz₁sq⟩
  have hz₁V : z₁ ∈ VZ T M := cx.c.hyp.Z_le_VZ hz₁Z
  have hz₁D : ∀ d ∈ D, d * z₁ * d⁻¹ = z₁ := by
    intro d hd
    have := Subgroup.mem_centralizer_iff.mp hz₁Q.2 d (hDY hd)
    calc d * z₁ * d⁻¹ = (z₁ * d) * d⁻¹ := by rw [this]
      _ = z₁ := by group
  have hz1 := hCV z₁ hz₁V hz₁D
  rw [hz1, orderOf_one] at hord
  omega

end Fifty2G

end S153E

end CFSG.Quasithin
