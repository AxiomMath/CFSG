module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153D0Model
public import CFSG.Quasithin.EmptyFaithful.S153Plus
public import CFSG.Quasithin.EmptyFaithful.S153YCases

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

noncomputable abbrev actV (h : Hyp153 G T Mc M) : OTwoQuot M →* MulAut ↥(VZ T M) :=
  starAct M (VZ T M) h.le_normalizer h.hyp14117.pCoreOf_le_centralizer

@[expose] noncomputable def ZstarOf (h : Hyp153 G T Mc M) : Subgroup (OTwoQuot M) :=
  (actV h).ker ⊓ imageOTwoQuot M (Y153 Mc M)

@[expose] def starOf (h : Hyp153 G T Mc M) (r : G) (hr : r ∈ T) : OTwoQuot M :=
  QuotientGroup.mk (⟨r, h.T_le hr⟩ : ↥M)

@[expose] def SignData {Q : Type*} [Group Q] (Zs : Subgroup Q) (A B ρ : Q) (e₁ e₂ : ℤ) : Prop :=
  (∃ c ∈ Zs, ρ * A * ρ⁻¹ = A ^ e₂ * c) ∧ (∃ c ∈ Zs, ρ * B * ρ⁻¹ = B ^ e₁ * c)

structure StarCoords (h : Hyp153 G T Mc M) (V₁ : Subgroup G) (A B : OTwoQuot M) : Prop where
  A_mem : A ∈ imageOTwoQuot M (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))
  B_mem : B ∈ imageOTwoQuot M (Y153 Mc M)
  A_ne : actV h A ≠ 1
  comm_mem : ⁅A, B⁆ ∈ ZstarOf h
  gen : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), ∃ (i j : ℤ), ∃ c ∈ ZstarOf h, y = B ^ i * A ^ j * c
  genK : ∀ y ∈ imageOTwoQuot M (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)),
    ∃ (j : ℤ), ∃ c ∈ ZstarOf h, y = A ^ j * c
  sign : ∀ (r : G) (hr : r ∈ Sgp153 T V₁), ∃ e₁ e₂ : ℤ, (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
    SignData (ZstarOf h) A B (starOf h r hr.1) e₁ e₂ ∧
      (e₁ = 1 → e₂ = 1 → r ∈ Subgroup.centralizer (VZ T M : Set G))
  inv₂ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G) →
    ∃ (j : G) (hj : j ∈ thompsonJ T),
      SignData (ZstarOf h) A B (starOf h j (thompsonJ_le_self T hj)) 1 (-1)
  inv₁ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G) →
    ∃ (j : G) (hj : j ∈ thompsonJ T),
      SignData (ZstarOf h) A B (starOf h j (thompsonJ_le_self T hj)) (-1) 1
  J_le : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G) → thompsonJ T ≤ Sgp153 T V₁

theorem starOf_conj_mem (h : Hyp153 G T Mc M) {r : G} (hr : r ∈ T) {y : OTwoQuot M}
    (hy : y ∈ imageOTwoQuot M (Y153 Mc M)) :
    starOf h r hr * y * (starOf h r hr)⁻¹ ∈ imageOTwoQuot M (Y153 Mc M) :=
  imageOTwoQuot_conj_mem h.T_le (fun _ hx => le_normalizer_Y153 Mc M (h.T_le hx)) hr hy

theorem actV_starOf (h : Hyp153 G T Mc M) {r : G} (hr : r ∈ T) :
    actV h (starOf h r hr) =
      convI h.elemAbelian (⟨r, h.le_normalizer (h.T_le hr)⟩ : Subgroup.normalizer (VZ T M : Set G)) :=
  rfl

theorem exists_central_of_actV_eq (h : Hyp153 G T Mc M) {y₁ y₂ : OTwoQuot M}
    (h₁ : y₁ ∈ imageOTwoQuot M (Y153 Mc M)) (h₂ : y₂ ∈ imageOTwoQuot M (Y153 Mc M))
    (he : actV h y₁ = actV h y₂) : ∃ c ∈ ZstarOf h, y₁ = y₂ * c := by
  refine ⟨y₂⁻¹ * y₁, ⟨(MonoidHom.mem_ker).2 ?_, (imageOTwoQuot M (Y153 Mc M)).mul_mem
    ((imageOTwoQuot M (Y153 Mc M)).inv_mem h₂) h₁⟩, by group⟩
  rw [map_mul, map_inv, he, inv_mul_cancel]

theorem signData_of_actV (h : Hyp153 G T Mc M) {A B ρ : OTwoQuot M}
    (hρ : ∀ y ∈ imageOTwoQuot M (Y153 Mc M), ρ * y * ρ⁻¹ ∈ imageOTwoQuot M (Y153 Mc M))
    (hA : A ∈ imageOTwoQuot M (Y153 Mc M)) (hB : B ∈ imageOTwoQuot M (Y153 Mc M)) {e₁ e₂ : ℤ}
    (h₁ : actV h ρ * actV h B * (actV h ρ)⁻¹ = actV h B ^ e₁)
    (h₂ : actV h ρ * actV h A * (actV h ρ)⁻¹ = actV h A ^ e₂) :
    SignData (ZstarOf h) A B ρ e₁ e₂ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc, hc'⟩ := exists_central_of_actV_eq h (hρ A hA)
      ((imageOTwoQuot M (Y153 Mc M)).zpow_mem hA e₂) (by rw [map_mul, map_mul, map_inv, map_zpow]; exact h₂)
    exact ⟨c, hc, hc'⟩
  · obtain ⟨c, hc, hc'⟩ := exists_central_of_actV_eq h (hρ B hB)
      ((imageOTwoQuot M (Y153 Mc M)).zpow_mem hB e₁) (by rw [map_mul, map_mul, map_inv, map_zpow]; exact h₁)
    exact ⟨c, hc, hc'⟩

theorem exists_starCoords (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) : ∃ A B : OTwoQuot M, StarCoords h V₁ A B := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hsyl : IsSylowTwoOf (autI hV T) (autI hV M) := h.isSylowTwoOf_autI
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  obtain ⟨x₁, hx₁L, hx₁3, hx₁1⟩ := exists_orderThree hS.nat₁
  obtain ⟨x₂, hx₂L, hx₂3, hx₂1⟩ := exists_orderThree hS.nat₂
  have hord₁ : orderOf x₁ = 3 := orderOf_eq_prime hx₁3 hx₁1
  have hord₂ : orderOf x₂ = 3 := orderOf_eq_prime hx₂3 hx₂1
  have hP := zpowers_sup_eq_oTwoUpper hS hsyl hx₁L hx₂L hord₁ hord₂
  have hx₁Y : x₁ ∈ autI hV (Y153 Mc M) := by
    rw [hYbar, ← hP]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂Y : x₂ ∈ autI hV (Y153 Mc M) := by
    rw [hYbar, ← hP]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  obtain ⟨b', hb'Y, hb'⟩ := (mem_autI hV).1 hx₁Y
  obtain ⟨a', ha'Y, ha'⟩ := (mem_autI hV).1 hx₂Y
  set Ys : Subgroup (OTwoQuot M) := imageOTwoQuot M (Y153 Mc M) with hYs
  set A : OTwoQuot M := QuotientGroup.mk (⟨(a' : G), hYM ha'Y⟩ : ↥M) with hA
  set B : OTwoQuot M := QuotientGroup.mk (⟨(b' : G), hYM hb'Y⟩ : ↥M) with hB
  have hAY : A ∈ Ys := mem_imageOTwoQuot_iff.mpr ⟨a', hYM ha'Y, ha'Y, rfl⟩
  have hBY : B ∈ Ys := mem_imageOTwoQuot_iff.mpr ⟨b', hYM hb'Y, hb'Y, rfl⟩
  have hactA : actV h A = x₂ := ha'
  have hactB : actV h B = x₁ := hb'
  have hAC : (a' : G) ∈ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) :=
    (mem_centralizer_map_inclMod_iff hV a'.2 (commV L₁)).2 fun u hu => by
      rw [ha']
      exact hS.L₂_fix₁ hx₂L hu
  have hcommP : ∀ a ∈ Subgroup.zpowers x₁, ∀ b ∈ Subgroup.zpowers x₂, a * b = b * a :=
    fun a ha b hb => hS.comm a (Subgroup.zpowers_le.mpr hx₁L ha) b
      (Subgroup.zpowers_le.mpr hx₂L hb)
  refine ⟨A, B, ?_, hBY, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_imageOTwoQuot_iff.mpr ⟨a', hYM ha'Y, ⟨ha'Y, hAC⟩, rfl⟩
  · rw [hactA]
    exact hx₂1
  · have hcomm : x₂ * x₁ * x₂⁻¹ * x₁⁻¹ = 1 := by
      have e : x₂ * x₁ * x₂⁻¹ * x₁⁻¹ = (x₂ * x₁) * (x₁ * x₂)⁻¹ := by group
      rw [e, hS.comm x₁ hx₁L x₂ hx₂L]
      group
    refine ⟨(MonoidHom.mem_ker).2 ?_, ?_⟩
    · rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hactA, hactB]
      exact hcomm
    · rw [commutatorElement_def]
      exact Ys.mul_mem (Ys.mul_mem (Ys.mul_mem hAY hBY) (Ys.inv_mem hAY)) (Ys.inv_mem hBY)
  · intro y hy
    obtain ⟨g, hgM, hgY, rfl⟩ := mem_imageOTwoQuot_iff.mp hy
    have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hgM
    have hgbar : convI hV ⟨g, hgN⟩ ∈ oTwoUpper (autI hV M) :=
      hYbar ▸ convI_mem_autI hV hgY hgN
    rw [← hP] at hgbar
    obtain ⟨u, hu, v, hv, huv⟩ := exists_mul_of_mem_sup_of_commute hcommP hgbar
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hBA : B ^ i * A ^ j ∈ Ys := Ys.mul_mem (Ys.zpow_mem hBY i) (Ys.zpow_mem hAY j)
    obtain ⟨c, hc, hc'⟩ := exists_central_of_actV_eq h hy hBA (by
      rw [map_mul, map_zpow, map_zpow, hactA, hactB]
      exact huv.symm)
    exact ⟨i, j, c, hc, hc'⟩
  · intro y hy
    obtain ⟨k, hkM, ⟨hkY, hkC⟩, rfl⟩ := mem_imageOTwoQuot_iff.mp hy
    have hkN : k ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hkM
    have hgbar : convI hV ⟨k, hkN⟩ ∈ oTwoUpper (autI hV M) :=
      hYbar ▸ convI_mem_autI hV hkY hkN
    have hgX : convI hV ⟨k, hkN⟩ ∈ autI hV M := convI_mem_autI hV hkM hkN
    have hgL : convI hV ⟨k, hkN⟩ ∈ L₂ :=
      (hS.mem_L₂_iff hgX).2 ((mem_centralizer_map_inclMod_iff hV hkN (commV L₁)).1 hkC)
    have hmem : convI hV ⟨k, hkN⟩ ∈ oTwoUpper (autI hV M) ⊓ L₂ := ⟨hgbar, hgL⟩
    rw [oTwoUpper_inf_L₂_eq hS hsyl hx₂L hord₂] at hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hAj : A ^ j ∈ Ys := Ys.zpow_mem hAY j
    have hy' : (QuotientGroup.mk (⟨k, hkM⟩ : ↥M) : OTwoQuot M) ∈ Ys :=
      mem_imageOTwoQuot_iff.mpr ⟨k, hkM, hkY, rfl⟩
    obtain ⟨c, hc, hc'⟩ := exists_central_of_actV_eq h hy' hAj (by
      rw [map_zpow, hactA]
      exact hj.symm)
    exact ⟨j, c, hc, hc'⟩
  · intro r hr
    have hrT : r ∈ T := hr.1
    have hrM : r ∈ M := h.T_le hrT
    have hrN : r ∈ Subgroup.normalizer (VZ T M : Set G) := hMV hrM
    have hgS : convI hV ⟨r, hrN⟩ ∈ autI hV T ⊓ (L₁ ⊔ L₂) := by
      rw [← autI_nS hV hS h.T_le]
      exact convI_mem_autI hV hr hrN
    obtain ⟨e₁, e₂, he₁, he₂, hgx₁, hgx₂, hone⟩ :=
      model_signs hS hsyl hx₁L hx₂L hx₁3 hx₂3 hgS
    refine ⟨e₁, e₂, he₁, he₂, signData_of_actV h
      (fun y hy => starOf_conj_mem h hrT hy) hAY hBY ?_ ?_, fun h1 h2 => ?_⟩
    · rw [actV_starOf, hactB]
      exact hgx₁
    · rw [actV_starOf, hactA]
      exact hgx₂
    · exact (convI_eq_one_iff hV ⟨r, hrN⟩).1 (hone h1 h2)
  · intro hJ
    obtain ⟨s₁, s₂, hs₁, hs₂, h11, h12, h21, h22⟩ :=
      model_inverting hS hsyl hx₁L hx₂L hx₁3 hx₂3
    rcases h.lemma_15_3_5 D with ⟨hJ', -⟩ | ⟨-, hJS, -⟩
    · exact absurd hJ' hJ
    · have hs₂J : s₂ ∈ autI hV (thompsonJ T) := by
        have h1 : s₂ ∈ autI hV (T ⊓ Subgroup.normalizer
            ((((commV L₁).map (inclMod hV) : Subgroup G)) : Set G)) := by
          rw [autI_nS hV hS h.T_le]
          exact hs₂
        have h2 : autI hV (thompsonJ T) = autI hV (T ⊓ Subgroup.normalizer
            ((((commV L₁).map (inclMod hV) : Subgroup G)) : Set G)) := hJS
        rw [h2]
        exact h1
      obtain ⟨j, hjJ, hj⟩ := (mem_autI hV).1 hs₂J
      have hjT : (j : G) ∈ T := thompsonJ_le_self T hjJ
      have hρ' : actV h (starOf h j hjT) = s₂ := hj
      refine ⟨j, hjJ, signData_of_actV h (fun y hy => starOf_conj_mem h hjT hy) hAY hBY ?_ ?_⟩
      · rw [zpow_one, hρ', hactB]
        exact h21
      · rw [zpow_neg_one, hρ', hactA]
        exact h22
  · intro hJ
    obtain ⟨s₁, s₂, hs₁, hs₂, h11, h12, h21, h22⟩ :=
      model_inverting hS hsyl hx₁L hx₂L hx₁3 hx₂3
    rcases h.lemma_15_3_5 D with ⟨hJ', -⟩ | ⟨-, hJS, -⟩
    · exact absurd hJ' hJ
    · have hs₁J : s₁ ∈ autI hV (thompsonJ T) := by
        have h1 : s₁ ∈ autI hV (T ⊓ Subgroup.normalizer
            ((((commV L₁).map (inclMod hV) : Subgroup G)) : Set G)) := by
          rw [autI_nS hV hS h.T_le]
          exact hs₁
        have h2 : autI hV (thompsonJ T) = autI hV (T ⊓ Subgroup.normalizer
            ((((commV L₁).map (inclMod hV) : Subgroup G)) : Set G)) := hJS
        rw [h2]
        exact h1
      obtain ⟨j, hjJ, hj⟩ := (mem_autI hV).1 hs₁J
      have hjT : (j : G) ∈ T := thompsonJ_le_self T hjJ
      have hρ' : actV h (starOf h j hjT) = s₁ := hj
      refine ⟨j, hjJ, signData_of_actV h (fun y hy => starOf_conj_mem h hjT hy) hAY hBY ?_ ?_⟩
      · rw [zpow_neg_one, hρ', hactB]
        exact h11
      · rw [zpow_one, hρ', hactA]
        exact h12
  · intro hJ
    exact thompsonJ_le_nS hV hS h.T_le h.le_normalizer h.VZ_le_T hJ hsyl

end S153D

end CFSG.Quasithin
