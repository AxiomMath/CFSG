module

public import CFSG.Quasithin.H13.L32NLem144Ba

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace L1447

variable {G : Type} [Group G]

@[expose] def F1 (T V V₂ : Subgroup G) : Prop :=
  ∀ x ∈ l32nH T V, x ∉ pCoreOf 2 (l32nH T V) → x * x ∈ pCoreOf 2 (l32nH T V) →
    ∃ w ∈ l32nW T V V₂, w * x * w⁻¹ * x⁻¹ ∉ V₂

@[expose] def F2 (T V V₂ : Subgroup G) (g : G) : Prop :=
  ∀ u ∈ fsuU T V, (∀ x ∈ CFSG.conjugate (l32nW T V V₂) g, u * x = x * u) → u ∈ V₂

@[expose] def F3 (T V V₂ : Subgroup G) (g : G) : Prop :=
  oTwoUpper (l32nH T V) ≤ Subgroup.closure {y | ∃ h ∈ l32nH T V,
    ∃ w ∈ CFSG.conjugate (l32nW T V V₂) g, y = h * w * h⁻¹} ⊔ pCoreOf 2 (l32nH T V)

@[expose] def dG (T V : Subgroup G) (g : G) : Subgroup G :=
  CFSG.conjugate (l32nH T V) g ⊓ Subgroup.centralizer (CFSG.conjugate (fsuU T V) g : Set G)

theorem mem_conj {X : Subgroup G} {g y : G} : y ∈ CFSG.conjugate X g ↔ g * y * g⁻¹ ∈ X :=
  mem_rconj

theorem exists_pow_sq_mem {Q : Subgroup G} {x : G} {k : ℕ} (hk : x ^ 2 ^ k ∈ Q) (hx : x ∉ Q) :
    ∃ j, x ^ 2 ^ j ∉ Q ∧ x ^ 2 ^ j * x ^ 2 ^ j ∈ Q := by
  induction k with
  | zero => exact absurd (by simpa using hk) hx
  | succ k ih =>
    by_cases h : x ^ 2 ^ k ∈ Q
    · exact ih h
    · refine ⟨k, h, ?_⟩
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hk

theorem V_le_U {T V : Subgroup G} : V ≤ fsuU T V := le_conjClosure V _

theorem dG_normal {T V : Subgroup G} {g h : G} (hh : h ∈ CFSG.conjugate (l32nH T V) g) {x : G}
    (hx : x ∈ dG T V g) : h * x * h⁻¹ ∈ dG T V g := by
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hx.1) (Subgroup.inv_mem _ hh),
    Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hUn : (g * h * g⁻¹)⁻¹ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    Subgroup.inv_mem _ (L14332.l32nH_le_normalizer_fsuU T V (mem_conj.mp hh))
  have hu' : h⁻¹ * u * h ∈ CFSG.conjugate (fsuU T V) g := by
    rw [mem_conj]
    have e : g * (h⁻¹ * u * h) * g⁻¹ =
        (g * h * g⁻¹)⁻¹ * (g * u * g⁻¹) * ((g * h * g⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hUn _).mp (mem_conj.mp hu)
  have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hu'
  calc u * (h * x * h⁻¹) = h * ((h⁻¹ * u * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * u * h)) * h⁻¹ := by rw [hc]
    _ = h * x * h⁻¹ * u := by group

end L1447

namespace L144B.Base

open L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
variable (C : Base G T L V V₂ g)
include C

theorem g_mem_LT : g ∈ L ⊔ T := (Subgroup.mem_inf.mp C.gP).1

theorem gV : g ∈ Subgroup.normalizer (V : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  exact sup_le S.LV S.TV C.g_mem_LT

theorem gL : g ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  exact sup_le Subgroup.le_normalizer S.TL C.g_mem_LT

theorem V_le_Ug : V ≤ CFSG.conjugate (fsuU T V) g := fun v hv => mem_conj.mpr
  (V_le_U ((Subgroup.mem_normalizer_iff.mp C.gV v).mp hv))

theorem V2_le_Ug : V₂ ≤ CFSG.conjugate (fsuU T V) g := fun v hv => mem_conj.mpr
  (C.V2U ((Subgroup.mem_normalizer_iff.mp C.gV₂ v).mp hv))

theorem V1g_le_V2 : CFSG.conjugate (fsuV1 T V) g ≤ V₂ := by
  intro v hv
  have h1 := C.plane.2 (mem_conj.mp hv)
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ C.gV₂) _).mp h1
  simpa [mul_assoc] using this

theorem dG_comm_V {x : G} (hx : x ∈ dG T V g) {v : G} (hv : v ∈ V) : x * v = v * x :=
  (Subgroup.mem_centralizer_iff.mp hx.2 v (C.V_le_Ug hv)).symm

theorem dG_le_H : dG T V g ≤ l32nH T V := by
  obtain ⟨_, S⟩ := C.set14
  intro x hx
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  refine S.mem_g1 hz hz1 ?_
  have := Subgroup.mem_centralizer_iff.mp hx.2 z (C.V2_le_Ug (C.plane.2 hz))
  rw [← this]
  group

theorem dG_conj_mem_Q {x : G} (hx : x ∈ dG T V g) : g * x * g⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
  rw [← C.cHat]
  refine ⟨mem_conj.mp hx.1, ?_, fun u hu => ?_⟩
  · rw [C.zU]
    exact mem_conj.mp hx.1
  · have hu' : g⁻¹ * u * g ∈ CFSG.conjugate (fsuU T V) g := by
      rw [mem_conj]
      simpa [mul_assoc] using hu
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hu'
    have e : g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ * u⁻¹ = 1 := by
      calc g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ * u⁻¹ =
          g * (x * (g⁻¹ * u * g)) * x⁻¹ * g⁻¹ * u⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * x) * x⁻¹ * g⁻¹ * u⁻¹ := by rw [hc]
        _ = 1 := by group
    rw [e]
    exact one_mem _

theorem dG_pow {x : G} (hx : x ∈ dG T V g) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l32nH T V) ⟨_, C.dG_conj_mem_Q hx⟩
  refine ⟨k, ?_⟩
  have h1 : (g * x * g⁻¹) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [conj_pow] at h1
  have := congrArg (fun y => g⁻¹ * y * g) h1
  simpa [mul_assoc] using this

theorem mem_V1g_of_mem_V {x : G} (hx : x ∈ dG T V g) (hxV : x ∈ V) :
    x ∈ CFSG.conjugate (fsuV1 T V) g := by
  rw [mem_conj, ← C.zU]
  refine ⟨mem_conj.mp (C.V_le_Ug hxV), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ CFSG.conjugate (fsuU T V) g := by
    rw [mem_conj]
    simpa [mul_assoc] using hu
  have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hu'
  calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * u := by group

theorem W_le_Hg : l32nW T V V₂ ≤ CFSG.conjugate (l32nH T V) g := by
  obtain ⟨_, S⟩ := C.set14
  intro w hw
  rw [mem_conj]
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  refine S.mem_g1 hz hz1 ?_
  have hzg : g⁻¹ * z * g ∈ V₂ := C.V1g_le_V2 (mem_conj.mpr (by simpa [mul_assoc] using hz))
  have hc := Subgroup.mem_centralizer_iff.mp hw.2 _ hzg
  calc g * w * g⁻¹ * z * (g * w * g⁻¹)⁻¹ = g * (w * (g⁻¹ * z * g)) * w⁻¹ * g⁻¹ := by group
    _ = g * ((g⁻¹ * z * g) * w) * w⁻¹ * g⁻¹ := by rw [hc]
    _ = z := by group

theorem comm_mem_V1g (hF2 : F2 T V V₂ g) {d : G} (hd : d ∈ dG T V g) {w : G}
    (hw : w ∈ l32nW T V V₂) : d * w * d⁻¹ * w⁻¹ ∈ CFSG.conjugate (fsuV1 T V) g := by
  have hcD : d * w * d⁻¹ * w⁻¹ ∈ dG T V g := by
    have h1 := dG_normal (C.W_le_Hg hw) (Subgroup.inv_mem _ hd)
    have := Subgroup.mul_mem _ hd h1
    simpa [mul_assoc] using this
  have hcU : d * w * d⁻¹ * w⁻¹ ∈ fsuU T V := by
    have hdN := L14332.l32nH_le_normalizer_fsuU T V (C.dG_le_H hd)
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hdN w).mp hw.1)
      (Subgroup.inv_mem _ hw.1)
  have hcV2 : d * w * d⁻¹ * w⁻¹ ∈ V₂ := by
    refine hF2 _ hcU fun x hx => ?_
    have hxU : x ∈ CFSG.conjugate (fsuU T V) g := by
      rw [mem_conj] at hx ⊢
      exact hx.1
    exact (Subgroup.mem_centralizer_iff.mp hcD.2 x hxU).symm
  exact C.mem_V1g_of_mem_V hcD (C.plane.1.1 hcV2)

theorem dG_le_Q (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g) : dG T V g ≤ pCoreOf 2 (l32nH T V) := by
  intro x hx
  by_contra hxQ
  obtain ⟨k, hk⟩ := C.dG_pow hx
  obtain ⟨j, hj, hj2⟩ := exists_pow_sq_mem (Q := pCoreOf 2 (l32nH T V))
    (hk ▸ one_mem _ : x ^ 2 ^ k ∈ pCoreOf 2 (l32nH T V)) hxQ
  have hd : x ^ 2 ^ j ∈ dG T V g := Subgroup.pow_mem _ hx _
  obtain ⟨w, hw, hnot⟩ := hF1 _ (C.dG_le_H hd) hj hj2
  apply hnot
  have h1 := C.V1g_le_V2 (C.comm_mem_V1g hF2 hd hw)
  have := Subgroup.inv_mem _ h1
  simpa [mul_assoc] using this

theorem eq_one_of_mem_V1_V1g {c : G} (hc : c ∈ fsuV1 T V)
    (hcg : c ∈ CFSG.conjugate (fsuV1 T V) g) : c = 1 := by
  obtain ⟨_, S⟩ := C.set14
  by_contra hc1
  apply C.gH
  have h1 := mem_conj.mp hcg
  rcases S.eq_of_mem_V1 hc hc1 h1 with h2 | h2
  · exfalso
    apply hc1
    have := congrArg (fun y => g⁻¹ * y * g) h2
    simpa [mul_assoc] using this
  · exact S.mem_g1 hc hc1 h2

theorem dG_comm_W (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g) {d : G} (hd : d ∈ dG T V g) {w : G}
    (hw : w ∈ l32nW T V V₂) : d * w = w * d := by
  have hQ := C.dG_le_Q hF1 hF2 hd
  rw [← C.cHat] at hQ
  have h1 : d * w * d⁻¹ * w⁻¹ ∈ fsuV1 T V := C.zU ▸ hQ.2.2 w hw.1
  have h2 := C.eq_one_of_mem_V1_V1g h1 (C.comm_mem_V1g hF2 hd hw)
  calc d * w = d * w * d⁻¹ * w⁻¹ * (w * d) := by group
    _ = w * d := by rw [h2, one_mul]

end L144B.Base

end CFSG.Quasithin.H13
