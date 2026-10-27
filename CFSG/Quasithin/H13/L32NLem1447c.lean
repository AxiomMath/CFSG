module

public import CFSG.Quasithin.Vol2.GoldschmidtL128Quad
public import CFSG.Quasithin.H13.L32NLem1447a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L128A.HatU

namespace L1447

variable {G : Type} [Group G] [Finite G] {U : Subgroup G}

omit [Finite G] in
theorem comm_mul_center {q a ζ : G} (hqζ : q * ζ = ζ * q) :
    q * (a * ζ) * q⁻¹ * (a * ζ)⁻¹ = q * a * q⁻¹ * a⁻¹ := by
  calc q * (a * ζ) * q⁻¹ * (a * ζ)⁻¹ = q * a * (q⁻¹ * (q * ζ)) * q⁻¹ * ζ⁻¹ * a⁻¹ := by group
    _ = q * a * (q⁻¹ * (ζ * q)) * q⁻¹ * ζ⁻¹ * a⁻¹ := by rw [hqζ]
    _ = q * a * q⁻¹ * a⁻¹ := by group

omit [Finite G] in
theorem comm_mul_mul {q a b : G} (h : (q * b * q⁻¹ * b⁻¹) * a = a * (q * b * q⁻¹ * b⁻¹)) :
    q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by
  calc q * (a * b) * q⁻¹ * (a * b)⁻¹
      = (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹)) * a⁻¹ := by group
    _ = (q * a * q⁻¹ * a⁻¹) * ((q * b * q⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [h]
    _ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by group

theorem exists_mul_comm (D : HatModelU U) (hZ : Nat.card (centerOf U) = 2)
    (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ centerOf U) {q : G}
    (hqc : ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ centerOf U)
    (hqz : ∀ ζ ∈ centerOf U, q * ζ = ζ * q) :
    ∃ u₀ ∈ U, ∀ u ∈ U, (u₀⁻¹ * q) * u = u * (u₀⁻¹ * q) := by
  classical
  let σ : D.V → G := fun v => Classical.choose (D.π_surj v)
  have hσU : ∀ v, σ v ∈ U := fun v => (Classical.choose_spec (D.π_surj v)).1
  have hσπ : ∀ v, D.π (σ v) = v := fun v => (Classical.choose_spec (D.π_surj v)).2
  have hwd : ∀ a ∈ U, ∀ b ∈ U, D.π a = D.π b →
      q * a * q⁻¹ * a⁻¹ = q * b * q⁻¹ * b⁻¹ := by
    intro a ha b hb hab
    have hζ := (D.π_eq_iff a ha b hb).mp hab
    have e : b = a * (a⁻¹ * b) := by group
    rw [e, comm_mul_center (hqz _ hζ)]
  let f : D.V →+ ZMod 2 :=
    { toFun := fun v => eps (q * σ v * q⁻¹ * (σ v)⁻¹)
      map_zero' := by
        show eps (q * σ 0 * q⁻¹ * (σ 0)⁻¹) = 0
        rw [hwd _ (hσU 0) 1 U.one_mem (by rw [hσπ, π_one]), eps_eq_zero_iff]
        group
      map_add' := fun v w => by
        show eps (q * σ (v + w) * q⁻¹ * (σ (v + w))⁻¹) =
          eps (q * σ v * q⁻¹ * (σ v)⁻¹) + eps (q * σ w * q⁻¹ * (σ w)⁻¹)
        have h1 : D.π (σ (v + w)) = D.π (σ v * σ w) := by
          rw [D.π_mul _ (hσU v) _ (hσU w), hσπ, hσπ, hσπ]
        rw [hwd _ (hσU _) _ (U.mul_mem (hσU v) (hσU w)) h1,
          comm_mul_mul ((Subgroup.mem_centralizer_iff.mp (hqc _ (hσU w)).2 _ (hσU v)).symm),
          eps_mul hZ (hqc _ (hσU v)) (hqc _ (hσU w))] }
  let F : Module.Dual (ZMod 2) D.V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c v => by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl <;> simp }
  have hnd : D.B.Nondegenerate :=
    ⟨fun v hv => B_nondegenerate D v hv,
      fun v hv => B_nondegenerate D v fun w => by rw [B_symm]; exact hv w⟩
  have : FiniteDimensional (ZMod 2) D.V := Module.Finite.of_finite
  set v₀ := (D.B.toDual hnd).symm F with hv₀
  refine ⟨σ v₀, hσU v₀, fun u hu => ?_⟩
  have hB : D.B (D.π (σ v₀)) (D.π u) = F (D.π u) := by
    rw [hσπ, hv₀, LinearMap.BilinForm.apply_toDual_symm_apply]
  have hF : F (D.π u) = eps (q * u * q⁻¹ * u⁻¹) := by
    show eps (q * σ (D.π u) * q⁻¹ * (σ (D.π u))⁻¹) = _
    rw [hwd _ (hσU _) _ hu (hσπ _)]
  have hBu : D.B (D.π (σ v₀)) (D.π u) = eps (σ v₀ * u * (σ v₀)⁻¹ * u⁻¹) :=
    zmod_two_eq_of_iff (by rw [D.B_spec _ (hσU v₀) _ hu, eps_eq_zero_iff])
  have heps : eps (σ v₀ * u * (σ v₀)⁻¹ * u⁻¹) = eps (q * u * q⁻¹ * u⁻¹) := by
    rw [← hBu, hB, hF]
  have hc : σ v₀ * u * (σ v₀)⁻¹ * u⁻¹ = q * u * q⁻¹ * u⁻¹ := by
    have h1 := hcomm _ (hσU v₀) _ hu
    have h2 := hqc _ hu
    by_cases e1 : σ v₀ * u * (σ v₀)⁻¹ * u⁻¹ = 1
    · rw [e1, eps_of_eq_one rfl] at heps
      rw [e1, (eps_eq_zero_iff.mp heps.symm)]
    · have e2 : q * u * q⁻¹ * u⁻¹ ≠ 1 := fun h => by
        rw [h, eps_of_eq_one rfl, eps_eq_zero_iff] at heps
        exact e1 heps
      exact SteinbergBS.eq_of_card_le_two hZ.le h1 h2 e1 e2
  calc (σ v₀)⁻¹ * q * u = (σ v₀)⁻¹ * (q * u * q⁻¹ * u⁻¹) * u * q := by group
    _ = (σ v₀)⁻¹ * (σ v₀ * u * (σ v₀)⁻¹ * u⁻¹) * u * q := by rw [hc]
    _ = u * ((σ v₀)⁻¹ * q) := by group

end L1447

namespace L144B.Base

open L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
variable (C : Base G T L V V₂ g)
include C

theorem fsuU_eq_of_cent (h12213 : Stmt12_2_13)
    (hcent : l32nH T V ⊓ Subgroup.centralizer (fsuU T V : Set G) ≤ centerOf (fsuU T V)) :
    fsuU T V = pCoreOf 2 (l32nH T V) := by
  obtain ⟨D⟩ := C.s1282.exists_hatModelU C.h1222 h12213
  refine le_antisymm (C.UQ D) fun q hq => ?_
  have hqC := hq
  rw [← C.cHat] at hqC
  have hZ : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact C.ext.2.2.2
  have hqz : ∀ ζ ∈ centerOf (fsuU T V), q * ζ = ζ * q := by
    intro ζ hζ
    obtain ⟨_, S⟩ := C.set14
    rw [C.zU] at hζ
    have hqH : q ∈ l32nH T V := hqC.1
    rw [l32nH, normalizer_eq_centralizer_of_card_eq_two S.card_V1] at hqH
    exact (Subgroup.mem_centralizer_iff.mp hqH ζ hζ).symm
  obtain ⟨u₀, hu₀, hc⟩ := exists_mul_comm D hZ C.comm_center hqC.2.2 hqz
  have hcH : u₀⁻¹ * q ∈ l32nH T V := Subgroup.mul_mem _ (Subgroup.inv_mem _ (C.UH hu₀)) hqC.1
  have hcZ := hcent ⟨hcH, Subgroup.mem_centralizer_iff.mpr fun u hu => (hc u hu).symm⟩
  have : q = u₀ * (u₀⁻¹ * q) := by group
  rw [this]
  exact Subgroup.mul_mem _ hu₀ hcZ.1

end L144B.Base

end CFSG.Quasithin.H13
