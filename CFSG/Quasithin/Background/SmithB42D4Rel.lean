module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951

public section

namespace CFSG.Quasithin.B42D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open scoped commutatorElement

section Prod5

variable {G : Type*} [Group G] {M : Type*} [AddCommMonoid M]

theorem prod5_mul (x₁ x₂ x₃ x₄ x₅ : M → G) (h₁ : ∀ a b, x₁ (a + b) = x₁ a * x₁ b)
    (h₂ : ∀ a b, x₂ (a + b) = x₂ a * x₂ b) (h₃ : ∀ a b, x₃ (a + b) = x₃ a * x₃ b)
    (h₄ : ∀ a b, x₄ (a + b) = x₄ a * x₄ b) (h₅ : ∀ a b, x₅ (a + b) = x₅ a * x₅ b)
    (c12 : ∀ a b, Commute (x₁ a) (x₂ b)) (c13 : ∀ a b, Commute (x₁ a) (x₃ b))
    (c14 : ∀ a b, Commute (x₁ a) (x₄ b)) (c15 : ∀ a b, Commute (x₁ a) (x₅ b))
    (c23 : ∀ a b, Commute (x₂ a) (x₃ b)) (c24 : ∀ a b, Commute (x₂ a) (x₄ b))
    (c25 : ∀ a b, Commute (x₂ a) (x₅ b)) (c34 : ∀ a b, Commute (x₃ a) (x₄ b))
    (c35 : ∀ a b, Commute (x₃ a) (x₅ b)) (c45 : ∀ a b, Commute (x₄ a) (x₅ b))
    (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : M) :
    x₁ a₁ * x₂ a₂ * x₃ a₃ * x₄ a₄ * x₅ a₅ * (x₁ b₁ * x₂ b₂ * x₃ b₃ * x₄ b₄ * x₅ b₅) =
      x₁ (a₁ + b₁) * x₂ (a₂ + b₂) * x₃ (a₃ + b₃) * x₄ (a₄ + b₄) * x₅ (a₅ + b₅) := by
  rw [h₁, h₂, h₃, h₄, h₅]
  simp only [mul_assoc]
  rw [(c15 b₁ a₅).symm.left_comm, (c14 b₁ a₄).symm.left_comm, (c13 b₁ a₃).symm.left_comm,
    (c12 b₁ a₂).symm.left_comm]
  rw [(c25 b₂ a₅).symm.left_comm, (c24 b₂ a₄).symm.left_comm, (c23 b₂ a₃).symm.left_comm]
  rw [(c35 b₃ a₅).symm.left_comm, (c34 b₃ a₄).symm.left_comm]
  rw [(c45 b₄ a₅).symm.left_comm]

end Prod5

section Basic

variable {K : Type} [Field K]

local notation "Xr" => pinnedX TwistTag.D4.tag K

@[expose] noncomputable def abProd (v : K × K × K × K × K) : ModGL TwistTag.D4.tag K :=
  Xr d4N13 v.1 * Xr d4N03 v.2.1 * Xr d4N01 v.2.2.1 * Xr d4P v.2.2.2.1 * Xr d4H v.2.2.2.2

theorem abProd_n13 (a : K) : Xr d4N13 a = abProd (a, 0, 0, 0, 0) := by
  simp [abProd, pinnedX_zero]

theorem abProd_n03 (a : K) : Xr d4N03 a = abProd (0, a, 0, 0, 0) := by
  simp [abProd, pinnedX_zero]

theorem abProd_n01 (a : K) : Xr d4N01 a = abProd (0, 0, a, 0, 0) := by
  simp [abProd, pinnedX_zero]

theorem abProd_p (a : K) : Xr d4P a = abProd (0, 0, 0, a, 0) := by
  simp [abProd, pinnedX_zero]

theorem abProd_h (a : K) : Xr d4H a = abProd (0, 0, 0, 0, a) := by
  simp [abProd, pinnedX_zero]

end Basic

section Coe

variable {K : Type} [Field K] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "kk" => trialityFixedField K σ.toRingHom

theorem coe_ox₁_eq (s : K) : ox₁ σ s = Xr d4E0 s * Xr d4E1 (σ s) * Xr d4E3 (σ (σ s)) := by
  have h0 : trialityRoot 0 = d4E0 := List.ofFn_injective (by decide +kernel)
  have h1 : permLattice TwistTag.D4.perm d4E0 = d4E1 := List.ofFn_injective (by decide +kernel)
  have h2 : permLattice (TwistTag.D4.perm ^ 2) d4E0 = d4E3 :=
    List.ofFn_injective (by decide +kernel)
  rw [ox₁, trialityX₁, coe_trialityOrbitProd, h0, h1, h2]
  rfl

theorem coe_ox₃_eq (s : K) : ox₃ σ s = Xr d4M0 s * Xr d4M1 (σ s) * Xr d4M3 (σ (σ s)) := by
  have h0 : trialityRoot 2 = d4M0 := List.ofFn_injective (by decide +kernel)
  have h1 : permLattice TwistTag.D4.perm d4M0 = d4M1 := List.ofFn_injective (by decide +kernel)
  have h2 : permLattice (TwistTag.D4.perm ^ 2) d4M0 = d4M3 :=
    List.ofFn_injective (by decide +kernel)
  rw [ox₃, trialityX₃, coe_trialityOrbitProd, h0, h1, h2]
  rfl

theorem coe_ox₄_eq (s : K) :
    ox₄ σ s = Xr d4N13 s * Xr d4N03 (σ s) * Xr d4N01 (σ (σ s)) := by
  have h0 : trialityRoot 3 = d4N13 := List.ofFn_injective (by decide +kernel)
  have h1 : permLattice TwistTag.D4.perm d4N13 = d4N03 :=
    List.ofFn_injective (by decide +kernel)
  have h2 : permLattice (TwistTag.D4.perm ^ 2) d4N13 = d4N01 :=
    List.ofFn_injective (by decide +kernel)
  rw [ox₄, trialityX₄, coe_trialityOrbitProd, h0, h1, h2]
  rfl

theorem coe_ox₂_eq (b : kk) : ox₂ σ b = Xr d4C (b : K) := by
  rw [← trialityRoot_one']; rfl

theorem coe_ox₅_eq (b : kk) : ox₅ σ b = Xr d4P (b : K) := by
  rw [← trialityRoot_four']; rfl

theorem coe_ox₆_eq (b : kk) : ox₆ σ b = Xr d4H (b : K) := by
  rw [← trialityRoot_five']; rfl

end Coe

section Norm

variable {K : Type} [Field K] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "kk" => trialityFixedField K σ.toRingHom

include hσ3 in
theorem sigma_sigma_sigma (s : K) : σ (σ (σ s)) = s :=
  ringHom_apply_apply_apply_of_pow_three hσ3 s

include hσ3 in
theorem nrm_mem (s : K) : s * σ s * σ (σ s) ∈ trialityFixedField K τ₀ := by
  rw [mem_trialityFixedField]
  change σ (s * σ s * σ (σ s)) = s * σ s * σ (σ s)
  rw [map_mul, map_mul, sigma_sigma_sigma σ hσ3]
  ring

@[expose] def nrm (s : K) : kk := ⟨s * σ s * σ (σ s), nrm_mem σ hσ3 s⟩

theorem coe_nrm (s : K) : ((nrm σ hσ3 s : kk) : K) = s * σ s * σ (σ s) := rfl

end Norm


section D4

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem conj_pinnedX_of_sum {α β γ : Fin TwistTag.D4.tag.rank → ℤ} (h : d4SumB α β γ = true)
    (s t : K) : Xr α s * Xr β t * (Xr α s)⁻¹ = Xr γ (s * t) * Xr β t := by
  rw [← commutator_of_d4SumB h s t, commutatorElement_def]
  group

theorem conj_pinnedX_of_comm {α β : Fin TwistTag.D4.tag.rank → ℤ} (h : d4CommB α β = true)
    (s t : K) : Xr α s * Xr β t * (Xr α s)⁻¹ = Xr β t := by
  rw [(commute_of_d4CommB h s t).eq, mul_inv_cancel_right]

theorem comm_root_gen (β s₀ s₁ s₃ : K) :
    ⁅Xr d4C β, Xr d4E0 s₀ * Xr d4E1 s₁ * Xr d4E3 s₃⁆ =
      Xr d4M0 (β * s₀) * Xr d4M1 (β * s₁) * Xr d4M3 (β * s₃) *
        (Xr d4N13 (s₁ * (β * s₃)) * Xr d4N03 (s₀ * (β * s₃)) * Xr d4N01 (s₀ * (β * s₁))) *
        Xr d4P (s₀ * (s₁ * (β * s₃))) * Xr d4H (s₀ * (β * s₁) * (β * s₃)) := by
  have hs : ∀ {α γ δ : Fin TwistTag.D4.tag.rank → ℤ}, d4SumB α γ δ = true → ∀ s t : K,
      ⁅Xr α s, Xr γ t⁆ = Xr δ (s * t) := fun h s t => commutator_of_d4SumB h s t
  have hc : ∀ {α γ : Fin TwistTag.D4.tag.rank → ℤ}, d4CommB α γ = true → ∀ s t : K,
      Commute (Xr α s) (Xr γ t) := fun h s t => commute_of_d4CommB h s t
  refine comm_expand (A := Xr d4C β) (Y0 := Xr d4E0 s₀) (Y1 := Xr d4E1 s₁) (Y3 := Xr d4E3 s₃)
    (M0 := Xr d4M0 (β * s₀)) (M1 := Xr d4M1 (β * s₁)) (M3 := Xr d4M3 (β * s₃))
    (N01 := Xr d4N01 (s₀ * (β * s₁))) (N03 := Xr d4N03 (s₀ * (β * s₃)))
    (N13 := Xr d4N13 (s₁ * (β * s₃))) (P := Xr d4P (s₀ * (s₁ * (β * s₃))))
    (H := Xr d4H (s₀ * (β * s₁) * (β * s₃)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hs (α := d4C) (γ := d4E0) (δ := d4M0) (by decide +kernel) β s₀
  · exact hs (α := d4C) (γ := d4E1) (δ := d4M1) (by decide +kernel) β s₁
  · exact hs (α := d4C) (γ := d4E3) (δ := d4M3) (by decide +kernel) β s₃
  · exact hs (α := d4E0) (γ := d4M1) (δ := d4N01) (by decide +kernel) s₀ (β * s₁)
  · exact hs (α := d4E1) (γ := d4M3) (δ := d4N13) (by decide +kernel) s₁ (β * s₃)
  · exact hs (α := d4E0) (γ := d4M3) (δ := d4N03) (by decide +kernel) s₀ (β * s₃)
  · exact hs (α := d4E0) (γ := d4N13) (δ := d4P) (by decide +kernel) s₀ (s₁ * (β * s₃))
  · exact hs (α := d4N01) (γ := d4M3) (δ := d4H) (by decide +kernel) _ _
  · exact hc (α := d4N01) (γ := d4M1) (by decide +kernel) _ _
  · exact hc (α := d4M3) (γ := d4N03) (by decide +kernel) _ _
  · exact hc (α := d4M3) (γ := d4N13) (by decide +kernel) _ _
  · exact hc (α := d4M3) (γ := d4P) (by decide +kernel) _ _
  · exact hc (α := d4H) (γ := d4M3) (by decide +kernel) _ _
  · exact hc (α := d4H) (γ := d4N01) (by decide +kernel) _ _
  · exact hc (α := d4H) (γ := d4P) (by decide +kernel) _ _
  · exact hc (α := d4H) (γ := d4N13) (by decide +kernel) _ _
  · exact hc (α := d4H) (γ := d4N03) (by decide +kernel) _ _
  · exact hc (α := d4N01) (γ := d4N13) (by decide +kernel) _ _
  · exact hc (α := d4N01) (γ := d4N03) (by decide +kernel) _ _
  · exact hc (α := d4P) (γ := d4N13) (by decide +kernel) _ _
  · exact hc (α := d4P) (γ := d4N03) (by decide +kernel) _ _

theorem comm_e0_m (u t₀ t₁ t₃ : K) :
    ⁅Xr d4E0 u, Xr d4M0 t₀ * Xr d4M1 t₁ * Xr d4M3 t₃⁆ =
      Xr d4N01 (u * t₁) * Xr d4H (t₁ * (u * t₃)) * Xr d4N03 (u * t₃) := by
  have e1 : ⁅Xr d4E0 u, Xr d4M0 t₀⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (commute_of_d4CommB (by decide +kernel) _ _)
  have e2 := commutator_of_d4SumB (α := d4E0) (β := d4M1) (γ := d4N01) (by decide +kernel) u t₁
  have e3 := commutator_of_d4SumB (α := d4E0) (β := d4M3) (γ := d4N03) (by decide +kernel) u t₃
  have e4 := conj_pinnedX_of_sum (α := d4M1) (β := d4N03) (γ := d4H) (by decide +kernel) t₁
    (u * t₃)
  have e5 := conj_pinnedX_of_comm (α := d4M0) (β := d4N01) (by decide +kernel) t₀ (u * t₁)
  have e6 := conj_pinnedX_of_comm (α := d4M0) (β := d4H) (by decide +kernel) t₀ (t₁ * (u * t₃))
  have e7 := conj_pinnedX_of_comm (α := d4M0) (β := d4N03) (by decide +kernel) t₀ (u * t₃)
  have key : ∀ a x y z : ModGL TwistTag.D4.tag K, ⁅a, x * y * z⁆ =
      ⁅a, x⁆ * (x * (⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹)) * x⁻¹) := fun a x y z => by
    simp only [commutatorElement_def]; group
  rw [key, e1, e2, e3, one_mul,
    show Xr d4M1 t₁ * Xr d4N03 (u * t₃) * (Xr d4M1 t₁)⁻¹ = _ from e4]
  have c3 : ∀ x y z : ModGL TwistTag.D4.tag K, Xr d4M0 t₀ * (x * (y * z)) * (Xr d4M0 t₀)⁻¹ =
      (Xr d4M0 t₀ * x * (Xr d4M0 t₀)⁻¹) * ((Xr d4M0 t₀ * y * (Xr d4M0 t₀)⁻¹) *
        (Xr d4M0 t₀ * z * (Xr d4M0 t₀)⁻¹)) := fun x y z => by group
  rw [c3, e5, e6, e7, mul_assoc]

theorem comm_e1_m (u t₀ t₁ t₃ : K) :
    ⁅Xr d4E1 u, Xr d4M0 t₀ * Xr d4M1 t₁ * Xr d4M3 t₃⁆ =
      Xr d4N01 (u * t₀) * Xr d4H (t₀ * (u * t₃)) * Xr d4N13 (u * t₃) := by
  have e1 := commutator_of_d4SumB (α := d4E1) (β := d4M0) (γ := d4N01) (by decide +kernel) u t₀
  have e2 : ⁅Xr d4E1 u, Xr d4M1 t₁⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (commute_of_d4CommB (by decide +kernel) _ _)
  have e3 := commutator_of_d4SumB (α := d4E1) (β := d4M3) (γ := d4N13) (by decide +kernel) u t₃
  have e4 := conj_pinnedX_of_comm (α := d4M1) (β := d4N13) (by decide +kernel) t₁ (u * t₃)
  have e5 := conj_pinnedX_of_sum (α := d4M0) (β := d4N13) (γ := d4H) (by decide +kernel) t₀
    (u * t₃)
  have key : ∀ a x y z : ModGL TwistTag.D4.tag K, ⁅a, x * y * z⁆ =
      ⁅a, x⁆ * (x * (⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹)) * x⁻¹) := fun a x y z => by
    simp only [commutatorElement_def]; group
  rw [key, e1, e2, e3, one_mul, e4, e5, mul_assoc]

theorem comm_e3_m (u t₀ t₁ t₃ : K) :
    ⁅Xr d4E3 u, Xr d4M0 t₀ * Xr d4M1 t₁ * Xr d4M3 t₃⁆ =
      Xr d4N03 (u * t₀) * Xr d4H (t₀ * (u * t₁)) * Xr d4N13 (u * t₁) := by
  have e1 := commutator_of_d4SumB (α := d4E3) (β := d4M0) (γ := d4N03) (by decide +kernel) u t₀
  have e2 := commutator_of_d4SumB (α := d4E3) (β := d4M1) (γ := d4N13) (by decide +kernel) u t₁
  have e3 : ⁅Xr d4E3 u, Xr d4M3 t₃⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (commute_of_d4CommB (by decide +kernel) _ _)
  have e5 := conj_pinnedX_of_sum (α := d4M0) (β := d4N13) (γ := d4H) (by decide +kernel) t₀
    (u * t₁)
  have key : ∀ a x y z : ModGL TwistTag.D4.tag K, ⁅a, x * y * z⁆ =
      ⁅a, x⁆ * (x * (⁅a, y⁆ * (y * ⁅a, z⁆ * y⁻¹)) * x⁻¹) := fun a x y z => by
    simp only [commutatorElement_def]; group
  rw [key, e1, e2, e3, mul_one, mul_inv_cancel, mul_one, e5, mul_assoc]

theorem abProd_mul (v w : K × K × K × K × K) : abProd v * abProd w = abProd (v + w) := by
  obtain ⟨a, b, c, d, e⟩ := v
  obtain ⟨a', b', c', d', e'⟩ := w
  exact prod5_mul (Xr d4N13) (Xr d4N03) (Xr d4N01) (Xr d4P) (Xr d4H)
    (pinnedX_add _ _ _) (pinnedX_add _ _ _) (pinnedX_add _ _ _) (pinnedX_add _ _ _)
    (pinnedX_add _ _ _)
    (commute_of_d4CommB (by decide +kernel)) (commute_of_d4CommB (by decide +kernel))
    (commute_of_d4CommB (by decide +kernel)) (commute_of_d4CommB (by decide +kernel))
    (commute_of_d4CommB (by decide +kernel)) (commute_of_d4CommB (by decide +kernel))
    (commute_of_d4CommB (by decide +kernel)) (commute_of_d4CommB (by decide +kernel))
    (commute_of_d4CommB (by decide +kernel)) (commute_of_d4CommB (by decide +kernel))
    a b c d e a' b' c' d' e'

theorem comm_e_m (s₀ s₁ s₃ t₀ t₁ t₃ : K) :
    ⁅Xr d4E0 s₀ * Xr d4E1 s₁ * Xr d4E3 s₃, Xr d4M0 t₀ * Xr d4M1 t₁ * Xr d4M3 t₃⁆ =
      abProd (s₃ * t₁ + s₁ * t₃, s₃ * t₀ + s₀ * t₃, s₁ * t₀ + s₀ * t₁,
        s₁ * (s₃ * t₀) + s₀ * (s₃ * t₁) + s₀ * (s₁ * t₃),
        t₀ * (s₃ * t₁) + t₀ * (s₁ * t₃) + t₁ * (s₀ * t₃)) := by
  set z := Xr d4M0 t₀ * Xr d4M1 t₁ * Xr d4M3 t₃
  have key : ∀ a b c : ModGL TwistTag.D4.tag K, ⁅a * b * c, z⁆ =
      a * (b * ⁅c, z⁆ * b⁻¹) * a⁻¹ * (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := fun a b c => by
    simp only [commutatorElement_def]; group
  rw [key, comm_e3_m, comm_e1_m, comm_e0_m]
  have conj3 : ∀ g x y w : ModGL TwistTag.D4.tag K, g * (x * y * w) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) * (g * w * g⁻¹) := fun g x y w => by group
  have f1 := conj_pinnedX_of_sum (α := d4E1) (β := d4N03) (γ := d4P) (by decide +kernel) s₁
    (s₃ * t₀)
  have f2 := conj_pinnedX_of_comm (α := d4E1) (β := d4H) (by decide +kernel) s₁
    (t₀ * (s₃ * t₁))
  have f3 := conj_pinnedX_of_comm (α := d4E1) (β := d4N13) (by decide +kernel) s₁ (s₃ * t₁)
  have g1 := conj_pinnedX_of_comm (α := d4E0) (β := d4P) (by decide +kernel) s₀
    (s₁ * (s₃ * t₀))
  have g2 := conj_pinnedX_of_comm (α := d4E0) (β := d4N03) (by decide +kernel) s₀ (s₃ * t₀)
  have g3 := conj_pinnedX_of_comm (α := d4E0) (β := d4H) (by decide +kernel) s₀
    (t₀ * (s₃ * t₁))
  have g4 := conj_pinnedX_of_sum (α := d4E0) (β := d4N13) (γ := d4P) (by decide +kernel) s₀
    (s₃ * t₁)
  have g5 := conj_pinnedX_of_comm (α := d4E0) (β := d4N01) (by decide +kernel) s₀ (s₁ * t₀)
  have g6 := conj_pinnedX_of_comm (α := d4E0) (β := d4H) (by decide +kernel) s₀
    (t₀ * (s₁ * t₃))
  have g7 := conj_pinnedX_of_sum (α := d4E0) (β := d4N13) (γ := d4P) (by decide +kernel) s₀
    (s₁ * t₃)
  rw [conj3 (Xr d4E1 s₁), f1, f2, f3]
  have conj4 : ∀ g x y w v : ModGL TwistTag.D4.tag K, g * (x * y * w * v) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) * (g * w * g⁻¹) * (g * v * g⁻¹) := fun g x y w v => by
    group
  rw [conj4, g1, g2, g3, g4, conj3, g5, g6, g7]
  simp only [abProd_n13, abProd_n03, abProd_n01, abProd_p, abProd_h, abProd_mul]
  congr 1
  simp only [Prod.mk_add_mk, add_zero, zero_add]

end D4

section Triality

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "kk" => trialityFixedField K σ.toRingHom

theorem ox₂_comm_ox₁_gen (β : kk) (s : K) :
    ⁅ox₂ σ β, ox₁ σ s⁆ = ox₃ σ ((β : K) * s) * ox₄ σ ((β : K) * (σ s * σ (σ s))) *
      ox₅ σ (β * nrm σ hσ3 s) * ox₆ σ (β * β * nrm σ hσ3 s) := by
  have hβ : σ (β : K) = β := β.2
  have h3 := sigma_sigma_sigma σ hσ3
  rw [coe_ox₂_eq, coe_ox₁_eq, comm_root_gen, coe_ox₃_eq, coe_ox₄_eq, coe_ox₅_eq, coe_ox₆_eq]
  have f1 : Xr d4M1 (σ ((β : K) * s)) = Xr d4M1 (β * σ s) := by rw [map_mul, hβ]
  have f2 : Xr d4M3 (σ (σ ((β : K) * s))) = Xr d4M3 (β * σ (σ s)) := by
    rw [map_mul, map_mul, hβ, hβ]
  have f3 : Xr d4N13 (σ s * ((β : K) * σ (σ s))) = Xr d4N13 (β * (σ s * σ (σ s))) := by
    congr 1; ring
  have f4 : Xr d4N03 (s * ((β : K) * σ (σ s))) =
      Xr d4N03 (σ ((β : K) * (σ s * σ (σ s)))) := by
    congr 1; simp only [map_mul, hβ, h3]; try ring
  have f5 : Xr d4N01 (s * ((β : K) * σ s)) =
      Xr d4N01 (σ (σ ((β : K) * (σ s * σ (σ s))))) := by
    congr 1; simp only [map_mul, hβ, h3]; try ring
  have f6 : Xr d4P (s * (σ s * ((β : K) * σ (σ s)))) =
      Xr d4P ((β * nrm σ hσ3 s : kk) : K) := by
    congr 1; rw [Subfield.coe_mul, coe_nrm]; ring
  have f7 : Xr d4H (s * ((β : K) * σ s) * ((β : K) * σ (σ s))) =
      Xr d4H ((β * β * nrm σ hσ3 s : kk) : K) := by
    congr 1; rw [Subfield.coe_mul, Subfield.coe_mul, coe_nrm]; ring
  rw [f1, f2, f3, f4, f5, f6, f7]

theorem ox₁_comm_ox₃ (s t : K) :
    ⁅ox₁ σ s, ox₃ σ t⁆ = ox₄ σ (σ s * σ (σ t) + σ (σ s) * σ t) *
      ox₅ σ (trialityTrace K τ₀ hσ3 (s * σ s * σ (σ t))) *
      ox₆ σ (trialityTrace K τ₀ hσ3 (s * σ t * σ (σ t))) := by
  have h3 := sigma_sigma_sigma σ hσ3
  rw [coe_ox₁_eq, coe_ox₃_eq, comm_e_m, coe_ox₄_eq, coe_ox₅_eq, coe_ox₆_eq, abProd,
    coe_trialityTrace, coe_trialityTrace]
  have f1 : Xr d4N13 (σ (σ s) * σ t + σ s * σ (σ t)) =
      Xr d4N13 (σ s * σ (σ t) + σ (σ s) * σ t) := by congr 1; ring
  have f2 : Xr d4N03 (σ (σ s) * t + s * σ (σ t)) =
      Xr d4N03 (σ (σ s * σ (σ t) + σ (σ s) * σ t)) := by
    congr 1; simp only [map_add, map_mul, h3]; try ring
  have f3 : Xr d4N01 (σ s * t + s * σ t) =
      Xr d4N01 (σ (σ (σ s * σ (σ t) + σ (σ s) * σ t))) := by
    congr 1; simp only [map_add, map_mul, h3]; try ring
  have f4 : Xr d4P (σ s * (σ (σ s) * t) + s * (σ (σ s) * σ t) + s * (σ s * σ (σ t))) =
      Xr d4P (s * σ s * σ (σ t) + σ (s * σ s * σ (σ t)) + σ (σ (s * σ s * σ (σ t)))) := by
    congr 1; simp only [map_mul, h3]; try ring
  have f5 : Xr d4H (t * (σ (σ s) * σ t) + t * (σ s * σ (σ t)) + σ t * (s * σ (σ t))) =
      Xr d4H (s * σ t * σ (σ t) + σ (s * σ t * σ (σ t)) + σ (σ (s * σ t * σ (σ t)))) := by
    congr 1; simp only [map_mul, h3]; try ring
  rw [f1, f2, f3, f4, f5]
  rfl

end Triality

end CFSG.Quasithin.B42D4
