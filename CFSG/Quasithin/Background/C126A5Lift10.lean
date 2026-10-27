module

public import CFSG.Quasithin.Background.C126A5Lift9
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C126A5Lift8

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem cv_comm {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G}
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (hb : b ∈ Subgroup.normalizer (V : Set G)) :
    cv hV (a * b * a⁻¹ * b⁻¹) = cv hV a * cv hV b * (cv hV a)⁻¹ * (cv hV b)⁻¹ := by
  have h1 := Subgroup.mul_mem _ ha hb
  have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ ha)
  rw [cv_mul hV h2 (Subgroup.inv_mem _ hb), cv_mul hV h1 (Subgroup.inv_mem _ ha),
    cv_mul hV ha hb, cv_inv hV ha, cv_inv hV hb]

theorem Data.th_comm {H T V Y : Subgroup G} {hV : IsElemAbelian 2 V} (d : Data H T V Y hV)
    {φ ψ : MulAut (IntMod V hV)} (hφ : φ ∈ d.L) (hψ : ψ ∈ d.L) :
    d.th (φ * ψ * φ⁻¹ * ψ⁻¹) = d.th φ * d.th ψ * (d.th φ)⁻¹ * (d.th ψ)⁻¹ := by
  have h1 := d.L.mul_mem hφ hψ
  have h2 := d.L.mul_mem h1 (d.L.inv_mem hφ)
  rw [d.th_mul h2 (d.L.inv_mem hψ), d.th_mul h1 (d.L.inv_mem hφ), d.th_mul hφ hψ,
    d.th_inv hφ, d.th_inv hψ]

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem gen_eq : H = T ⊔ conjClosure (Khat s d x) T := by
  apply le_antisymm
  · calc H = Y ⊔ T := s.gen.symm
      _ ≤ T ⊔ conjClosure (Khat s d x) T :=
        sup_le ((hx.Y_le_Khat.trans (le_conjClosure _ _)).trans le_sup_right) le_sup_left
  · refine sup_le s.hT.1 (conjClosure_le fun t ht k hk => ?_)
    exact H.mul_mem (H.mul_mem (s.hT.1 ht) (hx.Khat_le_H hk)) (H.inv_mem (s.hT.1 ht))

variable (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hY hA3

theorem commutator_eq
    (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    ⁅Khat s d x, thompsonJ T⁆ = Khat s d x := by
  have hK := hx.isShort2 hY hA3 hRad
  have hJT : thompsonJ T ≤ H := (thompsonJ_le T).trans s.hT.1
  obtain ⟨φ, hφJ, hφL, hφθ⟩ := d.t_lift
  obtain ⟨t₀, ht₀J, hcv⟩ := (mem_autI_iff hV (hJT.trans s.H_le_N)).1 hφJ
  have hN₁ : ⁅Khat s d x, thompsonJ T⁆ ≤ Khat s d x := by
    rw [Subgroup.commutator_le]
    intro k hk t ht
    have h1 := hx.Jt_conj_mem_Khat hRad (thompsonJ_le_Jt s ht) ((Khat s d x).inv_mem hk)
    have e : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Khat s d x).mul_mem hk h1
  have hN₂ : Khat s d x ≤ Subgroup.normalizer ((⁅Khat s d x, thompsonJ T⁆ : Subgroup G) : Set G) :=
    A3.le_normalizer_commutator_left _ _
  have hq : IsAltQuotient (Khat s d x) (Subgroup.centralizer (V : Set G)) 5 :=
    ⟨hx.alpha, hx.alpha_surj, hx.alpha_ker_C⟩
  refine C1GN.isShort2_eq_of_isAltQuotient hK (by decide) (by norm_num) hq hN₁ hN₂ ?_
  intro hle
  have hxK : x ∈ Khat s d x := hx.zpowers_le_Khat (Subgroup.mem_zpowers x)
  have hc : ⁅x, t₀⁆ ∈ ⁅Khat s d x, thompsonJ T⁆ := Subgroup.commutator_mem_commutator hxK ht₀J
  have hc1 : ⁅x, t₀⁆ ∈ Subgroup.centralizer (V : Set G) := hle hc
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (s.Y_le hx.mem)
  have ht₀N : t₀ ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (hJT ht₀J)
  have hmem : x * t₀ * x⁻¹ * t₀⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN ht₀N)
      (Subgroup.inv_mem _ hxN)) (Subgroup.inv_mem _ ht₀N)
  have h1 : cv hV (x * t₀ * x⁻¹ * t₀⁻¹) = 1 := by
    rw [cv_eq_one_iff hV hmem]
    rwa [commutatorElement_def] at hc1
  rw [cv_comm hV hxN ht₀N] at h1
  have hb₀ : cv hV t₀ ∈ d.L := hcv ▸ hφL
  have h2 := congrArg d.th h1
  rw [d.th_comm hx.mem_L hb₀, d.th_one] at h2
  have hb₀th : d.th (cv hV t₀) = swap (d.π 2) (d.π 3) := by
    rw [hcv, d.th_of_mem hφL]
    exact hφθ
  rw [hx.th_eq, hb₀th, comm_cyc3_swap] at h2
  exact cyc3_mul_self_ne_one d.π h2

theorem oneBlock (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    OneBlock H T :=
  ⟨Khat s d x, hx.isChi0Block hY hA3 hRad, hx.commutator_eq hY hA3 hRad, hx.gen_eq⟩

end XData

end Lift

end CFSG.Quasithin.C126.A5
