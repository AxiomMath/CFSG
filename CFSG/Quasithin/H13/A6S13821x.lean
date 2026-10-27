module

public import CFSG.Quasithin.H13.A6S13821p
public import CFSG.Quasithin.H13.A6S13821q
public import CFSG.Quasithin.H13.A6S13821w
public import CFSG.Quasithin.H13.A6S13821r
public import CFSG.Quasithin.H13.A6S13821t
public import CFSG.Quasithin.H13.A6S13821v

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_isPSL_kst_of_not_hat (h16 : Lem13816)
    (h1376 : Lem1376Full) (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hS : S.Hyp138) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L) : ¬ IsPSL 3 2 1 ↥(S.KSt H H) := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab := L13825.isElemAbelian_UH hS hH
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hab.1
  obtain ⟨θ, hθs, hker, hθT, hθL⟩ := S.exists_theta_l32 hS hH hhat hP
  obtain ⟨K, hK, hKn, hHK⟩ := S.exists_cComp_l32 h16 hS hH hhat hP
  have hθK := map_eq_top_of_cComp hθs hker hK hKn
  have D := S.secMod_UH hS hH hθs hker
  have := D.normal
  obtain ⟨ρ, hρ, hcases⟩ := A6S19.cases_of_secMod D (S.v2_mem_UH H)
    (S.comm_v2_of_borel hS hH hker hθT) (S.mem_closure_v2 hS hH) rfl
    (S.relIndex_closure_v2_Ll hS hH hker hθL)
  have hNN : A6S19.NotNat ρ := by
    rcases hcases with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact (S.false_of_isoMod_v h1376 hS hH D hK hθK hρ h).elim
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hLTH : S.L1 ⊔ T ≤ H := hH.1.1
  rcases S.exists_transv_or_quad h36 h139 h1334 h13 h13314 h13315 h1356two hS hH hK hKn hHK with
    ⟨x, hxR, htr⟩ | ⟨Y, hYR, hYq, hY4⟩
  ·
    have hxH : x ∈ H := hLTH (pCoreOf_le 2 _ hxR)
    have hg := S.theta_mem_Ul hθT hθL (x := ⟨x, hxH⟩) hxR
    obtain ⟨hnot, c, hc⟩ := htr
    push Not at hnot
    obtain ⟨x₀, hx₀, hd⟩ := hnot
    have hg1 : θ ⟨x, hxH⟩ ≠ 1 := fun h1 =>
      hd ((S.mem_QH_iff hS hH hxH).mp ((hker _).mp h1) x₀ hx₀)
    have hxN := le_normalizer_conjClosure S.V3 H hxH
    have hdX : x * x₀ * x⁻¹ * x₀⁻¹ ∈ conjClosure S.V3 H :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hxN x₀).mp hx₀)
        (Subgroup.inv_mem _ hx₀)
    have hd' := (hc x₀ hx₀).resolve_left hd
    have hcoe : ∀ s : ↥(conjClosure S.V3 H),
        ((D.conjX ⟨x, hxH⟩ s / s : ↥(conjClosure S.V3 H)) : G) = x * s * x⁻¹ * s⁻¹ :=
      fun s => by
        rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, L32A.SecMod.coe_conjX]
    refine A6S19.false_of_transv hNN hg hg1
      (d := Additive.ofMul (QuotientGroup.mk ⟨_, hdX⟩)) fun m => ?_
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective m
    induction q using QuotientGroup.induction_on with
    | H s =>
    rw [hρ, ← ofMul_div, ← QuotientGroup.mk_div]
    rcases hc s s.2 with h1 | h1
    · left
      rw [← ofMul_one]
      congr 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hcoe]
      exact h1
    · right
      congr 1
      rw [D.mk_eq_mk_iff, hcoe]
      have e : x * s * x⁻¹ * s⁻¹ * (x * x₀ * x⁻¹ * x₀⁻¹)⁻¹ =
          (x * s * x⁻¹ * s⁻¹ * c⁻¹) * (x * x₀ * x⁻¹ * x₀⁻¹ * c⁻¹)⁻¹ := by group
      show x * s * x⁻¹ * s⁻¹ * (x * x₀ * x⁻¹ * x₀⁻¹)⁻¹ ∈ fsuV1 T V
      rw [e]
      exact (fsuV1 T V).mul_mem h1 ((fsuV1 T V).inv_mem hd')
  ·
    have hYH : Y ≤ H := hYR.trans ((pCoreOf_le 2 _).trans hLTH)
    have hθY : (Y.subgroupOf H).map θ = A6S19.Ul := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨y, hy, rfl⟩
        exact S.theta_mem_Ul hθT hθL (hYR (Subgroup.mem_subgroupOf.mp hy))
      · rw [A6S19.card_Ul, ← Subgroup.relIndex_ker]
        have hk : θ.ker = (pCoreOf 2 H).subgroupOf H := by
          ext h
          rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
        rw [hk, Subgroup.relIndex_subgroupOf hYH]
        rwa [Subgroup.inf_relIndex_left] at hY4
    refine A6S19.false_of_quad hNN fun a ha b hb m => ?_
    rw [← hθY] at ha hb
    obtain ⟨ya, hya, rfl⟩ := ha
    obtain ⟨yb, hyb, rfl⟩ := hb
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective m
    induction q using QuotientGroup.induction_on with
    | H s =>
    rw [hρ, ← ofMul_div, ← QuotientGroup.mk_div, hρ]
    have hw : D.conjX yb (s / D.conjX ya s) = s / D.conjX ya s := by
      apply Subtype.ext
      rw [L32A.SecMod.coe_conjX]
      have hc1 : ((s / D.conjX ya s : ↥(conjClosure S.V3 H)) : G) = ⁅(s : G), (ya : G)⁆ := by
        rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, L32A.SecMod.coe_conjX,
          commutatorElement_def]
        group
      rw [hc1]
      have h1 : ⁅⁅(s : G), (ya : G)⁆, (yb : G)⁆ = 1 := by
        have h2 := Subgroup.commutator_mem_commutator
          (Subgroup.commutator_mem_commutator s.2 (Subgroup.mem_subgroupOf.mp hya))
          (Subgroup.mem_subgroupOf.mp hyb)
        rw [hYq] at h2
        exact h2
      have h3 := (commutatorElement_eq_one_iff_commute.mp h1).eq
      rw [← h3, mul_inv_cancel_right]
    rw [hw]

end Setting4

theorem lem13819_of (h16 : Lem13816) (h1376 : Lem1376Full)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) : Lem13819 := by
  intro G _ _ T L V S hS H hH
  by_cases hhat : IsHatA6 L
  · exact S.not_isPSL_kst_of_hat hS hH hhat
  · exact S.not_isPSL_kst_of_not_hat h16 h1376 h36 h139 h1334 h13 h13314 h13315 h1356two hS hH
      hhat

end CFSG.Quasithin.H13.A6
