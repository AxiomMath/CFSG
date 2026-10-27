module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Vol2.Ch3E213MDefs

public section

namespace CFSG.Quasithin.Ch3E213M.OL

open CFSG.Open CFSG.QuasithinUnique B6 E2P
open CFSG.OrderReductions.FrattiniAutomorphisms

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem exists_quadratic_module (hS : Setting H T M V K) (hJU : kerIn M H ≤ pCoreOf 2 H)
    (hnot2 : ¬ IsPGroup 2 ↥(E2.star M H K)) :
    ∃ (W : Type) (_ : Group W) (_ : Finite W), (∀ a b : W, a * b = b * a) ∧
      (∀ a : W, a * a = 1) ∧ ∃ ρ : E2.StarQuot M H →* MulAut W,
        (∃ k ∈ E2.star M H K, ρ k ≠ 1) ∧
        ∀ v ∈ E2.star M H V, ∀ v' ∈ E2.star M H V, ∀ w : W,
          ρ v (ρ v' w * w⁻¹) * (ρ v' w * w⁻¹)⁻¹ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHU : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  set U₀ : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H with hU₀
  have hU₀n : U₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr hHU
  have hU₀2 : IsPGroup 2 ↥U₀ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).of_equiv
    (Subgroup.subgroupOfEquivOfLe hUH).symm
  obtain ⟨-, hcommW, hpowW, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hU₀2
  have hc : ∀ a b : ↥U₀ ⧸ frattini ↥U₀, a * b = b * a := fun a b => hcommW.is_comm.comm a b
  let ρH : ↥H →* MulAut (↥U₀ ⧸ frattini ↥U₀) :=
    quotientAction (frattini ↥U₀) (MulAut.conjNormal : ↥H →* MulAut ↥U₀)
  have hρH : ∀ (h : ↥H) (u : ↥U₀), ρH h (u : ↥U₀ ⧸ frattini ↥U₀) =
      ((MulAut.conjNormal h u : ↥U₀) : ↥U₀ ⧸ frattini ↥U₀) := fun h u =>
    quotientAction_apply (frattini ↥U₀) _ h u
  have hρker : (kerIn M H).subgroupOf H ≤ ρH.ker := by
    intro j hj
    rw [MonoidHom.mem_ker]
    ext w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
    have hjU : j ∈ U₀ := Subgroup.mem_subgroupOf.mpr (hJU (Subgroup.mem_subgroupOf.mp hj))
    rw [hρH]
    have h1 : (MulAut.conjNormal j u : ↥U₀) = ⟨j, hjU⟩ * u * (⟨j, hjU⟩ : ↥U₀)⁻¹ :=
      Subtype.ext (MulAut.conjNormal_apply j u)
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      hc (((⟨j, hjU⟩ : ↥U₀)) : ↥U₀ ⧸ frattini ↥U₀), mul_inv_cancel_right]
    rfl
  let ρ : E2.StarQuot M H →* MulAut (↥U₀ ⧸ frattini ↥U₀) :=
    QuotientGroup.lift ((kerIn M H).subgroupOf H) ρH hρker
  have hρ : ∀ h : ↥H, ρ (starMap M H h) = ρH h := fun h => rfl
  refine ⟨↥U₀ ⧸ frattini ↥U₀, inferInstance, inferInstance, hc,
    fun a => by rw [← pow_two]; exact hpowW a, ρ, ?_, ?_⟩
  ·
    by_contra hcon
    have hall : ∀ k ∈ E2.star M H K, ρ k = 1 := fun k hk => not_not.mp fun h => hcon ⟨k, hk, h⟩
    apply hnot2
    rintro ⟨y, hy⟩
    rw [star_def] at hy
    obtain ⟨h, hhK, rfl⟩ := hy
    obtain ⟨a, m, hmodd, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
    set h₁ := h ^ 2 ^ a with hh₁
    have hh₁m : h₁ ^ m = 1 := by rw [hh₁, ← pow_mul, ← ham, pow_orderOf_eq_one]
    have hh₁K : (h₁ : G) ∈ K := by
      rw [hh₁, Subgroup.coe_pow]
      exact K.pow_mem (Subgroup.mem_subgroupOf.mp hhK) _
    have hρ1 : ρH h₁ = 1 := by
      have h1 := hall (starMap M H h₁) ⟨h₁, Subgroup.mem_subgroupOf.mpr hh₁K, rfl⟩
      rwa [hρ] at h1
    have hτker : MulAut.conjNormal h₁ ∈ (quotientAutomorphism (frattini ↥U₀)).ker := hρ1
    obtain ⟨j, hj⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hU₀2).2 ⟨_, hτker⟩
    have hτj : (MulAut.conjNormal h₁ : MulAut ↥U₀) ^ 2 ^ j = 1 := by
      simpa using congrArg Subtype.val hj
    have hτm : (MulAut.conjNormal h₁ : MulAut ↥U₀) ^ m = 1 := by rw [← map_pow, hh₁m, map_one]
    have hcop : Nat.Coprime m (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hmodd)
    have hτ1 : (MulAut.conjNormal h₁ : MulAut ↥U₀) = 1 := by
      have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτm) (orderOf_dvd_of_pow_eq_one hτj)
      rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h2
      exact h2
    have hh₁C : (h₁ : G) ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      set u : ↥U₀ := ⟨⟨x, hUH hx⟩, Subgroup.mem_subgroupOf.mpr hx⟩ with hu
      have h1 : MulAut.conjNormal h₁ u = u := DFunLike.congr_fun hτ1 u
      have h2 : (h₁ : G) * x * (h₁ : G)⁻¹ = x := by
        have h3 := congrArg (fun y : ↥U₀ => ((y : ↥H) : G)) h1
        simpa [MulAut.conjNormal_apply, hu] using h3
      calc x * (h₁ : G) = (h₁ : G) * x * (h₁ : G)⁻¹ * (h₁ : G) := by rw [h2]
        _ = (h₁ : G) * x := by group
    have hh₁U : (h₁ : G) ∈ pCoreOf 2 H := hS.charTwo ⟨h₁.2, hh₁C⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨(h₁ : G), hh₁U⟩
    have hh₁k : h₁ ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hcop' : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hmodd)
    have hh₁1 : h₁ = 1 := by
      have h2 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hh₁m) (orderOf_dvd_of_pow_eq_one hh₁k)
      rw [hcop'.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h2
      exact h2
    refine ⟨a, Subtype.ext ?_⟩
    show (starMap M H h) ^ 2 ^ a = 1
    rw [← map_pow, ← hh₁, hh₁1, map_one]
  ·
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
    have haV : (a : G) ∈ V := Subgroup.mem_subgroupOf.mp ha
    have hbV : (b : G) ∈ V := Subgroup.mem_subgroupOf.mp hb
    have huU : ((u : ↥H) : G) ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp u.2
    have huT : ((u : ↥H) : G) ∈ T :=
      CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS.hyp.minParabolic.isSylow huU
    set c₀ : ↥U₀ := MulAut.conjNormal b u * u⁻¹ with hc₀
    have hc₀G : ((c₀ : ↥H) : G) =
        (b : G) * (((u : ↥H) : G) * (b : G)⁻¹ * ((u : ↥H) : G)⁻¹) := by
      rw [hc₀]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      group
    have hc₀V : ((c₀ : ↥H) : G) ∈ V := by
      rw [hc₀G]
      exact V.mul_mem hbV
        ((Subgroup.mem_normalizer_iff.mp (hS.hyp.normal_T huT) _).mp (V.inv_mem hbV))
    have hcomm : (a : G) * ((c₀ : ↥H) : G) = ((c₀ : ↥H) : G) * (a : G) :=
      congrArg Subtype.val (hS.hyp.elem.1.is_comm.comm ⟨a, haV⟩ ⟨_, hc₀V⟩)
    have e1 : ρ (starMap M H b) (u : ↥U₀ ⧸ frattini ↥U₀) * (u : ↥U₀ ⧸ frattini ↥U₀)⁻¹ =
        (c₀ : ↥U₀ ⧸ frattini ↥U₀) := by
      rw [hρ, hρH, hc₀, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [e1, hρ, hρH]
    have e2 : (MulAut.conjNormal a c₀ : ↥U₀) = c₀ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm, mul_inv_cancel_right]
    rw [e2, mul_inv_cancel]

end CFSG.Quasithin.Ch3E213M.OL
