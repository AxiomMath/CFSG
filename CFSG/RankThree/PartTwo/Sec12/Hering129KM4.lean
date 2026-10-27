module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KH1
public import CFSG.RankThree.PartTwo.Sec12.Hering129KM1
public import CFSG.RankThree.PartTwo.Sec12.Hering129KM3
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Open (StatedScalars)
open Matrix (ProjGenLinGroup)

section Group

variable {G : Type} [Group G] {x₁ x₂ n₁ : G}

theorem km4_not_mem_zpowers (h1 : x₁ ^ 3 = 1) (hx₁ : x₁ ≠ 1)
    (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁) :
    x₂ ∉ Subgroup.zpowers x₁ := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have e : x₁ = x₁ ^ (-(k * k)) := by
    calc x₁ = n₁ * x₂ * n₁⁻¹ := hF2.symm
      _ = n₁ * x₁ ^ k * n₁⁻¹ := by rw [hk]
      _ = (n₁ * x₁ * n₁⁻¹) ^ k := conj_zpow.symm
      _ = (x₂⁻¹) ^ k := by rw [hF1]
      _ = x₁ ^ (-(k * k)) := by rw [← hk, inv_zpow, ← zpow_neg, ← zpow_mul, mul_neg]
  have hx : x₁ ^ (k * k + 1) = 1 := by
    calc x₁ ^ (k * k + 1) = x₁ ^ (k * k) * x₁ := zpow_add_one _ _
      _ = x₁ ^ (k * k) * x₁ ^ (-(k * k)) := by rw [← e]
      _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
  have hord : orderOf x₁ = 3 := orderOf_eq_prime h1 hx₁
  have hdvd : (3 : ℤ) ∣ k * k + 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hx
    rwa [hord] at this
  have h0 : ((k * k + 1 : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvd
  push_cast at h0
  generalize (k : ZMod 3) = z at h0
  revert z
  decide

theorem km4_card_nine [Finite G] (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hx₁ : x₁ ≠ 1) (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁) :
    Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup G) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx₂ : x₂ ≠ 1 := by
    rintro rfl
    apply hx₁
    rw [← hF2]
    group
  have hA : Nat.card (Subgroup.zpowers x₁) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h1 hx₁]
  have hB : Nat.card (Subgroup.zpowers x₂) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h2 hx₂]
  have hcomm : ∀ x ∈ Subgroup.zpowers x₁, ∀ y ∈ Subgroup.zpowers x₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow h12 i j).eq
  have hinf : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
    have hIle : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ ≤ Subgroup.zpowers x₁ := inf_le_left
    have hdvd : Nat.card ↥(Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂) ∣ 3 := by
      rw [← hA]
      exact Subgroup.card_dvd_of_le hIle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = Subgroup.zpowers x₁ :=
        Subgroup.eq_of_le_of_card_ge hIle (by rw [h, hA])
      have hle : Subgroup.zpowers x₁ ≤ Subgroup.zpowers x₂ := heq ▸ inf_le_right
      have heq2 : Subgroup.zpowers x₁ = Subgroup.zpowers x₂ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hA, hB])
      exact km4_not_mem_zpowers h1 hx₁ hF1 hF2 (heq2 ▸ Subgroup.mem_zpowers x₂)
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hinf, Subgroup.card_bot, hA, hB] at h
  omega

end Group

section Frame

variable {K : Type} [Field K]

theorem km4_scalar_comm (u : Kˣ) (A : GL (Fin 3) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) u * A =
      A * Matrix.GeneralLinearGroup.scalar (Fin 3) u :=
  (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq.symm

theorem km4_mk_conj (g A : GL (Fin 3) K) :
    ProjGenLinGroup.mk (g * A * g⁻¹) =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk A * (ProjGenLinGroup.mk g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem km4_mk_conj_diagTau_ne_one {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (g : GL (Fin 3) K) :
    ProjGenLinGroup.mk (g * Sec4.diagTau hτ * g⁻¹) ≠ 1 := by
  intro h
  rw [Sec4.mk_eq_one_iff_mem_statedScalars] at h
  obtain ⟨u, hu⟩ := h
  have hd : Sec4.diagTau hτ = Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
    calc Sec4.diagTau hτ = g⁻¹ * (g * Sec4.diagTau hτ * g⁻¹) * g := by group
      _ = g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) u * g := by rw [← hu]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u := by
        rw [mul_assoc, km4_scalar_comm u g]
        group
  have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hd
  have h22 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) hd
  simp [Sec4.coe_diagTau, Matrix.scalar_apply] at h00 h22
  exact hτ1 (h00.trans h22.symm)

theorem km4_comm_diagTau_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    Sec4.diagTau hτ * Sec4.cycThree * (Sec4.diagTau hτ)⁻¹ * Sec4.cycThree⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) := by
  have h1 := Sec4.cycThree_pow_conj_diagTau hτ hτ0 1
  rw [pow_one, mul_one] at h1
  have hu : (Units.mk0 τ hτ0 ^ 2)⁻¹ = Units.mk0 τ hτ0 := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ← pow_succ]
    exact hτ
  calc Sec4.diagTau hτ * Sec4.cycThree * (Sec4.diagTau hτ)⁻¹ * Sec4.cycThree⁻¹ =
      (Sec4.cycThree * Sec4.diagTau hτ * Sec4.cycThree⁻¹ * (Sec4.diagTau hτ)⁻¹)⁻¹ := by group
    _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * Sec4.diagTau hτ *
        (Sec4.diagTau hτ)⁻¹)⁻¹ := by rw [h1]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2))⁻¹ := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) := by rw [← map_inv, hu]

theorem km4_diagUnits_comm {τ : K} (hτ : τ ^ 3 = 1) (a b c : Kˣ) :
    Sec4.diagUnits a b c * Sec4.diagTau hτ = Sec4.diagTau hτ * Sec4.diagUnits a b c := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  rw [Sec4.diagTau_eq_diagUnits hτ hτ0, Sec4.diagUnits_mul, Sec4.diagUnits_mul]
  congr 1 <;> exact mul_comm _ _

theorem km4_conj_cycThree (a b c : Kˣ) :
    Sec4.diagUnits a b c * Sec4.cycThree * (Sec4.diagUnits a b c)⁻¹ =
      Sec4.cycThree * Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹) := by
  have h := Sec4.cycThree_inv_conj_diagUnits (K := K) a b c
  have hinv : (Sec4.diagUnits a b c : GL (Fin 3) K)⁻¹ = Sec4.diagUnits a⁻¹ b⁻¹ c⁻¹ :=
    Units.ext rfl
  calc Sec4.diagUnits a b c * Sec4.cycThree * (Sec4.diagUnits a b c)⁻¹ =
      Sec4.cycThree * (Sec4.cycThree⁻¹ * Sec4.diagUnits a b c * Sec4.cycThree) *
        (Sec4.diagUnits a b c)⁻¹ := by group
    _ = Sec4.cycThree * (Sec4.diagUnits b c a * Sec4.diagUnits a⁻¹ b⁻¹ c⁻¹) := by
      rw [h, hinv]
      group
    _ = Sec4.cycThree * Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹) := by
      rw [Sec4.diagUnits_mul]

theorem km4_mk_diagUnits_eq {τ : K} (hτ : τ ^ 3 = 1) {u v w : Kˣ}
    (hu : (u : K) = w * τ) (hv : (v : K) = w * τ ^ 2) :
    ProjGenLinGroup.mk (Sec4.diagUnits u v w) = ProjGenLinGroup.mk (Sec4.diagTau hτ) := by
  refine Sec4.mk_eq_of_coe_eq_smul (a := (w : K)) ?_
  rw [Sec4.coe_diagUnits_eq, Sec4.coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hu, hv]

theorem km4_mk_diagUnits_eq_inv {τ : K} (hτ : τ ^ 3 = 1) {u v w : Kˣ}
    (hu : (u : K) = w * τ ^ 2) (hv : (v : K) = w * τ) :
    ProjGenLinGroup.mk (Sec4.diagUnits u v w) = (ProjGenLinGroup.mk (Sec4.diagTau hτ))⁻¹ := by
  rw [← map_inv]
  refine Sec4.mk_eq_of_coe_eq_smul (a := (w : K)) ?_
  rw [Sec4.coe_diagUnits_eq, show (((Sec4.diagTau hτ)⁻¹ : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hu, hv]

theorem km4_mk_shape {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {a b c e : Kˣ}
    (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1)
    (hshape : (a = e ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = e ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = e)) :
    ProjGenLinGroup.mk (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹)) =
        ProjGenLinGroup.mk (Sec4.diagTau hτ) ∨
      ProjGenLinGroup.mk (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹)) =
        (ProjGenLinGroup.mk (Sec4.diagTau hτ))⁻¹ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hs := Sec4.one_add_tau_add_sq hτ hτ1
  have he : (e : K) = τ ∨ (e : K) = τ ^ 2 := by
    rcases Sec4.eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 he3 with h | h | h
    · exact absurd (Units.ext h) he1
    · exact Or.inl h
    · exact Or.inr h
  rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rcases he with he | he
  all_goals first
    | (left; refine km4_mk_diagUnits_eq hτ ?_ ?_ <;> simp [he] <;> field_simp <;> grind)
    | (right; refine km4_mk_diagUnits_eq_inv hτ ?_ ?_ <;> simp [he] <;> field_simp <;> grind)

theorem km4_det_of_mk {X₁ X₂ M : GL (Fin 3) K} {ω : Kˣ} {a b c d : ℤ}
    (hω : X₁ * X₂ * X₁⁻¹ * X₂⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ω)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (h1 : ProjGenLinGroup.mk M * ProjGenLinGroup.mk X₁ * (ProjGenLinGroup.mk M)⁻¹ =
      ProjGenLinGroup.mk X₁ ^ a * ProjGenLinGroup.mk X₂ ^ c)
    (h2 : ProjGenLinGroup.mk M * ProjGenLinGroup.mk X₂ * (ProjGenLinGroup.mk M)⁻¹ =
      ProjGenLinGroup.mk X₁ ^ b * ProjGenLinGroup.mk X₂ ^ d) :
    (a * d - b * c) % 3 = 1 := by
  obtain ⟨u₁, hu₁⟩ : ∃ u : Kˣ, (X₁ ^ a * X₂ ^ c) * Matrix.GeneralLinearGroup.scalar (Fin 3) u =
      M * X₁ * M⁻¹ := by
    refine ProjGenLinGroup.mk_eq_mk_iff.mp ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, map_zpow]
    exact h1.symm
  obtain ⟨u₂, hu₂⟩ : ∃ u : Kˣ, (X₁ ^ b * X₂ ^ d) * Matrix.GeneralLinearGroup.scalar (Fin 3) u =
      M * X₂ * M⁻¹ := by
    refine ProjGenLinGroup.mk_eq_mk_iff.mp ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, map_zpow]
    exact h2.symm
  refine pairing_det_mod_three (x := X₁) (y := X₂)
    (ω := Matrix.GeneralLinearGroup.scalar (Fin 3) ω)
    (l₁ := Matrix.GeneralLinearGroup.scalar (Fin 3) u₁)
    (l₂ := Matrix.GeneralLinearGroup.scalar (Fin 3) u₂) (m := M)
    (km4_scalar_comm ω) ?_ ?_ hω (km4_scalar_comm u₁) (km4_scalar_comm u₂) ?_ ?_
  · rw [← map_pow, hω3, map_one]
  · exact fun h => hω1 (Sec4.scalar_injective_three (h.trans (map_one _).symm))
  · rw [← hu₁]
    exact (km4_scalar_comm u₁ _).symm
  · rw [← hu₂]
    exact (km4_scalar_comm u₂ _).symm

end Frame


theorem pglHess_of_frame {K : Type} [Field K] {p f : ℕ} {π : Bool}
    (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {g : GL (Fin 3) K} (hg : g ∈ Sec4.glPi π 3 (p ^ f) K)
    {y : GL (Fin 3) K} {a b c e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1)
    (hshape : (a = e ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = e ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = e))
    (hy : ProjGenLinGroup.mk y = ProjGenLinGroup.mk (g * Sec4.diagUnits a b c * g⁻¹)) :
    PglHess π p f K y (ProjGenLinGroup.mk (g * Sec4.diagTau hτ * g⁻¹))
      (Subgroup.zpowers (ProjGenLinGroup.mk (g * Sec4.diagTau hτ * g⁻¹)) ⊔
        Subgroup.zpowers (ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹))) := by
  classical
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => by subst h; exact hK.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h3 := hK.three_ne_zero hq
  have hs := Sec4.one_add_tau_add_sq hτ hτ1
  haveI : Finite K := hK.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  set Lh := projImage (Sec4.slPi π 3 (p ^ f) K)
  set mg := ProjGenLinGroup.mk g
  set md := ProjGenLinGroup.mk (Sec4.diagTau hτ) with hmd
  set mc := ProjGenLinGroup.mk (Sec4.cycThree : GL (Fin 3) K) with hmc
  set mF := ProjGenLinGroup.mk (Sec4.fourierGL h3 hs)
  set my := ProjGenLinGroup.mk (Sec4.diagUnits a b c) with hmy
  set x₁ := ProjGenLinGroup.mk (g * Sec4.diagTau hτ * g⁻¹)
  set x₂ := ProjGenLinGroup.mk (g * Sec4.cycThree * g⁻¹)
  set n₁ := ProjGenLinGroup.mk (g * Sec4.fourierGL h3 hs * g⁻¹)
  set F := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂
  have ex₁ : x₁ = mg * md * mg⁻¹ := km4_mk_conj _ _
  have ex₂ : x₂ = mg * mc * mg⁻¹ := km4_mk_conj _ _
  have exn : n₁ = mg * mF * mg⁻¹ := km4_mk_conj _ _
  have R1 : mF * md * mF⁻¹ = mc⁻¹ := Sec4.mk_fourier_diagTau hτ h3 hs
  have R2 : mF * mc * mF⁻¹ = md := Sec4.mk_fourier_cycThree hτ h3 hs
  have R5 : md * mc = mc * md := Sec4.mk_diagTau_cycThree hτ
  have hd3 : md ^ 3 = 1 := by rw [hmd, ← map_pow, Sec4.diagTau_pow_three hτ, map_one]
  have hc3 : mc ^ 3 = 1 := by rw [hmc, ← map_pow, Sec4.cycThree_pow_three, map_one]
  have hx₁L : x₁ ∈ Lh := Subgroup.mem_map.mpr ⟨g * Sec4.diagTau hτ * g⁻¹,
    Sec4.conj_mem_slPi hπ hg (Sec4.diagTau_mem_slPi hπ hq' hτ), rfl⟩
  have hx₂L : x₂ ∈ Lh := Subgroup.mem_map.mpr ⟨g * Sec4.cycThree * g⁻¹,
    Sec4.conj_mem_slPi hπ hg (Sec4.cycThree_mem_slPi hπ), rfl⟩
  have hn₁L : n₁ ∈ Lh := Subgroup.mem_map.mpr ⟨g * Sec4.fourierGL h3 hs * g⁻¹,
    Sec4.conj_mem_slPi hπ hg (Sec4.fourierGL_mem_slPi hK hq hτ h3 hs), rfl⟩
  have h12 : x₁ * x₂ = x₂ * x₁ := by
    rw [ex₁, ex₂]
    calc mg * md * mg⁻¹ * (mg * mc * mg⁻¹) = mg * (md * mc) * mg⁻¹ := by group
      _ = mg * (mc * md) * mg⁻¹ := by rw [R5]
      _ = mg * mc * mg⁻¹ * (mg * md * mg⁻¹) := by group
  have h1 : x₁ ^ 3 = 1 := by rw [ex₁, conj_pow, hd3]; group
  have h2 : x₂ ^ 3 = 1 := by rw [ex₂, conj_pow, hc3]; group
  have hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹ := by
    rw [exn, ex₁, ex₂]
    calc mg * mF * mg⁻¹ * (mg * md * mg⁻¹) * (mg * mF * mg⁻¹)⁻¹ =
        mg * (mF * md * mF⁻¹) * mg⁻¹ := by group
      _ = (mg * mc * mg⁻¹)⁻¹ := by rw [R1]; group
  have hF2 : n₁ * x₂ * n₁⁻¹ = x₁ := by
    rw [exn, ex₁, ex₂]
    calc mg * mF * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * mF * mg⁻¹)⁻¹ =
        mg * (mF * mc * mF⁻¹) * mg⁻¹ := by group
      _ = mg * md * mg⁻¹ := by rw [R2]
  have hx₁ne : x₁ ≠ 1 := km4_mk_conj_diagTau_ne_one hτ hτ1 g
  have hcard : Nat.card F = 9 := km4_card_nine h12 h1 h2 hx₁ne hF1 hF2
  have ew : ProjGenLinGroup.mk y = mg * my * mg⁻¹ := by rw [hy]; exact km4_mk_conj _ _
  have hw1 : ProjGenLinGroup.mk y * x₁ * (ProjGenLinGroup.mk y)⁻¹ = x₁ := by
    have hc : my * md = md * my := by
      rw [hmy, hmd, ← map_mul, ← map_mul, km4_diagUnits_comm hτ]
    rw [ew, ex₁]
    calc mg * my * mg⁻¹ * (mg * md * mg⁻¹) * (mg * my * mg⁻¹)⁻¹ =
        mg * (my * md * my⁻¹) * mg⁻¹ := by group
      _ = mg * md * mg⁻¹ := by rw [hc]; group
  have hw2 : ProjGenLinGroup.mk y * x₂ * (ProjGenLinGroup.mk y)⁻¹ = x₂ * x₁ ∨
      ProjGenLinGroup.mk y * x₂ * (ProjGenLinGroup.mk y)⁻¹ = x₂ * x₁⁻¹ := by
    have hc : my * mc * my⁻¹ = mc *
        ProjGenLinGroup.mk (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹)) := by
      rw [hmy, hmc, ← map_inv, ← map_mul, ← map_mul, km4_conj_cycThree, map_mul]
    have key : ProjGenLinGroup.mk y * x₂ * (ProjGenLinGroup.mk y)⁻¹ = x₂ *
        (mg * ProjGenLinGroup.mk (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹)) * mg⁻¹) := by
      rw [ew, ex₂]
      calc mg * my * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * my * mg⁻¹)⁻¹ =
          mg * (my * mc * my⁻¹) * mg⁻¹ := by group
        _ = mg * (mc * ProjGenLinGroup.mk (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹))) *
            mg⁻¹ := by rw [hc]
        _ = mg * mc * mg⁻¹ * (mg * ProjGenLinGroup.mk
            (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹)) * mg⁻¹) := by group
    rcases km4_mk_shape hτ hτ1 he3 he1 hshape with h | h
    · left
      have h' : ProjGenLinGroup.mk (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹)) = md := h
      rw [key, h', ex₁]
    · right
      have h' : ProjGenLinGroup.mk (Sec4.diagUnits (b * a⁻¹) (c * b⁻¹) (a * c⁻¹)) = md⁻¹ := h
      rw [key, h', ex₁]
      group
  have hx₁F : x₁ ∈ F := Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂F : x₂ ∈ F := Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hω : (g * Sec4.diagTau hτ * g⁻¹) * (g * Sec4.cycThree * g⁻¹) *
      (g * Sec4.diagTau hτ * g⁻¹)⁻¹ * (g * Sec4.cycThree * g⁻¹)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) := by
    calc _ = g * (Sec4.diagTau hτ * Sec4.cycThree * (Sec4.diagTau hτ)⁻¹ * Sec4.cycThree⁻¹) *
          g⁻¹ := by group
      _ = g * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * g⁻¹ := by
        rw [km4_comm_diagTau_cycThree hτ hτ0]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) := by
        rw [← km4_scalar_comm _ g]
        group
  have hω3 : Units.mk0 τ hτ0 ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hτ)
  have hω1 : Units.mk0 τ hτ0 ≠ 1 := fun h => hτ1 (by simpa using congrArg Units.val h)
  have hdet : ∀ m ∈ (Lh ⊔ Subgroup.zpowers (ProjGenLinGroup.mk y)) ⊓
      Subgroup.normalizer (F : Set (ProjGenLinGroup (Fin 3) K)),
      ∃ i j k l : ℤ, (i * l - j * k) % 3 = 1 ∧ m * x₁ * m⁻¹ = x₁ ^ i * x₂ ^ k ∧
        m * x₂ * m⁻¹ = x₁ ^ j * x₂ ^ l := by
    intro m hm
    have hmN : m ∈ Subgroup.normalizer (F : Set (ProjGenLinGroup (Fin 3) K)) := hm.2
    have e1 : m * x₁ * m⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hmN x₁).mp hx₁F
    have e2 : m * x₂ * m⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hmN x₂).mp hx₂F
    obtain ⟨i, k, hik⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 e1
    obtain ⟨j, l, hjl⟩ := Sec4.exists_zpow_mul_of_mem_sup h12 e2
    refine ⟨i, j, k, l, ?_, hik, hjl⟩
    obtain ⟨M, rfl⟩ := ProjGenLinGroup.mk_surjective m
    exact km4_det_of_mk (X₁ := g * Sec4.diagTau hτ * g⁻¹) (X₂ := g * Sec4.cycThree * g⁻¹)
      (M := M) hω hω3 hω1 hik hjl
  have h9 : ∀ x ∈ F, x ≠ 1 → ∃ n ∈ Lh ⊓
      Subgroup.normalizer (F : Set (ProjGenLinGroup (Fin 3) K)), n * x₁ * n⁻¹ = x := by
    have key := Sec4.transitive_of_normal_form (G := ProjGenLinGroup (Fin 3) K) (L := Lh)
      hK hq (MulEquiv.refl _) hτ hτ1 hg hx₁L hx₂L rfl rfl
    intro x hx hx1
    exact key x₁ hx₁F hx₁ne x hx hx1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c10⟩ := hess_abstract (F := F) (Lh := Lh) rfl hx₁L
    hx₂L h12 h1 h2 hcard hn₁L hF1 hF2 hw1 hw2 hdet
  unfold PglHess
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, h9, c10⟩

end CFSG.RankThree.PartTwo.Sec12
