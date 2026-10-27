module

public import CFSG.Quasithin.H13.L32AC38i
public import CFSG.Quasithin.H13.L32AC38f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

theorem sq_mem_of_mem_sup_zpowers {X : Type*} [Group X] {K : Subgroup X} {τ : X}
    (hτ : τ ^ 2 = 1) (hτK : τ ∈ Subgroup.normalizer (K : Set X)) {g : X}
    (hg : g ∈ K ⊔ Subgroup.zpowers τ) : g ^ 2 ∈ K := by
  have hZ : Subgroup.zpowers τ ≤ Subgroup.normalizer (K : Set X) := Subgroup.zpowers_le.mpr hτK
  obtain ⟨k, hk, z, hz, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZ).mp hg
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h2m : τ ^ m * τ ^ m = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ← pow_two, hτ, one_zpow]
  have hconj : τ ^ m * k * (τ ^ m)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hZ (Subgroup.zpow_mem_zpowers τ m)) k).mp hk
  have e : (k * τ ^ m) ^ 2 = k * (τ ^ m * k * (τ ^ m)⁻¹) * (τ ^ m * τ ^ m) := by
    rw [pow_two]
    group
  rw [e, h2m, mul_one]
  exact mul_mem hk hconj

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem Wt_eq_of_two (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {K₀ K₁ : Subgroup (MulAut (IntMod C.Wt C.hUe))}
    (hK₀ : K₀ ≤ ((H1 H b).subgroupOf H).map C.ψ) (hK₁ : K₁ ≤ ((H1 H b).subgroupOf H).map C.ψ)
    (hcomm : ∀ x ∈ K₀, ∀ y ∈ K₁, x * y = y * x) (hdisj : K₀ ⊓ K₁ = ⊥)
    (h3₀ : ∃ e ∈ K₀, e ^ 3 = 1 ∧ e ≠ 1) (h3₁ : ∃ e ∈ K₁, e ^ 3 = 1 ∧ e ≠ 1)
    (hsq : ∀ g ∈ C.ψ.range, g ^ 2 ∈ ((H1 H b).subgroupOf H).map C.ψ) :
    C.Wt = tildeOf (fsuV1 T V) (conjClosure V H) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf C.S.hyp hMod h1222 h1332 h1334
  have hxH := C.l1_le_H hxL
  obtain ⟨e₀, he₀, h30, h10⟩ := h3₀
  obtain ⟨e₁, he₁, h31, h11⟩ := h3₁
  have hx3' : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hψ3 : C.ψ ⟨x, hxH⟩ ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
  have hxK : C.ψ ⟨x, hxH⟩ ∈ ((H1 H b).subgroupOf H).map C.ψ := by
    have h1 := pow_mem (hsq (C.ψ ⟨x, hxH⟩) ⟨⟨x, hxH⟩, rfl⟩) 2
    have e : C.ψ ⟨x, hxH⟩ = (C.ψ ⟨x, hxH⟩ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hψ3, one_mul]
    rw [e]
    exact h1
  have hind : ∀ i j : ZMod 3, e₀ ^ i.val * e₁ ^ j.val = 1 → i = 0 ∧ j = 0 := by
    intro i j h
    have hm : e₀ ^ i.val ∈ K₀ ⊓ K₁ := by
      refine ⟨pow_mem he₀ _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h]
      exact K₁.inv_mem (K₁.pow_mem he₁ _)
    rw [hdisj, Subgroup.mem_bot] at hm
    have hi := eq_zero_of_pow_val h30 h10 hm
    refine ⟨hi, ?_⟩
    rw [hm, one_mul] at h
    exact eq_zero_of_pow_val h31 h11 h
  have hxN := C.mem_H1sup_of_e9 hxH hx3 hxK (hK₀ he₀) (hK₁ he₁) h30 h31 (hcomm _ he₀ _ he₁) hind
  have hxO : x ∉ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
    intro h
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 _) ⟨x, h⟩
    have h1 : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
    have hx1 : x = 1 := by
      have := (pow_gcd_eq_one (a := x)).mpr ⟨h1, hx3⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
    have hle : V ≤ fsuV1 T V := fun v hv => hfpf v hv (by
      rw [hx1, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact one_mem _)
    have := Subgroup.card_le_of_le hle
    rw [hV8, hV12] at this
    omega
  exact C.Wt_eq (C.tildeV_le_Wt h1222 h1332 h1334 hxL hfpf hxL hxO hxN)

end Ctx38

end CFSG.Quasithin.H13.L32A.C
