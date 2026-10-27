module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIFrattini

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

variable {X : Type*} [Group X] [Finite X]

structure TIConfigC {X : Type*} [Group X] (H V N : Subgroup X) : Prop where
  V_le : V ≤ H
  V_ne_bot : V ≠ ⊥
  V_le_N : V ≤ N
  ti : ∀ g : X, ∀ x ∈ V, x ≠ 1 → g * x * g⁻¹ ∈ V → g ∈ normalizer (V : Set X)
  N_le : N ≤ NormIn H V
  N_normal : ∀ k ∈ NormIn H V, k ∈ normalizer (N : Set X)
  N_pgroup : IsPGroup 2 N
  cent2 : ∀ k ∈ NormIn H V, IsPGroup 2 (Subgroup.zpowers k) →
    (∀ n ∈ N, k * n = n * k) → k ∈ V

namespace TIConfigC

variable {H V N : Subgroup X}

theorem ne_bot_of_N_le (h : TIConfigC H V N) {S : Subgroup X} (hNS : N ≤ S) : S ≠ ⊥ := by
  intro h0
  apply h.V_ne_bot
  have hVS : V ≤ S := h.V_le_N.trans hNS
  rw [h0] at hVS
  exact le_bot_iff.mp hVS

theorem N_le_of_maximal (h : TIConfigC H V N) {S : Subgroup X} (hSK : S ≤ NormIn H V)
    (hSp : IsPGroup 2 S) (hS : ∀ T : Subgroup X, T ≤ NormIn H V → IsPGroup 2 T → S ≤ T → T = S) :
    N ≤ S := by
  have hNS : IsPGroup 2 (N ⊔ S : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' h.N_pgroup hSp (fun s hs => h.N_normal s (hSK hs))
  have h1 := hS (N ⊔ S) (sup_le h.N_le hSK) hNS le_sup_right
  exact le_sup_left.trans h1.le

theorem cenIn_le_V (h : TIConfigC H V N) {S : Subgroup X} (hSK : S ≤ NormIn H V)
    (hSp : IsPGroup 2 S)
    (hS : ∀ T : Subgroup X, T ≤ NormIn H V → IsPGroup 2 T → S ≤ T → T = S) :
    TIConfig.cenIn S ≤ V := by
  have hNS := h.N_le_of_maximal hSK hSp hS
  intro z hz
  obtain ⟨hzS, hzc⟩ := TIConfig.mem_cenIn.1 hz
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    hSp.to_le (Subgroup.zpowers_le.mpr hzS)
  exact h.cent2 z (hSK hzS) hzp (fun n hn => hzc n (hNS hn))

theorem normalizer_le_normalizer_V (h : TIConfigC H V N) {S : Subgroup X} (hSp : IsPGroup 2 S)
    (hSne : S ≠ ⊥) (hZ : TIConfig.cenIn S ≤ V) :
    normalizer (S : Set X) ≤ normalizer (V : Set X) := by
  intro k hk
  obtain ⟨z, hzc, hz1⟩ := TIConfig.exists_ne_one_mem_cenIn hSp hSne
  have hzV : z ∈ V := hZ hzc
  have hkzV : k * z * k⁻¹ ∈ V := hZ (TIConfig.conj_mem_cenIn hk hzc)
  exact h.ti k z hzV hz1 hkzV

theorem sylow_of_maximal (h : TIConfigC H V N) {S : Subgroup X} (hSK : S ≤ NormIn H V)
    (hSp : IsPGroup 2 S)
    (hS : ∀ T : Subgroup X, T ≤ NormIn H V → IsPGroup 2 T → S ≤ T → T = S) :
    ∀ T : Subgroup X, T ≤ H → IsPGroup 2 T → S ≤ T → T = S := by
  intro T hTH hTp hST
  have hNS : N ≤ S := h.N_le_of_maximal hSK hSp hS
  have hSne : S ≠ ⊥ := h.ne_bot_of_N_le hNS
  have hZV : TIConfig.cenIn S ≤ V := h.cenIn_le_V hSK hSp hS
  by_contra hne
  have hnTS : ¬ T ≤ S := fun hle => hne (le_antisymm hle hST)
  obtain ⟨x, hxT, hxN, hxS⟩ := TIConfig.exists_mem_normalizer_not_mem hTp hST hnTS
  have hxV : x ∈ normalizer (V : Set X) := h.normalizer_le_normalizer_V hSp hSne hZV hxN
  have hxK : x ∈ NormIn H V := mem_NormIn.mpr ⟨hTH hxT, hxV⟩
  have hpT : IsPGroup 2 (T ⊓ NormIn H V : Subgroup X) := hTp.to_inf_left
  have hTK : S ≤ T ⊓ NormIn H V := le_inf hST hSK
  have hEq : T ⊓ NormIn H V = S := hS (T ⊓ NormIn H V) inf_le_right hpT hTK
  have hxS' : x ∈ S := by
    rw [← hEq]
    exact Subgroup.mem_inf.mpr ⟨hxT, hxK⟩
  exact hxS hxS'

theorem frattini_conj (h : TIConfigC H V N) (hHn : ∀ x : X, x ∈ normalizer (H : Set X))
    (g : X) : ∃ k ∈ normalizer (V : Set X), ∃ y ∈ H, g = k * y := by
  obtain ⟨S, hNS, hSK, hSp, hS⟩ := exists_maximal_pgroup h.N_le h.N_pgroup
  have hSH : S ≤ H := fun x hx => (mem_NormIn.mp (hSK hx)).1
  have hmaxH := h.sylow_of_maximal hSK hSp hS
  have hZV : TIConfig.cenIn S ≤ V := h.cenIn_le_V hSK hSp hS
  have hSne : S ≠ ⊥ := h.ne_bot_of_N_le hNS
  obtain ⟨k, _, hkS, y, hy, hgky⟩ :=
    frattini_core (Hn := H) (X' := ⊤) le_top (fun x _ => hHn x) hSH hSp hmaxH g
      (Subgroup.mem_top g)
  exact ⟨k, h.normalizer_le_normalizer_V hSp hSne hZV hkS, y, hy, hgky⟩

end TIConfigC

end CFSG.RankThree.GF2n.Stroth80
