module

public import CFSG.Quasithin.H13.A6S1372L74s
public import CFSG.Quasithin.H13.A6S1372L74c

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace A6L74

variable {G : Type} [Group G]

theorem le_centralizer_of_quadratic {U K : Subgroup G} (hU : IsElemAbelian 2 U)
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hK2 : oTwoRes K = K)
    (hq : ∀ u ∈ U, ∀ k ∈ K, k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (K : Set G)) :
    K ≤ Subgroup.centralizer (U : Set G) := by
  rw [← hK2]
  refine (Subgroup.closure_le _).2 ?_
  rintro k ⟨hk, m, hm, hkm⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro u hu
  have hW : ∀ w ∈ U ⊓ Subgroup.centralizer (K : Set G), k * w * k⁻¹ = w := fun w hw => by
    rw [Subgroup.mem_centralizer_iff.mp hw.2 k hk, mul_inv_cancel_right]
  have hkW : ∀ a ∈ U, k * a * k⁻¹ * a⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G) := fun a ha =>
    ⟨U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKU hk) a).mp ha) (U.inv_mem ha), hq a ha k hk⟩
  have h1 := conj_eq_of_odd hU inf_le_left hW hkW hm hkm hu
  calc u * k = k * u * k⁻¹ * k := by rw [h1]
    _ = k * u := by group

theorem eq_pCoreOf_or_eq_of_simple {K N : Subgroup G}
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hON : pCoreOf 2 K ≤ N) :
    N = pCoreOf 2 K ∨ N = K := by
  have hn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hn' : ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hn.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with h | h
  · left
    refine le_antisymm (fun x hx => ?_) hON
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hNK hx⟩ ∈
        (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
      ⟨⟨x, hNK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (mem_pCoreOf_iff _).2 h1
  · right
    refine le_antisymm hNK fun k hk => ?_
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ ∈
        (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnk⟩ := h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
    have h2 : ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := (mem_pCoreOf_iff _).2 hnk
    have e : k = (n : G) * ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
    rw [e]
    exact N.mul_mem (Subgroup.mem_subgroupOf.mp hn) (hON h2)

theorem exists_minimal_centralizer [Finite G] {K X X' W : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hXX' : X ≤ X')
    (hX'X : X' ≤ Subgroup.normalizer (X : Set G)) (hX'W : X' ≤ Subgroup.normalizer (W : Set G))
    (hWe : IsElemAbelian 2 W) (hW : K ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 K) :
    ∃ U : Subgroup G, U ≤ W ∧ X' ≤ Subgroup.normalizer (U : Set G) ∧
      K ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 K ∧
      pCoreOf 2 X ≤ Subgroup.centralizer (U : Set G) ∧
      ∀ U' : Subgroup G, U' ≤ U → X' ≤ Subgroup.normalizer (U' : Set G) →
        K ⊓ Subgroup.centralizer (U' : Set G) = pCoreOf 2 K → U' = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, -, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun U' : Subgroup G => U' ≤ W ∧ X' ≤ Subgroup.normalizer (U' : Set G) ∧
      K ⊓ Subgroup.centralizer (U' : Set G) = pCoreOf 2 K) W ⟨le_rfl, hX'W, hW⟩
  obtain ⟨⟨hUW, hX'U, hCU⟩, hmin'⟩ := hmin
  have hmin'' : ∀ U' : Subgroup G, U' ≤ U → X' ≤ Subgroup.normalizer (U' : Set G) →
      K ⊓ Subgroup.centralizer (U' : Set G) = pCoreOf 2 K → U' = U := fun U' hU'U hX'U' hC' =>
    le_antisymm hU'U (hmin' ⟨hU'U.trans hUW, hX'U', hC'⟩ hU'U)
  refine ⟨U, hUW, hX'U, hCU, ?_, hmin''⟩
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := hXX'.trans hX'U
  have hUe : IsElemAbelian 2 U := A1b.isElemAbelian_of_le hUW hWe
  have hX'O : X' ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hX'X.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hD : ∀ d ∈ pCoreOf 2 X, ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (U : Set G) := by
    intro d hd
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact Subgroup.one_mem _
  have hkey := A1b.centralizer_inf_centralizer_eq hKX hXK hXU hUe hCU
    (pCoreOf_le 2 X) (le_normalizer_pCoreOf 2 X) hD
  have hX'C : X' ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf_of (hX'U hg) (InternalSec.le_normalizer_centralizer hX'O hg)
  have hle := hmin'' _ inf_le_left hX'C hkey
  have h2 : U ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) :=
    calc U = U ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) := hle.symm
      _ ≤ _ := inf_le_right
  exact Subgroup.le_centralizer_iff.mp h2

theorem tr3_of_fixed {c u : G} (hcu : c * u * c⁻¹ = u) (hu2 : u * u = 1) : tr3 c u = u := by
  unfold tr3
  have e : c * c * u * c⁻¹ * c⁻¹ = c * (c * u * c⁻¹) * c⁻¹ := by group
  rw [e, hcu, hcu, hu2, one_mul]

section Coprime

variable {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {c : G}
  (hc : c ∈ Subgroup.normalizer (A : Set G))

include hA hc in
theorem tr3_mul_tr3 (h3 : ∀ x ∈ A, c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = x)
    (hsq : ∀ x ∈ A, x * x = 1) {u : G} (hu : u ∈ A) : tr3 c (u * tr3 c u) = 1 := by
  rw [tr3_mul hA hc hu (tr3_mem hc hu),
    tr3_of_fixed (conj_tr3 hA hc h3 hu) (hsq _ (tr3_mem hc hu)), hsq _ (tr3_mem hc hu)]

end Coprime

end A6L74

end CFSG.Quasithin.H13.A6
