module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem eq_bot_of_commutator_self_eq_of_isSolvable {Q : Type*} [Group Q] [Group.IsSolvable Q]
    {T : Subgroup Q} (hT : ⁅T, T⁆ = T) : T = ⊥ := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def Q).mp ‹_›
  have h : ∀ m, T ≤ derivedSeries Q m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
      calc T = ⁅T, T⁆ := hT.symm
        _ ≤ derivedSeries Q (m + 1) := by
          rw [derivedSeries_succ]
          exact commutator_mono ih ih
  exact eq_bot_iff.mpr (hn ▸ h n)

theorem perfect_le_of_le_mul_pGroup [Finite G] {p : ℕ} (hp : p.Prime) {X R K S : Subgroup G}
    (hR : IsPGroup p R) (hXK : X ≤ K) (hKN : K ≤ normalizer (X : Set G))
    (hKXR : ∀ k ∈ K, ∃ x ∈ X, ∃ r ∈ R, x * r = k) (hSK : S ≤ K) (hS : ⁅S, S⁆ = S) :
    S ≤ X := by
  have := Fact.mk hp
  have : (X.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hXK).mpr hKN
  set π := QuotientGroup.mk' (X.subgroupOf K) with hπ
  have hQ : IsPGroup p (K ⧸ X.subgroupOf K) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (X.subgroupOf K) q
    obtain ⟨x, hx, r, hr, hk⟩ := hKXR k k.2
    have hrK : r ∈ K := by
      have : r = x⁻¹ * k := by rw [← hk]; group
      rw [this]
      exact K.mul_mem (K.inv_mem (hXK hx)) k.2
    obtain ⟨m, hm⟩ := hR ⟨r, hr⟩
    refine ⟨m, ?_⟩
    have hk' : k = ⟨x, hXK hx⟩ * ⟨r, hrK⟩ := Subtype.ext hk.symm
    have hx1 : π ⟨x, hXK hx⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    have hr1 : (⟨r, hrK⟩ : K) ^ p ^ m = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hm
    rw [hk', map_mul, hx1, one_mul, ← map_pow, hr1, map_one]
  have := hQ.isNilpotent
  have hinj := K.subtype_injective
  have hmS := map_subgroupOf_eq_of_le hSK
  have hS' : ⁅S.subgroupOf K, S.subgroupOf K⁆ = S.subgroupOf K := by
    apply map_injective hinj
    rw [map_commutator, hmS, hS]
  have hbot : (S.subgroupOf K).map π = ⊥ :=
    eq_bot_of_commutator_self_eq_of_isSolvable (by rw [← map_commutator, hS'])
  have hle : S.subgroupOf K ≤ X.subgroupOf K := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
    exact hbot
  intro s hs
  exact hle (show (⟨s, hSK hs⟩ : K) ∈ S.subgroupOf K from hs)

theorem le_normalizer_of_perfect_conj_le {X K L : Subgroup G} (hXp : ⁅X, X⁆ = X)
    (hL : ∀ S : Subgroup G, S ≤ L → ⁅S, S⁆ = S → S ≤ X)
    (hKL : ∀ z ∈ K, ∀ x ∈ X, z * x * z⁻¹ ∈ L) : K ≤ normalizer (X : Set G) := by
  have hconj : ∀ z ∈ K, ∀ x ∈ X, z * x * z⁻¹ ∈ X := by
    intro z hz x hx
    have hle : X.map (MulAut.conj z).toMonoidHom ≤ L := by
      rintro _ ⟨w, hw, rfl⟩
      exact hKL z hz w hw
    exact hL _ hle (by rw [← map_commutator, hXp]) ⟨x, hx, rfl⟩
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hconj y hy x, fun h => ?_⟩
  have := hconj y⁻¹ (K.inv_mem hy) _ h
  simpa [mul_assoc] using this

theorem perfect_subnormal_p_signalizer_action [Finite G] {p : ℕ} (hp : p.Prime)
    {X R : Subgroup G} (hXp : ⁅X, X⁆ = X) (hXs : X.IsSubnormal) (hR : IsPGroup p R)
    (hXR : X ≤ normalizer (R : Set G)) :
    R ≤ normalizer (X : Set G) ∧ ⁅X, R⁆ ≤ CFSG.inSubgroup (CFSG.pCore p) X := by
  obtain ⟨n, f, hfm, hfn, hf0, hftop⟩ := hXs.exists_chain
  set H := X ⊔ R with hH
  have hXH : X ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  have hmul : ((H : Subgroup G) : Set G) = (X : Set G) * (R : Set G) :=
    coe_mul_of_left_le_normalizer_right X R hXR
  have hXf : ∀ i, X ≤ f i := fun i => hf0 ▸ hfm (Nat.zero_le i)
  have key : ∀ i, ∀ S : Subgroup G, S ≤ f i ⊓ H → ⁅S, S⁆ = S → S ≤ X := by
    intro i
    induction i with
    | zero =>
      intro S hS _
      rw [hf0] at hS
      exact hS.trans inf_le_left
    | succ i ih =>
      intro S hS hSp
      have hKN : f (i + 1) ⊓ H ≤ normalizer (X : Set G) := by
        refine le_normalizer_of_perfect_conj_le hXp ih fun z hz x hx => ⟨?_, ?_⟩
        · exact (hfn i).conj_mem ⟨x, hfm (Nat.le_succ i) (hXf i hx)⟩ (hXf i hx) ⟨z, hz.1⟩
        · exact H.mul_mem (H.mul_mem hz.2 (hXH hx)) (H.inv_mem hz.2)
      refine perfect_le_of_le_mul_pGroup hp hR (le_inf (hXf (i + 1)) hXH) hKN
        (fun k hk => ?_) hS hSp
      have hkH : k ∈ (H : Set G) := hk.2
      rw [hmul] at hkH
      exact hkH
  have hRN : R ≤ normalizer (X : Set G) := by
    refine le_normalizer_of_perfect_conj_le hXp (L := H) (fun S hS hSp => ?_)
      fun z hz x hx => H.mul_mem (H.mul_mem (hRH hz) (hXH hx)) (H.inv_mem (hRH hz))
    refine key n S ?_ hSp
    rw [hftop, top_inf_eq]
    exact hS
  refine ⟨hRN, ?_⟩
  have hCX : ⁅X, R⁆ ≤ X := le_normalizer_iff_commutator_le_left.mp hRN
  have hCR : ⁅X, R⁆ ≤ R := le_normalizer_iff_commutator_le_right.mp hXR
  have hnorm : (⁅X, R⁆.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCX).mpr (normalizer_commutator_ge_left X R)
  have hpC : IsPGroup p (⁅X, R⁆.subgroupOf X) :=
    (hR.to_le hCR).of_equiv (subgroupOfEquivOfLe hCX).symm
  have hle : ⁅X, R⁆.subgroupOf X ≤ CFSG.pCore p X := le_sSup ⟨hnorm, hpC⟩
  calc ⁅X, R⁆ = (⁅X, R⁆.subgroupOf X).map X.subtype := (map_subgroupOf_eq_of_le hCX).symm
    _ ≤ (CFSG.pCore p X).map X.subtype := map_mono hle

end CFSG.Quasithin.SteinbergBM
