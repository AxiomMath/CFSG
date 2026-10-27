module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreOdd
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeFibreHbar
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeOddFrame

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}
  {ρ : ↥K →* Equiv.Perm (ZMod p)}

private theorem nine3_inv_mul_mem_of_relIndex_two {L K' : Subgroup G}
    (hrel : L.relIndex K' = 2) {a b : G} (ha : a ∈ K') (hb : b ∈ K') (haL : a ∉ L)
    (hbL : b ∉ L) : a⁻¹ * b ∈ L := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K') hrel
    (a := (⟨a, ha⟩ : K')⁻¹) (b := ⟨b, hb⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haL hbL)
  exact Subgroup.mem_subgroupOf.1 key

theorem nine3_mk_eq_of_mem (hc : Nine3Choice V T A K S X p g x) {U : Subgroup G}
    (hU : U ∈ omegaIn V K (nineE V K)) {u u' : ↥(nineH V K)} (hu : (u : G) ∈ U)
    (hu' : (u' : G) ∈ U) (huR : (u : G) ∉ pCoreOf 2 K) (hu'R : (u' : G) ∉ pCoreOf 2 K) :
    (QuotientGroup.mk u : Nine3Hbar V K) = QuotientGroup.mk u' := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hmem : (u : G)⁻¹ * (u' : G) ∈ U ⊓ pCoreOf 2 K :=
    nine3_inv_mul_mem_of_relIndex_two (nine3_relIndex_of_mem_omegaIn hc hU) hu hu'
      (fun h => huR h.2) (fun h => hu'R h.2)
  exact (le_iSup₂_of_le U hU le_rfl : U ⊓ pCoreOf 2 K ≤ nineI V K) (by simpa using hmem)

theorem nine3_eq_of_mk_eq (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {U U' : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) (hU' : U' ∈ omegaIn V K (nineE V K))
    {u u' : ↥(nineH V K)} (hu : (u : G) ∈ U) (hu' : (u' : G) ∈ U') (huR : (u : G) ∉ pCoreOf 2 K)
    (hu'R : (u' : G) ∉ pCoreOf 2 K)
    (h : (QuotientGroup.mk u : Nine3Hbar V K) = QuotientGroup.mk u') : U = U' := by
  have hmemI : (u : G)⁻¹ * (u' : G) ∈ nineI V K := by
    have hh := QuotientGroup.eq.mp h
    simpa [Subgroup.mem_subgroupOf] using hh
  have hle : U' ≤ U ⊔ nineI V K := by
    intro w hw
    by_cases hwR : w ∈ pCoreOf 2 K
    · exact Subgroup.mem_sup_right
        ((le_iSup₂_of_le U' hU' le_rfl : U' ⊓ pCoreOf 2 K ≤ nineI V K) ⟨hw, hwR⟩)
    · have hwI : (u' : G)⁻¹ * w ∈ nineI V K :=
        (le_iSup₂_of_le U' hU' le_rfl : U' ⊓ pCoreOf 2 K ≤ nineI V K)
          (nine3_inv_mul_mem_of_relIndex_two (nine3_relIndex_of_mem_omegaIn hc hU') hu' hw
            (fun hh => hu'R hh.2) (fun hh => hwR hh.2))
      have hprod : (u : G) * ((u : G)⁻¹ * (u' : G)) * ((u' : G)⁻¹ * w) = w := by group
      rw [← hprod]
      exact (U ⊔ nineI V K).mul_mem
        ((U ⊔ nineI V K).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hmemI))
        (Subgroup.mem_sup_right hwI)
  exact (nine3_eq_of_le_sup_nineI hc hI hU hU' hle).symm

theorem nine3_fib_conj {U : Subgroup G} {c t : ZMod p} (h : Nine3Fib K p ρ U c) {k : ↥K}
    (hk : ∀ i : ZMod p, ρ k i = i + t) : Nine3Fib K p ρ (conjSubgroup U (k : G)) (c - t) := by
  intro w hw hwR
  have hwU : ((k * w * k⁻¹ : ↥K) : G) ∈ U := by
    have h1 : (k : G) * (w : G) * (k : G)⁻¹ ∈ U := mem_conjSubgroup_iff.mp hw
    simpa using h1
  have hw'R : ((k * w * k⁻¹ : ↥K) : G) ∉ pCoreOf 2 K := by
    intro hh
    exact hwR ((Nine3Core.mem_pCoreOf_conj_iff K k.2).mpr (by simpa using hh))
  have hconj : ρ k * ρ w * (ρ k)⁻¹ = zmodRefl p c := by
    have h2 := h (k * w * k⁻¹) hwU hw'R
    rwa [map_mul, map_mul, map_inv] at h2
  have hw_eq : ρ w = (ρ k)⁻¹ * zmodRefl p c * ρ k := by
    rw [← hconj]
    group
  have hk_inv : ∀ j : ZMod p, (ρ k)⁻¹ j = j - t := by
    intro j
    rw [Equiv.Perm.inv_eq_iff_eq, hk, sub_add_cancel]
  rw [hw_eq]
  ext i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hk_inv]
  rw [zmodRefl, zmodRefl, Equiv.subLeft_apply, Equiv.subLeft_apply, hk i]
  ring

theorem nine3_exists_translation (hc : Nine3Choice V T A K S X p g x)
    (hρ : Nine3FibreAct K S p x ρ) (t : ZMod p) :
    ∃ k : ↥K, (k : G) ∈ X ∧ (t ≠ 0 → (k : G) ≠ 1) ∧ ∀ i : ZMod p, ρ k i = i + t := by
  haveI : NeZero p := ⟨hc.core.hyp.base.prime.ne_zero⟩
  have hxK : x ∈ K := hc.core.hyp.base.toTwoPTwo.sylowP.le hc.x_mem
  let x₀ : ↥K := ⟨x, hxK⟩
  have hx₀ : (x₀ : G) = x := rfl
  have hshift : ∀ i : ZMod p, ρ x₀ i = i + 1 := hρ.shift x₀ hx₀
  have hpow : ∀ n : ℕ, ∀ i : ZMod p, (ρ x₀ ^ n) i = i + n := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
        intro i
        rw [pow_succ, Equiv.Perm.mul_apply, hshift i, ih (i + 1), Nat.cast_succ]
        ring
  refine ⟨x₀ ^ t.val, ?_, ?_, ?_⟩
  · simpa [x₀, Subgroup.coe_pow] using X.pow_mem hc.x_mem t.val
  · intro ht hk1
    apply ht
    have hk_eq : x₀ ^ t.val = 1 := Subtype.ext hk1
    have h0 : ρ (x₀ ^ t.val) 0 = 0 + t := by
      rw [map_pow, hpow t.val 0, ZMod.natCast_zmod_val]
    rw [hk_eq, map_one] at h0
    simpa using h0.symm
  · intro i
    rw [map_pow, hpow t.val i, ZMod.natCast_zmod_val]

theorem nine3_exists_fib_over (hc : Nine3Choice V T A K S X p g x)
    (hρ : Nine3FibreAct K S p x ρ) (c : ZMod p) :
    ∃ U ∈ omegaIn V K (nineE V K), Nine3Fib K p ρ U c := by
  have hAΩ : A ∈ omegaIn V K (nineE V K) :=
    ⟨hc.core.A_mem_nineOmegaIn.1, hc.core.nineOmegaIn_le_K hc.core.A_mem_nineOmegaIn⟩
  have hA0 : Nine3Fib K p ρ A 0 :=
    (nine3_fib_zero_iff hc hρ hAΩ).mpr hc.core.A_mem_nineOmegaIn.2
  obtain ⟨k, -, -, hk⟩ := nine3_exists_translation hc hρ (-c)
  exact ⟨conjSubgroup A (k : G), conjSubgroup_mem_omegaIn hAΩ k.2,
    by simpa using nine3_fib_conj hA0 hk⟩

theorem nine3_dbar_over (hc : Nine3Choice V T A K S X p g x) (hρ : Nine3FibreAct K S p x ρ)
    {d : Nine3Hbar V K} (hd : d ∈ Nine3Dbar V K) {c : ZMod p}
    (hdc : nine3Pi V K ρ hρ.le_ker d = zmodRefl p c) :
    ∃ U ∈ omegaIn V K (nineE V K), Nine3Fib K p ρ U c ∧ ∃ u : ↥(nineH V K), (u : G) ∈ U ∧
      (u : G) ∉ pCoreOf 2 K ∧ (QuotientGroup.mk u : Nine3Hbar V K) = d := by
  obtain ⟨U, hU, u, hu, huR, hd_eq⟩ := hd
  obtain ⟨c', hc'⟩ := nine3_exists_fib hc hρ hU
  have h1 : nine3Pi V K ρ hρ.le_ker (QuotientGroup.mk u) = zmodRefl p c' := by
    rw [nine3Pi_mk]
    exact hc' ⟨u, Nine3Choice.nineH_le_K u.2⟩ hu huR
  have hc'_eq : zmodRefl p c' = zmodRefl p c := by
    rw [← hd_eq, h1] at hdc
    exact hdc
  have hcc' : c' = c := zmodRefl_inj hc.core.hyp.base.prime hc.core.hyp.base.odd hc'_eq
  refine ⟨U, hU, ?_, ?_⟩
  · rwa [hcc'] at hc'
  · exact ⟨u, hu, huR, hd_eq⟩

theorem nine3_mk_mem_dbar {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K))
    (hker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → ρ k = 1) {c : ZMod p} (h : Nine3Fib K p ρ U c)
    {u : ↥(nineH V K)} (hu : (u : G) ∈ U) (huR : (u : G) ∉ pCoreOf 2 K) :
    (QuotientGroup.mk u : Nine3Hbar V K) ∈ Nine3Dbar V K ∧
      nine3Pi V K ρ hker (QuotientGroup.mk u) = zmodRefl p c :=
  ⟨⟨U, hU, u, hu, huR, rfl⟩, by
    rw [nine3Pi_mk]
    exact h ⟨u, Nine3Choice.nineH_le_K u.2⟩ hu huR⟩

end CFSG.LocalAnalysis.WeakClosure81
