module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaE1Aux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_alphaE_card_range {M : Type} [CommGroup M] [Finite M]
    (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)] {d : MulAut M}
    (hd2 : d ^ 2 = 1) (hcost : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 2) :
    Nat.card ↥(LinearMap.range (w1369LinHom hw2 d - 1)) = 4 := by
  rw [← w1369_card_submoduleToSubgroup (LinearMap.range (w1369LinHom hw2 d - 1)),
    ← w1369_commSub_eq hw2 hd2, card_eq_two_pow hw2 (commSub ⊤ (Subgroup.zpowers d)),
    hcost]
  norm_num

private theorem w1369_alphaE_card_E_le_four {M : Type} [CommGroup M] [Finite M]
    (hw2 : ∀ m : M, m ^ 2 = 1) [Module (ZMod 2) (Additive M)]
    {K : Subgroup (MulAut M)} (hirr : IsIrrOn K ⊤ ⊥) {d : MulAut M} (hd2 : d ^ 2 = 1)
    (hdN : K.map (MulAut.conj d).toMonoidHom = K)
    (hcost : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 2)
    (hα : ∀ e : w1369E hw2 K, w1369Alpha hw2 hd2 hdN e = e) :
    Nat.card (w1369E hw2 K) ≤ 4 := by
  have hcard := w1369_alphaE_card_range hw2 hd2 hcost
  have hne : LinearMap.range (w1369LinHom hw2 d - 1) ≠ ⊥ := by
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨q, hq, hq0⟩ :=
    (Submodule.ne_bot_iff (LinearMap.range (w1369LinHom hw2 d - 1))).mp hne
  let f : w1369E hw2 K → ↥(LinearMap.range (w1369LinHom hw2 d - 1)) :=
    fun e => ⟨(e : Module.End (ZMod 2) (Additive M)) q,
      w1369_range_sub_mem hw2 (w1369_alpha_eq_self_comm hw2 hd2 hdN (hα e)) hq⟩
  have hf : Function.Injective f := by
    intro e e' h
    have hq_eq : (e : Module.End (ZMod 2) (Additive M)) q =
        (e' : Module.End (ZMod 2) (Additive M)) q := congrArg Subtype.val h
    have hsub : (((e - e' : w1369E hw2 K)) : Module.End (ZMod 2) (Additive M)) q = 0 := by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, hq_eq, sub_self]
    rcases w1369_ker_eq_bot_or_top hw2 hirr (e - e').2 with hker | hker
    · exfalso
      have hmem : q ∈ LinearMap.ker
          (((e - e' : w1369E hw2 K)) : Module.End (ZMod 2) (Additive M)) := by
        rw [LinearMap.mem_ker]; exact hsub
      rw [hker, Submodule.mem_bot] at hmem
      exact hq0 hmem
    · have hzero : (e - e' : w1369E hw2 K) = 0 := by
        apply Subtype.ext
        ext v
        have hmem : v ∈ LinearMap.ker
            (((e - e' : w1369E hw2 K)) : Module.End (ZMod 2) (Additive M)) := by
          rw [hker]; exact Submodule.mem_top
        exact LinearMap.mem_ker.mp hmem
      exact sub_eq_zero.mp hzero
  calc Nat.card (w1369E hw2 K) ≤
        Nat.card ↥(LinearMap.range (w1369LinHom hw2 d - 1)) :=
        Nat.card_le_card_of_injective f hf
    _ = 4 := hcard

private theorem w1369_four_le_card {E : Type} [Finite E] {a b c d : E}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : 4 ≤ Nat.card E := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  have hmem1 : a ∉ ({b, c, d} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac, had⟩
  have hmem2 : b ∉ ({c, d} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbc, hbd⟩
  have hmem3 : c ∉ ({d} : Finset E) := by simpa using hcd
  have hcard : ({a, b, c, d} : Finset E).card = 4 := by
    rw [Finset.card_insert_of_notMem hmem1, Finset.card_insert_of_notMem hmem2,
      Finset.card_insert_of_notMem hmem3, Finset.card_singleton]
  rw [← hcard]
  have hle := Finset.card_le_card (Finset.subset_univ ({a, b, c, d} : Finset E))
  rw [Finset.card_univ] at hle
  rwa [Nat.card_eq_fintype_card]

theorem Std139.alpha_centralizer (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) (hirr : IsIrrOn K ⊤ ⊥) :
    Subgroup.centralizer (K : Set (MulAut W)) = X := by
  classical
  letI : Module (ZMod 2) (Additive W) := addModTwo hw2
  haveI : Nontrivial W := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact absurd (Subsingleton.elim (⊥ : Subgroup W) ⊤) (ne_of_lt hirr.1)
  haveI : Finite (Module.End (ZMod 2) (Additive W)) :=
    Finite.of_injective
      (fun f : Module.End (ZMod 2) (Additive W) => (f : Additive W → Additive W))
      DFunLike.coe_injective
  haveI : Finite (w1369E hw2 K) :=
    Finite.of_injective (fun e : w1369E hw2 K => (e : Module.End (ZMod 2) (Additive W)))
      Subtype.val_injective
  letI : Fintype (w1369E hw2 K) := Fintype.ofFinite _
  have h01 : (0 : w1369E hw2 K) ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ : ∃ m : W, m ≠ 1 := exists_ne 1
    have h' : (0 : Module.End (ZMod 2) (Additive W)) = 1 := Subtype.ext_iff.mp h
    have h2 := congrArg (fun f : Module.End (ZMod 2) (Additive W) =>
      f (Additive.ofMul m)) h'
    rw [LinearMap.zero_apply, Module.End.one_apply] at h2
    exact hm (Additive.ofMul.injective h2.symm)
  have hDgt : 1 < Nat.card D := by
    rw [S.Dcard]
    exact Nat.one_lt_pow (by omega) (by norm_num : 1 < 2)
  letI : Fintype ↥D := Fintype.ofFinite _
  obtain ⟨dD, hdD1⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [← Nat.card_eq_fintype_card]; exact hDgt) (1 : ↥D)
  let d : MulAut W := dD
  have hdD : d ∈ D := dD.2
  have hd1 : d ≠ 1 := fun h => hdD1 (Subtype.ext h)
  have hd2 : d ^ 2 = 1 := S.elem.2 d hdD
  have hdN : K.map (MulAut.conj d).toMonoidHom = K := hK.normal d (S.DG hdD)
  have hcost : rk ↥(commSub ⊤ (Subgroup.zpowers d)) = 2 :=
    (Std139.commSub_axis hw2 S hdD hd1).1
  refine le_antisymm ?_ ?_
  · intro c hc
    have hcomm : ∀ k ∈ K, c * k = k * c :=
      fun k hk => (Subgroup.mem_centralizer_iff.mp hc k hk).symm
    obtain ⟨x, hxgen, hx3, hxne, _, _⟩ := Std139.exists_gen hw2 S
    have hxmem : x ∈ X := by rw [hxgen]; exact Subgroup.mem_zpowers x
    have hxcomm : ∀ k ∈ K, x * k = k * x :=
      fun k hk => (Std139.component_commutes_X S hK.comp k hk x hxmem).symm
    let φ : w1369E hw2 K := ⟨w1369LinHom hw2 x, w1369_linHom_mem_E hw2 hxcomm⟩
    let e : w1369E hw2 K := ⟨w1369LinHom hw2 c, w1369_linHom_mem_E hw2 hcomm⟩
    have hxinvcomm : ∀ k ∈ K, x⁻¹ * k = k * x⁻¹ := by
      intro k hk
      have h := hxcomm k hk
      calc x⁻¹ * k = x⁻¹ * (k * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * k) * x⁻¹ := by rw [← h]
        _ = k * x⁻¹ := by group
    let φ' : w1369E hw2 K := ⟨w1369LinHom hw2 x⁻¹, w1369_linHom_mem_E hw2 hxinvcomm⟩
    have hφmul : φ * φ' = 1 := by
      apply Subtype.ext
      change w1369LinHom hw2 x * w1369LinHom hw2 x⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one]
    have hφ0 : φ ≠ 0 := by
      intro h
      have h1 : (1 : w1369E hw2 K) = 0 := by rw [← hφmul, h, zero_mul]
      exact h01 h1.symm
    have hφ3 : φ ^ 3 = 1 := by
      apply Subtype.ext
      change (w1369LinHom hw2 x) ^ 3 = 1
      rw [← map_pow, hx3, map_one]
    have hφ1 : φ ≠ 1 := by
      intro h
      exact hxne (w1369_linHom_eq_one hw2 (Subtype.ext_iff.mp h))
    have hφsq0 : φ ^ 2 ≠ 0 := by
      intro h
      have hφz : φ = 0 := by
        calc φ = φ * 1 := (mul_one φ).symm
          _ = φ * (φ * φ') := by rw [hφmul]
          _ = (φ * φ) * φ' := by noncomm_ring
          _ = φ ^ 2 * φ' := by rw [pow_two]
          _ = 0 := by rw [h, zero_mul]
      exact hφ0 hφz
    have h1φ2 : (1 : w1369E hw2 K) ≠ φ ^ 2 := by
      intro h
      apply hφ1
      calc φ = φ * 1 := (mul_one φ).symm
        _ = φ * φ ^ 2 := by rw [h]
        _ = φ ^ 3 := by noncomm_ring
        _ = 1 := hφ3
    have hφφ2 : φ ≠ φ ^ 2 := by
      intro h
      have h2 : φ ^ 2 = 1 := by
        calc φ ^ 2 = φ * φ := by rw [pow_two]
          _ = φ * φ ^ 2 := congrArg (fun y => φ * y) h
          _ = φ ^ 3 := by noncomm_ring
          _ = 1 := hφ3
      exact h1φ2 h2.symm
    have h0φ : (0 : w1369E hw2 K) ≠ φ := fun h => hφ0 h.symm
    have h0φ2 : (0 : w1369E hw2 K) ≠ φ ^ 2 := fun h => hφsq0 h.symm
    have h1φ : (1 : w1369E hw2 K) ≠ φ := fun h => hφ1 h.symm
    have hφval : ((φ ^ 2 : w1369E hw2 K) : Module.End (ZMod 2) (Additive W)) =
        w1369LinHom hw2 (x ^ 2) := by
      change (w1369LinHom hw2 x) ^ 2 = w1369LinHom hw2 (x ^ 2)
      rw [map_pow]
    have he0 : e ≠ 0 := by
      have hcinvcomm : ∀ k ∈ K, c⁻¹ * k = k * c⁻¹ := by
        intro k hk
        have h := hcomm k hk
        calc c⁻¹ * k = c⁻¹ * (k * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * k) * c⁻¹ := by rw [← h]
          _ = k * c⁻¹ := by group
      let e' : w1369E hw2 K := ⟨w1369LinHom hw2 c⁻¹, w1369_linHom_mem_E hw2 hcinvcomm⟩
      have hemul : e * e' = 1 := by
        apply Subtype.ext
        change w1369LinHom hw2 c * w1369LinHom hw2 c⁻¹ = 1
        rw [← map_mul, mul_inv_cancel, map_one]
      intro h
      have h1 : (1 : w1369E hw2 K) = 0 := by rw [← hemul, h, zero_mul]
      exact h01 h1.symm
    by_cases hα : ∀ e : w1369E hw2 K, w1369Alpha hw2 hd2 hdN e = e
    · have hcardE : Nat.card (w1369E hw2 K) ≤ 4 :=
        w1369_alphaE_card_E_le_four hw2 hirr hd2 hdN hcost hα
      have hcard4 : 4 ≤ Nat.card (w1369E hw2 K) :=
        w1369_four_le_card h01 h0φ h0φ2 h1φ h1φ2 hφφ2
      have hEcard : Nat.card (w1369E hw2 K) = 4 := le_antisymm hcardE hcard4
      have hcardT : ({0, 1, φ, φ ^ 2} : Finset (w1369E hw2 K)).card = 4 := by
        have hmem1 : (0 : w1369E hw2 K) ∉ ({1, φ, φ ^ 2} : Finset (w1369E hw2 K)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h01, h0φ, h0φ2⟩
        have hmem2 : (1 : w1369E hw2 K) ∉ ({φ, φ ^ 2} : Finset (w1369E hw2 K)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1φ, h1φ2⟩
        have hmem3 : φ ∉ ({φ ^ 2} : Finset (w1369E hw2 K)) := by simpa using hφφ2
        rw [Finset.card_insert_of_notMem hmem1, Finset.card_insert_of_notMem hmem2,
          Finset.card_insert_of_notMem hmem3, Finset.card_singleton]
      have hs : ({0, 1, φ, φ ^ 2} : Finset (w1369E hw2 K)).card =
          Fintype.card (w1369E hw2 K) := by
        rw [hcardT, ← Nat.card_eq_fintype_card, hEcard]
      have hTuniv : ({0, 1, φ, φ ^ 2} : Finset (w1369E hw2 K)) = Finset.univ :=
        Finset.eq_univ_of_card ({0, 1, φ, φ ^ 2} : Finset (w1369E hw2 K)) hs
      have heT : e = 0 ∨ e = 1 ∨ e = φ ∨ e = φ ^ 2 := by
        have hmem : e ∈ ({0, 1, φ, φ ^ 2} : Finset (w1369E hw2 K)) := by
          rw [hTuniv]; exact Finset.mem_univ e
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
      rcases heT with h | h | h | h
      · exact absurd h he0
      · have hc1 : c = 1 := w1369_linHom_eq_one hw2 (Subtype.ext_iff.mp h)
        rw [hxgen, hc1]; exact Subgroup.one_mem _
      · have hcx : c = x := w1369LinHom_injective hw2 (Subtype.ext_iff.mp h)
        rw [hxgen, hcx]; exact Subgroup.mem_zpowers x
      · have hcx2 : c = x ^ 2 := by
          apply w1369LinHom_injective hw2
          have h1 := Subtype.ext_iff.mp h
          rwa [hφval] at h1
        rw [hxgen, hcx2]
        exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) 2
    · exfalso
      rw [not_forall] at hα
      obtain ⟨e₁, he₁⟩ := hα
      have hsq := w1369_card_eq_ker_sq hw2 hirr hd2 hdN ⟨e₁, he₁⟩
      have hrn := w1369_card_eq_ker_mul_range (w1369LinHom hw2 d - 1)
      have hrange := w1369_alphaE_card_range hw2 hd2 hcost
      have hker4 : Nat.card ↥(LinearMap.ker (w1369LinHom hw2 d - 1)) = 4 := by
        have h : Nat.card ↥(LinearMap.ker (w1369LinHom hw2 d - 1)) ^ 2 =
            Nat.card ↥(LinearMap.ker (w1369LinHom hw2 d - 1)) * 4 := by
          rw [← hsq, hrn, hrange]
        rw [pow_two] at h
        exact Nat.mul_left_cancel
          (Nat.card_pos (α := ↥(LinearMap.ker (w1369LinHom hw2 d - 1)))) h
      have hW16 : Nat.card (Additive W) = 16 := by rw [hsq, hker4]; norm_num
      have hW16' : Nat.card W = 16 :=
        (Nat.card_congr (Additive.ofMul : W ≃ Additive W)).trans hW16
      have hn2 : n = 2 := by
        have h : 4 ^ n = 4 ^ 2 := by rw [← S.card, hW16']; norm_num
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h
      omega
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Std139.component_commutes_X S hK.comp k hk x hx

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
