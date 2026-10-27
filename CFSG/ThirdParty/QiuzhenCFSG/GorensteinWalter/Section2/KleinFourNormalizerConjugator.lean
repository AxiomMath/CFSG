module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.KleinFourNormalizerEscape
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerSetupCentralInvolution
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Aligning an escaping Klein-four normalizer element

An element outside an overgroup that normalizes a fixed Klein four can be
adjusted inside that normalizer to send the distinguished involution to any
prescribed nontrivial, distinct element of the Klein four.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem kleinFour_mulAut_sq_apply_eq_mul
    {K : Type u} [Group K] [IsKleinFour K]
    (φ : MulAut K) (hφ2 : φ ^ 2 ≠ 1)
    (x : K) (hx1 : x ≠ 1) :
    φ (φ x) = x * φ x := by
  have hfix_none : ∀ y : K, y ≠ 1 → φ y ≠ y := by
    intro y hy hfix
    exact hφ2 (mulAut_sq_eq_one_of_fixed_ne_one φ hy hfix)
  have hφx1 : φ x ≠ 1 := by
    intro h
    apply hx1
    exact φ.injective (by simpa using h)
  have hφx_ne_x : φ x ≠ x := hfix_none x hx1
  have hφ2x1 : φ (φ x) ≠ 1 := by
    intro h
    apply hφx1
    exact φ.injective (by simpa using h)
  have hφ2x_ne_φx : φ (φ x) ≠ φ x := hfix_none (φ x) hφx1
  have hφ2x_ne_x : φ (φ x) ≠ x := by
    intro h
    let z : K := x * φ x
    have hz1 : z ≠ 1 := by
      intro hz
      have hφx_eq : φ x = x := by
        calc
          φ x = ((φ x)⁻¹)⁻¹ := by simp
          _ = x⁻¹ := by rw [← mul_eq_one_iff_eq_inv.mp hz]
          _ = x := IsKleinFour.inv_eq_self x
      exact hfix_none x hx1 hφx_eq
    have hφz : φ z = z := by
      calc
        φ z = φ (x * φ x) := rfl
        _ = φ x * φ (φ x) := map_mul φ x (φ x)
        _ = φ x * x := by rw [h]
        _ = x * φ x :=
          (IsKleinFour.isMulCommutative (G := K)).is_comm.comm (φ x) x
        _ = z := rfl
    exact hfix_none z hz1 hφz
  exact IsKleinFour.eq_mul_of_ne_all
    (x := x) (y := φ x) (z := φ (φ x))
    hx1 hφx1 hφx_ne_x.symm hφ2x1 hφ2x_ne_x hφ2x_ne_φx

private theorem kleinFour_mulAut_cube_eq_one
    {K : Type u} [Group K] [IsKleinFour K]
    (φ : MulAut K) (hφ2 : φ ^ 2 ≠ 1) :
    φ ^ 3 = 1 := by
  ext x
  by_cases hx1 : x = 1
  · subst x
    simp
  have hsq := kleinFour_mulAut_sq_apply_eq_mul φ hφ2 x hx1
  have hcomm :=
    (IsKleinFour.isMulCommutative (G := K)).is_comm.comm (φ x) x
  change φ (φ (φ x)) = x
  calc
    φ (φ (φ x)) = φ (x * φ x) := by rw [hsq]
    _ = φ x * φ (φ x) := map_mul φ x (φ x)
    _ = φ x * (x * φ x) := by rw [hsq]
    _ = x * (φ x * φ x) := by rw [← mul_assoc, hcomm, mul_assoc]
    _ = x := by rw [IsKleinFour.mul_self, mul_one]

/-- Align an escaping element of `N_G(V)` so that it conjugates the
distinguished involution to a prescribed other nonidentity element of `V`.
-/
public theorem exists_outside_normalizer_conjugating_t_to
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (A V : Subgroup G)
    (hHA : c.H ≤ A) (hVS : V ≤ (c.S : Subgroup G))
    (hV : IsKleinFour V)
    (hescape : ¬ Subgroup.normalizer (V : Set G) ≤ A)
    {s : G} (hsV : s ∈ V) (hs1 : s ≠ 1) (hst : s ≠ c.t)
    (htV : c.t ∈ V) :
    ∃ g : G, g ∈ Subgroup.normalizer (V : Set G) ∧ g ∉ A ∧
      g * c.t * g⁻¹ = s := by
  classical
  obtain ⟨g0, hg0N, hg0A⟩ := SetLike.not_le_iff_exists.mp hescape
  let s0 : G := g0 * c.t * g0⁻¹
  have hs0V : s0 ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hg0N c.t).1 htV
  have hs01 : s0 ≠ 1 := by
    intro h
    apply c.t_involution.1
    calc
      c.t = g0⁻¹ * s0 * g0 := by dsimp [s0]; group
      _ = 1 := by rw [h]; simp
  have hs0t : s0 ≠ c.t := by
    intro h
    change g0 * c.t * g0⁻¹ = c.t at h
    apply hg0A
    apply hHA
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc
      g0 * c.t = (g0 * c.t * g0⁻¹) * g0 := by group
      _ = c.t * g0 := by rw [h]
  obtain ⟨e⟩ := c.dihedralEquiv
  by_cases hm : 2 ≤ c.m
  · by_cases hs0s : s0 = s
    · exact ⟨g0, hg0N, hg0A, hs0s⟩
    · have htz : c.t = zAmbient c.S e := by
        simpa [zAmbient, dCentral] using
          centralizerSetup_t_eq_dihedralCentralRotation c hm e
      obtain ⟨δ, hδS, hδN, hδfix, hδmove, _hδall⟩ :=
        exists_dihedral_transposition_of_kleinFour_le_sylow
          c.S hm e hVS hV
      have hδs0ne : δ * s0 * δ⁻¹ ≠ s0 :=
        hδmove V hVS hV s0 hs0V hs01 (by simpa [htz] using hs0t)
      have hδs0 : δ * s0 * δ⁻¹ = c.t * s0 := by
        apply kleinFour_action_fix_move V hV htV hs0V
          c.t_involution.1 hs01 hs0t.symm hδN
        · simpa [htz] using hδfix
        · exact hδs0ne
      let tV : V := ⟨c.t, htV⟩
      let s0V : V := ⟨s0, hs0V⟩
      let sV : V := ⟨s, hsV⟩
      have hsEq : s = c.t * s0 := by
        exact congrArg Subtype.val
          (IsKleinFour.eq_mul_of_ne_all
            (x := tV) (y := s0V) (z := sV)
            (by simpa [tV] using c.t_involution.1)
            (by simpa [s0V] using hs01)
            (by intro h; exact hs0t (congrArg Subtype.val h).symm)
            (by simpa [sV] using hs1)
            (by intro h; exact hst (congrArg Subtype.val h))
            (by intro h; exact hs0s (congrArg Subtype.val h).symm))
      have hδA : δ ∈ A := hHA (centralizerSetup_S_le_H c hδS)
      have hprodN : δ * g0 ∈ Subgroup.normalizer (V : Set G) :=
        (Subgroup.normalizer (V : Set G)).mul_mem hδN hg0N
      have hprodA : δ * g0 ∉ A := by
        intro h
        apply hg0A
        have := A.mul_mem (A.inv_mem hδA) h
        simpa using this
      refine ⟨δ * g0, hprodN, hprodA, ?_⟩
      calc
        (δ * g0) * c.t * (δ * g0)⁻¹ = δ * s0 * δ⁻¹ := by dsimp [s0]; group
        _ = c.t * s0 := hδs0
        _ = s := hsEq.symm
  · have hm1 : c.m = 1 := by
      have hmpos := c.one_le_m
      omega
    have hSK4 : IsKleinFour (c.S : Subgroup G) :=
      m1_sylow_isKleinFour c.S hm1 e
    have hVeq : V = (c.S : Subgroup G) := by
      apply le_antisymm hVS
      intro x hxS
      by_contra hxV
      have hne : (V : Set G) ≠ ((c.S : Subgroup G) : Set G) := by
        intro heq
        apply hxV
        change x ∈ (V : Set G)
        rw [heq]
        exact hxS
      have hlt : (V : Set G) ⊂ ((c.S : Subgroup G) : Set G) :=
        Set.ssubset_iff_subset_ne.mpr ⟨hVS, hne⟩
      have hcardlt := Set.Finite.card_lt_card
        (Set.toFinite ((c.S : Subgroup G) : Set G)) hlt
      have hcardlt' : Nat.card V < Nat.card (c.S : Subgroup G) := by
        simp at hcardlt
      rw [hV.card_four, hSK4.card_four] at hcardlt'
      omega
    subst V
    let S : Subgroup G := (c.S : Subgroup G)
    let : IsKleinFour S := by simpa [S] using hSK4
    have hcardS : Nat.card S = 4 := (inferInstance : IsKleinFour S).card_four
    have hcardG : 4 ≤ Nat.card G := by
      rw [← hcardS]
      exact Nat.card_le_card_of_injective _ S.subtype_injective
    have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
    have hno2 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
      rintro ⟨N, hNnormal, hNindex⟩
      rcases (haveI := hNnormal; hsimple.eq_bot_or_eq_top_of_normal N) with hNbot | hNtop
      · rw [hNbot, Subgroup.index_bot] at hNindex
        omega
      · rw [hNtop, Subgroup.index_top] at hNindex
        omega
    have hCprime : NormalizerContainsCPrime S :=
      (case1_no_index_two_fusion_and_normalizer hmin.1 hno2).2
        c.S S (by rfl) (inferInstance : IsKleinFour S)
    obtain ⟨n, hnN, hn2C⟩ :=
      (normalizerContainsCPrime_iff_exists S).mp hCprime
    let φ : MulAut S := S.normalizerMonoidHom ⟨n, hnN⟩
    have hφ2 : φ ^ 2 ≠ 1 := by
      intro hφ2'
      apply hn2C
      have hφ2eq : φ ^ 2 = S.normalizerMonoidHom (⟨n, hnN⟩ ^ 2) := by
        dsimp [φ]
        exact (map_pow S.normalizerMonoidHom ⟨n, hnN⟩ 2).symm
      rw [hφ2eq] at hφ2'
      have hker : ⟨n, hnN⟩ ^ 2 ∈ S.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact hφ2'
      rw [Subgroup.normalizerMonoidHom_ker] at hker
      change n ^ 2 ∈ Subgroup.centralizer (S : Set G)
      rw [Subgroup.mem_subgroupOf] at hker
      exact hker
    have hφ1 : φ ≠ 1 := by
      intro hφ
      apply hφ2
      rw [hφ]
      simp
    by_cases hnA : n ∈ A
    · let s0S : S := ⟨s0, hs0V⟩
      let sS : S := ⟨s, hsV⟩
      obtain ⟨k, hk⟩ := kleinFour_aut_orbit_all φ hφ1 hφ2
        s0S sS (by simpa [s0S] using hs01) (by simpa [sS] using hs1)
      have hpow := normalizerMonoidHom_pow_apply S n hnN k s0S
      have hconj : n ^ k * s0 * (n ^ k)⁻¹ = s :=
        congrArg Subtype.val (hpow.symm.trans hk)
      have hnkN : n ^ k ∈ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normalizer (S : Set G)).pow_mem hnN k
      have hnkA : n ^ k ∈ A := A.pow_mem hnA k
      have hprodN : n ^ k * g0 ∈ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normalizer (S : Set G)).mul_mem hnkN hg0N
      have hprodA : n ^ k * g0 ∉ A := by
        intro h
        apply hg0A
        have := A.mul_mem (A.inv_mem hnkA) h
        simpa using this
      refine ⟨n ^ k * g0, hprodN, hprodA, ?_⟩
      calc
        (n ^ k * g0) * c.t * (n ^ k * g0)⁻¹ =
            n ^ k * s0 * (n ^ k)⁻¹ := by dsimp [s0]; group
        _ = s := hconj
    · let tS : S := ⟨c.t, htV⟩
      let sS : S := ⟨s, hsV⟩
      have hφt1 : φ tS ≠ 1 := by simpa [tS] using c.t_involution.1
      have hφt_ne : φ tS ≠ tS := by
        intro hfix
        exact hφ2 (mulAut_sq_eq_one_of_fixed_ne_one φ
          (by simpa [tS] using c.t_involution.1) hfix)
      by_cases hφts : φ tS = sS
      · refine ⟨n, hnN, hnA, ?_⟩
        have happly := normalizerMonoidHom_pow_apply S n hnN 1 tS
        have hEq := happly.symm.trans (by simpa [φ] using hφts)
        simpa using congrArg Subtype.val hEq
      · have hφ2ts : φ (φ tS) = sS := by
          have hsq := kleinFour_mulAut_sq_apply_eq_mul φ hφ2 tS
            (by simpa [tS] using c.t_involution.1)
          have hsEq : sS = tS * φ tS :=
            IsKleinFour.eq_mul_of_ne_all
              (x := tS) (y := φ tS) (z := sS)
              (by simpa [tS] using c.t_involution.1)
              hφt1 hφt_ne.symm
              (by simpa [sS] using hs1)
              (by intro h; exact hst (congrArg Subtype.val h))
              (by intro h; exact hφts h.symm)
          exact hsq.trans hsEq.symm
        have hn2N : n ^ 2 ∈ Subgroup.normalizer (S : Set G) :=
          (Subgroup.normalizer (S : Set G)).pow_mem hnN 2
        have hn2A : n ^ 2 ∉ A := by
          intro hn2A
          have hφ3 : φ ^ 3 = 1 :=
            kleinFour_mulAut_cube_eq_one φ hφ2
          have hn3C : n ^ 3 ∈ Subgroup.centralizer (S : Set G) := by
            have hmap : S.normalizerMonoidHom (⟨n, hnN⟩ ^ 3) = 1 := by
              rw [map_pow]
              exact hφ3
            have hker : ⟨n, hnN⟩ ^ 3 ∈ S.normalizerMonoidHom.ker := by
              rw [MonoidHom.mem_ker]
              exact hmap
            rw [Subgroup.normalizerMonoidHom_ker] at hker
            change n ^ 3 ∈ Subgroup.centralizer (S : Set G)
            rw [Subgroup.mem_subgroupOf] at hker
            exact hker
          have hn3A : n ^ 3 ∈ A := by
            apply hHA
            rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
            have hn3comm := Subgroup.mem_centralizer_iff.mp hn3C c.t htV
            exact hn3comm.symm
          apply hnA
          have := A.mul_mem hn3A (A.inv_mem hn2A)
          simpa [pow_succ] using this
        refine ⟨n ^ 2, hn2N, hn2A, ?_⟩
        have happly := normalizerMonoidHom_pow_apply S n hnN 2 tS
        have hφpow : (φ ^ 2) tS = sS := by
          simpa [pow_two] using hφ2ts
        have hEq := happly.symm.trans hφpow
        exact congrArg Subtype.val hEq

end CFSG.GorensteinWalter
