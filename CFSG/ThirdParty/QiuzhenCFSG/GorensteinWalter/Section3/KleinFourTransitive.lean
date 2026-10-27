module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.KleinFourNormalizerEscape

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Preamble fact (3): normalizers are transitive on the punctured
Klein-four subgroups of the fixed Sylow `2`-subgroup

The Section-2 preamble recalls from Gorenstein--Walter that `N_G(V)` is
transitive on `V^#` for every subgroup `V` of type `(2,2)` of `S`.  This
fact is not exported by the Section-2 modules; the following local assembly
reuses the dihedral-fusion machinery of `GWLemma21Trichotomy` (the same
machinery used by `KleinFourNormalizerEscape`).
-/

/-- The central involution `t` can be conjugated to every nonidentity element
of a Klein-four subgroup `V ≤ S` by an element of `N_G(V)` (one-involution-
class + dihedral fusion). -/
private theorem central_conj_in_normalizer_of_kleinFour
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {V : Subgroup G} (hVle : V ≤ (c.S : Subgroup G)) (hV : IsKleinFour V) :
    ∀ s : G, s ∈ V → s ≠ 1 →
      ∃ n : G, n ∈ Subgroup.normalizer (V : Set G) ∧ n * c.t * n⁻¹ = s := by
  classical
  obtain ⟨e⟩ := c.dihedralEquiv
  by_cases hm : 2 ≤ c.m
  · have htz : c.t = zAmbient c.S e := by
      simpa [zAmbient, dCentral] using
        centralizerSetup_t_eq_zAmbient c hm e
    intro s hsV hs1
    by_cases hst : s = c.t
    · exact ⟨1, (Subgroup.normalizer (V : Set G)).one_mem, by
        rw [hst]
        simp⟩
    · have hconj : IsConj (zAmbient c.S e) s := by
        rw [isConj_iff]
        have hs2 : s * s = 1 := by
          let sV : V := ⟨s, hsV⟩
          exact congrArg Subtype.val (IsKleinFour.mul_self sV)
        obtain ⟨g, hg⟩ := fact_2_preamble_involutions_conjugate_proved
          hmin c.t s c.t_involution ⟨hs1, by simpa [pow_two] using hs2⟩
        exact ⟨g, by simpa [htz] using hg⟩
      obtain ⟨n, hnN, hnz, _hns⟩ :=
        fusion_to_normalizer_moves_central c.S hm e hVle hV hsV hs1
          (by intro h; apply hst; exact h.trans htz.symm) hconj
      obtain ⟨γ, _hγS, hγN, hγfix, hγmove, _hγAll⟩ :=
        exists_dihedral_transposition_of_kleinFour_le_sylow c.S hm e hVle hV
      have hzV : zAmbient c.S e ∈ V := by
        rcases isKleinFour_eq_dKleinAmbient c.S hm e V hVle hV with ⟨i, hVi⟩
        rw [hVi]
        exact dCentralAmbient_mem_dKleinAmbient c.S (by omega : 1 ≤ c.m) e i
      have hγs_ne : γ * s * γ⁻¹ ≠ s :=
        hγmove V hVle hV s hsV hs1
          (by intro h; exact hst (h.trans htz.symm))
      have hγs : γ * s * γ⁻¹ = zAmbient c.S e * s :=
        kleinFour_action_fix_move V hV (x := zAmbient c.S e) (y := s) (δ := γ)
          hzV hsV (zAmbient_ne_one c.S (by omega : 1 ≤ c.m) e) hs1
          (by intro h; exact hst (h.symm.trans htz.symm))
          hγN hγfix hγs_ne
      refine ⟨γ * n, (Subgroup.normalizer (V : Set G)).mul_mem hγN hnN, ?_⟩
      calc
        (γ * n) * c.t * (γ * n)⁻¹ =
            γ * (n * zAmbient c.S e * n⁻¹) * γ⁻¹ := by rw [htz]; group
        _ = γ * (zAmbient c.S e * s) * γ⁻¹ := by rw [hnz]
        _ = (γ * zAmbient c.S e * γ⁻¹) * (γ * s * γ⁻¹) := by group
        _ = zAmbient c.S e * (zAmbient c.S e * s) := by rw [hγfix, hγs]
        _ = s := by
          have hz2 : zAmbient c.S e * zAmbient c.S e = 1 := by
            rw [← htz]
            simpa [pow_two] using c.t_involution.2
          rw [← mul_assoc, hz2]
          simp
  · have hmle : c.m < 2 := Nat.lt_of_not_ge hm
    have hm1 : c.m = 1 :=
      le_antisymm (Nat.le_of_lt_succ hmle) c.one_le_m
    let : IsKleinFour (c.S : Subgroup G) := m1_sylow_isKleinFour c.S hm1 e
    have hSle : (c.S : Subgroup G) ≤ (c.S : Subgroup G) := by rfl
    have hVS : V = (c.S : Subgroup G) := by
      apply le_antisymm hVle
      intro s hsS
      have hVp : IsPGroup 2 V := by
        refine (IsPGroup.iff_card (p := 2) (G := V)).2 ?_
        refine ⟨2, ?_⟩
        exact hV.card_four
      have hSp : IsPGroup 2 (c.S : Subgroup G) := by
        refine (IsPGroup.iff_card (p := 2) (G := (c.S : Subgroup G))).2 ?_
        refine ⟨2, ?_⟩
        exact (inferInstance : IsKleinFour (c.S : Subgroup G)).card_four
      have hVScard : Nat.card V = Nat.card (c.S : Subgroup G) := by
        rw [hV.card_four]
        exact (inferInstance : IsKleinFour (c.S : Subgroup G)).card_four.symm
      have hVtop : V = (c.S : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge (H := V) (K := (c.S : Subgroup G))
          hVle hVScard.symm.le
      rw [hVtop]
      exact hsS
    have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
    have hcardS : Nat.card (c.S : Subgroup G) = 4 :=
      (inferInstance : IsKleinFour (c.S : Subgroup G)).card_four
    have hcardG : 4 ≤ Nat.card G := by
      rw [← hcardS]
      exact Nat.card_le_card_of_injective _ (c.S : Subgroup G).subtype_injective
    have hno2 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
      rintro ⟨N, hNnormal, hNindex⟩
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple N hNnormal with hNbot | hNtop
      · have hNcard : Nat.card G = 2 := by
          simpa [hNbot, Subgroup.index_bot] using hNindex
        omega
      · have hNcard : 1 = 2 := by
          simpa [hNtop, Subgroup.index_top] using hNindex
        omega
    have hCprime : NormalizerContainsCPrime (c.S : Subgroup G) :=
      (case1_no_index_two_fusion_and_normalizer hmin.1 hno2).2
        c.S (c.S : Subgroup G) hSle
          (inferInstance : IsKleinFour (c.S : Subgroup G))
    obtain ⟨n, hnN, hn2C⟩ :=
      (normalizerContainsCPrime_iff_exists (c.S : Subgroup G)).mp hCprime
    let φ : MulAut (c.S : Subgroup G) :=
      (c.S : Subgroup G).normalizerMonoidHom ⟨n, hnN⟩
    have hφ2 : φ ^ 2 ≠ 1 := by
      intro hφ2'
      apply hn2C
      have hφ2eq : φ ^ 2 = (c.S : Subgroup G).normalizerMonoidHom
          (⟨n, hnN⟩ ^ 2) := by
        dsimp [φ]
        exact (map_pow (c.S : Subgroup G).normalizerMonoidHom ⟨n, hnN⟩ 2).symm
      rw [hφ2eq] at hφ2'
      have hker : ⟨n, hnN⟩ ^ 2 ∈
          (c.S : Subgroup G).normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact hφ2'
      rw [Subgroup.normalizerMonoidHom_ker] at hker
      change n ^ 2 ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G)
      rw [Subgroup.mem_subgroupOf] at hker
      exact hker
    have hφ1 : φ ≠ 1 := by
      intro hφ
      apply hφ2
      rw [hφ]
      simp
    intro s hsV hs1
    have hsS : s ∈ (c.S : Subgroup G) := hVle hsV
    let tS : (c.S : Subgroup G) := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
    let sS : (c.S : Subgroup G) := ⟨s, hsS⟩
    have htS1 : tS ≠ 1 := by
      intro h
      exact c.t_involution.1 (congrArg Subtype.val h)
    have hsS1 : sS ≠ 1 := by
      intro h
      exact hs1 (congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := kleinFour_aut_orbit_all φ hφ1 hφ2 tS sS htS1 hsS1
    have hpow := normalizerMonoidHom_pow_apply
      (c.S : Subgroup G) n hnN k tS
    have hconj : n ^ k * c.t * (n ^ k)⁻¹ = s :=
      congrArg Subtype.val (hpow.symm.trans hk)
    refine ⟨n ^ k, ?_, hconj⟩
    rw [hVS]
    exact (Subgroup.normalizer ((c.S : Subgroup G) : Set G)).pow_mem hnN k

/-- Preamble fact (3): `N_G(V)` is transitive on `V^#` for every Klein-four
subgroup `V` of the fixed Sylow `2`-subgroup. -/
public theorem normalizer_transitive_on_kleinFour_pontset
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {V : Subgroup G} (hVle : V ≤ (c.S : Subgroup G)) (hV : IsKleinFour V) :
    ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 →
      ∃ n : G, n ∈ Subgroup.normalizer (V : Set G) ∧ n * x * n⁻¹ = y := by
  classical
  intro x y hxV hyV hx1 hy1
  have hcent := central_conj_in_normalizer_of_kleinFour hmin c hVle hV
  by_cases hxt : x = c.t
  · by_cases hyt : y = c.t
    · exact ⟨1, (Subgroup.normalizer (V : Set G)).one_mem, by
        rw [hxt, hyt]
        simp⟩
    · obtain ⟨n, hnN, hn⟩ := hcent y hyV hy1
      refine ⟨n, hnN, ?_⟩
      rwa [hxt]
  · obtain ⟨n1, hn1N, hn1⟩ := hcent x hxV hx1
    by_cases hyt : y = c.t
    · refine ⟨n1⁻¹, (Subgroup.normalizer (V : Set G)).inv_mem hn1N, ?_⟩
      rw [hyt]
      calc
        n1⁻¹ * x * (n1⁻¹)⁻¹ = n1⁻¹ * x * n1 := by simp
        _ = c.t := by
          calc
            n1⁻¹ * x * n1 = n1⁻¹ * (n1 * c.t * n1⁻¹) * n1 := by rw [← hn1]
            _ = c.t := by group
    · obtain ⟨n2, hn2N, hn2⟩ := hcent y hyV hy1
      refine ⟨n2 * n1⁻¹,
        (Subgroup.normalizer (V : Set G)).mul_mem hn2N
          ((Subgroup.normalizer (V : Set G)).inv_mem hn1N), ?_⟩
      calc
        (n2 * n1⁻¹) * x * (n2 * n1⁻¹)⁻¹ =
            n2 * (n1⁻¹ * x * n1) * n2⁻¹ := by group
        _ = n2 * c.t * n2⁻¹ := by
          have : n1⁻¹ * x * n1 = c.t := by
            calc
              n1⁻¹ * x * n1 = n1⁻¹ * (n1 * c.t * n1⁻¹) * n1 := by rw [← hn1]
              _ = c.t := by group
          rw [this]
        _ = y := hn2

end CFSG.GorensteinWalter
