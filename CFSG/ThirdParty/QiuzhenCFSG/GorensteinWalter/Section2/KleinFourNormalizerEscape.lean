module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerSetupCentralInvolution
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution

namespace CFSG
end CFSG
open CFSG

/-!
# A Klein-four normalizer escaping an involution-centralizer overgroup

This is the source consequence of Gorenstein--Walter Lemma 2.1 used in the
minimal invariant odd-prime subgroup argument of Theorem 2.6.  If every
Klein four in the fixed Sylow subgroup had normalizer in an overgroup `A` of
`C_G(t)`, the dihedral fusion machinery would make all involutions of `A`
conjugate in `A`.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private lemma centralizerSetup_t_eq_zAmbient
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hm : 2 ≤ c.m)
    (e : c.S ≃* DihedralGroup (2 ^ c.m)) :
    c.t = zAmbient c.S e := by
  simpa [zAmbient, dCentral] using
    centralizerSetup_t_eq_dihedralCentralRotation c hm e

private lemma conjugate_involution_into_fixed_sylow_of_mem
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (A : Subgroup G) (hSA : (S : Subgroup G) ≤ A)
    {x : G} (hxA : x ∈ A) (hx : IsInvolution x) :
    ∃ a : G, a ∈ A ∧ a * x * a⁻¹ ∈ (S : Subgroup G) := by
  classical
  let xA : A := ⟨x, hxA⟩
  have hxAinv : IsInvolution xA := by
    constructor
    · intro h
      exact hx.1 (congrArg Subtype.val h)
    · exact Subtype.ext hx.2
  let X : Subgroup A := Subgroup.zpowers xA
  have hxord : orderOf xA = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hxAinv.2) hxAinv.1
  have hXp : IsPGroup 2 X := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hxord]
    norm_num
  obtain ⟨Q, hXQ⟩ := IsPGroup.exists_le_sylow hXp
  have hxQ : xA ∈ (Q : Subgroup A) := hXQ (Subgroup.mem_zpowers xA)
  let SA : Sylow 2 A := S.subtype hSA
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A Q SA
  have hxSA : a * xA * a⁻¹ ∈ (SA : Subgroup A) := by
    have hsmul : (MulAut.conj a) xA ∈ (MulAut.conj a) • (Q : Set A) :=
      Set.smul_mem_smul_set hxQ
    have hSAset : (MulAut.conj a) • (Q : Set A) = (SA : Set A) := by
      rw [← Sylow.coe_smul, ha]
    rw [hSAset] at hsmul
    exact hsmul
  exact ⟨a, a.property, hxSA⟩

private lemma exists_kleinFour_le_sylow_containing_of_ne_central
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hm : 2 ≤ c.m)
    (e : c.S ≃* DihedralGroup (2 ^ c.m))
    (htz : c.t = zAmbient c.S e)
    {s : G} (hsS : s ∈ (c.S : Subgroup G))
    (hs : IsInvolution s) (hst : s ≠ c.t) :
    ∃ V : Subgroup G, V ≤ (c.S : Subgroup G) ∧ IsKleinFour V ∧
      c.t ∈ V ∧ s ∈ V := by
  classical
  let sS : c.S := ⟨s, hsS⟩
  let a : DihedralGroup (2 ^ c.m) := e sS
  have hsS2 : sS ^ 2 = 1 := Subtype.ext hs.2
  have ha2 : a ^ 2 = 1 := by
    simpa [a] using congrArg e hsS2
  have ha1 : a ≠ 1 := by
    intro h
    apply hs.1
    have hsS1 : sS = 1 := e.injective (by simpa [a] using h)
    exact congrArg Subtype.val hsS1
  rcases dihedralGroup_cases a with ⟨i, hai⟩ | ⟨i, hai⟩
  · have hord : orderOf (DihedralGroup.r i) = 2 := by
      rw [← hai]
      exact orderOf_eq_prime ha2 ha1
    have hri : DihedralGroup.r i = dCentral c.m :=
      rotation_order_two_eq_dCentral (by omega : 1 ≤ c.m) i hord
    have hsz : s = zAmbient c.S e := by
      have hsS_eq : sS = e.symm (dCentral c.m) := by
        apply e.injective
        simp [a, hai, hri]
      exact congrArg Subtype.val hsS_eq
    exact False.elim (hst (hsz.trans htz.symm))
  · let V : Subgroup G := dKleinAmbient c.S c.one_le_m e i
    have hVle : V ≤ (c.S : Subgroup G) :=
      dKleinAmbient_le_S c.S c.one_le_m e i
    have hV : IsKleinFour V := dKleinAmbient_isKleinFour c.S c.one_le_m e i
    have htV : c.t ∈ V := by
      rw [htz]
      exact dCentralAmbient_mem_dKleinAmbient c.S c.one_le_m e i
    have hsEq : s = (e.symm (DihedralGroup.sr i) : G) := by
      have hsS_eq : sS = e.symm (DihedralGroup.sr i) := by
        apply e.injective
        simpa [a] using hai
      exact congrArg Subtype.val hsS_eq
    have hsV : s ∈ V := by
      change s ∈ dKleinAmbient c.S c.one_le_m e i
      rw [hsEq, dKleinAmbient, Subgroup.mem_map]
      refine ⟨e.symm (DihedralGroup.sr i), ?_, rfl⟩
      simpa [dKleinAmbient] using dKlein_sr_mem c.one_le_m i
    exact ⟨V, hVle, hV, htV, hsV⟩

private lemma fixed_sylow_involutions_conjugate_in_A_large
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (A : Subgroup G) (hNorm : ∀ V : Subgroup G, V ≤ (c.S : Subgroup G) →
      IsKleinFour V → Subgroup.normalizer (V : Set G) ≤ A)
    (hm : 2 ≤ c.m) (e : c.S ≃* DihedralGroup (2 ^ c.m))
    (htz : c.t = zAmbient c.S e) :
    ∀ s : G, s ∈ (c.S : Subgroup G) → IsInvolution s →
      ∃ a : G, a ∈ A ∧ a * c.t * a⁻¹ = s := by
  intro s hsS hs
  by_cases hst : s = c.t
  · exact ⟨1, A.one_mem, by simp [hst]⟩
  · obtain ⟨V, hVle, hV, htV, hsV⟩ :=
      exists_kleinFour_le_sylow_containing_of_ne_central c hm e htz hsS hs hst
    have hVNorm : Subgroup.normalizer (V : Set G) ≤ A := hNorm V hVle hV
    have haz : s ≠ zAmbient c.S e := by
      intro h
      apply hst
      exact h.trans htz.symm
    have hconj : IsConj (zAmbient c.S e) s := by
      rw [isConj_iff]
      obtain ⟨g, hg⟩ := fact_2_preamble_involutions_conjugate_proved
        hmin c.t s c.t_involution hs
      exact ⟨g, by simpa [htz] using hg⟩
    obtain ⟨n, hnN, hnz, _hns⟩ :=
      fusion_to_normalizer_moves_central c.S hm e hVle hV hsV hs.1 haz hconj
    obtain ⟨γ, _hγS, hγN, hγfix, hγmove, _hγAll⟩ :=
      exists_dihedral_transposition_of_kleinFour_le_sylow c.S hm e hVle hV
    have hγs_ne : γ * s * γ⁻¹ ≠ s :=
      hγmove V hVle hV s hsV hs.1 haz
    have hzV : zAmbient c.S e ∈ V := by
      rw [← htz]
      exact htV
    have hγs : γ * s * γ⁻¹ = zAmbient c.S e * s :=
      kleinFour_action_fix_move V hV (x := zAmbient c.S e) (y := s) (δ := γ)
        hzV hsV (zAmbient_ne_one c.S (by omega : 1 ≤ c.m) e) hs.1 haz.symm
        hγN hγfix hγs_ne
    have hnA : n ∈ A := hVNorm hnN
    have hγA : γ ∈ A := hVNorm hγN
    refine ⟨γ * n, A.mul_mem hγA hnA, ?_⟩
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

private lemma fixed_sylow_involutions_conjugate_in_A_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (A : Subgroup G) (hNorm : ∀ V : Subgroup G, V ≤ (c.S : Subgroup G) →
      IsKleinFour V → Subgroup.normalizer (V : Set G) ≤ A)
    (hm : c.m = 1) (e : c.S ≃* DihedralGroup (2 ^ c.m)) :
    ∀ s : G, s ∈ (c.S : Subgroup G) → IsInvolution s →
      ∃ a : G, a ∈ A ∧ a * c.t * a⁻¹ = s := by
  classical
  let S : Subgroup G := (c.S : Subgroup G)
  let : IsKleinFour S := by
    dsimp [S]
    exact m1_sylow_isKleinFour c.S hm e
  have hSle : S ≤ (c.S : Subgroup G) := by rfl
  have hNormS : Subgroup.normalizer (S : Set G) ≤ A :=
    hNorm S hSle (inferInstance : IsKleinFour S)
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
      c.S S hSle (inferInstance : IsKleinFour S)
  obtain ⟨n, hnN, hn2C⟩ := (normalizerContainsCPrime_iff_exists S).mp hCprime
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
  intro s hsS hs
  let tS : S := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
  let sS : S := ⟨s, hsS⟩
  have htS1 : tS ≠ 1 := by
    intro h
    exact c.t_involution.1 (congrArg Subtype.val h)
  have hsS1 : sS ≠ 1 := by
    intro h
    exact hs.1 (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := kleinFour_aut_orbit_all φ hφ1 hφ2 tS sS htS1 hsS1
  have hpow := normalizerMonoidHom_pow_apply S n hnN k tS
  have hconj : n ^ k * c.t * (n ^ k)⁻¹ = s :=
    congrArg Subtype.val (hpow.symm.trans hk)
  exact ⟨n ^ k,
    hNormS ((Subgroup.normalizer (S : Set G)).pow_mem hnN k), hconj⟩

/-- If an overgroup `A` of the distinguished involution centralizer has at
least two involution classes, some Klein four in the fixed Sylow `2`-subgroup
has ambient normalizer not contained in `A`. -/
public theorem exists_kleinFour_le_sylow_normalizer_not_le_of_two_involution_classes
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (A : Subgroup G)
    (hHA : c.H ≤ A)
    (hclasses : HasAtLeastTwoInvolutionClasses A) :
    ∃ V : Subgroup G,
      V ≤ (c.S : Subgroup G) ∧
      IsKleinFour V ∧
      ¬ Subgroup.normalizer (V : Set G) ≤ A := by
  classical
  by_contra hescape
  have hNorm : ∀ V : Subgroup G, V ≤ (c.S : Subgroup G) →
      IsKleinFour V → Subgroup.normalizer (V : Set G) ≤ A := by
    intro V hVle hV
    by_contra hnot
    exact hescape ⟨V, hVle, hV, hnot⟩
  have hSA : (c.S : Subgroup G) ≤ A :=
    (centralizerSetup_S_le_H c).trans hHA
  obtain ⟨e⟩ := c.dihedralEquiv
  have hSylowFusion : ∀ s : G, s ∈ (c.S : Subgroup G) → IsInvolution s →
      ∃ a : G, a ∈ A ∧ a * c.t * a⁻¹ = s := by
    by_cases hm : 2 ≤ c.m
    · exact fixed_sylow_involutions_conjugate_in_A_large hmin c A hNorm hm e
        (centralizerSetup_t_eq_zAmbient c hm e)
    · have hmge : 1 ≤ c.m := c.one_le_m
      have hm1 : c.m = 1 := by omega
      exact fixed_sylow_involutions_conjugate_in_A_four hmin c A hNorm hm1 e
  rcases hclasses with ⟨x, y, hx, hy, hnconj⟩
  have hxG : IsInvolution (x : G) := by
    constructor
    · intro h
      exact hx.1 (Subtype.ext h)
    · exact congrArg Subtype.val hx.2
  have hyG : IsInvolution (y : G) := by
    constructor
    · intro h
      exact hy.1 (Subtype.ext h)
    · exact congrArg Subtype.val hy.2
  obtain ⟨a, haA, haxS⟩ :=
    conjugate_involution_into_fixed_sylow_of_mem c.S A hSA x.property hxG
  obtain ⟨b, hbA, hbyS⟩ :=
    conjugate_involution_into_fixed_sylow_of_mem c.S A hSA y.property hyG
  have haxI : IsInvolution (a * (x : G) * a⁻¹) := by
    constructor
    · intro h
      apply hxG.1
      have h' := congrArg (fun z : G => a⁻¹ * z * a) h
      simpa [mul_assoc] using h'
    · calc
        (a * (x : G) * a⁻¹) ^ 2 = a * ((x : G) ^ 2) * a⁻¹ := by
          simp [pow_two, mul_assoc]
        _ = 1 := by rw [hxG.2]; simp
  have hbyI : IsInvolution (b * (y : G) * b⁻¹) := by
    constructor
    · intro h
      apply hyG.1
      have h' := congrArg (fun z : G => b⁻¹ * z * b) h
      simpa [mul_assoc] using h'
    · calc
        (b * (y : G) * b⁻¹) ^ 2 = b * ((y : G) ^ 2) * b⁻¹ := by
          simp [pow_two, mul_assoc]
        _ = 1 := by rw [hyG.2]; simp
  obtain ⟨kx, hkxA, hkx⟩ := hSylowFusion
    (a * (x : G) * a⁻¹) haxS haxI
  obtain ⟨ky, hkyA, hky⟩ := hSylowFusion
    (b * (y : G) * b⁻¹) hbyS hbyI
  have hkxBack : kx⁻¹ * (a * (x : G) * a⁻¹) * kx = c.t := by
    rw [← hkx]
    group
  let g : G := b⁻¹ * ky * kx⁻¹ * a
  have hgA : g ∈ A := by
    exact A.mul_mem
      (A.mul_mem (A.mul_mem (A.inv_mem hbA) hkyA) (A.inv_mem hkxA)) haA
  have hgxy : g * (x : G) * g⁻¹ = (y : G) := by
    calc
      g * (x : G) * g⁻¹ =
          b⁻¹ * (ky * (kx⁻¹ * (a * (x : G) * a⁻¹) * kx) * ky⁻¹) * b := by
            dsimp [g]
            group
      _ = b⁻¹ * (ky * c.t * ky⁻¹) * b := by rw [hkxBack]
      _ = b⁻¹ * (b * (y : G) * b⁻¹) * b := by rw [hky]
      _ = (y : G) := by group
  apply hnconj
  exact ⟨⟨g, hgA⟩, Subtype.ext hgxy⟩

end CFSG.GorensteinWalter
