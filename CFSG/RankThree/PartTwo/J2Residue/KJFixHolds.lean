module

public import CFSG.RankThree.PartTwo.J2Residue.KFactsCommon
public import CFSG.RankThree.PartTwo.J2Residue.ConjAction
public import CFSG.RankThree.PartTwo.J2Residue.KJFixCore
public import CFSG.RankThree.PartTwo.J2Residue.KFacts

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic CFSG.ComponentClassification.J2Cover
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

theorem exists_sylow_zJ :
    ∃ S : Sylow 3 J2, nativeEquivP.symm zJ ∈ (S : Subgroup J2) ∧
      (S : Subgroup J2) ≤ Subgroup.centralizer {nativeEquivP.symm zJ} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ : Nat.card J2 = 604800 := (Nat.card_congr nativeEquivP.toEquiv).trans card_GJ
  have hcard : Nat.card ↥(P3.map nativeEquivP.symm.toMonoidHom) =
      3 ^ (Nat.card J2).factorization 3 := by
    rw [Subgroup.card_map_of_injective nativeEquivP.symm.injective, card_P3, hJ,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 604800 = 3 ^ 3 * 22400 by norm_num) (by norm_num)]
    norm_num
  have hzC : zJ ∈ P3 ⊓ Subgroup.centralizer (P3 : Set GJ) := by
    rw [inf_centralizer_P3, ← z_eq]
    exact Subgroup.mem_zpowers _
  refine ⟨Sylow.ofCard _ hcard, ?_, ?_⟩
  · rw [Sylow.coe_ofCard]
    exact Subgroup.mem_map_of_mem _ hzC.1
  · rw [Sylow.coe_ofCard]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_iff.mp hzC.2 s hs
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h]

theorem mulAut_inv_apply_eq_self_iff {V : Type*} [Group V] (f : MulAut V) (m : V) :
    f⁻¹ m = m ↔ f m = m := by
  constructor
  · intro h
    calc f m = f (f⁻¹ m) := by rw [h]
      _ = m := MulAut.apply_inv_self V f m
  · intro h
    calc f⁻¹ m = f⁻¹ (f m) := by rw [h]
      _ = m := MulAut.inv_apply_self V f m

theorem kJFix_holds :
    KJFix := by
  intro L _ _ hψ M hMn hMR hM1 hmin d hd hdS hcard
  obtain ⟨ψ⟩ := hψ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 L).Normal := CFSG.pCore_normal
  haveI : M.Normal := hMn
  have hR2 : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  obtain ⟨hEA, hRC⟩ := CFSG.minimalNormal_le_isPGroup hMn CFSG.pCore_normal hR2 hMR hM1 hmin
  have hRM : ∀ r ∈ CFSG.pCore 2 L, ∀ m ∈ M, r * m = m * r := fun r hr m hm =>
    (Subgroup.mem_centralizer_iff.mp (hRC hr) m hm).symm
  set ρ : GJ →* MulAut ↥M := (conjActionJ2 hRM ψ).comp nativeEquivP.symm.toMonoidHom with hρdef
  have hρ : ∀ (ℓ : L) (m : M), ((ρ (nativeEquivP (ψ ℓ)) m : M) : L) = ℓ * m * ℓ⁻¹ := by
    intro ℓ m
    rw [hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      conjActionJ2_mk]
  have hirr : ∀ W : Subgroup ↥M, (∀ g : GJ, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hK : (W.map M.subtype).Normal := ⟨by
      rintro _ ⟨w, hw, rfl⟩ ℓ
      refine ⟨ρ (nativeEquivP (ψ ℓ)) w, hW _ w hw, ?_⟩
      rw [Subgroup.coe_subtype, hρ]⟩
    rcases hmin _ hK (Subgroup.map_subtype_le W) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h
    · right
      rw [eq_top_iff]
      intro w _
      have hw : (w : L) ∈ W.map M.subtype := by
        rw [h]
        exact w.2
      obtain ⟨w', hw', hww⟩ := hw
      rwa [Subtype.ext hww] at hw'
  obtain ⟨g, hg⟩ := exists_conj_mk_eq_or_eq_inv hR2 ψ hd hdS
    (fun h => zJ_ne_one (by rw [← nativeEquivP.apply_symm_apply zJ, h, map_one]))
    exists_sylow_zJ
  obtain ⟨γ, hγ⟩ : ∃ γ : GJ, γ⁻¹ * zJ * γ = nativeEquivP (ψ d) ∨
      γ⁻¹ * zJ * γ = (nativeEquivP (ψ d))⁻¹ := by
    refine ⟨nativeEquivP (ψ g), ?_⟩
    have e : nativeEquivP (ψ ((g * d * g⁻¹ : L) : L ⧸ CFSG.pCore 2 L)) =
        nativeEquivP (ψ g) * nativeEquivP (ψ d) * (nativeEquivP (ψ g))⁻¹ := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    rcases hg with h | h
    · left
      rw [h, MulEquiv.apply_symm_apply] at e
      rw [e]
      group
    · right
      rw [h, map_inv, MulEquiv.apply_symm_apply] at e
      have e' : zJ = nativeEquivP (ψ g) * (nativeEquivP (ψ d))⁻¹ * (nativeEquivP (ψ g))⁻¹ := by
        rw [← inv_inv zJ, e]
        group
      rw [e']
      group
  set ρ' : GJ →* MulAut ↥M := ρ.comp (MulAut.conj γ⁻¹).toMonoidHom with hρ'def
  have hρ' : ∀ h : GJ, ρ' h = ρ (γ⁻¹ * h * γ) := by
    intro h
    rw [hρ'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hirr' : ∀ W : Subgroup ↥M, (∀ g : GJ, ∀ w ∈ W, ρ' g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hirr W fun g w hw => ?_
    have h := hW (γ * g * γ⁻¹) w hw
    rwa [hρ', show γ⁻¹ * (γ * g * γ⁻¹) * γ = g by group] at h
  have hfixd : ∀ m : ↥M, ρ' zJ m = m ↔ (m : L) ∈ M ⊓ Subgroup.centralizer {d} := by
    intro m
    have hp : ρ (nativeEquivP (ψ d)) m = m ↔ d * m * d⁻¹ = m := by
      rw [Subtype.ext_iff, hρ]
    have hp' : ρ' zJ m = m ↔ ρ (nativeEquivP (ψ d)) m = m := by
      rw [hρ']
      rcases hγ with h | h
      · rw [h]
      · rw [h, map_inv, mulAut_inv_apply_eq_self_iff]
    rw [hp', hp, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    simp only [SetLike.coe_mem, true_and]
    exact eq_comm
  obtain ⟨v₀, hv₀1, hv₀u⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(M ⊓ Subgroup.centralizer {d}))).mp hcard
  set v : ↥M := ⟨v₀.1, v₀.2.1⟩ with hvdef
  have hv : v ≠ 1 := by
    intro h
    apply hv₀1
    apply Subtype.ext
    have h' : ((v : ↥M) : L) = ((1 : ↥M) : L) := congrArg Subtype.val h
    exact h'
  have hfix : ∀ m : ↥M, ρ' zJ m = m ↔ m = 1 ∨ m = v := by
    intro m
    rw [hfixd]
    constructor
    · intro hm
      by_cases h1 : (⟨m, hm⟩ : ↥(M ⊓ Subgroup.centralizer {d})) = 1
      · left
        apply Subtype.ext
        have h' : ((⟨m, hm⟩ : ↥(M ⊓ Subgroup.centralizer {d})) : L) =
            ((1 : ↥(M ⊓ Subgroup.centralizer {d})) : L) := congrArg Subtype.val h1
        exact h'
      · right
        apply Subtype.ext
        have h' : ((⟨m, hm⟩ : ↥(M ⊓ Subgroup.centralizer {d})) : L) = (v₀ : L) :=
          congrArg Subtype.val (hv₀u _ h1)
        exact h'
    · rintro (rfl | rfl)
      · exact (M ⊓ Subgroup.centralizer {d}).one_mem
      · exact v₀.2
  haveI := hEA
  have hcomm : ∀ a b : ↥M, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := ↥M)).comm a b
  have hsq : ∀ a : ↥M, a * a = 1 := fun a => by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := M) (a : L) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq, h])
  letI : CommGroup ↥M := { (inferInstance : Group ↥M) with mul_comm := hcomm }
  exact C280.card_eq_two ρ' v hsq hirr' hv hfix

end CFSG.RankThree.PartTwo.J2Residue
