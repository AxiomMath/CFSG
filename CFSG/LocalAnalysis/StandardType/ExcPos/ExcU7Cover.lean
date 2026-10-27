module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7Frame
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7CoverRoot
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7CoverIota
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7CoverSwap
import CFSG.LieType.HighestRoot.ModelCenter
import CFSG.ClassicalInvolution.Q3.ModelCenter
import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.RootSystem CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open scoped MatrixGroups


theorem excU7Cover_ggU_eq (f : ℕ) (hf : 1 ≤ f) :
    ggU .PSU 6 f =
      ⟨CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6,
        CFSG.LieType.Universal.Unitary.rootDatum (excU7Cover_card_field f hf) 6⟩ := by
  simp only [ggU, CFSG.LieType.Universal.lieUniversal, hf, ↓reduceDIte]

theorem excU7Cover_core {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀) (a : Fin Tag.E6.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (f p : ℕ) (h : ExcSuClass S a i f p) :
    ∃ φ : (ggU .PSU 6 f).K →* ModGL Tag.E6 GGL,
      φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
      φ.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧ Finite (ggU .PSU 6 f).K ∧
      Group.IsPerfect (ggU .PSU 6 f).K ∧
      CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .PSU 6 f).K ∧
      ∃ (β : Fin (ggU .PSU 6 f).D.rank → ℤ) (u : (ggU .PSU 6 f).K),
        β ∈ (ggU .PSU 6 f).D.roots ∧ 2 • β ∉ (ggU .PSU 6 f).D.roots ∧
        ExcSwapped S a i f (ggRootSub (ggU .PSU 6 f).D φ β u) := by
  classical
  obtain ⟨σQ, ψ, σf, z, hσQ, hψ, hΨ, hz, hconj, hrange, hfix, -, hf1, hker, -⟩ :=
    excSuClass_frame S a i f p h
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := excU7Cover_card_field f hf1
  obtain ⟨E, g, ι, hEinj, hEσ, hg, hιmat⟩ := excU7Cover_iota f hf1 σQ hσQ
  obtain ⟨hfin, hperf, hodd⟩ := excU7Cover_group_props f hf1
  let σF : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
    CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f
  have hσ : ∀ c, σF (σF c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hF
  have hM : ggU .PSU 6 f = (⟨SU σF 6, rootDatum hF 6⟩ : LieUniversal) :=
    excU7Cover_ggU_eq f hf1
  refine hM.symm ▸ ?_
  let ψ' : SL(6, GGL) →* ModGL Tag.E6 GGL := (MulAut.conj z).toMonoidHom.comp ψ
  let Fix : Subgroup (SL(6, GGL)) := fixSubgroup (stdUnitaryEquiv (ν := 6) σQ)
  let φ : (SU σF 6) →* ModGL Tag.E6 GGL := (ψ'.comp Fix.subtype).comp ι.toMonoidHom
  have hφ_apply : ∀ y : SU σF 6, φ y = z * ψ (ι y) * z⁻¹ := fun _ => rfl
  have hff : ∀ X : SL(6, GGL), ψ' X = 1 ↔ ψ X = 1 := by
    intro X
    change z * ψ X * z⁻¹ = 1 ↔ ψ X = 1
    constructor
    · intro h
      calc ψ X = z⁻¹ * (z * ψ X * z⁻¹) * z := by group
        _ = z⁻¹ * 1 * z := by rw [h]
        _ = 1 := by group
    · intro h
      rw [h]
      group
  have hrangeφ : φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    change ((ψ'.comp Fix.subtype).comp ι.toMonoidHom).range =
      rationalComponent S.ρ S.Γ (rootCharHom a) i
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hfix
  have hkerφ : φ.ker ≤ Subgroup.center (SU σF 6) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : ψ' (ι x) = 1 := hx
    have hx2 : ψ (ι x) = 1 := (hff (ι x)).1 hx1
    have hx3 : (ι x : SL(6, GGL)) ∈ Subgroup.center SL(6, GGL) :=
      hker (by rw [MonoidHom.mem_ker]; exact hx2)
    have hx4 : ι x ∈ Subgroup.center ↥Fix :=
      Subgroup.comap_center_le_center (f := Fix.subtype) Fix.subtype_injective
        (by simpa using hx3)
    exact Subgroup.comap_center_le_center (f := ι.toMonoidHom) ι.injective
      (by simpa using hx4)
  have hrat_le : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.Γ := by
    rw [rationalComponent]
    refine (Subgroup.commutator_le_self (rationalSpan S.ρ S.Γ (rootCharHom a) i)).trans ?_
    rw [rationalSpan]
    exact inf_le_right
  obtain ⟨α, w, hα, hw, hle, hF2, hcomm, hall⟩ :=
    excU7Cover_swap S a i f σQ hσQ ψ σf hψ hΨ z hz hconj hrange g hg
  have hgg : ggRootSub (rootDatum hF 6) φ excU7Beta 1 =
      ((rootDatum hF 6).rootGroup excU7Beta).map φ := by
    change (((rootDatum hF 6).rootGroup excU7Beta).map
        (MulAut.conj (1 : SU σF 6)).toMonoidHom).map φ =
      ((rootDatum hF 6).rootGroup excU7Beta).map φ
    have h1 : (MulAut.conj (1 : SU σF 6)).toMonoidHom = MonoidHom.id (SU σF 6) := by
      ext x
      simp
    rw [h1, Subgroup.map_id]
  have hrev1 : Fin.rev (1 : Fin 6) = 4 := by decide
  have hrev0 : Fin.rev (0 : Fin 6) = 5 := by decide
  have hrootmap : ∀ c : Multiplicative (GaloisField 2 (2 * f)),
      (rootMatrix σF (0 : Fin 6) (1 : Fin 6) c.toAdd).map E =
        1 + Matrix.single (0 : Fin 6) (1 : Fin 6) (E c.toAdd) +
          Matrix.single (4 : Fin 6) (5 : Fin 6) (σQ (E c.toAdd)) := by
    intro c
    rw [rootMatrix, Matrix.map_sub E (map_sub E), Matrix.map_add E (map_add E),
      Matrix.map_one E (map_zero E) (map_one E), Matrix.map_single, Matrix.map_single,
      hEσ c.toAdd, hrev1, hrev0, sub_eq_add_neg, Matrix.single_neg, CharTwo.neg_eq]
  have hinj : Function.Injective
      (φ.domRestrict ((rootDatum hF 6).rootGroup excU7Beta)) := by
    intro x y hxy
    have hxy' : φ (x : SU σF 6) = φ (y : SU σF 6) := by simpa using hxy
    let ρ : Multiplicative (GaloisField 2 (2 * f)) →* SU σF 6 :=
      rootHom σF hσ (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide) (by decide) (by decide)
    have hHR : (rootDatum hF 6).rootGroup excU7Beta ≤ ρ.range := by
      rw [rootGroup_excU7Beta (p := 2) (f := f) hF]
    obtain ⟨c₁, hc₁⟩ := MonoidHom.mem_range.1 (hHR x.2)
    obtain ⟨c₂, hc₂⟩ := MonoidHom.mem_range.1 (hHR y.2)
    have hxy_eq : (x : SU σF 6) * (y : SU σF 6)⁻¹ = ρ (c₁ * c₂⁻¹) := by
      rw [← hc₁, ← hc₂, ← map_inv, ← map_mul]
    have hsq : ((x : SU σF 6) * (y : SU σF 6)⁻¹) ^ 2 = 1 := by
      rw [hxy_eq, ← map_pow]
      have hc12 : (c₁ * c₂⁻¹) ^ 2 = 1 := by
        rw [← ofAdd_toAdd (c₁ * c₂⁻¹), ← ofAdd_nsmul, two_nsmul,
          CharTwo.add_self_eq_zero, ofAdd_zero]
      rw [hc12, map_one]
    have hker1 : (x : SU σF 6) * (y : SU σF 6)⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy', mul_inv_cancel]
    have hcent : (x : SU σF 6) * (y : SU σF 6)⁻¹ ∈ Subgroup.center (SU σF 6) :=
      hkerφ hker1
    have h32 : ((6 : ℕ), 2 ^ f) ≠ (3, 2) := by
      intro hcon
      exact (by norm_num : (6 : ℕ) ≠ 3) (congrArg Prod.fst hcon)
    have hq : (x : SU σF 6) * (y : SU σF 6)⁻¹ = 1 :=
      CFSG.ComponentClassification.RankTwoOddLie.centerPPrime_unitary
        (F := GaloisField 2 (2 * f)) (f := f) (n := 6) hF (by norm_num) h32
        ((x : SU σF 6) * (y : SU σF 6)⁻¹) hcent hsq
    exact Subtype.ext (mul_inv_eq_one.mp hq)
  have hcardmap : Nat.card ↥(((rootDatum hF 6).rootGroup excU7Beta).map φ) =
      Nat.card ↥((rootDatum hF 6).rootGroup excU7Beta) := by
    rw [← MonoidHom.domRestrict_range (f := φ)
      (K := (rootDatum hF 6).rootGroup excU7Beta)]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcardH : Nat.card ↥((rootDatum hF 6).rootGroup excU7Beta) = (2 ^ f) ^ 2 :=
    card_rootGroup_excU7Beta (p := 2) (f := f) hF
  have hAle : ((rootDatum hF 6).rootGroup excU7Beta).map φ ≤ S.Γ :=
    (Subgroup.map_le_range φ ((rootDatum hF 6).rootGroup excU7Beta)).trans
      ((le_of_eq hrangeφ).trans hrat_le)
  refine ⟨φ, hrangeφ, hkerφ, hfin, hperf, hodd, ?_⟩
  refine ⟨excU7Beta, 1, ?_, ?_, ?_⟩
  · exact excU7Beta_mem_roots (p := 2) (f := f) hF
  · exact two_smul_excU7Beta_notMem_roots (p := 2) (f := f) hF
  · rw [hgg]
    unfold ExcSwapped
    refine ⟨?_, ?_, α, w, hα, hw, hle, hF2, hcomm, ?_⟩
    · rw [hcardmap, hcardH]
    · exact hAle
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      rw [rootGroup_excU7Beta (p := 2) (f := f) hF] at hy
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hy
      rw [hφ_apply]
      have hX : ((ι (rootHom σF hσ (i := (0 : Fin 6)) (j := (1 : Fin 6))
            (by decide) (by decide) (by decide) c) : SL(6, GGL)) :
            Matrix (Fin 6) (Fin 6) GGL) =
          (g : Matrix (Fin 6) (Fin 6) GGL) *
            (1 + Matrix.single (0 : Fin 6) (1 : Fin 6) (E c.toAdd) +
              Matrix.single (4 : Fin 6) (5 : Fin 6) (σQ (E c.toAdd))) *
            ((g⁻¹ : SL(6, GGL)) : Matrix (Fin 6) (Fin 6) GGL) := by
        rw [hιmat (rootHom σF hσ (i := (0 : Fin 6)) (j := (1 : Fin 6))
              (by decide) (by decide) (by decide) c),
          coe_rootHom, hrootmap c]
      exact hall (E c.toAdd) _ hX

theorem excU7Cover_holds : ExcU7Cover := fun _ S a i f p h => excU7Cover_core S a i f p h

end CFSG.StandardType.LieKnownR2.ExcPos
