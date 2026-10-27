module

public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreLang
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreFrame
import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.StandardType.TwE6D5Core

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups


theorem twE6D5Core_of_lang
    (hF4 : ∀ {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
      {Fr : L →+* L}, (∀ c, Fr c = c ^ S.D.q) → S.D.Φ = twistHom TwistTag.E6 L Fr →
      ringChar L = 2 → 3 ∣ S.D.q + 1 → ∀ {a : Fin Tag.E6.rank → Lˣ},
      rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
      (kernelRoots (rootCharHom a)).ncard = 40 →
      ∃ Z R : Subgroup (ModGL Tag.E6 L),
        S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} = Z ⊔ R ∧ IsCyclic Z ∧
          Z ≤ Subgroup.centralizer (R : Set (ModGL Tag.E6 L)) ∧ CFSG.IsQuasisimple R) :
    TwE6RootAs.TwE6D5Core := by
  intro K _ _ σ q hK hσ h2 h3q Fr hFr v _ g0 hg0C hg0 t ht a hap hk hta
  obtain ⟨S, ι, hSq, hSΦ, hT, hinj, hrange, hconj, -, -, -⟩ :=
    exists_langSetup_of_twE6Frame σ hK hσ h2 hFr hg0C hg0 ht hta
  haveI : CharP K 2 := ringChar.of_eq h2
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Z, R, hZR, hZ, hZc, hR⟩ := hF4 S (fun c => by rw [hSq]; exact hFr c) hSΦ
    (ringChar.eq (AlgebraicClosure K) 2) (by rw [hSq]; exact h3q) hT hap hk
  have hZι : Z ≤ ι.range := hrange ▸ le_sup_left.trans (hZR.symm.le.trans inf_le_left)
  have hRι : R ≤ ι.range := hrange ▸ le_sup_right.trans (hZR.symm.le.trans inf_le_left)
  have hcomap : ∀ H : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)),
      Function.Injective (ι.subgroupComap H) :=
    fun H x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  refine ⟨Z.comap ι, R.comap ι, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.comap_sup_eq_of_le_range ι hZι hRι, ← hZR]
    ext c
    have key : (c : ModGL TwistTag.E6.tag K) * t = t * c ↔
        ι c * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * ι c := by
      have e : twistedE6InndiagConj K σ ⟨t, ht⟩ c = c ↔ (c : ModGL TwistTag.E6.tag K) * t = t * c :=
        by
          rw [Subtype.ext_iff]
          change t * (c : ModGL TwistTag.E6.tag K) * t⁻¹ = c ↔ _
          rw [mul_inv_eq_iff_eq_mul, eq_comm]
      rw [← e, ← hinj.eq_iff, hconj c, mul_inv_eq_iff_eq_mul, eq_comm]
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, key, Subgroup.mem_comap,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, ← hrange]
    exact ⟨fun h => ⟨MonoidHom.mem_range.2 ⟨c, rfl⟩, h⟩, fun h => h.2⟩
  · haveI := hZ
    exact isCyclic_of_injective (ι.subgroupComap Z) (hcomap Z)
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 (hZc hx) (ι y) hy
  · refine CFSG.IsQuasisimple.of_mulEquiv (MulEquiv.ofBijective (ι.subgroupComap R)
      ⟨hcomap R, fun y => ?_⟩) hR
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hRι y.2)
    exact ⟨⟨x, show ι x ∈ R from hx ▸ y.2⟩, Subtype.ext hx⟩

end CFSG.StandardType.TwE6D5Core

namespace CFSG.StandardType.TwE6RootAs


theorem twE6D5Core_holds : TwE6D5Core :=
  CFSG.StandardType.TwE6D5Core.twE6D5Core_of_lang
    CFSG.StandardType.TwE6D5Core.exists_centralizer_eq_sup_d5

end CFSG.StandardType.TwE6RootAs

end
