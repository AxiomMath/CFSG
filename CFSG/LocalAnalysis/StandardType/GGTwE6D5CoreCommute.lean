module

public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreLang

public section

namespace CFSG.StandardType.TwE6D5Core

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen

section Helpers

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

private theorem exists_fixed_split_d5 [CharP L 2]
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 40) {b : Fin Tag.E6.rank → Lˣ}
    (hb : rootDiagUnit Tag.E6 b ∈ S.D.torus) :
    ∃ t ∈ charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)),
      S.D.step t = t ∧ ∃ g ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)),
        S.D.step g = g ∧ rootDiagUnit Tag.E6 b = t * g := by
  obtain ⟨v, J, hJ, hΨv⟩ := d5_position h3 hap hk
  have hHcomm : ∀ x ∈ charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)),
      ∀ y ∈ charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)), x * y = y * x := by
    intro x hx y hy
    obtain ⟨b₁, -, rfl⟩ := mem_charKerTorus.1 hx
    obtain ⟨b₂, -, rfl⟩ := mem_charKerTorus.1 hy
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hHQ : charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)) ≤
      Subgroup.normalizer (rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
        Set (ModGL Tag.E6 L)) :=
    (charKerTorus_le_centralizer_rootSpan (fun γ hγ => hγ.1)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hbot : charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)) ⊓
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) = ⊥ := by
    rw [hΨv]
    exact charKerTorus_inf_rootSpan v hJ
  have hsup : torusGroup Tag.E6 L ≤
      charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)) ⊔
        rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    rw [hΨv]
    exact torusGroup_le_charKerTorus_sup v hJ
  obtain ⟨t, htH, htF, g, hgQ, hgF, hmul⟩ := exists_fixed_split S.D.step hHcomm hHQ
    (fun h hh => step_mem_charKerTorus S hFr hΦ hT hh)
    (fun g hg => step_mem_rootSpan S (fun γ hγ => hγ.1)
      (fun γ hγ => rho_mem_kernelRoots_of_mem_torus S hT γ hγ) hg)
    (fun s hs => ⟨1, one_mem _, by
      rw [hbot, Subgroup.mem_bot] at hs
      rw [hs, map_one, inv_one, one_mul]⟩)
    (hsup (rootDiagUnit_mem_torusGroup b)) (mem_twistedTorusOf.1 hb).2
  exact ⟨t, htH, htF, g, hgQ, hgF, hmul⟩

end Helpers

section HelperSplit

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
private theorem rootChar_eq_one_of_split [CharP L 2]
    (S : LangSetup Tag.E6 L p₀) {a b : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} {t g : ModGL Tag.E6 L}
    (hmul : rootDiagUnit Tag.E6 b = t * g)
    (htH : t ∈ charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)))
    (hgR : g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (hRQ : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)))
    (hHQ : charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)) ≤
      Subgroup.centralizer (rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
        Set (ModGL Tag.E6 L)))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      x * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * x)
    (hZ4 : ∀ z ∈ Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      z ^ 4 = 1) :
    ∀ γ ∈ kernelRoots (rootCharHom a), rootChar b γ = 1 := by
  have hg_inv : g = t⁻¹ * rootDiagUnit Tag.E6 b := by rw [hmul]; group
  have hcent : g ∈ Subgroup.centralizer
      (rationalComponent S.ρ S.Γ (rootCharHom a) i : Set (ModGL Tag.E6 L)) := by
    rw [Subgroup.mem_centralizer_iff]; intro x hx
    have hxQ : x ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := hRQ hx
    have hxt : x * t = t * x := Subgroup.mem_centralizer_iff.1 (hHQ htH) x hxQ
    have hxt' : x * t⁻¹ = t⁻¹ * x := (Commute.inv_right hxt).eq
    calc x * g = x * (t⁻¹ * rootDiagUnit Tag.E6 b) := by rw [hg_inv]
      _ = (x * t⁻¹) * rootDiagUnit Tag.E6 b := by group
      _ = (t⁻¹ * x) * rootDiagUnit Tag.E6 b := by rw [hxt']
      _ = t⁻¹ * (x * rootDiagUnit Tag.E6 b) := by group
      _ = t⁻¹ * (rootDiagUnit Tag.E6 b * x) := by rw [hcomm x hx]
      _ = (t⁻¹ * rootDiagUnit Tag.E6 b) * x := by group
      _ = g * x := by rw [hg_inv]
  have hcen : (⟨g, hgR⟩ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∈
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    Subgroup.mem_center_iff.2 fun x => Subtype.ext (hcent x x.2)
  have hgpow : g ^ 4 = 1 := by simpa using congrArg Subtype.val (hZ4 ⟨g, hgR⟩ hcen)
  obtain ⟨c, hc, rfl⟩ := mem_charKerTorus.1 htH
  have hg_eq : g = rootDiagUnit Tag.E6 (c⁻¹ * b) := by
    rw [hg_inv, rootDiagUnit_inv, ← rootDiagUnit_mul]
  have hcb4 : (c⁻¹ * b) ^ 4 = 1 := by
    refine CFSG.LieType.Chevalley.rootDiagUnit_injective ?_
    rw [show rootDiagUnit Tag.E6 ((c⁻¹ * b) ^ 4) =
        rootDiagUnit Tag.E6 (c⁻¹ * b) ^ 4 from
      map_pow (rootDiagUnitHom Tag.E6 L) (c⁻¹ * b) 4,
      rootDiagUnit_one, ← hg_eq]
    exact hgpow
  have hcb : c⁻¹ * b = 1 := funext fun j =>
    Units.ext (eq_one_of_pow_four_eq_one_of_charTwo (by
      simpa using congrArg Units.val (congrFun hcb4 j)))
  intro γ hγ; exact (inv_mul_eq_one.1 hcb).symm ▸ hc γ hγ

end HelperSplit

theorem rootChar_eq_one_of_commute_d5
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr)
    (hL : ringChar L = 2) (h3q : 3 ∣ S.D.q + 1) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 40) (i : KernelComponent (rootCharHom a))
    {b : Fin Tag.E6.rank → Lˣ} (hb : rootDiagUnit Tag.E6 b ∈ S.D.torus)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      x * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * x) :
    ∀ γ ∈ kernelRoots (rootCharHom a), rootChar b γ = 1 := by
  have hchar : CharP L 2 := ringChar.of_eq hL
  have h3 : ((3 : ℕ) : L) ≠ 0 := fun h =>
    absurd ((CharP.cast_eq_zero_iff L 2 3).1 h) (by omega)
  obtain ⟨t, htH, -, g, hgQ, hgF, hmul⟩ :=
    exists_fixed_split_d5 S hFr hΦ h3 hT hap hk hb
  have hgR := mem_rationalComponent_of_step_eq S hFr hΦ h3 h3q hT hap hk i hgQ hgF
  have hRQ := rationalComponent_le_rootSpan S hT i
  have hHQ : charKerTorus Tag.E6 L (kernelRoots (rootCharHom a)) ≤
      Subgroup.centralizer (rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :
        Set (ModGL Tag.E6 L)) :=
    charKerTorus_le_centralizer_rootSpan (fun γ hγ => hγ.1)
  obtain ⟨_, _, -, -, hmodel⟩ := d5_class_strongModel S hFr hΦ h3 hT hap h3q hk i
  exact rootChar_eq_one_of_split (S := S) (i := i) hmul htH hgR hRQ hHQ hcomm hmodel.2.2

end CFSG.StandardType.TwE6D5Core

end
