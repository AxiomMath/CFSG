module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5PlainFix

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section YBasic

@[expose] noncomputable def ggG5_Y
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    (F : GGLangFrame t p f ht) (u : WeylGroup (langTag t)) : ModGL (langTag t) GGL :=
  F.M.D.g0 * canonicalRep (coxeterSystem (langTag t)) GGL u * F.M.D.g0⁻¹

private theorem g5_canonicalRep_conj_charTwo
    {τ : Tag} {M : Type} [Field M] [CharP M 2]
    (a b : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) M a * canonicalRep (coxeterSystem τ) M b *
        (canonicalRep (coxeterSystem τ) M a)⁻¹ =
      canonicalRep (coxeterSystem τ) M (a * b * a⁻¹) := by
  rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]

private theorem g5_permLattice_permCongr_one {τ : Tag} {R : ℕ} (h : R = τ.rank)
    (v : Fin τ.rank → ℤ) :
    permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) v = v := by
  subst h
  rfl

private theorem g5_permLattice_sub_smul {τ : Tag} (σ : Equiv.Perm (Fin τ.rank))
    (v : Fin τ.rank → ℤ) (c : ℤ) (β : Fin τ.rank → ℤ) :
    permLattice σ (v - c • β) = permLattice σ v - c • permLattice σ β := by
  funext j
  simp [permLattice, Pi.sub_apply, Pi.smul_apply]

private theorem g5_weyl_conj_untw
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t}
    (F : GGLangFrame t p f ht) (u : WeylGroup (langTag t)) (hu : GGCommPi t p f ht u)
    (hgraph : ∀ y : Fin (langTag t).rank → ℤ, ggGraphLat t y = y) :
    F.M.w * u * F.M.w⁻¹ = u := by
  have hw' : ∀ y : Fin (langTag t).rank → ℤ,
      F.M.w • y = eps p f •
        permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) y := by
    intro y
    have h := F.M.hw y
    rwa [hgraph y] at h
  have hwu : F.M.w * u = u * F.M.w := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin (langTag t).rank → ℤ)
    intro v
    calc (F.M.w * u) • v = F.M.w • (u • v) := by rw [mul_smul]
      _ = eps p f •
            permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) (u • v) :=
          hw' (u • v)
      _ = eps p f •
            (u • permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) v) :=
          by rw [hu v]
      _ = u • (eps p f •
            permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) v) :=
          by rw [smul_comm]
      _ = u • (F.M.w • v) := by rw [← hw' v]
      _ = (u * F.M.w) • v := by rw [mul_smul]
  rw [hwu, mul_assoc, mul_inv_cancel, mul_one]

private theorem g5_weyl_conj_tw
    {p f : ℕ} {ht : GGExcFive .twistedE6}
    (F : GGLangFrame .twistedE6 p f ht) (u : WeylGroup (langTag .twistedE6))
    (hu : GGCommPi .twistedE6 p f ht u) :
    (show WeylGroup TwistTag.E6.tag from F.M.w) *
        weylTwist TwistTag.E6 (show WeylGroup TwistTag.E6.tag from u) *
        (show WeylGroup TwistTag.E6.tag from F.M.w)⁻¹ =
      (show WeylGroup TwistTag.E6.tag from u) := by
  let w : WeylGroup TwistTag.E6.tag := F.M.w
  let u' : WeylGroup TwistTag.E6.tag := u
  change w * weylTwist TwistTag.E6 u' * w⁻¹ = u'
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.E6.tag.rank → ℤ)
  intro v
  have hw' : ∀ y : Fin TwistTag.E6.tag.rank → ℤ,
      w • permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6) y =
        eps p f • permLattice (τ := TwistTag.E6.tag)
          ((finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)) y := by
    intro y
    have h := F.M.hw (show Fin (langTag .twistedE6).rank → ℤ from y)
    exact h
  have hu' : ∀ y : Fin TwistTag.E6.tag.rank → ℤ,
      u' • permLattice (τ := TwistTag.E6.tag)
          ((finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)) y =
        permLattice (τ := TwistTag.E6.tag)
          ((finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)) (u' • y) :=
    fun y => hu (show Fin (langTag .twistedE6).rank → ℤ from y)
  set z : Fin TwistTag.E6.tag.rank → ℤ :=
    permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6).symm (w⁻¹ • v) with hz
  have hγz : permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6) z = w⁻¹ • v := by
    rw [hz, permLattice_permLattice_symm]
  have hπ'z : eps p f • permLattice (τ := TwistTag.E6.tag)
      ((finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)) z = v := by
    have h1 := hw' z
    rw [hγz] at h1
    rw [← mul_smul, mul_inv_cancel, one_smul] at h1
    exact h1.symm
  calc (w * weylTwist TwistTag.E6 u' * w⁻¹) • v
      = w • (weylTwist TwistTag.E6 u' • (w⁻¹ • v)) := by rw [mul_smul, mul_smul]
    _ = w • (permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6)
          (u' • permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6).symm (w⁻¹ • v))) := by
          rw [weylTwist_smul]
    _ = w • (permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6) (u' • z)) := by rw [hz]
    _ = eps p f • permLattice (τ := TwistTag.E6.tag)
          ((finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)) (u' • z) := hw' (u' • z)
    _ = eps p f • (u' • permLattice (τ := TwistTag.E6.tag)
          ((finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)) z) := by
          rw [← hu' z]
    _ = u' • (eps p f • permLattice (τ := TwistTag.E6.tag)
          ((finCongr (rank_eq_langTag f ht)).permCongr (piB .twistedE6 p f)) z) := by
          rw [smul_comm]
    _ = u' • v := by rw [hπ'z]

theorem ggG5_Y_mul
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} (F : GGLangFrame t p f ht)
    (u v : WeylGroup (langTag t)) : ggG5_Y F (u * v) = ggG5_Y F u * ggG5_Y F v := by
  unfold ggG5_Y
  rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]
  group

theorem ggG5_Y_one
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} (F : GGLangFrame t p f ht) :
    ggG5_Y F 1 = 1 := by
  unfold ggG5_Y
  rw [canonicalRep_one]
  group

theorem ggG5_Y_inv
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} (F : GGLangFrame t p f ht)
    (u : WeylGroup (langTag t)) : ggG5_Y F u⁻¹ = (ggG5_Y F u)⁻¹ := by
  unfold ggG5_Y
  rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo]
  group

theorem ggG5_Y_mem_fix
    {t : StatedLieTag} {p f : ℕ} {ht : GGExcFive t} (F : GGLangFrame t p f ht)
    (u : WeylGroup (langTag t)) (hu : GGCommPi t p f ht u) : ggG5_Y F u ∈ F.M.D.fix := by
  have hmodel : canonicalRep (coxeterSystem (langTag t)) GGL u ∈ F.M.D.model := by
    rw [LangDatum.mem_model]
    refine ⟨canonicalRep_mem_adjointGroup (coxeterSystem (langTag t)) GGL u, ?_⟩
    rw [F.M.hn, F.M.hΦ]
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [ggG5_phi_canonicalRep_untw (Or.inl rfl) f u,
        g5_canonicalRep_conj_charTwo, g5_weyl_conj_untw F u hu (fun y => rfl)]
    · rw [ggG5_phi_canonicalRep_untw (Or.inr (Or.inl rfl)) f u,
        g5_canonicalRep_conj_charTwo, g5_weyl_conj_untw F u hu (fun y => rfl)]
    · rw [ggG5_phi_canonicalRep_untw (Or.inr (Or.inr (Or.inl rfl))) f u,
        g5_canonicalRep_conj_charTwo, g5_weyl_conj_untw F u hu (fun y => rfl)]
    · rw [ggG5_phi_canonicalRep_untw (Or.inr (Or.inr (Or.inr rfl))) f u,
        g5_canonicalRep_conj_charTwo, g5_weyl_conj_untw F u hu (fun y => rfl)]
    · let b : WeylGroup (langTag .twistedE6) := weylTwist TwistTag.E6 u
      have hphi : ggPhi .twistedE6 f (canonicalRep (coxeterSystem (langTag .twistedE6)) GGL u) =
          canonicalRep (coxeterSystem (langTag .twistedE6)) GGL b := by
        change twistHom TwistTag.E6 GGL (ggFrobT f)
            (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL (show WeylGroup TwistTag.E6.tag from u)) =
          canonicalRep (coxeterSystem TwistTag.E6.tag) GGL b
        exact twistHom_canonicalRep TwistTag.E6 GGL (ggFrobT f)
          (show WeylGroup TwistTag.E6.tag from u)
      have hweyl : F.M.w * b * F.M.w⁻¹ = u :=
        g5_weyl_conj_tw F u hu
      rw [hphi, g5_canonicalRep_conj_charTwo F.M.w b, hweyl]
  rw [show ggG5_Y F u =
      (MulAut.conj F.M.D.g0) (canonicalRep (coxeterSystem (langTag t)) GGL u) by
    unfold ggG5_Y
    rw [MulAut.conj_apply]]
  rw [← LangDatum.map_conj_model]
  exact Subgroup.mem_map_of_mem _ hmodel

theorem ggG5_commPi_reflection
    {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t)
    {α : Fin (langTag t).rank → ℤ} (hα : IsRoot (langTag t) α)
    (hfix : permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) α = α) :
    GGCommPi t p f ht (rootReflection α) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · unfold GGCommPi
    rw [piB_F4]
    change ∀ v : Fin (langTag .F4).rank → ℤ, rootReflection α • v = rootReflection α • v
    intro v
    rfl
  · unfold GGCommPi
    by_cases hdvd : p ∣ 2 ^ f - 1
    · rw [piB_E6_of_dvd f hdvd]
      change ∀ v : Fin (langTag .E6).rank → ℤ, rootReflection α • v = rootReflection α • v
      intro v
      rfl
    · rw [piB_E6_of_not_dvd f hdvd] at hfix ⊢
      change ∀ v : Fin (langTag .E6).rank → ℤ,
          rootReflection α • permLattice (τ := langTag .E6) (TwistTag.perm .E6) v =
            permLattice (τ := langTag .E6) (TwistTag.perm .E6) (rootReflection α • v)
      change permLattice (τ := langTag .E6) (TwistTag.perm .E6) α = α at hfix
      intro v
      rw [rootReflection_smul hα, rootReflection_smul hα]
      rw [show permLattice (τ := langTag .E6) (TwistTag.perm .E6) (v - corootPair α v • α) =
          permLattice (τ := langTag .E6) (TwistTag.perm .E6) v -
            corootPair α v • permLattice (τ := langTag .E6) (TwistTag.perm .E6) α from
        g5_permLattice_sub_smul (τ := langTag .E6) (TwistTag.perm .E6) v (corootPair α v) α,
        hfix]
      have h1 : iform (permLattice (τ := langTag .E6) (TwistTag.perm .E6) α)
          (permLattice (τ := langTag .E6) (TwistTag.perm .E6) v) = iform α v :=
        iform_permLattice_E6 α v
      rw [hfix] at h1
      have hcoroot : corootPair α (permLattice (τ := langTag .E6) (TwistTag.perm .E6) v) =
          corootPair α v := by
        rw [corootPair, corootPair, h1]
      rw [hcoroot]
  · unfold GGCommPi
    rw [piB_E7]
    change ∀ v : Fin (langTag .E7).rank → ℤ, rootReflection α • v = rootReflection α • v
    intro v
    rfl
  · unfold GGCommPi
    rw [piB_E8]
    change ∀ v : Fin (langTag .E8).rank → ℤ, rootReflection α • v = rootReflection α • v
    intro v
    rfl
  · unfold GGCommPi
    by_cases hdvd : p ∣ 2 ^ f + 1
    · rw [piB_twistedE6_of_dvd f hdvd]
      change ∀ v : Fin (langTag .twistedE6).rank → ℤ, rootReflection α • v = rootReflection α • v
      intro v
      rfl
    · rw [piB_twistedE6_of_not_dvd f hdvd] at hfix ⊢
      change ∀ v : Fin (langTag .twistedE6).rank → ℤ,
          rootReflection α • permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) v =
            permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) (rootReflection α • v)
      change permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) α = α at hfix
      intro v
      rw [rootReflection_smul hα, rootReflection_smul hα]
      rw [show permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) (v - corootPair α v • α) =
          permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) v -
            corootPair α v • permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) α from
        g5_permLattice_sub_smul (τ := langTag .twistedE6) (TwistTag.perm .E6) v (corootPair α v) α,
        hfix]
      have h1 : iform (permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) α)
          (permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) v) = iform α v :=
        iform_permLattice_E6 α v
      rw [hfix] at h1
      have hcoroot : corootPair α (permLattice (τ := langTag .twistedE6) (TwistTag.perm .E6) v) =
          corootPair α v := by
        rw [corootPair, corootPair, h1]
      rw [hcoroot]

theorem ggG5_commPi_iff_weylTwist_E6
    {p f : ℕ} (ht : GGExcFive .E6) (h : ¬ p ∣ 2 ^ f - 1)
    (u : WeylGroup (langTag .E6)) :
    GGCommPi .E6 p f ht u ↔ weylTwist TwistTag.E6 u = u := by
  unfold GGCommPi
  rw [piB_E6_of_not_dvd f h]
  let u' : WeylGroup TwistTag.E6.tag := u
  change (∀ v : Fin TwistTag.E6.tag.rank → ℤ,
      u' • permLattice (TwistTag.perm .E6) v =
        permLattice (TwistTag.perm .E6) (u' • v)) ↔
    weylTwist TwistTag.E6 u' = u'
  rw [← mem_relWeylTwist_iff_smul, mem_relWeylTwist]

theorem ggG5_commPi_iff_weylTwist_twistedE6
    {p f : ℕ} (ht : GGExcFive .twistedE6)
    (h : ¬ p ∣ 2 ^ f + 1) (u : WeylGroup (langTag .twistedE6)) :
    GGCommPi .twistedE6 p f ht u ↔ weylTwist TwistTag.E6 u = u := by
  unfold GGCommPi
  rw [piB_twistedE6_of_not_dvd f h]
  let u' : WeylGroup TwistTag.E6.tag := u
  change (∀ v : Fin TwistTag.E6.tag.rank → ℤ,
      u' • permLattice (TwistTag.perm .E6) v =
        permLattice (TwistTag.perm .E6) (u' • v)) ↔
    weylTwist TwistTag.E6 u' = u'
  rw [← mem_relWeylTwist_iff_smul, mem_relWeylTwist]

theorem ggG5_w_eq_one_of_eps
    {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t) (hp : p.Prime)
    (hp2 : p ≠ 2) (heps : eps p f = 1) {w : WeylGroup (langTag t)} (hw : GGWeylLaw t p f ht w) :
    w = 1 := by
  have hdvd : p ∣ 2 ^ f - 1 := (eps_eq_one_iff p f).1 heps
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin (langTag .F4).rank → ℤ)
    intro x
    rw [one_smul]
    have h := hw x
    rw [heps, one_smul, piB_F4, g5_permLattice_permCongr_one] at h
    simpa [ggGraphLat] using h
  · apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin (langTag .E6).rank → ℤ)
    intro x
    rw [one_smul]
    have h := hw x
    rw [piB_E6_of_dvd f hdvd, heps, one_smul, g5_permLattice_permCongr_one] at h
    simpa [ggGraphLat] using h
  · apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin (langTag .E7).rank → ℤ)
    intro x
    rw [one_smul]
    have h := hw x
    rw [heps, one_smul, piB_E7, g5_permLattice_permCongr_one] at h
    simpa [ggGraphLat] using h
  · apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin (langTag .E8).rank → ℤ)
    intro x
    rw [one_smul]
    have h := hw x
    rw [heps, one_smul, piB_E8, g5_permLattice_permCongr_one] at h
    simpa [ggGraphLat] using h
  · have hnd : ¬ p ∣ 2 ^ f + 1 := not_dvd_pow_two_add_one_of_dvd hp hp2 f hdvd
    let w' : WeylGroup TwistTag.E6.tag := w
    change w' = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.E6.tag.rank → ℤ)
    intro x
    rw [one_smul]
    have hww : ∀ y : Fin TwistTag.E6.tag.rank → ℤ,
        w' • permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6) y =
          permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6) y := by
      intro y
      have h := hw (show Fin (langTag .twistedE6).rank → ℤ from y)
      rw [piB_twistedE6_of_not_dvd f hnd, heps, one_smul] at h
      exact h
    calc w' • x = w' • permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6)
          (permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6).symm x) := by
          rw [permLattice_permLattice_symm]
      _ = permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6)
          (permLattice (τ := TwistTag.E6.tag) (TwistTag.perm .E6).symm x) := hww _
      _ = x := permLattice_permLattice_symm (TwistTag.perm .E6) x

end YBasic

end CFSG.StandardType.GGFinModel.G5
