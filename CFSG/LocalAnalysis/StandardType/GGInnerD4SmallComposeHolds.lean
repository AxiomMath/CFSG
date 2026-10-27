module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallCompose
public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallBound

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrsm1_not_ggLabelIso_of_d4_typeA {labJ labC : LargeEvenLabel}
    (htagJ : labJ.tag = .D) (hrkJ : labJ.rank = 4) (hTypeA : S2MathAs51600.TypeALabel labC) :
    ¬ GGLabelIso labJ labC := by
  intro hIso
  unfold S2MathAs51600.TypeALabel at hTypeA
  unfold GGLabelIso at hIso
  rcases hIso with heq | hBC | hD3 | hA3 | htwD3 | htwA3 | htwD2 | hA1
  · rw [← heq] at hTypeA
    rcases hTypeA with hA | hA <;> rw [htagJ] at hA <;> cases hA
  · obtain ⟨hBC, -⟩ := hBC
    rcases hBC with hB | hC
    · rw [htagJ] at hB; cases hB
    · rw [htagJ] at hC; cases hC
  · obtain ⟨h1, -⟩ := hD3
    have h3 : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    omega
  · obtain ⟨h1, -⟩ := hA3
    have hA : labJ.tag = .A := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA
  · obtain ⟨h1, -⟩ := htwD3
    have h3 : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    omega
  · obtain ⟨h1, -⟩ := htwA3
    have hA : labJ.tag = .twA := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA
  · obtain ⟨h1, -⟩ := htwD2
    have h2 : labJ.rank = 2 := congrArg LargeEvenLabel.rank h1
    omega
  · obtain ⟨-, h1⟩ := hA1
    have hA : labJ.tag = .A := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA

private theorem ltrsm1_not_ggLabelIso_of_d4_small {labJ lab : LargeEvenLabel}
    (htagJ : labJ.tag = .D) (hrkJ : labJ.rank = 4)
    (hSmall : S2MathAs51600Small.SmallRegime lab) :
    ¬ GGLabelIso labJ lab := by
  intro hIso
  unfold S2MathAs51600Small.SmallRegime at hSmall
  unfold GGLabelIso at hIso
  rcases hIso with heq | hBC | hD3 | hA3 | htwD3 | htwA3 | htwD2 | hA1
  · have htag : lab.tag = .D := by rw [← heq]; exact htagJ
    rcases hSmall with h | h | h | h | h | h | h <;> rw [htag] at h <;> cases h
  · obtain ⟨hBC, -⟩ := hBC
    rcases hBC with hB | hC
    · rw [htagJ] at hB; cases hB
    · rw [htagJ] at hC; cases hC
  · obtain ⟨h1, -⟩ := hD3
    have h3 : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    omega
  · obtain ⟨h1, -⟩ := hA3
    have hA : labJ.tag = .A := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA
  · obtain ⟨h1, -⟩ := htwD3
    have h3 : labJ.rank = 3 := congrArg LargeEvenLabel.rank h1
    omega
  · obtain ⟨h1, -⟩ := htwA3
    have hA : labJ.tag = .twA := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA
  · obtain ⟨h1, -⟩ := htwD2
    have h2 : labJ.rank = 2 := congrArg LargeEvenLabel.rank h1
    omega
  · obtain ⟨-, h1⟩ := hA1
    have hA : labJ.tag = .A := congrArg LargeEvenLabel.tag h1
    rw [htagJ] at hA; cases hA

private theorem ltrsm1_typeA_of_tableComponentLabel {lab out : LargeEvenLabel}
    (h : S2MathAs51600Small.TableComponentLabel lab out) : S2MathAs51600.TypeALabel out := by
  unfold S2MathAs51600Small.TableComponentLabel at h
  unfold S2MathAs51600.TypeALabel
  rcases h with ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]; unfold S2MathAs51600Small.A2Label; split_ifs <;> simp
  · rw [h]; exact Or.inl rfl
  · rw [h.2]; unfold S2MathAs51600Small.A2Label; split_ifs <;> simp
  · rw [h]; exact Or.inr rfl

private theorem ltrsm1_hasLabel_of_iso {lab : LargeEvenLabel} {G H : Type} [Group G] [Group H]
    (h : GGHasLabel lab G) (e : G ≃* H) : GGHasLabel lab H := by
  unfold GGHasLabel at h ⊢
  refine largeEvenRawDatum_mono ?_ h
  rintro R _ I F ⟨e'⟩
  exact ⟨e.symm.trans e'⟩

private theorem ltrsm1_center_eq_bot {R : Type*} [Group R]
    (hsimple : IsSimpleGroup R) (hnonab : ∃ a b : R, a * b ≠ b * a) :
    Subgroup.center R = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · exfalso
    have hab : ∀ a b : R, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    obtain ⟨a, b, hab'⟩ := hnonab
    exact hab' (hab a b)

private theorem ltrsm1_ne_bot_of_isQuasisimple {G : Type*} [Group G] {K : Subgroup G}
    (h : Assembly.IsQuasisimple ↥K) : K ≠ ⊥ := by
  intro hK
  haveI : Nontrivial (↥K ⧸ Subgroup.center ↥K) := h.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have ha : a = 1 := Subtype.ext (by simpa [hK] using a.2)
  have hb : b = 1 := Subtype.ext (by simpa [hK] using b.2)
  rw [ha, hb]

theorem smallComposition_holds : S2MathAs51600SmallCompose.SmallComposition := by
  unfold S2MathAs51600SmallCompose.SmallComposition
  intro hTable hActors hSuz hDer hD4 hRig hTr
  unfold S2MathAs51600Small.SmallVacuity
  intro X _ _ A σ J hA hσ hJ hN hmark labJ hΛ htag hrk hlab
  obtain ⟨hXperf, lab, hlabMark, hraw⟩ := hmark
  obtain ⟨R, _, I, F, hRsimple, hRnonab, θ, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hSmall, hInnA⟩ := hP
  haveI : Finite R := by
    haveI : Finite (X ⧸ Subgroup.center X) := inferInstance
    exact Finite.of_surjective θ θ.surjective
  have hcenterR : Subgroup.center R = ⊥ := ltrsm1_center_eq_bot hRsimple hRnonab
  let π : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  let β : MulAut R := ggInducedAut θ σ
  let Jb : Subgroup R := J.map π
  have hsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hker : π.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : QuotientGroup.mk' (Subgroup.center X) x = 1 :=
      θ.injective (by simpa [π, MonoidHom.comp_apply] using hx)
    have hm : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := MonoidHom.mem_ker.2 hx'
    rwa [QuotientGroup.ker_mk'] at hm
  have heq : ∀ x : X, π (σ x) = β (π x) :=
    fun x => by simp [π, β, MonoidHom.comp_apply, ggInducedAut_apply]
  obtain ⟨hJbcomp, hiso⟩ := hTr π hsurj hker σ β heq J hJ

  have hidentity : β = 1 → False := by
    intro hβ1
    have hfix : ggAutFixedSubgroup β = ⊤ := by
      rw [hβ1]
      ext x
      simp [ggAutFixedSubgroup]
    have hJbsub : Assembly.IsSubnormal Jb ⊤ := by
      have h := hJbcomp.2.1
      rwa [hfix] at h
    have hJbTop : Jb = ⊤ := by
      rcases Assembly.IsSubnormal.eq_bot_or_top hJbsub with h | h
      · exact absurd h (ltrsm1_ne_bot_of_isQuasisimple hJbcomp.2.2)
      · exact h
    have hcenterTop : Subgroup.center (↥(⊤ : Subgroup R)) = ⊥ := by
      ext x
      constructor
      · intro hx
        have hx' : (x : R) ∈ Subgroup.center R := by
          rw [Subgroup.mem_center_iff]
          intro r
          exact congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hx ⟨r, Subgroup.mem_top r⟩)
        rw [hcenterR] at hx'
        exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hx'))
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact Subgroup.mem_center_iff.mpr (fun y => by simp)
    have hisoJbR : Nonempty ((↥Jb ⧸ Subgroup.center ↥Jb) ≃* R) := by
      rw [hJbTop]
      exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenterTop).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)⟩
    obtain ⟨e₁⟩ := hiso
    obtain ⟨e₂⟩ := hisoJbR
    have hhasLabJ_R : GGHasLabel labJ R := ltrsm1_hasLabel_of_iso hlab (e₁.trans e₂)
    have hhasLabR : GGHasLabel lab R := by
      unfold GGHasLabel
      refine largeEvenRawDatum_mono ?_ hraw
      intro R' _ I' F' hQ
      obtain ⟨-, -, θ', -⟩ := hQ
      exact ⟨θ.symm.trans θ'⟩
    exact ltrsm1_not_ggLabelIso_of_d4_small htag hrk hSmall
      (hRig labJ lab R hΛ hlabMark hhasLabJ_R hhasLabR)

  have table_case : S2MathAs51600Small.TableRegime lab → False := by
    intro htableReg
    by_cases hσ1 : σ = 1
    · exact hidentity (by simp [β, hσ1])
    have hrawT := hTable lab hlabMark htableReg _ hraw
    obtain ⟨R2, _, I2, F2, hQ2, hPtable2⟩ := largeEvenRawDatum_exists hrawT
    obtain ⟨hR2simple, hR2nonab, θ2, hP2⟩ := hQ2
    obtain ⟨-, hInnA2⟩ := hP2
    have hPtable := hPtable2 hR2simple hR2nonab
    haveI : Finite R2 := by
      haveI : Finite (X ⧸ Subgroup.center X) := inferInstance
      exact Finite.of_surjective θ2 θ2.surjective
    have hcenterR2 : Subgroup.center R2 = ⊥ := ltrsm1_center_eq_bot hR2simple hR2nonab
    let π2 : X →* R2 := θ2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    let β2 : MulAut R2 := ggInducedAut θ2 σ
    let Jb2 : Subgroup R2 := J.map π2
    have hsurj2 : Function.Surjective π2 :=
      θ2.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
    have hker2 : π2.ker ≤ Subgroup.center X := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : QuotientGroup.mk' (Subgroup.center X) x = 1 :=
        θ2.injective (by simpa [π2, MonoidHom.comp_apply] using hx)
      have hm : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := MonoidHom.mem_ker.2 hx'
      rwa [QuotientGroup.ker_mk'] at hm
    have heq2 : ∀ x : X, π2 (σ x) = β2 (π2 x) :=
      fun x => by simp [π2, β2, MonoidHom.comp_apply, ggInducedAut_apply]
    obtain ⟨hJbcomp2, hiso2⟩ := hTr π2 hsurj2 hker2 σ β2 heq2 J hJ
    have hβ2I : β2 ∈ I2 := hInnA2 σ hσ
    have hβ2pow : β2 ^ 3 = 1 := by
      show ggInducedAut θ2 σ ^ 3 = 1
      simp [← map_pow, hA.2 σ hσ]
    have hβ2ne : β2 ≠ 1 := by
      intro hβ1
      apply hσ1
      exact ggInducedAut_injective_of_perfect hXperf θ2 (by simpa [β2] using hβ1)
    obtain ⟨out, hΛout, hTableComp, hLabOut⟩ :=
      hPtable β2 hβ2I hβ2pow hβ2ne Jb2 hJbcomp2
    obtain ⟨eiso2⟩ := hiso2
    have hLabJ_Jb2 : GGHasLabel labJ (↥Jb2 ⧸ Subgroup.center ↥Jb2) :=
      ltrsm1_hasLabel_of_iso hlab eiso2
    exact ltrsm1_not_ggLabelIso_of_d4_typeA htag hrk
      (ltrsm1_typeA_of_tableComponentLabel hTableComp)
      (hRig labJ out (↥Jb2 ⧸ Subgroup.center ↥Jb2) hΛ hΛout hLabJ_Jb2 hLabOut)

  have suzuki_case : lab.tag = .twB2 → False := by
    intro htwB2
    have hInnerAll := hActors lab hlabMark (Or.inr htwB2)
    have hSuzAll := hSuz lab hlabMark htwB2
    have hBoth := largeEvenLabelAll_and hInnerAll hSuzAll
    have hrawS := hBoth _ hraw
    obtain ⟨R2, _, I2, F2, hQ2, hInnerGuard, hSuzR2⟩ := largeEvenRawDatum_exists hrawS
    obtain ⟨hR2simple, hR2nonab, θ2, hP2⟩ := hQ2
    obtain ⟨-, hInnA2⟩ := hP2
    have hInner := hInnerGuard hR2simple hR2nonab
    haveI : Finite R2 := by
      haveI : Finite (X ⧸ Subgroup.center X) := inferInstance
      exact Finite.of_surjective θ2 θ2.surjective
    have hcenterR2 : Subgroup.center R2 = ⊥ := ltrsm1_center_eq_bot hR2simple hR2nonab
    let π2 : X →* R2 := θ2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    let β2 : MulAut R2 := ggInducedAut θ2 σ
    let Jb2 : Subgroup R2 := J.map π2
    have hsurj2 : Function.Surjective π2 :=
      θ2.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
    have hker2 : π2.ker ≤ Subgroup.center X := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : QuotientGroup.mk' (Subgroup.center X) x = 1 :=
        θ2.injective (by simpa [π2, MonoidHom.comp_apply] using hx)
      have hm : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := MonoidHom.mem_ker.2 hx'
      rwa [QuotientGroup.ker_mk'] at hm
    have heq2 : ∀ x : X, π2 (σ x) = β2 (π2 x) :=
      fun x => by simp [π2, β2, MonoidHom.comp_apply, ggInducedAut_apply]
    obtain ⟨-, _⟩ := hTr π2 hsurj2 hker2 σ β2 heq2 J hJ
    have hβ2I : β2 ∈ I2 := hInnA2 σ hσ
    obtain ⟨r, hr⟩ := hInner β2 hβ2I
    have hβ2pow : β2 ^ 3 = 1 := by
      show ggInducedAut θ2 σ ^ 3 = 1
      simp [← map_pow, hA.2 σ hσ]
    have hconj : MulAut.conj (r ^ 3) = 1 := by
      rw [map_pow, ← hr]
      exact hβ2pow
    have hr3 : r ^ 3 = 1 := by
      have hmem : r ^ 3 ∈ Subgroup.center R2 := by
        rw [Subgroup.mem_center_iff]
        intro x
        have h := congrArg (fun f : MulAut R2 => f x) hconj
        simp only [MulAut.one_apply, MulAut.conj_apply] at h
        calc x * r ^ 3 = (r ^ 3 * x * (r ^ 3)⁻¹) * r ^ 3 := by rw [h]
          _ = r ^ 3 * x := by group
      rw [hcenterR2] at hmem
      exact Subgroup.mem_bot.1 hmem
    have hdvd3 : orderOf r ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hr3
    have hdvdCard : orderOf r ∣ Nat.card R2 := orderOf_dvd_natCard r
    have horder1 : orderOf r = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h3
      · exact h1
      · exfalso
        rw [h3] at hdvdCard
        exact hSuzR2 hdvdCard
    have hr1 : r = 1 := orderOf_eq_one_iff.mp horder1
    have hβ2one : β2 = 1 := by rw [hr, hr1]; simp
    have hσ1 : σ = 1 :=
      ggInducedAut_injective_of_perfect hXperf θ2 (by simpa [β2] using hβ2one)
    exact hidentity (by simp [β, hσ1])

  have derived_case : S2MathAs51600Small.DerivedRegime lab → False := by
    intro hderReg
    have hrawD := hDer lab hlabMark hderReg _ hraw
    obtain ⟨R2, _, I2, F2, hQ2, hPder2⟩ := largeEvenRawDatum_exists hrawD
    obtain ⟨hR2simple, hR2nonab, θ2, hP2⟩ := hQ2
    obtain ⟨-, hInnA2⟩ := hP2
    have hOrder : Nat.card R2 = S2MathAs51600Small.DerivedOrder lab.tag :=
      hPder2 hR2simple hR2nonab
    haveI : Finite R2 := by
      haveI : Finite (X ⧸ Subgroup.center X) := inferInstance
      exact Finite.of_surjective θ2 θ2.surjective
    let π2 : X →* R2 := θ2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
    let β2 : MulAut R2 := ggInducedAut θ2 σ
    have hsurj2 : Function.Surjective π2 :=
      θ2.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
    have hker2 : π2.ker ≤ Subgroup.center X := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : QuotientGroup.mk' (Subgroup.center X) x = 1 :=
        θ2.injective (by simpa [π2, MonoidHom.comp_apply] using hx)
      have hm : x ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := MonoidHom.mem_ker.2 hx'
      rwa [QuotientGroup.ker_mk'] at hm
    have heq2 : ∀ x : X, π2 (σ x) = β2 (π2 x) :=
      fun x => by simp [π2, β2, MonoidHom.comp_apply, ggInducedAut_apply]
    obtain ⟨-, hiso2⟩ := hTr π2 hsurj2 hker2 σ β2 heq2 J hJ
    have hbig : 174182400 ≤ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
      hD4 labJ (↥J ⧸ Subgroup.center ↥J) hΛ htag hrk hlab
    have hR2lt : Nat.card R2 < 174182400 := by
      rw [hOrder]
      rcases hderReg with h | h | h
      · rw [h]; norm_num [S2MathAs51600Small.DerivedOrder]
      · rw [h]; norm_num [S2MathAs51600Small.DerivedOrder]
      · rw [h]; norm_num [S2MathAs51600Small.DerivedOrder]
    exact S2MathAs51600SmallBound.card_bound_contradiction π2 J hiso2 hbig hR2lt

  unfold S2MathAs51600Small.SmallRegime at hSmall
  rcases hSmall with hG2 | htri | htwB2 | htwF4 | hB2der | hG2der | htwF4der
  · exact table_case (Or.inl hG2)
  · exact table_case (Or.inr (Or.inl htri))
  · exact suzuki_case htwB2
  · exact table_case (Or.inr (Or.inr htwF4))
  · exact derived_case (Or.inl hB2der)
  · exact derived_case (Or.inr (Or.inl hG2der))
  · exact derived_case (Or.inr (Or.inr htwF4der))

end CFSG.StandardType.GGInnerD4SmallParts

end
