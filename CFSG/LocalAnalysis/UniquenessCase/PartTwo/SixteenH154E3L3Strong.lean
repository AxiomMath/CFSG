module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoBar2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoComp
public import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_not_isMulCommutative_of_isL3 {Y : Type} [Group Y] [Finite Y]
    (h : IsL3 Y 1) : ¬ IsMulCommutative Y := by
  intro hcomm
  haveI : IsMulCommutative Y := hcomm
  haveI : IsSimpleGroup Y := isSimpleGroup_of_isL3 h
  have hp : (Nat.card Y).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  rw [card_eq_of_isL3 h] at hp
  norm_num at hp

private theorem s16h_e3_bar2_of_calC {M V₀ V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) (hKM : K ≤ M) (hK : CFSG.Open.IsQuasisimple (Bar2 K))
    (hKb : IsL3 ↥(barSub V₀ V hV K) 1) : IsL3 (Bar2 K) 1 := by
  let ψ : ↥K →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (hKM.trans hMs))
  have hrange : ψ.range = barSub V₀ V hV K := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion (hKM.trans hMs) k, k.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hY : IsL3 ↥ψ.range 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (MulEquiv.subgroupCongr hrange.symm) hKb
  exact (s16c7_quot_isL3 hY ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ) hK).1

private theorem s16h_e3_frame_components {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} {U U' : Subgroup W}
    (F : s16h_E3Frame X L L' T U U') (hL : IsL3 ↥L 1) (hLc : IsComponentOf L X)
    (hK : IsL3 ↥(X ⊓ Subgroup.centralizer
      ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) 1) :
    IsComponentOf L' X ∧ IsL3 ↥L' 1 ∧
      IsComponentOf (X ⊓ Subgroup.centralizer
        ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) X ∧
      L ≠ L' ∧ (X ⊓ Subgroup.centralizer
        ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) ≠ L ∧
      (X ⊓ Subgroup.centralizer
        ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))) ≠ L' := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => MulEquiv.ext (congrFun h))
  obtain ⟨t, htT, hL', -⟩ := F.swap
  have htX : t ∈ X := F.t_le htT
  have hXconj : X.map (MulAut.conj t).toMonoidHom = X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact X.mul_mem (X.mul_mem htX hy) (X.inv_mem htX)
    · intro hx
      refine ⟨t⁻¹ * x * t, X.mul_mem (X.mul_mem (X.inv_mem htX) hx) htX, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hL'c : IsComponentOf L' X := by
    have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj t) hLc
    rwa [hXconj, hL'] at h
  have hL'3 : IsL3 ↥L' 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      ((Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective).trans (MulEquiv.subgroupCongr hL')) hL
  let K : Subgroup (MulAut W) :=
    X ⊓ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W))
  have hK' : IsL3 ↥K 1 := hK
  have hKle : K ≤ X := inf_le_left
  have hXnormS : X ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    rcases F.perm x hx with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -⟩
    · rw [show L.map (↑(MulAut.conj x) : MulAut W →* MulAut W) = L from h1,
        show L'.map (↑(MulAut.conj x) : MulAut W →* MulAut W) = L' from h2]
    · rw [show L.map (↑(MulAut.conj x) : MulAut W →* MulAut W) = L' from h1,
        show L'.map (↑(MulAut.conj x) : MulAut W →* MulAut W) = L from h2]
      exact sup_comm _ _
  have hXnormC : X ≤ Subgroup.normalizer
      (Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) :
        Set (MulAut W)) :=
    hXnormS.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup
      (L ⊔ L'))
  have hKnorm : X ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    (le_inf Subgroup.le_normalizer hXnormC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKsub : IsSubnormal K X :=
    A3.subnormal_of_normal hKle ((Subgroup.normal_subgroupOf_iff_le_normalizer hKle).2 hKnorm)
  have hKc : IsComponentOf K X :=
    ⟨hKle, hKsub, s16c7_isQuasisimple_of_isL3 hK'⟩
  have hLL' : L ≠ L' := by
    intro heq
    have hUeq : U = U' :=
      F.u_eq.trans ((congrArg (commSub ⊤) heq).trans F.u'_eq.symm)
    have hUbot : U = ⊥ := by
      have h := F.inf_eq
      rw [← hUeq, inf_idem] at h
      exact h
    have htop : (⊤ : Subgroup W) = ⊥ := by
      have h := F.sup_eq
      rw [← hUeq, sup_idem, hUbot] at h
      exact h.symm
    haveI : Subsingleton W := ⟨fun a b => by
      have ha : a = 1 := Subgroup.mem_bot.1 (htop ▸ Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.1 (htop ▸ Subgroup.mem_top b)
      rw [ha, hb]⟩
    haveI : Subsingleton (MulAut W) :=
      ⟨fun a b => MulEquiv.ext (fun w => Subsingleton.elim (a w) (b w))⟩
    have hLbot : L = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      exact Subsingleton.elim x 1
    have hcard := card_eq_of_isL3 hL
    rw [hLbot, Subgroup.card_bot] at hcard
    omega
  have hK_ne_L : K ≠ L := by
    intro heq
    have hKC : K ≤ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) :=
      inf_le_right
    have hle : L ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
      have h1 : K ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
        hKC.trans (Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx))
      exact heq ▸ h1
    haveI : IsMulCommutative ↥L :=
      ⟨⟨fun a b => Subtype.ext (by
        exact ((Subgroup.mem_centralizer_iff.1 (hle a.2)) (b : MulAut W) b.2).symm)⟩⟩
    exact (s16h_e3_not_isMulCommutative_of_isL3 hL) inferInstance
  have hK_ne_L' : K ≠ L' := by
    intro heq
    have hKC : K ≤ Subgroup.centralizer ((L ⊔ L' : Subgroup (MulAut W)) : Set (MulAut W)) :=
      inf_le_right
    have hle : L' ≤ Subgroup.centralizer (L' : Set (MulAut W)) := by
      have h1 : K ≤ Subgroup.centralizer (L' : Set (MulAut W)) :=
        hKC.trans (Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_right hx))
      exact heq ▸ h1
    haveI : IsMulCommutative ↥L' :=
      ⟨⟨fun a b => Subtype.ext (by
        exact ((Subgroup.mem_centralizer_iff.1 (hle a.2)) (b : MulAut W) b.2).symm)⟩⟩
    exact (s16h_e3_not_isMulCommutative_of_isL3 hL'3) inferInstance
  exact ⟨hL'c, hL'3, hKc, hLL', hK_ne_L, hK_ne_L'⟩

theorem s16h_e3_l3_K_strong (D : Data G) (S : s16h_Std D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hL : IsL3 ↥(lBar V₀ V h.hyp151.isElemAbelian L) 1)
    {L' : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))}
    {U' : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian)}
    (F : s16h_E3Frame (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (lBar V₀ V h.hyp151.isElemAbelian L) L'
      (barSub V₀ V h.hyp151.isElemAbelian D.T) (wTil V₀ V h.hyp151.isElemAbelian L) U')
    (hK : IsL3 ↥(Mbar D.M V₀ V h.hyp151.isElemAbelian ⊓ Subgroup.centralizer
      ((lBar V₀ V h.hyp151.isElemAbelian L ⊔ L' :
        Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))) :
          Set (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)))) 1) :
    IsStronglyPEmbedded 3 D.M ∧ 3 ≤ CFSG.Open.pRank 3 D.M := by
  classical
  haveI : Finite (Vtil V₀ V h.hyp151.isElemAbelian) := inferInstance
  haveI : Finite (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)) := MulEquiv.finite_left
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp16.hyp125.pairFacts.le_normalizer
      h.hyp16.hyp125.pairFacts.le_normalizer₀
  obtain ⟨hL'c, hL'3, hKc, hLL', hKL, hKL'⟩ :=
    s16h_e3_frame_components F hL hcomp hK
  obtain ⟨K₁, hK₁mem, hK₁bar, -⟩ := exists_calC_cover_of_simple_component
    (D := D) (V₀ := V₀) (V := V) (hV := h.hyp151.isElemAbelian) h.hyp16.hyp125 S.h127 S.h119
    hcomp (isSimpleGroup_of_isL3 hL)
  obtain ⟨K₂, hK₂mem, hK₂bar, -⟩ := exists_calC_cover_of_simple_component
    (D := D) (V₀ := V₀) (V := V) (hV := h.hyp151.isElemAbelian) h.hyp16.hyp125 S.h127 S.h119
    hL'c (isSimpleGroup_of_isL3 hL'3)
  obtain ⟨K₃, hK₃mem, hK₃bar, -⟩ := exists_calC_cover_of_simple_component
    (D := D) (V₀ := V₀) (V := V) (hV := h.hyp151.isElemAbelian) h.hyp16.hyp125 S.h127 S.h119
    hKc (isSimpleGroup_of_isL3 hK)
  have hb₁ : IsL3 (Bar2 K₁) 1 :=
    s16h_e3_bar2_of_calC (M := D.M) h.hyp151.isElemAbelian hMs (A3.subnormal_le hK₁mem.1)
      hK₁mem.2.2 (by rw [hK₁bar]; exact hL)
  have hb₂ : IsL3 (Bar2 K₂) 1 :=
    s16h_e3_bar2_of_calC (M := D.M) h.hyp151.isElemAbelian hMs (A3.subnormal_le hK₂mem.1)
      hK₂mem.2.2 (by rw [hK₂bar]; exact hL'3)
  have hb₃ : IsL3 (Bar2 K₃) 1 :=
    s16h_e3_bar2_of_calC (M := D.M) h.hyp151.isElemAbelian hMs (A3.subnormal_le hK₃mem.1)
      hK₃mem.2.2 (by rw [hK₃bar]; exact hK)
  have h12 : K₁ ≠ K₂ := by
    intro heq
    have h : lBar V₀ V h.hyp151.isElemAbelian L = L' := by
      rw [← hK₁bar, heq, hK₂bar]
    exact hLL' h
  have h13 : K₁ ≠ K₃ := by
    intro heq
    have h : (Mbar D.M V₀ V h.hyp151.isElemAbelian ⊓ Subgroup.centralizer
        ((lBar V₀ V h.hyp151.isElemAbelian L ⊔ L' :
          Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))) :
            Set (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)))) =
        lBar V₀ V h.hyp151.isElemAbelian L := by
      rw [← hK₃bar, ← heq, hK₁bar]
    exact hKL h
  have h23 : K₂ ≠ K₃ := by
    intro heq
    have h : (Mbar D.M V₀ V h.hyp151.isElemAbelian ⊓ Subgroup.centralizer
        ((lBar V₀ V h.hyp151.isElemAbelian L ⊔ L' :
          Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))) :
            Set (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)))) = L' := by
      rw [← hK₃bar, ← heq, hK₂bar]
    exact hKL' h
  have h81 : F08.Hyp81 D.M (K₁ ⊔ K₂ ⊔ K₃) :=
    hyp81_of_three hK₁mem hK₂mem hK₃mem h12 h13 h23 hb₁ hb₂ hb₃
  refine ⟨S.h82 (K₁ ⊔ K₂ ⊔ K₃) h81, ?_⟩
  have hle : K₁ ⊔ K₂ ⊔ K₃ ≤ D.M :=
    sup_le (sup_le (A3.subnormal_le hK₁mem.1) (A3.subnormal_le hK₂mem.1))
      (A3.subnormal_le hK₃mem.1)
  have hmono := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num : 1 < 3) hle
  have h2 : 2 < CFSG.Open.pRank 3 (K₁ ⊔ K₂ ⊔ K₃) := by
    have hh := h81
    unfold F08.Hyp81 at hh
    exact hh.2.2.1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
