module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Small
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.NParamMap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

variable {W : Type} [CommGroup W]

section Res

variable {I : Subgroup W} {A : Subgroup (MulAut W)}

@[expose] noncomputable def resTo (hA : A ≤ stabSub I) : ↥A →* ↥(autSub A I) :=
  (MulEquiv.subgroupCongr (B1Red.autSub_eq_range hA).symm).toMonoidHom.comp
    ((resHom I).comp (Subgroup.inclusion hA)).rangeRestrict

theorem resTo_surjective (hA : A ≤ stabSub I) : Function.Surjective (resTo hA) :=
  (MulEquiv.subgroupCongr (B1Red.autSub_eq_range hA).symm).surjective.comp
    (MonoidHom.rangeRestrict_surjective _)

theorem resTo_apply (hA : A ≤ stabSub I) (a : ↥A) (u : ↥I) :
    ((((resTo hA a : ↥(autSub A I)) : MulAut ↥I) u : ↥I) : W) = (a : MulAut W) u :=
  rfl

theorem resTo_eq_one_iff (hA : A ≤ stabSub I) (a : ↥A) :
    resTo hA a = 1 ↔ ∀ u ∈ I, (a : MulAut W) u = u := by
  constructor
  · intro h u hu
    have := congrArg (fun φ : ↥(autSub A I) => (((φ : MulAut ↥I) ⟨u, hu⟩ : ↥I) : W)) h
    simpa [resTo_apply] using this
  · intro h
    apply Subtype.ext
    ext u
    rw [resTo_apply]
    exact h u u.2

end Res

section Induced

variable {I : Subgroup W} {L : Subgroup (MulAut W)}

theorem le_stabSub_of_mem_irrSet (hI : I ∈ irrSet L) : L ≤ stabSub I := by
  have hst : StableUnder L I := hI.2.2.1
  intro l hl
  exact mem_stabSub_of_invariant (fun u hu => hst l hl u hu)
    (fun u hu => hst l⁻¹ (L.inv_mem hl) u hu)

theorem isIrrOn_autSub_of_mem_irrSet (hI : I ∈ irrSet L) (hfix : I ⊓ fixV L = ⊥) :
    IsIrrOn (autSub L I) ⊤ ⊥ := by
  have hLI := le_stabSub_of_mem_irrSet hI
  obtain ⟨-, hlt, -, -, hmax⟩ := hI
  rw [hfix] at hlt hmax
  refine ⟨?_, fun _ _ _ _ => Subgroup.mem_top _, fun φ _ u hu => ?_, fun J hJ _ _ => ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro htop
    refine hlt.ne' (eq_bot_iff.mpr fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥I) ∈ (⊤ : Subgroup ↥I) := Subgroup.mem_top _
    rw [htop, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  ·
    have hJst : StableUnder L (J.map I.subtype) := by
      rintro l hl _ ⟨j, hj, rfl⟩
      refine ⟨(resTo hLI ⟨l, hl⟩ : MulAut ↥I) j, hJ _ (resTo hLI ⟨l, hl⟩).2 j hj, ?_⟩
      rfl
    rcases hmax (J.map I.subtype) hJst bot_le (Subgroup.map_subtype_le J) with h | h
    · left
      rw [eq_bot_iff]
      intro j hj
      have : (j : W) ∈ J.map I.subtype := ⟨j, hj, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    · right
      rw [eq_top_iff]
      intro j _
      have : (j : W) ∈ J.map I.subtype := by
        rw [h]
        exact j.2
      obtain ⟨j', hj', hjj'⟩ := this
      rwa [← Subtype.ext hjj']

theorem not_le_centSub_of_mem_irrSet (hI : I ∈ irrSet L) (hfix : I ⊓ fixV L = ⊥) :
    ¬ L ≤ centSub I := by
  intro hle
  obtain ⟨hcomm, hlt, -⟩ := hI
  rw [hfix] at hlt
  apply hlt.ne'
  rw [← hcomm, commSub_eq_bot_iff]
  intro u hu
  rw [mem_fixV]
  exact fun l hl => mem_centSub.mp (hle hl) u hu

theorem normal_autSub_of_normalizes {Y : Subgroup (MulAut W)}
    (hnormI : ∀ y ∈ Y, y ∈ stabSub I → y ∈ normalizer (L : Set (MulAut W))) :
    ((autSub L I).subgroupOf (autSub Y I)).Normal := by
  refine ⟨fun l hl y => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hl ⊢
  obtain ⟨h, hhL, hh⟩ := mem_autSub.mp hl
  obtain ⟨g, hgY, hg⟩ := mem_autSub.mp y.2
  have hgN := hnormI _ hgY g.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hh, ← hg, ← map_inv,
    ← map_mul, ← map_mul]
  refine mem_autSub.mpr ⟨g * h * g⁻¹, ?_, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hhL

end Induced

section Central

variable [Finite W] {I : Subgroup W} {L : Subgroup (MulAut W)}

omit [Finite W] in
theorem ker_resTo_le_center (hq : CFSG.Open.IsQuasisimple ↥L) (hLI : L ≤ stabSub I)
    (hne : ¬ L ≤ centSub I) : (resTo hLI).ker ≤ Subgroup.center ↥L := by
  have hsub : CFSG.Open.IsSubnormal (resTo hLI).ker ⊤ :=
    CFSG.Open.IsSubnormal.step le_top
      ((Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ =>
        (MonoidHom.normal_ker (resTo hLI)).conj_mem x hx k)
      (CFSG.Open.IsSubnormal.refl ⊤)
  rcases MinDegLow.le_center_or_eq_top_of_isSubnormal (Or.inr hq) hsub with h | h
  · exact h
  · exfalso
    apply hne
    intro l hl
    have hk : (⟨l, hl⟩ : ↥L) ∈ (resTo hLI).ker := h ▸ Subgroup.mem_top _
    exact mem_centSub.mpr ((resTo_eq_one_iff hLI _).mp hk)

omit [Finite W] in
theorem nontrivial_autSub (hLI : L ≤ stabSub I) (hne : ¬ L ≤ centSub I) :
    Nontrivial ↥(autSub L I) := by
  obtain ⟨l, hl, hl'⟩ := Set.not_subset.mp hne
  refine ⟨⟨resTo hLI ⟨l, hl⟩, 1, fun h => hl' ?_⟩⟩
  exact mem_centSub.mpr ((resTo_eq_one_iff hLI _).mp h)

theorem shape14_5_autSub
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hLI : L ≤ stabSub I) (hne : ¬ L ≤ centSub I) {e : ℕ}
    (h : Shape14_5 ↥L e) : Shape14_5 ↥(autSub L I) e := by
  have hs := resTo_surjective hLI
  have hnt := nontrivial_autSub hLI hne
  have hk := ker_resTo_le_center hq hLI hne
  have hc : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ},
      (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus) → LieModel ↥L t m 2 f →
      LieModel ↥(autSub L I) t m 2 f := fun ht h' =>
    lieModel_of_surjective_of_isSimple (uc22p22r_lieModel_isSimple_classical ht h') (resTo hLI)
      hs hnt h'
  rcases h with h | h | h | h | h | h | h | h | h | h | h | ⟨he, h⟩ | h | h | h
  · exact Or.inl (hc (Or.inl rfl) h)
  · exact Or.inr (Or.inl (lieModel_of_surjective_of_isSimple
      (uc22p22r_lieModel_isSimple_twistedB2 h) (resTo hLI) hs hnt h))
  · exact Or.inr (Or.inr (Or.inl (hc (Or.inr (Or.inl rfl)) h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isSU3_of_surjective_central h (resTo hLI) hs hk hnt))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hc (Or.inl rfl) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (isSL3_of_surjective_central h (resTo hLI) hs hk hnt))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hc (Or.inr (Or.inr (Or.inl rfl))) h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hc (Or.inr (Or.inl rfl)) h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (lieModel_of_surjective_of_isSimple (hG2 _ e h) (resTo hLI) hs hnt h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (lieModel_of_surjective_of_isSimple (h3D4 _ e h) (resTo hLI) hs hnt h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (lieModel_of_surjective_of_isSimple (h2F4 _ e h) (resTo hLI) hs hnt h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨he, hc (Or.inr (Or.inl rfl)) h⟩)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl (hc (Or.inl rfl) h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl (hc (Or.inr (Or.inr (Or.inl rfl))) h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (hc (Or.inr (Or.inr (Or.inr rfl))) h))))))))))))))

theorem isParabolicTwo_autSub (hLI : L ≤ stabSub I) {P : Subgroup (MulAut W)} (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) :
    IsParabolicTwo ↥(autSub L I) ((autSub P I).subgroupOf (autSub L I)) := by
  have heq : (P.subgroupOf L).map (resTo hLI) = (autSub P I).subgroupOf (autSub L I) := by
    ext φ
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, mem_autSub]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨(l : MulAut W), hLI l.2⟩, Subgroup.mem_subgroupOf.mp hl, rfl⟩
    · rintro ⟨g, hgP, hg⟩
      refine ⟨⟨g, hPL hgP⟩, Subgroup.mem_subgroupOf.mpr hgP, Subtype.ext ?_⟩
      exact hg
  rw [← heq]
  exact hpar.map (resTo hLI) (resTo_surjective hLI)

theorem hinf_autSub {P : Subgroup (MulAut W)} (hPI : P ≤ stabSub I) :
    Hinf (autSub P I) = autSub (Hinf P) I := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite (MulAut ↥I) :=
    Finite.of_injective (fun f : MulAut ↥I => (f : ↥I → ↥I)) DFunLike.coe_injective
  set f : ↥P →* MulAut ↥I := (resHom I).comp (Subgroup.inclusion hPI) with hf
  have h1 : autSub P I = (⊤ : Subgroup ↥P).map f := by
    rw [B1Red.autSub_eq_range hPI, MonoidHom.range_eq_map]
  have h2 : Hinf (⊤ : Subgroup ↥P) = (Hinf P).subgroupOf P := by
    rw [← Ctx23L.Hinf_subgroupOf_of_le le_rfl, Subgroup.subgroupOf_self]
  rw [h1, ← Hinf_map f, h2]
  ext φ
  rw [Subgroup.mem_map, mem_autSub]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨(x : MulAut W), hPI x.2⟩, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, (uc22p21c_Hinf_le P) hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

end Central

theorem hinf_autSub_ne_bot_and_nParam [Finite W] {I : Subgroup W} {L P : Subgroup (MulAut W)}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hLI : L ≤ stabSub I) (hne : ¬ L ≤ centSub I)
    (hPL : P ≤ L) (hinf : Hinf P ≠ ⊥) {n : ℕ} (hN : NParam (Hinf P) n) :
    Hinf (autSub P I) ≠ ⊥ ∧ NParam (Hinf (autSub P I)) n := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hPI : P ≤ stabSub I := hPL.trans hLI
  have hHI : Hinf P ≤ stabSub I := (uc22p21c_Hinf_le P).trans hPI
  have hinf' : Hinf (autSub P I) ≠ ⊥ := by
    rw [hinf_autSub hPI]
    intro hbot
    apply hinf
    have hcent : ∀ x ∈ Hinf P, ∀ y ∈ Hinf P, x * y = y * x := by
      intro x hx y hy
      have hx1 : resTo hHI ⟨x, hx⟩ = 1 := by
        apply Subtype.ext
        have hmem : ((resTo hHI ⟨x, hx⟩ : ↥(autSub (Hinf P) I)) : MulAut ↥I) ∈
            (⊥ : Subgroup (MulAut ↥I)) := hbot ▸ (resTo hHI ⟨x, hx⟩).2
        exact Subgroup.mem_bot.mp hmem
      have hxL : (⟨x, (uc22p21c_Hinf_le P |>.trans hPL) hx⟩ : ↥L) ∈ (resTo hLI).ker := by
        rw [MonoidHom.mem_ker, resTo_eq_one_iff]
        exact (resTo_eq_one_iff hHI _).mp hx1
      have := Subgroup.mem_center_iff.mp (ker_resTo_le_center hq hLI hne hxL)
        ⟨y, (uc22p21c_Hinf_le P |>.trans hPL) hy⟩
      exact (congrArg Subtype.val this).symm
    rw [← uc22p21c_Hinf_perfect P, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def, hcent x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  refine ⟨hinf', ?_⟩
  let ψ : ↥(Hinf P) →* ↥(Hinf (autSub P I)) :=
    (MulEquiv.subgroupCongr (hinf_autSub hPI).symm).toMonoidHom.comp (resTo hHI)
  have hψ : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr (hinf_autSub hPI).symm).surjective.comp (resTo_surjective hHI)
  have hker : ψ.ker ≤ Subgroup.center ↥(Hinf P) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : resTo hHI x = 1 := by
      have := congrArg (MulEquiv.subgroupCongr (hinf_autSub hPI).symm).symm hx
      simpa [ψ] using this
    have hxL : (⟨x, (uc22p21c_Hinf_le P |>.trans hPL) x.2⟩ : ↥L) ∈ (resTo hLI).ker := by
      rw [MonoidHom.mem_ker, resTo_eq_one_iff]
      exact (resTo_eq_one_iff hHI _).mp hx1
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.mp (ker_resTo_le_center hq hLI hne hxL)
      ⟨y, (uc22p21c_Hinf_le P |>.trans hPL) y.2⟩
    exact Subtype.ext (show (y : MulAut W) * x = x * y from congrArg Subtype.val this)
  exact nParam_of_surjective_central ψ hψ hker (uc22p21c_Hinf_perfect _) hinf' hN

theorem small_of_mem_irrSet (hSmall : K14_5Small)
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L P : Subgroup (MulAut W)} {e n : ℕ}
    (hL : IsComponentOf L Y) (hshape : Shape14_5 ↥L e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n)
    (hn : 2 < n) {I : Subgroup W} (hI : I ∈ irrSet L) (hfix : I ⊓ fixV L = ⊥)
    (hnormI : ∀ y ∈ Y, y ∈ stabSub I → y ∈ normalizer (L : Set (MulAut W)))
    (hm : E3.mParam (autSub Y I) ≤ n + 1) :
    (∃ k : ℕ, IsNaturalClassicalModule (autSub L I) k ∧ (n = k ∨ n = 2 * k)) ∨
      (IsL2 ↥(autSub L I) 3 ∧ n = 3 ∧ E3.mParam (autSub Y I) = 4 ∧
        E3.aParam (autSub Y I) ≤ 1) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLI := le_stabSub_of_mem_irrSet hI
  have hne : ¬ L ≤ centSub I := not_le_centSub_of_mem_irrSet hI hfix
  obtain ⟨hinf', hN'⟩ := hinf_autSub_ne_bot_and_nParam hq hLI hne hPL hinf hN
  have : Finite ↥I := inferInstance
  exact hSmall ↥I (fun w => Subtype.ext (hW w)) (autSub Y I) (autSub L I) (autSub P I) e n
    (autSub_mono hL.1 I) (normal_autSub_of_normalizes hnormI)
    (B1Red.isQuasisimple_autSub hLI hq hne)
    (isIrrOn_autSub_of_mem_irrSet hI hfix) (shape14_5_autSub hG2 h3D4 h2F4 hq hLI hne hshape)
    (autSub_mono hPL I) (isParabolicTwo_autSub hLI hPL hpar) hinf' hN' hn hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
