module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139CTensor
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139CMov
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139CTrans
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN3MovedContradictionFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.Quasithin.G11 CFSG.ASVolI.ChH

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

local notation "F₄" => GaloisField 2 2
local notation "M₄" => Matrix (Fin 2) (Fin 2) F₄

private theorem w1369_nonempty_mulEquiv_sup_prod {Q : Type*} [Group Q] (A B : Subgroup Q)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥) :
    Nonempty (↥(A ⊔ B) ≃* ↥A × ↥B) := by
  let f : ↥A × ↥B →* Q :=
    MonoidHom.noncommCoprod A.subtype B.subtype (fun a b => hcomm a a.2 b b.2)
  have hfapp : ∀ a : ↥A, ∀ b : ↥B, f (a, b) = (a : Q) * b := fun a b => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    have h' : (a : Q) * b = 1 := by rw [← hfapp]; exact h
    have ha : (a : Q) = (b : Q)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have ha1 : (a : Q) ∈ A ⊓ B := ⟨a.2, by rw [ha]; exact B.inv_mem b.2⟩
    rw [hdisj, Subgroup.mem_bot] at ha1
    have hb1 : (b : Q) = 1 := by rw [ha1, one_mul] at h'; exact h'
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have hrange : f.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [hfapp]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)
    · refine sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), by simp [hfapp]⟩)
        (fun b hb => ⟨(1, ⟨b, hb⟩), by simp [hfapp]⟩)
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

private theorem w1369_inf_eq_bot_of_commute_of_center {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hZ : Subgroup.center ↥A = ⊥) :
    A ⊓ B = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hzA, hzB⟩ := hz
  have hzc : (⟨z, hzA⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hcomm a a.2 z hzB)
  have h1 : (⟨z, hzA⟩ : ↥A) = 1 := by
    have hmem : (⟨z, hzA⟩ : ↥A) ∈ (⊥ : Subgroup ↥A) := by
      rw [← hZ]
      exact hzc
    exact Subgroup.mem_bot.mp hmem
  exact Subtype.ext_iff.mp h1

private theorem w1369_commSub_invariant_of_normalizes {V : Type*} [CommGroup V]
    {R : Subgroup (MulAut V)} {g : MulAut V} (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∀ u ∈ commSub ⊤ R, g u ∈ commSub ⊤ R := by
  intro u hu
  rw [commSub] at hu ⊢
  refine Subgroup.closure_induction (p := fun c _ =>
    g c ∈ Subgroup.closure {c | ∃ x ∈ R, ∃ w ∈ (⊤ : Subgroup V), x w * w⁻¹ = c})
    ?_ ?_ ?_ ?_ hu
  · rintro c ⟨r, hr, w, -, rfl⟩
    refine Subgroup.subset_closure ⟨g * r * g⁻¹, hg r hr, g w, Subgroup.mem_top _, ?_⟩
    rw [show (g * r * g⁻¹) (g w) = g (r w) from by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]]
    simp
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (Subgroup.closure _).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (Subgroup.closure _).inv_mem ha

private theorem w1369_commSub_invariant_self {V : Type*} [CommGroup V]
    {R : Subgroup (MulAut V)} : StableUnder R (commSub ⊤ R) :=
  fun r hr => w1369_commSub_invariant_of_normalizes
    (fun s hs => R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr))

theorem w1369_moved_component_contradiction
    {W : Type} [CommGroup W] [Finite W] (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {Y K : Subgroup (MulAut W)} {U A : Subgroup W}
    {d : MulAut W}
    (hK : CFSG.Open.IsComponentOf K G) (hdD : d ∈ D)
    (hY : Y = K ⊔ K.map (MulAut.conj d).toMonoidHom)
    (hOmega : IsOmegaPlus ↥Y 4 2) (hNat : NatTensor Y U ⊥ 2 2) (hU : U = commSub ⊤ Y)
    (hVd : commSub ⊤ (Subgroup.zpowers d) ≤ U)
    (hDfaith : ∀ e ∈ D, (∀ y ∈ Y, e * y = y * e) → e = 1)
    (hDcard : 2 < Nat.card D)
    (hDnorm : ∀ e ∈ D, Y.map (MulAut.conj e).toMonoidHom = Y)
    (haxis : ∀ e ∈ D, e ∉ centSub U → ∀ u ∈ U, e u = u ↔ u ∈ A)
    (huniq : ∀ e ∈ D, e ∉ centSub U → ∀ f ∈ D, f ∉ centSub U →
      (∀ u ∈ U, e u = u ↔ f u = u) → e = f) :
    False := by
  classical
  subst U
  have hYU : ∀ y ∈ Y, ∀ u ∈ commSub ⊤ Y, y u ∈ commSub ⊤ Y := by
    intro y hy u hu
    have hYmap : Y.map (MulAut.conj y).toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy)
    have hUmap : (commSub ⊤ Y).map y.toMonoidHom = commSub ⊤ Y := by
      have h := commSub_conjBy y ⊤ Y
      have hconj : conjBy y Y = Y := by
        simpa [conjBy] using hYmap
      have htop : (⊤ : Subgroup W).map y.toMonoidHom = ⊤ := by
        rw [Subgroup.map_top]
        exact MonoidHom.range_eq_top.mpr y.surjective
      rw [hconj, htop] at h
      exact h.symm
    rw [← hUmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  let D0 : Subgroup (MulAut W) := D ⊓ centSub (commSub ⊤ Y)
  have hD0bot : D0 = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    have heD : e ∈ D := he.1
    have heC : e ∈ centSub (commSub ⊤ Y) := he.2
    rw [Subgroup.mem_bot]
    apply hDfaith e heD
    intro y hy
    have hmem : e * y * e⁻¹ ∈ Y := by
      have hYmap := hDnorm e heD
      rw [← hYmap]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have heinvC : e⁻¹ ∈ centSub (commSub ⊤ Y) := Subgroup.inv_mem _ heC
    have hzact : ∀ u ∈ commSub ⊤ Y, (e * y * e⁻¹) (y⁻¹ u) = u := by
      intro u hu
      have hyu : y⁻¹ u ∈ commSub ⊤ Y := hYU y⁻¹ (Y.inv_mem hy) u hu
      show e (y (e⁻¹ (y⁻¹ u))) = u
      rw [mem_centSub.mp heinvC (y⁻¹ u) hyu, MulAut.apply_inv_self]
      exact mem_centSub.mp heC u hu
    have h1 : (e * y * e⁻¹) * y⁻¹ = 1 := by
      apply eq_one_of_fix_of_natTensor hNat (Y.mul_mem hmem (Y.inv_mem hy))
      intro u hu
      show (e * y * e⁻¹) (y⁻¹ u) = u
      exact hzact u hu
    have hz : e * y * e⁻¹ = y := mul_inv_eq_one.mp h1
    calc e * y = (e * y * e⁻¹) * e := by group
      _ = y * e := by rw [hz]
  have hDuniq : ∀ e ∈ D, e ∉ centSub (commSub ⊤ Y) →
      ∀ f ∈ D, f ∉ centSub (commSub ⊤ Y) → e = f := by
    intro e heD henot f hfD hfnot
    exact huniq e heD henot f hfD hfnot fun u hu => by
      rw [haxis e heD henot u hu, haxis f hfD hfnot u hu]
  have hDcard_le_two : Nat.card D ≤ 2 := by
    by_cases hne : ∃ e ∈ D, e ∉ centSub (commSub ⊤ Y)
    · obtain ⟨e0, he0D, he0not⟩ := hne
      have hinj : Function.Injective
          (fun x : D => if (x : MulAut W) = 1 then (0 : Fin 2) else 1) := by
        intro x y hxy
        by_cases hx : (x : MulAut W) = 1
        · by_cases hy : (y : MulAut W) = 1
          · exact Subtype.ext (hx.trans hy.symm)
          · simp [hx, hy] at hxy
        · by_cases hy : (y : MulAut W) = 1
          · simp [hx, hy] at hxy
          · have hxnot : (x : MulAut W) ∉ centSub (commSub ⊤ Y) := by
              intro hxc
              have hxD0 : (x : MulAut W) ∈ D0 := ⟨x.2, hxc⟩
              rw [hD0bot] at hxD0
              exact hx (Subgroup.mem_bot.mp hxD0)
            have hynot : (y : MulAut W) ∉ centSub (commSub ⊤ Y) := by
              intro hyc
              have hyD0 : (y : MulAut W) ∈ D0 := ⟨y.2, hyc⟩
              rw [hD0bot] at hyD0
              exact hy (Subgroup.mem_bot.mp hyD0)
            have hxe := hDuniq (x : MulAut W) x.2 hxnot e0 he0D he0not
            have hye := hDuniq (y : MulAut W) y.2 hynot e0 he0D he0not
            exact Subtype.ext (hxe.trans hye.symm)
      have := Nat.card_le_card_of_injective
        (f := fun x : D => if (x : MulAut W) = 1 then (0 : Fin 2) else 1) hinj
      simpa using this
    · have hDle : D ≤ centSub (commSub ⊤ Y) := by
        intro e he
        by_contra hcon
        exact hne ⟨e, he, hcon⟩
      have hDbot : D = ⊥ := by
        rw [eq_bot_iff]
        intro e he
        have heD0 : e ∈ D0 := ⟨he, hDle he⟩
        rw [hD0bot] at heD0
        exact Subgroup.mem_bot.mp heD0
      rw [hDbot]
      simp
  omega

theorem w1369_moved_component_contradiction_of_axis
    {W : Type} [CommGroup W] [Finite W] (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {Y K : Subgroup (MulAut W)} {U A : Subgroup W}
    {d : MulAut W}
    (hK : CFSG.Open.IsComponentOf K G) (hdD : d ∈ D)
    (hY : Y = K ⊔ K.map (MulAut.conj d).toMonoidHom)
    (hOmega : IsOmegaPlus ↥Y 4 2) (hNat : NatTensor Y U ⊥ 2 2) (hU : U = commSub ⊤ Y)
    (hVd : commSub ⊤ (Subgroup.zpowers d) ≤ U)
    (hDfaith : ∀ e ∈ D, (∀ y ∈ Y, e * y = y * e) → e = 1)
    (hDcard : 2 < Nat.card D)
    (hDnorm : ∀ e ∈ D, Y.map (MulAut.conj e).toMonoidHom = Y)
    (haxis : ∀ e ∈ D, e ∉ centSub U → ∀ u ∈ U, e u = u ↔ u ∈ A)
    [Module (ZMod 2) (Additive ↥U)]
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U)
    (hDU : ∀ e ∈ D, ∀ u ∈ U, e u ∈ U)
    (hD0 : D ⊓ centSub U = ⊥)
    (H : Subgroup (GLV (Additive ↥U)))
    (hHY : H = (restrictActionHom hYU).range)
    (φ : ↥H ≃* ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄))
    (ψ : Additive ↥U ≃ₗ[ZMod 2] M₄)
    (hψ : ∀ (h : ↥H) (v : Additive ↥U),
      ψ ((h : GLV (Additive ↥U)) v) =
        (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ v *
          ((((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ)
    (Hax : Submodule F₄ M₄)
    (hT : ∀ e (he : e ∈ D), e ∉ centSub U →
      IsFTransvectionOn F₄ M₄
          (transportedAutHom ψ (restrictLinearOf e (hDU e he))) ∧
        fixVSub (F := F₄) (M := M₄)
          (transportedAutHom ψ (restrictLinearOf e (hDU e he))) = Hax) :
    False := by
  refine w1369_moved_component_contradiction (X := X) hw2 hK hdD hY hOmega hNat hU hVd hDfaith
    hDcard hDnorm haxis ?_
  exact huniq_of_axisOfTensorModel hYU hHY hψ D hD0 hDnorm hDU Hax hT

theorem w1369_moved_component_contradiction_of_transvections
    {W : Type} [CommGroup W] [Finite W] (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {Y K : Subgroup (MulAut W)} {U A : Subgroup W}
    {d : MulAut W}
    (hK : CFSG.Open.IsComponentOf K G) (hdD : d ∈ D)
    (hY : Y = K ⊔ K.map (MulAut.conj d).toMonoidHom)
    (hOmega : IsOmegaPlus ↥Y 4 2) (hNat : NatTensor Y U ⊥ 2 2) (hU : U = commSub ⊤ Y)
    (hVd : commSub ⊤ (Subgroup.zpowers d) ≤ U)
    (hDfaith : ∀ e ∈ D, (∀ y ∈ Y, e * y = y * e) → e = 1)
    (hDcard : 2 < Nat.card D)
    (hDnorm : ∀ e ∈ D, Y.map (MulAut.conj e).toMonoidHom = Y)
    (haxis : ∀ e ∈ D, e ∉ centSub U → ∀ u ∈ U, e u = u ↔ u ∈ A)
    [Module (ZMod 2) (Additive ↥U)]
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U)
    (hDU : ∀ e ∈ D, ∀ u ∈ U, e u ∈ U)
    (hD0 : D ⊓ centSub U = ⊥)
    (H : Subgroup (GLV (Additive ↥U)))
    (hHY : H = (restrictActionHom hYU).range)
    (φ : ↥H ≃* ↥(StatedSL 2 F₄) × ↥(StatedSL 2 F₄))
    (ψ : Additive ↥U ≃ₗ[ZMod 2] M₄)
    (hψ : ∀ (h : ↥H) (v : Additive ↥U),
      ψ ((h : GLV (Additive ↥U)) v) =
        (((φ h).1 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄) * ψ v *
          ((((φ h).2 : Matrix.GeneralLinearGroup (Fin 2) F₄) : M₄))ᵀ)
    (hT : ∀ e (he : e ∈ D), e ∉ centSub U →
      IsFTransvectionOn F₄ M₄
        (transportedAutHom ψ (restrictLinearOf e (hDU e he)))) :
    False := by
  classical
  by_cases hne : ∃ e ∈ D, e ∉ centSub U
  · obtain ⟨e0, he0D, he0not⟩ := hne
    refine w1369_moved_component_contradiction_of_axis (X := X) hw2 hK hdD hY hOmega hNat
      hU hVd hDfaith hDcard hDnorm haxis hYU hDU hD0 H hHY φ ψ hψ
      (fixVSub (F := F₄) (M := M₄)
        (transportedAutHom ψ (restrictLinearOf e0 (hDU e0 he0D)))) ?_
    intro e he henot
    refine ⟨hT e he henot, ?_⟩
    ext m
    rw [mem_fixVSub_transportedAutHom_restrictLinearOf_iff (hDU e he) ψ (hT e he henot)
        (haxis e he henot) m,
      mem_fixVSub_transportedAutHom_restrictLinearOf_iff (hDU e0 he0D) ψ (hT e0 he0D he0not)
        (haxis e0 he0D he0not) m]
  · refine w1369_moved_component_contradiction_of_axis (X := X) hw2 hK hdD hY hOmega hNat
      hU hVd hDfaith hDcard hDnorm haxis hYU hDU hD0 H hHY φ ψ hψ ⊥ ?_
    intro e he henot
    exact absurd ⟨e, he, henot⟩ hne

theorem Std139.lemmaC (h134 : W4Lem13_4) (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    (hn : 3 ≤ n) : DNormComp G D := by
  intro K hK d hd
  by_contra hKd
  have hd1 : d ≠ 1 := by
    intro h1
    apply hKd
    have hconj : MulAut.conj d = 1 := by rw [h1, map_one]
    have hmap : (MulAut.conj d).toMonoidHom = MonoidHom.id (MulAut W) := by
      rw [hconj]
      ext x
      rfl
    rw [hmap, Subgroup.map_id]
  have hC134 : Conc4_134 G K d :=
    Std139.conc134_of_moved h134 hw2 S hK hd hd1 hKd
  obtain ⟨hL2, hNat⟩ := Std139.selection hw2 S hK hd hd1 hKd hC134
  let Kd : Subgroup (MulAut W) := K.map (MulAut.conj d).toMonoidHom
  have hKdcomp : IsComponentOf Kd G :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (S.DG hd)
  have hne : K ≠ Kd := by
    intro h
    exact hKd h.symm
  have hcomm_el : ∀ a ∈ K, ∀ b ∈ Kd, a * b = b * a :=
    fun a ha b hb =>
      CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hKdcomp hne ha hb
  haveI hperf : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  have hStated : StatedClassicalModel ↥K .PSL 2 2 2 :=
    LieModel.statedClassicalModel hL2 (by decide)
  have hZ : Subgroup.center ↥K = ⊥ :=
    CFSG.RankThree.PartOne.center_eq_bot_of_cover (J := ↥K) inferInstance
      (MonoidHom.id ↥K) Function.surjective_id hStated
  have hdisj : K ⊓ Kd = ⊥ :=
    w1369_inf_eq_bot_of_commute_of_center (A := K) (B := Kd) hcomm_el hZ
  have hL2d : IsL2 ↥Kd 2 :=
    LieModel.of_mulEquiv (K.equivMapOfInjective (MulAut.conj d).toMonoidHom
      (MulAut.conj d).injective) hL2
  have hprod : Nonempty (↥(swapPair K d) ≃* ↥K × ↥Kd) :=
    w1369_nonempty_mulEquiv_sup_prod K Kd hcomm_el hdisj
  have hL2sq : IsL2Square ↥(swapPair K d) 2 :=
    ⟨↥K, ↥Kd, inferInstance, inferInstance, hprod, hL2, hL2d⟩
  have hOmega : IsOmegaPlus ↥(swapPair K d) 4 2 :=
    isOmegaPlus_of_isL2Square (by norm_num) hL2sq
  have hVd : commSub ⊤ (Subgroup.zpowers d) ≤ commSub ⊤ (swapPair K d) :=
    Std139.moved_comm_le hw2 S hK hd hd1 hKd
  have hDfaith : ∀ e ∈ D, (∀ y ∈ swapPair K d, e * y = y * e) → e = 1 :=
    Std139.moved_faithful hw2 S hK hd hd1 hKd hC134
  have hDnorm : ∀ e ∈ D, (swapPair K d).map (MulAut.conj e).toMonoidHom = swapPair K d :=
    Std139.moved_normalized hw2 S hK hd hd1 hKd hC134
  have haxis : ∀ e ∈ D, e ∉ centSub (commSub ⊤ (swapPair K d)) →
      ∀ u ∈ commSub ⊤ (swapPair K d),
        e u = u ↔ u ∈ commSub ⊤ (swapPair K d) ⊓ Y :=
    Std139.moved_axis hw2 S hK hd hd1 hKd hC134
  have hD0 : D ⊓ centSub (commSub ⊤ (swapPair K d)) = ⊥ :=
    Std139.moved_D0 hw2 S hK hd hd1 hKd hC134
  have hDcard : 2 < Nat.card D := by
    rw [S.Dcard]
    calc 2 < 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hYU : ∀ y ∈ swapPair K d, ∀ u ∈ commSub ⊤ (swapPair K d),
      y u ∈ commSub ⊤ (swapPair K d) :=
    w1369_commSub_invariant_self
  have hDU : ∀ e ∈ D, ∀ u ∈ commSub ⊤ (swapPair K d),
      e u ∈ commSub ⊤ (swapPair K d) := by
    intro e he
    exact w1369_commSub_invariant_of_normalizes (R := swapPair K d) (g := e) (by
      intro r hr
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hr
      rw [hDnorm e he] at hmem
      simpa [MulAut.conj_apply] using hmem)
  letI : Module (ZMod 2) (Additive ↥(commSub ⊤ (swapPair K d))) :=
    moduleAdditiveSubgroup (commSub ⊤ (swapPair K d)) (fun u _ => hw2 u)
  obtain ⟨H, φ, ψ, hHY, hψ⟩ :=
    exists_tensorCoord_four_of_natTensor (W := W) hw2 (Y := swapPair K d)
      (U := commSub ⊤ (swapPair K d)) hNat hYU
  have hT : ∀ e (he : e ∈ D), e ∉ centSub (commSub ⊤ (swapPair K d)) →
      IsFTransvectionOn F₄ M₄ (transportedAutHom ψ (restrictLinearOf e (hDU e he))) :=
    Std139.moved_transvection hw2 S hK hd hd1 hKd hC134 hYU hDU H hHY φ ψ hψ
  exact w1369_moved_component_contradiction_of_transvections (W := W) (X := X) (Y := swapPair K d)
    (K := K) (U := commSub ⊤ (swapPair K d)) (A := commSub ⊤ (swapPair K d) ⊓ Y) (d := d)
    hw2 hK hd rfl hOmega hNat rfl hVd hDfaith hDcard hDnorm haxis hYU hDU hD0 H hHY φ ψ hψ hT

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139