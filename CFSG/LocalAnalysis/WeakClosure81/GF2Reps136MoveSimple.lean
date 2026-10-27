module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveB2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136LemmaF
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136IrrCorr
public import CFSG.Quasithin.Background.F918V2F
public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsXMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem w1369_center_mulAut_of_sq_eq_one {Q : Type} [CommGroup Q] [Finite Q]
    (hQ : ∀ x : Q, x ^ 2 = 1) (hcard : Nat.card Q = 8) :
    Subgroup.center (MulAut Q) = ⊥ := by
  obtain ⟨e⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one hQ (d := 3) (by rw [hcard]; norm_num)
  let F : MulAut Q ≃* GL (Fin 3) (ZMod 2) :=
    (MulAut.congr e).trans (S153E58.mulAutPiEquivGL 3)
  rw [Subgroup.eq_bot_iff_forall]
  intro φ hφ
  have hFφ : F φ ∈ Subgroup.center (GL (Fin 3) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff] at hφ ⊢
    intro g
    obtain ⟨ψ, rfl⟩ := F.surjective g
    rw [← map_mul, ← map_mul, hφ ψ]
  rw [w1369_center_GL32, Subgroup.mem_bot] at hFφ
  exact F.injective (by rw [hFφ, map_one])

theorem w1369_move_endUnitsTrivial (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    Z391.EndUnitsTrivial (secSub (Wd L) (Cd L) L) (w1369_im (Wd L) (Cd L) I) := by
  obtain ⟨hIle, -, hMW, hIirr0, -⟩ := irr_to_sect hw2 L S.hI
  have hCI : Cd L ≤ I := by rw [(move_C hw2 S).1]; exact inf_le_left
  have hIirr : IsIrrOn L I (Cd L) := by
    have := hIirr0
    rwa [sup_eq_left.mpr hCI] at this
  have htop : secSub I (Cd L) L = ⊤ := (move_gl3 hw2 S).1
  have hcard : Nat.card (Sect I (Cd L)) = 2 ^ 3 := (move_gl3 hw2 S).2
  have hstI : L ≤ stabSub I := s16h_le_stabSub_of_stable hIirr.2.1
  have hstC : L ≤ stabSub (Cd L) := s16h_le_stabSub_of_stable hIirr.2.2.1
  have hWdstab : StableUnder L (Wd L) := by
    intro l hl w hw
    have hgen : l w * w⁻¹ ∈ Wd L :=
      Subgroup.subset_closure ⟨l, hl, w, Subgroup.mem_top w, rfl⟩
    rw [show l w = (l w * w⁻¹) * w by group]
    exact (Wd L).mul_mem hgen hw
  have hfixstab : StableUnder L (fixV L) := by
    intro x hx u hu
    rw [mem_fixV] at hu ⊢
    intro z hz
    calc z (x u) = (z * x) u := rfl
      _ = u := hu (z * x) (L.mul_mem hz hx)
      _ = x u := (hu x hx).symm
  have hCdstab : StableUnder L (Cd L) := by
    intro x hx u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    exact Subgroup.mem_inf.mpr ⟨hWdstab x hx u hu1, hfixstab x hx u hu2⟩
  have hstU : L ≤ stabSub (Wd L) := s16h_le_stabSub_of_stable hWdstab
  have hstabI : StabPair L I (Cd L) := fun a ha => ⟨hIirr.2.1 a ha, hIirr.2.2.1 a ha⟩
  have hstabU : StabPair L (Wd L) (Cd L) := fun a ha => ⟨hWdstab a ha, hCdstab a ha⟩
  have hrange : (s16h_secIncl (Cd L) I (Wd L) hIle).range =
      w1369_im (Wd L) (Cd L) I :=
    s16h_secIncl_range (Cd L) I (Wd L) hIle
  let e : Sect I (Cd L) ≃* ↥(w1369_im (Wd L) (Cd L) I) :=
    (MonoidHom.ofInjective (s16h_secIncl_injective (Cd L) I (Wd L) hIle)).trans
      (MulEquiv.subgroupCongr hrange)
  have he : ∀ u : Sect I (Cd L),
      (e u : Sect (Wd L) (Cd L)) = s16h_secIncl (Cd L) I (Wd L) hIle u := fun u => rfl
  have hinter : ∀ (a : ↥L) (w : Sect I (Cd L)),
      (e (B5.secHom L hstI hstC a w) : Sect (Wd L) (Cd L)) =
        B5.secHom L hstU hstC a (e w) := by
    intro a w
    rw [he (B5.secHom L hstI hstC a w), he w]
    exact s16h_secIncl_secHom (Cd L) I (Wd L) hIle hstI hstC hstU a w
  have hsecHom_mem : ∀ a : ↥L,
      B5.secHom L hstU hstC a ∈ secSub (Wd L) (Cd L) L := by
    intro a
    show B5.secHom L hstU hstC a ∈ autSec L (Wd L) (Cd L)
    rw [← B5.range_secHom L hstU hstC]
    exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hAstable : StableUnder (secSub (Wd L) (Cd L) L) (w1369_im (Wd L) (Cd L) I) :=
    w1369_stable_im hstabU hIirr.2.1
  have hmemA : ∀ (a : ↥L) (x : ↥(w1369_im (Wd L) (Cd L) I)),
      B5.secHom L hstU hstC a ((x : ↥(w1369_im (Wd L) (Cd L) I)) : Sect (Wd L) (Cd L)) ∈
        w1369_im (Wd L) (Cd L) I :=
    fun a x => hAstable (B5.secHom L hstU hstC a) (hsecHom_mem a)
      ((x : ↥(w1369_im (Wd L) (Cd L) I)) : Sect (Wd L) (Cd L)) x.2
  intro φ hφ
  let ψ : Sect I (Cd L) ≃* Sect I (Cd L) := e.trans (φ.trans e.symm)
  have hψ_apply : ∀ z : Sect I (Cd L), ψ z = e.symm (φ (e z)) := fun z => rfl
  have hψcenter : ψ ∈ Subgroup.center (MulAut (Sect I (Cd L))) := by
    rw [Subgroup.mem_center_iff]
    intro γ
    apply MulEquiv.ext
    intro x
    simp only [MulAut.mul_apply]
    have hγmem : γ ∈ (B5.secHom L hstI hstC).range := by
      rw [B5.range_secHom L hstI hstC]
      show γ ∈ secSub I (Cd L) L
      rw [htop]
      exact Subgroup.mem_top γ
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hγmem
    rw [← ha]
    let l : ↥(secSub (Wd L) (Cd L) L) := ⟨B5.secHom L hstU hstC a, hsecHom_mem a⟩
    let y : ↥(w1369_im (Wd L) (Cd L) I) :=
      ⟨B5.secHom L hstU hstC a
          ((e x : ↥(w1369_im (Wd L) (Cd L) I)) : Sect (Wd L) (Cd L)),
        hmemA a (e x)⟩
    have hφl := hφ l (e x) y rfl
    apply e.injective
    rw [hψ_apply, hψ_apply, MulEquiv.apply_symm_apply]
    rw [show e (B5.secHom L hstI hstC a x) = y from Subtype.ext (hinter a x)]
    apply Subtype.ext
    rw [hinter a (e.symm (φ (e x))), MulEquiv.apply_symm_apply]
    exact hφl
  have hψ1 : ψ = 1 := by
    have hc := w1369_center_mulAut_of_sq_eq_one (sect_exp_two hw2 I (Cd L))
      (by rw [hcard]; norm_num)
    rw [hc, Subgroup.mem_bot] at hψcenter
    exact hψcenter
  apply MulEquiv.ext
  intro y
  have h2 : e.symm (φ y) = e.symm y := by
    have h : ψ (e.symm y) = e.symm y := by
      rw [hψ1]
      rfl
    simpa [hψ_apply, MulEquiv.apply_symm_apply] using h
  exact e.symm.injective h2

theorem w1369_sum_two_irr_unique {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {P P' R R' : Subgroup Q} (hP : XMod.IsIrr ↥Λ P) (hP' : XMod.IsIrr ↥Λ P')
    (hspan : P ⊔ P' = ⊤)
    (hE : Z391.EndUnitsTrivial Λ P) (hR : XMod.IsIrr ↥Λ R) (hR' : XMod.IsIrr ↥Λ R')
    (hRP : R ≠ P) (hRP' : R ≠ P') (hR'P : R' ≠ P) (hR'P' : R' ≠ P') : R = R' :=
  Z391.v2f_eq_of_le_sup hP hP' (fun φ hφ => hE φ hφ) hR hR'
    (hspan ▸ le_top) (hspan ▸ le_top) hRP hRP' hR'P hR'P'

theorem w1369_map_conj_self_of_sq_one {U : Subgroup W} {t : MulAut W} (ht : t * t = 1) :
    (U.map t.toMonoidHom).map t.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have hcomp : t.toMonoidHom.comp t.toMonoidHom = MonoidHom.id W := by
    ext x
    show t (t x) = x
    rw [← MulAut.mul_apply, ht]
    rfl
  rw [hcomp, Subgroup.map_id]

theorem w1369_move_stabPair {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    StabPair L (Wd L) (Cd L) := by
  have hWdstab : StableUnder L (Wd L) := by
    intro l hl w hw
    have hgen : l w * w⁻¹ ∈ Wd L :=
      Subgroup.subset_closure ⟨l, hl, w, Subgroup.mem_top w, rfl⟩
    rw [show l w = (l w * w⁻¹) * w by group]
    exact (Wd L).mul_mem hgen hw
  have hfixstab : StableUnder L (fixV L) := by
    intro x hx u hu
    rw [mem_fixV] at hu ⊢
    intro z hz
    calc z (x u) = (z * x) u := rfl
      _ = u := hu (z * x) (L.mul_mem hz hx)
      _ = x u := (hu x hx).symm
  refine fun l hl => ⟨hWdstab l hl, ?_⟩
  intro u hu
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  exact Subgroup.mem_inf.mpr ⟨hWdstab l hl u hu1, hfixstab l hl u hu2⟩

theorem w1369_move_sec_isIrr (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I)
    {I' : Subgroup W} (hI' : I' ∈ irrSet L) :
    XMod.IsIrr ↥(secSub (Wd L) (Cd L) L) (w1369_im (Wd L) (Cd L) (I' ⊔ Cd L)) := by
  obtain ⟨-, hCM, hMW, hI'irr, -⟩ := irr_to_sect hw2 L hI'
  exact isIrrOn_bot_iff_isIrr.mp
    (w1369_irr_transfer (w1369_move_stabPair S) hCM hMW hI'irr)

theorem w1369_move_irr_cases_aux (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) :
    (∀ I' ∈ irrSet L, I' = I ∨ I' = I.map t.toMonoidHom) ∨
      ∃ I₃ ∈ irrSet L, I₃ ≠ I ∧ I₃ ≠ I.map t.toMonoidHom ∧ I₃.map t.toMonoidHom = I₃ ∧
        I₃ ⊔ Cd L < Wd L ∧
        ∀ I' ∈ irrSet L, I' = I ∨ I' = I.map t.toMonoidHom ∨ I' = I₃ := by
  classical
  have hCI : Cd L ≤ I := by rw [(move_C hw2 S).1]; exact inf_le_left
  have hIle : I ≤ Wd L := (irr_to_sect hw2 L S.hI).1
  have hcommI : commSub I L = I := by
    have h := (irr_to_sect hw2 L S.hI).2.2.2.2
    rwa [sup_eq_left.mpr hCI] at h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [S.ctx.std.t2] at h
    simpa [pow_two] using h
  by_cases hthird : ∃ I' ∈ irrSet L, I' ≠ I ∧ I' ≠ I.map t.toMonoidHom
  · right
    obtain ⟨I₀, hI₀mem, hI₀I, hI₀B⟩ := hthird
    let B' : Subgroup W := I.map t.toMonoidHom
    let U : Subgroup W := Wd L
    let C : Subgroup W := Cd L
    let Λ : Subgroup (MulAut (Sect U C)) := secSub U C L
    let A : Subgroup (Sect U C) := w1369_im U C I
    let Bs : Subgroup (Sect U C) := w1369_im U C B'
    have hB'mem : B' ∈ irrSet L := (move_conj_irr S).1
    have hCB : C ≤ B' := by
      change Cd L ≤ I.map t.toMonoidHom
      rw [(move_C hw2 S).1, ← (move_C hw2 S).2]
      exact inf_le_left
    have hA : XMod.IsIrr ↥Λ A := by
      have h := w1369_move_sec_isIrr hw2 S S.hI
      rwa [sup_eq_left.mpr hCI] at h
    have hB : XMod.IsIrr ↥Λ Bs := by
      have h := w1369_move_sec_isIrr hw2 S hB'mem
      rwa [sup_eq_left.mpr hCB] at h
    have hspan : A ⊔ Bs = ⊤ := by
      have hIleU : I ≤ U := (irr_to_sect hw2 L S.hI).1
      have hB'leU : B' ≤ U := (irr_to_sect hw2 L hB'mem).1
      change w1369_im U C I ⊔ w1369_im U C B' = ⊤
      rw [← w1369_im_sup hIleU hB'leU, ← move_W hw2 S, w1369_im_top]
    have hE : Z391.EndUnitsTrivial Λ A := w1369_move_endUnitsTrivial hw2 S
    have hsec_inj : ∀ I' ∈ irrSet L, ∀ J' ∈ irrSet L,
        w1369_im U C (I' ⊔ C) = w1369_im U C (J' ⊔ C) → I' = J' := by
      intro I' hI' J' hJ' heq
      obtain ⟨-, hCI', hI'U, -, hI'comm⟩ := irr_to_sect hw2 L hI'
      obtain ⟨-, hCJ', hJ'U, -, hJ'comm⟩ := irr_to_sect hw2 L hJ'
      have hpre : w1369_pre U C (w1369_im U C (I' ⊔ C)) =
          w1369_pre U C (w1369_im U C (J' ⊔ C)) := by rw [heq]
      rw [w1369_pre_im hCI' hI'U, w1369_pre_im hCJ' hJ'U] at hpre
      rw [← hI'comm, hpre, hJ'comm]
    have hsec_eq_I : ∀ I' ∈ irrSet L, w1369_im U C (I' ⊔ C) = A ↔ I' = I := by
      intro I' hI'
      constructor
      · intro heq
        refine hsec_inj I' hI' I S.hI ?_
        rw [heq, sup_eq_left.mpr hCI]
      · intro hEq
        rw [hEq, sup_eq_left.mpr hCI]
    have hsec_eq_B : ∀ I' ∈ irrSet L, w1369_im U C (I' ⊔ C) = Bs ↔ I' = B' := by
      intro I' hI'
      constructor
      · intro heq
        refine hsec_inj I' hI' B' hB'mem ?_
        rw [heq, sup_eq_left.mpr hCB]
      · intro hEq
        rw [hEq, sup_eq_left.mpr hCB]
    have huniq : ∀ I' ∈ irrSet L, I' ≠ I → I' ≠ B' → I' = I₀ := by
      intro I' hI' hneI hneB
      have hR := w1369_move_sec_isIrr hw2 S hI'
      have hR₀ := w1369_move_sec_isIrr hw2 S hI₀mem
      have hRneA : w1369_im U C (I' ⊔ C) ≠ A := fun heq => hneI ((hsec_eq_I I' hI').mp heq)
      have hRneB : w1369_im U C (I' ⊔ C) ≠ Bs := fun heq => hneB ((hsec_eq_B I' hI').mp heq)
      have hR₀neA : w1369_im U C (I₀ ⊔ C) ≠ A := fun heq => hI₀I ((hsec_eq_I I₀ hI₀mem).mp heq)
      have hR₀neB : w1369_im U C (I₀ ⊔ C) ≠ Bs := fun heq => hI₀B ((hsec_eq_B I₀ hI₀mem).mp heq)
      exact hsec_inj I' hI' I₀ hI₀mem
        (w1369_sum_two_irr_unique hA hB hspan hE hR hR₀ hRneA hRneB hR₀neA hR₀neB)
    have hR₀neTop : w1369_im U C (I₀ ⊔ C) ≠ ⊤ := by
      intro htop
      have hbot : w1369_im U C (I₀ ⊔ C) ⊓ A = ⊥ :=
        Z391.v2f_inf_eq_bot (w1369_move_sec_isIrr hw2 S hI₀mem) hA
          (fun heq => hI₀I ((hsec_eq_I I₀ hI₀mem).mp heq))
      have hAbot : A = ⊥ := by
        calc A = w1369_im U C (I₀ ⊔ C) ⊓ A := by rw [htop, top_inf_eq]
          _ = ⊥ := hbot
      exact (ne_of_gt hA.2.1) hAbot
    have hI₀lt : I₀ ⊔ Cd L < Wd L := by
      refine lt_of_le_of_ne (irr_to_sect hw2 L hI₀mem).2.2.1 ?_
      intro hEq
      exact hR₀neTop (by rw [hEq, w1369_im_top])
    have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (S.ctx.hfix L S.ctx.comp)
    have hI₀t : I₀.map t.toMonoidHom = I₀ := by
      have htmap : (I₀.map t.toMonoidHom).map t.toMonoidHom = I₀ :=
        w1369_map_conj_self_of_sq_one ht2
      have hJmem : I₀.map t.toMonoidHom ∈ irrSet L :=
        (irr_stab htN).2.2 I₀ hI₀mem
      have hJneI : I₀.map t.toMonoidHom ≠ I := by
        intro hJI
        apply hI₀B
        have h := congrArg (fun J : Subgroup W => J.map t.toMonoidHom) hJI
        rwa [htmap] at h
      have hJneB : I₀.map t.toMonoidHom ≠ B' := by
        intro hJB
        apply hI₀I
        have h := congrArg (fun J : Subgroup W => J.map t.toMonoidHom) hJB
        rwa [htmap, w1369_map_conj_self_of_sq_one ht2] at h
      exact huniq (I₀.map t.toMonoidHom) hJmem hJneI hJneB
    have hlast : ∀ I' ∈ irrSet L, I' = I ∨ I' = I.map t.toMonoidHom ∨ I' = I₀ := by
      intro I' hI'
      by_cases h1 : I' = I
      · exact Or.inl h1
      · by_cases h2 : I' = B'
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (huniq I' hI' h1 h2))
    exact ⟨I₀, hI₀mem, hI₀I, hI₀B, hI₀t, hI₀lt, hlast⟩
  · left
    intro I' hI'
    by_contra hcon
    rw [not_or] at hcon
    exact hthird ⟨I', hI', hcon.1, hcon.2⟩

theorem w1369_move_trans_aux (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I)
    (hT : Tcl Y L) :
    ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L, ∃ g ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      I₂ = I₁.map g.toMonoidHom := by
  classical
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [S.ctx.std.t2] at h
    simpa [pow_two] using h
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (S.ctx.hfix L S.ctx.comp)
  have htmem : t ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_inf.mpr ⟨S.ctx.std.tY, htN⟩
  rcases w1369_move_irr_cases_aux hw2 S with hcase | ⟨I₃, hI₃mem, hI₃I, hI₃B, hI₃t, hI₃lt, hI₃all⟩
  ·
    intro I₁ hI₁ I₂ hI₂
    have h1 := hcase I₁ hI₁
    have h2 := hcase I₂ hI₂
    rcases h1 with hI1 | hI1 <;> rcases h2 with hI2 | hI2
    · refine ⟨1, Subgroup.mem_inf.mpr ⟨Y.one_mem, Subgroup.one_mem _⟩, ?_⟩
      rw [hI2, hI1, show (1 : MulAut W).toMonoidHom = MonoidHom.id W from rfl,
        Subgroup.map_id]
    · refine ⟨t, htmem, ?_⟩
      rw [hI2, hI1]
    · refine ⟨t, htmem, ?_⟩
      rw [hI2, hI1, w1369_map_conj_self_of_sq_one (U := I) ht2]
    · refine ⟨1, Subgroup.mem_inf.mpr ⟨Y.one_mem, Subgroup.one_mem _⟩, ?_⟩
      rw [hI2, hI1, show (1 : MulAut W).toMonoidHom = MonoidHom.id W from rfl,
        Subgroup.map_id]
  ·
    have hF := lemmaF hw2 S.ctx hT (move_perfCentTriv hw2 S)
    have hMns : ¬ StableUnder (Y ⊓ Subgroup.normalizer (L : Set (MulAut W)))
        (I₃ ⊔ Cd L) := by
      intro hstab
      rcases hF (I₃ ⊔ Cd L) le_sup_right (le_of_lt hI₃lt) hstab with h | h
      · have hle : I₃ ≤ Cd L := h ▸ le_sup_left
        have hbot : w1369_im (Wd L) (Cd L) (I₃ ⊔ Cd L) = ⊥ := by
          rw [sup_eq_right.mpr hle, w1369_im_C]
        exact (ne_of_gt (w1369_move_sec_isIrr hw2 S hI₃mem).2.1) hbot
      · exact absurd h (ne_of_lt hI₃lt)
    unfold StableUnder at hMns
    push Not at hMns
    obtain ⟨g, hgN, m, hmM, hgm⟩ := hMns
    have hgNorm : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := (Subgroup.mem_inf.mp hgN).2
    have hgCd : (Cd L).map g.toMonoidHom = Cd L := (irr_stab hgNorm).2.1
    have hgne : I₃.map g.toMonoidHom ≠ I₃ := by
      intro heq
      have hmapM : (I₃ ⊔ Cd L).map g.toMonoidHom = I₃ ⊔ Cd L := by
        rw [Subgroup.map_sup, heq, hgCd]
      exact hgm (hmapM ▸ Subgroup.mem_map_of_mem g.toMonoidHom hmM)
    have hI₃gmem : I₃.map g.toMonoidHom ∈ irrSet L := (irr_stab hgNorm).2.2 I₃ hI₃mem
    have hI₃_to_I : ∃ gI ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)),
        I.map gI.toMonoidHom = I₃ := by
      rcases hI₃all (I₃.map g.toMonoidHom) hI₃gmem with h | h | h
      · refine ⟨g⁻¹, Subgroup.inv_mem _ hgN, ?_⟩
        have h1 : (I₃.map g.toMonoidHom).map g⁻¹.toMonoidHom =
            I.map g⁻¹.toMonoidHom := by rw [h]
        rw [Subgroup.map_map] at h1
        have hcomp : g⁻¹.toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
          ext x; show g⁻¹ (g x) = x; simp
        rw [hcomp, Subgroup.map_id] at h1
        exact h1.symm
      · refine ⟨(t * g)⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ htmem hgN), ?_⟩
        have h2 : I₃.map (t * g).toMonoidHom = I := by
          rw [show (t * g).toMonoidHom = t.toMonoidHom.comp g.toMonoidHom from rfl]
          rw [← Subgroup.map_map, h, w1369_map_conj_self_of_sq_one ht2]
        have h1 : (I₃.map (t * g).toMonoidHom).map (t * g)⁻¹.toMonoidHom =
            I.map (t * g)⁻¹.toMonoidHom := by rw [h2]
        rw [Subgroup.map_map] at h1
        have hcomp : (t * g)⁻¹.toMonoidHom.comp (t * g).toMonoidHom = MonoidHom.id W := by
          ext x; show (t * g)⁻¹ ((t * g) x) = x; simp
        rw [hcomp, Subgroup.map_id] at h1
        exact h1.symm
      · exact absurd h hgne
    have horb : ∀ I' ∈ irrSet L, ∃ g ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)),
        I.map g.toMonoidHom = I' := by
      intro I' hI'
      rcases hI₃all I' hI' with h | h | h
      · refine ⟨1, Subgroup.mem_inf.mpr ⟨Y.one_mem, Subgroup.one_mem _⟩, ?_⟩
        rw [show (1 : MulAut W).toMonoidHom = MonoidHom.id W from rfl, Subgroup.map_id]
        exact h.symm
      · exact ⟨t, htmem, h.symm⟩
      · obtain ⟨gI, hgI, hgIeq⟩ := hI₃_to_I
        rw [h]
        exact ⟨gI, hgI, hgIeq⟩
    intro I₁ hI₁ I₂ hI₂
    obtain ⟨g₁, hg₁, hg₁eq⟩ := horb I₁ hI₁
    obtain ⟨g₂, hg₂, hg₂eq⟩ := horb I₂ hI₂
    refine ⟨g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
    rw [← hg₂eq, ← hg₁eq]
    rw [show (g₂ * g₁⁻¹).toMonoidHom = g₂.toMonoidHom.comp g₁⁻¹.toMonoidHom from rfl]
    rw [← Subgroup.map_map]
    have hcancel : (I.map g₁.toMonoidHom).map g₁⁻¹.toMonoidHom = I := by
      rw [Subgroup.map_map]
      have hcomp : g₁⁻¹.toMonoidHom.comp g₁.toMonoidHom = MonoidHom.id W := by
        ext x; show g₁⁻¹ (g₁ x) = x; simp
      rw [hcomp, Subgroup.map_id]
    rw [hcancel]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
