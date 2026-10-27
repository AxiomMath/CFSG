module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {W : Type} [CommGroup W]
variable {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}

private noncomputable def s168e3_alt6_prodEquiv (F : Cfg2Setting X H J₀ J₁) :
    ↥J₀ × ↥J₁ ≃* W := by
  classical
  let prodHom : ↥J₀ × ↥J₁ →* W :=
    { toFun := fun p => (p.1 : W) * (p.2 : W)
      map_one' := by simp
      map_mul' := by
        intro p q
        change ((p.1 * q.1 : ↥J₀) : W) * ((p.2 * q.2 : ↥J₁) : W) =
          ((p.1 : W) * (p.2 : W)) * ((q.1 : W) * (q.2 : W))
        simp only [Subgroup.coe_mul]
        ac_rfl }
  have hcompl : J₀.IsComplement' J₁ := by
    refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · exact disjoint_iff_inf_le.mpr (le_of_eq F.inf_eq)
    · have h := Subgroup.mul_normal J₀ J₁
      rw [F.sup_eq] at h
      simpa using h.symm
  exact MulEquiv.ofBijective prodHom hcompl

@[simp] private lemma s168e3_alt6_prodEquiv_apply (F : Cfg2Setting X H J₀ J₁)
    (p : ↥J₀ × ↥J₁) :
    s168e3_alt6_prodEquiv F p = (p.1 : W) * (p.2 : W) := rfl

private noncomputable def s168e3_alt6_psiOfGraph (F : Cfg2Setting X H J₀ J₁)
    (θ : ↥J₀ ≃* ↥J₁) : MulAut W :=
  let e := s168e3_alt6_prodEquiv F
  e.symm.trans ((MulEquiv.prodComm.trans (θ.symm.prodCongr θ)).trans e)

private lemma s168e3_alt6_psiOfGraph_apply_mul (F : Cfg2Setting X H J₀ J₁)
    (θ : ↥J₀ ≃* ↥J₁) {x y : W} (hx : x ∈ J₀) (hy : y ∈ J₁) :
    s168e3_alt6_psiOfGraph F θ (x * y) = θ.symm ⟨y, hy⟩ * θ ⟨x, hx⟩ := by
  classical
  let e := s168e3_alt6_prodEquiv F
  have hp : e (⟨x, hx⟩, ⟨y, hy⟩) = x * y := by
    rw [s168e3_alt6_prodEquiv_apply]
  have hsymm : e.symm (x * y) = (⟨x, hx⟩, ⟨y, hy⟩) := by
    rw [← hp, MulEquiv.symm_apply_apply]
  change e ((MulEquiv.prodComm.trans (θ.symm.prodCongr θ)) (e.symm (x * y))) =
    θ.symm ⟨y, hy⟩ * θ ⟨x, hx⟩
  rw [hsymm]
  change ((θ.symm ⟨y, hy⟩ : ↥J₀) : W) * ((θ ⟨x, hx⟩ : ↥J₁) : W) =
    ((θ.symm ⟨y, hy⟩ : ↥J₀) : W) * ((θ ⟨x, hx⟩ : ↥J₁) : W)
  rfl

private lemma s168e3_alt6_psiOfGraph_apply_left (F : Cfg2Setting X H J₀ J₁)
    (θ : ↥J₀ ≃* ↥J₁) {x : W} (hx : x ∈ J₀) :
    s168e3_alt6_psiOfGraph F θ x = θ ⟨x, hx⟩ := by
  have h := s168e3_alt6_psiOfGraph_apply_mul F θ hx (J₁.one_mem : (1 : W) ∈ J₁)
  have h1 : (θ.symm ⟨(1 : W), J₁.one_mem⟩ : W) = 1 := by simp
  simpa [h1] using h

private lemma s168e3_alt6_psiOfGraph_apply_right (F : Cfg2Setting X H J₀ J₁)
    (θ : ↥J₀ ≃* ↥J₁) {y : W} (hy : y ∈ J₁) :
    s168e3_alt6_psiOfGraph F θ y = θ.symm ⟨y, hy⟩ := by
  have h := s168e3_alt6_psiOfGraph_apply_mul F θ (J₀.one_mem : (1 : W) ∈ J₀) hy
  have h1 : (θ ⟨(1 : W), J₀.one_mem⟩ : W) = 1 := by simp
  simpa [h1] using h

private lemma s168e3_alt6_psiOfGraph_map (F : Cfg2Setting X H J₀ J₁)
    (θ : ↥J₀ ≃* ↥J₁) :
    J₀.map (s168e3_alt6_psiOfGraph F θ).toMonoidHom = J₁ := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hz
    have hxz' : s168e3_alt6_psiOfGraph F θ x = z := hxz
    rw [← hxz', s168e3_alt6_psiOfGraph_apply_left F θ hx]
    exact (θ ⟨x, hx⟩).2
  · intro hz
    refine Subgroup.mem_map.2 ⟨(θ.symm ⟨z, hz⟩ : W), (θ.symm ⟨z, hz⟩).2, ?_⟩
    show s168e3_alt6_psiOfGraph F θ (θ.symm ⟨z, hz⟩ : W) = z
    rw [s168e3_alt6_psiOfGraph_apply_left F θ (θ.symm ⟨z, hz⟩).2]
    exact congrArg Subtype.val (θ.apply_symm_apply ⟨z, hz⟩)

private lemma s168e3_alt6_psiOfGraph_mem_centralizer [Finite W]
    (F : Cfg2Setting X H J₀ J₁) (θ : ↥J₀ ≃* ↥J₁)
    (hθ : Z391.V2fEqv ↥H θ) :
    s168e3_alt6_psiOfGraph F θ ∈ Subgroup.centralizer (H : Set (MulAut W)) := by
  classical
  have hJ0inv : XMod.IsInv ↥H J₀ := (s16e_two_isIrr_of_mem F F.irr₀).1
  have hJ1inv : XMod.IsInv ↥H J₁ := (s16e_two_isIrr_of_mem F F.irr₁).1
  have hJ0stab : StableUnder H J₀ := (s16e_two_isIrrOn_of_mem F F.irr₀).2.1
  have hJ1stab : StableUnder H J₁ := (s16e_two_isIrrOn_of_mem F F.irr₁).2.1
  have hθsymm : Z391.V2fEqv ↥H θ.symm := Z391.V2fEqv.symm hJ0inv hθ
  refine Subgroup.mem_centralizer_iff.2 fun h hH => ?_
  apply MulEquiv.ext
  intro w
  let e := s168e3_alt6_prodEquiv F
  let p : ↥J₀ × ↥J₁ := e.symm w
  have hw : (p.1 : W) * (p.2 : W) = w := by
    have h := e.apply_symm_apply w
    rwa [s168e3_alt6_prodEquiv_apply] at h
  have hh1 : h (p.1 : W) ∈ J₀ := hJ0stab h hH (p.1 : W) p.1.2
  have hh2 : h (p.2 : W) ∈ J₁ := hJ1stab h hH (p.2 : W) p.2.2
  have hψ1 : h (s168e3_alt6_psiOfGraph F θ (p.1 : W)) =
      s168e3_alt6_psiOfGraph F θ (h (p.1 : W)) := by
    have h1 : θ ⟨h (p.1 : W), hh1⟩ = h (θ p.1) := by
      have := hθ ⟨h, hH⟩ (p.1) ⟨h (p.1 : W), hh1⟩ rfl
      simpa using this.symm
    rw [s168e3_alt6_psiOfGraph_apply_left F θ p.1.2,
      s168e3_alt6_psiOfGraph_apply_left F θ hh1]
    exact h1.symm
  have hψ2 : h (s168e3_alt6_psiOfGraph F θ (p.2 : W)) =
      s168e3_alt6_psiOfGraph F θ (h (p.2 : W)) := by
    have h1 : θ.symm ⟨h (p.2 : W), hh2⟩ = h (θ.symm p.2) := by
      have := hθsymm ⟨h, hH⟩ (p.2) ⟨h (p.2 : W), hh2⟩ rfl
      simpa using this.symm
    rw [s168e3_alt6_psiOfGraph_apply_right F θ p.2.2,
      s168e3_alt6_psiOfGraph_apply_right F θ hh2]
    exact h1.symm
  calc (h * s168e3_alt6_psiOfGraph F θ) w
      = h (s168e3_alt6_psiOfGraph F θ ((p.1 : W) * (p.2 : W))) := by
        rw [MulAut.mul_apply, hw]
    _ = h (s168e3_alt6_psiOfGraph F θ (p.1 : W) *
          s168e3_alt6_psiOfGraph F θ (p.2 : W)) := by
        rw [map_mul]
    _ = h (s168e3_alt6_psiOfGraph F θ (p.1 : W)) *
          h (s168e3_alt6_psiOfGraph F θ (p.2 : W)) := by rw [map_mul]
    _ = s168e3_alt6_psiOfGraph F θ (h (p.1 : W)) *
          s168e3_alt6_psiOfGraph F θ (h (p.2 : W)) := by rw [hψ1, hψ2]
    _ = s168e3_alt6_psiOfGraph F θ (h (p.1 : W) * h (p.2 : W)) := by rw [map_mul]
    _ = s168e3_alt6_psiOfGraph F θ (h ((p.1 : W) * (p.2 : W))) := by
        rw [map_mul h (p.1 : W) (p.2 : W)]
    _ = s168e3_alt6_psiOfGraph F θ (h w) := by rw [hw]
    _ = (s168e3_alt6_psiOfGraph F θ * h) w := by rw [MulAut.mul_apply]

theorem s168e3_alt6_irr_eq_pair [Finite W] {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X H J₀ J₁)
    (hne : ∀ ψ ∈ Subgroup.centralizer (H : Set (MulAut W)), J₀.map ψ.toMonoidHom ≠ J₁) :
    irrSet H = {J₀, J₁} := by
  ext I
  constructor
  · intro hI
    by_contra hnot
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hnot
    have hI0 : I ≠ J₀ := fun h => hnot (Or.inl h)
    have hI1 : I ≠ J₁ := fun h => hnot (Or.inr h)
    have hIrr : XMod.IsIrr ↥H I := s16e_two_isIrr_of_mem F hI
    have hIrr₀ : XMod.IsIrr ↥H J₀ := s16e_two_isIrr_of_mem F F.irr₀
    have hIrr₁ : XMod.IsIrr ↥H J₁ := s16e_two_isIrr_of_mem F F.irr₁
    have hle : I ≤ J₀ ⊔ J₁ := F.sup_eq.symm ▸ le_top
    have hRP : I ⊓ J₀ = ⊥ := Z391.v2f_inf_eq_bot hIrr hIrr₀ hI0
    have hRP' : I ⊓ J₁ = ⊥ := Z391.v2f_inf_eq_bot hIrr hIrr₁ hI1
    obtain ⟨θ, hθ, -⟩ := Z391.v2f_exists_graph hIrr₀ hIrr₁ hIrr.1 hIrr.2.1.ne' hle hRP hRP'
    exact hne (s168e3_alt6_psiOfGraph F θ)
      (s168e3_alt6_psiOfGraph_mem_centralizer F θ hθ)
      (s168e3_alt6_psiOfGraph_map F θ)
  · rintro (rfl | rfl)
    · exact F.irr₀
    · exact F.irr₁


private lemma s168e3_alt6_isIrrOn_iff {W : Type} [CommGroup W] (A : Subgroup (MulAut W))
    (J : Subgroup W) : IsIrrOn A J ⊥ ↔ XMod.IsIrr ↥A J := by
  unfold IsIrrOn XMod.IsIrr XMod.IsIrrSec XMod.IsInv StableUnder
  constructor
  · rintro ⟨hlt, hstab, -, hmin⟩
    exact ⟨fun a j hj => hstab a a.2 j hj, hlt,
      fun J' hJ' _ hJ'J => hmin J' (fun a ha u hu => hJ' ⟨a, ha⟩ u hu) bot_le hJ'J⟩
  · rintro ⟨hinv, hlt, hmin⟩
    exact ⟨hlt, (fun a ha u hu => hinv ⟨a, ha⟩ u hu),
      (fun a _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]),
      fun J' hJ' _ hJ'J => hmin J' (fun a u hu => hJ' (a : MulAut W) a.2 u hu) bot_le hJ'J⟩

private lemma s168e3_alt6_isIrr_of_iso {B : Type*} [Group B] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction B Q] {L L' : Subgroup Q} (hL' : XMod.IsInv B L')
    (hL : XMod.IsIrr B L) (h : XMod.Iso B L' L) : XMod.IsIrr B L' := by
  rw [XMod.isIrr_iff hL']
  have := (XMod.isIrr_iff hL.1).1 hL
  obtain ⟨e⟩ := XMod.nonempty_linearEquiv_of_iso hL' hL.1 h
  exact IsSimpleModule.congr e

private theorem s168e3_alt6_stable_commSub {U : Type*} [CommGroup U]
    {L : Subgroup (MulAut U)} {J : Subgroup U} (hJ : StableUnder L J) :
    StableUnder L (commSub J L) := by
  intro l hl i hi
  unfold commSub at hi ⊢
  induction hi using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    have e : l (x w * w⁻¹) = ((l * x) w * w⁻¹) * (l w * w⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.mul_apply]
      group
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨l * x, L.mul_mem hl hx, w, hw, rfl⟩)
      (inv_mem (Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩))
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

private def s168e3_alt6_graphHom (ψ : MulAut W) : W →* W :=
  MonoidHom.id W * ψ.toMonoidHom

@[simp] private lemma s168e3_alt6_graphHom_apply (ψ : MulAut W) (x : W) :
    s168e3_alt6_graphHom ψ x = x * ψ x := rfl

private def s168e3_alt6_graph (ψ : MulAut W) (J : Subgroup W) : Subgroup W :=
  J.map (s168e3_alt6_graphHom ψ)

private lemma s168e3_alt6_graph_stable (F : Cfg2Setting X H J₀ J₁) {ψ : MulAut W}
    (hψ : ψ ∈ Subgroup.centralizer (H : Set (MulAut W))) :
    StableUnder H (s168e3_alt6_graph ψ J₀) := by
  intro h hH z hz
  obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hz
  have hx' : h x ∈ J₀ := (s16e_two_isIrrOn_of_mem F F.irr₀).2.1 h hH x hx
  refine Subgroup.mem_map.2 ⟨h x, hx', ?_⟩
  have hc := (Subgroup.mem_centralizer_iff.1 hψ) h hH
  have hcomm : h (ψ x) = ψ (h x) := by
    have := congrArg (fun f : MulAut W => f x) hc
    simpa [MulAut.mul_apply] using this
  rw [← hxz]
  simp only [s168e3_alt6_graphHom_apply, map_mul, hcomm]

private lemma s168e3_alt6_graphHom_inj_on (F : Cfg2Setting X H J₀ J₁) {ψ : MulAut W}
    (hψJ : J₀.map ψ.toMonoidHom = J₁) {x y : W} (hx : x ∈ J₀) (hy : y ∈ J₀)
    (h : s168e3_alt6_graphHom ψ x = s168e3_alt6_graphHom ψ y) : x = y := by
  have hψx₁ : ψ x ∈ J₁ := by
    have : ψ x ∈ J₀.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [hψJ] at this
  have hψy₁ : ψ y ∈ J₁ := by
    have : ψ y ∈ J₀.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rwa [hψJ] at this
  have hxy : x * y⁻¹ = ψ y * (ψ x)⁻¹ := by
    calc x * y⁻¹ = y⁻¹ * x := mul_comm _ _
      _ = y⁻¹ * (x * ψ x) * (ψ x)⁻¹ := by group
      _ = y⁻¹ * (y * ψ y) * (ψ x)⁻¹ := by
        rw [s168e3_alt6_graphHom_apply, s168e3_alt6_graphHom_apply] at h
        rw [h]
      _ = ψ y * (ψ x)⁻¹ := by group
  have hmem₀ : x * y⁻¹ ∈ J₀ := J₀.mul_mem hx (J₀.inv_mem hy)
  have hmem₁ : x * y⁻¹ ∈ J₁ := by
    rw [hxy]
    exact J₁.mul_mem hψy₁ (J₁.inv_mem hψx₁)
  have hbot : x * y⁻¹ ∈ (⊥ : Subgroup W) := by
    rw [← F.inf_eq]
    exact ⟨hmem₀, hmem₁⟩
  have h1 : x * y⁻¹ = 1 := by simpa using hbot
  exact mul_inv_eq_one.mp h1

private lemma s168e3_alt6_graph_iso (F : Cfg2Setting X H J₀ J₁) {ψ : MulAut W}
    (hψ : ψ ∈ Subgroup.centralizer (H : Set (MulAut W)))
    (hψJ : J₀.map ψ.toMonoidHom = J₁) :
    XMod.Iso ↥H J₀ (s168e3_alt6_graph ψ J₀) := by
  let f : ↥J₀ →* ↥(s168e3_alt6_graph ψ J₀) :=
    { toFun := fun x => ⟨s168e3_alt6_graphHom ψ x, Subgroup.mem_map_of_mem _ x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [map_mul]) }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext
      (s168e3_alt6_graphHom_inj_on F hψJ x.2 y.2 (congrArg Subtype.val hxy))
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 z.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxz⟩
  refine ⟨MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩, ?_⟩
  intro a x x' hxx
  have hxx' : (a : MulAut W) (x : W) = (x' : W) := by
    simpa [Subgroup.smul_def, MulAut.smul_def] using hxx
  have hc := (Subgroup.mem_centralizer_iff.1 hψ) (a : MulAut W) a.2
  have hcomm : (a : MulAut W) (ψ (x : W)) = ψ ((a : MulAut W) (x : W)) := by
    have := congrArg (fun f : MulAut W => f (x : W)) hc
    simpa [MulAut.mul_apply] using this
  change (a : MulAut W) (s168e3_alt6_graphHom ψ (x : W)) =
    s168e3_alt6_graphHom ψ (x' : W)
  rw [s168e3_alt6_graphHom_apply, map_mul, hcomm, hxx', s168e3_alt6_graphHom_apply]

private lemma s168e3_alt6_graph_fix_transfer (F : Cfg2Setting X H J₀ J₁) {ψ : MulAut W}
    (hψ : ψ ∈ Subgroup.centralizer (H : Set (MulAut W)))
    (hψJ : J₀.map ψ.toMonoidHom = J₁)
    (hle : s168e3_alt6_graph ψ J₀ ≤ fixV H) : J₀ ≤ fixV H := by
  intro x hx
  rw [mem_fixV]
  intro a ha
  obtain ⟨e, he⟩ := s168e3_alt6_graph_iso F hψ hψJ
  have hx' : a x ∈ J₀ := (s16e_two_isIrrOn_of_mem F F.irr₀).2.1 a ha x hx
  have hgx : (e ⟨x, hx⟩ : W) ∈ fixV H := hle (e ⟨x, hx⟩).2
  have h1 : a (e ⟨x, hx⟩ : W) = (e ⟨x, hx⟩ : W) := (mem_fixV.1 hgx) a ha
  have h2 := he ⟨a, ha⟩ ⟨x, hx⟩ ⟨a x, hx'⟩ rfl
  have h3 : e ⟨a x, hx'⟩ = e ⟨x, hx⟩ := by
    apply Subtype.ext
    rw [← h2]
    simpa [Subgroup.smul_def, MulAut.smul_def] using h1
  exact congrArg Subtype.val (e.injective h3)

private lemma s168e3_alt6_graph_mem_irrSet (F : Cfg2Setting X H J₀ J₁) {ψ : MulAut W}
    (hψ : ψ ∈ Subgroup.centralizer (H : Set (MulAut W)))
    (hψJ : J₀.map ψ.toMonoidHom = J₁) :
    s168e3_alt6_graph ψ J₀ ∈ irrSet H := by
  have hstable := s168e3_alt6_graph_stable F hψ
  have hiso := s168e3_alt6_graph_iso F hψ hψJ
  have hIrr0 : XMod.IsIrr ↥H J₀ := s16e_two_isIrr_of_mem F F.irr₀
  have hInv : XMod.IsInv ↥H (s168e3_alt6_graph ψ J₀) :=
    fun a x hx => hstable a a.2 x hx
  have hIrr : XMod.IsIrr ↥H (s168e3_alt6_graph ψ J₀) :=
    s168e3_alt6_isIrr_of_iso hInv hIrr0 (XMod.Iso.symm hIrr0.1 hiso)
  have hOn : IsIrrOn H (s168e3_alt6_graph ψ J₀) ⊥ :=
    (s168e3_alt6_isIrrOn_iff H _).2 hIrr
  have hJ0ne : J₀ ≠ ⊥ :=
    (s16e_two_isIrrOn_of_mem F F.irr₀).1.ne'
  have hcommle : commSub (s168e3_alt6_graph ψ J₀) H ≤ s168e3_alt6_graph ψ J₀ :=
    commSub_le_of_invariant hstable
  have hcommStable : StableUnder H (commSub (s168e3_alt6_graph ψ J₀) H) :=
    s168e3_alt6_stable_commSub hstable
  have hcomm_ne : commSub (s168e3_alt6_graph ψ J₀) H ≠ ⊥ := by
    intro hbot
    have hlefix : s168e3_alt6_graph ψ J₀ ≤ fixV H := commSub_eq_bot_iff.1 hbot
    have hle0 : J₀ ≤ fixV H := s168e3_alt6_graph_fix_transfer F hψ hψJ hlefix
    have hbot0 : commSub J₀ H = ⊥ := commSub_eq_bot_iff.2 hle0
    rw [F.irr₀.1] at hbot0
    exact hJ0ne hbot0
  have hcomm : commSub (s168e3_alt6_graph ψ J₀) H = s168e3_alt6_graph ψ J₀ := by
    rcases hOn.2.2.2 (commSub (s168e3_alt6_graph ψ J₀) H) hcommStable bot_le hcommle with h | h
    · exact absurd h hcomm_ne
    · exact h
  have hfixinf : s168e3_alt6_graph ψ J₀ ⊓ fixV H = ⊥ := by
    have hfixStable : StableUnder H (s168e3_alt6_graph ψ J₀ ⊓ fixV H) := by
      intro h hH z hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
      refine Subgroup.mem_inf.2 ⟨hstable h hH z hz1, ?_⟩
      rw [mem_fixV]
      intro a ha
      have h1 : (a * h) z = z := (mem_fixV.1 hz2) (a * h) (H.mul_mem ha hH)
      have h2 : h z = z := (mem_fixV.1 hz2) h hH
      simpa [MulAut.mul_apply, h2] using h1
    rcases hOn.2.2.2 (s168e3_alt6_graph ψ J₀ ⊓ fixV H) hfixStable bot_le inf_le_left with h | h
    · exact h
    · exfalso
      have hlefix : s168e3_alt6_graph ψ J₀ ≤ fixV H := fun z hz => by
        have : z ∈ s168e3_alt6_graph ψ J₀ ⊓ fixV H := by rw [h]; exact hz
        exact this.2
      have hle0 : J₀ ≤ fixV H := s168e3_alt6_graph_fix_transfer F hψ hψJ hlefix
      have hbot0 : commSub J₀ H = ⊥ := commSub_eq_bot_iff.2 hle0
      rw [F.irr₀.1] at hbot0
      exact hJ0ne hbot0
  refine ⟨hcomm, ?_⟩
  rwa [hfixinf]

private lemma s168e3_alt6_graph_inf_left (F : Cfg2Setting X H J₀ J₁) {ψ : MulAut W}
    (hψJ : J₀.map ψ.toMonoidHom = J₁) :
    s168e3_alt6_graph ψ J₀ ⊓ J₀ = ⊥ := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzΔ, hz₀⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hzΔ
    have hψx₁ : ψ x ∈ J₁ := by
      have : ψ x ∈ J₀.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hx
      rwa [hψJ] at this
    have hψx₀ : ψ x ∈ J₀ := by
      have : ψ x = x⁻¹ * z := by
        rw [← hxz, s168e3_alt6_graphHom_apply]
        group
      rw [this]
      exact J₀.mul_mem (J₀.inv_mem hx) hz₀
    have hψx_bot : ψ x = 1 := by
      have hmem : ψ x ∈ (⊥ : Subgroup W) := by
        rw [← F.inf_eq]
        exact ⟨hψx₀, hψx₁⟩
      simpa using hmem
    have hx1 : x = 1 := (MulEquiv.map_eq_one_iff ψ).1 hψx_bot
    rw [Subgroup.mem_bot]
    rw [← hxz, s168e3_alt6_graphHom_apply]
    simp [hx1, hψx_bot]
  · intro hz
    rw [Subgroup.mem_bot] at hz
    subst hz
    exact Subgroup.mem_inf.2 ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

private lemma s168e3_alt6_graph_inf_right (F : Cfg2Setting X H J₀ J₁) {ψ : MulAut W}
    (hψJ : J₀.map ψ.toMonoidHom = J₁) :
    s168e3_alt6_graph ψ J₀ ⊓ J₁ = ⊥ := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzΔ, hz₁⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hzΔ
    have hψx₁ : ψ x ∈ J₁ := by
      have : ψ x ∈ J₀.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hx
      rwa [hψJ] at this
    have hx₁ : x ∈ J₁ := by
      have : x = z * (ψ x)⁻¹ := by
        rw [← hxz, s168e3_alt6_graphHom_apply]
        group
      rw [this]
      exact J₁.mul_mem hz₁ (J₁.inv_mem hψx₁)
    have hx_bot : x ∈ (⊥ : Subgroup W) := by
      rw [← F.inf_eq]
      exact ⟨hx, hx₁⟩
    have hx1 : x = 1 := by simpa using hx_bot
    rw [Subgroup.mem_bot]
    rw [← hxz, s168e3_alt6_graphHom_apply, hx1, one_mul, map_one]
  · intro hz
    rw [Subgroup.mem_bot] at hz
    subst hz
    exact Subgroup.mem_inf.2 ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

theorem s168e3_alt6_irr_card_three [Finite W] {X H : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X H J₀ J₁) (hE₀ : Z391.EndUnitsTrivial H J₀) {ψ : MulAut W}
    (hψ : ψ ∈ Subgroup.centralizer (H : Set (MulAut W))) (hψJ : J₀.map ψ.toMonoidHom = J₁) :
    Nat.card ↥(irrSet H) = 3 := by
  haveI : Finite (Subgroup W) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite ↥(irrSet H) := Finite.of_injective _ Subtype.coe_injective
  have hJ₀ne : J₀ ≠ ⊥ := (s16e_two_isIrrOn_of_mem F F.irr₀).1.ne'
  have hJ₁ne : J₁ ≠ ⊥ := (s16e_two_isIrrOn_of_mem F F.irr₁).1.ne'
  have hJ01 : J₀ ≠ J₁ := by
    intro h
    have h1 : J₀ ⊓ J₁ = J₀ := by rw [h, inf_idem]
    rw [F.inf_eq] at h1
    exact hJ₀ne h1.symm
  have hΔmem : s168e3_alt6_graph ψ J₀ ∈ irrSet H :=
    s168e3_alt6_graph_mem_irrSet F hψ hψJ
  have hΔinf₀ := s168e3_alt6_graph_inf_left F hψJ
  have hΔinf₁ := s168e3_alt6_graph_inf_right F hψJ
  have hΔne₀ : s168e3_alt6_graph ψ J₀ ≠ J₀ := by
    intro h
    rw [h, inf_idem] at hΔinf₀
    exact hJ₀ne hΔinf₀
  have hΔne₁ : s168e3_alt6_graph ψ J₀ ≠ J₁ := by
    intro h
    rw [h, inf_idem] at hΔinf₁
    exact hJ₁ne hΔinf₁
  let g : Fin 3 → ↥(irrSet H) := fun i =>
    if i = 0 then ⟨J₀, F.irr₀⟩
    else if i = 1 then ⟨J₁, F.irr₁⟩
    else ⟨s168e3_alt6_graph ψ J₀, hΔmem⟩
  have hJ01' : J₁ ≠ J₀ := fun h => hJ01 h.symm
  have hΔne₀' : J₀ ≠ s168e3_alt6_graph ψ J₀ := fun h => hΔne₀ h.symm
  have hΔne₁' : J₁ ≠ s168e3_alt6_graph ψ J₀ := fun h => hΔne₁ h.symm
  have hg_inj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [g, hJ01, hJ01', hΔne₀, hΔne₁, hΔne₀', hΔne₁'] at hij ⊢
  have hge : 3 ≤ Nat.card ↥(irrSet H) := by
    simpa using Nat.card_le_card_of_injective g hg_inj
  exact le_antisymm (s16e_two_irrSet_card_le_three F hE₀) hge

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
