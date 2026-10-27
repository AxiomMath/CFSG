module

public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

noncomputable def lkfTrans (a b : Fin 3) (hab : a ≠ b) : ↥(StatedSL 3 (ZMod 2)) :=
  ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.transvection a b (1 : ZMod 2))
      (by rw [Matrix.det_transvection_of_ne a b hab]; exact isUnit_one),
    Subgroup.subset_closure (by simp [Matrix.det_transvection_of_ne a b hab])⟩

theorem lkf_natAct_trans (a b : Fin 3) (hab : a ≠ b) (x : Fin 3 → ZMod 2) :
    Multiplicative.toAdd (natAct (StatedSL 3 (ZMod 2)) (lkfTrans a b hab) (Multiplicative.ofAdd x))
      = x + Pi.single a (x b) := by
  show (Matrix.transvection a b (1 : ZMod 2)).mulVec x = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  ext i
  by_cases h : i = a
  · subst h; simp
  · simp [h]

set_option maxRecDepth 100000 in
theorem lkf_dec : ∀ v : Fin 3 → Fin 3 → ZMod 2, (∀ a b, a ≠ b → v a = Pi.single a (v b b)) →
    ∀ a, v a = Pi.single a (v 0 0) := by
  decide

theorem lkf_schur_add (F : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2))
    (htr : ∀ (a b : Fin 3), a ≠ b → ∀ x : Fin 3 → ZMod 2,
      F (x + Pi.single a (x b)) = F x + Pi.single a (F x b)) :
    ∃ s : ZMod 2, ∀ x, F x = s • x := by
  have key : ∀ a b : Fin 3, a ≠ b → F (Pi.single a 1) = Pi.single a (F (Pi.single b 1) b) := by
    intro a b hab
    have h := htr a b hab (Pi.single b 1)
    rw [map_add] at h
    simp only [Pi.single_eq_same] at h
    exact add_left_cancel h
  refine ⟨F (Pi.single 0 1) 0, fun x => ?_⟩
  have hv := lkf_dec (fun a => F (Pi.single a 1)) key
  have hx : x = ∑ a, Pi.single a (x a) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hx]
  rw [map_sum]
  conv_rhs => rw [hx]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (x a) with h0 | h1
  · rw [h0]; simp
  · rw [h1]
    rw [hv a]
    ext i
    by_cases hi : i = a
    · subst hi; simp
    · simp [hi]

theorem lkf_schur (f : Multiplicative (Fin 3 → ZMod 2) →* Multiplicative (Fin 3 → ZMod 2))
    (hf : ∀ (g : ↥(StatedSL 3 (ZMod 2))) (x : Multiplicative (Fin 3 → ZMod 2)),
      f (natAct (StatedSL 3 (ZMod 2)) g x) = natAct (StatedSL 3 (ZMod 2)) g (f x)) :
    ∃ s : ZMod 2, ∀ x : Multiplicative (Fin 3 → ZMod 2),
      Multiplicative.toAdd (f x) = s • Multiplicative.toAdd x := by
  let F : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun x => Multiplicative.toAdd (f (Multiplicative.ofAdd x))
      map_zero' := by simp
      map_add' := fun x y => by simp [ofAdd_add, map_mul] }
  have htr : ∀ (a b : Fin 3), a ≠ b → ∀ x : Fin 3 → ZMod 2,
      F (x + Pi.single a (x b)) = F x + Pi.single a (F x b) := by
    intro a b hab x
    have h1 := hf (lkfTrans a b hab) (Multiplicative.ofAdd x)
    have h2 := lkf_natAct_trans a b hab x
    have h3 := lkf_natAct_trans a b hab (F x)
    have e1 : natAct (StatedSL 3 (ZMod 2)) (lkfTrans a b hab) (Multiplicative.ofAdd x)
        = Multiplicative.ofAdd (x + Pi.single a (x b)) := by
      rw [← h2]; rfl
    rw [e1] at h1
    have h4 : Multiplicative.toAdd (f (Multiplicative.ofAdd (x + Pi.single a (x b)))) =
        Multiplicative.toAdd (natAct (StatedSL 3 (ZMod 2)) (lkfTrans a b hab)
          (f (Multiplicative.ofAdd x))) := congrArg Multiplicative.toAdd h1
    show Multiplicative.toAdd (f (Multiplicative.ofAdd (x + Pi.single a (x b)))) = _
    rw [h4]
    exact h3
  obtain ⟨s, hs⟩ := lkf_schur_add F htr
  exact ⟨s, fun x => hs (Multiplicative.toAdd x)⟩

theorem lkf_natAct_mul (g : ↥(StatedSL 3 (ZMod 2))) (x y : Multiplicative (Fin 3 → ZMod 2)) :
    natAct (StatedSL 3 (ZMod 2)) g (x * y) =
      natAct (StatedSL 3 (ZMod 2)) g x * natAct (StatedSL 3 (ZMod 2)) g y := by
  simp [natAct, Matrix.mulVec_add]

def lkfNatHom (g : ↥(StatedSL 3 (ZMod 2))) :
    Multiplicative (Fin 3 → ZMod 2) →* Multiplicative (Fin 3 → ZMod 2) where
  toFun := natAct (StatedSL 3 (ZMod 2)) g
  map_one' := FFC.natAct_one_right g
  map_mul' := lkf_natAct_mul g

def lkfAct {k : ℕ} (g : ↥(StatedSL 3 (ZMod 2)))
    (m : Fin k → Multiplicative (Fin 3 → ZMod 2)) : Fin k → Multiplicative (Fin 3 → ZMod 2) :=
  fun i => natAct (StatedSL 3 (ZMod 2)) g (m i)

theorem lkf_act_mulSingle {k : ℕ} (g : ↥(StatedSL 3 (ZMod 2))) (j : Fin k)
    (x : Multiplicative (Fin 3 → ZMod 2)) :
    lkfAct g (Pi.mulSingle j x) = Pi.mulSingle j (natAct (StatedSL 3 (ZMod 2)) g x) := by
  funext l
  by_cases h : l = j
  · subst h; simp [lkfAct]
  · simp [lkfAct, Pi.mulSingle_eq_of_ne h, FFC.natAct_one_right]

def lkfActHom {k : ℕ} (g : ↥(StatedSL 3 (ZMod 2))) :
    (Fin k → Multiplicative (Fin 3 → ZMod 2)) →* (Fin k → Multiplicative (Fin 3 → ZMod 2)) :=
  MonoidHom.pi fun i => (lkfNatHom g).comp (Pi.evalMonoidHom _ i)

noncomputable def lkfB {k : ℕ}
    (φ : (Fin k → Multiplicative (Fin 3 → ZMod 2)) →* (Fin k → Multiplicative (Fin 3 → ZMod 2))) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun i j => Multiplicative.toAdd
    (φ (Pi.mulSingle j (Multiplicative.ofAdd (Pi.single 0 1))) i) 0

theorem lkf_apply {k : ℕ}
    (φ : (Fin k → Multiplicative (Fin 3 → ZMod 2)) →* (Fin k → Multiplicative (Fin 3 → ZMod 2)))
    (hφ : ∀ (g : ↥(StatedSL 3 (ZMod 2))) m, φ (lkfAct g m) = lkfAct g (φ m))
    (m : Fin k → Multiplicative (Fin 3 → ZMod 2)) (i : Fin k) (b : Fin 3) :
    Multiplicative.toAdd (φ m i) b = ∑ j, lkfB φ i j * Multiplicative.toAdd (m j) b := by
  have key : ∀ (j : Fin k) (x : Multiplicative (Fin 3 → ZMod 2)),
      Multiplicative.toAdd (φ (Pi.mulSingle j x) i) = lkfB φ i j • Multiplicative.toAdd x := by
    intro j
    obtain ⟨s, hs⟩ := lkf_schur ((Pi.evalMonoidHom _ i).comp (φ.comp (MonoidHom.mulSingle _ j)))
      (fun g x => by
        show φ (Pi.mulSingle j (natAct (StatedSL 3 (ZMod 2)) g x)) i =
          natAct (StatedSL 3 (ZMod 2)) g (φ (Pi.mulSingle j x) i)
        rw [← lkf_act_mulSingle, hφ]
        rfl)
    have hs0 : s = lkfB φ i j := by
      have := congrFun (hs (Multiplicative.ofAdd (Pi.single 0 1))) 0
      simpa [lkfB] using this.symm
    intro x
    rw [← hs0]
    exact hs x
  have hm : m = ∏ j, Pi.mulSingle j (m j) := (Finset.univ_prod_mulSingle m).symm
  conv_lhs => rw [hm]
  rw [map_prod, Finset.prod_apply, toAdd_prod, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j (m j)]
  simp

theorem lkf_B_comp {k : ℕ}
    (φ ψ : (Fin k → Multiplicative (Fin 3 → ZMod 2)) →* (Fin k → Multiplicative (Fin 3 → ZMod 2)))
    (hφ : ∀ (g : ↥(StatedSL 3 (ZMod 2))) m, φ (lkfAct g m) = lkfAct g (φ m)) :
    lkfB (φ.comp ψ) = lkfB φ * lkfB ψ := by
  ext i j
  rw [Matrix.mul_apply]
  exact lkf_apply φ hφ (ψ (Pi.mulSingle j (Multiplicative.ofAdd (Pi.single 0 1)))) i 0

theorem lkf_B_id {k : ℕ} :
    lkfB (MonoidHom.id (Fin k → Multiplicative (Fin 3 → ZMod 2))) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [lkfB]
  · simp [lkfB, Pi.mulSingle_eq_of_ne h, Matrix.one_apply_ne h]

theorem lkf_B_inj {k : ℕ}
    (φ ψ : (Fin k → Multiplicative (Fin 3 → ZMod 2)) →* (Fin k → Multiplicative (Fin 3 → ZMod 2)))
    (hφ : ∀ (g : ↥(StatedSL 3 (ZMod 2))) m, φ (lkfAct g m) = lkfAct g (φ m))
    (hψ : ∀ (g : ↥(StatedSL 3 (ZMod 2))) m, ψ (lkfAct g m) = lkfAct g (ψ m))
    (h : lkfB φ = lkfB ψ) : φ = ψ := by
  refine MonoidHom.ext fun m => funext fun i => Multiplicative.toAdd.injective (funext fun b => ?_)
  rw [lkf_apply φ hφ, lkf_apply ψ hψ, h]

theorem lkf_exists_iso {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)} {I : Subgroup Y}
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥Λ}
    (h : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia Λ I ⊥ π) :
    ∃ θ : ↥I ≃* Multiplicative (Fin 3 → ZMod 2),
      ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥I) (hu : (π γ : MulAut Y) (u : Y) ∈ I),
        θ ⟨(π γ : MulAut Y) (u : Y), hu⟩ = natAct (StatedSL 3 (ZMod 2)) γ (θ u) := by
  obtain ⟨f, hfs, hfk, hfe⟩ :=
    FFC.RealizesVia.secMap (D := FFModel.nat (StatedSL 3 (ZMod 2))) rfl h
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  refine ⟨(MulEquiv.ofBijective f ⟨hfi, hfs⟩).trans Subgroup.topEquiv, fun γ u hu => ?_⟩
  exact hfe γ u hu

theorem lkf_coord {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)} {k : ℕ}
    (hds : DirectSumOfCopies Λ ⊤ ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k) :
    ∃ (π : ↥(StatedSL 3 (ZMod 2)) →* ↥Λ)
      (Φ : (Fin k → Multiplicative (Fin 3 → ZMod 2)) ≃* Y),
      ∀ (g : ↥(StatedSL 3 (ZMod 2))) (m : Fin k → Multiplicative (Fin 3 → ZMod 2)),
        Φ (lkfAct g m) = (π g : MulAut Y) (Φ m) := by
  obtain ⟨I, π₀, -, hind, hsup, hreal₀⟩ := hds
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥Λ, π = π₀ := ⟨π₀, rfl⟩
  have hreal : ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia Λ (I i) ⊥ π := by
    rw [hπ]; exact hreal₀
  choose θ hθ using fun i => lkf_exists_iso (hreal i)
  have hIind : iSupIndep I := fun i => by
    have := hind i
    rw [bot_sup_eq] at this
    exact disjoint_iff.2 this
  have hIsup : ⨆ i, I i = ⊤ := by rwa [bot_sup_eq] at hsup
  let ϕ : ∀ i, Multiplicative (Fin 3 → ZMod 2) →* Y := fun i =>
    (I i).subtype.comp (θ i).symm.toMonoidHom
  have hrange : ∀ i, (ϕ i).range = I i := by
    intro i
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ((θ i).symm n).2
    · intro hy
      exact ⟨θ i ⟨y, hy⟩, by simp [ϕ]⟩
  have hϕinj : ∀ i, Function.Injective (ϕ i) := fun i =>
    Subtype.val_injective.comp (θ i).symm.injective
  have hcomm : Pairwise fun i j : Fin k =>
      ∀ (x y : Multiplicative (Fin 3 → ZMod 2)), Commute (ϕ i x) (ϕ j y) :=
    fun i j _ x y => Commute.all _ _
  obtain ⟨Φ0, hΦ0⟩ : ∃ Φ0 : (Fin k → Multiplicative (Fin 3 → ZMod 2)) →* Y,
      Φ0 = MonoidHom.noncommPiCoprod ϕ hcomm := ⟨_, rfl⟩
  have hΦinj : Function.Injective Φ0 := by
    rw [hΦ0]
    exact MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ (by simpa only [hrange] using hIind)
      hϕinj
  have hΦsurj : Function.Surjective Φ0 := by
    rw [← MonoidHom.range_eq_top, hΦ0, MonoidHom.noncommPiCoprod_range]
    simp only [hrange]
    exact hIsup
  refine ⟨π, MulEquiv.ofBijective Φ0 ⟨hΦinj, hΦsurj⟩, fun g m => ?_⟩
  show Φ0 (lkfAct g m) = (π g : MulAut Y) (Φ0 m)
  have key : Φ0.comp (lkfActHom g) = ((π g : MulAut Y) : Y →* Y).comp Φ0 := by
    refine MonoidHom.functions_ext _ _ _ fun i x => ?_
    show Φ0 (lkfAct g (Pi.mulSingle i x)) = (π g : MulAut Y) (Φ0 (Pi.mulSingle i x))
    rw [lkf_act_mulSingle, hΦ0, MonoidHom.noncommPiCoprod_mulSingle,
      MonoidHom.noncommPiCoprod_mulSingle]
    have hu : (π g : MulAut Y) (((θ i).symm x : ↥(I i)) : Y) ∈ I i :=
      (hreal i).2.2.2.1 (π g) _ ((θ i).symm x).2
    have h1 := hθ i g ((θ i).symm x) hu
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 : (⟨(π g : MulAut Y) (((θ i).symm x : ↥(I i)) : Y), hu⟩ : ↥(I i)) =
        (θ i).symm (natAct (StatedSL 3 (ZMod 2)) g x) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    exact (congrArg Subtype.val h2).symm
  exact DFunLike.congr_fun key m

theorem lkf_embed {Y : Type} [CommGroup Y] {Λ : Subgroup (MulAut Y)} {k : ℕ}
    (hds : DirectSumOfCopies Λ ⊤ ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k)
    (H : Subgroup (MulAut Y)) (hH : ∀ c ∈ H, ∀ l ∈ Λ, c * l = l * c) :
    ∃ ψ : ↥H →* Matrix.GeneralLinearGroup (Fin k) (ZMod 2), Function.Injective ψ := by
  obtain ⟨π, Φ, hΦ⟩ := lkf_coord hds
  let φ : MulAut Y → ((Fin k → Multiplicative (Fin 3 → ZMod 2)) →*
      (Fin k → Multiplicative (Fin 3 → ZMod 2))) := fun c =>
    Φ.symm.toMonoidHom.comp (c.toMonoidHom.comp Φ.toMonoidHom)
  have hφ_apply : ∀ c m, φ c m = Φ.symm (c (Φ m)) := fun c m => rfl
  have hφ_equiv : ∀ c ∈ H, ∀ g m, φ c (lkfAct g m) = lkfAct g (φ c m) := by
    intro c hc g m
    have h1 : c ((π g : MulAut Y) (Φ m)) = (π g : MulAut Y) (c (Φ m)) := by
      have := congrArg (fun f : MulAut Y => f (Φ m)) (hH c hc (π g) (π g).2)
      simpa using this
    rw [hφ_apply, hΦ g m, h1]
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hΦ g (φ c m), hφ_apply, MulEquiv.apply_symm_apply]
  have hφ_mul : ∀ c d, φ (c * d) = (φ c).comp (φ d) := by
    intro c d
    refine MonoidHom.ext fun m => ?_
    simp [hφ_apply]
  have hφ_one : φ 1 = MonoidHom.id _ := by
    refine MonoidHom.ext fun m => ?_
    simp [hφ_apply]
  have hφ_inj : ∀ c d, φ c = φ d → c = d := by
    intro c d h
    ext y
    obtain ⟨m, rfl⟩ := Φ.surjective y
    have := congrArg (fun f => Φ (f m)) h
    simpa [hφ_apply] using this
  let R : ↥H →* Matrix (Fin k) (Fin k) (ZMod 2) :=
    { toFun := fun c => lkfB (φ (c : MulAut Y))
      map_one' := by
        simp only [Subgroup.coe_one]
        rw [hφ_one]
        exact lkf_B_id
      map_mul' := fun c d => by
        simp only [Subgroup.coe_mul]
        rw [hφ_mul]
        exact lkf_B_comp _ _ (hφ_equiv c c.2) }
  refine ⟨R.toHomUnits, fun c d hcd => ?_⟩
  have h1 : R c = R d := by simpa using congrArg Units.val hcd
  have h2 : φ c = φ d := lkf_B_inj _ _ (hφ_equiv c c.2) (hφ_equiv d d.2) h1
  exact Subtype.ext (hφ_inj _ _ h2)

theorem lkf_card_GL_dvd (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k < 4) :
    Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) ∣ 168 := by
  interval_cases k
  · rw [Matrix.card_GL_field, ZMod.card]; decide
  · rw [Matrix.card_GL_field, ZMod.card]; decide

end CFSG.Quasithin
