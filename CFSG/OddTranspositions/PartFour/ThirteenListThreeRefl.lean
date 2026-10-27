module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListCorrected
import CFSG.Fischer.Classification.Orthogonal3.Local

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification CFSG.LocalAnalysis.WeakClosure81 CFSG.Open

theorem exists_reflGroup_six_embedding {m : ℕ} (hm : 6 ≤ m) :
    ∀ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3), IsF3Form f →
      ∀ v : Fin m → ZMod 3, f v v = 1 →
      ∃ (f₆ : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)) (c : Fin 6 → ZMod 3),
        IsF3Form f₆ ∧ f₆ c c = 1 ∧ ∃ Φ : F3.reflGroup f₆ →* F3.reflGroup f,
          Function.Injective Φ ∧
          (Φ ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩ : GL (Fin m) (ZMod 3)) = F3.refl f v ∧
          (6 < m → ∀ g, (Φ g : GL (Fin m) (ZMod 3)) ≠ -1) := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro f hf v hv
    exact ⟨f, v, hf, hv, MonoidHom.id _, fun _ _ h => h, rfl, fun h => absurd h (lt_irrefl 6)⟩
  | succ m hm ih =>
    intro f hf v hv
    obtain ⟨u, hu, huv⟩ := F3.exists_norm_eq_perp hf (by omega) hv (one_ne_zero (α := ZMod 3))
    let e : F3.perpOne f u ≃ₗ[ZMod 3] (Fin m → ZMod 3) :=
      LinearEquiv.ofFinrankEq _ _ (by
        rw [F3.finrank_perpOne hu, Module.finrank_fin_fun, Nat.add_sub_cancel])
    have hfe : ∀ a b : F3.perpOne f u, restrictForm f e (e a) (e b) = f a b :=
      restrictForm_apply e
    have hvu : f v u = 0 := by rw [hf.symm]; exact huv
    obtain ⟨f₆, c, hf₆, hc, Φ, hΦ, hΦc, -⟩ := ih (restrictForm f e)
      (isF3Form_restrictForm hf hu e) (e ⟨v, F3.mem_perpOne.2 hvu⟩) (by rw [hfe]; exact hv)
    let ψ : F3.reflGroupPerp f u ≃* F3.reflGroup (restrictForm f e) :=
      (MonoidHom.ofInjective (perpToGL_injective e hf hu)).trans
        (MulEquiv.subgroupCongr (range_perpToGL e hfe))
    have hψ : ψ ⟨F3.refl f v, refl_mem_reflGroupPerp hv hvu⟩ =
        ⟨F3.refl (restrictForm f e) (e ⟨v, F3.mem_perpOne.2 hvu⟩), F3.refl_mem_reflGroup _⟩ :=
      Subtype.ext (perpToGL_refl e hfe hv hvu)
    refine ⟨f₆, c, hf₆, hc, (Subgroup.inclusion (F3.reflGroupPerp_le_reflGroup u)).comp
      (ψ.symm.toMonoidHom.comp Φ), ?_, ?_, fun _ g h => ?_⟩
    · exact (Subgroup.inclusion_injective (F3.reflGroupPerp_le_reflGroup u)).comp
        (ψ.symm.injective.comp hΦ)
    · have h1 : Φ ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩ =
          ⟨F3.refl (restrictForm f e) (e ⟨v, F3.mem_perpOne.2 hvu⟩), F3.refl_mem_reflGroup _⟩ :=
        Subtype.ext hΦc
      show ((ψ.symm (Φ ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩) : F3.reflGroupPerp f u) :
        GL (Fin (m + 1)) (ZMod 3)) = F3.refl f v
      rw [h1, ← hψ, MulEquiv.symm_apply_apply]
    · have hfix := F3.act_eq_of_mem_reflGroupPerp hf (ψ.symm (Φ g)).2
      change ((ψ.symm (Φ g) : F3.reflGroupPerp f u) : GL (Fin (m + 1)) (ZMod 3)) = -1 at h
      rw [h, F3.act_neg_one] at hfix
      exact F3.ne_zero_of_norm_one hu (F3.eq_zero_of_eq_neg hfix.symm)

theorem injective_mk_comp_reflGroup {m : ℕ} (hm : 4 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f) {H : Type} [Group H]
    {Φ : H →* F3.reflGroup f} (hΦ : Function.Injective Φ)
    (hne : ∀ g, (Φ g : GL (Fin m) (ZMod 3)) ≠ -1) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center (F3.reflGroup f))).comp Φ) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => hΦ ?_
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
  rcases F3.coe_eq_of_mem_center hf hm hg with h | h
  · rw [map_one]
    exact Subtype.ext h
  · exact absurd h (hne g)

private theorem eq_of_mem_zpowers_of_mul_self {G : Type} [Group G] {g x : G} (hg : g * g = 1)
    (hx : x ∈ Subgroup.zpowers g) (hx1 : x ≠ 1) : x = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two, hg]
  rw [← Int.emod_add_ediv_mul k 2, zpow_add, zpow_mul', h2, one_zpow, mul_one] at hx1 ⊢
  rcases Int.emod_two_eq k with h | h <;> rw [h] at hx1 ⊢
  · exact absurd (zpow_zero g) hx1
  · exact zpow_one g

private theorem orthReflSet_three_eq {m : ℕ}
    (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)) :
    orthReflSet 3 m f = F3.reflSet f := by
  ext g
  simp only [orthReflSet, F3.reflSet, fischerTransvections, Set.mem_setOf_eq,
    show (-2 : ZMod 3) = 1 by decide]

theorem exists_sevenNine_of_reflQuot {G : Type} [Group G] {m : ℕ} (hm : 7 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (φ : G ≃* F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f)) {g₀ : G}
    (hg₀ : ∃ h : F3.reflGroup f, (h : GL (Fin m) (ZMod 3)) ∈ F3.reflSet f ∧
      φ g₀ = QuotientGroup.mk h) :
    ∃ L : Subgroup G, g₀ ∈ L ∧
      IsSevenNineGroup ↥L {x : ↥L | (x : G) ∈ Subgroup.zpowers g₀ ∧ x ≠ 1} := by
  obtain ⟨h, hh, hφh⟩ := hg₀
  obtain ⟨v, hv, hvh⟩ := F3.mem_reflSet_iff.1 hh
  obtain ⟨f₆, c, hf₆, hc, Φ, hΦ, hΦc, hne⟩ := exists_reflGroup_six_embedding (by omega) f hf v hv
  have hκ := injective_mk_comp_reflGroup (by omega) hf hΦ (hne (by omega))
  let θ : F3.reflGroup f₆ →* G :=
    φ.symm.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (F3.reflGroup f))).comp Φ)
  have hθ : Function.Injective θ := φ.symm.injective.comp hκ
  have hθc : θ ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩ = g₀ := by
    have hΦh : Φ ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩ = h := Subtype.ext (hΦc.trans hvh)
    show φ.symm (QuotientGroup.mk (Φ ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩)) = g₀
    rw [hΦh, ← hφh, MulEquiv.symm_apply_apply]
  have hrr : (⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩ : F3.reflGroup f₆) *
      ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩ = 1 := Subtype.ext (F3.refl_mul_self c)
  have hg₀sq : g₀ * g₀ = 1 := by rw [← hθc, ← map_mul, hrr, map_one]
  have hg₀L : g₀ ∈ θ.range := ⟨_, hθc⟩
  have hmem : F3.refl f₆ c ∈ orthReflSet 3 6 f₆ := by
    rw [orthReflSet_three_eq]
    exact F3.refl_mem_reflSet hc
  refine ⟨θ.range, hg₀L, Or.inr ⟨f₆, hf₆.symm, hf₆.nondeg,
    Or.inl ⟨(MonoidHom.ofInjective hθ).symm.trans
      (MulEquiv.subgroupCongr (congrArg Subgroup.closure (orthReflSet_three_eq f₆).symm)),
      fun d hd => ?_⟩⟩⟩
  have hd' : (d : G) = g₀ :=
    eq_of_mem_zpowers_of_mul_self hg₀sq hd.1 fun h1 => hd.2 (Subtype.ext h1)
  have hed : (MonoidHom.ofInjective hθ).symm d = ⟨F3.refl f₆ c, F3.refl_mem_reflGroup c⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (hd'.trans hθc.symm)
  show (((MonoidHom.ofInjective hθ).symm d : F3.reflGroup f₆) : GL (Fin 6) (ZMod 3)) ∈
    orthReflSet 3 6 f₆
  rw [hed]
  exact hmem

theorem isReflModel_of_center_eq_bot {G : Type} [Group G] {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hZ : Subgroup.center (F3.reflGroup f) = ⊥)
    (φ : G ≃* F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f)) {D : Set G}
    (hD : ∀ d ∈ D, ∃ h : F3.reflGroup f, (h : GL (Fin m) (ZMod 3)) ∈ F3.reflSet f ∧
      φ d = QuotientGroup.mk h) :
    IsReflModel 3 m f G D := by
  let ε : F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f) ≃* F3.reflGroup f :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨(φ.trans ε).trans
    (MulEquiv.subgroupCongr (congrArg Subgroup.closure (orthReflSet_three_eq f).symm)),
    fun d hd => ?_⟩
  obtain ⟨h, hh, hφh⟩ := hD d hd
  have hε : ε (φ d) = h := by
    rw [hφh]
    rfl
  show ((ε (φ d) : F3.reflGroup f) : GL (Fin m) (ZMod 3)) ∈ orthReflSet 3 m f
  rw [hε, orthReflSet_three_eq]
  exact hh

theorem exists_reflQuot_data {G : Type} [Group G] {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (φ : G ≃* F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f)) {D : Set G}
    (hD : ∀ d ∈ D, ∃ h : F3.reflGroup f, (h : GL (Fin m) (ZMod 3)) ∈ F3.reflSet f ∧
      φ d = QuotientGroup.mk h) :
    ∃ e : G ≃* ↥(Subgroup.closure (orthReflSet 3 m f)) ⧸
        Subgroup.center ↥(Subgroup.closure (orthReflSet 3 m f)),
      ∀ d ∈ D, ∃ r : ↥(Subgroup.closure (orthReflSet 3 m f)),
        (r : GL (Fin m) (ZMod 3)) ∈ orthReflSet 3 m f ∧ e d = QuotientGroup.mk r := by
  let κ : F3.reflGroup f ≃* ↥(Subgroup.closure (orthReflSet 3 m f)) :=
    MulEquiv.subgroupCongr (congrArg Subgroup.closure (orthReflSet_three_eq f).symm)
  let ψ : F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f) ≃*
      ↥(Subgroup.closure (orthReflSet 3 m f)) ⧸
        Subgroup.center ↥(Subgroup.closure (orthReflSet 3 m f)) :=
    QuotientGroup.congr _ _ κ (Subgroup.map_center_eq κ)
  refine ⟨φ.trans ψ, fun d hd => ?_⟩
  obtain ⟨h, hh, hφh⟩ := hD d hd
  refine ⟨κ h, ?_, ?_⟩
  · show (h : GL (Fin m) (ZMod 3)) ∈ orthReflSet 3 m f
    rw [orthReflSet_three_eq]
    exact hh
  · rw [MulEquiv.trans_apply, hφh]
    rfl

section List

variable {X : Type} [Group X] {s : X}

private noncomputable def equivQuotientCenter (hZ : Subgroup.center X = ⊥) :
    X ≃* X ⧸ Subgroup.center X :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center X))
    ⟨(injective_iff_map_eq_one _).2 fun x hx => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ] at hx
      exact Subgroup.mem_bot.mp hx, QuotientGroup.mk'_surjective _⟩

theorem oddTranspListAlt_of_reflSeven (hZ : Subgroup.center X = ⊥) {m : ℕ} (hm : 7 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hsym : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hM : fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    OddTranspListAlt X s := by
  obtain ⟨φ, hφ⟩ := hM
  exact Or.inr (Or.inr (Or.inr (Or.inl (exists_sevenNine_of_reflQuot hm ⟨hsym, hnd⟩
    ((equivQuotientCenter hZ).trans φ) ((hφ (QuotientGroup.mk s)).mp (IsConj.refl _))))))

private theorem forall_mem_zpowers_top {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hZ : Subgroup.center X = ⊥) (hs : s * s = 1)
    (φ : X ⧸ Subgroup.center X ≃* F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f))
    (hφs : ∃ h : F3.reflGroup f, (h : GL (Fin m) (ZMod 3)) ∈ F3.reflSet f ∧
      φ (QuotientGroup.mk s) = QuotientGroup.mk h) :
    ∀ d ∈ {x : ↥(⊤ : Subgroup X) | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1},
      ∃ h : F3.reflGroup f, (h : GL (Fin m) (ZMod 3)) ∈ F3.reflSet f ∧
        (Subgroup.topEquiv.trans ((equivQuotientCenter hZ).trans φ)) d = QuotientGroup.mk h := by
  intro d hd
  have hds : (d : X) = s := eq_of_mem_zpowers_of_mul_self hs hd.1 fun h1 => hd.2 (Subtype.ext h1)
  obtain ⟨h, hh, hφh⟩ := hφs
  refine ⟨h, hh, ?_⟩
  show φ (QuotientGroup.mk (d : X)) = QuotientGroup.mk h
  rw [hds, hφh]

theorem oddTranspListAlt_of_reflSix_center (hZ : Subgroup.center X = ⊥) (hs : s * s = 1)
    {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (hsym : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) (hZR : Subgroup.center (F3.reflGroup f) = ⊥)
    (hM : fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    OddTranspListAlt X s := by
  obtain ⟨φ, hφ⟩ := hM
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⊤, Subgroup.mem_top s, Or.inr ⟨f, hsym, hnd, Or.inl
    (isReflModel_of_center_eq_bot hZR (Subgroup.topEquiv.trans ((equivQuotientCenter hZ).trans φ))
      (forall_mem_zpowers_top hZ hs φ ((hφ (QuotientGroup.mk s)).mp (IsConj.refl _))))⟩⟩)))

theorem exists_reflQuot_top_of_refl (hZ : Subgroup.center X = ⊥) (hs : s * s = 1) {m : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hM : fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) :
    ∃ e : ↥(⊤ : Subgroup X) ≃* ↥(Subgroup.closure (orthReflSet 3 m f)) ⧸
        Subgroup.center ↥(Subgroup.closure (orthReflSet 3 m f)),
      ∀ d ∈ {x : ↥(⊤ : Subgroup X) | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1},
        ∃ r : ↥(Subgroup.closure (orthReflSet 3 m f)),
          (r : GL (Fin m) (ZMod 3)) ∈ orthReflSet 3 m f ∧ e d = QuotientGroup.mk r := by
  obtain ⟨φ, hφ⟩ := hM
  exact exists_reflQuot_data (Subgroup.topEquiv.trans ((equivQuotientCenter hZ).trans φ))
    (forall_mem_zpowers_top hZ hs φ ((hφ (QuotientGroup.mk s)).mp (IsConj.refl _)))

end List

theorem oddTranspListThreeTranspReflSixQuot_holds :
    ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
      CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
      Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
      fusionOddCore X ≤ Subgroup.center X →
      derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
      (∀ d ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
        ∀ e ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x},
          orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
      Subgroup.center X = ⊥ →
      ∀ f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3), (∀ x y, f x y = f y x) →
        (∀ x, (∀ y, f x y = 0) → x = 0) →
        Subgroup.center ↥(Subgroup.closure (fischerTransvections (fun x y => f x y)
          fun v => f v v = 1)) ≠ ⊥ →
        fischerCentralQuotientModel {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}
          (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
          (fischerTransvections (fun x y => f x y) fun v => f v v = 1) →
        OddTranspListAlt X s := by
  intro X _ _ s hs _ _ _ _ _ _ hZ f hsym hnd _ hM
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  obtain ⟨e, he⟩ := exists_reflQuot_top_of_refl hZ hs2 hM
  exact Or.inr (Or.inr (Or.inr (Or.inl
    ⟨⊤, Subgroup.mem_top s, Or.inr ⟨f, hsym, hnd, Or.inr ⟨e, he⟩⟩⟩)))

end CFSG.OddTranspositions.PartFour
