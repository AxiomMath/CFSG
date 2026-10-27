module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLData
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLNormalizes
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLWeyl
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLCentres
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLBasis
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLPhiAct
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFaith
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelActs
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6Dep E6Dep.ZL

open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

@[expose] def GGE6DepZLCoord (Bs L : Subgroup G) (x : G) (hxBs : x ∈ Bs)
    (ι : Additive ↥Bs ≃+ Vec6) : Prop :=
  ι (Additive.ofMul ⟨x, hxBs⟩) = kappa ∧
    (∀ φ ∈ ggAutomizer L Bs, ∃ g ∈ closureU, ActsAs ι φ g) ∧
    (∀ g ∈ closureU, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ g)

theorem zl_frame_abs {V : Type} [AddCommGroup V] [Finite V] (hcard : Nat.card V = 3 ^ 6)
    (hexp : ∀ v : V, 3 • v = 0) {Φ : V →+ Vec6} {σ : Fin 6 → V →+ V} {x : V}
    (hΦ1 : ∀ v, kappa ⬝ᵥ Φ v = 0) (hΦ2 : ∀ u : Vec6, kappa ⬝ᵥ u = 0 → ∃ v, Φ v = u)
    (hΦ3 : ∀ v, Φ v = 0 ↔ v ∈ AddSubgroup.zmultiples x) (hx : x ≠ 0)
    (hσΦ : ∀ i v, Φ (σ i v) = Φ v - Φ v i • cartanE6 i) (hσx : ∀ i, σ i x = x)
    (hσσ : ∀ i v, σ i (σ i v) = v)
    (hcob : x ∈ AddSubgroup.closure {u | ∃ (i : Fin 6) (v : V), u = σ i v - v}) :
    ∃ ι : V ≃+ Vec6, (∃ a : ZMod 3, a ≠ 0 ∧ ι x = a • kappa) ∧
      (∀ v, Φ v = cartanM.mulVec (ι v)) ∧ ∀ i v, ι (σ i v) = (indepGens i).mulVec (ι v) := by
  obtain ⟨h, hhΦ, hσ⟩ := zl_frame_centres hexp hΦ2 hΦ3 hx hσΦ hσx hσσ
  exact zl_frame_basis hcard hexp hΦ1 hΦ3 hx hhΦ hσ hcob

theorem zl_coord_scale {Bs L : Subgroup G} {x : G} {hxBs : x ∈ Bs} {ι : Additive ↥Bs ≃+ Vec6}
    (hx : ∃ a : ZMod 3, a ≠ 0 ∧ ι (Additive.ofMul ⟨x, hxBs⟩) = a • kappa)
    (h₁ : ∀ φ ∈ ggAutomizer L Bs, ∃ g ∈ closureU, ActsAs ι φ g)
    (h₂ : ∀ g ∈ closureU, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ g) :
    ∃ ι' : Additive ↥Bs ≃+ Vec6, GGE6DepZLCoord Bs L x hxBs ι' := by
  obtain ⟨a, ha, hax⟩ := hx
  let u : (ZMod 3)ˣ := Units.mk0 a ha
  let ι' : Additive ↥Bs ≃+ Vec6 := ι.trans (DistribMulAction.toAddEquiv Vec6 u⁻¹)
  have hι' : ∀ v, ι' v = ((u⁻¹ : (ZMod 3)ˣ) : ZMod 3) • ι v := fun v => rfl
  have hact : ∀ (φ : MulAut ↥Bs) (g : Mat6), ActsAs ι φ g → ActsAs ι' φ g := by
    intro φ g h b
    rw [hι', hι', h b, Matrix.mulVec_smul]
  refine ⟨ι', ?_, fun φ hφ => ?_, fun g hg => ?_⟩
  · rw [hι', hax, smul_smul]
    simp [u, inv_mul_cancel₀ ha]
  · obtain ⟨g, hg, h⟩ := h₁ φ hφ
    exact ⟨g, hg, hact φ g h⟩
  · obtain ⟨φ, hφ, h⟩ := h₂ g hg
    exact ⟨φ, hφ, hact φ g h⟩

theorem mem_zpowers_of_mem_zmultiples {Bs : Subgroup G} {x : G} (hxBs : x ∈ Bs) {c : ↥Bs}
    (h : Additive.ofMul c ∈ AddSubgroup.zmultiples (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) :
    (c : G) ∈ Subgroup.zpowers x := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h1 : (⟨x, hxBs⟩ : ↥Bs) ^ k = c := by
    apply Additive.ofMul.injective
    rw [ofMul_zpow]
    exact hk
  rw [← h1]
  rfl

variable [Finite G]

theorem ggE6Dep_frameLIn (hRig : GGLabelRigidInput) (hZL : GGE6DepZLKnown)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) (hnt : GGNoTransvection 3 Bs) {K : Subgroup G}
    (hE : GGE6DepPerpCfg 3 Bs L K) (hxL : x ∈ L) :
    ∃ (hxBs : x ∈ Bs) (ι : Additive ↥Bs ≃+ Vec6), GGE6DepZLCoord Bs L x hxBs ι := by
  classical
  obtain ⟨hBsN, _, _, _, ψ, Φ, _, w, -, hcard, hZ, hmodel, hcob⟩ :=
    ggE6Dep_known_data_zl hRig hZL hcfg hinn hE
  obtain ⟨-, hcardBs, -⟩ := hE
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hxord : orderOf x = 3 := hcfg.orderOf_x
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hxord
  have hwN := ggE6Dep_zl_weyl_normalizes hcfg hBsN hmodel
  obtain ⟨hΦinj, hΦrange, -, -, -, -, -, hcl8, -, hcl10, -, -⟩ := hmodel
  refine ⟨hxBs, ?_⟩
  haveI : IsMulCommutative ↥Bs := hBs.1
  let σ : Fin 6 → Additive ↥Bs →+ Additive ↥Bs := fun i =>
    (MulEquiv.toAdditive (ggConjAut Bs (hwN i))).toAddMonoidHom
  have hσ : ∀ (i : Fin 6) (v : Additive ↥Bs),
      σ i v = Additive.ofMul (ggConjAut Bs (hwN i) (Additive.toMul v)) := fun _ _ => rfl
  have hσA : ∀ i, ggConjAut Bs (hwN i) ∈ ggAutomizer L Bs := fun i =>
    ggConjAut_mem_ggAutomizer (w i).2 (hwN i)
  have hΦ1 := phiB_kappa hBsN hcard hΦrange hΦinj
  have hΦ2 := phiB_surj hBsN hcard hΦrange hΦinj
  have hΦ3 := phiB_ker hcfg hBsN hΦinj hxBs
  have hσΦ : ∀ (i : Fin 6) (v : Additive ↥Bs),
      phiB hBsN Φ (σ i v) = phiB hBsN Φ v - phiB hBsN Φ v i • cartanE6 i := by
    intro i v
    rw [hσ, phiB_refl hBsN hwN hcl8 i v, adRefl_E6_eq]
  have hσx : ∀ i, σ i (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) =
      Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) := by
    intro i
    rw [hσ]
    congr 1
    apply Subtype.ext
    show ((w i : ↥L) : G) * x * ((w i : ↥L) : G)⁻¹ = x
    have hc : x * ((w i : ↥L) : G) = ((w i : ↥L) : G) * x :=
      Subgroup.mem_centralizer_iff.mp (hLx (w i).2) x (Set.mem_singleton x)
    rw [← hc]
    group
  have hnx : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) ≠ 0 := by
    intro h
    apply hx1
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := Additive.ofMul.injective h
    exact congrArg Subtype.val h1
  have hσσ : ∀ (i : Fin 6) (v : Additive ↥Bs), σ i (σ i v) = v := by
    intro i v
    have hθ : ggConjAut Bs (hwN i) * ggConjAut Bs (hwN i) ∈ ggAutomizer L Bs :=
      Subgroup.mul_mem _ (hσA i) (hσA i)
    have hθb : ∀ b : ↥Bs,
        ((b⁻¹ * (ggConjAut Bs (hwN i) * ggConjAut Bs (hwN i)) b : ↥Bs) : G) ∈
          Subgroup.zpowers x := by
      intro b
      apply mem_zpowers_of_mem_zmultiples hxBs
      apply (hΦ3 _).mp
      have h1 := phiB_refl hBsN hwN hcl8 i (Additive.ofMul b)
      have h2 := phiB_refl hBsN hwN hcl8 i (Additive.ofMul (ggConjAut Bs (hwN i) b))
      rw [toMul_ofMul] at h1 h2
      rw [MulAut.mul_apply, ofMul_mul, ofMul_inv, map_add, map_neg, h2, h1, adRefl_E6_invol]
      exact neg_add_cancel _
    have h3 := zl_aut_eq_one hxBs hx1 hBs hnt hLx hθ hθb
    have h4 : ggConjAut Bs (hwN i) (ggConjAut Bs (hwN i) (Additive.toMul v)) =
        Additive.toMul v := by
      rw [← MulAut.mul_apply, h3]
      rfl
    rw [hσ, hσ, toMul_ofMul, h4]
    rfl
  have hcardV : Nat.card (Additive ↥Bs) = 3 ^ 6 := by
    rw [← hcardBs]
    exact (Nat.card_congr Additive.ofMul).symm
  have hexp : ∀ v : Additive ↥Bs, 3 • v = 0 := by
    intro v
    have h1 : (Additive.toMul v) ^ 3 = 1 := Subtype.ext (hBs.2 _ (Additive.toMul v).2)
    have h2 := congrArg Additive.ofMul h1
    rwa [ofMul_pow, ofMul_toMul, ofMul_one] at h2
  have hker : (⟨x, hxL⟩ : ↥L) ∈ ψ.ker := by
    apply hZ
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hLx l.2) x (Set.mem_singleton x)).symm
  have hord : orderOf (⟨x, hxL⟩ : ↥L) = 3 := by
    rw [← hxord]
    exact Subgroup.orderOf_mk x hxL
  have hcobV : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) ∈ AddSubgroup.closure
      {u | ∃ (i : Fin 6) (v : Additive ↥Bs), u = σ i v - v} :=
    phiB_cobdry hBsN hwN hxBs hxL (hcob _ hker hord)
  obtain ⟨ι, ⟨a, ha, hιx⟩, hΦι, hισ⟩ :=
    zl_frame_abs hcardV hexp hΦ1 hΦ2 hΦ3 hnx hσΦ hσx hσσ hcobV
  have h3 : ∀ g ∈ closureU, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ g := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact ⟨ggConjAut Bs (hwN i), hσA i, fun b => hισ i (Additive.ofMul b)⟩
    | one => exact ⟨1, one_mem _, ActsAs.one ι⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨φ, hφ, hφg⟩ := ihg
      obtain ⟨ψ', hψ', hψh⟩ := ihh
      exact ⟨φ * ψ', mul_mem hφ hψ', hφg.mul hψh⟩
  have h2 : ∀ φ ∈ ggAutomizer L Bs, ∃ g ∈ closureU, ActsAs ι φ g := by
    intro φ hφ
    obtain ⟨n, hnL, hnN, hφn⟩ := mem_ggAutomizer_iff.mp hφ
    have hφeq : φ = ggConjAut Bs hnN := by
      ext b
      rw [ggConjAut_apply]
      exact hφn b
    obtain ⟨u, hu⟩ := phiB_weyl hBsN hcl10 hnL hnN
    obtain ⟨g, hg, hgv⟩ := exists_closureU_of_weyl u
    obtain ⟨ψ', hψ'A, hψ'g⟩ := h3 g hg
    refine ⟨g, hg, ?_⟩
    have hsame : ∀ b : ↥Bs, phiB hBsN Φ (Additive.ofMul (φ b)) =
        phiB hBsN Φ (Additive.ofMul (ψ' b)) := by
      intro b
      have h1 := hu (Additive.ofMul b)
      rw [toMul_ofMul] at h1
      rw [hφeq, h1, hΦι (Additive.ofMul (ψ' b)), hψ'g b, hgv, ← hΦι]
    have hψ'invx : ψ'⁻¹ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
      ggAutomizer_fix_of_centralizes hxBs hLx ψ'⁻¹ (Subgroup.inv_mem _ hψ'A)
    have hθb : ∀ b : ↥Bs, ((b⁻¹ * (ψ'⁻¹ * φ) b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
      intro b
      have h1 : Additive.ofMul ((ψ' b)⁻¹ * φ b) ∈
          AddSubgroup.zmultiples (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
        apply (hΦ3 _).mp
        rw [ofMul_mul, ofMul_inv, map_add, map_neg, hsame b]
        exact neg_add_cancel _
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h1
      have hk' : (⟨x, hxBs⟩ : ↥Bs) ^ k = (ψ' b)⁻¹ * φ b := by
        apply Additive.ofMul.injective
        rw [ofMul_zpow]
        exact hk
      have hφb : φ b = ψ' b * (⟨x, hxBs⟩ : ↥Bs) ^ k := by
        rw [hk']
        group
      have h2 : (ψ'⁻¹ * φ) b = b * (⟨x, hxBs⟩ : ↥Bs) ^ k := by
        rw [MulAut.mul_apply, hφb, map_mul, map_zpow, hψ'invx]
        simp
      rw [h2]
      have h3 : b⁻¹ * (b * (⟨x, hxBs⟩ : ↥Bs) ^ k) = (⟨x, hxBs⟩ : ↥Bs) ^ k := by group
      rw [h3]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    have hθ1 := zl_aut_eq_one hxBs hx1 hBs hnt hLx
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hψ'A) hφ) hθb
    have hφψ : φ = ψ' := by
      have h5 := congrArg (fun θ => ψ' * θ) hθ1
      simpa using h5
    rw [hφψ]
    exact hψ'g
  exact zl_coord_scale ⟨a, ha, hιx⟩ h2 h3

end CFSG.StandardType

end
