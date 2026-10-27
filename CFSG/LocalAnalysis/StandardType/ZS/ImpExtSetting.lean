module

public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialFrame
public import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K] {U : Type} [AddCommGroup U] [Module K U]

@[expose] noncomputable def phiForm (f : Module.Basis (Fin 4) K U) : QuadraticForm K U :=
  (QuadraticMap.weightedSumSquares K fun i : Fin 4 => if i = 3 then (-1 : K) else 1).comp
    f.equivFun.toLinearMap

end Matrices

section Inputs

variable (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def SplitOfIrred (G : Subgroup (U ≃ₗ[ZMod p] U)) (l : ℕ) : Prop :=
  ∀ F ≤ G, ReflGen p F → IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) →
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l →
    (∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) → SplitSupport F l

@[expose] def LemmaOneSeven (G H : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∀ a ∈ G, IsRefl p a →
    (¬ ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c) →
      ∀ W : Submodule (ZMod p) U,
        (∀ g ∈ Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, g w ∈ W) →
          W = ⊥ ∨ W = ⊤

@[expose] def CentreOrderBound (G : Subgroup (U ≃ₗ[ZMod p] U)) (l : ℕ) : Prop :=
  ∀ X ≤ G, ReflGen p X → SplitSupport X l → ∀ z ∈ X, (∀ x ∈ X, z * x = x * z) → orderOf z ≤ 3

end Inputs

@[expose] def LemmaOneNineInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (U : Type) [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (G : Subgroup (U ≃ₗ[ZMod p] U)), p ≠ 2 → ReflGen p G →
      QTwoLin.TransvectionFree G → AbsIrred p G → ¬ Quasithin.SimsG4.IsImprimitiveOnV G →
        CentreOrderBound p G (Module.finrank (ZMod p) U - 1)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem absIrred_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hX : ReflGen p X)
    (hs : SplitSupport X l) : AbsIrred p (movedGroup X) := by
  apply absIrred_of_reflGen (reflGen_movedGroup hX)
  intro W hW
  let W' : Submodule (ZMod p) U :=
    W.map (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace X))
  have hW'le : W' ≤ HardMathSupport.Kantor79.commutatorSpace X := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  have hW'inv : ∀ h ∈ X, ∀ x ∈ W', h x ∈ W' := by
    intro h hh x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem : restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨h, hh⟩ ∈ movedGroup X :=
      ⟨⟨h, hh⟩, rfl⟩
    have hWy : (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨h, hh⟩) y ∈ W := hW _ hmem y hy
    exact ⟨_, hWy, by simp [restrictHom_apply]⟩
  have hres := hs.2.2 W' bot_le hW'le hW'inv
  rcases hres with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hw' : (w : U) ∈ W' := ⟨w, hw, rfl⟩
    rw [hbot] at hw'
    exact Subtype.ext (by simpa using hw')
  · right
    rw [Submodule.eq_top_iff']
    intro w
    have hw' : (w : U) ∈ W' := by rw [htop]; exact w.2
    obtain ⟨y, hy, hyw⟩ := hw'
    have : y = w := Subtype.ext hyw
    rwa [this] at hy

private lemma orderOf_coe_mul {X : Subgroup (U ≃ₗ[ZMod p] U)} (x y : X) :
    orderOf ((x : U ≃ₗ[ZMod p] U) * (y : U ≃ₗ[ZMod p] U)) = orderOf (x * y) := by
  rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]

theorem dmax_movedGroup_iff {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hs : SplitSupport X l)
    (d : ℕ) : DMax p (movedGroup X) d ↔ DMax p X d := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let φ := restrictHom X V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  have hord : ∀ x : X, orderOf (φ x) = orderOf x := fun x => orderOf_injective φ hinj x
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxr hyr
      have hx' : ((⟨x, hx⟩ : X) : U ≃ₗ[ZMod p] U) = x := rfl
      have hy' : ((⟨y, hy⟩ : X) : U ≃ₗ[ZMod p] U) = y := rfl
      have hle := h.1 (φ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ (φ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
        (isRefl_restrictHom_of_isRefl hs hxr) (isRefl_restrictHom_of_isRefl hs hyr)
      rw [← map_mul, hord (⟨x, hx⟩ * ⟨y, hy⟩)] at hle
      rw [← hx', ← hy', orderOf_coe_mul]
      exact hle
    · obtain ⟨x, hx, y, hy, hxr, hyr, hord'⟩ := h.2
      obtain ⟨x', rfl⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨y', rfl⟩ := MonoidHom.mem_range.mp hy
      refine ⟨x', x'.2, y', y'.2, isRefl_of_isRefl_restrictHom hs hxr,
        isRefl_of_isRefl_restrictHom hs hyr, ?_⟩
      rw [← map_mul, hord (x' * y')] at hord'
      exact (orderOf_coe_mul x' y').trans hord'
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxr hyr
      obtain ⟨x', rfl⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨y', rfl⟩ := MonoidHom.mem_range.mp hy
      have hle := h.1 x' x'.2 y' y'.2 (isRefl_of_isRefl_restrictHom hs hxr)
        (isRefl_of_isRefl_restrictHom hs hyr)
      rw [← map_mul, hord (x' * y')]
      exact (orderOf_coe_mul x' y').symm.trans_le hle
    · obtain ⟨x, hx, y, hy, hxr, hyr, hord'⟩ := h.2
      refine ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, φ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩,
        isRefl_restrictHom_of_isRefl hs hxr, isRefl_restrictHom_of_isRefl hs hyr, ?_⟩
      rw [← map_mul, hord (⟨x, hx⟩ * ⟨y, hy⟩)]
      exact (orderOf_coe_mul ⟨x, hx⟩ ⟨y, hy⟩).symm.trans hord'

structure ImpExtSetting (G H : Subgroup (U ≃ₗ[ZMod p] U)) (d : ℕ) : Prop where
  four_le_finrank : 4 ≤ Module.finrank (ZMod p) U
  reflGen : ReflGen p G
  absIrred : AbsIrred p G
  primitive : ¬ Quasithin.SimsG4.IsImprimitiveOnV G
  transvectionFree : QTwoLin.TransvectionFree G
  dmax : DMax p G d
  three_lt : 3 < d
  noOrth : ∀ X ≤ G, ReflGen p X → SplitSupport X (Module.finrank (ZMod p) U - 1) →
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) →
    (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ¬ IsOrthType p (movedGroup X)
  H_le : H ≤ G
  reflGen_H : ReflGen p H
  splitSupport : SplitSupport H (Module.finrank (ZMod p) U - 1)
  dmax_H : DMax p H d
  maximal : ∀ X ≤ G, ReflGen p X → SplitSupport X (Module.finrank (ZMod p) U - 1) →
    DMax p X d → Nat.card X ≤ Nat.card H
  imprimitive : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup H)

namespace ImpExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ}

theorem finrank_centralizerSpace [Module.Finite (ZMod p) U] (S : ImpExtSetting G H d) :
    Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
  obtain ⟨hcompl, hfinrank, _⟩ := S.splitSupport
  have hsup : HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H = ⊤ :=
    hcompl.sup_eq_top
  have hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ :=
    hcompl.inf_eq_bot
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H)
  rw [hsup, hinf, finrank_top, finrank_bot, add_zero] at hsum
  rw [hfinrank] at hsum
  have h4 : 4 ≤ Module.finrank (ZMod p) U := S.four_le_finrank
  omega

theorem card_le_of_orderOf (S : ImpExtSetting G H d) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hXG : X ≤ G) (hX : ReflGen p X) (hs : SplitSupport X (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = d) :
    Nat.card X ≤ Nat.card H := by
  have hDMax : DMax p X d := by
    refine ⟨?_, hd⟩
    intro x hx y hy hxr hyr
    exact S.dmax.1 x (hXG hx) y (hXG hy) hxr hyr
  exact S.maximal X hXG hX hs hDMax

theorem exists_standardBasis (hp : p ≠ 2) [Module.Finite (ZMod p) U] (S : ImpExtSetting G H d) :
    ∃ (e : Module.Basis (Fin (Module.finrank (ZMod p) U - 1)) (ZMod p)
        (HardMathSupport.Kantor79.commutatorSpace H))
      (j₀ j₁ : Fin (Module.finrank (ZMod p) U - 1)) (ζ : (ZMod p)ˣ), j₀ ≠ j₁ ∧
      (movedGroup H = gmmn p e j₀ j₁ ζ ∨ movedGroup H = g2mmn p e j₀ j₁ ζ) := by
  let n := Module.finrank (ZMod p) U - 1
  let V := HardMathSupport.Kantor79.commutatorSpace H
  have hn : Module.finrank (ZMod p) V = n := S.splitSupport.2.1
  have habs : AbsIrred p (movedGroup H) := absIrred_movedGroup S.reflGen_H S.splitSupport
  have hgen : movedGroup H = Subgroup.closure {t | t ∈ movedGroup H ∧ GGLinRefl t} :=
    reflGen_movedGroup S.reflGen_H
  obtain ⟨b, hbmon⟩ := ggRC_monomial_of_imprimitive hn (movedGroup H) habs hgen S.imprimitive
  obtain ⟨b', hb'mon, hb'perm, -⟩ := ggRC_monomial_frame hp b (movedGroup H) habs hgen hbmon
  have h3 : 3 ≤ n := by
    have h4 := S.four_le_finrank
    omega
  let j₀ : Fin n := ⟨0, by omega⟩
  let j₁ : Fin n := ⟨1, by omega⟩
  have hne : j₀ ≠ j₁ := by
    intro h
    have hval : j₀.val = j₁.val := congrArg Fin.val h
    simp [j₀, j₁] at hval
  by_cases hsign : ∃ i : Fin n, diagMap p b' (fun j => if j = i then -1 else 1) ∈ movedGroup H
  · obtain ⟨ζ, _hζ, hAeq⟩ := eq_g2mmn_of_permMap_mem hp b' hgen hb'mon hb'perm hsign
      (i₀ := j₀) (i₁ := j₁) hne
    exact ⟨b', j₀, j₁, ζ, hne, Or.inr hAeq⟩
  · have hsign' : ∀ i : Fin n, diagMap p b' (fun j => if j = i then -1 else 1) ∉ movedGroup H := by
      simpa [not_exists] using hsign
    obtain ⟨ζ, hAeq⟩ := eq_gmmn_of_permMap_mem hp b' hgen hb'mon hb'perm hsign'
      (i₀ := j₀) (i₁ := j₁) hne
    exact ⟨b', j₀, j₁, ζ, hne, Or.inl hAeq⟩

private lemma mem_closure_of_preserves [Module.Finite (ZMod p) U] {W : Submodule (ZMod p) U}
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hH : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) (ha : ∀ w ∈ W, a w ∈ W) :
    ∀ g ∈ Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, g w ∈ W := by
  let P : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | ∀ w ∈ W, g w ∈ W}
      mul_mem' := by
        intro x y hx hy w hw
        rw [LinearEquiv.mul_apply]
        exact hx (y w) (hy w hw)
      one_mem' := by intro w hw; exact hw
      inv_mem' := by
        intro x hx w hw
        have hle : W.map (x : U →ₗ[ZMod p] U) ≤ W := by
          rw [Submodule.map_le_iff_le_comap]
          intro v hv
          exact hx v hv
        have hdim : Module.finrank (ZMod p) (W.map (x : U →ₗ[ZMod p] U)) =
            Module.finrank (ZMod p) W := LinearEquiv.finrank_map_eq _ _
        have hmap_x : W.map (x : U →ₗ[ZMod p] U) = W :=
          Submodule.eq_of_le_of_finrank_eq hle hdim
        have hmap_inv : W.map (x.symm : U →ₗ[ZMod p] U) = W := by
          rw [Submodule.map_symm_eq_iff]
          exact hmap_x
        have hmem : x.symm w ∈ W.map (x.symm : U →ₗ[ZMod p] U) :=
          Submodule.mem_map_of_mem hw
        rwa [hmap_inv] at hmem }
  have haP : a ∈ P := ha
  have hHP : H ≤ P := hH
  exact (Subgroup.closure_le _).mpr (Set.insert_subset haP hHP)

private lemma false_of_invariant_of_split [Module.Finite (ZMod p) U] (S : ImpExtSetting G H d)
    {W : Submodule (ZMod p) U}
    (hW : W = HardMathSupport.Kantor79.commutatorSpace H ∨ W = centralizerSpace H)
    (hres : W = ⊥ ∨ W = ⊤) : False := by
  have hlt : Module.finrank (ZMod p) W < Module.finrank (ZMod p) U := by
    rcases hW with hW | hW
    · rw [hW]
      have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
          Module.finrank (ZMod p) U - 1 := S.splitSupport.2.1
      have h4 : 4 ≤ Module.finrank (ZMod p) U := S.four_le_finrank
      omega
    · rw [hW]
      have h1 : Module.finrank (ZMod p) (centralizerSpace H) = 1 := finrank_centralizerSpace S
      have h4 : 4 ≤ Module.finrank (ZMod p) U := S.four_le_finrank
      omega
  have hpos : 0 < Module.finrank (ZMod p) W := by
    rcases hW with hW | hW
    · rw [hW]
      have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
          Module.finrank (ZMod p) U - 1 := S.splitSupport.2.1
      have h4 : 4 ≤ Module.finrank (ZMod p) U := S.four_le_finrank
      omega
    · rw [hW]
      have h1 : Module.finrank (ZMod p) (centralizerSpace H) = 1 := finrank_centralizerSpace S
      omega
  rcases hres with hbot | htop
  · rw [hbot, finrank_bot] at hpos
    omega
  · rw [htop, finrank_top] at hlt
    omega

theorem mem_mul_centralizer_of_map_eq [Module.Finite (ZMod p) U] (S : ImpExtSetting G H d)
    (h17 : LemmaOneSeven p G H) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (har : IsRefl p a)
    (hmap : (HardMathSupport.Kantor79.commutatorSpace H).map (a : U →ₗ[ZMod p] U) =
        HardMathSupport.Kantor79.commutatorSpace H ∨
      (centralizerSpace H).map (a : U →ₗ[ZMod p] U) = centralizerSpace H) :
    ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)), a = h * c := by
  by_contra hnot
  have hirr := h17 a ha har hnot
  have haW : ∀ W : Submodule (ZMod p) U,
      (W.map (a : U →ₗ[ZMod p] U) = W) → ∀ w ∈ W, a w ∈ W := by
    intro W hW w hw
    rw [← hW]
    exact Submodule.mem_map_of_mem hw
  rcases hmap with hmap | hmap
  · exact false_of_invariant_of_split (W := HardMathSupport.Kantor79.commutatorSpace H) S
      (Or.inl rfl)
      (hirr _ (mem_closure_of_preserves (fun h hh w hw => apply_mem_commutatorSpace hh hw)
        (haW _ hmap)))
  · exact false_of_invariant_of_split (W := centralizerSpace H) S (Or.inr rfl)
      (hirr _ (mem_closure_of_preserves
        (fun h hh w hw => by rw [show h w = w from (mem_centralizerSpace).mp hw h hh]; exact hw)
        (haW _ hmap)))

end ImpExtSetting

end CFSG.StandardType.ZS

end
