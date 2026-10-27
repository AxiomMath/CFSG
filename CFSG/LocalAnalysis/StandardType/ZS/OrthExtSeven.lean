module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtRoots
public import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.OrthRefl
public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.LocalAnalysis.StandardType.ZS.MovedGroup
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.ClassicalGroups.Orthogonal.TwoHyperplanes.Basic
public import CFSG.ClassicalGroups.Orthogonal.TwoHyperplanes.Generation
public import CFSG.ClassicalGroups.Orthogonal.NormClass.Generation
public import CFSG.ClassicalGroups.Orthogonal.Represents
public import CFSG.LieType.Universal.SpinOmega.Reflections
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

@[expose] def IsPrimOrthSub (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (X : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ReflGen p X ∧ SplitSupport X (Module.finrank (ZMod p) U - 1) ∧
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) ∧ IsOrthType p (movedGroup X) ∧
    ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)

structure OrthExtSetting (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (G H : Subgroup (U ≃ₗ[ZMod p] U)) : Prop where
  four_le : 4 ≤ Module.finrank (ZMod p) U
  five_le_of_eq_three : p = 3 → 5 ≤ Module.finrank (ZMod p) U
  rGroup : IsRGroup p G
  irred : IrredOnSection G ⊥ ⊤
  primitive : ¬ Quasithin.SimsG4.IsImprimitiveOnV G
  le : H ≤ G
  sub : IsPrimOrthSub p H
  maxCard : ∀ X : Subgroup (U ≃ₗ[ZMod p] U), X ≤ G → IsPrimOrthSub p X → Nat.card X ≤ Nat.card H

@[expose] def IsOrthOvergroup (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (G H K : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  K ≤ G ∧ H ≤ K ∧ ReflGen p K ∧ IrredOnSection K ⊥ ⊤ ∧ IsOrthType p K

structure LemmaTwoSevenData (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (G H B : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) : Prop where
  setting : OrthExtSetting p G H
  mem_of_le : ∀ b ∈ G, IsRefl p b →
    HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H
  mem : h ∈ H
  isRefl : IsRefl p h
  split : IsCentralizingSplit p G H B h

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open Module in
private theorem finrank_centralizerSpace_eq_of_splitSupport [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hH : SplitSupport H l) :
    Module.finrank (ZMod p) (centralizerSpace H) = Module.finrank (ZMod p) U - l := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H)
  rw [hH.1.inf_eq_bot, hH.1.sup_eq_top, finrank_bot, finrank_top, hH.2.1] at h
  omega

private theorem commutatorSpace_le_or_le_centralizerSpace_of_splitSupport
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hH : SplitSupport H l)
    {W : Submodule (ZMod p) U} (hW : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) :
    HardMathSupport.Kantor79.commutatorSpace H ≤ W ∨ W ≤ centralizerSpace H := by
  have hXinv : ∀ h ∈ H, ∀ x ∈ W ⊓ HardMathSupport.Kantor79.commutatorSpace H, h x ∈
      W ⊓ HardMathSupport.Kantor79.commutatorSpace H := by
    intro h hh x hx
    exact ⟨hW h hh x hx.1, apply_mem_commutatorSpace hh hx.2⟩
  rcases hH.2.2 (W ⊓ HardMathSupport.Kantor79.commutatorSpace H) bot_le inf_le_right hXinv with
    hX | hX
  · refine Or.inr fun w hw => ?_
    rw [mem_centralizerSpace]
    intro h hh
    have hmem : h w - w ∈ W ⊓ HardMathSupport.Kantor79.commutatorSpace H :=
      ⟨sub_mem (hW h hh w hw) hw, Submodule.subset_span ⟨h, hh, w, rfl⟩⟩
    rw [hX] at hmem
    exact sub_eq_zero.mp hmem
  · exact Or.inl (hX ▸ inf_le_left)

private theorem false_of_mixed_of_splitSupport [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {H₁ H₂ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs₁ : SplitSupport H₁ (Module.finrank (ZMod p) U - 1))
    (hs₂ : SplitSupport H₂ (Module.finrank (ZMod p) U - 1))
    (hle : centralizerSpace H₁ ≤ HardMathSupport.Kantor79.commutatorSpace H₂)
    (hV : HardMathSupport.Kantor79.commutatorSpace H₁ ≤ centralizerSpace H₂ ∨
      HardMathSupport.Kantor79.commutatorSpace H₂ ≤ centralizerSpace H₁) : False := by
  have hEq : HardMathSupport.Kantor79.commutatorSpace H₂ = centralizerSpace H₁ := by
    rcases hV with hV | hV
    · have hdisj : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓
          HardMathSupport.Kantor79.commutatorSpace H₂ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hmem : x ∈ HardMathSupport.Kantor79.commutatorSpace H₂ ⊓ centralizerSpace H₂ :=
          ⟨hx.2, hV hx.1⟩
        rwa [hs₂.1.inf_eq_bot] at hmem
      refine le_antisymm ?_ hle
      intro x hx
      have hxsup : x ∈ HardMathSupport.Kantor79.commutatorSpace H₁ ⊔ centralizerSpace H₁ := by
        rw [hs₁.1.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxsup
      have hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace H₂ := hle hb
      have haV : a ∈ HardMathSupport.Kantor79.commutatorSpace H₂ := by
        have hxa : a = x - b := by rw [← hab]; abel
        rw [hxa]
        exact Submodule.sub_mem _ hx hbV
      have haBot : a ∈ (⊥ : Submodule (ZMod p) U) := by
        rw [← hdisj]
        exact ⟨ha, haV⟩
      have hazero : a = 0 := by simpa using haBot
      rw [hazero, zero_add] at hab
      rwa [← hab]
    · exact le_antisymm hV hle
  have hfin₁ : Module.finrank (ZMod p) (centralizerSpace H₁) = 1 := by
    have h := finrank_centralizerSpace_eq_of_splitSupport hs₁
    omega
  have hfin₂ : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₂) =
      Module.finrank (ZMod p) U - 1 := hs₂.2.1
  rw [hEq, hfin₁] at hfin₂
  omega

theorem irredOnSection_sup_of_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {H₁ H₂ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs₁ : SplitSupport H₁ (Module.finrank (ZMod p) U - 1))
    (hs₂ : SplitSupport H₂ (Module.finrank (ZMod p) U - 1))
    (hle : centralizerSpace H₁ ≤ HardMathSupport.Kantor79.commutatorSpace H₂) :
    IrredOnSection (H₁ ⊔ H₂) ⊥ ⊤ := by
  have hp' := hp
  intro W hbot htop hW
  have hW₁ : ∀ h ∈ H₁, ∀ w ∈ W, h w ∈ W := fun h hh => hW h (Subgroup.mem_sup_left hh)
  have hW₂ : ∀ h ∈ H₂, ∀ w ∈ W, h w ∈ W := fun h hh => hW h (Subgroup.mem_sup_right hh)
  have hr₁ := commutatorSpace_le_or_le_centralizerSpace_of_splitSupport hs₁ hW₁
  have hr₂ := commutatorSpace_le_or_le_centralizerSpace_of_splitSupport hs₂ hW₂
  rcases hr₁ with h1 | h1 <;> rcases hr₂ with h2 | h2
  · right
    rw [eq_top_iff]
    calc (⊤ : Submodule (ZMod p) U) =
        HardMathSupport.Kantor79.commutatorSpace H₁ ⊔ centralizerSpace H₁ :=
          hs₁.1.sup_eq_top.symm
      _ ≤ W := sup_le h1 (hle.trans h2)
  · exact (false_of_mixed_of_splitSupport h3 hs₁ hs₂ hle (Or.inl (h1.trans h2))).elim
  · exact (false_of_mixed_of_splitSupport h3 hs₁ hs₂ hle (Or.inr (h2.trans h1))).elim
  · left
    rw [eq_bot_iff]
    calc W ≤ centralizerSpace H₁ ⊓ centralizerSpace H₂ := le_inf h1 h2
      _ ≤ HardMathSupport.Kantor79.commutatorSpace H₂ ⊓ centralizerSpace H₂ :=
          le_inf (inf_le_left.trans hle) inf_le_right
      _ = ⊥ := hs₂.1.inf_eq_bot

open scoped commutatorElement

private theorem polar_self_eq_two_mul (Q : QuadraticForm (ZMod p) U) (x : U) :
    QuadraticMap.polar Q x x = 2 * Q x := by
  rw [QuadraticMap.polar_self, two_smul, two_mul]

private theorem mem_classRefl_of_isSquare_div (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0) {a : U} (ha : Q a ≠ 0) (hsq : IsSquare (Q a / c)) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ ClassRefl p Q c := by
  obtain ⟨mu, hmu⟩ := hsq
  have hmu0 : mu ≠ 0 := by
    intro h0
    have hzero : Q a / c = 0 := by rw [hmu, h0, mul_zero]
    rcases div_eq_zero_iff.mp hzero with h | h
    · exact ha h
    · exact hc h
  have hQa : Q a = mu * mu * c := by
    rw [← div_mul_cancel₀ (Q a) hc, hmu]
  have hQv : Q (mu⁻¹ • a) = c := by
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hQa]
    field_simp
  refine (mem_classRefl_iff hp hQ hc _).mpr ⟨mu⁻¹ • a, hQv, ?_⟩
  exact (CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (inv_ne_zero hmu0) a).symm

private theorem isSquare_div_or_isSquare_div {a b z : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hz : z ≠ 0) (h : ¬ IsSquare (a / b)) :
    IsSquare (z / a) ∨ IsSquare (z / b) := by
  by_contra hc
  rw [not_or] at hc
  have h1 : quadraticChar (ZMod p) (z / a) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hc.1
  have h2 : quadraticChar (ZMod p) (z / b) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hc.2
  have hab : quadraticChar (ZMod p) (a / b) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr h
  have hprod : (z / a) * (z / b) = (z / a) ^ 2 * (a / b) := by
    field_simp
  have hch : quadraticChar (ZMod p) ((z / a) * (z / b)) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  rw [hprod, map_mul, quadraticChar_sq_one' (div_ne_zero hz ha), hab, one_mul] at hch
  norm_num at hch

private theorem exists_reflect_mem_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hs : SplitSupport H l) (hl : 0 < l)
    (ho : IsOrthOn p Q H) :
    ∃ a : U, Q a ≠ 0 ∧ CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ H := by
  have hVne : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊥ := by
    intro hbot
    have h := hs.2.1
    rw [hbot, finrank_bot] at h
    omega
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hVne
    rw [hbot, HardMathSupport.Kantor79.commutatorSpace, Submodule.span_eq_bot]
    rintro w ⟨h, hh, v, rfl⟩
    rw [Subgroup.mem_bot.mp hh]
    simp
  rcases ho with hgen | ⟨c, hc, hgen⟩
  · have hSne : {t : U ≃ₗ[ZMod p] U | IsRefl p t ∧ IsIsom p Q t ∧
        HardMathSupport.Kantor79.movedSpace t ≤
          HardMathSupport.Kantor79.commutatorSpace H}.Nonempty := by
      by_contra h
      exact hHne (by rw [hgen, Set.not_nonempty_iff_eq_empty.mp h, Subgroup.closure_empty])
    obtain ⟨t, htrefl, htiso, htmoved⟩ := hSne
    have htH : t ∈ H := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨htrefl, htiso, htmoved⟩
    obtain ⟨a, hQa, hta⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ htrefl htiso
    have ha0 : a ≠ 0 := fun h => hQa (by rw [h]; exact QuadraticMap.map_zero Q)
    have ht_eq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q a :=
      DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ htrefl htiso
        (isRefl_reflect hp hQa) (isIsom_reflect Q a) ha0 hta
        (reflect_apply_self hQa)
    exact ⟨a, hQa, ht_eq ▸ htH⟩
  · have hSne : {t : U ≃ₗ[ZMod p] U | t ∈ ClassRefl p Q c ∧
        HardMathSupport.Kantor79.movedSpace t ≤
          HardMathSupport.Kantor79.commutatorSpace H}.Nonempty := by
      by_contra h
      exact hHne (by rw [hgen, Set.not_nonempty_iff_eq_empty.mp h, Subgroup.closure_empty])
    obtain ⟨t, htclass, htmoved⟩ := hSne
    obtain ⟨a, hQa, ht_eq⟩ := (mem_classRefl_iff hp hQ hc t).mp htclass
    have htH : t ∈ H := by
      rw [hgen]
      exact Subgroup.subset_closure ⟨htclass, htmoved⟩
    exact ⟨a, hQa ▸ hc, ht_eq ▸ htH⟩

private theorem exists_centralizerSpace_eq_span_of_isOrthOn
    [Module.Finite (ZMod p) U] (h4 : 4 ≤ Module.finrank (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) (ho : IsOrthOn p Q H) :
    ∃ e : U, e ≠ 0 ∧ centralizerSpace H = Submodule.span (ZMod p) {e} ∧ Q e ≠ 0 ∧
      HardMathSupport.Kantor79.commutatorSpace H =
        LinearMap.ker (QuadraticMap.polarBilin Q e) := by
  have hfin : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have h := finrank_centralizerSpace_eq_of_splitSupport hs
    have h1 : 1 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) h4
    omega
  have hne : centralizerSpace H ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : centralizerSpace H = Submodule.span (ZMod p) {e} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin he he0
  have hIso : ∀ g ∈ H, IsIsom p Q g := fun g hg => IsOrthOn.isIsom ho hg
  have hQe : Q e ≠ 0 := by
    intro hQe0
    have hpole : QuadraticMap.polar Q e e = 0 := by
      rw [polar_self_eq_two_mul, hQe0, mul_zero]
    have hemem : e ∈ HardMathSupport.Kantor79.commutatorSpace H := by
      rw [mem_commutatorSpace_iff_forall_polar_eq_zero hQ hIso hs.1]
      intro u hu
      rw [hspan] at hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hpole, mul_zero]
    have hbot : e ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hs.1.inf_eq_bot]
      exact ⟨hemem, he⟩
    exact he0 (by simpa using hbot)
  refine ⟨e, he0, hspan, hQe, ?_⟩
  apply Submodule.ext
  intro v
  rw [mem_commutatorSpace_iff_forall_polar_eq_zero hQ hIso hs.1]
  constructor
  · intro hv
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
    exact hv e he
  · intro hv u hu
    rw [hspan] at hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at hv
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hv, mul_zero]

private theorem reflect_mem_of_mem_commutatorSpace (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hgen : H = Subgroup.closure {t : U ≃ₗ[ZMod p] U | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H})
    {x : U} (hx : x ∈ HardMathSupport.Kantor79.commutatorSpace H) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ H := by
  rw [hgen]
  by_cases hQx : Q x = 0
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQx]
    exact Subgroup.one_mem _
  · refine Subgroup.subset_closure
      ⟨isRefl_reflect hp hQx, isIsom_reflect Q x, ?_⟩
    exact (movedSpace_reflect_le_span Q x).trans
      ((Submodule.span_singleton_le_iff_mem x _).mpr hx)

private theorem reflPairsPerp_subset_of_isOrthOn_full (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {e : U}
    (hgen : H = Subgroup.closure {t : U ≃ₗ[ZMod p] U | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H})
    (hker : HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q e)) :
    CFSG.ClassicalGroups.Orthogonal.reflPairsPerp Q e ⊆ H := by
  intro g hg
  obtain ⟨a, b, hae, hbe, -, rfl⟩ := hg
  have haV : a ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hker, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
    exact hae
  have hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hker, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
    exact hbe
  exact Subgroup.mul_mem _
    (reflect_mem_of_mem_commutatorSpace hp hQ hgen haV)
    (reflect_mem_of_mem_commutatorSpace hp hQ hgen hbV)

private theorem reflPairsPerp_subset_of_isOrthOn_class (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) (ho : IsOrthOn p Q H)
    (hd : p = 3 → ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {e : U} (hker : HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q e))
    {c : ZMod p} (hc : c ≠ 0)
    (hgen : H = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ ClassRefl p Q c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H}) :
    CFSG.ClassicalGroups.Orthogonal.reflPairsPerp Q e ⊆ H := by
  intro g hg
  obtain ⟨a, b, hae, hbe, hab, rfl⟩ := hg
  have haV : a ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hker, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
    exact hae
  have hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hker, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
    exact hbe
  have hIso : ∀ g ∈ H, IsIsom p Q g := fun g hg => IsOrthOn.isIsom ho hg
  by_cases hp3 : p = 3
  · exfalso
    have hle : H ≤ Subgroup.closure (ClassRefl p Q c) := by
      rw [hgen]
      exact Subgroup.closure_mono fun t ht => ht.1
    obtain ⟨x, hx, y, hy, hxr, hyr, hgt⟩ := hd hp3
    have := orderOf_mul_le_three_of_classRefl_three hp3 hQ hc (hle hx) (hle hy) hxr hyr
    omega
  · have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
    rw [hgen]
    have hS : ClassicalGroups.Orthogonal.PolarNondegOn Q
        (HardMathSupport.Kantor79.commutatorSpace H) :=
      polarNondegOn_commutatorSpace hQ hIso hs.1
    refine Subgroup.closure_mono ?_
      (CFSG.ClassicalGroups.Orthogonal.reflect_mul_reflect_mem_closure_of_map_eq
        (ZMod.prime_ne_zero p 2 hp) h3 hS haV hbV hab hc)
    rintro t ⟨x, hx, rfl⟩
    obtain ⟨hxV, hQx⟩ := hx
    refine ⟨(mem_classRefl_iff hp hQ hc _).mpr ⟨x, hQx, rfl⟩, ?_⟩
    exact (movedSpace_reflect_le_span Q x).trans
      ((Submodule.span_singleton_le_iff_mem x _).mpr hxV)

private theorem reflPairsPerp_subset_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) (ho : IsOrthOn p Q H)
    (hd : p = 3 → ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {e : U} (hker : HardMathSupport.Kantor79.commutatorSpace H =
      LinearMap.ker (QuadraticMap.polarBilin Q e)) :
    CFSG.ClassicalGroups.Orthogonal.reflPairsPerp Q e ⊆ H := by
  rcases ho with hgen | ⟨c, hc, hgen⟩
  · exact reflPairsPerp_subset_of_isOrthOn_full hp hQ hgen hker
  · exact reflPairsPerp_subset_of_isOrthOn_class hp hQ hs (Or.inr ⟨c, hc, hgen⟩) hd hker hc hgen

private theorem le_closure_classRefl_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (ho : IsOrthOn p Q H) {c : ZMod p} (hc : c ≠ 0)
    (hsq : ∀ x : U, Q x ≠ 0 → CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ H →
      IsSquare (Q x / c)) :
    H ≤ Subgroup.closure (ClassRefl p Q c) := by
  rcases ho with hgen | ⟨c₀, hc₀, hgen⟩
  · rw [hgen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨htrefl, htiso, htmoved⟩
    obtain ⟨a, hQa, hta⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ htrefl htiso
    have ha0 : a ≠ 0 := fun h => hQa (by rw [h]; exact QuadraticMap.map_zero Q)
    have ht_eq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q a :=
      DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ htrefl htiso
        (isRefl_reflect hp hQa) (isIsom_reflect Q a) ha0 hta
        (reflect_apply_self hQa)
    have hmemH : CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ H := by
      rw [hgen, ← ht_eq]
      exact Subgroup.subset_closure ⟨htrefl, htiso, htmoved⟩
    rw [ht_eq]
    exact Subgroup.subset_closure
      (mem_classRefl_of_isSquare_div hp hQ hc hQa (hsq a hQa hmemH))
  · rw [hgen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨htclass, htmoved⟩
    obtain ⟨a, hQa, ht_eq⟩ := (mem_classRefl_iff hp hQ hc₀ t).mp htclass
    have hmemH : CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ H := by
      rw [hgen, ← ht_eq]
      exact Subgroup.subset_closure ⟨htclass, htmoved⟩
    rw [ht_eq]
    exact Subgroup.subset_closure
      (mem_classRefl_of_isSquare_div hp hQ hc (hQa ▸ hc₀) (hsq a (hQa ▸ hc₀) hmemH))

private theorem reflect_mul_reflect_mem_orthogonalGroup {Q : QuadraticForm (ZMod p) U} (a b : U) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q a * CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q a)
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q b)

private theorem reflect_mem_of_isSquare_div (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hKle : K ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ K)
    {x y : U} (hy : Q y ≠ 0) (hsq : IsSquare (Q x / Q y))
    (hyK : CFSG.ClassicalGroups.Orthogonal.reflect Q y ∈ K) :
    CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ K := by
  by_cases hQx : Q x = 0
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQx]
    exact K.one_mem
  · obtain ⟨mu, hmu⟩ := hsq
    have hmu0 : mu ≠ 0 := by
      intro h0
      have hzero : Q x / Q y = 0 := by rw [hmu, h0, mul_zero]
      rcases div_eq_zero_iff.mp hzero with h | h
      · exact hQx h
      · exact hy h
    have hQv : Q (mu⁻¹ • x) = Q y := by
      rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq]
      have hQx' : Q x = (mu * mu) * Q y := by
        rw [← div_mul_cancel₀ (Q x) hy, hmu]
      rw [hQx']
      field_simp
    have hX : ∀ a b : U, Q a = Q b →
        CFSG.ClassicalGroups.Orthogonal.reflect Q a *
          CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈
            TauCeti.QuadraticMap.orthogonalGroup Q := fun a b _ =>
      reflect_mul_reflect_mem_orthogonalGroup a b
    obtain ⟨k, hkO, hky⟩ :=
      CFSG.ClassicalGroups.Orthogonal.exists_mem_apply_eq_of_reflect_mul_reflect_mem
        (ZMod.prime_ne_zero p 2 hp) hQ (le_trans (by norm_num) h4) hX hy hQv
    have hres : CFSG.ClassicalGroups.Orthogonal.reflect Q x =
        k * CFSG.ClassicalGroups.Orthogonal.reflect Q y * k⁻¹ := by
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_conj hkO, hky]
      exact (CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (inv_ne_zero hmu0) x).symm
    have hcommK : ⁅k, CFSG.ClassicalGroups.Orthogonal.reflect Q y⁆ ∈ K :=
      hcomm (Subgroup.commutator_mem_commutator hkO (hKle hyK))
    have heq : CFSG.ClassicalGroups.Orthogonal.reflect Q x =
        ⁅k, CFSG.ClassicalGroups.Orthogonal.reflect Q y⁆ *
          CFSG.ClassicalGroups.Orthogonal.reflect Q y := by
      rw [hres, commutatorElement_def,
        mul_assoc (k * CFSG.ClassicalGroups.Orthogonal.reflect Q y * k⁻¹)
          (CFSG.ClassicalGroups.Orthogonal.reflect Q y)⁻¹
          (CFSG.ClassicalGroups.Orthogonal.reflect Q y),
        inv_mul_cancel, mul_one]
    rw [heq]
    exact K.mul_mem hcommK hyK

private theorem commutator_orthogonalGroup_le_sup_of_isOrthOn (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H₁ H₂ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs₁ : SplitSupport H₁ (Module.finrank (ZMod p) U - 1))
    (hs₂ : SplitSupport H₂ (Module.finrank (ZMod p) U - 1))
    (ho₁ : IsOrthOn p Q H₁) (ho₂ : IsOrthOn p Q H₂)
    (hd₁ : p = 3 → ∃ x ∈ H₁, ∃ y ∈ H₁, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hd₂ : p = 3 → ∃ x ∈ H₂, ∃ y ∈ H₂, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hle : centralizerSpace H₁ ≤ HardMathSupport.Kantor79.commutatorSpace H₂) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ H₁ ⊔ H₂ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨e₁, -, hspan₁, hQe₁, hker₁⟩ :=
    exists_centralizerSpace_eq_span_of_isOrthOn h4 hQ hs₁ ho₁
  obtain ⟨e₂, -, -, hQe₂, hker₂⟩ :=
    exists_centralizerSpace_eq_span_of_isOrthOn h4 hQ hs₂ ho₂
  have he₁V : e₁ ∈ centralizerSpace H₁ := by
    rw [hspan₁]
    exact Submodule.mem_span_singleton_self e₁
  have hef : QuadraticMap.polar Q e₁ e₂ = 0 := by
    have hmem : QuadraticMap.polar Q e₂ e₁ = 0 := by
      have h := hle he₁V
      rwa [hker₂, LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at h
    rwa [QuadraticMap.polar_comm Q e₁ e₂]
  have hpair₁ := reflPairsPerp_subset_of_isOrthOn hp hQ hs₁ ho₁ hd₁ hker₁
  have hpair₂ := reflPairsPerp_subset_of_isOrthOn hp hQ hs₂ ho₂ hd₂ hker₂
  refine CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_le_of_reflPairsPerp_subset
    h2 hQ h4 ?_ hQe₁ hQe₂ hef ?_ ?_
  · by_cases hp3 : p = 3
    · exact Or.inr (h43 hp3)
    · exact Or.inl (ZMod.prime_ne_zero p 3 hp3)
  · intro x hx
    exact Subgroup.mem_sup_left (hpair₁ hx)
  · intro x hx
    exact Subgroup.mem_sup_right (hpair₂ hx)

private theorem eq_closure_classRefl_sup_of_isOrthOn (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {H₁ H₂ : Subgroup (U ≃ₗ[ZMod p] U)}
    (ho₁ : IsOrthOn p Q H₁) (ho₂ : IsOrthOn p Q H₂) {y₀ : U} (hQy₀ : Q y₀ ≠ 0)
    (hy₀ : CFSG.ClassicalGroups.Orthogonal.reflect Q y₀ ∈ H₁)
    (hWitt : ∀ x y : U, Q y ≠ 0 → IsSquare (Q x / Q y) →
      CFSG.ClassicalGroups.Orthogonal.reflect Q y ∈ H₁ ⊔ H₂ →
      CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ H₁ ⊔ H₂)
    (hcase : ∀ x : U, Q x ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ H₁ ⊔ H₂ → IsSquare (Q x / Q y₀)) :
    H₁ ⊔ H₂ = Subgroup.closure (ClassRefl p Q (Q y₀)) := by
  apply le_antisymm
  · exact sup_le
      (le_closure_classRefl_of_isOrthOn hp hQ ho₁ hQy₀
        fun x hx hmem => hcase x hx (Subgroup.mem_sup_left hmem))
      (le_closure_classRefl_of_isOrthOn hp hQ ho₂ hQy₀
        fun x hx hmem => hcase x hx (Subgroup.mem_sup_right hmem))
  · refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    rw [mem_classRefl_iff hp hQ hQy₀ t] at ht
    obtain ⟨a, hQa, rfl⟩ := ht
    exact hWitt a y₀ hQy₀ (by rw [hQa, div_self hQy₀]; exact ⟨1, by norm_num⟩)
      (Subgroup.mem_sup_left hy₀)

private theorem orthogonalGroup_le_sup_of_nonsquare (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H₁ H₂ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hWitt : ∀ x y : U, Q y ≠ 0 → IsSquare (Q x / Q y) →
      CFSG.ClassicalGroups.Orthogonal.reflect Q y ∈ H₁ ⊔ H₂ →
      CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ H₁ ⊔ H₂)
    {y₀ x₁ : U} (hQy₀ : Q y₀ ≠ 0) (hQx₁ : Q x₁ ≠ 0)
    (hy₀ : CFSG.ClassicalGroups.Orthogonal.reflect Q y₀ ∈ H₁ ⊔ H₂)
    (hx₁ : CFSG.ClassicalGroups.Orthogonal.reflect Q x₁ ∈ H₁ ⊔ H₂)
    (hnsq : ¬ IsSquare (Q x₁ / Q y₀)) :
    TauCeti.QuadraticMap.orthogonalGroup Q ≤ H₁ ⊔ H₂ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine le_trans
    (CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_reflect h2 hQ) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨z, rfl⟩
  by_cases hQz : Q z = 0
  · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hQz]
    exact Subgroup.one_mem _
  · rcases isSquare_div_or_isSquare_div hQx₁ hQy₀ hQz hnsq with hsq | hsq
    · exact hWitt z x₁ hQx₁ hsq hx₁
    · exact hWitt z y₀ hQy₀ hsq hy₀

theorem isOrthType_sup_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U) (h43 : p = 3 → 5 ≤ Module.finrank (ZMod p) U)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H₁ H₂ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs₁ : SplitSupport H₁ (Module.finrank (ZMod p) U - 1))
    (hs₂ : SplitSupport H₂ (Module.finrank (ZMod p) U - 1))
    (ho₁ : IsOrthOn p Q H₁) (ho₂ : IsOrthOn p Q H₂)
    (hd₁ : p = 3 → ∃ x ∈ H₁, ∃ y ∈ H₁, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hd₂ : p = 3 → ∃ x ∈ H₂, ∃ y ∈ H₂, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hle : centralizerSpace H₁ ≤ HardMathSupport.Kantor79.commutatorSpace H₂) :
    IsOrthType p (H₁ ⊔ H₂) := by
  have hcomm := commutator_orthogonalGroup_le_sup_of_isOrthOn hp h4 h43 hQ hs₁ hs₂
    ho₁ ho₂ hd₁ hd₂ hle
  have hKle : H₁ ⊔ H₂ ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sup_le
      (fun g hg => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (IsOrthOn.isIsom ho₁ hg))
      (fun g hg => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (IsOrthOn.isIsom ho₂ hg))
  obtain ⟨y₀, hQy₀, hry₀⟩ :=
    exists_reflect_mem_of_isOrthOn hp hQ hs₁ (by have := h4; omega) ho₁
  have hry₀K : CFSG.ClassicalGroups.Orthogonal.reflect Q y₀ ∈ H₁ ⊔ H₂ :=
    Subgroup.mem_sup_left hry₀
  have hWitt : ∀ x y : U, Q y ≠ 0 → IsSquare (Q x / Q y) →
      CFSG.ClassicalGroups.Orthogonal.reflect Q y ∈ H₁ ⊔ H₂ →
      CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ H₁ ⊔ H₂ :=
    fun x y hy hsq hyK => reflect_mem_of_isSquare_div hp hQ h4 hKle hcomm hy hsq hyK
  by_cases hcase : ∀ x : U, Q x ≠ 0 →
      CFSG.ClassicalGroups.Orthogonal.reflect Q x ∈ H₁ ⊔ H₂ → IsSquare (Q x / Q y₀)
  · exact ⟨Q, hQ, Or.inr ⟨Q y₀, hQy₀,
      eq_closure_classRefl_sup_of_isOrthOn hp hQ ho₁ ho₂ hQy₀ hry₀ hWitt hcase⟩⟩
  · push Not at hcase
    obtain ⟨x₁, hQx₁, hrx₁K, hnsq⟩ := hcase
    refine ⟨Q, hQ, Or.inl ?_⟩
    intro g
    exact ⟨fun hg => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hKle hg),
      fun hg => orthogonalGroup_le_sup_of_nonsquare hp hQ hWitt hQy₀ hQx₁ hry₀K hrx₁K hnsq
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg)⟩

variable {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

theorem exists_isOrthOvergroup_of_isOrthOn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hXG : X ≤ G) (hX : ReflGen p X) (hXs : SplitSupport X (Module.finrank (ZMod p) U - 1))
    (hXd : p = 3 → ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hoH : IsOrthOn p Q H) (hoX : IsOrthOn p Q X)
    (hle : centralizerSpace H ≤ HardMathSupport.Kantor79.commutatorSpace X) :
    ∃ K, IsOrthOvergroup p G H K := by
  refine ⟨H ⊔ X, sup_le hS.le hXG, le_sup_left, hS.sub.1.sup hX, ?_, ?_⟩
  · exact irredOnSection_sup_of_le hp (le_trans (by norm_num) hS.four_le)
      hS.sub.2.1 hXs hle
  · exact isOrthType_sup_of_isOrthOn hp hS.four_le hS.five_le_of_eq_three hQ
      hS.sub.2.1 hXs hoH hoX (fun _ => hS.sub.2.2.2.2) hXd hle

theorem exists_isOrthOvergroup_of_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ G) (hgQ : IsIsom p Q g)
    (hle : centralizerSpace H ≤
      (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[ZMod p] U)) :
    ∃ K, IsOrthOvergroup p G H K := by
  have hXG : H.map (MulAut.conj g).toMonoidHom ≤ G := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using G.mul_mem (G.mul_mem hg (hS.le hy)) (G.inv_mem hg)
  have hX : ReflGen p (H.map (MulAut.conj g).toMonoidHom) := reflGen_map_conj g hS.sub.1
  have hXs : SplitSupport (H.map (MulAut.conj g).toMonoidHom)
      (Module.finrank (ZMod p) U - 1) := splitSupport_map_conj g hS.sub.2.1
  have hXd : p = 3 → ∃ x ∈ H.map (MulAut.conj g).toMonoidHom,
      ∃ y ∈ H.map (MulAut.conj g).toMonoidHom,
        IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    intro _
    obtain ⟨x, hx, y, hy, hxr, hyr, hgt⟩ := hS.sub.2.2.2.2
    refine ⟨(MulAut.conj g).toMonoidHom x, Subgroup.mem_map_of_mem _ hx,
      (MulAut.conj g).toMonoidHom y, Subgroup.mem_map_of_mem _ hy, ?_, ?_, ?_⟩
    · simpa [MulAut.conj_apply] using IsRefl.conj hxr g
    · simpa [MulAut.conj_apply] using IsRefl.conj hyr g
    · have hord : orderOf ((MulAut.conj g).toMonoidHom (x * y)) = orderOf (x * y) := by
        have h := MulEquiv.orderOf_eq (MulAut.conj g) (x * y)
        simpa [MulAut.conj_apply] using h
      rw [← map_mul, hord]
      exact hgt
  have hoX : IsOrthOn p Q (H.map (MulAut.conj g).toMonoidHom) := isOrthOn_map_conj hoH hgQ
  have hle' : centralizerSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace (H.map (MulAut.conj g).toMonoidHom) := by
    rw [commutatorSpace_map_conj (g := g)]
    exact hle
  exact exists_isOrthOvergroup_of_isOrthOn hp hS hQ hXG hX hXs hXd hoH hoX hle'

private theorem fixedSpace_eq_span_of_polar_sq_ne (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {g : U ≃ₗ[ZMod p] U} {f : U} (hf : f ∈ centralizerSpace H)
    (hgf : QuadraticMap.polarBilin Q (g f) f ^ 2 ≠ QuadraticMap.polarBilin Q f f ^ 2) :
    f ≠ 0 ∧ centralizerSpace H = Submodule.span (ZMod p) {f} ∧ Q f ≠ 0 ∧
      QuadraticMap.polar Q f f ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hIsoH : ∀ x ∈ H, IsIsom p Q x := fun x hx => IsOrthOn.isIsom hoH hx
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hgf (by simp)
  have hfinV : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have h := finrank_centralizerSpace_eq_of_splitSupport hS.sub.2.1
    have h4 := hS.four_le
    omega
  have hVH : centralizerSpace H = Submodule.span (ZMod p) {f} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfinV hf hf0
  have hQf : Q f ≠ 0 := by
    intro hQf0
    have hpolf : QuadraticMap.polar Q f f = 0 := by
      rw [polar_self_eq_two_mul, hQf0, mul_zero]
    have hfmem : f ∈ HardMathSupport.Kantor79.commutatorSpace H := by
      rw [mem_commutatorSpace_iff_forall_polar_eq_zero hQ hIsoH hS.sub.2.1.1]
      intro u hu
      rw [hVH] at hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hpolf, mul_zero]
    have hbot : f ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hS.sub.2.1.1.inf_eq_bot]
      exact ⟨hfmem, hf⟩
    exact hf0 (by simpa using hbot)
  refine ⟨hf0, hVH, hQf, ?_⟩
  rw [polar_self_eq_two_mul]
  exact mul_ne_zero h2 hQf

private theorem exists_polarSq_decomposition (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {g : U ≃ₗ[ZMod p] U} (hgQ : IsIsom p Q g) {f : U} (hf : f ∈ centralizerSpace H)
    (hgf : QuadraticMap.polarBilin Q (g f) f ^ 2 ≠ QuadraticMap.polarBilin Q f f ^ 2) :
    ∃ (w : U) (lam : ZMod p),
      f ≠ 0 ∧ centralizerSpace H = Submodule.span (ZMod p) {f} ∧ Q f ≠ 0 ∧
      w ∈ HardMathSupport.Kantor79.commutatorSpace H ∧ Q w ≠ 0 ∧ g f = w + lam • f ∧
      Q w = (1 - lam ^ 2) * Q f ∧ lam ^ 2 ≠ 1 ∧
      QuadraticMap.polar Q w f = 0 ∧ QuadraticMap.polar Q f w = 0 := by
  obtain ⟨hf0, hVH, hQf, hpolf_ne⟩ := fixedSpace_eq_span_of_polar_sq_ne hp hS hQ hoH hf hgf
  have hIsoH : ∀ x ∈ H, IsIsom p Q x := fun x hx => IsOrthOn.isIsom hoH hx
  set lam : ZMod p := QuadraticMap.polar Q (g f) f / QuadraticMap.polar Q f f with hlamdef
  have hlam : QuadraticMap.polar Q (g f) f = lam * QuadraticMap.polar Q f f := by
    rw [hlamdef, div_mul_cancel₀ _ hpolf_ne]
  have hlam2 : lam ^ 2 ≠ 1 := by
    intro h
    apply hgf
    simp only [QuadraticMap.polarBilin_apply_apply, hlam, mul_pow, h, one_mul]
  set w : U := g f - lam • f with hwdef
  have hgfw : g f = w + lam • f := by rw [hwdef]; abel
  have hwV : w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [mem_commutatorSpace_iff_forall_polar_eq_zero hQ hIsoH hS.sub.2.1.1]
    intro u hu
    rw [hVH] at hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq]
    have hfw : QuadraticMap.polar Q f w = 0 := by
      rw [hwdef, QuadraticMap.polar_sub_right,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
        QuadraticMap.polar_comm Q f (g f), hlam, sub_self]
    rw [hfw, mul_zero]
  have hbwf : QuadraticMap.polar Q w f = 0 := by
    rw [QuadraticMap.polar_comm Q w f]
    exact polar_eq_zero_of_mem_centralizerSpace hIsoH hf hwV
  have hQw : Q w = (1 - lam ^ 2) * Q f := by
    have hEq : Q (g f) = Q w + lam ^ 2 * Q f := by
      rw [hgfw, QuadraticMap.map_add Q, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hbwf]; ring
    rw [hgQ f] at hEq
    have hsub : Q f - lam ^ 2 * Q f = Q w := by nth_rewrite 1 [hEq]; ring
    rw [← hsub]; ring
  refine ⟨w, lam, hf0, hVH, hQf, hwV, ?_, hgfw, hQw, hlam2, hbwf, ?_⟩
  · rw [hQw]
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hlam2)) hQf
  · rw [QuadraticMap.polar_comm Q f w]
    exact hbwf

private theorem exists_z_of_polarSq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {w : U} (hwV : w ∈ HardMathSupport.Kantor79.commutatorSpace H) (hQw_ne : Q w ≠ 0)
    {lam : ZMod p} :
    ∃ (alpha : ZMod p) (z : U), alpha = -lam ^ 2 / (1 - lam ^ 2) ∧
      z ∈ HardMathSupport.Kantor79.commutatorSpace H ∧ QuadraticMap.polar Q w z = 0 ∧
      Q z = (1 - alpha ^ 2) * Q w := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hIsoH : ∀ x ∈ H, IsIsom p Q x := fun x hx => IsOrthOn.isIsom hoH hx
  set alpha : ZMod p := -lam ^ 2 / (1 - lam ^ 2) with halpha
  set S : Submodule (ZMod p) U := HardMathSupport.Kantor79.commutatorSpace H ⊓
    (QuadraticMap.polarBilin Q w).ker with hSdef
  have hSnd : ClassicalGroups.Orthogonal.PolarNondegOn Q S := by
    rw [hSdef]
    exact ClassicalGroups.Orthogonal.PolarNondegOn.inf_ker h2
      (polarNondegOn_commutatorSpace hQ hIsoH hS.sub.2.1.1) hwV hQw_ne
  have hSfin : Module.finrank (ZMod p) S = Module.finrank (ZMod p) U - 2 := by
    have h := ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one
      (Q := Q) (S := HardMathSupport.Kantor79.commutatorSpace H) (u := w) h2 hwV hQw_ne
    rw [hSdef]
    have hVfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
        Module.finrank (ZMod p) U - 1 := hS.sub.2.1.2.1
    have h4 := hS.four_le
    omega
  have hSdim : 2 ≤ Module.finrank (ZMod p) S := by
    rw [hSfin]
    have h4 := hS.four_le
    omega
  obtain ⟨z, hzS, hQz⟩ := ClassicalGroups.Orthogonal.PolarNondegOn.exists_map_eq
    (Q := Q) h2 hSnd hSdim ((1 - alpha ^ 2) * Q w)
  have hzV : z ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hSdef] at hzS
    exact hzS.1
  have hzw : QuadraticMap.polar Q w z = 0 := by
    rw [hSdef] at hzS
    exact hzS.2
  exact ⟨alpha, z, halpha, hzV, hzw, hQz⟩

private theorem exists_apply_eq_of_polarSq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {f : U} (hf : f ∈ centralizerSpace H)
    {w : U} (hwV : w ∈ HardMathSupport.Kantor79.commutatorSpace H) (hQw_ne : Q w ≠ 0)
    {alpha : ZMod p} {z : U}
    (hzV : z ∈ HardMathSupport.Kantor79.commutatorSpace H) (hzw : QuadraticMap.polar Q w z = 0)
    (hQz : Q z = (1 - alpha ^ 2) * Q w) :
    ∃ (u : U) (k : U ≃ₗ[ZMod p] U), u = alpha • w + z ∧
      u ∈ HardMathSupport.Kantor79.commutatorSpace H ∧ Q u = Q w ∧ k ∈ H ∧ k w = u ∧ k f = f := by
  set u : U := alpha • w + z with hudef
  have huV : u ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hudef]
    exact add_mem (Submodule.smul_mem _ alpha hwV) hzV
  have hQu : Q u = Q w := by
    rw [hudef, QuadraticMap.map_add Q,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hzw, hQz]
    ring
  obtain ⟨k, hkH, hkw⟩ := exists_mem_apply_eq_of_isOrthOn hp hS.four_le hQ
    hS.sub.2.1 hoH (fun _ => hS.sub.2.2.2.2) hwV huV hQw_ne hQu
  exact ⟨u, k, hudef, huV, hQu, hkH, hkw, (mem_centralizerSpace.mp hf) k hkH⟩

private theorem polar_eq_zero_of_conj [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {H : Subgroup (U ≃ₗ[ZMod p] U)} (hoH : IsOrthOn p Q H)
    {g g' : U ≃ₗ[ZMod p] U}
    {k : U ≃ₗ[ZMod p] U} (hgQ : IsIsom p Q g) (hg' : g' = g⁻¹ * k⁻¹ * g)
    {f w z u : U} {lam alpha : ZMod p} (hf : f ∈ centralizerSpace H)
    (hwV : w ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hzV : z ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hzw : QuadraticMap.polar Q w z = 0) (hQw : Q w = (1 - lam ^ 2) * Q f)
    (hlam2 : lam ^ 2 ≠ 1) (halpha : alpha = -lam ^ 2 / (1 - lam ^ 2))
    (hgfw : g f = w + lam • f) (hu : u = alpha • w + z) (hkw : k w = u) (hkf : k f = f) :
    QuadraticMap.polar Q f (g'⁻¹ f) = 0 := by
  have hIsoH : ∀ x ∈ H, IsIsom p Q x := fun x hx => IsOrthOn.isIsom hoH hx
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
  have hstep : QuadraticMap.polar Q f (g'⁻¹ f) =
      QuadraticMap.polar Q (g f) (k (g f)) := by
    rw [hg']
    have hinv : (g⁻¹ * k⁻¹ * g)⁻¹ = g⁻¹ * k * g := by group
    rw [hinv]
    simp only [LinearEquiv.mul_apply]
    have h := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO f (g.symm (k (g f)))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  rw [hstep]
  have hkgf : k (g f) = (alpha • w + z) + lam • f := by
    rw [hgfw, map_add, map_smul, hkw, hkf, hu]
  rw [hkgf, hgfw]
  have hbfw : QuadraticMap.polar Q f w = 0 :=
    polar_eq_zero_of_mem_centralizerSpace hIsoH hf hwV
  have hbfz : QuadraticMap.polar Q f z = 0 :=
    polar_eq_zero_of_mem_centralizerSpace hIsoH hf hzV
  have hbwf : QuadraticMap.polar Q w f = 0 := by
    rw [QuadraticMap.polar_comm Q w f]
    exact hbfw
  have halphaQ : alpha * Q w = -(lam ^ 2) * Q f := by
    rw [hQw, halpha]
    field_simp
  have hexp : QuadraticMap.polar Q (w + lam • f) (alpha • w + z + lam • f) =
      2 * (alpha * Q w + lam ^ 2 * Q f) := by
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq]
    rw [polar_self_eq_two_mul Q w, polar_self_eq_two_mul Q f,
      hzw, hbwf, hbfw, hbfz]
    ring
  rw [hexp]
  have hfin : alpha * Q w + lam ^ 2 * Q f = 0 := by
    rw [halphaQ]
    ring
  rw [hfin, mul_zero]

theorem exists_isOrthOvergroup_of_polar_sq_ne (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hoH : IsOrthOn p Q H)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ G) (hgQ : IsIsom p Q g) {f : U} (hf : f ∈ centralizerSpace H)
    (hgf : QuadraticMap.polarBilin Q (g f) f ^ 2 ≠ QuadraticMap.polarBilin Q f f ^ 2) :
    ∃ K, IsOrthOvergroup p G H K := by
  obtain ⟨w, lam, hf0, hVH, hQf, hwV, hQw_ne, hgfw, hQw, hlam2, hbwf, -⟩ :=
    exists_polarSq_decomposition hp hS hQ hoH hgQ hf hgf
  obtain ⟨alpha, z, halpha, hzV, hzw, hQz⟩ :=
    exists_z_of_polarSq hp hS hQ hoH hwV hQw_ne
  obtain ⟨u, k, hu, huV, hQu, hkH, hkw, hkf⟩ :=
    exists_apply_eq_of_polarSq hp hS hQ hoH hf hwV hQw_ne hzV hzw hQz
  have hkIso : IsIsom p Q k := IsOrthOn.isIsom hoH hkH
  set g' : U ≃ₗ[ZMod p] U := g⁻¹ * k⁻¹ * g with hg'def
  have hg'G : g' ∈ G := by
    rw [hg'def]
    exact G.mul_mem (G.mul_mem (G.inv_mem hg) (G.inv_mem (hS.le hkH))) hg
  have hg'Q : IsIsom p Q g' := by
    rw [hg'def]
    exact isIsom_mul (isIsom_mul (isIsom_inv hgQ) (isIsom_inv hkIso)) hgQ
  have hperp : QuadraticMap.polar Q f (g'⁻¹ f) = 0 :=
    polar_eq_zero_of_conj hoH hgQ hg'def hf hwV hzV hzw hQw hlam2 halpha hgfw hu hkw hkf
  have hmemV : g'⁻¹ f ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [mem_commutatorSpace_iff_forall_polar_eq_zero hQ
      (fun x hx => IsOrthOn.isIsom hoH hx) hS.sub.2.1.1]
    intro x hx
    rw [hVH] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq, hperp, mul_zero]
  have hle' : centralizerSpace H ≤
      (HardMathSupport.Kantor79.commutatorSpace H).map (g' : U →ₗ[ZMod p] U) := by
    rw [hVH, Submodule.span_le]
    rintro x (hx : x = f)
    rw [hx]
    exact Submodule.mem_map.mpr ⟨g'⁻¹ f, hmemV, LinearEquiv.apply_symm_apply g' f⟩
  exact exists_isOrthOvergroup_of_isIsom hp hS hQ hoH hg'G hg'Q hle'

private theorem map_conj_reflSubgroupIn_le {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hS : OrthExtSetting p G H)
    (hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H)
    {W : Submodule (ZMod p) U} {g : U ≃ₗ[ZMod p] U} (hg : g ∈ G)
    (hgV : (HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W)).map
      (g : U →ₗ[ZMod p] U) = HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H W)) :
    (reflSubgroupIn p H W).map (MulAut.conj g).toMonoidHom ≤ reflSubgroupIn p H W := by
  let Y := reflSubgroupIn p H W
  let V := HardMathSupport.Kantor79.commutatorSpace Y
  have hYH : Y ≤ H := reflSubgroupIn_le H W
  have hYV : V ≤ W := commutatorSpace_reflSubgroupIn_le H W
  have hYVH : V ≤ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.commutatorSpace_mono hYH
  have key : ∀ t ∈ {t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t ∧ ∀ v, t v - v ∈ W},
      MulAut.conj g t ∈ Y := by
    intro t ht
    have htY : t ∈ Y := Subgroup.subset_closure ht
    have htV : HardMathSupport.Kantor79.movedSpace t ≤ V :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htY
    have hle : HardMathSupport.Kantor79.movedSpace (MulAut.conj g t) ≤ V := by
      rw [MulAut.conj_apply, movedSpace_conj]
      calc (HardMathSupport.Kantor79.movedSpace t).map (g : U →ₗ[ZMod p] U)
          ≤ V.map (g : U →ₗ[ZMod p] U) := Submodule.map_mono htV
        _ = V := hgV
    have ht'G : MulAut.conj g t ∈ G := by
      rw [MulAut.conj_apply]
      exact G.mul_mem (G.mul_mem hg (hS.le ht.1)) (G.inv_mem hg)
    have ht'refl : IsRefl p (MulAut.conj g t) := by
      rw [MulAut.conj_apply]
      exact IsRefl.conj ht.2.1 g
    have ht'H : MulAut.conj g t ∈ H := hmem _ ht'G ht'refl (hle.trans hYVH)
    refine Subgroup.subset_closure ⟨ht'H, ht'refl, fun v => ?_⟩
    exact (hle.trans hYV) ⟨v, rfl⟩
  rw [reflSubgroupIn]
  exact (Subgroup.map_le_iff_le_comap).2 ((Subgroup.closure_le _).2 key)

private theorem polarBilin_comp_subtype_apply_mem_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q : QuadraticForm (ZMod p) U} (ho : ∀ g ∈ X, IsIsom p Q g) :
    ∀ g ∈ movedGroup X, ∀ u v : HardMathSupport.Kantor79.commutatorSpace X,
      (QuadraticMap.polarBilin (Q.comp
        (HardMathSupport.Kantor79.commutatorSpace X).subtype)) (g u) (g v) =
      (QuadraticMap.polarBilin (Q.comp
        (HardMathSupport.Kantor79.commutatorSpace X).subtype)) u v := by
  intro g hg u v
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let hVmap : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  have hg' : g ∈ (restrictHom X V hVmap).range := by simpa only [movedGroup] using hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg'
  have hu : ((restrictHom X V hVmap x u : V) : U) = (x : U ≃ₗ[ZMod p] U) (u : U) :=
    restrictHom_apply X V hVmap x u
  have hv : ((restrictHom X V hVmap x v : V) : U) = (x : U ≃ₗ[ZMod p] U) (v : U) :=
    restrictHom_apply X V hVmap x v
  have hpol := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (ho x x.2)) (u : U) (v : U)
  simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.comp_apply,
    hu, hv] using hpol

private noncomputable def bilinRadical {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (B : LinearMap.BilinForm (ZMod p) V) : Submodule (ZMod p) V where
  carrier := {x | ∀ y : V, B x y = 0}
  add_mem' hx hy z := by simp [map_add, hx z, hy z]
  zero_mem' z := by simp
  smul_mem' c x hx z := by simp [hx z]

private theorem conjRestrictForm_invariant [Module.Finite (ZMod p) U]
    {H Y : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    (hYH : Y ≤ H) (hoH : IsOrthOn p Q H) {g : U ≃ₗ[ZMod p] U}
    (hconj : Y.map (MulAut.conj g).toMonoidHom ≤ Y) :
    ∀ a ∈ movedGroup Y, ∀ u v : HardMathSupport.Kantor79.commutatorSpace Y,
      (QuadraticMap.polarBilin ((Q.comp g).comp
        (HardMathSupport.Kantor79.commutatorSpace Y).subtype)) (a u) (a v) =
      (QuadraticMap.polarBilin ((Q.comp g).comp
        (HardMathSupport.Kantor79.commutatorSpace Y).subtype)) u v := by
  intro a ha u v
  let V := HardMathSupport.Kantor79.commutatorSpace Y
  let hVmap : ∀ h ∈ Y, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  have ha' : a ∈ (restrictHom Y V hVmap).range := by simpa only [movedGroup] using ha
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp ha'
  have hy' : MulAut.conj g (y : U ≃ₗ[ZMod p] U) ∈ Y :=
    hconj (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom y.2)
  have hiso := hoH.isIsom (hYH hy')
  have hgu : g ((restrictHom Y V hVmap y u : V) : U) =
      (MulAut.conj g (y : U ≃ₗ[ZMod p] U)) (g (u : U)) := by
    simp [MulAut.conj_apply, LinearEquiv.mul_apply]
  have hgv : g ((restrictHom Y V hVmap y v : V) : U) =
      (MulAut.conj g (y : U ≃ₗ[ZMod p] U)) (g (v : U)) := by
    simp [MulAut.conj_apply, LinearEquiv.mul_apply]
  have hpol : QuadraticMap.polar Q
      ((MulAut.conj g (y : U ≃ₗ[ZMod p] U)) (g (u : U)))
      ((MulAut.conj g (y : U ≃ₗ[ZMod p] U)) (g (v : U))) =
      QuadraticMap.polar Q (g (u : U)) (g (v : U)) :=
    CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso) _ _
  simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    QuadraticMap.comp_apply, hgu, hgv] using hpol

private theorem exists_eq_zero_of_bilinRadical_top (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} {g : U ≃ₗ[ZMod p] U}
    {V : Submodule (ZMod p) U} {B0 : LinearMap.BilinForm (ZMod p) V}
    (hB0 : B0 = QuadraticMap.polarBilin (Q.comp V.subtype))
    (hR : bilinRadical B0 = ⊤) (hgV : V.map (g : U →ₗ[ZMod p] U) = V) :
    ∃ c : ZMod p, ∀ x ∈ V, Q (g x) = c * Q x := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hzero : ∀ z : U, z ∈ V → Q z = 0 := by
    intro z hz
    have hzR : (⟨z, hz⟩ : V) ∈ bilinRadical B0 := by rw [hR]; trivial
    have h := hzR ⟨z, hz⟩
    rw [hB0, QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  refine ⟨0, fun x hx => ?_⟩
  have hgx : g x ∈ V := by
    have h := Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) hx
    rwa [hgV] at h
  simp [hzero (g x) hgx, hzero x hx]

private theorem exists_eq_mul_of_conj_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H Y : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    (hYH : Y ≤ H) (hoH : IsOrthOn p Q H) (hY : AbsIrred p (movedGroup Y))
    {g : U ≃ₗ[ZMod p] U} (hconj : Y.map (MulAut.conj g).toMonoidHom ≤ Y)
    (hgV : (HardMathSupport.Kantor79.commutatorSpace Y).map (g : U →ₗ[ZMod p] U) =
      HardMathSupport.Kantor79.commutatorSpace Y) :
    ∃ c : ZMod p, ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace Y, Q (g x) = c * Q x := by
  let V := HardMathSupport.Kantor79.commutatorSpace Y
  let B0 : LinearMap.BilinForm (ZMod p) V := QuadraticMap.polarBilin (Q.comp V.subtype)
  let C0 : LinearMap.BilinForm (ZMod p) V :=
    QuadraticMap.polarBilin ((Q.comp g).comp V.subtype)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hBinv : ∀ a ∈ movedGroup Y, ∀ u v : V, B0 (a u) (a v) = B0 u v := by
    simpa only [B0] using polarBilin_comp_subtype_apply_mem_movedGroup (X := Y) (Q := Q)
      (fun g hg => hoH.isIsom (hYH hg))
  have hCinv : ∀ a ∈ movedGroup Y, ∀ u v : V, C0 (a u) (a v) = C0 u v := by
    simpa only [C0] using conjRestrictForm_invariant hYH hoH hconj
  let R := bilinRadical B0
  have hRinv : ∀ a ∈ movedGroup Y, ∀ x ∈ R, a x ∈ R := by
    intro a ha x hx y
    rw [← a.apply_symm_apply y, hBinv a ha x (a.symm y)]
    exact hx (a.symm y)
  have hsym : ∀ x y : V, B0 x y = B0 y x := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm]
  rcases hY.1 R hRinv with hR | hR
  · have hBnd : B0.Nondegenerate := by
      refine ⟨?_, ?_⟩
      · intro x hx
        have hxR : x ∈ R := hx
        rw [hR] at hxR
        simpa using hxR
      · intro y hy
        have hyR : y ∈ R := fun x => by rw [hsym]; exact hy x
        rw [hR] at hyR
        simpa using hyR
    obtain ⟨c, hc⟩ := exists_eq_smul_of_absIrred hY hBnd hBinv hCinv
    refine ⟨c, fun x hx => ?_⟩
    have hxx := congrArg (fun B : LinearMap.BilinForm (ZMod p) V => B ⟨x, hx⟩ ⟨x, hx⟩) hc
    simp only [LinearMap.smul_apply, smul_eq_mul, C0, B0,
      QuadraticMap.polarBilin_apply_apply] at hxx
    rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul] at hxx
    refine mul_left_cancel₀ h2 ?_
    calc (2 : ZMod p) * Q (g x) = c * ((2 : ZMod p) * Q x) := hxx
      _ = (2 : ZMod p) * (c * Q x) := by ring
  · exact exists_eq_zero_of_bilinRadical_top hp (V := V) (B0 := B0) (by rfl) hR hgV

theorem exists_apply_eq_mul_of_map_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H)
    (hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H)
    {Q : QuadraticForm (ZMod p) U} (hoH : IsOrthOn p Q H) {W : Submodule (ZMod p) U}
    (hY : AbsIrred p (movedGroup (reflSubgroupIn p H W))) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ G)
    (hgV : (HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W)).map
      (g : U →ₗ[ZMod p] U) = HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W)) :
    ∃ c : ZMod p, ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W),
      Q (g x) = c * Q x := by
  have hconj : (reflSubgroupIn p H W).map (MulAut.conj g).toMonoidHom ≤
      reflSubgroupIn p H W := map_conj_reflSubgroupIn_le hS hmem hg hgV
  exact exists_eq_mul_of_conj_le hp (reflSubgroupIn_le H W) hoH hY hconj hgV

theorem false_of_map_eq_of_apply_eq_smul (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hS : OrthExtSetting p G H)
    (hmem : ∀ b ∈ G, IsRefl p b →
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H)
    {Q : QuadraticForm (ZMod p) U} (hoH : IsOrthOn p Q H) {W : Submodule (ZMod p) U}
    (hY : AbsIrred p (movedGroup (reflSubgroupIn p H W))) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ G)
    (hgV : (HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W)).map
      (g : U →ₗ[ZMod p] U) = HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W))
    {u w : U} (hu : u ∈ HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W))
    (hw : w ∈ HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W)) (hQu : Q u ≠ 0)
    (hQw : Q w ≠ 0) (hgu : g u = u) {ζ : ZMod p} (hζ : ζ * ζ ≠ 1) (hgw : g w = ζ • w) :
    False := by
  obtain ⟨c, hc⟩ := exists_apply_eq_mul_of_map_eq hp hS hmem hoH hY hg hgV
  have hcu : c = 1 := by
    have h := hc u hu
    rw [hgu] at h
    exact (mul_right_cancel₀ hQu (by simpa using h)).symm
  have hw' := hc w hw
  rw [hgw, hcu, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, one_mul] at hw'
  have hζ2 : ζ * ζ = 1 := by
    have h : ζ ^ 2 * Q w = 1 * Q w := by simpa [pow_two] using hw'
    simpa [pow_two] using mul_right_cancel₀ hQw h
  exact hζ hζ2

private theorem irred_movedGroup_of_irredOnSection {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : IrredOnSection X ⊥ (HardMathSupport.Kantor79.commutatorSpace X)) :
    ∀ W : Submodule (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X),
      (∀ g ∈ movedGroup X, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let hVmap : ∀ h ∈ X, ∀ w ∈ V, h w ∈ V := fun _ hh _ hw => apply_mem_commutatorSpace hh hw
  let φ := restrictHom X V hVmap
  let X' : Submodule (ZMod p) U := W.map V.subtype
  have hXinv : ∀ h ∈ X, ∀ x ∈ X', h x ∈ X' := by
    intro h hh x hx
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨φ ⟨h, hh⟩ w,
      hW (φ ⟨h, hh⟩) (MonoidHom.mem_range.mpr ⟨⟨h, hh⟩, rfl⟩) w hw, ?_⟩
    exact restrictHom_apply X V hVmap ⟨h, hh⟩ w
  have hX'le : X' ≤ V := by
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  rcases hirr X' bot_le hX'le hXinv with hX' | hX'
  · left
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    have : (w : U) ∈ X' := ⟨w, hw, rfl⟩
    rw [hX'] at this
    simpa using this
  · right
    refine le_antisymm le_top ?_
    intro w _
    have : (w : U) ∈ X' := by rw [hX']; exact w.2
    obtain ⟨w', hw', hEq⟩ := this
    have hw'' : w' = w := Subtype.ext hEq
    rwa [hw''] at hw'

private theorem nondegenerate_comp_subtype_of_absIrred (hp : p ≠ 2)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {Q : QuadraticForm (ZMod p) U}
    (hA : AbsIrred p (movedGroup X)) (ho : ∀ g ∈ X, IsIsom p Q g)
    {a : U} (ha : a ∈ HardMathSupport.Kantor79.commutatorSpace X) (hQa : Q a ≠ 0) :
    (QuadraticMap.polarBilin (Q.comp
      (HardMathSupport.Kantor79.commutatorSpace X).subtype)).Nondegenerate := by
  let V := HardMathSupport.Kantor79.commutatorSpace X
  let B : LinearMap.BilinForm (ZMod p) V := QuadraticMap.polarBilin (Q.comp V.subtype)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hBinv := polarBilin_comp_subtype_apply_mem_movedGroup (X := X) (Q := Q) ho
  let R : Submodule (ZMod p) V :=
    { carrier := {x | ∀ y : V, B x y = 0}
      add_mem' := fun hx hy z => by simp [map_add, hx z, hy z]
      zero_mem' := fun z => by simp
      smul_mem' := fun c x hx z => by simp [hx z] }
  have hRinv : ∀ g ∈ movedGroup X, ∀ x ∈ R, g x ∈ R := by
    intro g hg x hx y
    rw [← g.apply_symm_apply y, hBinv g hg x (g.symm y)]
    exact hx (g.symm y)
  have hsym : ∀ x y : V, B x y = B y x := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm]
  rcases hA.1 R hRinv with hR | hR
  · refine ⟨?_, ?_⟩
    · intro x hx
      have hxR : x ∈ R := hx
      rw [hR] at hxR
      simpa using hxR
    · intro y hy
      have hyR : y ∈ R := fun x => by rw [hsym]; exact hy x
      rw [hR] at hyR
      simpa using hyR
  · exfalso
    have hmem : (⟨a, ha⟩ : V) ∈ R := by rw [hR]; trivial
    have h := hmem ⟨a, ha⟩
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul] at h
    exact hQa ((mul_eq_zero.mp h).resolve_left h2)

private theorem exists_mem_centralizerSpace_ne_zero_of_splitSupport [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport X (Module.finrank (ZMod p) U - 1))
    (hn : 0 < Module.finrank (ZMod p) U) :
    ∃ e ∈ centralizerSpace X, e ≠ 0 := by
  have hVHfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) =
      Module.finrank (ZMod p) U - 1 := hs.2.1
  have hCfin : Module.finrank (ZMod p) (centralizerSpace X) = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hs.1
    have h1 : (Module.finrank (ZMod p) U - 1) +
        Module.finrank (ZMod p) (centralizerSpace X) = Module.finrank (ZMod p) U := by
      rw [← hVHfin]
      exact hsum
    have h2n : (Module.finrank (ZMod p) U - 1) + 1 = Module.finrank (ZMod p) U :=
      Nat.sub_add_cancel hn
    exact Nat.add_left_cancel (by rw [h1, h2n])
  have hCne : centralizerSpace X ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hCfin
    exact Nat.zero_ne_one hCfin
  exact Submodule.exists_mem_ne_zero_of_ne_bot hCne

private theorem reflGen_reflStab (H : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) :
    ReflGen p (reflStab p H h) := by
  change ReflGen p (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))
  rw [reflSubgroupIn]
  exact reflGen_closure_of_forall_isRefl (fun g hg => hg.2.1)

private theorem ne_bot_of_commutatorSpace_ne_bot {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hE : HardMathSupport.Kantor79.commutatorSpace X ≠ ⊥) : X ≠ ⊥ := by
  intro hbot
  apply hE
  rw [hbot, HardMathSupport.Kantor79.commutatorSpace, Submodule.span_eq_bot]
  rintro w ⟨g, hg, v, rfl⟩
  rw [Subgroup.mem_bot] at hg
  simp [hg]

private theorem exists_isRefl_of_reflGen_ne_bot {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hgen : ReflGen p X) (hne : X ≠ ⊥) : ∃ t ∈ X, IsRefl p t := by
  by_contra h
  push Not at h
  apply hne
  have hS : {t : U ≃ₗ[ZMod p] U | t ∈ X ∧ IsRefl p t} = ∅ := by
    ext t
    exact ⟨fun ht => (h t ht.1 ht.2).elim, False.elim⟩
  rw [hgen, hS, Subgroup.closure_empty]

private theorem exists_eq_mul_on_commutatorSpace_of_absIrred (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (_hD : LemmaTwoSevenData p G H B h) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q₁ Q₂ : QuadraticForm (ZMod p) U} (hXH : X ≤ H) (hXB : X ≤ B)
    (hA : AbsIrred p (movedGroup X)) (hQ₁nd : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    (hoQ₁ : IsOrthOn p Q₁ H) (hQ₂nd : (QuadraticMap.polarBilin Q₂).Nondegenerate)
    (hQ₂iso : ∀ g ∈ B, IsIsom p Q₂ g) (hex : ∃ t ∈ X, IsRefl p t) :
    ∃ c : ZMod p, c ≠ 0 ∧
      ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace X, Q₂ v = c * Q₁ v := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨t, htX, htrefl⟩ := hex
  obtain ⟨a, hQ₁a, hta⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₁nd htrefl
    (hoQ₁.isIsom (hXH htX))
  obtain ⟨a', hQ₂a', hta'⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₂nd htrefl
    (hQ₂iso t (hXB htX))
  have ha : a ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htX
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta)
  have ha' : a' ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htX
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta')
  have hB₁nd := nondegenerate_comp_subtype_of_absIrred hp (X := X) (Q := Q₁) hA
    (fun g hg => hoQ₁.isIsom (hXH hg)) ha hQ₁a
  have hB₂nd := nondegenerate_comp_subtype_of_absIrred hp (X := X) (Q := Q₂) hA
    (fun g hg => hQ₂iso g (hXB hg)) ha' hQ₂a'
  obtain ⟨c, hc⟩ := exists_eq_smul_of_absIrred hA hB₁nd
    (polarBilin_comp_subtype_apply_mem_movedGroup (X := X) (Q := Q₁)
      (fun g hg => hoQ₁.isIsom (hXH hg)))
    (polarBilin_comp_subtype_apply_mem_movedGroup (X := X) (Q := Q₂)
      (fun g hg => hQ₂iso g (hXB hg)))
  have hEq := eq_smul_of_polarBilin_eq_smul h2 hc
  have hcne : c ≠ 0 := by
    intro hc0
    have hv := congrArg (fun Q : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)
      => Q ⟨a', ha'⟩) hEq
    simp only [QuadraticMap.smul_apply, smul_eq_mul] at hv
    rw [hc0, zero_mul] at hv
    exact hQ₂a' (by simpa [QuadraticMap.comp_apply] using hv)
  refine ⟨c, hcne, fun v hv => ?_⟩
  have hv' := congrArg (fun Q : QuadraticForm (ZMod p)
    (HardMathSupport.Kantor79.commutatorSpace X) => Q ⟨v, hv⟩) hEq
  simpa [QuadraticMap.smul_apply, smul_eq_mul, QuadraticMap.comp_apply] using hv'

theorem exists_eq_mul_of_irredOnSection (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    (hψ : ∃ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₂).Nondegenerate ∧
      ∀ g ∈ B, IsIsom p Q₂ g) :
    ∃ Q₁ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₁).Nondegenerate ∧
      IsOrthOn p Q₁ H ∧ (QuadraticMap.polarBilin Q₂).Nondegenerate ∧ (∀ g ∈ B, IsIsom p Q₂ g) ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), Q₂ v = c * Q₁ v := by
  let X := reflStab p H h
  let E := HardMathSupport.Kantor79.commutatorSpace X
  have hXH : X ≤ H := reflSubgroupIn_le H _
  have hXB : X ≤ B := hD.split.2.2.2.2
  have hn : 0 < Module.finrank (ZMod p) U :=
    lt_of_lt_of_le (by norm_num) hD.setting.four_le
  obtain ⟨e, he, he0⟩ :=
    exists_mem_centralizerSpace_ne_zero_of_splitSupport hD.setting.sub.2.1 hn
  obtain ⟨Q₁, hQ₁nd, hoQ₁, -⟩ := exists_isOrthOn_of_isOrthType_movedGroup hp
    hD.setting.sub.2.1 hD.setting.sub.2.2.2.1 he he0 (c := 1) one_ne_zero
  obtain ⟨Q₂, hQ₂nd, hQ₂iso⟩ := hψ
  by_cases hE : E = ⊥
  · refine ⟨Q₁, Q₂, hQ₁nd, hoQ₁, hQ₂nd, hQ₂iso, 1, one_ne_zero, fun v hv => ?_⟩
    change v ∈ E at hv
    rw [hE] at hv
    have hv0 : v = 0 := by simpa using hv
    rw [hv0]
    simp
  · have hXne : X ≠ ⊥ := ne_bot_of_commutatorSpace_ne_bot (by simpa only [E] using hE)
    have hreflGen : ReflGen p X := reflGen_reflStab H h
    have hirr : ∀ W : Submodule (ZMod p) E,
        (∀ g ∈ movedGroup X, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
      irred_movedGroup_of_irredOnSection (X := X) (by simpa only [X] using hirr₁)
    have hA : AbsIrred p (movedGroup X) :=
      absIrred_of_reflGen (reflGen_movedGroup hreflGen) hirr
    obtain ⟨c, hcne, hrel⟩ := exists_eq_mul_on_commutatorSpace_of_absIrred hp hD hXH hXB
      hA hQ₁nd hoQ₁ hQ₂nd hQ₂iso (exists_isRefl_of_reflGen_ne_bot hreflGen hXne)
    exact ⟨Q₁, Q₂, hQ₁nd, hoQ₁, hQ₂nd, hQ₂iso, c, hcne, hrel⟩

private theorem polar_eq_of_eq_on_commutatorSpace [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {Q Q₁ : QuadraticForm (ZMod p) U}
    (ho₁ : IsOrthOn p Q₁ H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hVH : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, Q v = Q₁ v)
    (hC : ∀ a ∈ HardMathSupport.Kantor79.commutatorSpace H,
      ∀ f ∈ centralizerSpace H, QuadraticMap.polar Q a f = 0) :
    ∀ a ∈ HardMathSupport.Kantor79.commutatorSpace H, ∀ x : U,
      QuadraticMap.polar Q a x = QuadraticMap.polar Q₁ a x := by
  intro a ha x
  have hx : x ∈ HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H := by
    rw [hs.1.sup_eq_top]
    trivial
  obtain ⟨u, hu, f, hf, rfl⟩ := Submodule.mem_sup.mp hx
  have h1 : QuadraticMap.polar Q a u = QuadraticMap.polar Q₁ a u := by
    rw [QuadraticMap.polar, QuadraticMap.polar, hVH a ha, hVH u hu,
      hVH (a + u) (Submodule.add_mem _ ha hu)]
  have h2 : QuadraticMap.polar Q₁ a f = 0 := by
    rw [QuadraticMap.polar_comm]
    exact polar_eq_zero_of_mem_centralizerSpace (fun g hg => ho₁.isIsom hg) hf ha
  calc QuadraticMap.polar Q a (u + f)
      = QuadraticMap.polar Q a u + QuadraticMap.polar Q a f := by
        rw [QuadraticMap.polar_add_right]
    _ = QuadraticMap.polar Q₁ a u + 0 := by rw [h1, hC a ha f hf]
    _ = QuadraticMap.polar Q₁ a u + QuadraticMap.polar Q₁ a f := by rw [h2]
    _ = QuadraticMap.polar Q₁ a (u + f) := by rw [QuadraticMap.polar_add_right]

private theorem isOrthOn_of_eq_on_commutatorSpace_full (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q Q₁ : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    (hfull : H = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q₁ t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H})
    (hVH : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, Q v = Q₁ v)
    (hpol : ∀ a ∈ HardMathSupport.Kantor79.commutatorSpace H, ∀ x : U,
      QuadraticMap.polar Q a x = QuadraticMap.polar Q₁ a x) :
    H = Subgroup.closure {t | IsRefl p t ∧ IsIsom p Q t ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H} := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  conv_lhs => rw [hfull]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨htrefl, htiso, htle⟩ := ht
    obtain ⟨a, hQ₁a, hta⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₁ htrefl htiso
    have haVH : a ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      htle (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta)
    have hQa : Q a ≠ 0 := by rw [hVH a haVH]; exact hQ₁a
    have ha0 : a ≠ 0 := fun h0 => hQ₁a (by rw [h0]; exact map_zero Q₁)
    have ht_eq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q₁ a :=
      DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ₁ htrefl htiso
        (isRefl_reflect hp hQ₁a) (isIsom_reflect (Q := Q₁) a) ha0 hta (reflect_apply_self hQ₁a)
    have hrefl_eq : CFSG.ClassicalGroups.Orthogonal.reflect Q₁ a =
        CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
      ext x
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQ₁a,
        CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa, hVH a haVH, hpol a haVH x]
    refine Subgroup.subset_closure ⟨htrefl, ?_, htle⟩
    rw [ht_eq, hrefl_eq]; exact isIsom_reflect (Q := Q) a
  · rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨htrefl, htiso, htle⟩ := ht
    obtain ⟨a, hQa, hta⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ htrefl htiso
    have haVH : a ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      htle (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta)
    have hQ₁a : Q₁ a ≠ 0 := by rw [← hVH a haVH]; exact hQa
    have ha0 : a ≠ 0 := fun h0 => hQa (by rw [h0]; exact map_zero Q)
    have ht_eq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q a :=
      DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ htrefl htiso
        (isRefl_reflect hp hQa) (isIsom_reflect (Q := Q) a) ha0 hta (reflect_apply_self hQa)
    have hrefl_eq : CFSG.ClassicalGroups.Orthogonal.reflect Q a =
        CFSG.ClassicalGroups.Orthogonal.reflect Q₁ a := by
      ext x
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa,
        CFSG.ClassicalGroups.Orthogonal.reflect_apply hQ₁a, hVH a haVH, hpol a haVH x]
    exact Subgroup.subset_closure
      ⟨htrefl, by rw [ht_eq, hrefl_eq]; exact isIsom_reflect (Q := Q₁) a, htle⟩

private theorem isOrthOn_of_eq_on_commutatorSpace_class (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q Q₁ : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQ₁ : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    {c : ZMod p} (hc : c ≠ 0)
    (hclass : H = Subgroup.closure {t | t ∈ ClassRefl p Q₁ c ∧
      HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.commutatorSpace H})
    (hVH : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, Q v = Q₁ v)
    (hpol : ∀ a ∈ HardMathSupport.Kantor79.commutatorSpace H, ∀ x : U,
      QuadraticMap.polar Q a x = QuadraticMap.polar Q₁ a x) :
    IsOrthOn p Q H := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  right
  refine ⟨c, hc, ?_⟩
  conv_lhs => rw [hclass]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨htclass, htle⟩ := ht
    obtain ⟨a, hQ₁a, hta_refl⟩ := (mem_classRefl_iff hp hQ₁ hc t).mp htclass
    have hQ₁a_ne : Q₁ a ≠ 0 := by rw [hQ₁a]; exact hc
    have hta : t a = -a := by rw [hta_refl]; exact reflect_apply_self hQ₁a_ne
    have haVH : a ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      htle (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta)
    have hQa_eq : Q a = c := by rw [hVH a haVH]; exact hQ₁a
    have hQa : Q a ≠ 0 := by rw [hQa_eq]; exact hc
    have ht_eq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
      rw [hta_refl]
      ext x
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQ₁a_ne,
        CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa, hVH a haVH, hpol a haVH x]
    refine Subgroup.subset_closure ⟨?_, htle⟩
    exact (mem_classRefl_iff hp hQ hc t).mpr ⟨a, hQa_eq, ht_eq⟩
  · rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨htclass, htle⟩ := ht
    obtain ⟨a, hQa_eq, hta_refl⟩ := (mem_classRefl_iff hp hQ hc t).mp htclass
    have hQa : Q a ≠ 0 := by rw [hQa_eq]; exact hc
    have hta : t a = -a := by rw [hta_refl]; exact reflect_apply_self hQa
    have haVH : a ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      htle (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hta)
    have hQ₁a_eq : Q₁ a = c := by rw [← hVH a haVH]; exact hQa_eq
    have hQ₁a_ne : Q₁ a ≠ 0 := by rw [hQ₁a_eq]; exact hc
    have ht_eq : t = CFSG.ClassicalGroups.Orthogonal.reflect Q₁ a := by
      rw [hta_refl]
      ext x
      rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa,
        CFSG.ClassicalGroups.Orthogonal.reflect_apply hQ₁a_ne, hVH a haVH, hpol a haVH x]
    exact Subgroup.subset_closure
      ⟨(mem_classRefl_iff hp hQ₁ hc t).mpr ⟨a, hQ₁a_eq, ht_eq⟩, htle⟩

private noncomputable def glueForm (Q₂ : QuadraticForm (ZMod p) U) (c q : ZMod p)
    (VB : Submodule (ZMod p) U) (π : U →ₗ[ZMod p] VB) (f : U →ₗ[ZMod p] ZMod p) :
    QuadraticForm (ZMod p) U :=
  extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q

private theorem exists_root_decomp (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q₁ : QuadraticForm (ZMod p) U}
    (hQ₁nd : (QuadraticMap.polarBilin Q₁).Nondegenerate) (hoQ₁ : IsOrthOn p Q₁ H) :
    ∃ (e : U) (VB CB : Submodule (ZMod p) U), e ≠ 0 ∧ h e = -e ∧ Q₁ e ≠ 0 ∧
      VB = HardMathSupport.Kantor79.commutatorSpace B ∧
      CB = centralizerSpace B ∧ CB = Submodule.span (ZMod p) {e} := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : 3 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) hD.setting.four_le
  obtain ⟨hVB, hCB⟩ := commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl
  obtain ⟨e, hQ₁e, hhe⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ₁nd hD.isRefl
    (hoQ₁.isIsom hD.mem)
  have he0 : e ≠ 0 := fun h0 => hQ₁e (by rw [h0]; exact map_zero Q₁)
  have heCB : e ∈ centralizerSpace B := by
    rw [hCB]
    exact HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hhe
  have hCBspan : centralizerSpace B = Submodule.span (ZMod p) {e} := by
    refine eq_span_singleton_of_mem_of_finrank_eq_one ?_ heCB he0
    rw [hCB]
    exact hD.isRefl.2
  exact ⟨e, HardMathSupport.Kantor79.commutatorSpace B, centralizerSpace B, he0, hhe, hQ₁e,
    rfl, rfl, hCBspan⟩

private theorem exists_plane_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {Q₁ : QuadraticForm (ZMod p) U}
    (hQ₁nd : (QuadraticMap.polarBilin Q₁).Nondegenerate) (hoQ₁ : IsOrthOn p Q₁ H) :
    HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
  have hm : 3 ≤ Module.finrank (ZMod p) U - 1 := by
    have := hD.setting.four_le
    omega
  have hm3 : p = 3 → 4 ≤ Module.finrank (ZMod p) U - 1 := by
    intro hp3
    have := hD.setting.five_le_of_eq_three hp3
    omega
  exact commutatorSpace_reflStab (p := p) (U := U) (X := H) (h := h) hp hQ₁nd
    hD.setting.sub.2.1 hm hm3 hoQ₁ hD.mem hD.isRefl

private theorem exists_commutatorSpace_decomp (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) {CB : Submodule (ZMod p) U} {r : U}
    (hhe : h r = -r) (hCB : CB = HardMathSupport.Kantor79.movedSpace h)
    (hCBspan : CB = Submodule.span (ZMod p) {r})
    (hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
    ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace H,
      ∃ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
        ∃ α : ZMod p, u = x + α • r := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have heVH : r ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hhe)
  have hmemE_of_fix : ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace H,
      h u = u → u ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    intro u hu hfix
    rw [hEeq]
    exact ⟨hu, by simpa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using hfix⟩
  intro u hu
  have hdiff : h u - u ∈ CB := by
    rw [hCB]
    exact ⟨u, rfl⟩
  rw [hCBspan, Submodule.mem_span_singleton] at hdiff
  obtain ⟨β, hβ⟩ := hdiff
  let α : ZMod p := β * (2 : ZMod p)⁻¹
  have hα : (2 : ZMod p) * α = β := by
    dsimp only [α]
    rw [show (2 : ZMod p) * (β * (2 : ZMod p)⁻¹) =
      β * ((2 : ZMod p) * (2 : ZMod p)⁻¹) by ring, mul_inv_cancel₀ h2, mul_one]
  have hfix : h (u + α • r) = u + α • r := by
    have hβe : β • r = α • r + α • r := by
      rw [← hα, mul_smul, two_smul]
    have huβ : h u = u + β • r := sub_eq_iff_eq_add'.mp hβ.symm
    rw [map_add, map_smul, hhe, smul_neg, huβ, hβe]
    abel
  refine ⟨u + α • r, hmemE_of_fix _ (Submodule.add_mem _ hu (Submodule.smul_mem _ α heVH))
    hfix, -α, ?_⟩
  rw [neg_smul]
  abel

private theorem exists_proj {VB CB : Submodule (ZMod p) U} (hsplit : IsCompl VB CB) {e : U}
    (he0 : e ≠ 0) (heCB : e ∈ CB) (hCBspan : CB = Submodule.span (ZMod p) {e}) :
    ∃ (π : U →ₗ[ZMod p] VB) (f : U →ₗ[ZMod p] ZMod p),
      π e = 0 ∧ (∀ v : VB, π v.1 = v) ∧ (∀ v : VB, f v.1 = 0) ∧ f e = 1 ∧
      (∀ x : U, π x = 0 → x ∈ CB) ∧ (∀ x : U, x ∈ CB → π x = 0) := by
  let π : U →ₗ[ZMod p] VB := VB.projectionOnto CB hsplit
  let coordSpan : Submodule.span (ZMod p) {e} ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.coord (ZMod p) U e he0
  let coordC : CB ≃ₗ[ZMod p] ZMod p :=
    (LinearEquiv.ofEq CB (Submodule.span (ZMod p) {e}) hCBspan).trans coordSpan
  let f : U →ₗ[ZMod p] ZMod p := coordC.toLinearMap.comp (CB.projectionOnto VB hsplit.symm)
  have hπe : π e = 0 := Submodule.projectionOnto_apply_of_mem_right hsplit heCB
  have hπV : ∀ v : VB, π v.1 = v :=
    fun v => Submodule.projectionOnto_apply_of_mem_left hsplit v.2
  have hfV : ∀ v : VB, f v.1 = 0 := by
    intro v
    have hproj : CB.projectionOnto VB hsplit.symm v.1 = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hsplit.symm v.2
    simp [f, hproj]
  have hfe : f e = 1 := by
    have hproj : CB.projectionOnto VB hsplit.symm e = ⟨e, heCB⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hsplit.symm heCB
    have hcoord : coordC ⟨e, heCB⟩ = 1 := by
      change coordSpan (LinearEquiv.ofEq CB (Submodule.span (ZMod p) {e}) hCBspan
        ⟨e, heCB⟩) = 1
      rw [show (LinearEquiv.ofEq CB (Submodule.span (ZMod p) {e}) hCBspan) ⟨e, heCB⟩ =
        (⟨e, Submodule.mem_span_singleton_self e⟩ : Submodule.span (ZMod p) {e}) from
          Subtype.ext rfl, LinearEquiv.coord_self]
    simpa [f, hproj] using hcoord
  have hker : ∀ x : U, π x = 0 → x ∈ CB := fun x hx => by
    have hx' : x ∈ LinearMap.ker (VB.projectionOnto CB hsplit) := hx
    rwa [Submodule.ker_projectionOnto (p := VB) (q := CB) hsplit] at hx'
  have hπC : ∀ x : U, x ∈ CB → π x = 0 :=
    fun x hx => Submodule.projectionOnto_apply_of_mem_right hsplit hx
  exact ⟨π, f, hπe, hπV, hfV, hfe, hker, hπC⟩

private theorem glueForm_nondegenerate (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q₂ : QuadraticForm (ZMod p) U} {c q : ZMod p} (hc : c ≠ 0) (hq : q ≠ 0)
    {VB CB : Submodule (ZMod p) U}
    (hQ₂ : (QuadraticMap.polarBilin (Q₂.comp VB.subtype)).Nondegenerate)
    (π : U →ₗ[ZMod p] VB) (f : U →ₗ[ZMod p] ZMod p) {e : U}
    (hCspan : CB = Submodule.span (ZMod p) {e})
    (hker : ∀ x : U, π x = 0 → x ∈ CB)
    (hπ : ∀ v : VB, π v.1 = v) (hf : ∀ v : VB, f v.1 = 0)
    (hπe : π e = 0) (hfe : f e = 1) :
    (QuadraticMap.polarBilin (glueForm Q₂ c q VB π f)).Nondegenerate := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hQ'nd : (QuadraticMap.polarBilin (c⁻¹ • (Q₂.comp VB.subtype))).Nondegenerate := by
    have hpol : QuadraticMap.polarBilin (c⁻¹ • (Q₂.comp VB.subtype)) =
        c⁻¹ • QuadraticMap.polarBilin (Q₂.comp VB.subtype) := by
      ext u v
      have h := QuadraticMap.polar_smul (Q₂.comp VB.subtype) c⁻¹ u v
      simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.comp_apply,
        smul_eq_mul] using h
    rw [hpol]
    constructor
    · intro x hx
      apply hQ₂.1 x
      intro y
      have h := hx y
      simp only [LinearMap.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hc)
    · intro y hy
      apply hQ₂.2 y
      intro x
      have h := hy x
      simp only [LinearMap.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hc)
  exact extendForm_nondegenerate hQ'nd π f hq h2 hCspan hker hπ hf hπe hfe

private theorem glueForm_eq_on_reflStab [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    {Q₁ Q₂ : QuadraticForm (ZMod p) U} {c q : ZMod p} {VB : Submodule (ZMod p) U}
    {π : U →ₗ[ZMod p] VB} {f : U →ₗ[ZMod p] ZMod p}
    (hcompE : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
      Q₂ v = c * Q₁ v)
    (hEVB : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤ VB)
    (hc : c ≠ 0) (hπ : ∀ v : VB, π v.1 = v) (hf : ∀ v : VB, f v.1 = 0) :
    ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
      glueForm Q₂ c q VB π f x = Q₁ x := by
  intro x hx
  have hxVB : x ∈ VB := hEVB hx
  have hcompQ : (extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q).comp VB.subtype =
      c⁻¹ • (Q₂.comp VB.subtype) := extendForm_comp_subtype _ π f q hπ hf
  have hx' := congrArg (fun Qf : QuadraticForm (ZMod p) VB => Qf ⟨x, hxVB⟩) hcompQ
  simp only [QuadraticMap.comp_apply, Submodule.coe_subtype] at hx'
  change extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q x = Q₁ x
  rw [hx']
  change c⁻¹ * Q₂ x = Q₁ x
  rw [hcompE x hx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

private theorem polar_eq_zero_of_mem_reflStab (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hD : LemmaTwoSevenData p G H B h) {Q₁ : QuadraticForm (ZMod p) U}
    (hoQ₁ : IsOrthOn p Q₁ H) {e : U} (hhe : h e = -e)
    (hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    {x : U} (hxE : x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) :
    QuadraticMap.polar Q₁ x e = 0 := by
  have hxfix : h x = x := by
    have hxker : x ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := (hEeq ▸ hxE).2
    simpa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using hxker
  rw [QuadraticMap.polar_comm Q₁ x e]
  exact IsIsom.polar_eq_zero_of_apply_eq_neg_of_apply_eq hp (hoQ₁.isIsom hD.mem) hhe hxfix

private theorem glueForm_eq_on_commutatorSpace (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hD : LemmaTwoSevenData p G H B h) {Q₁ Q₂ : QuadraticForm (ZMod p) U} {c q : ZMod p}
    {e : U} {VB : Submodule (ZMod p) U} {π : U →ₗ[ZMod p] VB}
    {f : U →ₗ[ZMod p] ZMod p} (hoQ₁ : IsOrthOn p Q₁ H) (hQ₁e : q = Q₁ e)
    (hhe : h e = -e)
    (hEeq : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hVHdecomp : ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace H,
      ∃ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
        ∃ α : ZMod p, u = x + α • e)
    (hEVB : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤ VB)
    (hπ : ∀ v : VB, π v.1 = v) (hf : ∀ v : VB, f v.1 = 0)
    (hπe : π e = 0) (hfe : f e = 1)
    (hglueE : ∀ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
      glueForm Q₂ c q VB π f x = Q₁ x) :
    ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace H,
      glueForm Q₂ c q VB π f u = Q₁ u := by
  intro u hu
  obtain ⟨x, hxE, α, rfl⟩ := hVHdecomp u hu
  have hxVB : x ∈ VB := hEVB hxE
  have hQ₁x_e : QuadraticMap.polar Q₁ x e = 0 :=
    polar_eq_zero_of_mem_reflStab hp hD hoQ₁ hhe hEeq hxE
  have hQxe : QuadraticMap.polar (glueForm Q₂ c q VB π f) x e = 0 := by
    change QuadraticMap.polar (extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q) x e = 0
    rw [polar_extendForm]
    have hπx : π x = ⟨x, hxVB⟩ := hπ ⟨x, hxVB⟩
    have hfx : f x = 0 := hf ⟨x, hxVB⟩
    rw [hπx, hπe, hfx, hfe, QuadraticMap.polar_zero_right
      (c⁻¹ • (Q₂.comp VB.subtype)), zero_mul, mul_zero, add_zero]
  have h1 : glueForm Q₂ c q VB π f (x + α • e) = Q₁ x + α ^ 2 * q := by
    have hQe : glueForm Q₂ c q VB π f e = q := by
      change extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q e = q
      exact extendForm_apply_e _ π f q hπe hfe
    rw [QuadraticMap.map_add (glueForm Q₂ c q VB π f) x (α • e),
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hglueE x hxE, hQe,
      QuadraticMap.polar_smul_right, hQxe, smul_eq_mul, mul_zero, add_zero]
  have h2' : Q₁ (x + α • e) = Q₁ x + α ^ 2 * Q₁ e := by
    rw [QuadraticMap.map_add Q₁ x (α • e),
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, QuadraticMap.polar_smul_right,
      hQ₁x_e, smul_eq_mul, mul_zero, add_zero]
  rw [h1, h2', hQ₁e]

private theorem glueForm_polar_eq_zero [Module.Finite (ZMod p) U]
    {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hD : LemmaTwoSevenData p G H B h) {Q₂ : QuadraticForm (ZMod p) U} {c q : ZMod p}
    {e : U} {VB : Submodule (ZMod p) U} {π : U →ₗ[ZMod p] VB}
    {f : U →ₗ[ZMod p] ZMod p}
    (hQ₂iso : ∀ g ∈ B, IsIsom p Q₂ g) (hXH : reflStab p H h ≤ H)
    (hXB : reflStab p H h ≤ B)
    (hVB : VB = LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hVHdecomp : ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace H,
      ∃ x ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
        ∃ α : ZMod p, u = x + α • e)
    (hEVB : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤ VB)
    (hπ : ∀ v : VB, π v.1 = v) (hf : ∀ v : VB, f v.1 = 0)
    (hπe : π e = 0) (hfe : f e = 1) :
    ∀ a ∈ HardMathSupport.Kantor79.commutatorSpace H, ∀ z ∈ centralizerSpace H,
      QuadraticMap.polar (glueForm Q₂ c q VB π f) a z = 0 := by
  intro a ha z hz
  obtain ⟨x, hxE, α, rfl⟩ := hVHdecomp a ha
  have hxVB : x ∈ VB := hEVB hxE
  have hzVB : z ∈ VB := by
    rw [hVB, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact (mem_centralizerSpace.mp hz) h hD.mem
  have hzX : z ∈ centralizerSpace (reflStab p H h) := centralizerSpace_le_of_le hXH hz
  have hpq := polar_eq_zero_of_mem_centralizerSpace (X := reflStab p H h)
    (fun g hg => hQ₂iso g (hXB hg)) hzX hxE
  rw [QuadraticMap.polar_comm] at hpq
  have hπx : π x = ⟨x, hxVB⟩ := hπ ⟨x, hxVB⟩
  have hπz : π z = ⟨z, hzVB⟩ := hπ ⟨z, hzVB⟩
  have hfx : f x = 0 := hf ⟨x, hxVB⟩
  have hfz : f z = 0 := hf ⟨z, hzVB⟩
  have hQ'pol : QuadraticMap.polar (c⁻¹ • (Q₂.comp VB.subtype)) ⟨x, hxVB⟩ ⟨z, hzVB⟩ =
      c⁻¹ * QuadraticMap.polar Q₂ x z := by
    have h := QuadraticMap.polar_smul (Q₂.comp VB.subtype) c⁻¹ ⟨x, hxVB⟩ ⟨z, hzVB⟩
    simpa [QuadraticMap.polar, QuadraticMap.comp_apply, Submodule.coe_subtype, smul_eq_mul]
      using h
  have hQxz : QuadraticMap.polar (glueForm Q₂ c q VB π f) x z = 0 := by
    change QuadraticMap.polar (extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q) x z = 0
    rw [polar_extendForm, hπx, hπz, hfx, hfz, hQ'pol, hpq]
    simp
  have hQez : QuadraticMap.polar (glueForm Q₂ c q VB π f) e z = 0 := by
    change QuadraticMap.polar (extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q) e z = 0
    rw [polar_extendForm, hπe, hπz, hfe, hfz, QuadraticMap.polar_zero_left
      (c⁻¹ • (Q₂.comp VB.subtype)), one_mul, mul_zero, add_zero]
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hQxz, hQez,
    smul_eq_mul, mul_zero, add_zero]

private theorem glueForm_eq_inv_mul_on_commutatorSpace [Module.Finite (ZMod p) U]
    {B : Subgroup (U ≃ₗ[ZMod p] U)}
    {Q₂ : QuadraticForm (ZMod p) U} {c q : ZMod p}
    {VB : Submodule (ZMod p) U} {π : U →ₗ[ZMod p] VB}
    {f : U →ₗ[ZMod p] ZMod p}
    (hQ₂iso : ∀ g ∈ B, IsIsom p Q₂ g)
    (hVB : VB = HardMathSupport.Kantor79.commutatorSpace B)
    (hπ : ∀ v : VB, π v.1 = v) (hf : ∀ v : VB, f v.1 = 0) :
    ∀ y ∈ HardMathSupport.Kantor79.commutatorSpace B,
      glueForm Q₂ c q VB π f y = c⁻¹ * Q₂ y ∧
        ∀ g ∈ B, glueForm Q₂ c q VB π f (g y) = glueForm Q₂ c q VB π f y := by
  intro y hy
  have hyVB : y ∈ VB := by rw [hVB]; exact hy
  have hcompQ : (extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q).comp VB.subtype =
      c⁻¹ • (Q₂.comp VB.subtype) := extendForm_comp_subtype _ π f q hπ hf
  have hQy : glueForm Q₂ c q VB π f y = c⁻¹ * Q₂ y := by
    have hy' := congrArg (fun Qf : QuadraticForm (ZMod p) VB => Qf ⟨y, hyVB⟩) hcompQ
    simp only [QuadraticMap.comp_apply, Submodule.coe_subtype] at hy'
    change extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q y = c⁻¹ * Q₂ y
    rw [hy']
    rfl
  refine ⟨hQy, fun g hg => ?_⟩
  have hgyVB : g y ∈ VB := by
    rw [hVB]
    exact apply_mem_commutatorSpace hg hy
  have hgy' := congrArg (fun Qf : QuadraticForm (ZMod p) VB => Qf ⟨g y, hgyVB⟩) hcompQ
  simp only [QuadraticMap.comp_apply, Submodule.coe_subtype] at hgy'
  have hval : glueForm Q₂ c q VB π f (g y) = c⁻¹ * Q₂ (g y) := by
    change extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q (g y) = c⁻¹ * Q₂ (g y)
    rw [hgy']
    rfl
  rw [hval, hQy, hQ₂iso g hg y]

private theorem glueForm_polar_eq_zero_right [Module.Finite (ZMod p) U]
    {Q₂ : QuadraticForm (ZMod p) U} {c q : ZMod p} {VB : Submodule (ZMod p) U}
    {π : U →ₗ[ZMod p] VB} {f : U →ₗ[ZMod p] ZMod p}
    (hπC : ∀ z : U, z ∈ centralizerSpace B → π z = 0)
    (hf : ∀ v : VB, f v.1 = 0) :
    ∀ y ∈ VB, ∀ z : U, z ∈ centralizerSpace B →
      QuadraticMap.polar (glueForm Q₂ c q VB π f) y z = 0 := by
  intro y hy z hz
  change QuadraticMap.polar (extendForm (c⁻¹ • (Q₂.comp VB.subtype)) π f q) y z = 0
  rw [polar_extendForm]
  have hπz : π z = 0 := hπC z hz
  have hfy : f y = 0 := hf ⟨y, hy⟩
  rw [hπz, hfy, QuadraticMap.polar_zero_right (c⁻¹ • (Q₂.comp VB.subtype)),
    zero_mul, mul_zero, add_zero]

private theorem glueForm_isIsom_of_mem [Module.Finite (ZMod p) U]
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {Q₂ : QuadraticForm (ZMod p) U} {c q : ZMod p}
    {VB : Submodule (ZMod p) U} {π : U →ₗ[ZMod p] VB}
    {f : U →ₗ[ZMod p] ZMod p}
    (hQ₂iso : ∀ g ∈ B, IsIsom p Q₂ g)
    (hVB : VB = HardMathSupport.Kantor79.commutatorSpace B)
    (hπC : ∀ z : U, z ∈ centralizerSpace B → π z = 0)
    (hsplitB : SplitSupport B (Module.finrank (ZMod p) U - 1))
    (hπ : ∀ v : VB, π v.1 = v) (hf : ∀ v : VB, f v.1 = 0) :
    ∀ g ∈ B, IsIsom p (glueForm Q₂ c q VB π f) g := by
  intro g hg v
  have htop : VB ⊔ centralizerSpace B = ⊤ := by
    rw [hVB]
    exact hsplitB.1.sup_eq_top
  have hv : v ∈ VB ⊔ centralizerSpace B := by
    rw [htop]
    trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  have hyB : y ∈ HardMathSupport.Kantor79.commutatorSpace B := by simpa only [hVB] using hy
  have hgy : g y ∈ VB := by
    rw [hVB]
    exact apply_mem_commutatorSpace hg hyB
  have hgz : g z = z := (mem_centralizerSpace.mp hz) g hg
  obtain ⟨hQy, hQgy'⟩ :=
    glueForm_eq_inv_mul_on_commutatorSpace (Q₂ := Q₂) (c := c) (q := q) (VB := VB) (π := π) (f := f)
      hQ₂iso hVB hπ hf y hyB
  have hQgy : glueForm Q₂ c q VB π f (g y) = glueForm Q₂ c q VB π f y := hQgy' g hg
  have hperp_y : QuadraticMap.polar (glueForm Q₂ c q VB π f) y z = 0 :=
    glueForm_polar_eq_zero_right (Q₂ := Q₂) (c := c) (q := q) (VB := VB) (π := π) (f := f)
      hπC hf y hy z hz
  have hperp_gy : QuadraticMap.polar (glueForm Q₂ c q VB π f) (g y) z = 0 :=
    glueForm_polar_eq_zero_right (Q₂ := Q₂) (c := c) (q := q) (VB := VB) (π := π) (f := f)
      hπC hf (g y) hgy z hz
  rw [map_add, hgz]
  calc glueForm Q₂ c q VB π f (g y + z)
      = glueForm Q₂ c q VB π f (g y) + glueForm Q₂ c q VB π f z +
        QuadraticMap.polar (glueForm Q₂ c q VB π f) (g y) z :=
        QuadraticMap.map_add _ _ _
    _ = glueForm Q₂ c q VB π f (g y) + glueForm Q₂ c q VB π f z := by
        rw [hperp_gy]; abel
    _ = glueForm Q₂ c q VB π f y + glueForm Q₂ c q VB π f z := by rw [hQgy]
    _ = glueForm Q₂ c q VB π f y + glueForm Q₂ c q VB π f z +
        QuadraticMap.polar (glueForm Q₂ c q VB π f) y z := by rw [hperp_y]; abel
    _ = glueForm Q₂ c q VB π f (y + z) :=
        (QuadraticMap.map_add (glueForm Q₂ c q VB π f) y z).symm

theorem exists_isOrthOn_of_lemmaTwoSevenData (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    (hcomp : ∃ Q₁ Q₂ : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q₁).Nondegenerate ∧
      IsOrthOn p Q₁ H ∧ (QuadraticMap.polarBilin Q₂).Nondegenerate ∧ (∀ g ∈ B, IsIsom p Q₂ g) ∧
      ∃ c : ZMod p, c ≠ 0 ∧
        ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h), Q₂ v = c * Q₁ v) :
    ∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      IsOrthOn p Q H ∧ ∀ g ∈ B, IsIsom p Q g := by
  obtain ⟨Q₁, Q₂, hQ₁nd, hoQ₁, hQ₂nd, hQ₂iso, c, hcne, hcompE⟩ := hcomp
  obtain ⟨hVBker, hCBmem⟩ :=
    commutatorSpace_eq_ker_of_isCentralizingSplit hp
      (le_trans (by norm_num) hD.setting.four_le) hD.split hD.isRefl
  obtain ⟨e, VB, CB, he0, hhe, hQ₁e, hVB, hCB, hCBspan⟩ := exists_root_decomp hp hD hQ₁nd hoQ₁
  have heCB : e ∈ CB := hCBspan.symm ▸ Submodule.mem_span_singleton_self e
  have hEeq := exists_plane_eq hp hD hQ₁nd hoQ₁
  have hEVB : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤ VB := by
    rw [hEeq, hVB, hVBker]
    exact inf_le_right
  have hVHdecomp := exists_commutatorSpace_decomp hp hD hhe (hCB.trans hCBmem) hCBspan hEeq
  have hsplitBC : IsCompl VB CB := by
    rw [hVB, hCB]
    exact hD.split.2.2.1.1
  obtain ⟨π, f, hπe, hπV, hfV, hfe, hker, hπC⟩ :=
    exists_proj hsplitBC he0 (hCB ▸ heCB) hCBspan
  have hQ₂VBnd : (QuadraticMap.polarBilin (Q₂.comp VB.subtype)).Nondegenerate := by
    rw [hVB]
    exact CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
      (polarNondegOn_commutatorSpace (X := B) (Q := Q₂) hQ₂nd hQ₂iso hD.split.2.2.1.1)
  let q : ZMod p := Q₁ e
  let Q : QuadraticForm (ZMod p) U := glueForm Q₂ c q VB π f
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    glueForm_nondegenerate hp hcne (by simpa [q] using hQ₁e) hQ₂VBnd π f hCBspan hker
      hπV hfV hπe hfe
  have hglueE := glueForm_eq_on_reflStab (Q₂ := Q₂) (c := c) (q := q) (VB := VB)
    (π := π) (f := f) hcompE hEVB hcne hπV hfV
  have hQeq := glueForm_eq_on_commutatorSpace hp hD hoQ₁ (show q = Q₁ e from rfl) hhe hEeq
    hVHdecomp hEVB hπV hfV hπe hfe hglueE
  have hperp := glueForm_polar_eq_zero (Q₂ := Q₂) (c := c) (q := q) (VB := VB)
    (π := π) (f := f) hD hQ₂iso (reflSubgroupIn_le H _) hD.split.2.2.2.2
    (hVB.trans hVBker) hVHdecomp hEVB hπV hfV hπe hfe
  have hBiso := glueForm_isIsom_of_mem (Q₂ := Q₂) (c := c) (q := q) (VB := VB)
    (π := π) (f := f) hQ₂iso hVB
    (fun z hz => hπC z (hCB.symm ▸ hz)) hD.split.2.2.1 hπV hfV
  have hpol := polar_eq_of_eq_on_commutatorSpace hoQ₁ hD.setting.sub.2.1 hQeq hperp
  have hoQ : IsOrthOn p Q H := by
    rcases hoQ₁ with hfull | ⟨c₀, hc₀, hclass⟩
    · left
      exact isOrthOn_of_eq_on_commutatorSpace_full hp hQnd hQ₁nd hfull hQeq hpol
    · exact isOrthOn_of_eq_on_commutatorSpace_class hp hQnd hQ₁nd hc₀ hclass hQeq hpol
  exact ⟨Q, hQnd, hoQ, hBiso⟩

end CFSG.StandardType.ZS

end
