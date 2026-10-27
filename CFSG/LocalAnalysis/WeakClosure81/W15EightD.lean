module

public import CFSG.LocalAnalysis.WeakClosure81.W15EightC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_sup_le_conjClosure_sup (X Y H : Subgroup G) :
    conjClosure (X ⊔ Y) H ≤ conjClosure X H ⊔ conjClosure Y H := by
  refine conjClosure_le fun k hk z hz => ?_
  have hmem : z ∈ (Subgroup.closure ((X : Set G) ∪ (Y : Set G)) : Subgroup G) := by
    rwa [← Subgroup.sup_eq_closure]
  clear hz
  induction hmem using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · exact Subgroup.mem_sup_left (mem_conjClosure hk ha)
    · exact Subgroup.mem_sup_right (mem_conjClosure hk ha)
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ iha

@[expose] def zSub15 (V₀ U H' : Subgroup G) : Subgroup G :=
  conjClosure (U ⊔ v1Sub15 V₀ U) H'

@[expose] def Fam15 (V₀ V U S H' : Subgroup G) : Prop :=
  S ≤ H' ∧ ¬ V ≤ pCoreOf 2 H' ∧
    ∀ x ∈ zSub15 V₀ U H', ∀ y ∈ zSub15 V₀ U H', x * y = y * x

namespace Fam15

variable {V₀ V U S H' : Subgroup G}

theorem S_le (hF : Fam15 V₀ V U S H') : S ≤ H' := hF.1

theorem not_V_le_pCoreOf (hF : Fam15 V₀ V U S H') : ¬ V ≤ pCoreOf 2 H' := hF.2.1

theorem comm (hF : Fam15 V₀ V U S H') :
    ∀ x ∈ zSub15 V₀ U H', ∀ y ∈ zSub15 V₀ U H', x * y = y * x := hF.2.2

end Fam15

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem v1Sub15_comm_conj (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G))
    {x y : G} (hx : x ∈ v1Sub15 V₀ U) (hy : y ∈ v1Sub15 V₀ U) :
    x * (g * y * g⁻¹) = (g * y * g⁻¹) * x := by
  have hH := h.hyp
  by_cases hgM : g ∈ M
  · have hgN : g ∈ normalizer (V₀ : Set G) := by
      rw [hH.normalizer₀]
      exact hgM
    have hy' : g * y * g⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hgN y).1 hy.1
    exact hH.elemAbelian₀.comm hx.1 hy'
  · have hgi : g⁻¹ ∈ centralizer (U : Set G) := (centralizer (U : Set G)).inv_mem hg
    have hgiM : g⁻¹ ∉ M := fun hm => hgM (by simpa using M.inv_mem hm)
    have hne : conjSubgroup V₀ g⁻¹ ≠ V₀ := fun heq => hgiM (by
      have h1 := conjSubgroup_eq_iff_mem_normalizer.1 heq
      rwa [hH.normalizer₀] at h1)
    have hxn : x ∈ nVSub V₀ g⁻¹ := by
      refine mem_nVSub.2 ⟨hx.1, ?_⟩
      rw [← E3.conjSubgroup_normalizer, hH.normalizer₀]
      exact (h.v1Sub15_le_inf_conj hgi hx).2
    have hyb : g * y * g⁻¹ ∈ bSub V₀ g⁻¹ := by
      refine mem_bSub.2 ⟨?_, ?_⟩
      · rw [mem_conjSubgroup_iff, show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group]
        exact hy.1
      · rw [hH.normalizer₀]
        exact h.S_le_M (h.pCoreOf_le_S ((conj_mem_pCoreOf_iff hg y).2 hy.2))
    exact nVSub_comm_bSub hH.isTI hne hxn hyb

theorem isElemAbelian_conjClosure_v1Sub15 (h : Cex15 M V₀ V U S) {H : Subgroup G}
    (hH : H ≤ centralizer (U : Set G)) :
    IsElemAbelian 2 (conjClosure (v1Sub15 V₀ U) H) := by
  have hsq : ∀ z ∈ v1Sub15 V₀ U, z ^ 2 = 1 := fun z hz =>
    h.hyp.h6.elemAbelian.2 z (h.hyp.h6.le (v1Sub15_le_left V₀ U hz))
  unfold conjClosure
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · rintro a ⟨g, hg, y, hy, rfl⟩ b ⟨g', hg', y', hy', rfl⟩
    have key := h.v1Sub15_comm_conj ((centralizer (U : Set G)).mul_mem
      ((centralizer (U : Set G)).inv_mem (hH hg)) (hH hg')) hy hy'
    calc g * y * g⁻¹ * (g' * y' * g'⁻¹)
        = g * (y * ((g⁻¹ * g') * y' * (g⁻¹ * g')⁻¹)) * g⁻¹ := by group
      _ = g * (((g⁻¹ * g') * y' * (g⁻¹ * g')⁻¹) * y) * g⁻¹ := by rw [key]
      _ = g' * y' * g'⁻¹ * (g * y * g⁻¹) := by group
  · rintro a ⟨g, hg, y, hy, rfl⟩
    rw [conj_pow, hsq y hy]
    group

theorem zSub15_le_sup (V₀ U : Subgroup G) {H : Subgroup G} (hH : H ≤ centralizer (U : Set G)) :
    zSub15 V₀ U H ≤ U ⊔ conjClosure (v1Sub15 V₀ U) H := by
  refine (conjClosure_sup_le_conjClosure_sup U (v1Sub15 V₀ U) H).trans (sup_le_sup_right ?_ _)
  refine conjClosure_le fun k hk z hz => ?_
  have h1 : z * k = k * z := Subgroup.mem_centralizer_iff.1 (hH hk) z hz
  have h2 : k * z * k⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  rw [h2]
  exact hz

theorem centralizer_mem_fam (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) : Fam15 V₀ V U S (centralizer (U : Set G)) := by
  have hH : (centralizer (U : Set G)) ≤ centralizer (U : Set G) := le_rfl
  have hV₁H : v1Sub15 V₀ U ≤ centralizer (U : Set G) := fun x hx =>
    h.S_le_centralizer (h.V₀_le_S (v1Sub15_le_left V₀ U hx))
  refine ⟨h.S_le_centralizer, fun hV => hI.not_le_pCoreOf_centralizer hS h
    (h.hyp.h6.le.trans hV), fun x hx y hy => ?_⟩
  have hUab : IsElemAbelian 2 U := CFSG.Open.IsElemAbelian.mono h.hyp.h6.elemAbelian h.le
  have hNab := h.isElemAbelian_conjClosure_v1Sub15 hH
  have hNH : conjClosure (v1Sub15 V₀ U) (centralizer (U : Set G)) ≤ centralizer (U : Set G) :=
    conjClosure_le fun k hk z hz =>
      (centralizer (U : Set G)).mul_mem ((centralizer (U : Set G)).mul_mem hk (hV₁H hz))
        ((centralizer (U : Set G)).inv_mem hk)
  have hsup : IsElemAbelian 2 (U ⊔ conjClosure (v1Sub15 V₀ U) (centralizer (U : Set G))) :=
    hUab.sup_of_commute hNab fun a ha b hb => (Subgroup.mem_centralizer_iff.1 (hNH hb) a ha)
  have hle := zSub15_le_sup V₀ U hH
  exact hsup.comm (hle hx) (hle hy)

end Cex15

namespace Fam15

variable {M V₀ V U S H' : Subgroup G}

theorem isElemAbelian_zSub15 (h : Cex15 M V₀ V U S)
    (hF : Fam15 V₀ V U S H') : IsElemAbelian 2 (zSub15 V₀ U H') := by
  have hUV : U ⊔ v1Sub15 V₀ U ≤ V :=
    sup_le h.le ((v1Sub15_le_left V₀ U).trans h.hyp.h6.le)
  have hsq : ∀ z ∈ U ⊔ v1Sub15 V₀ U, z ^ 2 = 1 := fun z hz => h.hyp.h6.elemAbelian.2 z (hUV hz)
  have hcomm := hF.comm
  unfold zSub15 at hcomm ⊢
  unfold conjClosure at hcomm ⊢
  refine IsElemAbelian.closure_of_commute (fun a ha b hb =>
    hcomm a (Subgroup.subset_closure ha) b (Subgroup.subset_closure hb)) ?_
  rintro a ⟨k, hk, z, hz, rfl⟩
  rw [conj_pow, hsq z hz]
  group

theorem zSub15_le_pCoreOf (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') :
    zSub15 V₀ U H' ≤ pCoreOf 2 H' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUS : U ⊔ v1Sub15 V₀ U ≤ H' :=
    sup_le (h.le.trans (h.V_le_S.trans hF.S_le))
      (((v1Sub15_le_left V₀ U).trans h.V₀_le_S).trans hF.S_le)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_
    (le_normalizer_conjClosure _ _) (B2F.isPGroup_of_isElemAbelian (hF.isElemAbelian_zSub15 h))
  exact conjClosure_le fun k hk z hz => H'.mul_mem (H'.mul_mem hk (hUS hz)) (H'.inv_mem hk)

theorem U_le_pCoreOf (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') :
    U ≤ pCoreOf 2 H' :=
  (le_sup_left.trans (le_conjClosure _ _)).trans (hF.zSub15_le_pCoreOf h)

theorem v1_le_pCoreOf (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') :
    v1Sub15 V₀ U ≤ pCoreOf 2 H' :=
  (le_sup_right.trans (le_conjClosure _ _)).trans (hF.zSub15_le_pCoreOf h)

theorem not_V₀_le_pCoreOf (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') :
    ¬ V₀ ≤ pCoreOf 2 H' := fun hV₀ =>
  hF.not_V_le_pCoreOf (h.sup_eq ▸ sup_le (hF.U_le_pCoreOf h) hV₀)

end Fam15

end CFSG.LocalAnalysis.WeakClosure81
