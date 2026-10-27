module

public import CFSG.Quasithin.Vol2.Ch11SecS12F
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Quasithin.Background.OperatorJordanHolderJH1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open CFSG.Quasithin.Vol2.Ch11
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.OperatorJH
open scoped MatrixGroups

variable {G : Type} [Group G]

section Generic

variable {Y K : Subgroup G} {x : G} {F : Type} [Field F] {α₀ : ↥K →* ↥(StatedSL 2 F)}

theorem isLabFactor_of_nat (hα : Function.Surjective α₀) (hKY : K ≤ Y) {C S : Subgroup G}
    {a : F} (hCS : C ≤ S) (hSC : S ≤ Subgroup.normalizer (C : Set G))
    (hYC : Y ≤ Subgroup.normalizer (C : Set G)) (hYS : Y ≤ Subgroup.normalizer (S : Set G))
    (h : IsNatEigSection K x α₀ C S a) : IsLabFactor Y K x α₀ C S (some a) := by
  have hKS : K ≤ Subgroup.normalizer (S : Set G) := hKY.trans hYS
  refine ⟨lt_of_le_of_ne hCS fun heq => ?_, hSC, hYC, hYS, fun J hCJ hJS _ hYJ =>
    h.eq_or_eq le_rfl hα hKS hCJ hJS (hKY.trans hYJ), h⟩
  obtain ⟨β, hβs, hβk, -, -⟩ := h
  obtain ⟨c, hc⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have h1 : (c : G) ∈ C := heq ▸ c.2
  have h2 := (hβk c).mpr h1
  rw [hc] at h2
  have := congrArg (fun w : Multiplicative (Fin 2 → F) => Multiplicative.toAdd w 0) h2
  simp at this

theorem exists_isLabSeries_central [Finite G] {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hYC : Y ≤ Subgroup.normalizer (C : Set G))
    (hYD : Y ≤ Subgroup.normalizer (D : Set G))
    (hcent : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈ C) :
    ∃ l : List (Subgroup G × Option F), IsLabSeries Y K x α₀ C l D ∧ labMultiset l = 0 := by
  obtain ⟨t, ht⟩ := exists_ySeries (Y := Y) _ rfl hCD hDC hYC hYD
  have key : ∀ (t : List (Subgroup G)) (D : Subgroup G), IsYSeries Y C t D →
      (∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈ C) →
      ∃ l : List (Subgroup G × Option F), IsLabSeries Y K x α₀ C l D ∧ ∀ p ∈ l, p.2 = none := by
    intro t
    induction t with
    | nil =>
      intro D hD _
      exact ⟨[], hD, fun p hp => absurd hp List.not_mem_nil⟩
    | cons S t ih =>
      intro D hD hc
      obtain ⟨hS, ht⟩ := hD
      have hSD : S ≤ D := hS.1.le
      obtain ⟨l, hl, hln⟩ := ih S ht fun k hk s hs => hc k hk s (hSD hs)
      have hCS : C ≤ S := ht.le
      have hf : IsLabFactor Y K x α₀ S D none :=
        ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2, fun k hk d hd => hCS (hc k hk d hd)⟩
      refine ⟨l ++ [(D, none)], hl.append (isLabSeries_singleton hf), fun p hp => ?_⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact hln p hp
      · rw [List.mem_singleton] at hp
        rw [hp]
  obtain ⟨l, hl, hln⟩ := key t D ht hcent
  exact ⟨l, hl, labMultiset_eq_zero_of_forall hln⟩

end Generic

namespace NatData3'

variable {n : ℕ} {L K V V₁ : Subgroup G} (D : NatData3 n L K V V₁)

@[expose] noncomputable def betaV : ↥V →* Multiplicative (Fin 2 → GaloisField 2 n) where
  toFun v := Multiplicative.ofAdd ![Multiplicative.toAdd (D.ψ v) 1,
    Multiplicative.toAdd (D.ψ v) 2]
  map_one' := by
    apply Multiplicative.toAdd.injective
    rw [map_one, toAdd_one, toAdd_ofAdd, toAdd_one]
    ext i
    fin_cases i <;> rfl
  map_mul' a b := by
    rw [map_mul, toAdd_mul, ← ofAdd_add]
    congr 1
    ext i
    fin_cases i <;> rfl

variable [Finite G]

theorem natEig_V (hV₁V : V₁ ≤ V) {x : G} (hxL : x ∈ L) {c : GaloisField 2 n}
    (hxc : ∀ w : Fin 3 → GaloisField 2 n, D.θ ⟨x, hxL⟩ • w = c • w) :
    IsNatEigSection (LOf L V₁) x (alpha0 D hV₁V) V₁ V c := by
  refine ⟨betaV D, fun y => ?_, fun v => ?_, fun k v v' hv' => ?_, fun v v' hv' => ?_⟩
  · obtain ⟨v, hv⟩ := D.ψ.surjective (Multiplicative.ofAdd ![0, Multiplicative.toAdd y 0,
      Multiplicative.toAdd y 1])
    refine ⟨v, ?_⟩
    apply Multiplicative.toAdd.injective
    show ![Multiplicative.toAdd (D.ψ v) 1, Multiplicative.toAdd (D.ψ v) 2] = _
    rw [hv, toAdd_ofAdd]
    ext i
    fin_cases i <;> rfl
  · constructor
    · intro h1
      have h1' := congrArg Multiplicative.toAdd h1
      have e1 : Multiplicative.toAdd (D.ψ v) 1 = 0 := by
        have := congrFun h1' 0
        simpa [betaV] using this
      have e2 : Multiplicative.toAdd (D.ψ v) 2 = 0 := by
        have := congrFun h1' 1
        simpa [betaV] using this
      refine (D.line v).2 ⟨Multiplicative.toAdd (D.ψ v) 0, ?_⟩
      ext i
      fin_cases i <;> simp [vE, e1, e2]
    · intro hv
      obtain ⟨c', hc'⟩ := (D.line v).1 hv
      apply Multiplicative.toAdd.injective
      show ![Multiplicative.toAdd (D.ψ v) 1, Multiplicative.toAdd (D.ψ v) 2] = 0
      rw [hc']
      ext i
      fin_cases i <;> simp [vE]
  · have hkL : (k : G) ∈ L := lOf_le k.2
    have he := D.equiv ⟨k, hkL⟩ v
    have hvv : conjAct V ⟨(k : G), D.hnorm hkL⟩ v = v' := Subtype.ext (by
      rw [conjAct_coe_apply, hv'])
    rw [hvv] at he
    show ![Multiplicative.toAdd (D.ψ v') 1, Multiplicative.toAdd (D.ψ v') 2] = _
    rw [he, natAct3_apply, toAdd_ofAdd]
    have hl := levi_smul (theta1 D hV₁V k) (Multiplicative.toAdd (D.ψ v))
    rw [theta1_coe] at hl
    have hk : (Subgroup.inclusion lOf_le k : ↥L) = ⟨k, hkL⟩ := rfl
    rw [hk] at hl
    rw [hl, alpha0_coe]
    rfl
  · have he := D.equiv ⟨x, hxL⟩ v
    have hvv : conjAct V ⟨x, D.hnorm hxL⟩ v = v' := Subtype.ext (by
      rw [conjAct_coe_apply, hv'])
    rw [hvv] at he
    show ![Multiplicative.toAdd (D.ψ v') 1, Multiplicative.toAdd (D.ψ v') 2] =
      c • ![Multiplicative.toAdd (D.ψ v) 1, Multiplicative.toAdd (D.ψ v) 2]
    rw [he, natAct3_apply, toAdd_ofAdd, hxc]
    ext i
    fin_cases i <;> rfl

end NatData3'

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
