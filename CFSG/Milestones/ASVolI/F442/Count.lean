module

public import CFSG.Milestones.ASVolI.F442.Perm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.ASVolI

section Count

variable {G : Type*} [Group G]

theorem burnsideF42g_card_conj_pred [Finite G] (a : G) (P : G → Prop) :
    Nat.card {g : G // P (g * a * g⁻¹)} =
      Nat.card {y : G // P y ∧ IsConj a y} * Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  classical
  haveI := Fintype.ofFinite G
  rw [Nat.subtype_card (Finset.univ.filter (fun g => P (g * a * g⁻¹))) (by simp),
    Nat.subtype_card (Finset.univ.filter (fun y => P y ∧ IsConj a y)) (by simp),
    Nat.subtype_card (Finset.univ.filter (fun g : G => g * a = a * g))
      (by simp [Subgroup.mem_centralizer_singleton_iff])]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g * a * g⁻¹)
      (t := Finset.univ.filter (fun y => P y ∧ IsConj a y)) (by
        intro g hg
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
        exact ⟨hg, isConj_iff.mpr ⟨g, rfl⟩⟩)]
  refine Finset.sum_const_nat fun y hy => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
  obtain ⟨r, hr⟩ := isConj_iff.mp hy.2
  refine Finset.card_nbij' (fun g => r⁻¹ * g) (fun c => r * c) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    have e : r⁻¹ * g * a * (r⁻¹ * g)⁻¹ = a := by
      calc r⁻¹ * g * a * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * a * g⁻¹) * r := by group
        _ = a := by rw [hg.2, ← hr]; group
    calc r⁻¹ * g * a = r⁻¹ * g * a * (r⁻¹ * g)⁻¹ * (r⁻¹ * g) := by group
      _ = a * (r⁻¹ * g) := by rw [e]
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    have e : r * c * a * (r * c)⁻¹ = y := by
      calc r * c * a * (r * c)⁻¹ = r * (c * a) * c⁻¹ * r⁻¹ := by group
        _ = y := by rw [hc, ← hr]; group
    refine ⟨?_, e⟩
    rw [e]
    exact hy.1
  · intro g _
    simp
  · intro c _
    simp

theorem burnsideF42g_pair_count [Finite G] (a b : G) :
    Nat.card {y : G // y * b = b * y ∧ IsConj a y} *
        Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card {y : G // y * a = a * y ∧ IsConj b y} *
        Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  rw [← burnsideF42g_card_conj_pred a (fun y => y * b = b * y),
    ← burnsideF42g_card_conj_pred b (fun y => y * a = a * y)]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.inv G) fun g => ?_)
  simp only [Equiv.inv_apply, inv_inv]
  constructor
  · intro h
    calc g⁻¹ * b * g * a = g⁻¹ * (b * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * b) * g := by rw [h]
      _ = a * (g⁻¹ * b * g) := by group
  · intro h
    calc g * a * g⁻¹ * b = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by rw [h]
      _ = b * (g * a * g⁻¹) := by group

end Count

section LemmaA

variable {Eb M : Type*} [Group Eb] [Group M] [Finite Eb] [Finite M]

theorem burnsideF42g_card_slice_eq {cb db : Eb} {c d : M}
    (ψ : Subgroup.centralizer ({cb} : Set Eb) →* M) (hψ : Function.Injective ψ)
    (hr : ψ.range = Subgroup.centralizer ({c} : Set M))
    (hf : ∀ x : Subgroup.centralizer ({cb} : Set Eb), IsConj db (x : Eb) ↔ IsConj d (ψ x)) :
    Nat.card {y : M // y * c = c * y ∧ IsConj d y} =
      Nat.card {x : Eb // x * cb = cb * x ∧ IsConj db x} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨ψ ⟨x.1,
    Subgroup.mem_centralizer_singleton_iff.mpr x.2.1⟩, ?_⟩) ⟨?_, ?_⟩)
  · refine ⟨?_, (hf _).mp x.2.2⟩
    have hmem : ψ ⟨x.1, Subgroup.mem_centralizer_singleton_iff.mpr x.2.1⟩ ∈
        Subgroup.centralizer ({c} : Set M) := hr ▸ ⟨_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  · intro x x' hxx
    have := hψ (congrArg Subtype.val hxx)
    exact Subtype.ext
      (congrArg (fun w : Subgroup.centralizer ({cb} : Set Eb) => (w : Eb)) this)
  · rintro ⟨y, hyc, hyd⟩
    have hmem : y ∈ ψ.range := hr ▸ Subgroup.mem_centralizer_singleton_iff.mpr hyc
    obtain ⟨x, rfl⟩ := hmem
    refine ⟨⟨x.1, Subgroup.mem_centralizer_singleton_iff.mp x.2, (hf x).mpr hyd⟩, ?_⟩
    rfl

theorem burnsideF42g_lemmaA {zb tb : Eb} {z t : M}
    (ψ₁ : Subgroup.centralizer ({zb} : Set Eb) →* M) (hψ₁ : Function.Injective ψ₁)
    (hr₁ : ψ₁.range = Subgroup.centralizer ({z} : Set M))
    (ψ₂ : Subgroup.centralizer ({tb} : Set Eb) →* M) (hψ₂ : Function.Injective ψ₂)
    (hX : ψ₂.range ≤ Subgroup.centralizer ({t} : Set M))
    (hf₁ : ∀ c : Subgroup.centralizer ({zb} : Set Eb), IsConj tb (c : Eb) ↔ IsConj t (ψ₁ c))
    (hf₂ : ∀ c : Subgroup.centralizer ({tb} : Set Eb), IsConj zb (c : Eb) ↔ IsConj z (ψ₂ c))
    (h40 : ∀ y ∈ Subgroup.centralizer ({t} : Set M), IsConj z y →
      ∃ k ∈ Subgroup.centralizer ({t} : Set M), k⁻¹ * y * k ∈ ψ₂.range)
    {y : M} (hyX : y ∈ ψ₂.range) (hyz : IsConj z y) {h : M}
    (hh : h ∈ Subgroup.centralizer ({t} : Set M)) (hhy : h⁻¹ * y * h ∈ ψ₂.range) :
    h ∈ ψ₂.range := by
  classical
  haveI := Fintype.ofFinite M
  have cM := burnsideF42g_pair_count z t
  have cE := burnsideF42g_pair_count zb tb
  have tr1 : Nat.card (Subgroup.centralizer ({z} : Set M)) =
      Nat.card (Subgroup.centralizer ({zb} : Set Eb)) := by
    rw [← hr₁]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ₁).toEquiv).symm
  have tr3 : Nat.card ψ₂.range = Nat.card (Subgroup.centralizer ({tb} : Set Eb)) :=
    (Nat.card_congr (MonoidHom.ofInjective hψ₂).toEquiv).symm
  have tr2 := burnsideF42g_card_slice_eq ψ₁ hψ₁ hr₁ hf₁
  have tr4 : Nat.card {y : M // y ∈ ψ₂.range ∧ IsConj z y} =
      Nat.card {x : Eb // x * tb = tb * x ∧ IsConj zb x} := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨ψ₂ ⟨x.1,
      Subgroup.mem_centralizer_singleton_iff.mpr x.2.1⟩, ⟨_, rfl⟩, (hf₂ _).mp x.2.2⟩) ⟨?_, ?_⟩)
    · intro x x' hxx
      have := hψ₂ (congrArg Subtype.val hxx)
      exact Subtype.ext
        (congrArg (fun w : Subgroup.centralizer ({tb} : Set Eb) => (w : Eb)) this)
    · rintro ⟨y, ⟨x, rfl⟩, hyd⟩
      exact ⟨⟨x.1, Subgroup.mem_centralizer_singleton_iff.mp x.2, (hf₂ x).mpr hyd⟩, rfl⟩
  rw [tr1, tr2] at cM
  rw [← tr4, ← tr3] at cE
  have hKz : 0 < Nat.card (Subgroup.centralizer ({zb} : Set Eb)) := Nat.card_pos
  have hcount : Nat.card {y : M // y * t = t * y ∧ IsConj z y} * Nat.card ψ₂.range =
      Nat.card {y : M // y ∈ ψ₂.range ∧ IsConj z y} *
        Nat.card (Subgroup.centralizer ({t} : Set M)) := by
    refine Nat.eq_of_mul_eq_mul_right hKz ?_
    calc Nat.card {y : M // y * t = t * y ∧ IsConj z y} * Nat.card ψ₂.range *
          Nat.card (Subgroup.centralizer ({zb} : Set Eb))
        = (Nat.card {y : M // y * t = t * y ∧ IsConj z y} *
            Nat.card (Subgroup.centralizer ({zb} : Set Eb))) * Nat.card ψ₂.range := by ring
      _ = Nat.card {x : Eb // x * zb = zb * x ∧ IsConj tb x} *
            Nat.card (Subgroup.centralizer ({t} : Set M)) * Nat.card ψ₂.range := by rw [cM]
      _ = (Nat.card {x : Eb // x * zb = zb * x ∧ IsConj tb x} * Nat.card ψ₂.range) *
            Nat.card (Subgroup.centralizer ({t} : Set M)) := by ring
      _ = (Nat.card {y : M // y ∈ ψ₂.range ∧ IsConj z y} *
            Nat.card (Subgroup.centralizer ({zb} : Set Eb))) *
            Nat.card (Subgroup.centralizer ({t} : Set M)) := by rw [cE]
      _ = _ := by ring
  set H := Subgroup.centralizer ({t} : Set M) with hHdef
  set X := ψ₂.range with hXdef
  set ΩH : Finset M := Finset.univ.filter (fun y => y ∈ H ∧ IsConj z y) with hΩH
  set ΩX : Finset M := Finset.univ.filter (fun y => y ∈ X ∧ IsConj z y) with hΩX
  set Hf : Finset M := Finset.univ.filter (fun y => y ∈ H) with hHf
  set Xf : Finset M := Finset.univ.filter (fun y => y ∈ X) with hXf
  have cΩH : Nat.card {y : M // y * t = t * y ∧ IsConj z y} = ΩH.card :=
    Nat.subtype_card _ (by simp [hΩH, hHdef, Subgroup.mem_centralizer_singleton_iff])
  have cΩX : Nat.card {y : M // y ∈ X ∧ IsConj z y} = ΩX.card :=
    Nat.subtype_card _ (by simp [hΩX])
  have cH : Nat.card H = Hf.card := Nat.subtype_card _ (by simp [hHf])
  have cX : Nat.card X = Xf.card := Nat.subtype_card _ (by simp [hXf])
  rw [cΩH, cΩX, cH, cX] at hcount
  set A : M → Finset M := fun y' => Hf.filter (fun k => k⁻¹ * y' * k ∈ X) with hA
  have hsum : ∑ y' ∈ ΩH, (A y').card = Hf.card * ΩX.card := by
    calc ∑ y' ∈ ΩH, (A y').card
        = ∑ y' ∈ ΩH, ∑ k ∈ Hf, (if k⁻¹ * y' * k ∈ X then 1 else 0) := by
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [hA, Finset.card_filter]
      _ = ∑ k ∈ Hf, ∑ y' ∈ ΩH, (if k⁻¹ * y' * k ∈ X then 1 else 0) := Finset.sum_comm
      _ = ∑ k ∈ Hf, (ΩH.filter (fun y' => k⁻¹ * y' * k ∈ X)).card := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.card_filter]
      _ = ∑ k ∈ Hf, ΩX.card := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [hHf, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          refine Finset.card_nbij' (fun y' => k⁻¹ * y' * k) (fun y => k * y * k⁻¹) ?_ ?_ ?_ ?_
          · intro y' hy'
            simp only [hΩH, hΩX, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and] at hy' ⊢
            exact ⟨hy'.2, hy'.1.2.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)⟩
          · intro y hy
            simp only [hΩH, hΩX, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
              true_and] at hy ⊢
            refine ⟨⟨H.mul_mem (H.mul_mem hk (hX hy.1)) (H.inv_mem hk),
              hy.2.trans (isConj_iff.mpr ⟨k, rfl⟩)⟩, ?_⟩
            rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group]
            exact hy.1
          · intro y' _
            simp only
            group
          · intro y _
            simp only
            group
      _ = Hf.card * ΩX.card := by rw [Finset.sum_const, smul_eq_mul]
  have hlb : ∀ y' ∈ ΩH, Xf.card ≤ (A y').card := by
    intro y' hy'
    simp only [hΩH, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
    obtain ⟨k, hk, hkX⟩ := h40 y' hy'.1 hy'.2
    refine Finset.card_le_card_of_injOn (fun x => k * x) ?_ ?_
    · intro x hx
      simp only [hXf, hA, hHf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx ⊢
      refine ⟨H.mul_mem hk (hX hx), ?_⟩
      rw [show (k * x)⁻¹ * y' * (k * x) = x⁻¹ * (k⁻¹ * y' * k) * x by group]
      exact X.mul_mem (X.mul_mem (X.inv_mem hx) hkX) hx
    · intro x _ x' _ hxx
      exact mul_left_cancel hxx
  have heq : ∑ y' ∈ ΩH, Xf.card = ∑ y' ∈ ΩH, (A y').card := by
    rw [hsum, Finset.sum_const, smul_eq_mul, hcount, mul_comm]
  have hall := (Finset.sum_eq_sum_iff_of_le hlb).mp heq
  have hyΩ : y ∈ ΩH := by
    simp only [hΩH, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hX hyX, hyz⟩
  have hsub : Xf ⊆ A y := by
    intro x hx
    simp only [hXf, hA, hHf, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hX hx, X.mul_mem (X.mul_mem (X.inv_mem hx) hyX) hx⟩
  have hXA := Finset.eq_of_subset_of_card_le hsub (hall y hyΩ).ge
  have hhA : h ∈ A y := by
    simp only [hA, hHf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hh, hhy⟩
  rw [← hXA] at hhA
  simpa [hXf] using hhA

end LemmaA

end CFSG.ASVolI
