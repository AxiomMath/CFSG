module

public import CFSG.RankThree.PartOne.KE.CoreInner

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE
open scoped Pointwise commutatorElement

set_option linter.unusedSectionVars false

section Core

variable {C : Type*} [Group C] [Finite C] {p : ℕ}

abbrev coreM (B : Subgroup (MulAut C)) (x : C) : Subgroup (MulAut C) :=
  B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))

abbrev coreR (p : ℕ) (B : Subgroup (MulAut C)) (x : C) : Subgroup (MulAut C) :=
  inSubgroup (aschbacherSolvableCore p) (coreM B x)

def coreV (p : ℕ) (B : Subgroup (MulAut C)) (x : C) : Subgroup C :=
  (coreR p B x).comap (MulAut.conj : C →* MulAut C) ⊓ Subgroup.centralizer ({x} : Set C)

theorem coreR_le_coreM (B : Subgroup (MulAut C)) (x : C) : coreR p B x ≤ coreM B x :=
  Subgroup.map_subtype_le _

theorem coreR_conj_mem {B : Subgroup (MulAut C)} {x : C} {m s : MulAut C}
    (hm : m ∈ coreM B x) (hs : s ∈ coreR p B x) : m * s * m⁻¹ ∈ coreR p B x := by
  obtain ⟨s', hs', rfl⟩ := hs
  exact ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, (aschbacherSolvableCore_normal p (coreM B x)).conj_mem s' hs'
    ⟨m, hm⟩, rfl⟩

theorem coreR_solvable (hp : p.Prime) (B : Subgroup (MulAut C)) (x : C) :
    Group.IsSolvable (coreR p B x) := by
  have h := (solvable_prime_complement_core_characterization (H := coreM B x) hp).1
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore p (coreM B x)) (coreM B x).subtype
      (coreM B x).subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)

theorem coreR_card (hp : p.Prime) (B : Subgroup (MulAut C)) (x : C) :
    ¬ p ∣ Nat.card (coreR p B x) := by
  have h := (solvable_prime_complement_core_characterization (H := coreM B x) hp).2.2.1
  change ¬ p ∣ Nat.card ((aschbacherSolvableCore p (coreM B x)).map (coreM B x).subtype)
  rw [Subgroup.card_map_of_injective (coreM B x).subtype_injective]
  exact h

theorem conj_mem_coreM {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B)
    {x d : C} (hd : d ∈ Subgroup.centralizer ({x} : Set C)) :
    (MulAut.conj d : MulAut C) ∈ coreM B x := by
  refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
  rw [Set.mem_singleton_iff] at hh
  subst hh
  rw [← map_mul, ← map_mul]
  exact congrArg MulAut.conj (Subgroup.mem_centralizer_singleton_iff.1 hd).symm

theorem mem_coreV {B : Subgroup (MulAut C)} {x v : C} :
    v ∈ coreV p B x ↔ (MulAut.conj v : MulAut C) ∈ coreR p B x ∧
      v ∈ Subgroup.centralizer ({x} : Set C) := Iff.rfl

theorem coreV_le_centralizer (B : Subgroup (MulAut C)) (x : C) :
    coreV p B x ≤ Subgroup.centralizer ({x} : Set C) := inf_le_right

theorem coreV_conj_mem {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C} {d v : C}
    (hd : d ∈ Subgroup.centralizer ({x} : Set C)) (hv : v ∈ coreV p B x) :
    d * v * d⁻¹ ∈ coreV p B x := by
  have hv1 := (Subgroup.mem_inf.1 hv).1
  have hv2 := (Subgroup.mem_inf.1 hv).2
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hd hv2) (inv_mem hd)⟩
  have h := coreR_conj_mem (conj_mem_coreM hB hd) hv1
  rw [Subgroup.mem_comap]
  simpa [map_mul, map_inv] using h

theorem coreV_solvable (hp : p.Prime) (hC : Subgroup.center C = ⊥) (B : Subgroup (MulAut C))
    (x : C) : Group.IsSolvable (coreV p B x) := by
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  have := coreR_solvable hp B x
  let f : coreV p B x →* coreR p B x :=
    ((MulAut.conj : C →* MulAut C).comp (coreV p B x).subtype).codRestrict (coreR p B x)
      fun v => (Subgroup.mem_inf.1 v.2).1
  have hfi : Function.Injective f := fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))
  exact Group.isSolvable_of_isSolvable_injective (f := f) hfi

theorem coreV_card (hp : p.Prime) (hC : Subgroup.center C = ⊥) (B : Subgroup (MulAut C))
    (x : C) : ¬ p ∣ Nat.card (coreV p B x) := by
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  intro h
  let f : coreV p B x →* coreR p B x :=
    ((MulAut.conj : C →* MulAut C).comp (coreV p B x).subtype).codRestrict (coreR p B x)
      fun v => (Subgroup.mem_inf.1 v.2).1
  have hfi : Function.Injective f := fun a b hab =>
    Subtype.ext (hinj (congrArg Subtype.val hab))
  exact coreR_card hp B x (h.trans (Subgroup.card_dvd_of_injective f hfi))

theorem fix_of_mem_coreM (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)} {x : C}
    {η : MulAut C} (hη : η ∈ coreM B x) : η x = x := by
  refine fixes_of_commute_conj hC η x ?_
  have h := Subgroup.mem_centralizer_iff.1 hη.2 (MulAut.conj x) rfl
  exact h.symm

theorem maps_centralizer_of_mem_coreM (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    {x : C} {η : MulAut C} (hη : η ∈ coreM B x) {d : C}
    (hd : d ∈ Subgroup.centralizer ({x} : Set C)) :
    η d ∈ Subgroup.centralizer ({x} : Set C) := by
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have h := Subgroup.mem_centralizer_singleton_iff.1 hd
  have hx := fix_of_mem_coreM hC hη
  calc η d * x = η d * η x := by rw [hx]
    _ = η (d * x) := (map_mul η d x).symm
    _ = η (x * d) := by rw [h]
    _ = η x * η d := map_mul η x d
    _ = x * η d := by rw [hx]

theorem eta_mul_inv_mem_coreV (hC : Subgroup.center C = ⊥)
    {B : Subgroup (MulAut C)} (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    {η : MulAut C} (hη : η ∈ coreR p B x) {d : C}
    (hd : d ∈ Subgroup.centralizer ({x} : Set C)) : η d * d⁻¹ ∈ coreV p B x := by
  have hηM := coreR_le_coreM B x hη
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (maps_centralizer_of_mem_coreM hC hηM hd) (inv_mem hd)⟩
  rw [Subgroup.mem_comap]
  have h1 : (MulAut.conj (η d * d⁻¹) : MulAut C) =
      η * (MulAut.conj d * η⁻¹ * (MulAut.conj d)⁻¹) := by
    rw [map_mul, map_inv, ← aut_mul_conj_mul_inv]
    simp only [mul_assoc]
  rw [h1]
  exact mul_mem hη (coreR_conj_mem (conj_mem_coreM hB hd) (inv_mem hη))

end Core

section Perfect

theorem eq_of_mul_inv_mem_abelian {G : Type*} [Group G] (η : MulAut G) {Q V : Subgroup G}
    (hQ : ⁅Q, Q⁆ = Q) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hV : ∀ d ∈ Q, η d * d⁻¹ ∈ V) (hcomm : ∀ v ∈ V, ∀ d ∈ Q, v * d = d * v) :
    ∀ d ∈ Q, η d = d := by
  set w : G → G := fun d => η d * d⁻¹ with hw
  have hmul : ∀ d₁ ∈ Q, ∀ d₂ ∈ Q, w (d₁ * d₂) = w d₁ * w d₂ := by
    intro d₁ hd₁ d₂ hd₂
    have hc := hcomm (w d₂) (hV d₂ hd₂) d₁ hd₁
    simp only [hw, map_mul, mul_inv_rev]
    calc η d₁ * η d₂ * (d₂⁻¹ * d₁⁻¹) = η d₁ * (η d₂ * d₂⁻¹) * d₁⁻¹ := by group
      _ = η d₁ * (d₁⁻¹ * ((d₁ * (η d₂ * d₂⁻¹)) * d₁⁻¹)) := by group
      _ = η d₁ * d₁⁻¹ * (η d₂ * d₂⁻¹) := by
        have : d₁ * (η d₂ * d₂⁻¹) = (η d₂ * d₂⁻¹) * d₁ := hc.symm
        rw [this]
        group
  have hone : w 1 = 1 := by simp [hw]
  have hinv : ∀ d ∈ Q, w d⁻¹ = (w d)⁻¹ := by
    intro d hd
    have h := hmul d hd d⁻¹ (inv_mem hd)
    rw [mul_inv_cancel, hone] at h
    exact (inv_eq_of_mul_eq_one_right h.symm).symm
  have hcomm_w : ∀ d₁ ∈ Q, ∀ d₂ ∈ Q, w ⁅d₁, d₂⁆ = 1 := by
    intro d₁ hd₁ d₂ hd₂
    have e : ⁅d₁, d₂⁆ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := rfl
    have h12 := mul_mem hd₁ hd₂
    have h123 := mul_mem h12 (inv_mem hd₁)
    rw [e, hmul _ h123 _ (inv_mem hd₂), hmul _ h12 _ (inv_mem hd₁), hmul _ hd₁ _ hd₂,
      hinv d₁ hd₁, hinv d₂ hd₂]
    have hv1 := hV d₁ hd₁
    have hv2 := hV d₂ hd₂
    have c12 := hVab _ hv1 _ hv2
    simp only [hw] at c12 ⊢
    calc η d₁ * d₁⁻¹ * (η d₂ * d₂⁻¹) * (η d₁ * d₁⁻¹)⁻¹ * (η d₂ * d₂⁻¹)⁻¹
        = (η d₁ * d₁⁻¹ * (η d₂ * d₂⁻¹)) * ((η d₂ * d₂⁻¹) * (η d₁ * d₁⁻¹))⁻¹ := by group
      _ = 1 := by rw [c12]; group
  intro d hd
  have hall : ∀ g ∈ (⁅Q, Q⁆ : Subgroup G), w g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact hcomm_w a ha b hb
    | one => exact hone
    | mul x y hx hy hx' hy' =>
      have hxQ : x ∈ Q := hQ ▸ hx
      have hyQ : y ∈ Q := hQ ▸ hy
      rw [hmul x hxQ y hyQ, hx', hy', mul_one]
    | inv x hx hx' =>
      have hxQ : x ∈ Q := hQ ▸ hx
      rw [hinv x hxQ, hx', inv_one]
  have hd' : d ∈ (⁅Q, Q⁆ : Subgroup G) := by rw [hQ]; exact hd
  have h1 : w d = 1 := hall d hd'
  have : η d * d⁻¹ = 1 := h1
  exact mul_inv_eq_one.1 this

end Perfect

end CFSG.RankThree.PartOne.KE8F
