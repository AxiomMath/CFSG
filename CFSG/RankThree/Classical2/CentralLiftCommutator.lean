module

public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools

public section

namespace CFSG.RankThree.Classical2

open scoped commutatorElement

section CentralLift

variable {Y T : Type*} [Group Y] [Group T]

theorem commutatorElement_mul_central_left {x y c : Y} (hc : c ∈ Subgroup.center Y) :
    ⁅x * c, y⁆ = ⁅x, y⁆ := by
  have hcy : c * y = y * c := (Subgroup.mem_center_iff.mp hc y).symm
  calc ⁅x * c, y⁆ = x * (c * y) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [commutatorElement_def]; group
    _ = x * (y * c) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [hcy]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem commutatorElement_mul_central_right {x y c : Y} (hc : c ∈ Subgroup.center Y) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_central_left hc, commutatorElement_inv]

theorem eq_one_of_sq_eq_one_of_pow_eq_one {G : Type*} [Monoid G] {z : G} {p : ℕ} (hp : Odd p)
    (h2 : z ^ 2 = 1) (hp1 : z ^ p = 1) : z = 1 := by
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hp1
  exact hp1

variable (φ : Y →* T)

theorem commutatorElement_eq_of_map_eq (hker : φ.ker ≤ Subgroup.center Y) {x x' y y' : Y}
    (hx : φ x = φ x') (hy : φ y = φ y') : ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hcx : x⁻¹ * x' ∈ Subgroup.center Y :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel])
  have hcy : y⁻¹ * y' ∈ Subgroup.center Y :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel])
  have h1 : x' = x * (x⁻¹ * x') := by group
  have h2 : y' = y * (y⁻¹ * y') := by group
  rw [h1, h2, commutatorElement_mul_central_left hcx, commutatorElement_mul_central_right hcy]

theorem commutatorElement_mem_ker {x y : Y} (h : Commute (φ x) (φ y)) : ⁅x, y⁆ ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact h.eq

@[expose] noncomputable def liftComm (hφ : Function.Surjective φ) (s t : T) : Y :=
  ⁅Function.surjInv hφ s, Function.surjInv hφ t⁆

variable {φ}

theorem commutatorElement_eq_liftComm (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (x y : Y) : ⁅x, y⁆ = liftComm φ hφ (φ x) (φ y) :=
  commutatorElement_eq_of_map_eq φ hker (Function.surjInv_eq hφ _).symm
    (Function.surjInv_eq hφ _).symm

theorem liftComm_eq (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {s t : T} {x y : Y} (hx : φ x = s) (hy : φ y = t) : liftComm φ hφ s t = ⁅x, y⁆ := by
  rw [commutatorElement_eq_liftComm hφ hker, hx, hy]

theorem liftComm_mem_ker (hφ : Function.Surjective φ) {s t : T} (h : Commute s t) :
    liftComm φ hφ s t ∈ φ.ker :=
  commutatorElement_mem_ker φ (by rw [Function.surjInv_eq hφ s, Function.surjInv_eq hφ t]; exact h)

theorem liftComm_mem_center (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {s t : T} (h : Commute s t) : liftComm φ hφ s t ∈ Subgroup.center Y :=
  hker (liftComm_mem_ker hφ h)

theorem liftComm_mul_left (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {s s' t : T} (h : Commute s' t) :
    liftComm φ hφ (s * s') t = liftComm φ hφ s t * liftComm φ hφ s' t := by
  set x := Function.surjInv hφ s
  set x' := Function.surjInv hφ s'
  set y := Function.surjInv hφ t
  have hx : φ x = s := Function.surjInv_eq hφ s
  have hx' : φ x' = s' := Function.surjInv_eq hφ s'
  have hy : φ y = t := Function.surjInv_eq hφ t
  rw [liftComm_eq hφ hker (x := x * x') (y := y) (by rw [map_mul, hx, hx']) hy,
    liftComm_eq hφ hker hx hy, liftComm_eq hφ hker hx' hy]
  exact CFSG.SectionRank.OddCover.commutatorElement_mul_left_of_mem_center
    (hker (commutatorElement_mem_ker φ (by rw [hx', hy]; exact h)))

theorem liftComm_mul_right (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {s t t' : T} (h : Commute s t') :
    liftComm φ hφ s (t * t') = liftComm φ hφ s t * liftComm φ hφ s t' := by
  set x := Function.surjInv hφ s
  set y := Function.surjInv hφ t
  set y' := Function.surjInv hφ t'
  have hx : φ x = s := Function.surjInv_eq hφ s
  have hy : φ y = t := Function.surjInv_eq hφ t
  have hy' : φ y' = t' := Function.surjInv_eq hφ t'
  rw [liftComm_eq hφ hker (x := x) (y := y * y') hx (by rw [map_mul, hy, hy']),
    liftComm_eq hφ hker hx hy, liftComm_eq hφ hker hx hy']
  exact CFSG.SectionRank.OddCover.commutatorElement_mul_right_of_mem_center
    (hker (commutatorElement_mem_ker φ (by rw [hx, hy']; exact h)))

theorem liftComm_self (hφ : Function.Surjective φ) (s : T) : liftComm φ hφ s s = 1 :=
  commutatorElement_self _

theorem liftComm_one_left (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (t : T) : liftComm φ hφ 1 t = 1 := by
  rw [liftComm_eq hφ hker (x := 1) (y := Function.surjInv hφ t) (map_one φ)
    (Function.surjInv_eq hφ t), commutatorElement_one_left]

theorem liftComm_one_right (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (s : T) : liftComm φ hφ s 1 = 1 := by
  rw [liftComm_eq hφ hker (x := Function.surjInv hφ s) (y := 1) (Function.surjInv_eq hφ s)
    (map_one φ), commutatorElement_one_right]

theorem liftComm_swap (hφ : Function.Surjective φ) (s t : T) :
    liftComm φ hφ t s = (liftComm φ hφ s t)⁻¹ :=
  (commutatorElement_inv _ _).symm

theorem liftComm_conj (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {s t : T} (h : Commute s t) (g : T) :
    liftComm φ hφ (g * s * g⁻¹) (g * t * g⁻¹) = liftComm φ hφ s t := by
  set x := Function.surjInv hφ s
  set y := Function.surjInv hφ t
  set z := Function.surjInv hφ g
  have hx : φ x = s := Function.surjInv_eq hφ s
  have hy : φ y = t := Function.surjInv_eq hφ t
  have hz : φ z = g := Function.surjInv_eq hφ g
  rw [liftComm_eq hφ hker (x := z * x * z⁻¹) (y := z * y * z⁻¹)
    (by rw [map_mul, map_mul, map_inv, hx, hz]) (by rw [map_mul, map_mul, map_inv, hy, hz])]
  have hc : ⁅x, y⁆ ∈ Subgroup.center Y := by
    rw [← liftComm_eq hφ hker hx hy]
    exact liftComm_mem_center hφ hker h
  have hconj : ⁅z * x * z⁻¹, z * y * z⁻¹⁆ = z * ⁅x, y⁆ * z⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hconj, Subgroup.mem_center_iff.mp hc z, mul_inv_cancel_right]
  exact (liftComm_eq hφ hker hx hy).symm

theorem liftComm_pow_left (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {s t : T} (h : Commute s t) (k : ℕ) : liftComm φ hφ (s ^ k) t = liftComm φ hφ s t ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, liftComm_one_left hφ hker]
  | succ k ih => rw [pow_succ, liftComm_mul_left hφ hker h, ih, pow_succ]

theorem liftComm_inv_left (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {s t : T} (h : Commute s t) : liftComm φ hφ s⁻¹ t = (liftComm φ hφ s t)⁻¹ := by
  have h1 := liftComm_mul_left hφ hker (s := s⁻¹) h
  rw [inv_mul_cancel, liftComm_one_left hφ hker] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem mul_comm_of_liftComm_eq_one (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {U : Subgroup T}
    (h : ∀ s ∈ U, ∀ t ∈ U, liftComm φ hφ s t = 1) {x y : Y} (hx : x ∈ U.comap φ)
    (hy : y ∈ U.comap φ) : x * y = y * x := by
  rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_eq_liftComm hφ hker]
  exact h _ hx _ hy

theorem liftComm_eq_one_of_closure (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {A : Type*} [AddCommGroup A] (θ : Multiplicative A →* T)
    {S : Set A} (hS : AddSubgroup.closure S = ⊤)
    (h : ∀ s ∈ S, ∀ s' ∈ S,
      liftComm φ hφ (θ (Multiplicative.ofAdd s)) (θ (Multiplicative.ofAdd s')) = 1)
    (a a' : Multiplicative A) : liftComm φ hφ (θ a) (θ a') = 1 := by
  have hcomm : ∀ x y : Multiplicative A, Commute (θ x) (θ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  let H : Multiplicative A → AddSubgroup A := fun y =>
    { carrier := {x | liftComm φ hφ (θ (Multiplicative.ofAdd x)) (θ y) = 1}
      add_mem' := fun {x x'} hx hx' => by
        change liftComm φ hφ (θ (Multiplicative.ofAdd x * Multiplicative.ofAdd x')) (θ y) = 1
        rw [map_mul, liftComm_mul_left hφ hker (hcomm _ _), hx, hx', one_mul]
      zero_mem' := by
        change liftComm φ hφ (θ 1) (θ y) = 1
        rw [map_one, liftComm_one_left hφ hker]
      neg_mem' := fun {x} hx => by
        change liftComm φ hφ (θ (Multiplicative.ofAdd x)⁻¹) (θ y) = 1
        rw [map_inv, liftComm_inv_left hφ hker (hcomm _ _), hx, inv_one] }
  have hH : ∀ y, (∀ s ∈ S, liftComm φ hφ (θ (Multiplicative.ofAdd s)) (θ y) = 1) →
      ∀ x, liftComm φ hφ (θ x) (θ y) = 1 := fun y hy x => by
    have hle : AddSubgroup.closure S ≤ H y := (AddSubgroup.closure_le _).mpr fun s hs => hy s hs
    rw [hS] at hle
    exact hle (AddSubgroup.mem_top (Multiplicative.toAdd x))
  have h1 : ∀ s' ∈ S, ∀ x, liftComm φ hφ (θ x) (θ (Multiplicative.ofAdd s')) = 1 :=
    fun s' hs' => hH _ fun s hs => h s hs s' hs'
  have h2 : ∀ x y, liftComm φ hφ (θ x) (θ y) = 1 := by
    intro x y
    have hsym : ∀ s ∈ S, liftComm φ hφ (θ (Multiplicative.ofAdd s)) (θ x) = 1 := fun s hs => by
      rw [liftComm_swap, h1 s hs x, inv_one]
    rw [liftComm_swap, hH x hsym y, inv_one]
  exact h2 a a'

theorem liftComm_eq_one_of_conj_swap (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : Odd p) {s t : T} (h : Commute s t)
    (hs : s ^ p = 1) (g : T) (hgs : g * s * g⁻¹ = t) (hgt : g * t * g⁻¹ = s) :
    liftComm φ hφ s t = 1 := by
  have h2 : liftComm φ hφ s t ^ 2 = 1 := by
    have hc := liftComm_conj hφ hker h g
    rw [hgs, hgt, liftComm_swap] at hc
    rw [pow_two]
    nth_rewrite 2 [← hc]
    exact mul_inv_cancel _
  have hp1 : liftComm φ hφ s t ^ p = 1 := by
    rw [← liftComm_pow_left hφ hker h, hs, liftComm_one_left hφ hker]
  exact eq_one_of_sq_eq_one_of_pow_eq_one hp h2 hp1

end CentralLift

end CFSG.RankThree.Classical2
