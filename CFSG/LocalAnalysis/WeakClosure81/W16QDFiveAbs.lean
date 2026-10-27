module

public import CFSG.Open.FusionDefs
public import CFSG.Monster.B.Short.Extraspecial
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open Subgroup
open scoped commutatorElement Pointwise

private theorem w16q_odd_natCard_fusionOddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

@[expose] def oddCoreCenter (X : Type) [Group X] : Subgroup X :=
  (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype

structure Heis2p (X : Type) [Group X] (Y : Subgroup X) (p : ℕ) : Prop where
  card_Y : Nat.card Y = 2
  sup_eq : Y ⊔ fusionOddCore X = ⊤
  prime : p.Prime
  ext : CFSG.IsExtraspecial p ↥(fusionOddCore X)
  card_O : Nat.card (fusionOddCore X) = p ^ 3
  gen : Subgroup.normalClosure (Y : Set X) = ⊤

namespace Heis2p

variable {X : Type} [Group X] {Y : Subgroup X} {p : ℕ}

private theorem w16q_center_comm (h : Heis2p X Y p) {z n : X}
    (hz : z ∈ oddCoreCenter X) (hn : n ∈ fusionOddCore X) : z * n = n * z := by
  rcases Subgroup.mem_map.mp hz with ⟨w, hw, rfl⟩
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨n, hn⟩)).symm

private theorem w16q_commutator_eq_center [Finite X] (h : Heis2p X Y p) :
    ⁅fusionOddCore X, fusionOddCore X⁆ = oddCoreCenter X := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let N := ↥(fusionOddCore X)
  haveI : Finite N := Finite.of_injective (fun n : N => (n : X)) Subtype.coe_injective
  have hP : CFSG.IsExtraspecialPGroup p N :=
    CFSG.IsExtraspecial.isExtraspecialPGroup (p := p) (P := N) (hE := h.ext)
  have hcomm : commutator N = Subgroup.center N :=
    CFSG.IsExtraspecialPGroup.commutator_eq hP
  have hmap : (commutator N).map (fusionOddCore X).subtype =
      ⁅fusionOddCore X, fusionOddCore X⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hmap2 : (Subgroup.center N).map (fusionOddCore X).subtype = oddCoreCenter X := rfl
  rw [← hmap, ← hmap2, hcomm]

private theorem w16q_commutator_mem_center [Finite X] (h : Heis2p X Y p) {x y : X}
    (hx : x ∈ fusionOddCore X) (hy : y ∈ fusionOddCore X) :
    ⁅x, y⁆ ∈ oddCoreCenter X := by
  rw [← w16q_commutator_eq_center h]
  exact Subgroup.commutator_mem_commutator hx hy

private theorem w16q_commutator_inv_inv [Finite X] (h : Heis2p X Y p) {x y : X}
    (hx : x ∈ fusionOddCore X) (hy : y ∈ fusionOddCore X) :
    ⁅x⁻¹, y⁻¹⁆ = ⁅x, y⁆ := by
  have hxy : ⁅x, y⁆ ∈ oddCoreCenter X := w16q_commutator_mem_center h hx hy
  have hx' : x⁻¹ * ⁅x, y⁆ * x = ⁅x, y⁆ := by
    rw [← w16q_center_comm h hxy (Subgroup.inv_mem _ hx)]
    group
  have hy' : y⁻¹ * ⁅x, y⁆ * y = ⁅x, y⁆ := by
    rw [← w16q_center_comm h hxy (Subgroup.inv_mem _ hy)]
    group
  rw [commutatorElement_inv_right x⁻¹ y, commutatorElement_inv_right y x, hx', hy']

private theorem w16q_conj_eq_self [Finite X] (h : Heis2p X Y p) {v y : X}
    (hv : v ∈ Y) (hv1 : v ≠ 1) (hy : y ∈ Y) : y * v * y⁻¹ = v := by
  obtain ⟨y₀, -, hy₀uniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).1 h.card_Y
  have h1 : (⟨y * v * y⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hv) (Subgroup.inv_mem _ hy)⟩
      : Y) ≠ 1 := by
    intro hh
    have hhy : y * v * y⁻¹ = 1 := congrArg Subtype.val hh
    have hv_eq : v = 1 := by
      have := congrArg (fun t : X => y⁻¹ * t * y) hhy
      simpa [mul_assoc] using this
    exact hv1 hv_eq
  have h2 : (⟨v, hv⟩ : Y) ≠ 1 := by
    intro hh
    exact hv1 (congrArg Subtype.val hh)
  exact (congrArg Subtype.val ((hy₀uniq _ h2).trans (hy₀uniq _ h1).symm)).symm

private theorem w16q_commutator_center_mul [Finite X] (h : Heis2p X Y p) {x y z w : X}
    (hx : x ∈ fusionOddCore X) (hy : y ∈ fusionOddCore X)
    (hz : z ∈ oddCoreCenter X) (hw : w ∈ oddCoreCenter X) :
    ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  obtain ⟨z', hz'c, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨w', hw'c, rfl⟩ := Subgroup.mem_map.mp hw
  have hwN : (w' : X) ∈ fusionOddCore X := w'.2
  have hz'' : ∀ g ∈ fusionOddCore X, (z' : X) * g * (z' : X)⁻¹ = g := fun g hg => by
    have hc : (z' : X) * g = g * (z' : X) := by
      simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨g, hg⟩)).symm
    rw [hc, mul_inv_cancel_right]
  have hw'' : ∀ g ∈ fusionOddCore X, (w' : X) * g * (w' : X)⁻¹ = g := fun g hg => by
    have hc : (w' : X) * g = g * (w' : X) := by
      simpa using (congrArg Subtype.val (Subgroup.mem_center_iff.mp hw'c ⟨g, hg⟩)).symm
    rw [hc, mul_inv_cancel_right]
  calc ⁅x * (z' : X), y * (w' : X)⁆
        = x * ((z' : X) * (y * (w' : X)) * (z' : X)⁻¹) * x⁻¹ * (w' : X)⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * y * ((w' : X) * x⁻¹ * (w' : X)⁻¹) * y⁻¹ := by
        rw [hz'' (y * (w' : X)) (Subgroup.mul_mem _ hy hwN)]
        group
    _ = ⁅x, y⁆ := by
        rw [hw'' x⁻¹ (Subgroup.inv_mem _ hx), commutatorElement_def]

private def w16q_Nminus [Finite X] (h : Heis2p X Y p) (v : X) : Subgroup X where
  carrier := {n : X | n ∈ fusionOddCore X ∧ v * n * v⁻¹ * n ∈ oddCoreCenter X}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨Subgroup.mul_mem _ haN hbN, ?_⟩
    have hEq : MulAut.conj v (a * b) * (a * b) =
        (MulAut.conj v a * a) * (MulAut.conj v b * b) * ⁅a⁻¹, b⁻¹⁆ := by
      have hcb_comm : a⁻¹ * (MulAut.conj v b * b) = (MulAut.conj v b * b) * a⁻¹ :=
        (w16q_center_comm h hb (Subgroup.inv_mem _ haN)).symm
      rw [map_mul, commutatorElement_def]
      simp only [inv_inv]
      rw [show MulAut.conj v a = (MulAut.conj v a * a) * a⁻¹ from by group,
        show MulAut.conj v b = (MulAut.conj v b * b) * b⁻¹ from by group]
      rw [show ((MulAut.conj v a * a) * a⁻¹) * ((MulAut.conj v b * b) * b⁻¹) * (a * b)
            = (MulAut.conj v a * a) * (a⁻¹ * (MulAut.conj v b * b)) * (b⁻¹ * (a * b))
            from by group]
      rw [hcb_comm]
      group
    change MulAut.conj v (a * b) * (a * b) ∈ oddCoreCenter X
    rw [hEq]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ ha hb)
      (w16q_commutator_mem_center h (Subgroup.inv_mem _ haN) (Subgroup.inv_mem _ hbN))
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨Subgroup.inv_mem _ haN, ?_⟩
    have hcomm : MulAut.conj v a * a = a * MulAut.conj v a := by
      have h1 : (MulAut.conj v a * a) * a = (a * MulAut.conj v a) * a := by
        calc (MulAut.conj v a * a) * a = a * (MulAut.conj v a * a) :=
              w16q_center_comm h ha haN
          _ = (a * MulAut.conj v a) * a := by rw [mul_assoc]
      exact mul_right_cancel h1
    have hgoal : MulAut.conj v a⁻¹ * a⁻¹ = (MulAut.conj v a * a)⁻¹ := by
      rw [map_inv]
      calc (MulAut.conj v a)⁻¹ * a⁻¹ = (a * MulAut.conj v a)⁻¹ := by group
        _ = (MulAut.conj v a * a)⁻¹ := by rw [hcomm]
    change MulAut.conj v a⁻¹ * a⁻¹ ∈ oddCoreCenter X
    rw [hgoal]
    exact Subgroup.inv_mem _ ha

private theorem w16q_conj_v_Nminus [Finite X] (h : Heis2p X Y p) {v : X} (hv2 : v * v = 1)
    {m : X} (hm : m ∈ w16q_Nminus h v) : v * m * v⁻¹ ∈ w16q_Nminus h v := by
  obtain ⟨hmN, hmZ⟩ := hm
  have hxN : v * m * v⁻¹ ∈ fusionOddCore X := (fusionOddCore_normal X).conj_mem m hmN v
  have hconj' : v * (v * m * v⁻¹) * v⁻¹ = m := by
    have hvv : v⁻¹ = v := inv_eq_iff_mul_eq_one.mpr hv2
    rw [hvv, show v * (v * m * v) * v = (v * v) * m * (v * v) from by group, hv2,
      one_mul, mul_one]
  refine ⟨hxN, ?_⟩
  have hEq : v * (v * m * v⁻¹) * v⁻¹ * (v * m * v⁻¹) = m * (v * m * v⁻¹) := by
    rw [hconj']
  rw [hEq]
  have hcomm : m * (v * m * v⁻¹) = ((v * m * v⁻¹) * m) * ⁅m⁻¹, (v * m * v⁻¹)⁻¹⁆ := by
    rw [commutatorElement_def]; group
  rw [hcomm, w16q_commutator_inv_inv h hmN hxN]
  exact Subgroup.mul_mem _ hmZ (w16q_commutator_mem_center h hmN hxN)

theorem ne_two [Finite X] (h : Heis2p X Y p) : p ≠ 2 := by
  intro hp2
  have hodd := w16q_odd_natCard_fusionOddCore X
  rw [h.card_O, hp2] at hodd
  norm_num at hodd

theorem inv_center [Finite X] (h : Heis2p X Y p) {v : X} (hv : v ∈ Y) (hv1 : v ≠ 1) :
    (∀ n ∈ fusionOddCore X, v * n * v⁻¹ * n ∈ oddCoreCenter X) ∧
      ∀ z ∈ oddCoreCenter X, v * z = z * v := by
  classical
  have hv2 : v * v = 1 := by
    have hdvd : orderOf v ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hv
    rw [h.card_Y] at hdvd
    have hne1 : orderOf v ≠ 1 := by simpa [orderOf_eq_one_iff] using hv1
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd h1 hne1
    · have := pow_orderOf_eq_one v
      rw [h2] at this
      simpa [pow_two] using this
  have hvN : v ∉ fusionOddCore X := by
    intro hvv
    have hdvd : orderOf v ∣ Nat.card (fusionOddCore X) :=
      Subgroup.orderOf_dvd_natCard _ hvv
    have h2 : orderOf v = 2 := by
      have hdvd2 : orderOf v ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hv
      rw [h.card_Y] at hdvd2
      have hne1 : orderOf v ≠ 1 := by simpa [orderOf_eq_one_iff] using hv1
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2
      · exact absurd h1 hne1
      · exact h2
    rw [h2] at hdvd
    obtain ⟨k, hk⟩ := w16q_odd_natCard_fusionOddCore X
    obtain ⟨j, hj⟩ := hdvd
    omega
  have hYmem : ∀ a ∈ Y, a = 1 ∨ a = v := by
    intro a ha
    obtain ⟨y₀, -, hy₀uniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).1 h.card_Y
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · refine Or.inr ?_
      have h1 : (⟨a, ha⟩ : Y) ≠ 1 := fun hh => ha1 (Subtype.ext_iff.mp hh)
      have h2 : (⟨v, hv⟩ : Y) ≠ 1 := fun hh => hv1 (Subtype.ext_iff.mp hh)
      exact congrArg Subtype.val ((hy₀uniq _ h1).trans (hy₀uniq _ h2).symm)
  let Nminus := w16q_Nminus h v
  have hψ : ∀ n : X, n ∈ fusionOddCore X → n * (v * n * v⁻¹)⁻¹ ∈ Nminus := by
    intro n hn
    have hσ2 : MulAut.conj v (MulAut.conj v n) = n := by
      have hconj : (MulAut.conj v) * (MulAut.conj v) = 1 := by
        rw [← map_mul, hv2, map_one]
      have := congrArg (fun f : MulAut X => f n) hconj
      simpa using this
    refine ⟨Subgroup.mul_mem _ hn
      (Subgroup.inv_mem _ ((fusionOddCore_normal X).conj_mem n hn v)), ?_⟩
    have hσψ : MulAut.conj v (n * (MulAut.conj v n)⁻¹) = (MulAut.conj v n) * n⁻¹ := by
      rw [map_mul, map_inv, hσ2]
    have h1 : MulAut.conj v (n * (MulAut.conj v n)⁻¹) * (n * (MulAut.conj v n)⁻¹) = 1 := by
      rw [hσψ]; group
    have hmem : MulAut.conj v (n * (MulAut.conj v n)⁻¹) * (n * (MulAut.conj v n)⁻¹)
        ∈ oddCoreCenter X := by
      rw [h1]; exact Subgroup.one_mem _
    simpa [MulAut.conj_apply] using hmem
  have hconj : ∀ g : X, g * v * g⁻¹ ∈ Nminus ⊔ Y := by
    intro g
    have hg : g ∈ (fusionOddCore X : Set X) * (Y : Set X) := by
      have h1 : (fusionOddCore X ⊔ Y : Subgroup X) = ⊤ := by rw [sup_comm, h.sup_eq]
      rw [← Subgroup.normal_mul (fusionOddCore X) Y, h1]
      exact Subgroup.mem_top g
    rcases hg with ⟨n, hn, y, hy, hgy⟩
    rw [← hgy]
    have hyv : y * v * y⁻¹ = v := w16q_conj_eq_self h hv hv1 hy
    rw [show (n * y) * v * (n * y)⁻¹ = n * (y * v * y⁻¹) * n⁻¹ from by group, hyv]
    have hmem : n * v * n⁻¹ ∈ Nminus ⊔ Y := by
      have hψn := hψ n hn
      have hnv : n * v * n⁻¹ = (n * (v * n * v⁻¹)⁻¹) * v := by group
      rw [hnv]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hψn) (Subgroup.mem_sup_right hv)
    exact hmem
  have hRtop : Nminus ⊔ Y = ⊤ := by
    have hle : Subgroup.normalClosure (Y : Set X) ≤ Nminus ⊔ Y := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      rw [Group.mem_conjugatesOfSet_iff] at hx
      rcases hx with ⟨a, ha, hac⟩
      rw [isConj_iff] at hac
      rcases hac with ⟨c, rfl⟩
      rcases hYmem a ha with rfl | rfl
      · simpa using Subgroup.one_mem (Nminus ⊔ Y)
      · exact hconj c
    rw [h.gen] at hle
    exact top_le_iff.mp hle
  have hvnorm : v ∈ Subgroup.normalizer (Nminus : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm; exact w16q_conj_v_Nminus h hv2 hm
    · intro hm
      have hvm : v * (v * m * v⁻¹) * v⁻¹ = m := by
        have hvv : v⁻¹ = v := inv_eq_iff_mul_eq_one.mpr hv2
        rw [hvv, show v * (v * m * v) * v = (v * v) * m * (v * v) from by group, hv2,
          one_mul, mul_one]
      rw [← hvm]
      exact w16q_conj_v_Nminus h hv2 hm
  have hYnorm : Y ≤ Subgroup.normalizer (Nminus : Set X) := by
    intro y hy
    rcases hYmem y hy with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hvnorm
  have hNle : fusionOddCore X ≤ Nminus := by
    intro n hn
    have hnR : n ∈ Nminus ⊔ Y := by rw [hRtop]; exact Subgroup.mem_top n
    have hn' : n ∈ (Nminus : Set X) * (Y : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Nminus Y hYnorm]
      exact hnR
    rcases hn' with ⟨m, hm, y, hy, hmy⟩
    rw [← hmy]
    rcases hYmem y hy with hy1 | hyv
    · subst hy1
      simpa using hm
    · exfalso
      have hmN : m ∈ fusionOddCore X := hm.1
      have hvmem : v ∈ fusionOddCore X := by
        have hmyv : m * v = n := by rw [← hyv]; exact hmy
        have hvn : v = m⁻¹ * n := by rw [← hmyv]; group
        rw [hvn]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) hn
      exact hvN hvmem
  refine ⟨fun n hn => (hNle hn).2, ?_⟩
  intro z hz
  have hz' : z ∈ ⁅fusionOddCore X, fusionOddCore X⁆ := by
    rw [w16q_commutator_eq_center h]
    exact hz
  have hfix : ∀ a ∈ ⁅fusionOddCore X, fusionOddCore X⁆, v * a * v⁻¹ = a := by
    intro a ha
    rw [Subgroup.commutator_def] at ha
    refine Subgroup.closure_induction (p := fun a _ => v * a * v⁻¹ = a) ?_ ?_ ?_ ?_ ha
    · rintro g ⟨x, hx, y, hy, rfl⟩
      have hzZ : (v * x * v⁻¹) * x ∈ oddCoreCenter X := (hNle hx).2
      have hwZ : (v * y * v⁻¹) * y ∈ oddCoreCenter X := (hNle hy).2
      have hσx : v * x * v⁻¹ = x⁻¹ * ((v * x * v⁻¹) * x) := by
        rw [← w16q_center_comm h hzZ (Subgroup.inv_mem _ hx)]
        group
      have hσy : v * y * v⁻¹ = y⁻¹ * ((v * y * v⁻¹) * y) := by
        rw [← w16q_center_comm h hwZ (Subgroup.inv_mem _ hy)]
        group
      have hconjxy : v * ⁅x, y⁆ * v⁻¹ = ⁅v * x * v⁻¹, v * y * v⁻¹⁆ := by
        rw [show v * ⁅x, y⁆ * v⁻¹ = (MulAut.conj v) ⁅x, y⁆ from rfl, map_commutatorElement]
        rfl
      rw [hconjxy, hσx, hσy]
      rw [w16q_commutator_center_mul h (Subgroup.inv_mem _ hx) (Subgroup.inv_mem _ hy) hzZ hwZ]
      exact w16q_commutator_inv_inv h hx hy
    · simp
    · intro a b _ _ ha hb
      rw [show v * (a * b) * v⁻¹ = (v * a * v⁻¹) * (v * b * v⁻¹) from by group, ha, hb]
    · intro a _ ha
      rw [show v * a⁻¹ * v⁻¹ = (v * a * v⁻¹)⁻¹ from by group, ha]
  have hfixz := hfix z hz'
  calc v * z = v * z * v⁻¹ * v := by group
    _ = z * v := by rw [hfixz]

private theorem w16q_center_card (h : Heis2p X Y p) :
    Nat.card (Subgroup.center ↥(fusionOddCore X)) = p := by
  haveI : CFSG.IsExtraspecial p ↥(fusionOddCore X) := h.ext
  exact CFSG.IsExtraspecial.center_order_p p ↥(fusionOddCore X)

private theorem w16q_oddCoreCenter_card (h : Heis2p X Y p) :
    Nat.card (oddCoreCenter X) = p := by
  unfold oddCoreCenter
  rw [Subgroup.card_map_of_injective (fusionOddCore X).subtype_injective]
  exact w16q_center_card h

theorem exponent_eq [Finite X] (h : Heis2p X Y p) : Monoid.exponent ↥(fusionOddCore X) = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hpodd : Odd p := h.prime.odd_of_ne_two (ne_two h)
  obtain ⟨y₀, hy₀ne, -⟩ := (Nat.card_eq_two_iff' (1 : Y)).1 h.card_Y
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ Y, v ≠ 1 :=
    ⟨y₀, y₀.2, fun hh => hy₀ne (Subtype.ext (by simpa using hh))⟩
  have hinv := inv_center h hv hv1
  have hZp : ∀ c ∈ oddCoreCenter X, c ^ p = 1 := by
    intro c hc
    rcases Subgroup.mem_map.mp hc with ⟨w, hw, rfl⟩
    have hwpow : w ^ p = 1 := by
      have hdvd : orderOf w ∣ p := by
        rw [← w16q_center_card h]
        exact Subgroup.orderOf_dvd_natCard (Subgroup.center ↥(fusionOddCore X)) hw
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa using congrArg Subtype.val hwpow
  have hpow : ∀ a : ↥(fusionOddCore X), a ^ p = 1 := by
    intro a
    set A : X := (a : X) with hA
    haveI hE : CFSG.IsExtraspecial p ↥(fusionOddCore X) := h.ext
    have hq : IsElementaryAbelian p
        (↥(fusionOddCore X) ⧸ Subgroup.center ↥(fusionOddCore X)) :=
      CFSG.IsExtraspecial.quotient_elementary_abelian p ↥(fusionOddCore X)
    have hqpow : ∀ q : ↥(fusionOddCore X) ⧸ Subgroup.center ↥(fusionOddCore X), q ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hq.exponent_dvd_p
    have haz : a ^ p ∈ Subgroup.center ↥(fusionOddCore X) := by
      refine (QuotientGroup.eq_one_iff (N := Subgroup.center ↥(fusionOddCore X))
        (a ^ p)).mp ?_
      rw [QuotientGroup.mk_pow]
      exact hqpow _
    have hAZ : A ^ p ∈ oddCoreCenter X := by
      rw [hA]
      exact (Subgroup.mem_map (f := (fusionOddCore X).subtype)).mpr ⟨a ^ p, haz, rfl⟩
    have hcZ : v * A * v⁻¹ * A ∈ oddCoreCenter X := hinv.1 A a.2
    have hσpow : (v * A * v⁻¹) ^ p = A ^ p := by
      rw [show v * A * v⁻¹ = MulAut.conj v A from rfl, ← map_pow]
      change v * A ^ p * v⁻¹ = A ^ p
      rw [hinv.2 (A ^ p) hAZ, mul_assoc, mul_inv_cancel, mul_one]
    have hσpow' : (v * A * v⁻¹) ^ p = (A ^ p)⁻¹ := by
      have hcomm : Commute (v * A * v⁻¹ * A) A⁻¹ :=
        w16q_center_comm h hcZ (Subgroup.inv_mem _ a.2)
      rw [show v * A * v⁻¹ = (v * A * v⁻¹ * A) * A⁻¹ from by group,
        hcomm.mul_pow, hZp _ hcZ, one_mul, inv_pow]
    have hAsq : A ^ p * A ^ p = 1 := by
      have hEq : A ^ p = (A ^ p)⁻¹ := hσpow.symm.trans hσpow'
      nth_rewrite 2 [hEq]
      rw [mul_inv_cancel]
    have hdvd2 : orderOf (A ^ p) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hAsq)
    have hdvdp : orderOf (A ^ p) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr (hZp (A ^ p) hAZ)
    have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
    have hdvd1 : orderOf (A ^ p) ∣ 1 := by
      have := Nat.dvd_gcd hdvd2 hdvdp
      rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at this
    have hAp : A ^ p = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
    exact Subtype.ext (by simpa [hA] using hAp)
  have hExp : Monoid.exponent ↥(fusionOddCore X) ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  haveI hnt : Nontrivial ↥(fusionOddCore X) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rw [h.card_O]; exact one_lt_pow' h.prime.one_lt (by norm_num))
  rcases h.prime.eq_one_or_self_of_dvd (Monoid.exponent ↥(fusionOddCore X)) hExp with h1 | hp
  · exfalso
    have := Monoid.one_lt_exponent (G := ↥(fusionOddCore X))
    omega
  · exact hp

private theorem w16q_map_fusionOddCore [Finite X] (h : Heis2p X Y p) (α : MulAut X) :
    (fusionOddCore X).map α.toMonoidHom = fusionOddCore X := by
  have hle : (fusionOddCore X).map α.toMonoidHom ≤ fusionOddCore X :=
    le_sSup ⟨(fusionOddCore_normal X).map α.toMonoidHom α.surjective, by
      rw [Subgroup.card_map_of_injective α.injective]
      exact w16q_odd_natCard_fusionOddCore X⟩
  have hle' : (fusionOddCore X).map α.symm.toMonoidHom ≤ fusionOddCore X :=
    le_sSup ⟨(fusionOddCore_normal X).map α.symm.toMonoidHom α.symm.surjective, by
      rw [Subgroup.card_map_of_injective α.symm.injective]
      exact w16q_odd_natCard_fusionOddCore X⟩
  refine le_antisymm hle ?_
  intro n hn
  have h1 : α.symm n ∈ fusionOddCore X :=
    hle' (Subgroup.mem_map_of_mem α.symm.toMonoidHom hn)
  have h2 : α (α.symm n) ∈ (fusionOddCore X).map α.toMonoidHom :=
    Subgroup.mem_map_of_mem α.toMonoidHom h1
  simpa using h2

private theorem w16q_oddCoreCenter_le (h : Heis2p X Y p) :
    oddCoreCenter X ≤ fusionOddCore X := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨w, -, rfl⟩
  exact w.2

private theorem w16q_commutator_inv_right [Finite X] (h : Heis2p X Y p) {x y : X}
    (hx : x ∈ fusionOddCore X) (hy : y ∈ fusionOddCore X) :
    ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have hxy : ⁅x, y⁆ ∈ oddCoreCenter X := w16q_commutator_mem_center h hx hy
  rw [commutatorElement_inv_right x y, ← commutatorElement_inv x y]
  have : y⁻¹ * ⁅x, y⁆⁻¹ * y = ⁅x, y⁆⁻¹ := by
    rw [← w16q_center_comm h (Subgroup.inv_mem _ hxy) (Subgroup.inv_mem _ hy)]
    group
  exact this

private def w16q_NplusAut [Finite X] (h : Heis2p X Y p) (α : MulAut X) : Subgroup X where
  carrier := {n : X | n ∈ fusionOddCore X ∧ α n * n⁻¹ ∈ oddCoreCenter X}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨Subgroup.mul_mem _ haN hbN, ?_⟩
    have hcomm : (α b * b⁻¹) * a = a * (α b * b⁻¹) := w16q_center_comm h hb haN
    have hEq : α (a * b) * (a * b)⁻¹ = (α a * a⁻¹) * (α b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      rw [show α a = (α a * a⁻¹) * a from by group,
          show α b = (α b * b⁻¹) * b from by group]
      rw [show ((α a * a⁻¹) * a) * ((α b * b⁻¹) * b) * (b⁻¹ * a⁻¹)
            = (α a * a⁻¹) * (a * (α b * b⁻¹)) * (b * (b⁻¹ * a⁻¹)) from by group]
      rw [← hcomm]
      group
    change α (a * b) * (a * b)⁻¹ ∈ oddCoreCenter X
    rw [hEq]
    exact Subgroup.mul_mem _ ha hb
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨Subgroup.inv_mem _ haN, ?_⟩
    have hgoal : α a⁻¹ * a = (α a * a⁻¹)⁻¹ := by
      rw [map_inv, show α a = (α a * a⁻¹) * a from by group]
      rw [show ((α a * a⁻¹) * a)⁻¹ * a = a⁻¹ * (α a * a⁻¹)⁻¹ * a from by group]
      rw [← w16q_center_comm h (Subgroup.inv_mem _ ha) (Subgroup.inv_mem _ haN)]
      group
    rw [inv_inv, hgoal]
    exact Subgroup.inv_mem _ ha

private def w16q_NminusAut [Finite X] (h : Heis2p X Y p) (α : MulAut X) : Subgroup X where
  carrier := {n : X | n ∈ fusionOddCore X ∧ α n * n ∈ oddCoreCenter X}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨Subgroup.mul_mem _ haN hbN, ?_⟩
    have hEq : α (a * b) * (a * b) =
        (α a * a) * (α b * b) * ⁅a⁻¹, b⁻¹⁆ := by
      have hcb_comm : a⁻¹ * (α b * b) = (α b * b) * a⁻¹ :=
        (w16q_center_comm h hb (Subgroup.inv_mem _ haN)).symm
      rw [map_mul, commutatorElement_def]
      simp only [inv_inv]
      rw [show α a = (α a * a) * a⁻¹ from by group,
        show α b = (α b * b) * b⁻¹ from by group]
      rw [show ((α a * a) * a⁻¹) * ((α b * b) * b⁻¹) * (a * b)
            = (α a * a) * (a⁻¹ * (α b * b)) * (b⁻¹ * (a * b))
            from by group]
      rw [hcb_comm]
      group
    change α (a * b) * (a * b) ∈ oddCoreCenter X
    rw [hEq]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ ha hb)
      (w16q_commutator_mem_center h (Subgroup.inv_mem _ haN) (Subgroup.inv_mem _ hbN))
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨Subgroup.inv_mem _ haN, ?_⟩
    have hgoal : α a⁻¹ * a⁻¹ = (α a * a)⁻¹ := by
      rw [map_inv, show α a = (α a * a) * a⁻¹ from by group]
      rw [show ((α a * a) * a⁻¹)⁻¹ * a⁻¹ = a * (α a * a)⁻¹ * a⁻¹ from by group]
      rw [← w16q_center_comm h (Subgroup.inv_mem _ ha) haN]
      group
    change α a⁻¹ * a⁻¹ ∈ oddCoreCenter X
    rw [hgoal]
    exact Subgroup.inv_mem _ ha

private theorem w16q_mem_NplusAut_iff [Finite X] (h : Heis2p X Y p) (α : MulAut X) {n : X} :
    n ∈ w16q_NplusAut h α ↔ n ∈ fusionOddCore X ∧ α n * n⁻¹ ∈ oddCoreCenter X :=
  Iff.rfl

private theorem w16q_mem_NminusAut_iff [Finite X] (h : Heis2p X Y p) (α : MulAut X) {n : X} :
    n ∈ w16q_NminusAut h α ↔ n ∈ fusionOddCore X ∧ α n * n ∈ oddCoreCenter X :=
  Iff.rfl

theorem card_le_two [Finite X] (h : Heis2p X Y p) (E : Subgroup (MulAut X))
    (hE : IsElemAbelian 2 E) (hEY : ∀ α ∈ E, ∀ y ∈ Y, α y = y)
    (hEZ : ∀ α ∈ E, ∀ z ∈ oddCoreCenter X, α z = z) : Nat.card E ≤ 2 := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI hExt : CFSG.IsExtraspecial p ↥(fusionOddCore X) := h.ext
  have hpodd : Odd p := h.prime.odd_of_ne_two (ne_two h)
  let Q := ↥(fusionOddCore X) ⧸ Subgroup.center ↥(fusionOddCore X)
  have hQe : IsElementaryAbelian p Q :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p ↥(fusionOddCore X)
  have hQpow : ∀ q : Q, q ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQe.exponent_dvd_p
  have hpowN : ∀ n : ↥(fusionOddCore X), n ^ p = 1 := by
    have := exponent_eq h
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [this])
  have hsquare : ∀ α ∈ E, α * α = 1 := fun α hα => by
    have := hE.2 α hα
    simpa [pow_two] using this
  have hinf : ∀ α ∈ E, w16q_NplusAut h α ⊓ w16q_NminusAut h α = oddCoreCenter X := by
    intro α hαE
    apply le_antisymm
    · intro n hn
      rw [Subgroup.mem_inf] at hn
      rcases hn with ⟨hnp, hnm⟩
      rw [w16q_mem_NplusAut_iff] at hnp
      rw [w16q_mem_NminusAut_iff] at hnm
      obtain ⟨hnN, hnp⟩ := hnp
      obtain ⟨-, hnm⟩ := hnm
      have hn2 : n ^ 2 ∈ oddCoreCenter X := by
        have hEq : n * n = (α n * n⁻¹)⁻¹ * (α n * n) := by group
        rw [pow_two, hEq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hnp) hnm
      have hmem : (⟨n, hnN⟩ : ↥(fusionOddCore X)) ^ 2 ∈ Subgroup.center ↥(fusionOddCore X) := by
        obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hn2
        have hw_eq : w = (⟨n, hnN⟩ : ↥(fusionOddCore X)) ^ 2 := by
          apply Subtype.ext
          simpa using hwv
        rw [← hw_eq]
        exact hw
      have hq2 : (((⟨n, hnN⟩ : ↥(fusionOddCore X)) : Q)) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥(fusionOddCore X))
          ((⟨n, hnN⟩ : ↥(fusionOddCore X)) ^ 2)).mpr hmem
      have hqp : (((⟨n, hnN⟩ : ↥(fusionOddCore X)) : Q)) ^ p = 1 := hQpow _
      have hdvd : orderOf (((⟨n, hnN⟩ : ↥(fusionOddCore X)) : Q)) ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hq2) (orderOf_dvd_iff_pow_eq_one.mpr hqp)
      have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
      have hmemc : (⟨n, hnN⟩ : ↥(fusionOddCore X)) ∈ Subgroup.center ↥(fusionOddCore X) :=
        (QuotientGroup.eq_one_iff (N := Subgroup.center ↥(fusionOddCore X))
          (⟨n, hnN⟩ : ↥(fusionOddCore X))).mp hdvd
      exact (Subgroup.mem_map (f := (fusionOddCore X).subtype)).mpr ⟨⟨n, hnN⟩, hmemc, rfl⟩
    · intro z hz
      rw [Subgroup.mem_inf]
      constructor
      · rw [w16q_mem_NplusAut_iff]
        refine ⟨w16q_oddCoreCenter_le h hz, ?_⟩
        rw [hEZ α hαE z hz]
        simpa using Subgroup.one_mem (oddCoreCenter X)
      · rw [w16q_mem_NminusAut_iff]
        refine ⟨w16q_oddCoreCenter_le h hz, ?_⟩
        rw [hEZ α hαE z hz]
        exact Subgroup.mul_mem _ hz hz
  have hsup : ∀ α ∈ E, w16q_NplusAut h α ⊔ w16q_NminusAut h α = fusionOddCore X := by
    intro α hαE
    apply le_antisymm
    · refine sup_le (fun x hx => (w16q_mem_NplusAut_iff h α).mp hx |>.1) ?_
      intro x hx
      exact (w16q_mem_NminusAut_iff h α).mp hx |>.1
    · intro n hnN
      have hαnN : α n ∈ fusionOddCore X := by
        rw [← w16q_map_fusionOddCore h α]
        exact Subgroup.mem_map_of_mem α.toMonoidHom hnN
      have hnp : n ^ p = 1 := by
        have := hpowN ⟨n, hnN⟩
        simpa using congrArg Subtype.val this
      have hm : n * α n ∈ w16q_NplusAut h α := by
        rw [w16q_mem_NplusAut_iff]
        refine ⟨Subgroup.mul_mem _ hnN hαnN, ?_⟩
        have hαα : α (α n) = n := by
          have := congrArg (fun f : MulAut X => f n) (hsquare α hαE)
          simpa using this
        have : α (n * α n) * (n * α n)⁻¹ = ⁅α n, n⁆ := by
          rw [map_mul, hαα, mul_inv_rev]
          group
        rw [this]
        exact w16q_commutator_mem_center h hαnN hnN
      have hm' : n * (α n)⁻¹ ∈ w16q_NminusAut h α := by
        rw [w16q_mem_NminusAut_iff]
        refine ⟨Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ hαnN), ?_⟩
        have hαα : α (α n) = n := by
          have := congrArg (fun f : MulAut X => f n) (hsquare α hαE)
          simpa using this
        have : α (n * (α n)⁻¹) * (n * (α n)⁻¹) = 1 := by
          rw [map_mul, map_inv, hαα]
          group
        rw [this]
        exact Subgroup.one_mem _
      have hc : ⁅α n, n⁆ ∈ oddCoreCenter X := w16q_commutator_mem_center h hαnN hnN
      have hcan : α n * n = ⁅α n, n⁆ * n * α n := by
        rw [commutatorElement_def]; group
      have hmm' : (n * α n) * (n * (α n)⁻¹) = ⁅α n, n⁆ * n ^ 2 := by
        have hcan : α n * n = ⁅α n, n⁆ * n * α n := by
          rw [commutatorElement_def]; group
        rw [show (n * α n) * (n * (α n)⁻¹) = n * (α n * n) * (α n)⁻¹ from by group]
        rw [hcan]
        rw [show n * (⁅α n, n⁆ * n * α n) * (α n)⁻¹
              = (n * ⁅α n, n⁆) * (n * (α n * (α n)⁻¹)) from by group]
        rw [← w16q_center_comm h hc hnN]
        group
      have hcZ : ⁅α n, n⁆⁻¹ ∈ oddCoreCenter X := Subgroup.inv_mem _ hc
      have hcN : ⁅α n, n⁆⁻¹ ∈ w16q_NplusAut h α := by
        rw [w16q_mem_NplusAut_iff]
        refine ⟨w16q_oddCoreCenter_le h hcZ, ?_⟩
        rw [hEZ α hαE _ hcZ, mul_inv_cancel]
        exact Subgroup.one_mem _
      have hn2 : n ^ 2 ∈ w16q_NplusAut h α ⊔ w16q_NminusAut h α := by
        rw [show n ^ 2 = (⁅α n, n⁆⁻¹ * (n * α n)) * (n * (α n)⁻¹) from by
          rw [show ⁅α n, n⁆⁻¹ * (n * α n) * (n * (α n)⁻¹)
                = ⁅α n, n⁆⁻¹ * ((n * α n) * (n * (α n)⁻¹)) from by group]
          rw [hmm']
          group]
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mem_sup_left hcN) (Subgroup.mem_sup_left hm))
          (Subgroup.mem_sup_right hm')
      obtain ⟨k, hk⟩ := hpodd
      have hk2 : 2 * (k + 1) = p + 1 := by omega
      have hnk : (n ^ 2) ^ (k + 1) = n := by
        rw [← pow_mul, hk2, pow_succ, hnp, one_mul]
      rw [← hnk]
      exact Subgroup.pow_mem _ hn2 (k + 1)
  have hcomm : ∀ α ∈ E, ∀ a ∈ w16q_NplusAut h α, ∀ b ∈ w16q_NminusAut h α,
      a * b = b * a := by
    intro α hαE a ha b hb
    rw [w16q_mem_NplusAut_iff] at ha
    rw [w16q_mem_NminusAut_iff] at hb
    obtain ⟨haN, haZ⟩ := ha
    obtain ⟨hbN, hbZ⟩ := hb
    have hcZ : ⁅a, b⁆ ∈ oddCoreCenter X := w16q_commutator_mem_center h haN hbN
    have hfix : α ⁅a, b⁆ = ⁅a, b⁆ := hEZ α hαE _ hcZ
    have halpha : α ⁅a, b⁆ = ⁅a, b⁆⁻¹ := by
      rw [map_commutatorElement]
      rw [show α a = (α a * a⁻¹) * a from by group,
          show α b = (α b * b) * b⁻¹ from by group]
      rw [show (α a * a⁻¹) * a = a * (α a * a⁻¹) from w16q_center_comm h haZ haN,
          show (α b * b) * b⁻¹ = b⁻¹ * (α b * b) from
            w16q_center_comm h hbZ (Subgroup.inv_mem _ hbN)]
      rw [w16q_commutator_center_mul h haN (Subgroup.inv_mem _ hbN) haZ hbZ,
        w16q_commutator_inv_right h haN hbN]
    rw [hfix] at halpha
    have h2 : ⁅a, b⁆ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [halpha]
      rw [mul_inv_cancel]
    have hdvd : orderOf ⁅a, b⁆ ∣ Nat.gcd 2 p := Nat.dvd_gcd
      (orderOf_dvd_iff_pow_eq_one.mpr h2)
      (by rw [← w16q_oddCoreCenter_card h]
          exact Subgroup.orderOf_dvd_natCard (oddCoreCenter X) hcZ)
    have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.dvd_one, orderOf_eq_one_iff,
      commutatorElement_eq_one_iff_mul_comm] at hdvd
    exact hdvd
  have hdich : ∀ α ∈ E, (∀ n ∈ fusionOddCore X, α n * n⁻¹ ∈ oddCoreCenter X) ∨
      (∀ n ∈ fusionOddCore X, α n * n ∈ oddCoreCenter X) := by
    intro α hαE
    by_cases hplus : w16q_NplusAut h α = fusionOddCore X
    · left
      intro n hn
      exact (w16q_mem_NplusAut_iff h α).mp (hplus ▸ hn) |>.2
    · by_cases hminus : w16q_NminusAut h α = fusionOddCore X
      · right
        intro n hn
        exact (w16q_mem_NminusAut_iff h α).mp (hminus ▸ hn) |>.2
      · exfalso
        have hle_plus : w16q_NplusAut h α ≤ fusionOddCore X :=
          fun x hx => (w16q_mem_NplusAut_iff h α).mp hx |>.1
        have hle_minus : w16q_NminusAut h α ≤ fusionOddCore X :=
          fun x hx => (w16q_mem_NminusAut_iff h α).mp hx |>.1
        have hZle_plus : oddCoreCenter X ≤ w16q_NplusAut h α := by
          rw [← hinf α hαE]
          exact inf_le_left
        have hZle_minus : oddCoreCenter X ≤ w16q_NminusAut h α := by
          rw [← hinf α hαE]
          exact inf_le_right
        have hcardeq := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
          (w16q_NplusAut h α) (w16q_NminusAut h α) (hcomm α hαE)).1
        rw [hsup α hαE, hinf α hαE, h.card_O, w16q_oddCoreCenter_card h] at hcardeq
        have hAdvd : Nat.card (w16q_NplusAut h α) ∣ p ^ 3 := by
          rw [← h.card_O]; exact Subgroup.card_dvd_of_le hle_plus
        have hBdvd : Nat.card (w16q_NminusAut h α) ∣ p ^ 3 := by
          rw [← h.card_O]; exact Subgroup.card_dvd_of_le hle_minus
        have hAge : p ≤ Nat.card (w16q_NplusAut h α) := by
          calc p = Nat.card (oddCoreCenter X) := (w16q_oddCoreCenter_card h).symm
            _ ≤ Nat.card (w16q_NplusAut h α) := Subgroup.card_le_of_le hZle_plus
        have hBge : p ≤ Nat.card (w16q_NminusAut h α) := by
          calc p = Nat.card (oddCoreCenter X) := (w16q_oddCoreCenter_card h).symm
            _ ≤ Nat.card (w16q_NminusAut h α) := Subgroup.card_le_of_le hZle_minus
        have hAne : Nat.card (w16q_NplusAut h α) ≠ p ^ 3 := by
          intro hc
          exact hplus (Subgroup.eq_of_le_of_card_ge hle_plus (by rw [hc, h.card_O]))
        have hBne : Nat.card (w16q_NminusAut h α) ≠ p ^ 3 := by
          intro hc
          exact hminus (Subgroup.eq_of_le_of_card_ge hle_minus (by rw [hc, h.card_O]))
        obtain ⟨ka, hka_le, hka_eq⟩ := (Nat.dvd_prime_pow h.prime).mp hAdvd
        obtain ⟨kb, hkb_le, hkb_eq⟩ := (Nat.dvd_prime_pow h.prime).mp hBdvd
        have hp2 : 2 ≤ p := h.prime.two_le
        have hka_ge : 1 ≤ ka := by
          rcases Nat.eq_zero_or_pos ka with hk0 | hkpos
          · rw [hk0, pow_zero] at hka_eq
            omega
          · exact hkpos
        have hkb_ge : 1 ≤ kb := by
          rcases Nat.eq_zero_or_pos kb with hk0 | hkpos
          · rw [hk0, pow_zero] at hkb_eq
            omega
          · exact hkpos
        have hka_ne : ka ≠ 3 := by
          intro hk3; exact hAne (hka_eq.trans (by rw [hk3]))
        have hkb_ne : kb ≠ 3 := by
          intro hk3; exact hBne (hkb_eq.trans (by rw [hk3]))
        have hka_le2 : ka ≤ 2 := by omega
        have hkb_le2 : kb ≤ 2 := by omega
        have hprod : ka + kb = 4 := by
          have h1 : p ^ (ka + kb) = p ^ 4 := by
            rw [pow_add, ← hka_eq, ← hkb_eq, ← hcardeq, ← pow_succ,
              show 3 + 1 = 4 from rfl]
          exact (Nat.pow_right_injective h.prime.one_lt h1)
        have hka2 : ka = 2 := by omega
        have hkb2 : kb = 2 := by omega
        have hAcard : Nat.card (w16q_NplusAut h α) = p ^ 2 := hka_eq.trans (by rw [hka2])
        have hBcard : Nat.card (w16q_NminusAut h α) = p ^ 2 := hkb_eq.trans (by rw [hkb2])
        haveI hApgr : IsPGroup p ↥(w16q_NplusAut h α) :=
          (CFSG.IsExtraspecial.isPGroup p ↥(fusionOddCore X)).of_injective
            (Subgroup.inclusion hle_plus) (Subgroup.inclusion_injective hle_plus)
        haveI hBpgr : IsPGroup p ↥(w16q_NminusAut h α) :=
          (CFSG.IsExtraspecial.isPGroup p ↥(fusionOddCore X)).of_injective
            (Subgroup.inclusion hle_minus) (Subgroup.inclusion_injective hle_minus)
        have hAbel : IsMulCommutative ↥(w16q_NplusAut h α) :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq hAcard
        have hBbel : IsMulCommutative ↥(w16q_NminusAut h α) :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq hBcard
        have hNab : IsMulCommutative ↥(fusionOddCore X) := by
          have hset : ((w16q_NplusAut h α ⊔ w16q_NminusAut h α : Subgroup X) : Set X) =
              (w16q_NplusAut h α : Set X) * (w16q_NminusAut h α : Set X) :=
            (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
              (w16q_NplusAut h α) (w16q_NminusAut h α) (hcomm α hαE)).2
          refine ⟨⟨fun x y => ?_⟩⟩
          have hx : (x : X) ∈ (w16q_NplusAut h α : Set X) * (w16q_NminusAut h α : Set X) := by
            rw [← hset, hsup α hαE]
            exact x.2
          have hy : (y : X) ∈ (w16q_NplusAut h α : Set X) * (w16q_NminusAut h α : Set X) := by
            rw [← hset, hsup α hαE]
            exact y.2
          obtain ⟨a, ha, b, hb, hxab⟩ := hx
          obtain ⟨a', ha', b', hb', hyab⟩ := hy
          have hba' : b * a' = a' * b := (hcomm α hαE a' ha' b hb).symm
          have hab' : a * b' = b' * a := hcomm α hαE a ha b' hb'
          have haa' : a * a' = a' * a := by
            exact congrArg Subtype.val
              ((IsMulCommutative.is_comm (M := ↥(w16q_NplusAut h α))).comm
                ⟨a, ha⟩ ⟨a', ha'⟩)
          have hbb' : b * b' = b' * b := by
            exact congrArg Subtype.val
              ((IsMulCommutative.is_comm (M := ↥(w16q_NminusAut h α))).comm
                ⟨b, hb⟩ ⟨b', hb'⟩)
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxab, ← hyab]
          exact Commute.mul_left (Commute.mul_right haa' hab') (Commute.mul_right hba' hbb')
        haveI := hNab
        have hcenter : Subgroup.center ↥(fusionOddCore X) = ⊤ := Subgroup.center_eq_top
        have hcardc : Nat.card (Subgroup.center ↥(fusionOddCore X)) =
            Nat.card ↥(fusionOddCore X) := by rw [hcenter, Subgroup.card_top]
        rw [w16q_center_card h, h.card_O] at hcardc
        nlinarith [h.prime.two_le]
  have hker : ∀ α ∈ E, (∀ n ∈ fusionOddCore X, α n * n⁻¹ ∈ oddCoreCenter X) → α = 1 := by
    intro α hαE htriv
    have hαα : ∀ y : X, α (α y) = y := fun y => by
      have := congrArg (fun f : MulAut X => f y) (hsquare α hαE)
      simpa using this
    have hfixN : ∀ n ∈ fusionOddCore X, α n = n := by
      intro n hn
      have hcZ : α n * n⁻¹ ∈ oddCoreCenter X := htriv n hn
      have h1 : α (α n) = (α n * n⁻¹) * ((α n * n⁻¹) * n) := by
        calc α (α n) = α ((α n * n⁻¹) * n) := by
              nth_rewrite 1 [show α n = (α n * n⁻¹) * n from by group]
              group
          _ = α (α n * n⁻¹) * α n := by rw [map_mul]
          _ = (α n * n⁻¹) * α n := by rw [hEZ α hαE _ hcZ]
          _ = (α n * n⁻¹) * ((α n * n⁻¹) * n) := by
              nth_rewrite 2 [show α n = (α n * n⁻¹) * n from by group]
              group
      have h3 : (α n * n⁻¹) * (α n * n⁻¹) = 1 := by
        have hnn : n = (α n * n⁻¹) * ((α n * n⁻¹) * n) := (hαα n).symm.trans h1
        have hcong := congrArg (· * n⁻¹) hnn
        rw [mul_inv_cancel] at hcong
        have hcc : ((α n * n⁻¹) * ((α n * n⁻¹) * n)) * n⁻¹
            = (α n * n⁻¹) * (α n * n⁻¹) := by group
        rw [hcc] at hcong
        exact hcong.symm
      have h4 : α n * n⁻¹ = 1 := by
        have hdvd : orderOf (α n * n⁻¹) ∣ Nat.gcd 2 p := Nat.dvd_gcd
          (orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using h3))
          (by rw [← w16q_oddCoreCenter_card h]
              exact Subgroup.orderOf_dvd_natCard (oddCoreCenter X) hcZ)
        have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
        rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
        exact hdvd
      rw [show α n = (α n * n⁻¹) * n from by group, h4, one_mul]
    ext x
    have hx : x ∈ (fusionOddCore X : Set X) * (Y : Set X) := by
      have h1 : (fusionOddCore X ⊔ Y : Subgroup X) = ⊤ := by rw [sup_comm, h.sup_eq]
      rw [← Subgroup.normal_mul (fusionOddCore X) Y, h1]
      exact Subgroup.mem_top x
    obtain ⟨n, hn, y, hy, rfl⟩ := hx
    show α (n * y) = n * y
    rw [map_mul, hfixN n hn, hEY α hαE y hy]
  have huniq : ∀ α ∈ E, ∀ β ∈ E, α ≠ 1 → β ≠ 1 → α = β := by
    intro α hαE β hβE hα1 hβ1
    have hαinv : ∀ n ∈ fusionOddCore X, α n * n ∈ oddCoreCenter X := by
      rcases hdich α hαE with hp | hm
      · exact absurd (hker α hαE hp) hα1
      · exact hm
    have hβinv : ∀ n ∈ fusionOddCore X, β n * n ∈ oddCoreCenter X := by
      rcases hdich β hβE with hp | hm
      · exact absurd (hker β hβE hp) hβ1
      · exact hm
    have hαβplus : ∀ n ∈ fusionOddCore X, (α * β) n * n⁻¹ ∈ oddCoreCenter X := by
      intro n hn
      have hcα : α n * n ∈ oddCoreCenter X := hαinv n hn
      have hcβ : β n * n ∈ oddCoreCenter X := hβinv n hn
      have hαinvn : α n⁻¹ = n * (α n * n)⁻¹ := by
        rw [map_inv, show α n = (α n * n) * n⁻¹ from by group]
        group
      have hgoal : (α * β) n * n⁻¹ = (β n * n) * (α n * n)⁻¹ := by
        rw [MulAut.mul_apply, show β n = (β n * n) * n⁻¹ from by group, map_mul, hαinvn,
          hEZ α hαE _ hcβ]
        rw [← w16q_center_comm h (Subgroup.inv_mem _ hcα) hn]
        group
      rw [hgoal]
      exact Subgroup.mul_mem _ hcβ (Subgroup.inv_mem _ hcα)
    have hαβ1 : α * β = 1 := hker (α * β) (E.mul_mem hαE hβE) hαβplus
    have hβ2 : β⁻¹ = β := by
      rw [inv_eq_iff_mul_eq_one]
      exact hsquare β hβE
    rw [mul_eq_one_iff_eq_inv] at hαβ1
    rwa [hβ2] at hαβ1
  by_cases hbot : E = ⊥
  · rw [hbot, Subgroup.card_bot]; norm_num
  · obtain ⟨α₀, hα₀E, hα₀ne⟩ : ∃ α ∈ E, α ≠ 1 := by
      by_contra hcon
      apply hbot
      rw [eq_bot_iff]
      intro x hx
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    have hsub : E ≤ Subgroup.zpowers α₀ := by
      intro β hβE
      rcases eq_or_ne β 1 with rfl | hβ1
      · exact Subgroup.one_mem _
      · rw [huniq β hβE α₀ hα₀E hβ1 hα₀ne]
        exact Subgroup.mem_zpowers α₀
    calc Nat.card E ≤ Nat.card (Subgroup.zpowers α₀) := Subgroup.card_le_of_le hsub
      _ = orderOf α₀ := Nat.card_zpowers α₀
      _ ≤ 2 := by
          have hdvd : orderOf α₀ ∣ 2 :=
            orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hsquare α₀ hα₀E)
          exact Nat.le_of_dvd (by norm_num) hdvd

end Heis2p

theorem w16q_two_le_of_pow_modEq_one {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (h : 2 ^ (p * k) ≡ 1 [MOD p]) : 2 ≤ k := by
  by_contra hk2
  have hk1 : k = 1 := by omega
  subst hk1
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : ((2 : ZMod p) ^ (p * 1)) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (2 ^ (p * 1)) 1 p).2 (by simpa using h)
    simpa using this
  rw [mul_one, ZMod.pow_card] at hz
  have hmod : 2 ≡ 1 [MOD p] := by
    exact (ZMod.natCast_eq_natCast_iff 2 1 p).1 (by simpa using hz)
  have hdvd : p ∣ 1 := by
    have h12 : 1 ≡ 2 [MOD p] := hmod.symm
    have := (Nat.modEq_iff_dvd' (show 1 ≤ 2 by norm_num)).1 h12
    simpa using this
  exact hp.not_dvd_one hdvd

end CFSG.LocalAnalysis.WeakClosure81

end
