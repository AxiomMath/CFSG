module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open

section Generic

variable {G : Type*} [Group G]

theorem eq_one_of_mem_center_of_pow_eq_one (hZ : Nat.card (center G) ∣ 3) {c : G} (hc : c ∈ center G)
    {n : ℕ} (hn : n.Coprime 3) (hcn : c ^ n = 1) : c = 1 :=
  (pow_eq_one_iff_of_coprime hn).1 ⟨hcn, pow_three_eq_one_of_mem_center hZ hc⟩

theorem apply_mul_inv_mem_center_of_autQuot_fixed (α : MulAut G) {z : G}
    (h : autQuot α (QuotientGroup.mk z) = QuotientGroup.mk z) : α z * z⁻¹ ∈ center G := by
  refine (QuotientGroup.eq_one_iff _).1 ?_
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← autQuot_mk, h, mul_inv_cancel]

theorem apply_mem_center (α : MulAut G) {z : G} (hz : z ∈ center G) : α z ∈ center G := by
  have h := (Subgroup.characteristic_iff_map_eq.mp (inferInstance : (center G).Characteristic)) α
  rw [← h]
  exact ⟨z, hz, rfl⟩

theorem apply_eq_of_mem_closure (α : MulAut G) {s : Set G} (hs : ∀ y ∈ s, α y = y) {y : G}
    (hy : y ∈ closure s) : α y = y :=
  MonoidHom.eqOn_closure (f := α.toMonoidHom) (g := MonoidHom.id G) (fun a ha => hs a ha) hy

theorem pow_apply_eq_pow_pow (α : MulAut G) {ζ : G} {s : ℕ} (hs : α ζ = ζ ^ s) (k : ℕ) :
    (α ^ k) ζ = ζ ^ (s ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hs, map_pow, ih, ← pow_mul, pow_succ]

theorem pow_odd_mod_three (s : ℕ) {r : ℕ} (hr : r % 2 = 1) : s ^ r % 3 = s % 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = 2 * m + 1 := ⟨r / 2, by omega⟩
  have hs : s % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [Nat.pow_mod]
  interval_cases h : s % 3
  · simp
  · simp
  · rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem exists_pow_eq_of_mem_center (h3 : Nat.card (center G) = 3) {ζ : G} (hζ : ζ ∈ center G)
    (hζ3 : orderOf ζ = 3) {c : G} (hc : c ∈ center G) : ∃ j : ℕ, ζ ^ j = c := by
  have hne : (⟨ζ, hζ⟩ : center G) ≠ 1 := by
    intro h
    have h1 : ζ = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hζ3
    exact absurd hζ3 (by norm_num)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_of_prime_card (g' := (⟨c, hc⟩ : center G)) h3 hne)
  exact ⟨j, congrArg Subtype.val hj⟩

theorem apply_central_order_three (h3 : Nat.card (center G) = 3) {ζ : G} (hζ : ζ ∈ center G)
    (hζ3 : orderOf ζ = 3) {r : ℕ} (hr : r % 2 = 1) (α : MulAut G) (hα : α ^ r = 1) : α ζ = ζ := by
  obtain ⟨s, hs⟩ := exists_pow_eq_of_mem_center h3 hζ hζ3 (apply_mem_center α hζ)
  have hit := pow_apply_eq_pow_pow α hs.symm r
  rw [hα, MulAut.one_apply] at hit
  have hmod : s ^ r ≡ 1 [MOD 3] := by
    have h1 : ζ ^ (s ^ r) = ζ ^ 1 := by rw [pow_one]; exact hit.symm
    rw [← hζ3]
    exact pow_eq_pow_iff_modEq.1 h1
  have hs1 : s ≡ 1 [MOD 3] := by
    have h2 : s ^ r % 3 = s % 3 := pow_odd_mod_three s hr
    exact h2.symm.trans hmod
  have h4 : ζ ^ s = ζ ^ 1 := pow_eq_pow_iff_modEq.2 (by rw [hζ3]; exact hs1)
  rw [← hs, h4, pow_one]

theorem apply_eq_of_mem_center (h3 : Nat.card (center G) = 3) {ζ : G} (hζ : ζ ∈ center G)
    (hζ3 : orderOf ζ = 3) (α : MulAut G) (hαζ : α ζ = ζ) {c : G} (hc : c ∈ center G) : α c = c := by
  obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_center h3 hζ hζ3 hc
  rw [map_pow, hαζ]

theorem apply_eq_of_autQuot_fixed (h3 : Nat.card (center G) = 3) {ζ : G} (hζ : ζ ∈ center G)
    (hζ3 : orderOf ζ = 3) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (α : MulAut G) (hα : α ^ r = 1)
    (hαζ : α ζ = ζ) {w : G} (hw : autQuot α (QuotientGroup.mk w) = QuotientGroup.mk w) : α w = w := by
  have hcc : α w * w⁻¹ ∈ center G := apply_mul_inv_mem_center_of_autQuot_fixed α hw
  have hcf : α (α w * w⁻¹) = α w * w⁻¹ := apply_eq_of_mem_center h3 hζ hζ3 α hαζ hcc
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = α w * w⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hcc hcf
  have hcw : α w = c * w := by rw [hcdef, inv_mul_cancel_right]
  have hk : ∀ k : ℕ, (α ^ k) w = c ^ k * w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hcf, hcw, pow_succ, mul_assoc]
  have hcr : c ^ r = 1 := by
    have h1 : c ^ r * w = 1 * w := by rw [one_mul, ← hk r, hα, MulAut.one_apply]
    exact mul_right_cancel h1
  have hcop : r.Coprime 3 := (Nat.coprime_primes hr Nat.prime_three).2 hr3
  have hc1 : c = 1 := eq_one_of_mem_center_of_pow_eq_one (by rw [h3]) hcc hcop hcr
  rw [hcw, hc1, one_mul]

theorem exists_cube_one_lift_mem [Finite G] (hZ : Nat.card (center G) ∣ 3) {e f g : G ⧸ center G}
    (he : orderOf e = 3) (hf : orderOf f = 3) (hef : e * f = f * e) (hn : f ∉ zpowers e)
    (hge : g * e = e * g) (hgf : g * f = f⁻¹ * g) :
    ∃ w : G, w ^ 3 = 1 ∧ w ∉ center G ∧
      (QuotientGroup.mk w : G ⧸ center G) ∈ closure ({e, f} : Set (G ⧸ center G)) ∧
      ∀ a : G, (QuotientGroup.mk a : G ⧸ center G) ∈ closure ({e, f} : Set (G ⧸ center G)) →
        a * w = w * a := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective e
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective f
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective g
  have hxy : x * y = y * x := mul_comm_of_lift hZ hef hge hgf hx hy hh
  have he3 : e ^ 3 = 1 := he ▸ pow_orderOf_eq_one e
  have hf3 : f ^ 3 = 1 := hf ▸ pow_orderOf_eq_one f
  have hx3 : x ^ 3 ∈ center G :=
    (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow, hx, he3])
  have hy3 : y ^ 3 ∈ center G :=
    (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow, hy, hf3])
  by_cases hu : x ^ 3 = 1
  · refine ⟨x, hu, fun hxc => ?_, ?_, fun a ha => mul_comm_of_mem_closure_pair hx hy rfl hxy.symm ha⟩
    · have h1 : e = 1 := by rw [← hx]; exact (QuotientGroup.eq_one_iff _).2 hxc
      rw [h1, orderOf_one] at he
      exact absurd he (by norm_num)
    · rw [hx]
      exact subset_closure (by simp)
  · have h3 : Nat.card (center G) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
      · exfalso
        have hb : center G = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
        rw [hb, Subgroup.mem_bot] at hx3
        exact hu hx3
      · exact h3
    have hu1 : (⟨x ^ 3, hx3⟩ : center G) ≠ 1 := fun h => hu (congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
      (mem_powers_of_prime_card (g' := (⟨y ^ 3, hy3⟩ : center G)) h3 hu1)
    have hk' : (x ^ 3) ^ k = y ^ 3 := congrArg Subtype.val hk
    have hcw : Commute y (x ^ k)⁻¹ := ((show Commute y x from hxy.symm).pow_right k).inv_right
    refine ⟨y * (x ^ k)⁻¹, ?_, ?_, ?_, fun a ha => mul_comm_of_mem_closure_pair hx hy ?_ ?_ ha⟩
    · rw [hcw.mul_pow, inv_pow, pow_right_comm, hk', mul_inv_cancel]
    · intro hwc
      have h1 : (QuotientGroup.mk (y * (x ^ k)⁻¹) : G ⧸ center G) = 1 :=
        (QuotientGroup.eq_one_iff _).2 hwc
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hx, hy,
        mul_inv_eq_one] at h1
      apply hn
      rw [h1]
      exact pow_mem (mem_zpowers e) k
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hx, hy]
      exact mul_mem (subset_closure (by simp)) (inv_mem (pow_mem (subset_closure (by simp)) k))
    · exact ((show Commute x y from hxy).mul_right ((Commute.refl x).pow_right k).inv_right).eq
    · exact ((Commute.refl y).mul_right hcw).eq

end Generic

section Main

variable {X : Type} [Group X] [Finite X]

theorem lift_prime_fixed (hZ : Nat.card (center X) ∣ 3) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (α : MulAut X) {zb : X ⧸ center X} (hzb : orderOf zb = q) (hfix : autQuot α zb = zb) :
    ∃ z : X, orderOf z = q ∧ α z = z := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective zb
  have hzq : (QuotientGroup.mk x : X ⧸ center X) ^ q = 1 := hzb ▸ pow_orderOf_eq_one _
  have hxq : x ^ q ∈ center X :=
    (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow]; exact hzq)
  have hxq3 : (x ^ q) ^ 3 = 1 := pow_three_eq_one_of_mem_center hZ hxq
  have hcop : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).2 (by omega)
  obtain ⟨u, hu3, huq⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨z, hzx, hzq1⟩ : ∃ z : X,
      (QuotientGroup.mk z : X ⧸ center X) = QuotientGroup.mk x ∧ z ^ q = 1 := by
    refine ⟨x ^ u, ?_, ?_⟩
    · have h1 : u % q = 1 := by
        have h2 : 1 % q = 1 := Nat.mod_eq_of_lt (by omega)
        exact (show u % q = 1 % q from huq).trans h2
      rw [QuotientGroup.mk_pow, pow_eq_pow_mod u hzq, h1, pow_one]
    · obtain ⟨k, hk⟩ := (Nat.modEq_zero_iff_dvd).1 hu3
      rw [pow_right_comm, hk, pow_mul, hxq3, one_pow]
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk x : X ⧸ center X) = 1 := by rw [← hzx, h, QuotientGroup.mk_one]
    rw [h1, orderOf_one] at hzb
    omega
  refine ⟨z, orderOf_eq_prime hzq1 hz1, ?_⟩
  have hc : α z * z⁻¹ ∈ center X :=
    apply_mul_inv_mem_center_of_autQuot_fixed α (by rw [hzx]; exact hfix)
  obtain ⟨c, hcdef⟩ : ∃ c : X, c = α z * z⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hcz : α z = c * z := by rw [hcdef, inv_mul_cancel_right]
  have hcomm : Commute c z := (Subgroup.mem_center_iff.1 hc z).symm
  have hcq : c ^ q = 1 := by
    have h1 : (α z) ^ q = 1 := by rw [← map_pow, hzq1, map_one]
    rw [hcz, hcomm.mul_pow, hzq1, mul_one] at h1
    exact h1
  have hc1 : c = 1 := eq_one_of_mem_center_of_pow_eq_one hZ hc hcop.symm hcq
  rw [hcz, hc1, one_mul]

theorem lift_E9_fixed (hZ : Nat.card (center X) ∣ 3)
    {e f g : X ⧸ center X} (he : orderOf e = 3) (hf : orderOf f = 3) (hef : e * f = f * e)
    (hn : f ∉ Subgroup.zpowers e) (hge : g * e = e * g) (hgf : g * f = f⁻¹ * g)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (α : MulAut X) (hα : α ^ r = 1)
    (hαe : autQuot α e = e) (hαf : autQuot α f = f) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ∀ x ∈ E, α x = x := by
  have hcl : ∀ y ∈ closure ({e, f} : Set (X ⧸ center X)), autQuot α y = y := fun y hy =>
    apply_eq_of_mem_closure (autQuot α) (s := {e, f}) (by rintro y (rfl | rfl); exacts [hαe, hαf]) hy
  rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
  · have hcen : center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_center_eq_bot hcen
    obtain ⟨hel, hcard⟩ := closure_pair_isElemAbelian_card he hf hef hn
    refine ⟨(closure ({e, f} : Set (X ⧸ center X))).map φ.symm.toMonoidHom, hel.map _, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective φ.symm.injective, hcard]
    · rintro _ ⟨b, hb, rfl⟩
      have h2 : (QuotientGroup.mk (φ.symm b) : X ⧸ center X) = b := by
        rw [← hφ]; exact φ.apply_symm_apply b
      apply φ.injective
      calc φ (α (φ.symm b)) = QuotientGroup.mk (α (φ.symm b)) := hφ _
        _ = autQuot α (QuotientGroup.mk (φ.symm b)) := (autQuot_mk _ _).symm
        _ = autQuot α b := by rw [h2]
        _ = b := hcl b hb
        _ = φ (φ.symm b) := (φ.apply_symm_apply b).symm
  · obtain ⟨ζ, hζ, hζ3⟩ := exists_central_order_three h3
    obtain ⟨w, hw3, hwc, hwmem, -⟩ := exists_cube_one_lift_mem hZ he hf hef hn hge hgf
    have hw : orderOf w = 3 := orderOf_eq_prime hw3 (fun h => hwc (h ▸ one_mem _))
    obtain ⟨hel, hcard⟩ := closure_pair_central_isElemAbelian_card hw hζ3 hwc hζ
    have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
    have hζf : α ζ = ζ := apply_central_order_three h3 hζ hζ3 hodd α hα
    have hwf : α w = w :=
      apply_eq_of_autQuot_fixed h3 hζ hζ3 hr hr3 α hα hζf (hcl _ hwmem)
    refine ⟨closure ({w, ζ} : Set X), hel, hcard, fun x hx => ?_⟩
    exact apply_eq_of_mem_closure α (s := {w, ζ}) (by rintro y (rfl | rfl); exacts [hwf, hζf]) hx

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK
