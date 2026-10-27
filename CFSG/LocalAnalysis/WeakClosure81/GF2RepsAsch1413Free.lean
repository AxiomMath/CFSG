module

public import CFSG.Quasithin.Background.FixVLattice
import CFSG.Quasithin.Background.OddCoprimeFixV
import CFSG.Quasithin.Background.B4L3Inv
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

private lemma a1413Free_exists_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : Odd (Nat.card X)) {z : MulAut V} (hz : ∀ x ∈ X, z * x * z⁻¹ = x⁻¹)
    {u : V} (hu : u ∈ commV X) (hzu : z u = u) :
    ∃ v ∈ commV X, u = z v * v⁻¹ := by
  classical
  have hXne : Nat.card X ≠ 0 := by
    rintro h0
    rw [h0] at hX
    exact Nat.not_odd_zero hX
  haveI : Finite X := Nat.finite_of_card_ne_zero hXne
  haveI : Fintype X := Fintype.ofFinite X
  have hinv_ne : ∀ x : X, x ≠ 1 → x⁻¹ ≠ x := by
    intro x hx1 h
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr h.symm
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact hx1 (orderOf_eq_one_iff.mp h1)
    · have h2dvd : 2 ∣ Nat.card X := by
        rw [← h2]
        exact orderOf_dvd_natCard x
      exact hX.not_two_dvd_nat h2dvd
  let s : Setoid X :=
    { r := fun x y => y = x ∨ y = x⁻¹
      iseqv :=
        { refl := fun x => Or.inl rfl
          symm := fun {x y} h => by
            rcases h with h | h
            · exact Or.inl h.symm
            · exact Or.inr (by rw [h, inv_inv])
          trans := fun {x y w} h1 h2 => by
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
            · exact Or.inl (h2.trans h1)
            · exact Or.inr (by rw [h2, h1])
            · exact Or.inr (by rw [h2, h1])
            · exact Or.inl (by rw [h2, h1, inv_inv]) } }
  haveI : Fintype (Quotient s) := Quotient.fintype s
  let R : Finset X := (Finset.univ : Finset (Quotient s)).image Quotient.out
  have hR_out : ∀ c : Quotient s, Quotient.out c ∈ R := fun c =>
    Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
  have hcover : ∀ x : X, x ≠ 1 → x ∈ R.erase 1 ∨ x⁻¹ ∈ R.erase 1 := by
    intro x hx1
    have hmk := Quotient.mk_out (s := s) x
    rcases hmk with h | h
    · left
      refine Finset.mem_erase.mpr ⟨hx1, ?_⟩
      rw [h]
      exact hR_out _
    · right
      refine Finset.mem_erase.mpr ⟨fun h1 => hx1 (inv_eq_one.mp h1), ?_⟩
      rw [h, inv_inv]
      exact hR_out _
  have hdisj : Disjoint (R.erase 1) ((R.erase 1).image (fun x : X => x⁻¹)) := by
    rw [Finset.disjoint_left]
    intro y hy hyim
    obtain ⟨r, hr, hr_eq⟩ := Finset.mem_image.mp hyim
    have hr1 : r ≠ 1 := (Finset.mem_erase.mp hr).1
    have hrR : r ∈ R := (Finset.mem_erase.mp hr).2
    have hyR : y ∈ R := (Finset.mem_erase.mp hy).2
    have hrinvR : r⁻¹ ∈ R := by rw [hr_eq]; exact hyR
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hrR
    obtain ⟨c', -, hc'⟩ := Finset.mem_image.mp hrinvR
    have h_mk_r : Quotient.mk s r = c := by rw [← hc, Quotient.out_eq]
    have h_mk_rinv : Quotient.mk s r⁻¹ = c' := by rw [← hc', Quotient.out_eq]
    have hcc : c = c' := by
      rw [← h_mk_r, ← h_mk_rinv]
      exact Quotient.sound (Or.inr rfl)
    have hrr : r = r⁻¹ := by
      have hrout : Quotient.out c = Quotient.out c' := by rw [hcc]
      rw [hc, hc'] at hrout
      exact hrout
    exact hinv_ne r hr1 hrr.symm
  have hunion : R.erase 1 ∪ (R.erase 1).image (fun x : X => x⁻¹) =
      (Finset.univ : Finset X).erase 1 := by
    ext x
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro (⟨hx1, -⟩ | ⟨r, ⟨hr1, -⟩, hr_eq⟩)
      · exact ⟨hx1, Finset.mem_univ x⟩
      · refine ⟨?_, Finset.mem_univ x⟩
        intro h1
        exact hr1 (inv_eq_one.mp (hr_eq.trans h1))
    · rintro ⟨hx1, -⟩
      rcases hcover x hx1 with h | h
      · exact Or.inl (Finset.mem_erase.mp h)
      · exact Or.inr ⟨x⁻¹, Finset.mem_erase.mp h, by rw [inv_inv]⟩
  have hprod : (∏ x ∈ (R.erase 1 ∪ (R.erase 1).image (fun x : X => x⁻¹)),
        (x : MulAut V) u)
      = (∏ r ∈ R.erase 1, (r : MulAut V) u) *
        (∏ r ∈ R.erase 1, ((r⁻¹ : X) : MulAut V) u) := by
    rw [Finset.prod_union hdisj]
    rw [Finset.prod_image (s := R.erase 1) (g := fun x : X => x⁻¹)
      (f := fun x : X => (x : MulAut V) u) (fun a _ b _ h => inv_injective h)]
  set v : V := ∏ r ∈ R.erase 1, (r : MulAut V) u with hv
  have hvS : v ∈ commV X := by
    rw [hv]
    exact (commV X).prod_mem (fun r _ => commV_apply_mem_of_mem r.2 hu)
  set w : V := ∏ x : X, (x : MulAut V) u with hw
  have hwS : w ∈ commV X := by
    rw [hw]
    exact (commV X).prod_mem (fun x _ => commV_apply_mem_of_mem x.2 hu)
  have hwfix : w ∈ fixV X := by
    intro y hy
    let yX : X := ⟨y, hy⟩
    show y w = w
    rw [hw]
    rw [map_prod y (fun x : X => (x : MulAut V) u) (Finset.univ : Finset X)]
    exact Fintype.prod_equiv (Equiv.mulLeft yX) (fun x : X => y ((x : MulAut V) u))
      (fun z : X => (z : MulAut V) u) (fun x => by
        change y ((x : MulAut V) u) = ((yX : MulAut V) * (x : MulAut V)) u
        rw [MulAut.mul_apply])
  have hw1 : w = 1 := by
    have hmem : w ∈ commV X ⊓ fixV X := ⟨hwS, hwfix⟩
    rw [commV_inf_fixV_eq_bot_of_odd_card hV X hX] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hw_decomp : w = (∏ x ∈ (Finset.univ : Finset X).erase 1, (x : MulAut V) u) * u := by
    rw [hw]
    rw [← Finset.prod_erase_mul (Finset.univ : Finset X)
      (fun x : X => (x : MulAut V) u) (Finset.mem_univ (1 : X))]
    simp
  have hprod_u : (∏ x ∈ (Finset.univ : Finset X).erase 1, (x : MulAut V) u) = u := by
    have h : (∏ x ∈ (Finset.univ : Finset X).erase 1, (x : MulAut V) u) * u = 1 := by
      rw [← hw_decomp, hw1]
    exact mul_inv_eq_one.mp (by rw [inv_eq_self_of_sq hV u]; exact h)
  have hzv : z v = ∏ r ∈ R.erase 1, ((r⁻¹ : X) : MulAut V) u := by
    rw [hv]
    rw [map_prod z (fun r : X => (r : MulAut V) u) (R.erase 1)]
    refine Finset.prod_congr rfl ?_
    intro r _
    have hzr : z * (r : MulAut V) * z⁻¹ = ((r⁻¹ : X) : MulAut V) := by
      rw [hz (r : MulAut V) r.2, Subgroup.coe_inv]
    calc z ((r : MulAut V) u) = (z * (r : MulAut V) * z⁻¹) (z u) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
      _ = ((r⁻¹ : X) : MulAut V) (z u) := by rw [hzr]
      _ = ((r⁻¹ : X) : MulAut V) u := by rw [hzu]
  have hvzv : v * z v = u := by
    rw [hzv, hv]
    rw [← hprod, hunion]
    exact hprod_u
  have hu_eq : u = z v * v⁻¹ := by
    rw [inv_eq_self_of_sq hV v]
    exact hvzv.symm.trans (mul_comm v (z v))
  exact ⟨v, hvS, hu_eq⟩

theorem eq_bot_of_inverted_free [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : Odd (Nat.card X)) {z i : MulAut V} (hz : ∀ x ∈ X, z * x * z⁻¹ = x⁻¹)
    (hi : i * i = z) (hiX : ∀ x ∈ X, i * x * i⁻¹ ∈ X)
    (hfix : ∀ w ∈ commV (zpowers z), i w = w) : X = ⊥ := by
  classical
  have hzS : ∀ u ∈ commV X, z u ∈ commV X := fun u hu =>
    commV_apply_mem_of_normalizes
      (fun x hx => by rw [hz x hx]; exact X.inv_mem hx) hu
  have hiS : ∀ u ∈ commV X, i u ∈ commV X := fun u hu =>
    commV_apply_mem_of_normalizes (fun x hx => hiX x hx) hu
  have hkey : ∀ u ∈ commV X, z u = u → u ∈ commV (Subgroup.zpowers z) := by
    intro u hu hzu
    obtain ⟨v, -, hv⟩ := a1413Free_exists_of_fixed hV hX hz hu hzu
    exact Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, v, hv.symm⟩
  let t : V → V := fun u => i u * u⁻¹
  have ht2 : ∀ u : V, t (t u) = z u * u⁻¹ := by
    intro u
    change i (i u * u⁻¹) * (i u * u⁻¹)⁻¹ = z u * u⁻¹
    rw [map_mul i, map_inv i, ← MulAut.mul_apply, hi]
    rw [inv_eq_self_of_sq hV (i u), inv_eq_self_of_sq hV u,
      inv_eq_self_of_sq hV (i u * u)]
    have hiu2 : i u * i u = 1 := by rw [← pow_two]; exact hV (i u)
    calc z u * i u * (i u * u) = z u * (i u * i u) * u := by ac_rfl
      _ = z u * u := by rw [hiu2, mul_one]
  have ht3 : ∀ u : V, t (z u * u⁻¹) = 1 := by
    intro u
    change i (z u * u⁻¹) * (z u * u⁻¹)⁻¹ = 1
    have hmem : z u * u⁻¹ ∈ commV (Subgroup.zpowers z) :=
      Subgroup.subset_closure ⟨z, Subgroup.mem_zpowers z, u, rfl⟩
    rw [hfix _ hmem]
    group
  have hzfixS : ∀ u ∈ commV X, z u = u := by
    intro u hu
    have htuS : t u ∈ commV X := (commV X).mul_mem (hiS u hu) ((commV X).inv_mem hu)
    have ht3u : t (t (t u)) = 1 := by
      rw [ht2 u]
      exact ht3 u
    have hzy : z (t u) = t u := by
      have h := ht2 (t u)
      rw [ht3u] at h
      exact mul_inv_eq_one.mp h.symm
    have hmem_tu : t u ∈ commV (Subgroup.zpowers z) := hkey (t u) htuS hzy
    have hiy : i (t u) = t u := hfix _ hmem_tu
    have h2 : t (t u) = 1 := by
      change i (t u) * (t u)⁻¹ = 1
      rw [hiy]
      group
    have h3 : z u * u⁻¹ = 1 := by rw [← ht2 u, h2]
    exact mul_inv_eq_one.mp h3
  have hSbot : commV X = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro u hu
    obtain ⟨v, hv, hv_eq⟩ := a1413Free_exists_of_fixed hV hX hz hu (hzfixS u hu)
    have hzv : z v = v := hzfixS v hv
    have hu1 : u = 1 := by rw [hv_eq, hzv, mul_inv_cancel]
    exact Subgroup.mem_bot.mpr hu1
  exact FixVLat.eq_bot_of_commV_eq_bot hSbot

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
