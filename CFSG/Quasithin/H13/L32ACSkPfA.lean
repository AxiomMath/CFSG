module

public import CFSG.Quasithin.H13.L32ACSk10
public import CFSG.Quasithin.H13.NQCatBNExc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Abstract

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_mul_central {S : Subgroup X} {a : ℕ} (hS : ∀ s ∈ S, s ^ 2 ^ a = 1)
    (hZ : Odd (Nat.card (Subgroup.center X))) {s z : X} (hs : s ∈ S)
    (hz : z ∈ Subgroup.center X) (hx : (s * z) ^ 2 ^ a = 1) : z = 1 := by
  have hc : Commute s z := Subgroup.mem_center_iff.mp hz s
  have hz2 : z ^ 2 ^ a = 1 := by
    rw [hc.mul_pow, hS s hs, one_mul] at hx
    exact hx
  have hd : orderOf (⟨z, hz⟩ : Subgroup.center X) ∣ 2 ^ a :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hz2))
  have hodd : Odd (orderOf (⟨z, hz⟩ : Subgroup.center X)) :=
    Odd.of_dvd_nat hZ (orderOf_dvd_natCard _)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd
    exact Nat.not_even_iff_odd.mpr hodd ((Nat.even_pow' hj0).mpr even_two)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact congrArg Subtype.val hj

theorem lieSylowOver3_holds :
    LieSylowOver3 := by
  intro X _ _ n hn hq hZ hL S Y hS hSY hidx
  set π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hS.2.1 : ∃ a, Nat.card S = 2 ^ a)
  have hSexp : ∀ s ∈ S, s ^ 2 ^ a = 1 := fun s hs => by
    have : (⟨s, hs⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [ha] at this
    simpa using congrArg Subtype.val this
  have hYcard : Nat.card Y = 2 ^ a * 3 ^ 1 := by
    have h1 := (S.subgroupOf Y).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, ha] at h1
    have h2 : (S.subgroupOf Y).index = 3 := hidx
    rw [h2] at h1
    rw [← h1, pow_one]
  have hYs : Group.IsSolvable ↥Y := Vol2Native.A312L.isSolvable_of_card_two_three hYcard
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have hbig : IsLieChar2Big (X ⧸ Subgroup.center X) := ⟨n, hn, hL⟩
  have hSbar : IsSylowTwoOf (S.map π) ⊤ := by
    have h := CFSG.QuasithinUnique.Setup.X3.isSylowTwoOf_map_of_odd_ker π
      (by rw [hker]; exact hZ) hS
    rwa [MonoidHom.range_eq_top.mpr hπs] at h
  have hYbs : Group.IsSolvable ↥(Y.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective Y)
  have key := NQCat.lieOvergroupFact_holds (X ⧸ Subgroup.center X) hsimple hbig (S.map π) hSbar
    (Y.map π) (Subgroup.map_mono hSY) hYbs
  have hconj : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have hyn : π y ∈ Subgroup.normalizer ((S.map π : Subgroup _) : Set (X ⧸ Subgroup.center X)) :=
      key ⟨y, hy, rfl⟩
    have h1 : π (y * s * y⁻¹) ∈ S.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hyn (π s)).mp ⟨s, hs, rfl⟩
    obtain ⟨s', hs', he⟩ := h1
    have hz : s'⁻¹ * (y * s * y⁻¹) ∈ Subgroup.center X := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have hx : (s' * (s'⁻¹ * (y * s * y⁻¹))) ^ 2 ^ a = 1 := by
      rw [mul_inv_cancel_left, conj_pow, hSexp s hs, mul_one, mul_inv_cancel]
    have h1 := eq_one_of_mul_central hSexp hZ hs' hz hx
    rw [show y * s * y⁻¹ = s' * (s'⁻¹ * (y * s * y⁻¹)) by group, h1, mul_one]
    exact hs'
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact hconj y hy s
  · intro h
    have := hconj y⁻¹ (Y.inv_mem hy) _ h
    simpa [mul_assoc] using this

end CFSG.Quasithin.H13.L32A.C.SkPf
