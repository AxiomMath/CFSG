module

public import CFSG.Quasithin.Background.A1cA130
public import CFSG.Quasithin.Background.A1cA133

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped MatrixGroups commutatorElement

namespace A1c

section General

variable {L : Type*} [Group L]

theorem hom_eq_one_of_perfect_quotient {S A : Type*} [Group S] [CommGroup A] (π : L →* S)
    (hπ : Function.Surjective π) (hS : Group.IsPerfect S) (f : L →* A) (hf : π.ker ≤ f.ker) :
    f = 1 := by
  ext g
  have h1 : (⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆).map π = ⊤ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ, ← commutator_def]
    exact hS.commutator_eq_top
  have hmem : π g ∈ (⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆).map π := by rw [h1]; trivial
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.1 hmem
  have hcker : c ∈ f.ker := by
    have : (⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆) ≤ f.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    exact this hc
  have hker : c⁻¹ * g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, inv_mul_cancel]
  have h2 := hf hker
  rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
  rw [MonoidHom.mem_ker] at hcker
  rw [hcker, inv_one, one_mul] at h2
  simpa using h2

theorem centerOf_normal {P : Subgroup L} [P.Normal] : (centerOf P).Normal := by
  refine ⟨fun z hz g => ?_⟩
  rw [mem_centerOf_iff] at hz ⊢
  refine ⟨Subgroup.Normal.conj_mem ‹P.Normal› z hz.1 g, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ P := by
    have := Subgroup.Normal.conj_mem ‹P.Normal› y hy g⁻¹
    simpa using this
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hz.2 _ hy']
    _ = g * z * g⁻¹ * y := by group

theorem centerOf_le_center {S : Type*} [Group S] (π : L →* S) (hπ : Function.Surjective π)
    (hS : Group.IsPerfect S) {P : Subgroup L} [P.Normal] (hker : π.ker = P)
    (hcyc : IsCyclic ↥(centerOf P)) (g : L) {z : L} (hz : z ∈ centerOf P) : g * z = z * g := by
  have := centerOf_normal (P := P)
  let ψ : L →* MulAut ↥(centerOf P) := MulAut.conjNormal
  let f : L →* (ZMod (Nat.card ↥(centerOf P)))ˣ :=
    (IsCyclic.mulAutMulEquiv ↥(centerOf P)).toMonoidHom.comp ψ
  have hf : π.ker ≤ f.ker := by
    intro k hk
    rw [hker] at hk
    rw [MonoidHom.mem_ker]
    have hψ : ψ k = 1 := by
      ext w
      have h1 := (mem_centerOf_iff.1 w.2).2 k hk
      have h2 : (((MulAut.conjNormal k : MulAut ↥(centerOf P)) w : ↥(centerOf P)) : L) =
          k * w * k⁻¹ := MulAut.conjNormal_apply k w
      show (((MulAut.conjNormal k : MulAut ↥(centerOf P)) w : ↥(centerOf P)) : L) = (w : L)
      rw [h2, mul_inv_eq_iff_eq_mul]
      exact h1
    simp [f, hψ]
  have hf1 := hom_eq_one_of_perfect_quotient π hπ hS f hf
  have hψg : ψ g = 1 := by
    have h1 : f g = 1 := by rw [hf1]; rfl
    exact (IsCyclic.mulAutMulEquiv ↥(centerOf P)).injective (by simpa [f] using h1)
  have h3 := congrArg (fun φ : MulAut ↥(centerOf P) => ((φ ⟨z, hz⟩ : ↥(centerOf P)) : L)) hψg
  have h2 : (((MulAut.conjNormal g : MulAut ↥(centerOf P)) ⟨z, hz⟩ : ↥(centerOf P)) : L) =
      g * z * g⁻¹ := MulAut.conjNormal_apply g ⟨z, hz⟩
  have h4 : g * z * g⁻¹ = z := by
    have h5 : (((MulAut.conjNormal g : MulAut ↥(centerOf P)) ⟨z, hz⟩ : ↥(centerOf P)) : L) = z :=
      h3
    rw [← h2]; exact h5
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4

theorem exists_mul_mem_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup L}
    (hP : IsPGroup p ↥P) {t : L} (ht : t ^ 2 = 1) {g : L} (hg : g * t * g⁻¹ * t⁻¹ ∈ P) :
    ∃ y ∈ P, y⁻¹ * g ∈ Subgroup.centralizer ({t} : Set L) := by
  set x := g * t * g⁻¹ * t⁻¹ with hx
  have htt : t * t = 1 := by rw [← sq]; exact ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hxt : x * t = g * t * g⁻¹ := by rw [hx]; group
  have hinv : t * x * t⁻¹ = x⁻¹ := by
    have h1 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    rw [← hxt] at h1
    have h2 : x * (t * x * t) = 1 := by
      calc x * (t * x * t) = (x * t) * (x * t) := by group
        _ = 1 := h1
    rw [htinv]
    exact eq_inv_of_mul_eq_one_right h2
  obtain ⟨k, hk⟩ := hP ⟨x, hg⟩
  have hxn : x ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, hj⟩ : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  rw [hj] at hxn
  set y := x ^ (j + 1) with hy
  have hyP : y ∈ P := P.pow_mem hg _
  have hty : t * y * t⁻¹ = y⁻¹ := by
    rw [hy, ← conj_pow, hinv, inv_pow]
  have h1 : t * y⁻¹ * t⁻¹ = y := by
    calc t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ := by group
      _ = y := by rw [hty, inv_inv]
  have h2 : y * t * y⁻¹ = x * t := by
    calc y * t * y⁻¹ = y * (t * y⁻¹ * t⁻¹) * t := by group
      _ = y * y * t := by rw [h1]
      _ = x ^ (2 * j + 1) * x * t := by rw [hy, ← pow_add, ← pow_succ]; congr 2; ring_nf
      _ = x * t := by rw [hxn, one_mul]
  refine ⟨y, hyP, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
  rw [Set.mem_singleton_iff.1 hh]
  rw [hxt] at h2
  calc t * (y⁻¹ * g) = y⁻¹ * (y * t * y⁻¹) * g := by group
    _ = y⁻¹ * (g * t * g⁻¹) * g := by rw [h2]
    _ = y⁻¹ * g * t := by group

theorem inv_mul_mem_iff_mul_inv_mem {P : Subgroup L} {u v : L} (hu : u ∈ P) (hv : v ∈ P) :
    u⁻¹ * v ∈ centerOf P ↔ u * v⁻¹ ∈ centerOf P := by
  constructor
  · intro h
    have h2 : u * (u⁻¹ * v) = (u⁻¹ * v) * u := (mem_centerOf_iff.1 h).2 u hu
    have h3 : v * u⁻¹ = u⁻¹ * v := by
      calc v * u⁻¹ = u * (u⁻¹ * v) * u⁻¹ := by group
        _ = (u⁻¹ * v) * u * u⁻¹ := by rw [h2]
        _ = u⁻¹ * v := by group
    have h4 : u * v⁻¹ = (u⁻¹ * v)⁻¹ := by
      calc u * v⁻¹ = (v * u⁻¹)⁻¹ := by group
        _ = (u⁻¹ * v)⁻¹ := by rw [h3]
    rw [h4]
    exact (centerOf P).inv_mem h
  · intro h
    have h2 : v * (u * v⁻¹) = (u * v⁻¹) * v := (mem_centerOf_iff.1 h).2 v hv
    have h3 : v⁻¹ * u = u * v⁻¹ := by
      calc v⁻¹ * u = v⁻¹ * (u * v⁻¹) * v := by group
        _ = v⁻¹ * ((u * v⁻¹) * v) := by group
        _ = v⁻¹ * (v * (u * v⁻¹)) := by rw [h2]
        _ = u * v⁻¹ := by group
    have h4 : u⁻¹ * v = (u * v⁻¹)⁻¹ := by
      calc u⁻¹ * v = (v⁻¹ * u)⁻¹ := by group
        _ = (u * v⁻¹)⁻¹ := by rw [h3]
    rw [h4]
    exact (centerOf P).inv_mem h

theorem pow_eq_one_of_lift {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (π : L →* SL(2, ZMod p))
    {Z C : Subgroup L} (hZc : ∀ g : L, ∀ z ∈ Z, g * z = z * g) (hZexp : ∀ z ∈ Z, z ^ p = 1)
    (hCZ : ∀ y ∈ C, π y = 1 → y ∈ Z) {c d : L} (hc : c ∈ C) (hd : d ∈ C)
    (hπc : π c = sl2U p) (hπd : π d * sl2U p = sl2U p ^ 4 * π d) : c ^ p = 1 := by
  have hUp : sl2U p ^ p = 1 := by
    have := pow_orderOf_eq_one (sl2U p)
    rwa [orderOf_sl2U] at this
  have hcp : c ^ p ∈ Z := hCZ _ (C.pow_mem hc p) (by rw [map_pow, hπc, hUp])
  set z'' := (c ^ 4 * d)⁻¹ * (d * c) with hz''
  have hz''C : z'' ∈ C :=
    C.mul_mem (C.inv_mem (C.mul_mem (C.pow_mem hc 4) hd)) (C.mul_mem hd hc)
  have hπz'' : π z'' = 1 := by
    rw [hz'', map_mul, map_inv, map_mul, map_mul, map_pow, hπc, hπd, inv_mul_cancel]
  have hz''Z : z'' ∈ Z := hCZ _ hz''C hπz''
  have hdc : d * c = c ^ 4 * d * z'' := by rw [hz'']; group
  have hconj : d * c * d⁻¹ = c ^ 4 * z'' := by
    calc d * c * d⁻¹ = c ^ 4 * d * z'' * d⁻¹ := by rw [hdc]
      _ = c ^ 4 * (d * z'' * d⁻¹) := by group
      _ = c ^ 4 * z'' := by rw [hZc d z'' hz''Z]; group
  have h1 : (d * c * d⁻¹) ^ p = c ^ p := by
    rw [conj_pow, hZc d _ hcp]; group
  have hcomm : Commute (c ^ 4) z'' := hZc _ z'' hz''Z
  have h2 : (d * c * d⁻¹) ^ p = (c ^ p) ^ 4 := by
    rw [hconj, hcomm.mul_pow, hZexp z'' hz''Z, mul_one, ← pow_mul, ← pow_mul, mul_comm]
  have h3 : c ^ p = (c ^ p) ^ 4 := h1.symm.trans h2
  have h4 : (c ^ p) ^ 3 = 1 := by
    have : (c ^ p) * (c ^ p) ^ 3 = (c ^ p) * 1 := by
      rw [mul_one, ← pow_succ']; exact h3.symm
    exact mul_left_cancel this
  have h5 : orderOf (c ^ p) ∣ 3 := orderOf_dvd_of_pow_eq_one h4
  have h6 : orderOf (c ^ p) ∣ p := orderOf_dvd_of_pow_eq_one (hZexp _ hcp)
  have h7 : Nat.gcd 3 p = 1 := by
    have : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 this).symm
  have h8 : orderOf (c ^ p) ∣ Nat.gcd 3 p := Nat.dvd_gcd h5 h6
  rw [h7] at h8
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h8)

end General

end A1c

end CFSG.Quasithin
