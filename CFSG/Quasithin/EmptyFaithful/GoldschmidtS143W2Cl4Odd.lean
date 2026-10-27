module

public import CFSG.Quasithin.EmptyFaithful.Insp7RedA
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace S143

namespace InspW2

variable {G : Type} [Group G]

theorem mem_of_orderOf_three {L H P : Subgroup G} (hLH : L ≤ H)
    (hN : H ≤ Subgroup.normalizer (L : Set G)) (hP : IsPGroup 2 P)
    (hPc : H ⊓ Subgroup.centralizer (L : Set G) ≤ P) (hout : Nat.card (Outer ↥L) = 2) {n : G}
    (hn : n ∈ H) (h3 : orderOf n = 3) : n ∈ L := by
  set k : ↥H := ⟨n, hn⟩ with hk
  have hk3 : orderOf k = 3 := by rw [hk, Subgroup.orderOf_mk]; exact h3
  set σ : MulAut ↥L := Insp7.actOn hN k with hσdef
  have hσ : orderOf σ ∣ 3 := hk3 ▸ orderOf_map_dvd _ k
  set q : Outer ↥L := QuotientGroup.mk' (inner ↥L) σ with hq
  have hq3 : orderOf q ∣ 3 := (orderOf_map_dvd (QuotientGroup.mk' (inner ↥L)) σ).trans hσ
  have hq2 : orderOf q ∣ 2 := hout ▸ orderOf_dvd_natCard q
  have hq1 : orderOf q = 1 := by
    have : orderOf q ∣ Nat.gcd 3 2 := Nat.dvd_gcd hq3 hq2
    exact Nat.eq_one_of_dvd_one (by simpa using this)
  have hq0 : q = 1 := orderOf_eq_one_iff.mp hq1
  have hσin : σ ∈ inner ↥L := (QuotientGroup.eq_one_iff σ).mp hq0
  obtain ⟨l, hl⟩ := hσin
  have hconj : ∀ y : ↥L, (n : G) * y * (n : G)⁻¹ = (l : G) * y * (l : G)⁻¹ := by
    intro y
    have h1 := congrArg (fun m : ↥L => (m : G)) (DFunLike.congr_fun hl y)
    simp only [MulAut.conj_apply, hσdef, Insp7.actOn_apply_coe] at h1
    exact h1.symm
  set p : G := (l : G)⁻¹ * n with hpdef
  have hpH : p ∈ H := H.mul_mem (H.inv_mem (hLH l.2)) hn
  have hpC : p ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hconj ⟨y, hy⟩
    calc y * p = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * n := by rw [hpdef]; group
      _ = (l : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * n := by rw [h1]
      _ = p * y := by rw [hpdef]; group
  have hpP : p ∈ P := hPc ⟨hpH, hpC⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨p, hpP⟩
  have hpm : p ^ (2 ^ m) = 1 := by
    have h1 : orderOf p = 2 ^ m := (Subgroup.orderOf_mk _ _).symm.trans hm
    rw [← h1]; exact pow_orderOf_eq_one p
  have hcomm : Commute (l : G) p := Subgroup.mem_centralizer_iff.mp hpC (l : G) l.2
  have hn_eq : n = (l : G) * p := by rw [hpdef]; group
  have hn3 : n ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one n
  have h4m : n ^ (4 ^ m) = n := by
    have h5 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    rw [← pow_mod_orderOf, h3, h5, pow_one]
  have hpow : n ^ (4 ^ m) = (l : G) ^ (4 ^ m) := by
    have h6 : p ^ (4 ^ m) = 1 := by
      rw [show 4 ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num, pow_mul, hpm, one_pow]
    rw [hn_eq, hcomm.mul_pow, h6, mul_one]
  rw [← h4m, hpow]
  exact L.pow_mem l.2 _

end InspW2

end S143

end CFSG.Quasithin
