module

public import CFSG.Quasithin.Background.F918P5

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F918Fine4Pf

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem isPerfect_autIH (h : HypF918 T V L V₁ Vp H K) (I : Subgroup G) :
    Group.IsPerfect ↥(autIH V₁ I H K) :=
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.K_cComp)
  Group.IsPerfect.ofSurjective (toAutI_surjective h I)

theorem eq_one_of_mem_center_of_sq (h : HypF918 T V L V₁ Vp H K) (hK : conjClosure K T = K)
    {z : ↥(autIH V₁ Vp H K)} (hz : z ∈ Subgroup.center ↥(autIH V₁ Vp H K)) (hz2 : z ^ 2 = 1) :
    z = 1 := by
  have := factElem h (le_conjClosure Vp H)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  set N : Subgroup ↥K := (Subgroup.zpowers z).comap (toAutI h Vp) with hN
  have hNn : N.Normal :=
    (Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)).comap (toAutI h Vp)
  set E : Subgroup G := N.map K.subtype with hE
  have hEK : E ≤ conjClosure K T := by
    rw [hK]
    exact Subgroup.map_subtype_le N
  have hKE : conjClosure K T ≤ Subgroup.normalizer (E : Set G) := by
    have hle := Subgroup.le_normalizer_map (H := N) K.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hNn, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hle
    rw [hK]
    exact hle
  have h2 : ∀ e ∈ E, ∃ k : ℕ, e ^ 2 ^ k ∈ pCoreOf 2 H := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨1, ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hx)
    have hx2 : toAutI h Vp (x ^ 2) = 1 := by
      rw [map_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2,
        one_zpow]
    have hmem := mem_pCoreOf_of_actH_eq_one h (x := Subgroup.inclusion hKH (x ^ 2))
      ((toAutI_eq_one_iff h Vp _).mp hx2)
    simpa using hmem
  have hEO := h.F918_1.2.2.2 E hEK hKE h2
  obtain ⟨x, rfl⟩ := toAutI_surjective h Vp z
  have hxE : (x : G) ∈ E :=
    ⟨x, Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _), rfl⟩
  rw [toAutI_eq_one_iff]
  exact h.actH_eq_one_of_mem_pCoreOf (le_conjClosure Vp H) (x := Subgroup.inclusion hKH x)
    (hEO hxE)

theorem odd_card_center_autIH (h : HypF918 T V L V₁ Vp H K) (hK : conjClosure K T = K) :
    Odd (Nat.card (Subgroup.center ↥(autIH V₁ Vp H K))) := by
  rw [Nat.odd_iff]
  by_contra h2
  have h2' : 2 ∣ Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2'
  have hz2 : (z : ↥(autIH V₁ Vp H K)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have h1 := eq_one_of_mem_center_of_sq h hK z.2 hz2
  have hz1 : z = 1 := Subtype.ext h1
  rw [hz1, orderOf_one] at hz
  omega

end F918Fine4Pf

end CFSG.Quasithin
