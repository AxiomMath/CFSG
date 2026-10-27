module

public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartDefs
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxLift
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.StandardType.N2Chart

variable {G : Type} [Group G]

theorem F4_pow_three {c : F4} (hc : c ≠ 0) : c ^ 3 = 1 := by
  let : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [hcard] at h

theorem pow_three_eq_one_of_mem_center {z : SL6} (hz : z ∈ Subgroup.center SL6) :
    z ^ 3 = 1 := by
  obtain ⟨r, hr6, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr6
  have hr3 : r ^ 3 = 1 := F4_pow_three hr0
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr3, map_one,
    Matrix.SpecialLinearGroup.coe_one]

variable {ψ : SL6 →* G}

theorem ker_pow_three (hψ : ψ.ker ≤ Subgroup.center SL6) : ∀ z ∈ ψ.ker, z ^ 3 = 1 :=
  fun _ hz => pow_three_eq_one_of_mem_center (hψ hz)

theorem exists_lift_five (hψ : ψ.ker ≤ Subgroup.center SL6) {x : G} (hx : x ∈ ψ.range)
    (h5 : x ^ 5 = 1) : ∃ s : SL6, s ^ 5 = 1 ∧ ψ s = x :=
  CFSG.Quasithin.H13.lift_five_L3 (ker_pow_three hψ) hx h5

theorem lift_five_unique (hψ : ψ.ker ≤ Subgroup.center SL6) {s s' : SL6} (h : ψ s = ψ s')
    (hs : s ^ 5 = 1) (hs' : s' ^ 5 = 1) : s = s' :=
  CFSG.Quasithin.H13.lift_five_unique_L3 hψ (ker_pow_three hψ) h hs hs'

theorem orderOf_eq_five_of_lift {s : SL6} (hs : s ^ 5 = 1) (h : orderOf (ψ s) = 5) :
    orderOf s = 5 := by
  have hdvd : orderOf s ∣ 5 := orderOf_dvd_of_pow_eq_one hs
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
  · rw [orderOf_eq_one_iff] at h1
    rw [h1, map_one, orderOf_one] at h
    norm_num at h
  · exact h5

theorem commute_of_map_commute_five (hψ : ψ.ker ≤ Subgroup.center SL6) {s g : SL6}
    (hs : s ^ 5 = 1) (h : Commute (ψ g) (ψ s)) : Commute g s := by
  have h1 : ψ (g * s * g⁻¹) = ψ s := by
    rw [map_mul, map_mul, map_inv, h.eq, mul_inv_cancel_right]
  have h2 : (g * s * g⁻¹) ^ 5 = 1 := by
    rw [conj_pow, hs, mul_one, mul_inv_cancel]
  exact mul_inv_eq_iff_eq_mul.mp (lift_five_unique hψ h1 h2 hs)

theorem comap_inf_centralizer (hψ : ψ.ker ≤ Subgroup.center SL6) (X : Subgroup G) {s : SL6}
    (hs : s ^ 5 = 1) :
    (X ⊓ Subgroup.centralizer ({ψ s} : Set G)).comap ψ =
      X.comap ψ ⊓ Subgroup.centralizer ({s} : Set SL6) := by
  ext g
  simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hgX, hc⟩
    exact ⟨hgX, (commute_of_map_commute_five hψ hs hc).eq⟩
  · rintro ⟨hgX, hc⟩
    refine ⟨hgX, ?_⟩
    rw [← map_mul, hc, map_mul]

theorem map_comap_inf_centralizer (hψ : ψ.ker ≤ Subgroup.center SL6) {X : Subgroup G}
    (hX : X ≤ ψ.range) {s : SL6} (hs : s ^ 5 = 1) :
    (X.comap ψ ⊓ Subgroup.centralizer ({s} : Set SL6)).map ψ =
      X ⊓ Subgroup.centralizer ({ψ s} : Set G) := by
  rw [← comap_inf_centralizer hψ X hs, Subgroup.map_comap_eq_self (inf_le_left.trans hX)]

theorem exists_inverter_lift (hψ : ψ.ker ≤ Subgroup.center SL6) {X : Subgroup G}
    (hX : X ≤ ψ.range) {s t : SL6} (hs : s ^ 5 = 1) (ht : t ^ 5 = 1) {h : G}
    (hh : h ∈ X ⊓ Subgroup.centralizer ({ψ s} : Set G)) (hinv : h * ψ t * h⁻¹ = (ψ t)⁻¹) :
    ∃ g ∈ X.comap ψ ⊓ Subgroup.centralizer ({s} : Set SL6), g * t * g⁻¹ = t⁻¹ := by
  rw [← map_comap_inf_centralizer hψ hX hs] at hh
  obtain ⟨g, hg, rfl⟩ := hh
  refine ⟨g, hg, lift_five_unique hψ ?_ ?_ ?_⟩
  · rw [map_mul, map_mul, map_inv, hinv, map_inv]
  · rw [conj_pow, ht, mul_one, mul_inv_cancel]
  · rw [inv_pow, ht, inv_one]

end CFSG.StandardType.N2Chart

end
