module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseA3Setup

public section

namespace CFSG.Quasithin.H13.GM22.CaseA3

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] {T L V D : Subgroup G} {z : G}
  {φ : ↥(NV V) →* Equiv.Perm (Fin 5)}

namespace Setup

variable (C : Setup T L V D z φ) {d₀ : G} (hd : IsD0 T L z d₀)

include C hd in
theorem d0_mem_NV : d₀ ∈ NV V := C.L_le hd.mem_L

include C hd in
theorem d0_mem_normalizer_zs :
    d₀ ∈ Subgroup.normalizer ((zs T L V : Subgroup G) : Set G) :=
  mem_normalizer_inf_centralizer (C.L_le hd.mem_L) hd.mem_normalizer

include C hd in
theorem conj_z_mem_zs : d₀ * z * d₀⁻¹ ∈ zs T L V :=
  (Subgroup.mem_normalizer_iff.mp (d0_mem_normalizer_zs C hd) z).mp C.z_mem_zs

include C hd in
theorem inv_conj_mem_zs {u : G} (hu : u ∈ zs T L V) : d₀⁻¹ * u * d₀ ∈ zs T L V := by
  have hinv := (Subgroup.normalizer (zs T L V : Set G)).inv_mem (d0_mem_normalizer_zs C hd)
  simpa using (Subgroup.mem_normalizer_iff.mp hinv u).mp hu

include C hd in
theorem inter_mem_L {x : G} (hxD : x ∈ D) (hxc : x ∈ conjSubgroup D d₀⁻¹) : x ∈ L := by
  by_contra hxL
  have hxT : x ∈ T := C.D_le_T hxD
  have hz0 := conj_z_mem_zs C hd
  obtain ⟨y, hyD, rfl⟩ : ∃ y ∈ D, x = d₀ * y * d₀⁻¹ :=
    ⟨d₀⁻¹ * x * d₀, by simpa [mem_conjSubgroup_iff] using hxc, by group⟩
  have hx0 : Commute (d₀ * y * d₀⁻¹) (d₀ * z * d₀⁻¹) := by
    show d₀ * y * d₀⁻¹ * (d₀ * z * d₀⁻¹) = d₀ * z * d₀⁻¹ * (d₀ * y * d₀⁻¹)
    calc d₀ * y * d₀⁻¹ * (d₀ * z * d₀⁻¹) = d₀ * (y * z) * d₀⁻¹ := by group
      _ = d₀ * (z * y) * d₀⁻¹ := by rw [C.D_comm y hyD]
      _ = _ := by group
  have hall : ∀ t ∈ T, t * (d₀ * z * d₀⁻¹) = d₀ * z * d₀⁻¹ * t := by
    intro t ht
    by_cases htL : t ∈ L
    · exact comm_of_mem_zs ⟨ht, htL⟩ hz0
    · have hw : (d₀ * y * d₀⁻¹)⁻¹ * t ∈ T ⊓ L :=
        ⟨T.mul_mem (T.inv_mem hxT) ht, C.inv_mul_mem_L hxT ht hxL htL⟩
      have hw' : Commute ((d₀ * y * d₀⁻¹)⁻¹ * t) (d₀ * z * d₀⁻¹) := comm_of_mem_zs hw hz0
      have e : t = (d₀ * y * d₀⁻¹) * ((d₀ * y * d₀⁻¹)⁻¹ * t) := by group
      rw [e]
      exact (Commute.mul_left hx0 hw').eq
  rcases C.eq_one_or_eq _ hz0.1 hall with h1 | h1
  · apply C.z_ne_one
    simpa using mul_inv_eq_one.mp h1
  · exact hd.moves h1

variable [Finite G] in
include C in
theorem relIndex_two {y : G} (hyD : y ∈ D) (hyL : y ∈ L) (hyV : y ∉ V) :
    V.relIndex (D ⊓ L) = 2 := by
  have hVDL : V ⊓ (D ⊓ L) = V ⊓ D := by
    ext u
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨hu, hd, _⟩ => ⟨hu, hd⟩, fun ⟨hu, hd⟩ => ⟨hu, hd, C.V_le_L hu⟩⟩
  have h1 := Subgroup.relIndex_mul_card (H := V) (K := D ⊓ L)
  rw [hVDL, C.card_V_inf_D] at h1
  have hdvd : Nat.card ↥(D ⊓ L) ∣ 32 := C.card_D ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne32 : Nat.card ↥(D ⊓ L) ≠ 32 := fun h32 => C.not_D_le_L (by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_left : D ⊓ L ≤ D) (by rw [h32, C.card_D])
    exact inf_eq_left.mp this)
  have hr1 : V.relIndex (D ⊓ L) ≠ 1 := fun h1' => hyV (Subgroup.relIndex_eq_one.mp h1' ⟨hyD, hyL⟩)
  have hr4 : V.relIndex (D ⊓ L) ∣ 4 := by
    have : V.relIndex (D ⊓ L) * 8 ∣ 4 * 8 := by rw [h1]; simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have hle : V.relIndex (D ⊓ L) ≤ 4 := Nat.le_of_dvd (by norm_num) hr4
  generalize hr : V.relIndex (D ⊓ L) = r at *
  interval_cases r <;> omega

variable [Finite G] in
include C hd in
theorem inter_mem_V {x : G} (hxD : x ∈ D) (hxc : x ∈ conjSubgroup D d₀⁻¹) : x ∈ V := by
  have hxL : x ∈ L := inter_mem_L C hd hxD hxc
  by_contra hxV
  obtain ⟨y, hyD, rfl⟩ : ∃ y ∈ D, x = d₀ * y * d₀⁻¹ :=
    ⟨d₀⁻¹ * x * d₀, by simpa [mem_conjSubgroup_iff] using hxc, by group⟩
  have hdN := d0_mem_NV C hd
  have hyL : y ∈ L := by
    have := L.mul_mem (L.mul_mem (L.inv_mem hd.mem_L) hxL) hd.mem_L
    simpa [mul_assoc] using this
  have hyV : y ∉ V := fun hy => hxV ((Subgroup.mem_normalizer_iff.mp hdN y).mp hy)
  have h2 := C.relIndex_two hyD hyL hyV
  have hxy : d₀ * y * d₀⁻¹ * y ∈ V :=
    mul_mem_of_relIndex_eq_two h2 ⟨hxD, hxL⟩ ⟨hyD, hyL⟩ hxV hyV
  have hyy : y * y ∈ V := mul_mem_of_relIndex_eq_two h2 ⟨hyD, hyL⟩ ⟨hyD, hyL⟩ hyV hyV
  have hyN : y ∈ NV V := C.T_le (C.D_le_T hyD)
  have hxN : d₀ * y * d₀⁻¹ ∈ NV V := (NV V).mul_mem ((NV V).mul_mem hdN hyN) ((NV V).inv_mem hdN)
  have hw2 : φ ⟨y, hyN⟩ * φ ⟨y, hyN⟩ = 1 := by
    have := (C.ker_phi (⟨y, hyN⟩ * ⟨y, hyN⟩)).mpr hyy
    rwa [map_mul] at this
  have hxw : φ ⟨d₀ * y * d₀⁻¹, hxN⟩ * φ ⟨y, hyN⟩ = 1 := by
    have := (C.ker_phi (⟨d₀ * y * d₀⁻¹, hxN⟩ * ⟨y, hyN⟩)).mpr hxy
    rwa [map_mul] at this
  have hconj : φ ⟨d₀ * y * d₀⁻¹, hxN⟩ = φ ⟨d₀, hdN⟩ * φ ⟨y, hyN⟩ * (φ ⟨d₀, hdN⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hcomm : φ ⟨d₀, hdN⟩ * φ ⟨y, hyN⟩ = φ ⟨y, hyN⟩ * φ ⟨d₀, hdN⟩ := by
    have h1 : φ ⟨d₀ * y * d₀⁻¹, hxN⟩ = φ ⟨y, hyN⟩ := by
      have := eq_inv_of_mul_eq_one_left hxw
      rw [this]
      exact (inv_eq_of_mul_eq_one_right hw2)
    rw [hconj] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  have hw1 : φ ⟨y, hyN⟩ ≠ 1 := fun h1 => hyV ((C.ker_phi _).mp h1)
  have hsign : Equiv.Perm.sign (φ ⟨y, hyN⟩) = 1 := (C.mem_L_iff _).mp hyL
  have hδ : (φ ⟨d₀, hdN⟩) ^ orderOf d₀ = 1 := by
    rw [← map_pow]
    have : (⟨d₀, hdN⟩ : ↥(NV V)) ^ orderOf d₀ = 1 := Subtype.ext (by simp)
    rw [this, map_one]
  have hδ1 := perm_fin_five_eq_one_of_commute hd.prime hd.ne_two hw2 hw1 hsign hcomm hδ
  have hd0V : d₀ ∈ V := (C.ker_phi ⟨d₀, hdN⟩).mp hδ1
  exact orderOf_ne_prime_of_isPGroup C.isPGroup_T (C.V_le_T hd0V) hd.prime hd.ne_two rfl

end Setup

end CFSG.Quasithin.H13.GM22.CaseA3
