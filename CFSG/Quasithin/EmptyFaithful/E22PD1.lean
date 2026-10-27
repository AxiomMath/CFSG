module

public import CFSG.Quasithin.EmptyFaithful.E22PD1B
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open DihedralGroup

section Transport

variable {D H : Type*} [Group D] [Group H]

theorem e22pd1_exists_embedding {T : Subgroup H} (e : T ≃* D) :
    ∃ ι : D →* H, Function.Injective ι ∧ ι.range = T := by
  refine ⟨T.subtype.comp e.symm.toMonoidHom, Subtype.val_injective.comp e.symm.injective, ?_⟩
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    exact (e.symm d).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp⟩

theorem e22pd1_exists_map_eq {ι : D →* H} {V : Subgroup H} (hV : V ≤ ι.range) :
    ∃ W : Subgroup D, W.map ι = V :=
  ⟨V.comap ι, Subgroup.map_comap_eq_self hV⟩

theorem e22pd1_range_inf_normalizer_map (ι : D →* H) (hι : Function.Injective ι)
    (W : Subgroup D) :
    ι.range ⊓ Subgroup.normalizer ((W.map ι : Subgroup H) : Set H) =
      (Subgroup.normalizer (W : Set D)).map ι := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨d, rfl⟩, hx⟩
    refine ⟨d, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h := Subgroup.mem_normalizer_iff.mp hx (ι w)
    rwa [Subgroup.mem_map_iff_mem hι, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hι] at h
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨d * w * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd w).mp hw, by simp⟩
    · rintro ⟨w, hw, hwg⟩
      refine ⟨d⁻¹ * w * d, (Subgroup.mem_normalizer_iff''.mp hd w).mp hw, ?_⟩
      rw [map_mul, map_mul, map_inv, hwg]
      group

theorem e22pd1_range_inf_centralizer_map (ι : D →* H) (hι : Function.Injective ι)
    (W : Subgroup D) :
    ι.range ⊓ Subgroup.centralizer ((W.map ι : Subgroup H) : Set H) =
      (Subgroup.centralizer (W : Set D)).map ι := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨d, rfl⟩, hx⟩
    refine ⟨d, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h := Subgroup.mem_centralizer_iff.mp hx (ι w) ⟨w, hw, rfl⟩
    exact hι (by rw [map_mul, map_mul]; exact h)
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨d, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hd w hw]

theorem e22pd1_map_normalizer_le (ι : D →* H) (hι : Function.Injective ι) (W : Subgroup D) :
    (Subgroup.normalizer (W : Set D)).map ι ≤
      Subgroup.normalizer ((W.map ι : Subgroup H) : Set H) := by
  rw [← e22pd1_range_inf_normalizer_map ι hι W]
  exact inf_le_right

theorem e22pd1_isKleinFour_map (ι : D →* H) (hι : Function.Injective ι) {W : Subgroup D}
    (hW : IsKleinFour ↥W) : IsKleinFour ↥(W.map ι) :=
  let eW := W.equivMapOfInjective ι hι
  { card_four := (Nat.card_congr eW.toEquiv).symm.trans hW.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eW).symm.trans hW.exponent_two }

theorem e22pd1_isKleinFour_of_map (ι : D →* H) (hι : Function.Injective ι) {W : Subgroup D}
    (hW : IsKleinFour ↥(W.map ι)) : IsKleinFour ↥W :=
  let eW := W.equivMapOfInjective ι hι
  { card_four := (Nat.card_congr eW.toEquiv).trans hW.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eW).trans hW.exponent_two }

end Transport

section Main

set_option linter.unusedSectionVars false

variable {H : Type} [Group H] [Finite H]

theorem dihedral_sylow_data {T : Subgroup H} {m : ℕ} (hm : 2 ≤ m)
    (e : T ≃* DihedralGroup (2 ^ m)) :
    ∃ z : H, z ∈ T ∧ orderOf z = 2 ∧ (∀ t ∈ T, z * t = t * z) ∧
      (∀ V : Subgroup H, V ≤ T → IsKleinFour ↥V → z ∈ V) ∧
      (∀ A : Subgroup H, A ≤ T → IsElemAbelian 2 A → 4 ≤ Nat.card A →
        Nat.card A = 4 ∧ IsKleinFour ↥A) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ι, hι, rfl⟩ := e22pd1_exists_embedding e
  have hh0 : (2 ^ (k + 1) : ZMod (2 ^ (k + 2))) ≠ 0 := e22pd1_two_pow_ne_zero (by omega)
  refine ⟨ι (r (2 ^ (k + 1))), ⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective ι hι]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, r_mul_r, e22pd1_h_add_h k, r_zero]
    · intro h
      rw [← r_zero] at h
      exact hh0 (DihedralGroup.r.inj h)
  · rintro _ ⟨x, rfl⟩
    rw [← map_mul, ← map_mul, e22pd1_r_h_comm]
  · intro V hV hVK
    obtain ⟨W, rfl⟩ := e22pd1_exists_map_eq hV
    exact Subgroup.mem_map_of_mem ι
      (e22pd1_r_mem_of_isKleinFour (e22pd1_isKleinFour_of_map ι hι hVK))
  · intro A hA hAe hcard
    obtain ⟨W, rfl⟩ := e22pd1_exists_map_eq hA
    have hcardW : Nat.card (W.map ι) = Nat.card W := Subgroup.card_map_of_injective hι
    have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
      intro x hx y hy
      have h := hAe.1.is_comm.comm (⟨ι x, Subgroup.mem_map_of_mem ι hx⟩ : W.map ι)
        ⟨ι y, Subgroup.mem_map_of_mem ι hy⟩
      apply hι
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h
    have hsq : ∀ x ∈ W, x * x = 1 := by
      intro x hx
      have h := hAe.2 (ι x) (Subgroup.mem_map_of_mem ι hx)
      apply hι
      rw [map_mul, map_one, ← pow_two]
      exact h
    obtain ⟨a, rfl⟩ := e22pd1_exists_kf_eq hcomm hsq (by omega)
    exact ⟨by rw [hcardW, e22pd1_kf_card],
      e22pd1_isKleinFour_map ι hι (e22pd1_isKleinFour_kf k a)⟩

theorem dihedral_kleinFour_partner {T : Subgroup H} {m : ℕ} (hm : 2 ≤ m)
    (e : T ≃* DihedralGroup (2 ^ m)) {V : Subgroup H} (hVT : V ≤ T) (hV : IsKleinFour ↥V) :
    ∃ V' : Subgroup H, V' ≤ T ∧ IsKleinFour ↥V' ∧ V' ≠ V ∧ V' ≤ Subgroup.normalizer (V : Set H) ∧
      V ≤ Subgroup.normalizer (V' : Set H) ∧
      Nat.card ↥(T ⊓ Subgroup.normalizer (V' : Set H)) = 8 ∧
      T ⊓ Subgroup.centralizer (V : Set H) ≤ Subgroup.normalizer (V' : Set H) ∧
      ⁅T ⊓ Subgroup.normalizer (V' : Set H), V⁆ ≤ V' := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ι, hι, rfl⟩ := e22pd1_exists_embedding e
  obtain ⟨W, rfl⟩ := e22pd1_exists_map_eq hVT
  obtain ⟨W', hW'K, hne, hW'N, hWN', hcard, hC, hcomm⟩ :=
    e22pd1_partner_D (e22pd1_isKleinFour_of_map ι hι hV)
  refine ⟨W'.map ι, Subgroup.map_le_range ι W', e22pd1_isKleinFour_map ι hι hW'K, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun h => hne (Subgroup.map_injective hι h)
  · exact (Subgroup.map_mono hW'N).trans (e22pd1_map_normalizer_le ι hι W)
  · exact (Subgroup.map_mono hWN').trans (e22pd1_map_normalizer_le ι hι W')
  · rw [e22pd1_range_inf_normalizer_map ι hι W', Subgroup.card_map_of_injective hι]
    exact hcard
  · rw [e22pd1_range_inf_centralizer_map ι hι W]
    exact (Subgroup.map_mono hC).trans (e22pd1_map_normalizer_le ι hι W')
  · rw [e22pd1_range_inf_normalizer_map ι hι W', ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcomm

set_option linter.unusedVariables false in
theorem dihedral_normalizer_le_of_index_two {T T₀ : Subgroup H} {m : ℕ} (hm : 3 ≤ m)
    (e : T ≃* DihedralGroup (2 ^ m)) (hT₀T : T₀ ≤ T) (hidx : T₀.relIndex T = 2)
    {V V' : Subgroup H} (hVT : V ≤ T₀) (hV : IsKleinFour ↥V) (hV'T : V' ≤ T)
    (hV' : IsKleinFour ↥V') (hVV' : V ≤ Subgroup.normalizer (V' : Set H))
    (hV'V : V' ≤ Subgroup.normalizer (V : Set H)) (hne : V' ≠ V)
    (hN8 : Nat.card ↥(T ⊓ Subgroup.normalizer (V' : Set H)) = 8) :
    T ⊓ Subgroup.normalizer (V' : Set H) ≤ T₀ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ι, hι, rfl⟩ := e22pd1_exists_embedding e
  obtain ⟨X, rfl⟩ := e22pd1_exists_map_eq hT₀T
  obtain ⟨W, rfl⟩ := e22pd1_exists_map_eq (hVT.trans hT₀T)
  obtain ⟨W', rfl⟩ := e22pd1_exists_map_eq hV'T
  have hsq : ∀ x : DihedralGroup (2 ^ (k + 2)), x * x ∈ X := by
    intro x
    have h := Subgroup.mul_self_mem_of_index_two
      (H := (X.map ι).subgroupOf ι.range) hidx ⟨ι x, x, rfl⟩
    rw [Subgroup.mem_subgroupOf] at h
    obtain ⟨y, hy, hyx⟩ := h
    have hyx' : y = x * x := hι (by rw [hyx, map_mul]; rfl)
    exact hyx' ▸ hy
  have hWX : W ≤ X := (Subgroup.map_le_map_iff_of_injective hι).mp hVT
  have hW'N : W' ≤ Subgroup.normalizer (W : Set (DihedralGroup (2 ^ (k + 2)))) := by
    intro d hd
    have h1 := hV'V (Subgroup.mem_map_of_mem ι hd)
    have h2 : ι d ∈ ι.range ⊓ Subgroup.normalizer ((W.map ι : Subgroup H) : Set H) :=
      Subgroup.mem_inf.mpr ⟨⟨d, rfl⟩, h1⟩
    rw [e22pd1_range_inf_normalizer_map ι hι W] at h2
    obtain ⟨y, hy, hyd⟩ := h2
    rwa [← hι hyd]
  have h := e22pd1_normalizer_le_D (by omega) hsq (e22pd1_isKleinFour_of_map ι hι hV)
    (e22pd1_isKleinFour_of_map ι hι hV') hWX hW'N
  rw [e22pd1_range_inf_normalizer_map ι hι W']
  exact Subgroup.map_mono h

theorem dihedral_central_involution_sq {T : Subgroup H} {m : ℕ} (hm : 2 ≤ m)
    (e : T ≃* DihedralGroup (2 ^ m)) {z : H} (hzT : z ∈ T) (hz2 : orderOf z = 2)
    (hzc : ∀ t ∈ T, z * t = t * z) : ∃ t ∈ T, t ^ 2 = z := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨ι, hι, rfl⟩ := e22pd1_exists_embedding e
  obtain ⟨d, rfl⟩ := hzT
  have hd2 : orderOf d = 2 := by rw [← orderOf_injective ι hι d]; exact hz2
  have hdc : d ∈ Subgroup.center (DihedralGroup (2 ^ (k + 2))) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hι
    rw [map_mul, map_mul]
    exact (hzc (ι g) ⟨g, rfl⟩).symm
  have hdsq : d ^ 2 = 1 := by
    have h := pow_orderOf_eq_one d
    rwa [hd2] at h
  have hdne : d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hd2
    omega
  have hd : d = r (2 ^ (k + 1)) :=
    CFSG.GorensteinWalter.unique_central_involution_of_dihedral_two_pow
      (m := k + 2) (by omega) d hdc hdsq hdne
  refine ⟨ι (r (2 ^ k)), ⟨_, rfl⟩, ?_⟩
  rw [← map_pow, hd, pow_two, r_mul_r]
  congr 2
  ring

end Main

end CFSG.Quasithin.E22L2
