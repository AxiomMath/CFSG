module

public import CFSG.Quasithin.Background.HM22RowMain
public import CFSG.Quasithin.Background.H12OneHatM22PfMain
public import CFSG.CharacterTheory.Semidihedral.SemilinearLayerModel
public import CFSG.Quasithin.AppendixH.H12.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {V : Type} [CommGroup V]
  {ρ : G →* MulAut V}

theorem normal_of_fitting (hF : CFSG.generalizedFitting G = L) : L.Normal := by
  rw [← hF]
  exact CFSG.Semidihedral.SemilinearLayerModel.generalizedFitting_normal G

theorem centralizer_le_of_fitting (hF : CFSG.generalizedFitting G = L) :
    Subgroup.centralizer (L : Set G) ≤ L := by
  rw [← hF]
  exact CFSG.centralizer_generalizedFitting_le G

theorem injective_of_fitting (hF : CFSG.generalizedFitting G = L)
    (hinj : Function.Injective (ρ.comp L.subtype)) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hLnorm : L.Normal := normal_of_fitting hF
  have hkerL : ρ.ker ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxker, hxL⟩ := Subgroup.mem_inf.mp hx
    have h1 : (ρ.comp L.subtype) ⟨x, hxL⟩ = 1 := by
      rw [MonoidHom.comp_apply, Subgroup.subtype_apply]
      exact MonoidHom.mem_ker.mp hxker
    have h2 : (⟨x, hxL⟩ : ↥L) = 1 := hinj (by rw [h1, map_one])
    exact Subtype.ext_iff.mp h2
  have hgker : g ∈ ρ.ker := MonoidHom.mem_ker.mpr hg
  have hgL : g ∈ L := by
    apply centralizer_le_of_fitting hF
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hmem : g * l * g⁻¹ * l⁻¹ ∈ ρ.ker ⊓ L := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [MonoidHom.mem_ker]
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg]
        simp
      · exact L.mul_mem (hLnorm.conj_mem l hl g) (L.inv_mem hl)
    rw [hkerL, Subgroup.mem_bot] at hmem
    have hmem' : (g * l) * (l * g)⁻¹ = 1 := by
      rw [mul_inv_rev]
      simpa only [mul_assoc] using hmem
    exact (mul_inv_eq_one.mp hmem').symm
  rw [← Subgroup.mem_bot, ← hkerL, Subgroup.mem_inf]
  exact ⟨hgker, hgL⟩

theorem finite_of_faithIrr12 (h : IsFaithIrr12 (ρ.comp L.subtype)) : Finite V :=
  Nat.finite_of_card_ne_zero (by rw [h.2.1]; norm_num)

theorem isHat_map (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22)
    (hinj : Function.Injective (ρ.comp L.subtype)) :
    IsHat ↥(L.map ρ) ↥CFSG.Blueprint.NativeSporadic.M22 := by
  refine M22Link.isHat_of_mulEquiv'
    ((MonoidHom.ofInjective (f := ρ.comp L.subtype) hinj).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))) hL

theorem range_le_normalizer (hF : CFSG.generalizedFitting G = L) :
    ρ.range ≤ Subgroup.normalizer ((L.map ρ : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro x ⟨g, rfl⟩ y hy
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr
    ⟨g * l * g⁻¹, (normal_of_fitting hF).conj_mem l hl g, by rw [map_mul, map_mul, map_inv]⟩

theorem centralizer_inf_range_le (hF : CFSG.generalizedFitting G = L)
    (hinj : Function.Injective ρ) :
    Subgroup.centralizer ((L.map ρ : Subgroup (MulAut V)) : Set (MulAut V)) ⊓ ρ.range ≤
      L.map ρ := by
  intro x hx
  obtain ⟨hxcent, hxrange⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨g, rfl⟩ := hxrange
  have hgcent : g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hmap : ρ l ∈ L.map ρ := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hxcent (ρ l) hmap
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm
  exact Subgroup.mem_map.mpr ⟨g, centralizer_le_of_fitting hF hgcent, rfl⟩

theorem mhat22Twelve_map
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) : Mhat22Twelve (L.map ρ) ⊤ ⊥ := by
  haveI : Finite V := finite_of_faithIrr12 hρ
  have hL' : IsHat ↥(L.map ρ) ↥CFSG.Blueprint.NativeSporadic.M22 := isHat_map hL hρ.2.2.1
  have hW : Nat.card V = 4096 := by rw [hρ.2.1]; norm_num
  have hirr := M22Link.isIrrSec_of_isHat (W := V) hρ.1 hW hL'
  have hR := hatM22SmallModules_holds V hρ.1 (L.map ρ) hL' hirr (by rw [hW]; norm_num)
  exact ⟨FieldFour, inferInstance, inferInstance, hatM22Γ₀, FieldFour.natCard_eq,
    isHat_hatM22Γ₀, ⟨hatM22Form, hatM22Form_det_ne_zero, hatM22Form_hermitian,
      hatM22Form_invariant⟩, hR⟩

theorem card_le_two_mul_of_fitting
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) : Nat.card G ≤ 2 * Nat.card L := by
  haveI : Finite V := finite_of_faithIrr12 hρ
  haveI : Finite (MulAut V) := MulEquiv.finite_left
  have hinjρ : Function.Injective ρ := injective_of_fitting hF hρ.2.2.1
  obtain ⟨z, -, -, -, hz1, -, hdi⟩ :=
    M22Row.exists_center_gen (V := V) hρ.1 (mhat22Twelve_map hL hρ)
  have hrange := M22Row.card_le_two_mul (Y := MulAut V) (L := L.map ρ) (z := z) hz1 hdi
    (H := ρ.range) (range_le_normalizer hF)
  have hcardRange : Nat.card ↥ρ.range = Nat.card G := by
    rw [← Subgroup.map_top ρ, Subgroup.card_map_of_injective hinjρ, Subgroup.card_top]
  calc Nat.card G = Nat.card ↥ρ.range := hcardRange.symm
    _ ≤ 2 * Nat.card ↥(ρ.range ⊓ L.map ρ) := hrange
    _ = 2 * Nat.card ↥(L.map ρ) := by rw [inf_eq_right.mpr (Subgroup.map_le_range ρ L)]
    _ = 2 * Nat.card ↥L := by rw [Subgroup.card_map_of_injective hinjρ]

private theorem isSylowTwoOf_map {TG : Subgroup G} (hinj : Function.Injective ρ)
    (hTG : IsSylowIn 2 TG ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (TG.map ρ) ρ.range := by
  refine ⟨Subgroup.map_le_range ρ TG, IsPGroup.map hTG.isPGroup ρ, ?_⟩
  show ¬ 2 ∣ (TG.map ρ).relIndex ρ.range
  rw [show (TG.map ρ).relIndex ρ.range = TG.relIndex ⊤ from ?_]
  exact hTG.2.2
  rw [← Subgroup.map_top ρ]
  exact Subgroup.relIndex_map_map_of_injective TG ⊤ hinj

theorem card_fixV_sylow
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) (hlt : L < ⊤) {TG : Subgroup G}
    (hTG : IsSylowIn 2 TG ⊤) : Nat.card ↥(fixV (TG.map ρ)) = 2 := by
  haveI : Finite V := finite_of_faithIrr12 hρ
  haveI : Finite (MulAut V) := MulEquiv.finite_left
  have hinjρ : Function.Injective ρ := injective_of_fitting hF hρ.2.2.1
  have hM : Mhat22Twelve (L.map ρ) ⊤ ⊥ := mhat22Twelve_map hL hρ
  have hL' : IsHat ↥(L.map ρ) ↥CFSG.Blueprint.NativeSporadic.M22 := isHat_map hL hρ.2.2.1
  have hIndex2 : L.index = 2 := by
    have hle := card_le_two_mul_of_fitting hL hF hρ
    have hcard : Nat.card G = L.index * Nat.card L := by
      rw [← Subgroup.card_mul_index L, Nat.mul_comm]
    have hposL : 0 < Nat.card L := Nat.card_pos
    have hne : L ≠ ⊤ := ne_of_lt hlt
    have hge : 2 ≤ L.index := by
      have := Subgroup.one_lt_index_of_ne_top hne
      omega
    rw [hcard] at hle
    have h2 := Nat.le_of_mul_le_mul_right hle hposL
    omega
  have hTGnotle : ¬ TG ≤ L := by
    intro hTL
    have hdvd : 2 ∣ TG.index := by
      have hrel := Subgroup.relIndex_mul_index hTL
      rw [hIndex2] at hrel
      rw [← hrel]
      exact dvd_mul_left 2 _
    have hnot : ¬ 2 ∣ TG.index := by
      intro h
      exact hTG.2.2 (by simpa [Subgroup.relIndex_top_right] using h)
    exact hnot hdvd
  obtain ⟨g, hgTG, hgL⟩ := Set.not_subset.mp hTGnotle
  have hsup : L ⊔ TG = ⊤ := by
    refine Subgroup.index_eq_one.mp ?_
    have hdvd : (L ⊔ TG).index ∣ 2 := by
      rw [← hIndex2]
      exact Subgroup.index_dvd_of_le le_sup_left
    have hne2 : (L ⊔ TG).index ≠ 2 := by
      intro h2
      have hrel : L.relIndex (L ⊔ TG) = 1 := by
        have h := Subgroup.relIndex_mul_index (le_sup_left : L ≤ L ⊔ TG)
        rw [h2, hIndex2] at h
        omega
      have htop : L.subgroupOf (L ⊔ TG) = ⊤ := Subgroup.index_eq_one.mp hrel
      have hmap := Subgroup.map_subgroupOf_eq_of_le (le_sup_left : L ≤ L ⊔ TG)
      rw [htop, Subgroup.map_top, Subgroup.range_subtype] at hmap
      exact hTGnotle (by rw [← hmap]; exact le_sup_right)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd h hne2
  have hXLS : ρ.range = L.map ρ ⊔ TG.map ρ := by
    rw [← Subgroup.map_top ρ, ← hsup, Subgroup.map_sup]
  obtain ⟨z0, hz0mem, -, -, hz01, hz0c, hdi⟩ := M22Row.exists_center_gen (V := V) hρ.1 hM
  have hz0center : (⟨z0, hz0mem⟩ : ↥(L.map ρ)) ∈ Subgroup.center ↥(L.map ρ) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hz0c y.1 y.2)
  have hρg_not_mem : ρ g ∉ L.map ρ := by
    intro h
    obtain ⟨l, hl, hl'⟩ := Subgroup.mem_map.mp h
    exact hgL (by rw [← hinjρ hl']; exact hl)
  have hsz : ρ g * z0 * (ρ g)⁻¹ ≠ z0 := by
    have h1 : ρ g * z0 * (ρ g)⁻¹ = z0⁻¹ :=
      (hdi (ρ g) (range_le_normalizer hF ⟨g, rfl⟩)).resolve_left hρg_not_mem
    exact fun h => hz01 (h.symm.trans h1)
  have hmain := H12Pf.stmtH12_1HatM22_holds (W := V) hρ.1 (ρ.range) (L.map ρ) (TG.map ρ)
    (Subgroup.map_le_range ρ L) (range_le_normalizer hF)
    (centralizer_inf_range_le hF hinjρ) hM
    (isSylowTwoOf_map hinjρ hTG) hXLS
    ⟨ρ g, Subgroup.mem_map.mpr ⟨g, hgTG, rfl⟩, ⟨⟨z0, hz0mem⟩, hz0center, hsz⟩⟩
  exact hmain.1

theorem rk_fixV_sylow
    (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) (hF : CFSG.generalizedFitting G = L)
    (hρ : IsFaithIrr12 (ρ.comp L.subtype)) (hlt : L < ⊤) {TG : Subgroup G}
    (hTG : IsSylowIn 2 TG ⊤) : rk ↥(fixV (TG.map ρ)) = 1 := by
  rw [show rk ↥(fixV (TG.map ρ)) = padicValNat 2 (Nat.card ↥(fixV (TG.map ρ))) from rfl,
    card_fixV_sylow hL hF hρ hlt hTG]
  norm_num

end CFSG.Quasithin.AppendixH.H12
