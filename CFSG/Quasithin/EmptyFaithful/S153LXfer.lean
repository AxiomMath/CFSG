module

public import CFSG.Quasithin.EmptyFaithful.S153LStar
public import CFSG.Quasithin.EmptyFaithful.S153LNs
public import CFSG.Quasithin.Background.S1549CN3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.S1549C
  CFSG.Quasithin.S1549D
open scoped commutatorElement

namespace S153L

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem preStar_conj_mem (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))}
    (hAn : starOfSub h H ≤ Subgroup.normalizer (A : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))))
    {y : G} (hyH : y ∈ H) {x : G} (hx : x ∈ preStar h A) : y * x * y⁻¹ ∈ preStar h A := by
  obtain ⟨hxH, hxA⟩ := (mem_preStar_iff h).mp hx
  have hmem : y * x * y⁻¹ ∈ H := H.mul_mem (H.mul_mem hyH hxH) (H.inv_mem hyH)
  refine (mem_preStar_iff h).mpr ⟨hmem, ?_⟩
  have e : (⟨y * x * y⁻¹, hmem⟩ : ↥H) = ⟨y, hyH⟩ * ⟨x, hxH⟩ * (⟨y, hyH⟩ : ↥H)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  have hy' : starHom h ⟨y, hyH⟩ ∈ starOfSub h H := (mem_starOfSub h).mpr ⟨⟨y, hyH⟩, hyH, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hAn hy') _).mp hxA

theorem normalizes_of_star (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hA : A ≤ starOfSub h H)
    (hAn : starOfSub h H ≤ Subgroup.normalizer (A : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))))
    {K : Subgroup G} (hK : K ∈ cComp (preStar h A)) {y : G} (hyH : y ∈ H)
    (hyK : starHom h ⟨y, hyH⟩ ∈
      Subgroup.normalizer (starOfSub h K : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H))))) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  have hyJ : ∀ x, x ∈ preStar h A ↔ y * x * y⁻¹ ∈ preStar h A := fun x =>
    ⟨preStar_conj_mem h hAn hyH, fun hx => by
      simpa [mul_assoc] using preStar_conj_mem h hAn (H.inv_mem hyH) hx⟩
  have hK' : K.map (MulAut.conj y).toMonoidHom ∈ cComp (preStar h A) := comp_conj_mem_cComp hyJ hK
  have hKH : K ≤ H := (le_of_mem_cComp hK).trans (preStar_le h A)
  have heq : starOfSub h (K.map (MulAut.conj y).toMonoidHom) = starOfSub h K := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hxK', rfl⟩ := (mem_starOfSub h).mp hz
      obtain ⟨k, hk, hkx⟩ := hxK'
      have hkH : k ∈ H := hKH hk
      have hx : x = ⟨y, hyH⟩ * ⟨k, hkH⟩ * (⟨y, hyH⟩ : ↥H)⁻¹ :=
        Subtype.ext (by simp [← hkx, MulAut.conj_apply])
      rw [hx, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hyK _).mp ((mem_starOfSub h).mpr ⟨⟨k, hkH⟩, hk, rfl⟩)
    · intro hz
      set g := starHom h ⟨y, hyH⟩ with hg
      have hz' : g⁻¹ * z * g⁻¹⁻¹ ∈ starOfSub h K := by
        have := (Subgroup.mem_normalizer_iff.mp hyK (g⁻¹ * z * g⁻¹⁻¹)).mpr
        refine this ?_
        simpa [mul_assoc] using hz
      obtain ⟨k, hk, hkz⟩ := (mem_starOfSub h).mp hz'
      refine (mem_starOfSub h).mpr ⟨⟨y, hyH⟩ * k * (⟨y, hyH⟩ : ↥H)⁻¹, ?_, ?_⟩
      · exact ⟨k, hk, by simp [MulAut.conj_apply]⟩
      · rw [map_mul, map_mul, map_inv, hkz]
        simp [hg, mul_assoc]
  have hmap := starOfSub_injOn h hA hK' hK heq
  exact comp_mem_normalizer_of_map_eq hmap

theorem eq_commutator_of_star (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} (hA : A ≤ starOfSub h H)
    (hAn : starOfSub h H ≤ Subgroup.normalizer (A : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))))
    {K Y : Subgroup G} (hK : K ∈ cComp (preStar h A)) (hYH : Y ≤ H)
    (hYn : starOfSub h Y ≤
      Subgroup.normalizer (starOfSub h K : Set (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))))
    (hcomm : ⁅starOfSub h K, starOfSub h Y⁆ = starOfSub h K) : K = ⁅K, Y⁆ := by
  have hKH : K ≤ H := (le_of_mem_cComp hK).trans (preStar_le h A)
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    normalizes_of_star h hA hAn hK (hYH hy)
      (hYn ((mem_starOfSub h).mpr ⟨⟨y, hYH hy⟩, hy, rfl⟩))
  have hle1 : ⁅K, Y⁆ ≤ K := Subgroup.commutator_le.mpr fun k hk y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (hYK hy) k⁻¹).mp (K.inv_mem hk)
    rw [commutatorElement_def]
    have e : k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) := by group
    rw [e]
    exact K.mul_mem hk this
  have hKX : K ≤ Subgroup.normalizer ((⁅K, Y⁆ : Subgroup G) : Set G) := A3.le_normalizer_commutator_left K Y
  have hstar : starOfSub h K ≤ starOfSub h ⁅K, Y⁆ := by
    calc starOfSub h K = ⁅starOfSub h K, starOfSub h Y⁆ := hcomm.symm
      _ ≤ starOfSub h ⁅K, Y⁆ := by
        refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
        obtain ⟨k, hk, rfl⟩ := (mem_starOfSub h).mp ha
        obtain ⟨y, hy, rfl⟩ := (mem_starOfSub h).mp hb
        refine (mem_starOfSub h).mpr ⟨k * y * k⁻¹ * y⁻¹, ?_, by simp [commutatorElement_def]⟩
        exact Subgroup.commutator_mem_commutator hk hy
  have hQ : IsPGroup 2 ↥(K ⊓ pCoreOf 2 H) := (pCoreOf_isPGroup 2 H).to_le inf_le_right
  have hLKQ : K ≤ ⁅K, Y⁆ ⊔ (K ⊓ pCoreOf 2 H) := by
    intro l hl
    obtain ⟨x, hxc, hxl⟩ := (mem_starOfSub h).mp (hstar ((mem_starOfSub h).mpr ⟨⟨l, hKH hl⟩, hl, rfl⟩))
    have hxK : (x : G) ∈ K := hle1 hxc
    have hq : (x : G)⁻¹ * l ∈ pCoreOf 2 H := by
      have h1 : starHom h (x⁻¹ * ⟨l, hKH hl⟩) = 1 := by
        rw [map_mul, map_inv, hxl, inv_mul_cancel]
      exact (starHom_eq_one_iff h _).mp h1
    have e : l = (x : G) * ((x : G)⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hxc ⟨K.mul_mem (K.inv_mem hxK) hl, hq⟩
  exact le_antisymm
    (claimN_le_of_perfect_of_le_sup (perfect_of_mem_cComp hK) hQ (inf_le_left.trans hKX) hLKQ) hle1

end S153L

end CFSG.Quasithin
