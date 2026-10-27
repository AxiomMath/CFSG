module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {Z₁ : Subgroup G}

omit [Finite G] in
theorem tildeOf_le_normalizer_tildeOf {X Y : Subgroup G}
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    tildeOf Z₁ X ≤ Subgroup.normalizer (tildeOf Z₁ Y : Set (SecQuot
      (Subgroup.normalizer (Z₁ : Set G)) Z₁)) := by
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  exact secMk_mem_normalizer_secImg (hXY hx)

theorem isDiagramNontrivial_tildeOf {H K T : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (Z₁ : Set G)) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hT : IsSylowTwoOf T H) (hZT : Z₁ ≤ T)
    (hd : E2.IsDiagramNontrivial T K (T ⊓ K)) :
    E2.IsDiagramNontrivial (tildeOf Z₁ T) (tildeOf Z₁ K) (tildeOf Z₁ T ⊓ tildeOf Z₁ K) := by
  intro P' hP' hBP' hTP'
  have hKN : K ≤ Subgroup.normalizer (Z₁ : Set G) := hKH.trans hHN
  have hTN : T ≤ Subgroup.normalizer (Z₁ : Set G) := hT.1.trans hHN
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.1.trans hHK
  have hS : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hT hKH hHK
  have hinf : tildeOf Z₁ (T ⊓ K) = tildeOf Z₁ T ⊓ tildeOf Z₁ K := tildeOf_inf hZT
  have hS' : IsSylowTwoOf (tildeOf Z₁ T ⊓ tildeOf Z₁ K) (tildeOf Z₁ K) :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_secImg hT hHN hZT) (secImg_mono hKH)
      (tildeOf_le_normalizer_tildeOf hHK)
  set P : Subgroup G := ((P'.comap (tmk Z₁)).map (Subgroup.normalizer (Z₁ : Set G)).subtype) ⊓ K
    with hPdef
  have hmemP : ∀ x : ↥(Subgroup.normalizer (Z₁ : Set G)), (x : G) ∈ K → tmk Z₁ x ∈ P' →
      (x : G) ∈ P := fun x hxK hx => ⟨⟨x, hx, rfl⟩, hxK⟩
  have hPmem : ∀ x : ↥(Subgroup.normalizer (Z₁ : Set G)), (x : G) ∈ P → tmk Z₁ x ∈ P' := by
    rintro x ⟨⟨y, hy, hyx⟩, -⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hB : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ P := by
    rintro x ⟨hxK, hxN⟩
    refine hmemP ⟨x, hKN hxK⟩ hxK (hBP' ⟨secMk_mem_secImg hxK, ?_⟩)
    rw [← hinf]
    exact secMk_mem_normalizer_secImg hxN
  have hC : T ≤ Subgroup.normalizer (P : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    have hxK : x ∈ K := hx.2
    have hxN : x ∈ Subgroup.normalizer (Z₁ : Set G) := hKN hxK
    have h1 : tmk Z₁ ⟨x, hxN⟩ ∈ P' := hPmem ⟨x, hxN⟩ hx
    have h2 : tmk Z₁ (⟨t, hTN ht⟩ * ⟨x, hxN⟩ * ⟨t, hTN ht⟩⁻¹) ∈ P' := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hTP' (secMk_mem_secImg ht)) _).mp h1
    exact hmemP (⟨t, hTN ht⟩ * ⟨x, hxN⟩ * ⟨t, hTN ht⟩⁻¹)
      ((Subgroup.mem_normalizer_iff.mp (hTK ht) x).mp hxK) h2
  have hKZ : K ⊓ Z₁ ≤ P := by
    rintro z ⟨hzK, hzZ⟩
    refine hB ⟨hzK, ?_⟩
    exact Subgroup.le_normalizer (show z ∈ T ⊓ K from ⟨hZT hzZ, hzK⟩)
  have hD : IsMaxParabolic2 K P := by
    refine ⟨⟨inf_le_right, T ⊓ K, hS, hB⟩, ?_, ?_⟩
    · intro hPK
      apply hP'.2.1
      refine le_antisymm hP'.1.1 fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
      exact hPmem x (hPK ▸ hx)
    · intro Q hQ hQK hPQ
      have hQ'par : IsParabolic2 (tildeOf Z₁ K) (tildeOf Z₁ Q) := by
        refine ⟨secImg_mono hQ.1, tildeOf Z₁ T ⊓ tildeOf Z₁ K, hS', ?_⟩
        rintro y ⟨hyK, hyN⟩
        obtain ⟨k, hk, rfl⟩ := mem_secImg.mp hyK
        refine secMk_mem_secImg (hPQ (hB ⟨hk, ?_⟩))
        apply mem_normalizer_of_forall_conj_mem'
        intro x hx
        have hxN : x ∈ Subgroup.normalizer (Z₁ : Set G) := hKN hx.2
        refine ⟨?_, K.mul_mem (K.mul_mem hk hx.2) (K.inv_mem hk)⟩
        have h1 : tmk Z₁ ⟨x, hxN⟩ ∈ tildeOf Z₁ T ⊓ tildeOf Z₁ K := by
          rw [← hinf]; exact secMk_mem_secImg hx
        have h2 := (Subgroup.mem_normalizer_iff.mp hyN _).mp h1
        rw [← map_inv, ← map_mul, ← map_mul] at h2
        exact (secMk_mem_secImg_iff hZT).mp h2.1
      have hQ'ne : tildeOf Z₁ Q ≠ tildeOf Z₁ K := by
        intro h
        apply hQK
        refine le_antisymm hQ.1 fun k hk => ?_
        have hkN := hKN hk
        have : tmk Z₁ ⟨k, hkN⟩ ∈ tildeOf Z₁ Q := h ▸ secMk_mem_secImg hk
        obtain ⟨q, hq, hqk⟩ := mem_secImg.mp this
        have hz : (q : G)⁻¹ * k ∈ Z₁ := secMk_eq_secMk_iff.mp hqk
        have hzK : (q : G)⁻¹ * k ∈ K := K.mul_mem (K.inv_mem (hQ.1 hq)) hk
        have e : k = (q : G) * ((q : G)⁻¹ * k) := by group
        rw [e]
        exact Q.mul_mem hq (hPQ (hKZ ⟨hzK, hz⟩))
      have hPQ' : P' ≤ tildeOf Z₁ Q := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := mem_secImg.mp (hP'.1.1 hy)
        exact secMk_mem_secImg (hPQ (hmemP k hk hy))
      have heq : tildeOf Z₁ Q = P' := hP'.2.2 _ hQ'par hQ'ne hPQ'
      refine le_antisymm (fun x hx => ?_) hPQ
      have hxN := hKN (hQ.1 hx)
      exact hmemP ⟨x, hxN⟩ (hQ.1 hx) (heq ▸ secMk_mem_secImg hx)
  exact hd P hD hB hC

end CFSG.Quasithin.H13
