module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CaseTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

private theorem odd_eq_four_mul_add_one_or_three {q : ℕ} (hq : Odd q) :
    ∃ j : ℕ, q = 4 * j + 1 ∨ q = 4 * j + 3 := by
  obtain ⟨k, hk⟩ := hq
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨j, Or.inl (by omega)⟩
  · exact ⟨j, Or.inr (by omega)⟩

private theorem inner_involution_centralizer_aux {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t : PGL2 K}
    (ht : t * t = 1) (ht1 : t ≠ 1) (htJ : t ∈ pslRange K) :
    ∃ (Z : Subgroup (PGL2 K)) (w : PGL2 K), IsCyclic Z ∧
      Nat.card Z = 2 * Nat.card K - outerTorusOrder (Nat.card K) ∧ t ∈ Z ∧ w ∉ Z ∧
      w * w = 1 ∧ (∀ x ∈ Z, w * x * w⁻¹ = x⁻¹) ∧
      centralizer ({t} : Set (PGL2 K)) = Z ⊔ zpowers w ∧ ¬ Z ≤ pslRange K := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hqodd := odd_card_of_isOddPrimePower hK
  have hJ2 := pslRange_index_eq_two hK
  have hJn : (pslRange K).Normal := pslRange_normal hK hcard
  have hcomm : commutator (PGL2 K) = pslRange K :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  obtain ⟨U, s, w, hUc, hUcard, hsU, hss, hs1, hwU, hww, hwinv, hC, hUJ⟩ :
      ∃ (U : Subgroup (PGL2 K)) (s w : PGL2 K), IsCyclic U ∧
        Nat.card U = 2 * Nat.card K - outerTorusOrder (Nat.card K) ∧ s ∈ U ∧ s * s = 1 ∧
        s ≠ 1 ∧ w ∉ U ∧ w * w = 1 ∧ (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
        centralizer ({s} : Set (PGL2 K)) = U ⊔ zpowers w ∧ ¬ U ≤ pslRange K := by
    by_cases h : Nat.card K % 4 = 1
    · obtain ⟨U, s, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        pgl2_split_torus_centralizer_data K hqodd
      refine ⟨U, s, w, h1, ?_, h3, h4, h5, h6, h7, h8, h9, h10 hqodd⟩
      rw [h2]
      unfold outerTorusOrder
      rw [if_pos h]
      have hpos : 0 < Nat.card K := Nat.card_pos
      omega
    · obtain ⟨U, s, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        pgl2_nonsplit_torus_centralizer_data K hqodd
      refine ⟨U, s, w, h1, ?_, h3, h4, h5, h6, h7, h8, h9, h10 hqodd⟩
      rw [h2]
      unfold outerTorusOrder
      rw [if_neg h]
      have hpos : 0 < Nat.card K := Nat.card_pos
      omega
  have hUJc : ¬ U ≤ commutator (PGL2 K) := by rwa [hcomm]
  have hJindex : (commutator (PGL2 K)).index = 2 := by rw [hcomm]; exact hJ2
  have hsJ : s ∈ pslRange K := by
    rw [← hcomm]
    obtain ⟨j, hj | hj⟩ := odd_eq_four_mul_add_one_or_three hqodd
    · have hU4 : Nat.card U = 4 * j := by
        rw [hUcard, hj]
        unfold outerTorusOrder
        rw [if_pos (by omega : (4 * j + 1) % 4 = 1)]
        omega
      refine pgl2_torus_involution_mem_commutator hJindex U hUc hsU hss hs1
        (m := 2 * j) ?_ ⟨j, ?_⟩ hUJc
      · omega
      · omega
    · have hU4 : Nat.card U = 4 * j + 4 := by
        rw [hUcard, hj]
        unfold outerTorusOrder
        rw [if_neg (by omega : ¬ (4 * j + 3) % 4 = 1)]
        omega
      refine pgl2_torus_involution_mem_commutator hJindex U hUc hsU hss hs1
        (m := 2 * (j + 1)) ?_ ⟨j + 1, ?_⟩ hUJc
      · omega
      · omega
  have hsI : BenderSuzuki.PFAppendixIII.IsInvolution s :=
    ⟨hs1, by rw [pow_two]; exact hss⟩
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution t :=
    ⟨ht1, by rw [pow_two]; exact ht⟩
  have hsJc : s ∈ commutator (PGL2 K) := hcomm.symm ▸ hsJ
  have htJc : t ∈ commutator (PGL2 K) := hcomm.symm ▸ htJ
  obtain ⟨c, -, hc⟩ :=
    pgl2_inner_involutions_conjugate hK hcard (x := s) (y := t) hsJc hsI htJc htI
  let φ : PGL2 K →* PGL2 K := (MulAut.conj c).toMonoidHom
  have hφinj : Function.Injective φ := (MulAut.conj c).injective
  have hφ : ∀ x, φ x = c * x * c⁻¹ := fun x => rfl
  refine ⟨U.map φ, c * w * c⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (U.equivMapOfInjective φ hφinj)).mp hUc
  · rw [← hUcard]
    exact (Nat.card_congr (U.equivMapOfInjective φ hφinj).toEquiv).symm
  · exact ⟨s, hsU, by rw [hφ, hc]⟩
  · rintro ⟨x, hx, hxw⟩
    rw [hφ] at hxw
    have hx' : x = w := by
      have := congrArg (fun y => c⁻¹ * y * c) hxw
      simpa [mul_assoc] using this
    exact hwU (hx' ▸ hx)
  · calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hww]; group
  · rintro x ⟨y, hy, rfl⟩
    rw [hφ]
    calc c * w * c⁻¹ * (c * y * c⁻¹) * (c * w * c⁻¹)⁻¹ = c * (w * y * w⁻¹) * c⁻¹ := by group
      _ = c * y⁻¹ * c⁻¹ := by rw [hwinv y hy]
      _ = (c * y * c⁻¹)⁻¹ := by group
  · rw [← hc, centralizer_conj, hC, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  ·
    intro hZ
    apply hUJ
    intro u hu
    have hmem : φ u ∈ pslRange K := hZ ⟨u, hu, rfl⟩
    have h2 := hJn.conj_mem (c * u * c⁻¹) hmem c⁻¹
    rw [inv_inv] at h2
    have h3 : c⁻¹ * (c * u * c⁻¹) * c = u := by group
    rwa [h3] at h2

theorem inner_involution_centralizer {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t : PGL2 K}
    (ht : t * t = 1) (ht1 : t ≠ 1) (htJ : t ∈ pslRange K) :
    ∃ (Z : Subgroup (PGL2 K)) (w : PGL2 K), IsCyclic Z ∧
      Nat.card Z = 2 * Nat.card K - outerTorusOrder (Nat.card K) ∧ t ∈ Z ∧ w ∉ Z ∧
      w * w = 1 ∧ (∀ x ∈ Z, w * x * w⁻¹ = x⁻¹) ∧
      centralizer ({t} : Set (PGL2 K)) = Z ⊔ zpowers w := by
  obtain ⟨Z, w, hZc, hZcard, htZ, hwZ, hww, hwinv, hC, -⟩ :=
    inner_involution_centralizer_aux hK hcard ht ht1 htJ
  exact ⟨Z, w, hZc, hZcard, htZ, hwZ, hww, hwinv, hC⟩

theorem exists_inverted_of_inner_outer {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t β : PGL2 K}
    (ht : t * t = 1) (ht1 : t ≠ 1) (htJ : t ∈ pslRange K) (hβ : β * β = 1)
    (hβJ : β ∉ pslRange K) (hcomm : t * β = β * t) :
    ∃ z : PGL2 K, z * t = t * z ∧ β * z * β⁻¹ = z⁻¹ ∧
      orderOf z = 2 * Nat.card K - outerTorusOrder (Nat.card K) := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨Z, w, hZc, hZcard, htZ, -, hww, hwinv, hC⟩ :=
    inner_involution_centralizer hK hcard ht ht1 htJ
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hZc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hβ1 : β ≠ 1 := fun h => hβJ (h ▸ (pslRange K).one_mem)
  have hβC : β ∈ centralizer ({t} : Set (PGL2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hβsup : β ∈ Z ⊔ Subgroup.zpowers w := hC ▸ hβC
  have hβZ : β ∉ Z := by
    intro hβmem
    have hβeq : β = t := by
      have h1 : (⟨β, hβmem⟩ : Z) = ⟨t, htZ⟩ :=
        eq_of_sq_eq_one_of_isCyclic (Subtype.ext (by rw [pow_two]; exact hβ))
          (Subtype.ext (by rw [pow_two]; exact ht))
          (fun h => hβ1 (congrArg Subtype.val h))
          (fun h => ht1 (congrArg Subtype.val h))
      exact congrArg Subtype.val h1
    exact hβJ (hβeq ▸ htJ)
  obtain ⟨-, hβinv⟩ := inverts_of_mem_sup_not_mem hZcomm hww hwinv hβsup hβZ
  obtain ⟨z, hzord⟩ := hZc.exists_ofOrder_eq_natCard
  refine ⟨(z : PGL2 K), ?_, hβinv (z : PGL2 K) z.2, ?_⟩
  · exact congrArg Subtype.val (hZc.commGroup.mul_comm z ⟨t, htZ⟩)
  · rw [Subgroup.orderOf_coe, hzord, hZcard]

theorem exists_inverted_of_inner {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t : PGL2 K}
    (ht : t * t = 1) (ht1 : t ≠ 1) (htJ : t ∈ pslRange K) :
    ∃ τ ∈ pslRange K, orderOf τ = outerTorusOrder (Nat.card K) / 2 ∧ t * τ * t⁻¹ = τ⁻¹ := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨Z, w, hZc, hZcard, htZ, -, hww, hwinv, hC, hZJ⟩ :=
    inner_involution_centralizer_aux hK hcard ht ht1 htJ
  have hwC : w ∈ centralizer ({t} : Set (PGL2 K)) := by
    rw [hC]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwt : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
  have hex : ∃ β : PGL2 K, β * β = 1 ∧ β ∉ pslRange K ∧ t * β = β * t := by
    by_cases hwJ : w ∈ pslRange K
    · obtain ⟨z₀, hz₀Z, hz₀J⟩ := SetLike.not_le_iff_exists.mp hZJ
      have hz₀t : z₀ * t = t * z₀ :=
        congrArg Subtype.val (hZc.commGroup.mul_comm ⟨z₀, hz₀Z⟩ ⟨t, htZ⟩)
      refine ⟨z₀ * w, ?_, ?_, ?_⟩
      · calc z₀ * w * (z₀ * w) = z₀ * (w * z₀ * w⁻¹) * (w * w) := by group
          _ = z₀ * z₀⁻¹ * 1 := by rw [hwinv z₀ hz₀Z, hww]
          _ = 1 := by group
      · intro hmem
        apply hz₀J
        have h1 : (z₀ * w) * w⁻¹ = z₀ := by group
        rw [← h1]
        exact (pslRange K).mul_mem hmem ((pslRange K).inv_mem hwJ)
      · calc t * (z₀ * w) = (t * z₀) * w := by group
          _ = (z₀ * t) * w := by rw [← hz₀t]
          _ = z₀ * (t * w) := by group
          _ = z₀ * (w * t) := by rw [hwt]
          _ = z₀ * w * t := by group
    · exact ⟨w, hww, hwJ, hwt.symm⟩
  obtain ⟨β, hβ2, hβJ, htβ⟩ := hex
  have htCβ : t ∈ centralizer ({β} : Set (PGL2 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htβ
  obtain ⟨U, w', hUc, hUcard, hβU, -, hw'2, hw'inv, hC'⟩ :=
    outer_involution_centralizer hK hcard (g := β) (by rw [pow_two]; exact hβ2) hβJ
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hβ1 : β ≠ 1 := fun h => hβJ (h ▸ (pslRange K).one_mem)
  have htU : t ∉ U := by
    intro htU
    have heq : t = β := by
      have h1 : (⟨t, htU⟩ : U) = ⟨β, hβU⟩ :=
        eq_of_sq_eq_one_of_isCyclic (Subtype.ext (by rw [pow_two]; exact ht))
          (Subtype.ext (by rw [pow_two]; exact hβ2))
          (fun h => ht1 (congrArg Subtype.val h))
          (fun h => hβ1 (congrArg Subtype.val h))
      exact congrArg Subtype.val h1
    exact hβJ (heq ▸ htJ)
  have htU' : t ∈ U ⊔ Subgroup.zpowers w' := hC' ▸ htCβ
  obtain ⟨-, htinv⟩ := inverts_of_mem_sup_not_mem hUcomm hw'2 hw'inv htU' htU
  obtain ⟨g, hgord⟩ := hUc.exists_ofOrder_eq_natCard
  have hgord' : orderOf ((g : PGL2 K)) = Nat.card U := by
    rw [Subgroup.orderOf_coe, hgord]
  have h2dvd : 2 ∣ orderOf ((g : PGL2 K)) := by
    rw [hgord', hUcard, Nat.dvd_iff_mod_eq_zero]
    have hm := outerTorusOrder_mod_four (odd_card_of_isOddPrimePower hK)
    omega
  refine ⟨(g : PGL2 K) ^ 2, ?_, ?_, ?_⟩
  · rw [pow_two]
    exact Subgroup.mul_self_mem_of_index_two (pslRange_index_eq_two hK) (g : PGL2 K)
  · rw [orderOf_pow_of_dvd (by norm_num) h2dvd, hgord', hUcard]
  · have h1 : t * (g : PGL2 K) * t⁻¹ = (g : PGL2 K)⁻¹ := htinv (g : PGL2 K) g.2
    calc t * (g : PGL2 K) ^ 2 * t⁻¹
        = t * ((g : PGL2 K) * (g : PGL2 K)) * t⁻¹ := by rw [pow_two]
      _ = (t * (g : PGL2 K) * t⁻¹) * (t * (g : PGL2 K) * t⁻¹) := by group
      _ = ((g : PGL2 K)⁻¹) * ((g : PGL2 K)⁻¹) := by rw [h1]
      _ = ((g : PGL2 K) ^ 2)⁻¹ := by group

private theorem outer_centralizer_le_sup_zpowers {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t g : PGL2 K}
    (htJ : t ∈ pslRange K) (htt : t * t = 1) (ht1 : t ≠ 1) (hg2 : g ^ 2 = 1)
    (hgJ : g ∉ pslRange K) (htg : t * g = g * t) (H : Subgroup (PGL2 K)) (htH : t ∈ H)
    (hP1g : ∀ x ∈ pslRange K, x * g = g * x → Odd (orderOf x) → x ∈ H) :
    Subgroup.centralizer ({g} : Set (PGL2 K)) ≤ H ⊔ Subgroup.zpowers g := by
  classical
  have hJ2 := pslRange_index_eq_two hK
  obtain ⟨U, w, hUc, hUcard, hgU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard hg2 hgJ
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUodd : ∀ x ∈ U, x ∈ pslRange K → x ∈ H := fun x hxU hxJ =>
    hP1g x hxJ (hUcomm x hxU g hgU)
      (odd_orderOf_of_mem_outer_torus hK hcard hgJ hUcard hgU hxU hxJ)
  have hUH : U ≤ H ⊔ Subgroup.zpowers g := by
    intro u hu
    by_cases huJ : u ∈ pslRange K
    · exact Subgroup.mem_sup_left (hUodd u hu huJ)
    · have hugJ : u * g ∈ pslRange K :=
        (Subgroup.mul_mem_iff_of_index_two hJ2).mpr (iff_of_false huJ hgJ)
      have hugH : u * g ∈ H := hUodd _ (U.mul_mem hu hgU) hugJ
      have hu' : u = u * g * g := by rw [mul_assoc, ← pow_two, hg2, mul_one]
      rw [hu']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hugH)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have htU : t ∉ U := by
    intro htU
    have hodd := odd_orderOf_of_mem_outer_torus hK hcard hgJ hUcard hgU htU htJ
    rw [orderOf_eq_prime (by rw [pow_two]; exact htt) ht1] at hodd
    exact absurd hodd (by decide)
  have htC : t ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr htg
  have hwN : w ∈ Subgroup.normalizer (U : Set (PGL2 K)) :=
    zpowers_le_normalizer_of_inverting hww hwinv (Subgroup.mem_zpowers w)
  have hwH : w ∈ H ⊔ Subgroup.zpowers g := by
    have h := htC
    rw [sup_comm, mem_zpowers_sup_iff hwN (by rw [pow_two]; exact hww)] at h
    obtain ⟨l, hl, rfl | hl'⟩ := h
    · exact absurd hl htU
    · have hw' : w = t * l⁻¹ := by rw [hl']; group
      rw [hw']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htH) (Subgroup.inv_mem _ (hUH hl))
  rw [hC]
  exact sup_le hUH (Subgroup.zpowers_le.mpr hwH)

private theorem eq_pslRange_of_sup_zpowers_eq_top {K : Type} [Field K] {g : PGL2 K}
    (hg2 : g ^ 2 = 1) (hgJ : g ∉ pslRange K) (H : Subgroup (PGL2 K))
    (hHJ : H ≤ pslRange K) (hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h : H ⊔ Subgroup.zpowers g = ⊤) : H = pslRange K := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hg2)
  apply le_antisymm hHJ
  intro j hj
  have hjtop : j ∈ H ⊔ Subgroup.zpowers g := h ▸ Subgroup.mem_top j
  have hgN : g ∈ Subgroup.normalizer (H : Set (PGL2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hgH x
    · intro hx
      have h1 := hgH _ hx
      rwa [hg', show g * (g * x * g) * g = (g * g) * x * (g * g) by group, ← pow_two, hg2,
        one_mul, mul_one] at h1
  rw [sup_comm, mem_zpowers_sup_iff hgN hg2] at hjtop
  obtain ⟨l, hl, rfl | rfl⟩ := hjtop
  · exact hl
  · exfalso
    apply hgJ
    have hgl : g = g * l * l⁻¹ := by group
    rw [hgl]
    exact (pslRange K).mul_mem hj ((pslRange K).inv_mem (hHJ hl))

theorem eq_pslRange_of_commute {K : Type} [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {t g : PGL2 K} (htJ : t ∈ pslRange K) (htt : t * t = 1)
    (ht1 : t ≠ 1) (hg2 : g ^ 2 = 1) (hgJ : g ∉ pslRange K) (htg : t * g = g * t)
    (H : Subgroup (PGL2 K)) (hHJ : H ≤ pslRange K) (htH : t ∈ H)
    (hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hP1g : ∀ x ∈ pslRange K, x * g = g * x → Odd (orderOf x) → x ∈ H) {x : PGL2 K}
    (hxH : x ∈ H) (hxt : x * t = t * x) (hx2 : x * x ≠ 1) : H = pslRange K := by
  classical
  have hCH := outer_centralizer_le_sup_zpowers hK hcard htJ htt ht1 hg2 hgJ htg H htH hP1g
  obtain ⟨U, w, hUc, hUcard, hgU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard hg2 hgJ
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  have htU : t ∉ U := by
    intro htUm
    have hodd := odd_orderOf_of_mem_outer_torus hK hcard hgJ hUcard hgU htUm htJ
    rw [orderOf_eq_prime (by rw [pow_two]; exact htt) ht1] at hodd
    exact absurd hodd (by decide)
  rcases outer_involution_centralizer_maximal hKcard hK hcard hg2 hgJ
    (H ⊔ Subgroup.zpowers g) hCH with h | h
  ·
    exfalso
    have hxC : x ∈ Subgroup.centralizer ({g} : Set (PGL2 K)) :=
      h ▸ Subgroup.mem_sup_left hxH
    have hxsup : x ∈ U ⊔ Subgroup.zpowers w := hC ▸ hxC
    have htC : t ∈ U ⊔ Subgroup.zpowers w := by
      rw [← hC]
      exact Subgroup.mem_centralizer_singleton_iff.mpr htg
    by_cases hxU : x ∈ U
    · obtain ⟨-, htinv⟩ := inverts_of_mem_sup_not_mem hUcomm hww hwinv htC htU
      have h1 : t * x * t⁻¹ = x := by rw [← hxt]; group
      rw [htinv x hxU] at h1
      exact hx2 (by
        calc x * x = x * x⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel x)
    · obtain ⟨hxx, -⟩ := inverts_of_mem_sup_not_mem hUcomm hww hwinv hxsup hxU
      exact hx2 hxx
  · exact eq_pslRange_of_sup_zpowers_eq_top hg2 hgJ H hHJ hgH h

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
