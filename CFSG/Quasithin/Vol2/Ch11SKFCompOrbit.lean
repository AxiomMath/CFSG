module

public import CFSG.Quasithin.Vol2.Ch11SKFCompA
public import CFSG.Quasithin.Vol2.Ch11SKFIto
public import CFSG.Quasithin.Vol2.Ch11SecS12ZH
public import CFSG.Quasithin.Vol2.Ch11SecS12ZM

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.KF

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_facts {J : Subgroup G} (n : G) {x y : G} (hx : x ∈ J) (hy : y ∈ J)
    (hxy : x * y ≠ y * x) {p : ℕ} (hxp : x ^ p = 1) :
    n * x * n⁻¹ ∈ J.map (MulAut.conj n).toMonoidHom ∧
      n * y * n⁻¹ ∈ J.map (MulAut.conj n).toMonoidHom ∧
      (n * x * n⁻¹) * (n * y * n⁻¹) ≠ (n * y * n⁻¹) * (n * x * n⁻¹) ∧ (n * x * n⁻¹) ^ p = 1 := by
  refine ⟨⟨x, hx, by simp⟩, ⟨y, hy, by simp⟩, fun h => hxy ?_, ?_⟩
  · have h' : n * (x * y) * n⁻¹ = n * (y * x) * n⁻¹ := by
      calc n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
        _ = (n * y * n⁻¹) * (n * x * n⁻¹) := h
        _ = n * (y * x) * n⁻¹ := by group
    simpa using h'
  · rw [conj_pow, hxp, mul_one, mul_inv_cancel]

theorem false_of_four_components (he : CFSG.Assembly.evenRank G ≤ 2) {H J : Subgroup G}
    (hJ : CFSG.GorensteinWalter.IsComponentOf J H) {n₂ n₃ n₄ : G} (hn₂ : n₂ ∈ H)
    (hn₃ : n₃ ∈ H) (hn₄ : n₄ ∈ H) (h12 : J ≠ J.map (MulAut.conj n₂).toMonoidHom)
    (h13 : J ≠ J.map (MulAut.conj n₃).toMonoidHom) (h14 : J ≠ J.map (MulAut.conj n₄).toMonoidHom)
    (h23 : J.map (MulAut.conj n₂).toMonoidHom ≠ J.map (MulAut.conj n₃).toMonoidHom)
    (h24 : J.map (MulAut.conj n₂).toMonoidHom ≠ J.map (MulAut.conj n₄).toMonoidHom)
    (h34 : J.map (MulAut.conj n₃).toMonoidHom ≠ J.map (MulAut.conj n₄).toMonoidHom) : False := by
  have hK₂ := isComponentOf_map_conj hJ hn₂
  have hK₃ := isComponentOf_map_conj hJ hn₃
  have hK₄ := isComponentOf_map_conj hJ hn₄
  set K₂ := J.map (MulAut.conj n₂).toMonoidHom with hK₂def
  set K₃ := J.map (MulAut.conj n₃).toMonoidHom with hK₃def
  set K₄ := J.map (MulAut.conj n₄).toMonoidHom with hK₄def
  have hle : ∀ {A B : Subgroup G}, CFSG.GorensteinWalter.IsComponentOf A H →
      CFSG.GorensteinWalter.IsComponentOf B H → A ≠ B →
      A ≤ Subgroup.centralizer (B : Set G) := fun hA hB hAB a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (mul_comm_of_ne hA hB hAB ha hb).symm
  obtain ⟨hnt, hcomm, -⟩ := hJ.2.2
  have : Nontrivial ↥J := hnt
  have : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card_of_gwQuasisimple hJ.2.2)
  obtain ⟨p, hp, hp2, hpJ⟩ := exists_odd_prime_dvd_card (Q := ↥J)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxp, hxZ⟩ := exists_pow_eq_one_not_mem_center hp2 hpJ
  obtain ⟨y, hxy⟩ : ∃ y : ↥J, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hxZ (Subgroup.mem_center_iff.mpr fun g => (h g).symm)
  have hxy' : (x : G) * y ≠ y * x := fun h => hxy (Subtype.ext h)
  have hxp' : (x : G) ^ p = 1 := by rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one]
  obtain ⟨hx₂, hy₂, hxy₂, hp₂⟩ := conj_facts n₂ x.2 y.2 hxy' hxp'
  obtain ⟨hx₃, hy₃, hxy₃, hp₃⟩ := conj_facts n₃ x.2 y.2 hxy' hxp'
  obtain ⟨hx₄, hy₄, hxy₄, hp₄⟩ := conj_facts n₄ x.2 y.2 hxy' hxp'
  set x₂ := n₂ * (x : G) * n₂⁻¹
  set x₃ := n₃ * (x : G) * n₃⁻¹
  set x₄ := n₄ * (x : G) * n₄⁻¹
  set E₁ := Subgroup.zpowers x₂ with hE₁
  set E₂ := E₁ ⊔ Subgroup.zpowers x₃ with hE₂
  set E₃ := E₂ ⊔ Subgroup.zpowers x₄ with hE₃
  have hE₁K : E₁ ≤ K₂ := Subgroup.zpowers_le.mpr hx₂
  have hE₂C : E₂ ≤ Subgroup.centralizer (K₄ : Set G) :=
    sup_le (hE₁K.trans (hle hK₂ hK₄ h24)) ((Subgroup.zpowers_le.mpr hx₃).trans (hle hK₃ hK₄ h34))
  have hE₁el := C11AmS.S12.isElemAbelian_zpowers hp₂
  have hE₂el : CFSG.Open.IsElemAbelian p E₂ :=
    C11AmS.S12.isElemAbelian_sup hE₁el (C11AmS.S12.isElemAbelian_zpowers hp₃) fun a ha b hb =>
      mul_comm_of_ne hK₂ hK₃ h23 (hE₁K ha) ((Subgroup.zpowers_le.mpr hx₃) hb)
  have hE₃el : CFSG.Open.IsElemAbelian p E₃ :=
    C11AmS.S12.isElemAbelian_sup hE₂el (C11AmS.S12.isElemAbelian_zpowers hp₄) fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hE₂C ha) b ((Subgroup.zpowers_le.mpr hx₄) hb)).symm
  have hpg : ∀ {E : Subgroup G}, CFSG.Open.IsElemAbelian p E → IsPGroup p E := fun hE g =>
    ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hx₂1 : x₂ ≠ 1 := fun h => hxy₂ (by rw [h, one_mul, mul_one])
  have hE₁card : Nat.card E₁ = p := by
    rw [hE₁, Nat.card_zpowers, orderOf_eq_prime hp₂ hx₂1]
  have hE₁₂ : E₁ ≠ E₂ := fun h => by
    have hx₃E : x₃ ∈ E₁ := h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x₃)
    exact hxy₃ (Subgroup.mem_centralizer_iff.mp (hle hK₂ hK₃ h23 (hE₁K hx₃E)) _ hy₃).symm
  have hE₂₃ : E₂ ≠ E₃ := fun h => by
    have hx₄E : x₄ ∈ E₂ := h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x₄)
    exact hxy₄ (Subgroup.mem_centralizer_iff.mp (hE₂C hx₄E) _ hy₄).symm
  have hc₂ := p_mul_card_le_of_lt (hpg hE₁el) (hpg hE₂el) le_sup_left hE₁₂
  have hc₃ := p_mul_card_le_of_lt (hpg hE₂el) (hpg hE₃el) le_sup_left hE₂₃
  obtain ⟨k, hk⟩ := (hpg hE₃el).exists_card_eq
  have hk3 : 3 ≤ k := by
    refine (Nat.pow_le_pow_iff_right hp.one_lt).1 ?_
    rw [← hk]
    calc p ^ 3 = p * (p * p) := by ring
      _ ≤ p * Nat.card E₂ := Nat.mul_le_mul_left p (hE₁card ▸ hc₂)
      _ ≤ Nat.card E₃ := hc₃
  have hJt : Subgroup.centralizer (J : Set G) ≤ Subgroup.centralizer ({(t : G)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr t.2)
  have hE₃t : E₃ ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
    refine le_trans (sup_le (sup_le ?_ ?_) ?_) hJt
    · exact hE₁K.trans (hle hK₂ hJ (Ne.symm h12))
    · exact (Subgroup.zpowers_le.mpr hx₃).trans (hle hK₃ hJ (Ne.symm h13))
    · exact (Subgroup.zpowers_le.mpr hx₄).trans (hle hK₄ hJ (Ne.symm h14))
  have hk2 := le_two_of_evenRank he (t := (t : G)) (by rw [Subgroup.orderOf_coe, ht]) hp hp2
    ⟨hE₃el.1, hE₃el.2⟩ hE₃t hk
  omega

theorem factCompOrbit_holds : FactCompOrbit := by
  intro G _ _ _ _ hqtke X₁ J _ hJ
  by_contra hlt
  push Not at hlt
  set H := Subgroup.normalizer (X₁ : Set G) with hH
  have hJS : J ∈ conjSubgroupsBy H J := ⟨1, H.one_mem, by ext; simp⟩
  have h3 : 2 < (conjSubgroupsBy H J \ {J}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hJS]
    omega
  obtain ⟨K₂, K₃, K₄, hK₂, hK₃, hK₄, h23, h24, h34⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp h3
  obtain ⟨⟨n₂, hn₂, rfl⟩, h12⟩ := hK₂
  obtain ⟨⟨n₃, hn₃, rfl⟩, h13⟩ := hK₃
  obtain ⟨⟨n₄, hn₄, rfl⟩, h14⟩ := hK₄
  exact false_of_four_components hqtke.2.2 hJ hn₂ hn₃ hn₄ (fun h => h12 h.symm)
    (fun h => h13 h.symm) (fun h => h14 h.symm) h23 h24 h34

end CFSG.Quasithin.Vol2.Ch11.SecS.KF
