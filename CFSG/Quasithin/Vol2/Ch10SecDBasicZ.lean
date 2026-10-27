module

public import CFSG.Quasithin.Vol2.Ch10SecDBasic
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch10StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem eq_of_card_le_two [Finite G] {X : Subgroup G} (hX : Nat.card X ≤ 2) {x y : G}
    (hx : x ∈ X) (hy : y ∈ X) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  by_contra hne
  have h3 : ({1, x, y} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hx1, Ne.symm hy1]), Set.ncard_pair hne]
  have hle : ({1, x, y} : Set G).ncard ≤ (X : Set G).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro w (rfl | rfl | rfl)
    · exact X.one_mem
    · exact hx
    · exact hy
  have hX' : (X : Set G).ncard = Nat.card X := (Nat.card_coe_set_eq _).symm
  omega

variable {T L I : Subgroup G}

theorem inf_le_T1 : T ⊓ L ≤ T1 T L :=
  le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)

variable [Finite G]

theorem card_inf_centralizer_T1_le (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) :
    Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (T1 T L : Set G)) ≤ 2 := by
  have h2 := card_inf_centralizer_of_isSylowTwoOf h3 hc (SecA.isSylowTwoOf_inf h.fsu.maximal.1)
  rw [← h2]
  exact Subgroup.card_le_of_le (inf_le_inf_left _ (Subgroup.centralizer_le inf_le_T1))

theorem T_le_normalizer_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) : T ≤ Subgroup.normalizer (T1 T L : Set G) := by
  have : ((T1 T L).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two (SecA.index_T1 h37 h38 h)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp this

theorem mem_centralizer_L_of_conj (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : t * x * t⁻¹ ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G)) :
    x ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have htt := SecA.mul_self_mem_normalizer h37 h38 h ht htn
  have hm : t * t * l * (t * t)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htt l).mp hl
  have hlt : t * l * t⁻¹ ∈ CFSG.conjugate L t := by
    rw [SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hm
  have h1 := (Subgroup.mem_centralizer_iff.mp hx) _ hlt
  calc l * x = t⁻¹ * ((t * l * t⁻¹) * (t * x * t⁻¹)) * t := by group
    _ = t⁻¹ * ((t * x * t⁻¹) * (t * l * t⁻¹)) * t := by rw [h1]
    _ = x * l := by group

theorem V1_inf_V2 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ = ⊥ := by
  obtain ⟨_, -, -, hall, -⟩ := h.three
  have hUC := (hall t ht htn).2.2
  rw [eq_bot_iff]
  intro x ⟨hx1, hx2⟩
  have hx2' : x ∈ CFSG.conjugate ⁅fsuVM T L I, L⁆ t := by
    rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
    exact hx2
  rw [SecA.mem_conjugate_iff] at hx2'
  replace hx2 := hx2'
  have hxL := mem_centralizer_L_of_conj h37 h38 h ht htn (hUC hx2)
  have hxLt := hUC hx1
  have hxL0 : x ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    have h1 : Subgroup.zpowers x ≤ Subgroup.centralizer (fsuL0 T L : Set G) := by
      rw [Subgroup.le_centralizer_iff, SecA.fsuL0_eq_sup h37 h38 h ht htn]
      exact sup_le (Subgroup.le_centralizer_iff.mp ((Subgroup.zpowers_le).mpr hxL))
        (Subgroup.le_centralizer_iff.mp ((Subgroup.zpowers_le).mpr hxLt))
    exact h1 (Subgroup.mem_zpowers x)
  have : x ∈ fsuCVM T L I := ⟨V1_le_V hx1, hxL0⟩
  rwa [hc] at this

theorem conj_mem_centralizer_T1 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) {v : G}
    (hv : v ∈ Subgroup.centralizer (T1 T L : Set G)) :
    t * v * t⁻¹ ∈ Subgroup.centralizer (T1 T L : Set G) :=
  conj_mem_centralizer (T_le_normalizer_T1 h37 h38 h ht) hv

theorem conj_v2 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) : t * v₂ * t⁻¹ = v₁ := by
  obtain ⟨ht, -, hv1, hv11, hv2, hv21⟩ := hd
  have hmem : t * v₂ * t⁻¹ ∈ fsuUL T L I := by
    have h1 : v₂ ∈ CFSG.conjugate ⁅fsuVM T L I, L⁆ t := by
      rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)]
      exact hv2.1
    exact SecA.mem_conjugate_iff.mp h1
  have hne : t * v₂ * t⁻¹ ≠ 1 := fun h1 => hv21 (by
    calc v₂ = t⁻¹ * (t * v₂ * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group)
  exact eq_of_card_le_two (card_inf_centralizer_T1_le h h3 hc)
    ⟨hmem, conj_mem_centralizer_T1 h37 h38 h ht hv2.2⟩ hv1 hne hv11

theorem conj_v1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) : t * v₁ * t⁻¹ = v₂ := by
  have h1 := conj_v2 h37 h38 h h3 hc hd
  obtain ⟨ht, htn, -, -, hv2, -⟩ := hd
  have htt : t * t ∈ T1 T L := ⟨T.mul_mem ht ht, SecA.mul_self_mem_normalizer h37 h38 h ht htn⟩
  have h2 := (Subgroup.mem_centralizer_iff.mp hv2.2) _ htt
  rw [← h1]
  calc t * (t * v₂ * t⁻¹) * t⁻¹ = (t * t) * v₂ * (t * t)⁻¹ := by group
    _ = v₂ * (t * t) * (t * t)⁻¹ := by rw [h2]
    _ = v₂ := by group

theorem T_le_centralizer_z (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) : T ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) := by
  have hv1t := conj_v1 h37 h38 h h3 hc hd
  have hv2t := conj_v2 h37 h38 h h3 hc hd
  obtain ⟨ht, htn, hv1, -, hv2, -⟩ := hd
  have hV1 : v₁ ∈ fsuVM T L I := V1_le_V hv1.1
  have hV2 : v₂ ∈ fsuVM T L I :=
    commutator_le_left_of_le_normalizer ((SecA.conjugate_le_fsuL0 ht).trans
      (SecA.fsuL0_le_normalizer_fsuVM T L I)) hv2.1
  obtain ⟨hcomm, -⟩ := h.three
  have hv12 : v₁ * v₂ = v₂ * v₁ := by
    have := hcomm.is_comm.comm ⟨v₁, hV1⟩ ⟨v₂, hV2⟩
    exact congrArg Subtype.val this
  have hT1 : ∀ s ∈ T1 T L, s * (v₁ * v₂) = (v₁ * v₂) * s := by
    intro s hs
    have e1 := (Subgroup.mem_centralizer_iff.mp hv1.2) s hs
    have e2 := (Subgroup.mem_centralizer_iff.mp hv2.2) s hs
    calc s * (v₁ * v₂) = (s * v₁) * v₂ := by group
      _ = v₁ * (s * v₂) := by rw [e1]; group
      _ = v₁ * v₂ * s := by rw [e2]; group
  have htz : t * (v₁ * v₂) = (v₁ * v₂) * t := by
    have e : t * (v₁ * v₂) * t⁻¹ = v₁ * v₂ := by
      calc t * (v₁ * v₂) * t⁻¹ = (t * v₁ * t⁻¹) * (t * v₂ * t⁻¹) := by group
        _ = v₂ * v₁ := by rw [hv1t, hv2t]
        _ = v₁ * v₂ := hv12.symm
    calc t * (v₁ * v₂) = t * (v₁ * v₂) * t⁻¹ * t := by group
      _ = v₁ * v₂ * t := by rw [e]
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxn : x ∈ Subgroup.normalizer (L : Set G)
  · exact hT1 x ⟨hx, hxn⟩
  · have hxt : x * t⁻¹ ∈ T1 T L :=
      ⟨T.mul_mem hx (T.inv_mem ht), SecA.mul_inv_mem_normalizer h37 h38 h ht htn hx hxn⟩
    have e1 := hT1 _ hxt
    refine (?_ : v₁ * v₂ * x = x * (v₁ * v₂)).symm
    calc v₁ * v₂ * x = v₁ * v₂ * (x * t⁻¹) * t := by group
      _ = x * t⁻¹ * (v₁ * v₂) * t := by rw [← e1]
      _ = x * t⁻¹ * (t * (v₁ * v₂)) := by rw [mul_assoc (x * t⁻¹), htz]
      _ = x * (v₁ * v₂) := by group

theorem z_ne_one (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) : v₁ * v₂ ≠ 1 := by
  obtain ⟨ht, htn, hv1, -, hv2, hv21⟩ := hd
  intro h1
  have hv : v₂ = v₁⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hmem : v₂ ∈ fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    ⟨hv ▸ (fsuUL T L I).inv_mem hv1.1, hv2.1⟩
  rw [V1_inf_V2 h37 h38 h hc ht htn, Subgroup.mem_bot] at hmem
  exact hv21 hmem

end CFSG.Quasithin.Vol2.Ch10.SecD
