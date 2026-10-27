module

public import CFSG.Quasithin.EmptyFaithful.E111L2IA

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R

variable {G : Type} [Group G]

theorem relIndex_sup_eq_of_le_normalizer {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

theorem eq_one_of_mem_centralizer' {D : Subgroup G} (hD : IsSimpleGroup ↥D)
    (hnab : ∃ a b : ↥D, a * b ≠ b * a) {x : G} (hx : x ∈ D)
    (hxc : x ∈ Subgroup.centralizer (D : Set G)) : x = 1 := by
  have hZ := Vol2.Ch11.SecE3.center_eq_bot_of_simple hnab
  have hc : (⟨x, hx⟩ : ↥D) ∈ Subgroup.center ↥D :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2)
  rw [hZ, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

theorem card_innerImage {X A S : Subgroup G} (hS : IsComp X S)
    (hinn : ∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
      s⁻¹ * a ∈ Subgroup.centralizer (S : Set G)) :
    Nat.card ↥(innerImage A S) =
      (A ⊓ Subgroup.centralizer (S : Set G)).relIndex (A ⊓ Subgroup.normalizer (S : Set G)) := by
  set C := Subgroup.centralizer (S : Set G) with hC
  set V := A ⊓ Subgroup.normalizer (S : Set G) with hV
  have hNC := normalizer_le_normalizer_centralizer S
  have hI : innerImage A S ≤ Subgroup.normalizer (C : Set G) :=
    (innerImage_le_left A S).trans (Subgroup.le_normalizer.trans hNC)
  have h1 := relIndex_sup_eq_of_le_normalizer hI
  have h2 := relIndex_sup_eq_of_le_normalizer (inf_le_right.trans hNC : V ≤ _)
  rw [← sup_innerImage hinn, h2] at h1
  have h3 : (A ⊓ C).relIndex V = C.relIndex V := by
    rw [← Subgroup.inf_relIndex_right (A ⊓ C) V, ← Subgroup.inf_relIndex_right C V]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨hx.2.1, hx.1⟩, hx.2⟩⟩
  have h4 : C.relIndex (innerImage A S) = Nat.card ↥(innerImage A S) := by
    have hbot : C.subgroupOf (innerImage A S) = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot, Subgroup.disjoint_def]
      intro x hxC hxI
      exact eq_one_of_mem_centralizer hS hxI.1 hxC
    rw [Subgroup.relIndex, hbot, Subgroup.index_bot]
  rw [h3, ← h4]
  exact h1.symm

theorem innerImage_data [Finite G] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) {X T A S : Subgroup G} (hR : E111Reduced G X T)
    (hS : IsComp X S) (hSp : IsPSL 2 p 1 ↥S) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (h4 : 4 ≤ (A ⊓ Subgroup.centralizer (S : Set G)).relIndex
      (A ⊓ Subgroup.normalizer (S : Set G)))
    (hinn : ∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
      s⁻¹ * a ∈ Subgroup.centralizer (S : Set G))
    {z : G} (hzTS : z ∈ T ⊓ S) (hz2 : orderOf z = 2) (hzc : ∀ x ∈ T ⊓ S, z * x = x * z) :
    IsKleinFour ↥(innerImage A S) ∧ z ∈ innerImage A S := by
  obtain ⟨m, hm, ⟨eTS⟩⟩ := sub_dihedral hp7 hp8 hSp (isSylowIn_inf hR hS)
  obtain ⟨z₀, hz₀, hz₀2, hz₀c, hKl, hEA⟩ := CFSG.Quasithin.E22L2.dihedral_sylow_data hm eTS
  have hle := innerImage_le hR hS hAT hA
  have hsq : ∀ x ∈ innerImage A S, x * x = 1 := fun x hx => mul_self_of_mem_innerImage hS hA hx
  have hEl : IsElemAbelian 2 (innerImage A S) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => by rw [pow_two]; exact hsq x hx⟩
    have h1 := hsq _ (Subgroup.mul_mem _ x.2 y.2)
    have h2 := hsq _ x.2
    have h3 := hsq _ y.2
    simp only [Subgroup.coe_mul]
    calc (x : G) * y = ((x : G) * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = (y : G)⁻¹ * (x : G)⁻¹ := mul_inv_rev _ _
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]
  have hc4 : 4 ≤ Nat.card ↥(innerImage A S) := by rw [card_innerImage hS hinn]; exact h4
  have hK := (hEA _ hle hEl hc4).2
  refine ⟨hK, ?_⟩
  have hz₀I := hKl _ hle hK
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    norm_num at hz2
  have hz₀1 : z₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz₀2
    norm_num at hz₀2
  rwa [central_unique hm eTS hz₀ hzTS hz₀1 hz1 hz₀c hzc] at hz₀I

@[expose] noncomputable def diagInner (A S C : Subgroup G) [Fintype ↥C] (hC : DiagComm S C) :
    Subgroup G :=
  ((innerImage A S).subgroupOf S).map (diagHom S C hC)

section Diag

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C]
include h

theorem diagInner_le_diag : diagInner A S C h.diagComm ≤ diagSub S C h.diagComm :=
  Subgroup.map_le_range _ _

theorem diagInner_le_T [Finite G] : diagInner A S C h.diagComm ≤ T := by
  rintro _ ⟨x, hx, rfl⟩
  refine diagHom_mem_of h.diagComm x fun c hc => ?_
  have hxT : (x : G) ∈ T := (innerImage_le h.red h.comp h.AT h.elem hx).1
  exact T.mul_mem (T.mul_mem (h.AT (h.CA hc)) hxT) (T.inv_mem (h.AT (h.CA hc)))

theorem isKleinFour_diagInner (hK : IsKleinFour ↥(innerImage A S)) :
    IsKleinFour ↥(diagInner A S C h.diagComm) :=
  isKleinFour_of_equiv (((innerImage A S).subgroupOf S).equivMapOfInjective _
    (diagHom_injective h.diagComm h.center_trivial)).symm
    (isKleinFour_of_equiv (Subgroup.subgroupOfEquivOfLe (innerImage_le_left A S)) hK)

theorem exists_conj_diagInner (hCV : C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A)
    (hinn : ∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
      s⁻¹ * a ∈ Subgroup.centralizer (S : Set G)) {a : G} (ha : a ∈ A) :
    ∃ w ∈ diagInner A S C h.diagComm, ∀ x ∈ diagSub S C h.diagComm,
      a * x * a⁻¹ = w * x * w⁻¹ := by
  have hN : A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_comm fun x hx y hy => h.comm hx.1 (h.CA hy)
  obtain ⟨c, hc, v, hv, rfl⟩ := exists_mul_of_mem_sup hN (hCV ▸ ha)
  obtain ⟨s, hsS, hsv⟩ := hinn v hv
  have hsI : s ∈ innerImage A S := mem_innerImage_of hv hsS hsv
  refine ⟨diagHom S C h.diagComm ⟨s, hsS⟩, ⟨⟨s, hsS⟩, hsI, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hvC : ∀ c' ∈ C, v * c' = c' * v := fun c' hc' => h.comm hv.1 (h.CA hc')
  have h1 := conj_diagHom_of_comm h.diagComm y hv.2 hvC
  have h2 : (⟨v * y * v⁻¹, (Subgroup.mem_normalizer_iff.mp hv.2 y).mp y.2⟩ : ↥S) =
      ⟨s, hsS⟩ * y * (⟨s, hsS⟩ : ↥S)⁻¹ :=
    Subtype.ext (conj_eq_of_mem_innerImage hsv y.2).symm
  have hcD := Subgroup.mem_centralizer_iff.mp (h.le_centralizer_diag hc)
  calc c * v * diagHom S C h.diagComm y * (c * v)⁻¹ =
        c * (v * diagHom S C h.diagComm y * v⁻¹) * c⁻¹ := by group
    _ = c * diagHom S C h.diagComm (⟨s, hsS⟩ * y * (⟨s, hsS⟩ : ↥S)⁻¹) * c⁻¹ := by rw [h1, h2]
    _ = diagHom S C h.diagComm (⟨s, hsS⟩ * y * (⟨s, hsS⟩ : ↥S)⁻¹) := by
        rw [← hcD _ ⟨_, rfl⟩]
        group
    _ = diagHom S C h.diagComm ⟨s, hsS⟩ * diagHom S C h.diagComm y *
          (diagHom S C h.diagComm ⟨s, hsS⟩)⁻¹ := by
        rw [map_mul, map_mul, map_inv]

theorem exists_of_mem_diagInner {w : G} (hw : w ∈ diagInner A S C h.diagComm) :
    ∃ v ∈ A, ∀ x ∈ diagSub S C h.diagComm, v * x * v⁻¹ = w * x * w⁻¹ := by
  obtain ⟨s, hs, rfl⟩ := hw
  obtain ⟨v, hv, hsv⟩ := exists_of_mem_innerImage (Subgroup.mem_subgroupOf.mp hs)
  refine ⟨v, hv.1, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hvC : ∀ c' ∈ C, v * c' = c' * v := fun c' hc' => h.comm hv.1 (h.CA hc')
  have h2 : (⟨v * y * v⁻¹, (Subgroup.mem_normalizer_iff.mp hv.2 y).mp y.2⟩ : ↥S) = s * y * s⁻¹ :=
    Subtype.ext (conj_eq_of_mem_innerImage hsv y.2).symm
  rw [conj_diagHom_of_comm h.diagComm y hv.2 hvC, h2, map_mul, map_mul, map_inv]

theorem conj_eq_of_diagInner {k : G}
    (hkD : k ∈ Subgroup.normalizer (diagSub S C h.diagComm : Set G))
    (hkA : k ∈ Subgroup.centralizer (A : Set G)) {w : G}
    (hw : w ∈ diagInner A S C h.diagComm) : k * w * k⁻¹ = w := by
  obtain ⟨v, hvA, hv⟩ := exists_of_mem_diagInner h hw
  have hwD : w ∈ diagSub S C h.diagComm := diagInner_le_diag h hw
  have hw'D : k * w * k⁻¹ ∈ diagSub S C h.diagComm :=
    (Subgroup.mem_normalizer_iff.mp hkD w).mp hwD
  have hkv : k * v = v * k := (Subgroup.mem_centralizer_iff.mp hkA v hvA).symm
  have hcen : w⁻¹ * (k * w * k⁻¹) ∈ Subgroup.centralizer (diagSub S C h.diagComm : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : k⁻¹ * x * k ∈ diagSub S C h.diagComm := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkD) x).mp hx
      simpa using this
    have e1 := hv x hx
    have e2 := hv _ hx'
    have e3 : v * x * v⁻¹ = (k * w * k⁻¹) * x * (k * w * k⁻¹)⁻¹ := by
      have hv' : v = k * v * k⁻¹ := by rw [hkv]; group
      calc v * x * v⁻¹ = k * (v * (k⁻¹ * x * k) * v⁻¹) * k⁻¹ := by
            conv_lhs => rw [hv']
            group
        _ = k * (w * (k⁻¹ * x * k) * w⁻¹) * k⁻¹ := by rw [e2]
        _ = (k * w * k⁻¹) * x * (k * w * k⁻¹)⁻¹ := by group
    rw [e1] at e3
    calc x * (w⁻¹ * (k * w * k⁻¹)) = w⁻¹ * (w * x * w⁻¹) * (k * w * k⁻¹) := by group
      _ = w⁻¹ * ((k * w * k⁻¹) * x * (k * w * k⁻¹)⁻¹) * (k * w * k⁻¹) := by rw [e3]
      _ = w⁻¹ * (k * w * k⁻¹) * x := by group
  have h1 := eq_one_of_mem_centralizer' h.diag_simple h.diag_nonabelian
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwD) hw'D) hcen
  calc k * w * k⁻¹ = w * (w⁻¹ * (k * w * k⁻¹)) := by group
    _ = w := by rw [h1, mul_one]

end Diag

end CFSG.Quasithin.E2.E22N.E111L.KMI
