module

public import CFSG.Quasithin.Background.RonanE68Inn
public import CFSG.Quasithin.Background.RonanE68S6
public import CFSG.Quasithin.Background.RonanE68A6Aut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanE68

open CFSG.Open CFSG.Quasithin Equiv Equiv.Perm

section Dichotomy

variable {G : Type} [Group G]

theorem mem_or_mem_of_relIndex_two {V C : Subgroup G} (h2 : C.relIndex V = 2) {v w : G}
    (hv : v ∈ V) (hw : w ∈ V) (hvC : v ∉ C) : w ∈ C ∨ v⁻¹ * w ∈ C := by
  by_cases hwC : w ∈ C
  · exact Or.inl hwC
  · right
    have hidx : (C.subgroupOf V).index = 2 := h2
    have key := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨v, hv⟩ : ↥V)⁻¹) (b := ⟨w, hw⟩)).2 (by
        constructor
        · intro h
          exact absurd (by simpa [Subgroup.mem_subgroupOf] using h) hvC
        · intro h
          exact absurd (by simpa [Subgroup.mem_subgroupOf] using h) hwC)
    simpa [Subgroup.mem_subgroupOf] using key

end Dichotomy

section ZPowers

theorem mem_zpowers_of_mul_self {Y : Type*} [Group Y] {y : Y} (hy : y * y = 1) {g : Y} :
    g ∈ Subgroup.zpowers y ↔ g = 1 ∨ g = y := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hy, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hy, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

end ZPowers

section Core

variable {G : Type} [Group G] [Finite G]

theorem rootClause_a6_core {L V X : Subgroup G} (e : ↥L ≃* alternatingGroup (Fin 6))
    (hVN : V ≤ Subgroup.normalizer (L : Set G)) (hV2 : ∀ v ∈ V, v * v = 1)
    {v : G} (hvV : v ∈ V) (hvL : ¬ ∀ x ∈ L, x * v = v * x)
    (hdich : ∀ w ∈ V, (∀ x ∈ L, x * w = w * x) ∨ (∀ x ∈ L, x * (v⁻¹ * w) = (v⁻¹ * w) * x))
    (hXL : X ≤ L) (hXC : ∀ x ∈ X, ∀ w ∈ V, x * w = w * x) (hX8 : 8 ∣ Nat.card X)
    (hX9 : 8 < Nat.card X) :
    E6.IsMarkedSp4Root 1 (autSubInduced L (L ⊔ V)) (autSubInduced L V) := by
  classical
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := hVN hvV
  set ρ : MulAut ↥L := inducedAut L v hvN with hρdef
  have hρx : ∀ x : ↥L, ((ρ x : ↥L) : G) = v * (x : G) * v⁻¹ := fun x => rfl
  have hv2 : v * v = 1 := hV2 v hvV
  have hρ2 : ρ ^ 2 = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [pow_two, MulAut.mul_apply, hρx, hρx, MulAut.one_apply]
    calc v * (v * (x : G) * v⁻¹) * v⁻¹ = (v * v) * (x : G) * (v * v)⁻¹ := by group
      _ = x := by rw [hv2]; group
  have hρ1 : ρ ≠ 1 := by
    intro h1
    apply hvL
    intro x hx
    have := congrArg (fun α : MulAut ↥L => ((α ⟨x, hx⟩ : ↥L) : G)) h1
    simp only [MulAut.one_apply] at this
    rw [hρx] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  have hρX : ∀ x : ↥L, (x : G) ∈ X → ρ x = x := by
    intro x hx
    refine Subtype.ext ?_
    rw [hρx]
    have h := hXC x hx v hvV
    calc v * (x : G) * v⁻¹ = (x : G) * v * v⁻¹ := by rw [h]
      _ = x := by group
  have hcN_inj : Function.Injective
      (MulAut.conjNormal : Perm (Fin 6) →* MulAut ↥(alternatingGroup (Fin 6))) :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  rcases alt6_involution_cases' e hρ2 with ⟨σ, hσ⟩ | hcard
  swap
  ·
    exfalso
    have hle : X.subgroupOf L ≤ CFSG.GH74.GLS.fixedSubgroup ↥L ρ := by
      intro x hx
      exact hρX x (Subgroup.mem_subgroupOf.1 hx)
    have h1 : Nat.card (X.subgroupOf L) ∣ Nat.card (CFSG.GH74.GLS.fixedSubgroup ↥L ρ) :=
      Subgroup.card_dvd_of_le hle
    have h2 : Nat.card (X.subgroupOf L) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv
    rw [h2, hcard] at h1
    have := hX8.trans h1
    omega
  have hσ' : ∀ a : ↥L, MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ (e a) = e (ρ a) := by
    intro a
    have h0 : (MulAut.congr e ρ) (e a) = e (ρ a) := by
      simp [MulAut.congr_apply]
    calc MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ (e a) = (MulAut.congr e ρ) (e a) := by
          rw [hσ]
      _ = e (ρ a) := h0
  have hσ2 : σ * σ = 1 := by
    apply hcN_inj
    rw [map_mul, map_one, ← hσ, ← map_mul, ← pow_two, hρ2, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hρ1
    apply (MulAut.congr e).injective
    rw [hσ, h1, map_one, map_one]
  have hσodd : sign σ = -1 := by
    rcases Int.units_eq_one_or (sign σ) with h1 | h1
    · exfalso
      have hcard8 := card_centralizer_a6 σ h1 hσ2 hσ1
      let S : Finset (Perm (Fin 6)) :=
        Finset.univ.filter (fun y => sign y = 1 ∧ y * σ = σ * y)
      have hf : ∀ x : ↥X,
          ((e ⟨(x : G), hXL x.2⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) ∈ S := by
        intro x
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨mem_alternatingGroup.1 (e ⟨(x : G), hXL x.2⟩).2, ?_⟩
        have h3 := hσ' ⟨(x : G), hXL x.2⟩
        rw [hρX _ x.2] at h3
        have h4 := congrArg (fun a : alternatingGroup (Fin 6) => (a : Perm (Fin 6))) h3
        simp only [MulAut.conjNormal_apply] at h4
        exact (mul_inv_eq_iff_eq_mul.1 h4).symm
      have hinj : Function.Injective (fun x : ↥X => (⟨_, hf x⟩ : ↥S)) := by
        intro x y hxy
        have h5 := congrArg Subtype.val hxy
        have h6 : e ⟨(x : G), hXL x.2⟩ = e ⟨(y : G), hXL y.2⟩ := Subtype.ext h5
        have h7 := e.injective h6
        have h8 : ((⟨(x : G), hXL x.2⟩ : ↥L) : G) = ((⟨(y : G), hXL y.2⟩ : ↥L) : G) :=
          congrArg Subtype.val h7
        exact Subtype.ext h8
      have hle : Nat.card ↥X ≤ Nat.card ↥S := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_eq_fintype_card (α := ↥S), Fintype.card_coe, hcard8] at hle
      omega
    · exact h1
  set Θ : MulAut ↥L ≃* MulAut ↥(alternatingGroup (Fin 6)) := MulAut.congr e with hΘ
  set cN : Perm (Fin 6) →* MulAut ↥(alternatingGroup (Fin 6)) :=
    (MulAut.conjNormal : Perm (Fin 6) →* MulAut ↥(alternatingGroup (Fin 6))) with hcN
  have hΘconj : ∀ l : ↥L, Θ (MulAut.conj l) = MulAut.conj (e l) := by
    intro l
    ext x
    simp [hΘ, MulAut.congr_apply, MulAut.conj_apply]
  have hcNconj : ∀ a : alternatingGroup (Fin 6), cN (a : Perm (Fin 6)) = MulAut.conj a :=
    fun _ => MulAut.conjNormal_val
  have hΘρ : Θ ρ = cN σ := hσ
  have hAmem : ∀ α : MulAut ↥L, α ∈ autSubInduced L (L ⊔ V) ↔ ∃ p : Perm (Fin 6), cN p = Θ α := by
    intro α
    constructor
    · rintro ⟨g, hg, hα⟩
      have hgLV : g ∈ (L : Set G) * (V : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left L V hVN]
        exact hg.1
      obtain ⟨l, hl, w, hw, rfl⟩ := hgLV
      rcases hdich w hw with hc | hc
      · have hα' : α = MulAut.conj (⟨l, hl⟩ : ↥L) := by
          refine MulEquiv.ext fun x => Subtype.ext ?_
          rw [hα x]
          show l * w * (x : G) * (l * w)⁻¹ = l * (x : G) * l⁻¹
          have h1 := hc x x.2
          calc l * w * (x : G) * (l * w)⁻¹ = l * (w * x * w⁻¹) * l⁻¹ := by group
            _ = l * (x * w * w⁻¹) * l⁻¹ := by rw [← h1]
            _ = l * (x : G) * l⁻¹ := by group
        refine ⟨((e ⟨l, hl⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)), ?_⟩
        rw [hcNconj, hα', hΘconj]
      · have hα' : α = MulAut.conj (⟨l, hl⟩ : ↥L) * ρ := by
          refine MulEquiv.ext fun x => Subtype.ext ?_
          rw [hα x, MulAut.mul_apply]
          show l * w * (x : G) * (l * w)⁻¹ = l * (v * (x : G) * v⁻¹) * l⁻¹
          have h1 := hc x x.2
          calc l * w * (x : G) * (l * w)⁻¹
              = l * (v * ((v⁻¹ * w) * x * (v⁻¹ * w)⁻¹) * v⁻¹) * l⁻¹ := by group
            _ = l * (v * (x * (v⁻¹ * w) * (v⁻¹ * w)⁻¹) * v⁻¹) * l⁻¹ := by rw [← h1]
            _ = l * (v * (x : G) * v⁻¹) * l⁻¹ := by group
        refine ⟨((e ⟨l, hl⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ, ?_⟩
        rw [map_mul, hcNconj, hα', map_mul, hΘconj, hΘρ]
    · rintro ⟨p, hp⟩
      rcases Int.units_eq_one_or (sign p) with h1 | h1
      · have hpA : p ∈ alternatingGroup (Fin 6) := mem_alternatingGroup.2 h1
        obtain ⟨l, hl⟩ := e.surjective ⟨p, hpA⟩
        have hα' : α = MulAut.conj l := by
          apply Θ.injective
          rw [← hp, hΘconj, hl]
          exact hcNconj ⟨p, hpA⟩
        rw [hα']
        exact ⟨l, ⟨Subgroup.mem_sup_left l.2, Subgroup.le_normalizer l.2⟩, fun x => rfl⟩
      · have hpA : p * σ ∈ alternatingGroup (Fin 6) := by
          rw [mem_alternatingGroup, map_mul, h1, hσodd]
          decide
        obtain ⟨l, hl⟩ := e.surjective ⟨p * σ, hpA⟩
        have hα' : α = MulAut.conj l * ρ := by
          apply Θ.injective
          have hp' : cN p = cN (p * σ) * cN σ := by
            rw [← map_mul, mul_assoc, hσ2, mul_one]
          have hp'' : cN (p * σ) = MulAut.conj (e l) := by
            rw [hl]
            exact hcNconj ⟨p * σ, hpA⟩
          rw [map_mul Θ, hΘconj, hΘρ, ← hp'', ← hp', hp]
        rw [hα']
        refine ⟨(l : G) * v, ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2)
          (Subgroup.mem_sup_right hvV), Subgroup.mul_mem _ (Subgroup.le_normalizer l.2) hvN⟩,
          fun x => ?_⟩
        show (l : G) * (v * (x : G) * v⁻¹) * (l : G)⁻¹ = ((l : G) * v) * (x : G) * ((l : G) * v)⁻¹
        group
  have hRmem : ∀ α : MulAut ↥L, α ∈ autSubInduced L V ↔ α = 1 ∨ α = ρ := by
    intro α
    constructor
    · rintro ⟨g, hg, hα⟩
      rcases hdich g hg.1 with hc | hc
      · left
        refine MulEquiv.ext fun x => Subtype.ext ?_
        rw [hα x, MulAut.one_apply]
        have h1 := hc x x.2
        calc g * (x : G) * g⁻¹ = x * g * g⁻¹ := by rw [← h1]
          _ = x := by group
      · right
        refine MulEquiv.ext fun x => Subtype.ext ?_
        rw [hα x, hρx]
        have h1 := hc x x.2
        calc g * (x : G) * g⁻¹ = v * (((v⁻¹ * g) * x) * (v⁻¹ * g)⁻¹) * v⁻¹ := by group
          _ = v * ((x * (v⁻¹ * g)) * (v⁻¹ * g)⁻¹) * v⁻¹ := by rw [← h1]
          _ = v * (x : G) * v⁻¹ := by group
    · rintro (rfl | rfl)
      · exact ⟨1, ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, fun x => by simp⟩
      · exact inducedAut_mem_autSubInduced hvV hvN
  have hρA : ρ ∈ autSubInduced L (L ⊔ V) := (hAmem ρ).2 ⟨σ, hΘρ.symm⟩
  have hRA : autSubInduced L V ≤ autSubInduced L (L ⊔ V) :=
    fun α ⟨g, hg, h⟩ => ⟨g, ⟨Subgroup.mem_sup_right hg.1, hg.2⟩, h⟩
  have hAS : (autSubInduced L (L ⊔ V)).map Θ.toMonoidHom = cN.range := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      obtain ⟨p, hp⟩ := (hAmem α).1 hα
      exact ⟨p, hp⟩
    · rintro ⟨p, rfl⟩
      refine ⟨Θ.symm (cN p), (hAmem _).2 ⟨p, ?_⟩, by simp⟩
      simp
  set eA : ↥(autSubInduced L (L ⊔ V)) ≃* Perm (Fin 6) :=
    ((Θ.subgroupMap (autSubInduced L (L ⊔ V))).trans (MulEquiv.subgroupCongr hAS)).trans
      (MonoidHom.ofInjective hcN_inj).symm with heA
  have hcN_eA : ∀ a : ↥(autSubInduced L (L ⊔ V)), cN (eA a) = Θ a := by
    intro a
    have h1 := (MonoidHom.ofInjective hcN_inj).apply_symm_apply
      ((MulEquiv.subgroupCongr hAS) ((Θ.subgroupMap (autSubInduced L (L ⊔ V))) a))
    exact congrArg Subtype.val h1
  set marking : ↥(autSubInduced L (L ⊔ V)) ≃* ↥(CFSG.Open.StatedSp 2 (ZMod 2)) :=
    eA.trans Psi.symm with hmarking
  have hy2 : Psi.symm σ * Psi.symm σ = 1 := by rw [← map_mul, hσ2, map_one]
  have hmarkρ : marking ⟨ρ, hρA⟩ = Psi.symm σ := by
    have h1 : eA ⟨ρ, hρA⟩ = σ := by
      apply hcN_inj
      rw [hcN_eA]
      exact hΘρ
    show Psi.symm (eA ⟨ρ, hρA⟩) = _
    rw [h1]
  have hroot : ((autSubInduced L V).subgroupOf (autSubInduced L (L ⊔ V))).map
      marking.toMonoidHom = Subgroup.zpowers (Psi.symm σ) := by
    ext g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, mem_zpowers_of_mul_self hy2, hRmem]
    constructor
    · rintro (h | h)
      · left
        have h1 : marking.symm g = 1 := Subtype.ext h
        rw [← marking.apply_symm_apply g, h1, map_one]
      · right
        have h1 : marking.symm g = ⟨ρ, hρA⟩ := Subtype.ext h
        rw [← marking.apply_symm_apply g, h1, hmarkρ]
    · rintro (h | h)
      · left
        rw [h, map_one]
        rfl
      · right
        have h1 : marking.symm g = ⟨ρ, hρA⟩ := by
          rw [h, ← hmarkρ, marking.symm_apply_apply]
        rw [h1]
  obtain ⟨c, hc⟩ := exists_marked_root hσodd hσ2
  refine ⟨hRA, ZMod 2, inferInstance, inferInstance, inferInstance, ?_, marking, c, ?_⟩
  · rw [Nat.card_zmod]
    norm_num
  · rw [hroot]
    exact hc

end Core

end CFSG.Quasithin.RonanE68
