module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace SzPS8

namespace AxA

section Product

variable {A : Type*} [Group A]

@[expose] def fac1 : Subgroup (A × A) := (⊤ : Subgroup A).prod ⊥

@[expose] def fac2 : Subgroup (A × A) := (⊥ : Subgroup A).prod ⊤

theorem mem_fac1 {p : A × A} : p ∈ (fac1 : Subgroup (A × A)) ↔ p.2 = 1 := by
  simp [fac1, Subgroup.mem_prod]

theorem mem_fac2 {p : A × A} : p ∈ (fac2 : Subgroup (A × A)) ↔ p.1 = 1 := by
  simp [fac2, Subgroup.mem_prod]

@[expose] noncomputable def fac1Equiv : ↥(fac1 : Subgroup (A × A)) ≃* A :=
  MulEquiv.ofBijective ((MonoidHom.fst A A).comp (fac1 : Subgroup (A × A)).subtype)
    ⟨fun p q h => Subtype.ext (Prod.ext h (by
      rw [mem_fac1.mp p.2, mem_fac1.mp q.2])),
      fun a => ⟨⟨(a, 1), mem_fac1.mpr rfl⟩, rfl⟩⟩

@[expose] noncomputable def fac2Equiv : ↥(fac2 : Subgroup (A × A)) ≃* A :=
  MulEquiv.ofBijective ((MonoidHom.snd A A).comp (fac2 : Subgroup (A × A)).subtype)
    ⟨fun p q h => Subtype.ext (Prod.ext (by
      rw [mem_fac2.mp p.2, mem_fac2.mp q.2]) h),
      fun a => ⟨⟨(1, a), mem_fac2.mpr rfl⟩, rfl⟩⟩

theorem center_eq_bot [IsSimpleGroup A] (hnc : ¬ IsMulCommutative A) :
    Subgroup.center A = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · exact h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have : a ∈ Subgroup.center A := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

theorem fac_le_of_normal [IsSimpleGroup A] (hnc : ¬ IsMulCommutative A) {N : Subgroup (A × A)}
    [N.Normal] (hN : N ≠ ⊥) : (fac1 : Subgroup (A × A)) ≤ N ∨ (fac2 : Subgroup (A × A)) ≤ N := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hW1 : N.comap (MonoidHom.inl A A) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl A A)) with h | h
    · exact h
    · exfalso
      apply h1
      intro p hp
      have hp2 : p.2 = 1 := mem_fac1.mp hp
      have h3 : p.1 ∈ N.comap (MonoidHom.inl A A) := h ▸ Subgroup.mem_top _
      have e : (MonoidHom.inl A A) p.1 = p := Prod.ext rfl hp2.symm
      have h4 : (MonoidHom.inl A A) p.1 ∈ N := h3
      rwa [e] at h4
  have hW2 : N.comap (MonoidHom.inr A A) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr A A)) with h | h
    · exact h
    · exfalso
      apply h2
      intro p hp
      have hp1 : p.1 = 1 := mem_fac2.mp hp
      have h3 : p.2 ∈ N.comap (MonoidHom.inr A A) := h ▸ Subgroup.mem_top _
      have e : (MonoidHom.inr A A) p.2 = p := Prod.ext hp1.symm rfl
      have h4 : (MonoidHom.inr A A) p.2 ∈ N := h3
      rwa [e] at h4
  have hZ := center_eq_bot hnc
  apply hN
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hn
  rw [Subgroup.mem_bot]
  have ha : a = 1 := by
    have : a ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hc : (c * a * c⁻¹ * a⁻¹, (1 : A)) ∈ N := by
        have e1 := Subgroup.Normal.conj_mem inferInstance (a, b) hn ((c, 1) : A × A)
        have e2 := N.mul_mem e1 (N.inv_mem hn)
        convert e2 using 1
        simp [mul_assoc]
      have hc' : c * a * c⁻¹ * a⁻¹ ∈ N.comap (MonoidHom.inl A A) := hc
      rw [hW1, Subgroup.mem_bot] at hc'
      calc c * a = (c * a * c⁻¹ * a⁻¹) * (a * c) := by group
        _ = a * c := by rw [hc', one_mul]
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have hb : b = 1 := by
    have : b ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hc : ((1 : A), c * b * c⁻¹ * b⁻¹) ∈ N := by
        have e1 := Subgroup.Normal.conj_mem inferInstance (a, b) hn ((1, c) : A × A)
        have e2 := N.mul_mem e1 (N.inv_mem hn)
        convert e2 using 1
        simp [mul_assoc]
      have hc' : c * b * c⁻¹ * b⁻¹ ∈ N.comap (MonoidHom.inr A A) := hc
      rw [hW2, Subgroup.mem_bot] at hc'
      calc c * b = (c * b * c⁻¹ * b⁻¹) * (b * c) := by group
        _ = b * c := by rw [hc', one_mul]
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  rw [ha, hb]
  rfl

end Product

section Embed

variable {Ω : Type*} [Group Ω] {A : Type*} [Group A]

@[expose] def emb (F : Subgroup Ω) (θ : ↥F ≃* A × A) : A × A →* Ω :=
  F.subtype.comp θ.symm.toMonoidHom

theorem emb_injective (F : Subgroup Ω) (θ : ↥F ≃* A × A) : Function.Injective (emb F θ) :=
  F.subtype_injective.comp θ.symm.injective

theorem emb_mem (F : Subgroup Ω) (θ : ↥F ≃* A × A) (z : A × A) : emb F θ z ∈ F :=
  (θ.symm z).2

theorem exists_emb_eq {F : Subgroup Ω} (θ : ↥F ≃* A × A) {f : Ω} (hf : f ∈ F) :
    ∃ z, emb F θ z = f := ⟨θ ⟨f, hf⟩, by simp [emb]⟩

theorem range_emb (F : Subgroup Ω) (θ : ↥F ≃* A × A) : (emb F θ).range = F := by
  ext f
  constructor
  · rintro ⟨z, rfl⟩
    exact emb_mem F θ z
  · intro hf
    exact exists_emb_eq θ hf

@[expose] def sub1 (F : Subgroup Ω) (θ : ↥F ≃* A × A) : Subgroup Ω :=
  (fac1 : Subgroup (A × A)).map (emb F θ)

@[expose] def sub2 (F : Subgroup Ω) (θ : ↥F ≃* A × A) : Subgroup Ω :=
  (fac2 : Subgroup (A × A)).map (emb F θ)

theorem sub1_le (F : Subgroup Ω) (θ : ↥F ≃* A × A) : sub1 F θ ≤ F := by
  rintro _ ⟨z, -, rfl⟩
  exact emb_mem F θ z

theorem sub2_le (F : Subgroup Ω) (θ : ↥F ≃* A × A) : sub2 F θ ≤ F := by
  rintro _ ⟨z, -, rfl⟩
  exact emb_mem F θ z

theorem sub1_sup_sub2 (F : Subgroup Ω) (θ : ↥F ≃* A × A) : sub1 F θ ⊔ sub2 F θ = F := by
  apply le_antisymm (sup_le (sub1_le F θ) (sub2_le F θ))
  intro f hf
  obtain ⟨⟨a, b⟩, rfl⟩ := exists_emb_eq θ hf
  have e : ((a, b) : A × A) = (a, 1) * (1, b) := by simp
  rw [e, map_mul]
  exact Subgroup.mul_mem_sup ⟨(a, 1), mem_fac1.mpr rfl, rfl⟩ ⟨(1, b), mem_fac2.mpr rfl, rfl⟩

noncomputable def sub1Equiv (F : Subgroup Ω) (θ : ↥F ≃* A × A) : ↥(sub1 F θ) ≃* A :=
  (Subgroup.equivMapOfInjective _ (emb F θ) (emb_injective F θ)).symm.trans fac1Equiv

noncomputable def sub2Equiv (F : Subgroup Ω) (θ : ↥F ≃* A × A) : ↥(sub2 F θ) ≃* A :=
  (Subgroup.equivMapOfInjective _ (emb F θ) (emb_injective F θ)).symm.trans fac2Equiv

theorem conj_mem_sub1 {F : Subgroup Ω} (θ : ↥F ≃* A × A) {f a : Ω} (hf : f ∈ F)
    (ha : a ∈ sub1 F θ) : f * a * f⁻¹ ∈ sub1 F θ := by
  obtain ⟨z, rfl⟩ := exists_emb_eq θ hf
  obtain ⟨y, hy, rfl⟩ := ha
  refine ⟨z * y * z⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have hy2 : y.2 = 1 := mem_fac1.mp hy
  exact mem_fac1.mpr (by simp [hy2])

theorem conj_mem_sub2 {F : Subgroup Ω} (θ : ↥F ≃* A × A) {f a : Ω} (hf : f ∈ F)
    (ha : a ∈ sub2 F θ) : f * a * f⁻¹ ∈ sub2 F θ := by
  obtain ⟨z, rfl⟩ := exists_emb_eq θ hf
  obtain ⟨y, hy, rfl⟩ := ha
  refine ⟨z * y * z⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  have hy1 : y.1 = 1 := mem_fac2.mp hy
  exact mem_fac2.mpr (by simp [hy1])

variable [Finite A] [IsSimpleGroup A]

omit [Finite A] [IsSimpleGroup A] in
theorem card_sub1 (F : Subgroup Ω) (θ : ↥F ≃* A × A) : Nat.card (sub1 F θ) = Nat.card A := by
  unfold sub1
  rw [Subgroup.card_map_of_injective (emb_injective F θ)]
  exact Nat.card_congr fac1Equiv.toEquiv

omit [Finite A] [IsSimpleGroup A] in
theorem card_sub2 (F : Subgroup Ω) (θ : ↥F ≃* A × A) : Nat.card (sub2 F θ) = Nat.card A := by
  unfold sub2
  rw [Subgroup.card_map_of_injective (emb_injective F θ)]
  exact Nat.card_congr fac2Equiv.toEquiv

omit [Finite A] [IsSimpleGroup A] in
theorem sub1_ne_sub2 [Nontrivial A] (F : Subgroup Ω) (θ : ↥F ≃* A × A) :
    sub1 F θ ≠ sub2 F θ := by
  intro h
  have h1 : (fac1 : Subgroup (A × A)) = fac2 :=
    Subgroup.map_injective (emb_injective F θ) h
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have : ((a, (1 : A)) : A × A) ∈ (fac1 : Subgroup (A × A)) := mem_fac1.mpr rfl
  rw [h1] at this
  exact ha (mem_fac2.mp this)

theorem eq_fac_of_card (hnc : ¬ IsMulCommutative A) {N : Subgroup (A × A)} [N.Normal]
    (hcard : Nat.card N = Nat.card A) :
    N = (fac1 : Subgroup (A × A)) ∨ N = (fac2 : Subgroup (A × A)) := by
  have hnt : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnc ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  have hNbot : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < Nat.card A := Finite.one_lt_card_iff_nontrivial.mpr hnt
    omega
  have hc1 : Nat.card (fac1 : Subgroup (A × A)) = Nat.card A := Nat.card_congr fac1Equiv.toEquiv
  have hc2 : Nat.card (fac2 : Subgroup (A × A)) = Nat.card A := Nat.card_congr fac2Equiv.toEquiv
  rcases fac_le_of_normal hnc hNbot with h | h
  · left
    exact (Subgroup.eq_of_le_of_card_ge h (by rw [hc1, hcard])).symm
  · right
    exact (Subgroup.eq_of_le_of_card_ge h (by rw [hc2, hcard])).symm

theorem map_conj_eq_sub (hnc : ¬ IsMulCommutative A) {F : Subgroup Ω} (θ : ↥F ≃* A × A)
    (hFn : ∀ (γ : Ω), ∀ f ∈ F, γ * f * γ⁻¹ ∈ F) {B : Subgroup Ω} (hBF : B ≤ F)
    (hBn : ∀ f ∈ F, ∀ a ∈ B, f * a * f⁻¹ ∈ B) (hBcard : Nat.card B = Nat.card A) (γ : Ω) :
    B.map (MulAut.conj γ).toMonoidHom = sub1 F θ ∨
      B.map (MulAut.conj γ).toMonoidHom = sub2 F θ := by
  set N : Subgroup Ω := B.map (MulAut.conj γ).toMonoidHom with hN
  have hNF : N ≤ F := by
    rintro _ ⟨a, ha, rfl⟩
    exact hFn γ a (hBF ha)
  set N₀ : Subgroup (A × A) := N.comap (emb F θ) with hN₀
  have hN₀map : N₀.map (emb F θ) = N :=
    Subgroup.map_comap_eq_self (hNF.trans (range_emb F θ).ge)
  have : N₀.Normal := ⟨fun n hn z => by
    have hn' : emb F θ n ∈ N := hn
    obtain ⟨a, ha, hae⟩ := hn'
    show emb F θ (z * n * z⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv, ← hae]
    set f := emb F θ z with hf
    have hfF : f ∈ F := emb_mem F θ z
    have h1 : γ⁻¹ * f * γ⁻¹⁻¹ ∈ F := hFn γ⁻¹ f hfF
    have h2 := hBn _ h1 _ ha
    refine ⟨_, h2, ?_⟩
    simp [MulAut.conj_apply]
    group⟩
  have hcard : Nat.card N₀ = Nat.card A := by
    rw [← Subgroup.card_map_of_injective (emb_injective F θ), hN₀map, hN,
      Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    exact hBcard
  rcases eq_fac_of_card hnc hcard with h | h
  · left
    rw [← hN₀map, h]
    rfl
  · right
    rw [← hN₀map, h]
    rfl

theorem map_conj_sub1 (hnc : ¬ IsMulCommutative A) {F : Subgroup Ω} (θ : ↥F ≃* A × A)
    (hFn : ∀ (γ : Ω), ∀ f ∈ F, γ * f * γ⁻¹ ∈ F) (γ : Ω) :
    (sub1 F θ).map (MulAut.conj γ).toMonoidHom = sub1 F θ ∨
      (sub1 F θ).map (MulAut.conj γ).toMonoidHom = sub2 F θ :=
  map_conj_eq_sub hnc θ hFn (sub1_le F θ) (fun _ hf _ ha => conj_mem_sub1 θ hf ha)
    (card_sub1 F θ) γ

theorem map_conj_sub2 (hnc : ¬ IsMulCommutative A) {F : Subgroup Ω} (θ : ↥F ≃* A × A)
    (hFn : ∀ (γ : Ω), ∀ f ∈ F, γ * f * γ⁻¹ ∈ F) (γ : Ω) :
    (sub2 F θ).map (MulAut.conj γ).toMonoidHom = sub1 F θ ∨
      (sub2 F θ).map (MulAut.conj γ).toMonoidHom = sub2 F θ :=
  map_conj_eq_sub hnc θ hFn (sub2_le F θ) (fun _ hf _ ha => conj_mem_sub2 θ hf ha)
    (card_sub2 F θ) γ

omit [Finite A] in
theorem sub_le_of_normal (hnc : ¬ IsMulCommutative A) {F : Subgroup Ω} (θ : ↥F ≃* A × A)
    (hFn : ∀ (γ : Ω), ∀ f ∈ F, γ * f * γ⁻¹ ∈ F)
    (hCF : ∀ x : Ω, (∀ f ∈ F, x * f = f * x) → x ∈ F) {P : Subgroup Ω}
    (hPn : ∀ (γ : Ω), ∀ p ∈ P, γ * p * γ⁻¹ ∈ P) (hP : P ≠ ⊥) :
    sub1 F θ ≤ P ∨ sub2 F θ ≤ P := by
  have hQ : P ⊓ F ≠ ⊥ := by
    intro hQ
    apply hP
    rw [eq_bot_iff]
    intro p hp
    have hpF : p ∈ F := by
      apply hCF
      intro f hf
      have h1 : p * f * p⁻¹ * f⁻¹ ∈ P ⊓ F := by
        refine ⟨?_, ?_⟩
        · have := P.mul_mem hp (hPn f p⁻¹ (P.inv_mem hp))
          simpa [mul_assoc] using this
        · have := F.mul_mem (hFn p f hf) (F.inv_mem hf)
          exact this
      rw [hQ, Subgroup.mem_bot] at h1
      calc p * f = (p * f * p⁻¹ * f⁻¹) * (f * p) := by group
        _ = f * p := by rw [h1, one_mul]
    have h5 : p ∈ P ⊓ F := Subgroup.mem_inf.mpr ⟨hp, hpF⟩
    rwa [hQ] at h5
  set Q₀ : Subgroup (A × A) := (P ⊓ F).comap (emb F θ) with hQ₀
  have hQ₀map : Q₀.map (emb F θ) = P ⊓ F :=
    Subgroup.map_comap_eq_self (inf_le_right.trans (range_emb F θ).ge)
  have : Q₀.Normal := ⟨fun n hn z => by
    have hn' : emb F θ n ∈ P ⊓ F := hn
    show emb F θ (z * n * z⁻¹) ∈ P ⊓ F
    rw [map_mul, map_mul, map_inv]
    exact ⟨hPn _ _ hn'.1, F.mul_mem (F.mul_mem (emb_mem F θ z) hn'.2)
      (F.inv_mem (emb_mem F θ z))⟩⟩
  have hQ₀ne : Q₀ ≠ ⊥ := by
    intro h
    apply hQ
    rw [← hQ₀map, h, Subgroup.map_bot]
  rcases fac_le_of_normal hnc hQ₀ne with h | h
  · left
    calc sub1 F θ = (fac1 : Subgroup (A × A)).map (emb F θ) := rfl
      _ ≤ Q₀.map (emb F θ) := Subgroup.map_mono h
      _ = P ⊓ F := hQ₀map
      _ ≤ P := inf_le_left
  · right
    calc sub2 F θ = (fac2 : Subgroup (A × A)).map (emb F θ) := rfl
      _ ≤ Q₀.map (emb F θ) := Subgroup.map_mono h
      _ = P ⊓ F := hQ₀map
      _ ≤ P := inf_le_left

end Embed

section Swap

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem exists_mem_of_swap {B C : Subgroup Ω}
    (hdich : ∀ γ : Ω, B.map (MulAut.conj γ).toMonoidHom = B ∨
      B.map (MulAut.conj γ).toMonoidHom = C) {T₀ : Subgroup Ω} (hT : ¬ 2 ∣ T₀.index)
    (hswap : ∃ γ : Ω, B.map (MulAut.conj γ).toMonoidHom ≠ B) :
    ∃ t ∈ T₀, B.map (MulAut.conj t).toMonoidHom ≠ B := by
  classical
  by_contra hcon0
  have hcon : ∀ t ∈ T₀, B.map (MulAut.conj t).toMonoidHom = B := fun t ht =>
    by_contra fun h => hcon0 ⟨t, ht, h⟩
  set N : Subgroup Ω := Subgroup.normalizer (B : Set Ω) with hN
  have hmapN : ∀ γ : Ω, B.map (MulAut.conj γ).toMonoidHom = B ↔ γ ∈ N := by
    intro γ
    rw [hN, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  have hTN : T₀ ≤ N := fun t ht => (hmapN t).mp (hcon t ht)
  have hodd : ¬ 2 ∣ N.index := fun hd =>
    hT (hd.trans (Subgroup.index_dvd_of_le hTN))
  have hconj : ∀ γ γ' : Ω, B.map (MulAut.conj γ).toMonoidHom =
      B.map (MulAut.conj γ').toMonoidHom → γ⁻¹ * γ' ∈ N := by
    intro γ γ' h
    rw [← hmapN]
    have h1 : (B.map (MulAut.conj γ').toMonoidHom) =
        (B.map (MulAut.conj (γ⁻¹ * γ')).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [h1] at h
    have := Subgroup.map_injective (MulAut.conj γ).injective h
    exact this.symm
  let g : Ω ⧸ N → Bool := Quotient.lift (fun γ => decide (B.map (MulAut.conj γ).toMonoidHom = B))
    (fun γ γ' hγ => by
      have hγ' : γ⁻¹ * γ' ∈ N := QuotientGroup.leftRel_apply.mp hγ
      have h1 : B.map (MulAut.conj γ').toMonoidHom = B.map (MulAut.conj γ).toMonoidHom := by
        have h2 : (B.map (MulAut.conj (γ⁻¹ * γ')).toMonoidHom) = B := (hmapN _).mpr hγ'
        calc B.map (MulAut.conj γ').toMonoidHom
            = (B.map (MulAut.conj (γ⁻¹ * γ')).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
              rw [Subgroup.map_map]
              congr 1
              ext x
              simp [MulAut.conj_apply, mul_assoc]
          _ = B.map (MulAut.conj γ).toMonoidHom := by rw [h2]
      simp only [h1])
  have hginj : Function.Injective g := by
    intro a b hab
    induction a using Quotient.inductionOn with | _ γ => ?_
    induction b using Quotient.inductionOn with | _ γ' => ?_
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    apply hconj
    have hab' : decide (B.map (MulAut.conj γ).toMonoidHom = B) =
        decide (B.map (MulAut.conj γ').toMonoidHom = B) := hab
    have hiff : B.map (MulAut.conj γ).toMonoidHom = B ↔
        B.map (MulAut.conj γ').toMonoidHom = B := decide_eq_decide.mp hab'
    by_cases h1 : B.map (MulAut.conj γ).toMonoidHom = B
    · rw [h1, hiff.mp h1]
    · have h2 := mt hiff.mpr h1
      rcases hdich γ with h3 | h3
      · exact absurd h3 h1
      · rcases hdich γ' with h4 | h4
        · exact absurd h4 h2
        · rw [h3, h4]
  have hle : N.index ≤ 2 := by
    rw [Subgroup.index]
    calc Nat.card (Ω ⧸ N) ≤ Nat.card Bool := Nat.card_le_card_of_injective g hginj
      _ = 2 := by simp
  have hne : N.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    obtain ⟨γ₀, hγ₀⟩ := hswap
    exact hγ₀ ((hmapN γ₀).mpr (h1 ▸ Subgroup.mem_top γ₀))
  have : N.index = 2 := by
    have : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  exact hodd (by omega)

end Swap

end AxA

end SzPS8

end CFSG.Quasithin
