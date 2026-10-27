module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoGL
public import CFSG.Quasithin.Recognition.L34AmalgamGen
public meta import CFSG.Quasithin.Recognition.L34AmalgamIsoGL
public meta import CFSG.Quasithin.Recognition.L34AmalgamData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import Certificates.Certificate2195
public import CFSG.Quasithin.Recognition.L34AmalgamIsoRefInputs
public import Certificates.Certificate7040
public import Certificates.Certificate7036
public import Certificates.Certificate7037
public import Certificates.Certificate7041

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.Sporadic.Mathieu

theorem ref_facts :
    (refa : Equiv.Perm (Fin 22)) 0 = 0 ∧ (refa : Equiv.Perm (Fin 22)) 1 = 1 ∧
    (refb : Equiv.Perm (Fin 22)) 0 = 0 ∧ (refb : Equiv.Perm (Fin 22)) 1 = 1 ∧
    refa * refa = 1 ∧ refb ^ 3 = 1 ∧ (refa * refb) ^ 5 = 1 :=
  Certificates.certificate7040.1

theorem crd_facts :
    ∀ x : Fin 16, ((crd x : M22) : Equiv.Perm (Fin 22)) 0 = 0 ∧
    ((crd x : M22) : Equiv.Perm (Fin 22)) 1 = 1 :=
  Certificates.certificate7040.2.1

theorem crd_mul : ∀ x y : Fin 16, crd (bxor x y) = crd x * crd y :=
  Certificates.certificate7040.2.2.1

theorem crd_eq_one : ∀ x : Fin 16, crd x = 1 → x = 0 :=
  Certificates.certificate7040.2.2.2.1

theorem crd_zero : crd 0 = 1 :=
  Certificates.certificate7040.2.2.2.2.1

theorem crd_conj_a :
    ∀ x : Fin 16, refa * crd x * refa⁻¹ = crd (lin refA x) :=
  Certificates.certificate7040.2.2.2.2.2.1

theorem crd_conj_b :
    ∀ x : Fin 16, refb * crd x * refb⁻¹ = crd (lin refB x) :=
  Certificates.certificate7040.2.2.2.2.2.2.1

theorem cWords_inj :
    ∀ s ∈ cWords, ∀ t ∈ cWords, cOfWord s = cOfWord t → s = t :=
  Certificates.certificate7040.2.2.2.2.2.2.2.1

theorem cWords_closed :
    ∀ s ∈ cWords, (∃ t ∈ cWords, cOfWord s * refa = cOfWord t) ∧
    (∃ t ∈ cWords, cOfWord s * refb = cOfWord t) ∧
      ∃ t ∈ cWords, cOfWord s * refb⁻¹ = cOfWord t :=
  Certificates.certificate7040.2.2.2.2.2.2.2.2.1

theorem cWords_crd :
    ∀ s ∈ cWords, ∀ x : Fin 16, cOfWord s = crd x → x = 0 :=
  Certificates.certificate7040.2.2.2.2.2.2.2.2.2.1

theorem cWords_one : cOfWord "" = 1 :=
  Certificates.certificate7040.2.2.2.2.2.2.2.2.2.2.1

theorem crd_conj_gen :
    ∀ j : Fin 5, j ≠ 4 → ∀ x : Fin 16, ∃ y : Fin 16,
    gen j * crd x * (gen j)⁻¹ = crd y :=
  Certificates.certificate7040.2.2.2.2.2.2.2.2.2.2.2.1

theorem crd_mul_self (x : Fin 16) : crd x * crd x = 1 := by
  rw [← crd_mul, bxor_self, crd_zero]

theorem crd_inv (x : Fin 16) : (crd x)⁻¹ = crd x :=
  inv_eq_of_mul_eq_one_right (crd_mul_self x)

@[expose] def barA1 : Subgroup M22 where
  carrier := Set.range crd
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨bxor x y, crd_mul x y⟩
  one_mem' := ⟨0, crd_zero⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, (crd_inv x).symm⟩

theorem crd_injective : Function.Injective crd := by
  intro x y h
  have h1 : crd (bxor x y) = 1 := by rw [crd_mul, h, crd_mul_self]
  have h2 := crd_eq_one _ h1
  have := congrArg (bxor · y) h2
  simp only [bxor_assoc, bxor_self, bxor_zero, zero_bxor] at this
  exact this

theorem card_barA1 : Nat.card barA1 = 16 := by
  have : Nat.card barA1 = Nat.card (Fin 16) :=
    (Nat.card_congr (Equiv.ofInjective crd crd_injective)).symm
  rw [this, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def barC : Subgroup M22 := Subgroup.closure {refa, refb}

theorem cOfWord_mem (s : String) : cOfWord s ∈ barC := by
  unfold cOfWord
  suffices h : ∀ (l : List Char) (g : M22), g ∈ barC →
      l.foldl (fun g c => g * if c = 'a' then refa else if c = 'b' then refb else refb⁻¹) g ∈
        barC from h _ _ barC.one_mem
  intro l
  induction l with
  | nil => exact fun g hg => hg
  | cons c l ih =>
    intro g hg
    apply ih
    refine barC.mul_mem hg ?_
    have ha : refa ∈ barC := Subgroup.subset_closure (Set.mem_insert _ _)
    have hb : refb ∈ barC := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    split_ifs
    · exact ha
    · exact hb
    · exact barC.inv_mem hb

theorem refa_inv :
    refa⁻¹ = refa := inv_eq_of_mul_eq_one_right ref_facts.2.2.2.2.1

theorem mem_barC_iff {g : M22} :
    g ∈ barC ↔ ∃ s ∈ cWords, cOfWord s = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨"", by simp [cWords], cWords_one⟩
    | mul_right x hx y hy ih =>
      obtain ⟨s, hs, rfl⟩ := ih
      rcases hy with rfl | rfl
      · obtain ⟨t, ht, e⟩ := (cWords_closed s hs).1
        exact ⟨t, ht, e.symm⟩
      · obtain ⟨t, ht, e⟩ := (cWords_closed s hs).2.1
        exact ⟨t, ht, e.symm⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨s, hs, rfl⟩ := ih
      rcases hy with rfl | rfl
      · obtain ⟨t, ht, e⟩ := (cWords_closed s hs).1
        exact ⟨t, ht, by rw [refa_inv]; exact e.symm⟩
      · obtain ⟨t, ht, e⟩ := (cWords_closed s hs).2.2
        exact ⟨t, ht, e.symm⟩
  · rintro ⟨s, -, rfl⟩
    exact cOfWord_mem s

theorem card_barC : Nat.card barC = 60 := by
  have e : barC ≃ {s // s ∈ cWords} :=
    { toFun := fun g => ⟨(mem_barC_iff.mp g.2).choose, (mem_barC_iff.mp g.2).choose_spec.1⟩
      invFun := fun s => ⟨cOfWord s.1, cOfWord_mem _⟩
      left_inv := fun g => Subtype.ext (mem_barC_iff.mp g.2).choose_spec.2
      right_inv := fun s => Subtype.ext
        (cWords_inj _ (mem_barC_iff.mp (cOfWord_mem s.1)).choose_spec.1
          _ s.2 (mem_barC_iff.mp (cOfWord_mem s.1)).choose_spec.2) }
  have hnd : cWords.Nodup ∧ cWords.length = 60 :=
    Certificates.certificate7040.2.2.2.2.2.2.2.2.2.2.2.2
  rw [Nat.card_congr e,
    Nat.card_congr (Equiv.subtypeEquivRight fun s => (List.mem_toFinset (l := cWords)).symm),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hnd.1, hnd.2]

theorem barA1_inf_barC : barA1 ⊓ barC = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g ⟨⟨x, hx⟩, hgC⟩ => ?_
  obtain ⟨s, hs, hsg⟩ := mem_barC_iff.mp hgC
  have := cWords_crd s hs x (hsg.trans hx.symm)
  rw [← hx, this, crd_zero]

theorem barA1_le_two : barA1 ≤ m22TwoStab := by
  rintro _ ⟨x, rfl⟩
  exact mem_m22TwoStab_iff.mpr (crd_facts x)

theorem barC_le_two : barC ≤ m22TwoStab := by
  rw [barC, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact mem_m22TwoStab_iff.mpr ⟨ref_facts.1, ref_facts.2.1⟩
  · exact mem_m22TwoStab_iff.mpr ⟨ref_facts.2.2.1, ref_facts.2.2.2.1⟩

theorem conj_mem_barA1
    {g : M22} (hg : g ∈ m22TwoStab) {a : M22}
    (ha : a ∈ barA1) :
    g * a * g⁻¹ ∈ barA1 := by
  rw [← closure_gen_P1] at hg
  induction hg using Subgroup.closure_induction generalizing a with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := ha
    have hj4 : j ≠ 4 := by rintro rfl; simp at hj
    obtain ⟨z, hz⟩ := crd_conj_gen j hj4 y
    exact ⟨z, hz.symm⟩
  | one => simpa using ha
  | mul x y _ _ hx hy =>
    have := hx (hy ha)
    rwa [show x * (y * a * y⁻¹) * x⁻¹ = x * y * a * (x * y)⁻¹ by group] at this
  | inv x _ hx =>
    have hmap : ∀ b ∈ barA1, x * b * x⁻¹ ∈ barA1 := fun b hb => hx hb
    have hinj : Function.Injective (fun b : barA1 => (⟨x * b * x⁻¹, hmap b b.2⟩ : barA1)) := by
      intro b c h
      apply Subtype.ext
      have := congrArg Subtype.val h
      simpa using this
    have hsurj := (Finite.injective_iff_surjective.mp hinj) ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hsurj
    have hb' : x * b * x⁻¹ = a := congrArg Subtype.val hb
    rw [← hb', show x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ = b by group]
    exact b.2

end CFSG.Quasithin.L34Amalgam
