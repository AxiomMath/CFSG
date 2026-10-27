module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoRec
public import Certificates.Certificate7077

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.CosetTable

@[expose] def barA2 : Subgroup M22 where
  carrier := {g | ∀ y ∈ m22HexadL, (g : Equiv.Perm (Fin 22)) y = y}
  mul_mem' := by
    intro g h hg hh y hy
    show ((g * h : M22) : Equiv.Perm (Fin 22)) y = y
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hh y hy, hg y hy]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro g hg y hy
    show ((g⁻¹ : M22) : Equiv.Perm (Fin 22)) y = y
    rw [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq, hg y hy]

theorem mem_barA2 {g : M22} : g ∈ barA2 ↔ ∀ y ∈ m22HexadL, (g : Equiv.Perm (Fin 22)) y = y :=
  Iff.rfl

@[expose] def barC2 : Subgroup M22 := m22PtHexStab ⊓ stabilizer M22 (3 : Fin 22)

theorem mem_barC2 {g : M22} : g ∈ barC2 ↔ ((g : Equiv.Perm (Fin 22)) 0 = 0 ∧
    ∀ p ∈ m22HexadL, (g : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
      (g : Equiv.Perm (Fin 22)) 3 = 3 := by
  rw [barC2, Subgroup.mem_inf, M22Witt.mem_m22PtHexStab_iff, mem_stabilizer_iff, smul_m22_def]

theorem count_barA2 :
    m22Count (fun σ => ∀ y ∈ m22HexadL, σ y = y) = 16 :=
  Certificates.certificate7077.1

theorem count_barA2_sq :
    m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ ¬ ∀ x, σ (σ x) = x) = 0 :=
  Certificates.certificate7077.2.1

theorem count_barC2 :
    m22Count (fun σ => (σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = 3) = 60 :=
  Certificates.certificate7077.2.2.1

theorem count_barA2_three :
    m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧ σ 3 = 3 ∧ ¬ ∀ x, σ x = x) = 0 :=
  Certificates.certificate7077.2.2.2.1

theorem count_barA2_fpf :
    m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
      (∀ x, σ ((b2r : Equiv.Perm (Fin 22)) x) = (b2r : Equiv.Perm (Fin 22)) (σ x)) ∧
        ¬ ∀ x, σ x = x) = 0 :=
  Certificates.certificate7077.2.2.2.2.1

theorem c2_facts : (((a2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
    ∀ p ∈ m22HexadL, (a2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
      (a2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
    (((b2r : Equiv.Perm (Fin 22)) 0 = 0 ∧
      ∀ p ∈ m22HexadL, (b2r : Equiv.Perm (Fin 22)) p ∈ m22HexadL) ∧
        (b2r : Equiv.Perm (Fin 22)) 3 = 3) ∧
    a2r * a2r = 1 ∧ b2r ^ 3 = 1 ∧ (a2r * b2r) ^ 5 = 1 :=
  Certificates.certificate7077.2.2.2.2.2.1

theorem cWords_nodup : cWords.Nodup ∧ cWords.length = 60 :=
  Certificates.certificate7077.2.2.2.2.2.2.1

theorem c2Words_nodup :
    (cWords.map fun s => tab (c2OfWord s)).Nodup :=
  Certificates.certificate7077.2.2.2.2.2.2.2

theorem card_barA2 :
    Nat.card barA2 = 16 := by
  rw [← count_barA2, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => Iff.rfl)

theorem mul_self_of_mem_barA2
    {g : M22} (hg : g ∈ barA2) : g * g = 1 := by
  have h := not_of_count_eq_zero _ count_barA2_sq g
  simp only [not_and, not_not] at h
  have h2 := h hg
  apply Subtype.ext
  ext x
  rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, h2 x, Subgroup.coe_one, Equiv.Perm.one_apply]

theorem barA2_le : barA2 ≤ m22PtHexStab := fun g hg =>
  M22Witt.mem_m22PtHexStab_iff.mpr ⟨hg 0 (by simp [m22HexadL]), fun p hp => by
    rw [hg p hp]; exact hp⟩

theorem barA2_le_two : barA2 ≤ m22TwoStab := fun g hg =>
  mem_m22TwoStab_iff.mpr ⟨hg 0 (by simp [m22HexadL]), hg 1 (by simp [m22HexadL])⟩

theorem conj_mem_barA2 {n : M22} (hn : n ∈ m22PtHexStab) {e : M22} (he : e ∈ barA2) :
    n * e * n⁻¹ ∈ barA2 := by
  intro y hy
  have hn' := (M22Witt.mem_m22PtHexStab_iff.mp (m22PtHexStab.inv_mem hn)).2 y hy
  rw [Subgroup.coe_inv] at hn'
  show ((n * e * n⁻¹ : M22) : Equiv.Perm (Fin 22)) y = y
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, he _ hn']
  exact (n : Equiv.Perm (Fin 22)).apply_symm_apply y

theorem mul_comm_of_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y * x := by rw [mul_inv_rev, h1, h2]

theorem card_barC2 :
    Nat.card barC2 = 60 := by
  rw [← count_barC2, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_barC2)

theorem barC2_le : barC2 ≤ m22PtHexStab := inf_le_left

theorem a2r_mem : a2r ∈ barC2 := mem_barC2.mpr c2_facts.1

theorem b2r_mem : b2r ∈ barC2 := mem_barC2.mpr c2_facts.2.1

theorem c2OfWord_mem (s : String) : c2OfWord s ∈ Subgroup.closure ({a2r, b2r} : Set M22) := by
  unfold c2OfWord
  set K := Subgroup.closure ({a2r, b2r} : Set M22)
  suffices h : ∀ (l : List Char) (g : M22), g ∈ K →
      l.foldl (fun g c => g * if c = 'a' then a2r else if c = 'b' then b2r else b2r⁻¹) g ∈
        K from h _ _ K.one_mem
  intro l
  induction l with
  | nil => exact fun g hg => hg
  | cons c l ih =>
    intro g hg
    apply ih
    refine K.mul_mem hg ?_
    have ha : a2r ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
    have hb : b2r ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    split_ifs
    · exact ha
    · exact hb
    · exact K.inv_mem hb

theorem closure_c2 :
    Subgroup.closure ({a2r, b2r} : Set M22) = barC2 := by
  have hle : Subgroup.closure ({a2r, b2r} : Set M22) ≤ barC2 := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact a2r_mem
    · exact b2r_mem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_barC2]
  have hinj : Function.Injective (fun s : {s // s ∈ cWords} =>
      (⟨c2OfWord s.1, c2OfWord_mem s.1⟩ : Subgroup.closure ({a2r, b2r} : Set M22))) := by
    intro s t h
    have h' : c2OfWord s.1 = c2OfWord t.1 := congrArg Subtype.val h
    exact Subtype.ext (List.inj_on_of_nodup_map c2Words_nodup s.2 t.2 (by rw [h']))
  have hcard : Nat.card {s // s ∈ cWords} = 60 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun s => (List.mem_toFinset (l := cWords)).symm),
      Nat.card_eq_finsetCard, List.toFinset_card_of_nodup cWords_nodup.1, cWords_nodup.2]
  rw [← hcard]
  exact Nat.card_le_card_of_injective _ hinj

abbrev barA2' : Subgroup ↥m22PtHexStab := barA2.subgroupOf m22PtHexStab

abbrev barC2' : Subgroup ↥m22PtHexStab := barC2.subgroupOf m22PtHexStab

instance barA2'_normal : barA2'.Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_barA2 g.2 hn⟩

@[expose] def a2' : ↥m22PtHexStab := ⟨a2r, barC2_le a2r_mem⟩

@[expose] def b2' : ↥m22PtHexStab := ⟨b2r, barC2_le b2r_mem⟩

theorem coe_b2' : (b2' : M22) = b2r := rfl

theorem card_barA2' :
    Nat.card barA2' = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe barA2_le).toEquiv, card_barA2]

theorem card_barC2' :
    Nat.card barC2' = 60 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe barC2_le).toEquiv, card_barC2]

theorem barA2'_inf_barC2' :
    barA2' ⊓ barC2' = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g ⟨hgA, hgC⟩ => ?_
  have hgA' : (g : M22) ∈ barA2 := hgA
  have hgC' : (g : M22) ∈ barC2 := hgC
  have h := not_of_count_eq_zero _ count_barA2_three (g : M22)
  simp only [not_and, not_not] at h
  exact Subtype.ext (Subtype.ext (Equiv.ext (h hgA' (mem_barC2.mp hgC').2)))

theorem closure_c2' :
    Subgroup.closure {a2', b2'} = barC2' := by
  apply Subgroup.map_injective m22PtHexStab.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le barC2_le]
  have : (m22PtHexStab.subtype '' {a2', b2'}) = {a2r, b2r} := by
    ext g
    simp [a2', b2']
  rw [this, closure_c2]

theorem a2'_mul : a2' * a2' = 1 := Subtype.ext c2_facts.2.2.1

theorem b2'_pow : b2' ^ 3 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]; exact c2_facts.2.2.2.1)

theorem ab2'_pow : (a2' * b2') ^ 5 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow, Subgroup.coe_mul]; exact c2_facts.2.2.2.2)

theorem fpf_of_count {b : M22}
    (hcount : m22Count (fun σ => (∀ y ∈ m22HexadL, σ y = y) ∧
      (∀ x, σ ((b : Equiv.Perm (Fin 22)) x) = (b : Equiv.Perm (Fin 22)) (σ x)) ∧
        ¬ ∀ x, σ x = x) = 0) {e : M22} (he : e ∈ barA2) (hc : b * e = e * b) : e = 1 := by
  have h := not_of_count_eq_zero _ hcount e
  simp only [not_and, not_not] at h
  have hc' : ∀ x, (e : Equiv.Perm (Fin 22)) ((b : Equiv.Perm (Fin 22)) x) =
      (b : Equiv.Perm (Fin 22)) ((e : Equiv.Perm (Fin 22)) x) := fun x => by
    have := congrArg (fun z : M22 => (z : Equiv.Perm (Fin 22)) x) hc
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at this
    exact this.symm
  exact Subtype.ext (Equiv.ext (h he hc'))

theorem b2r_fpf {e : M22}
    (he : e ∈ barA2) (hc : b2r * e = e * b2r) : e = 1 :=
  fpf_of_count count_barA2_fpf he hc

theorem b2'_fpf :
    ∀ e ∈ barA2', b2' * e = e * b2' → e = 1 := by
  intro e he hc
  have he' : (e : M22) ∈ barA2 := he
  have hc' : b2r * (e : M22) = (e : M22) * b2r := by
    have := congrArg Subtype.val hc
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_b2'] at this
  exact Subtype.ext (b2r_fpf he' hc')

theorem barA2'_comm :
    ∀ x ∈ barA2', ∀ y ∈ barA2', x * y = y * x := by
  intro x hx y hy
  have h2 : ∀ z ∈ barA2', z * z = 1 := fun z hz =>
    Subtype.ext (mul_self_of_mem_barA2 (Subgroup.mem_subgroupOf.mp hz))
  exact mul_comm_of_mul_self (h2 x hx) (h2 y hy) (h2 _ (barA2'.mul_mem hx hy))

theorem exists_mulEquiv_P1_P2 :
    ∃ ψ : ↥m22TwoStab ≃* ↥m22PtHexStab,
    ∀ g : ↥m22TwoStab, ((ψ g : ↥m22PtHexStab) : M22) ∈ barA2 ↔ (g : M22) ∈ barA1 := by
  obtain ⟨ψ, h1, h2, -, -⟩ := exists_mulEquiv_P1 (X := ↥m22PtHexStab) (E := barA2')
    (C := barC2') barA2'_comm
    (fun z hz => Subtype.ext (mul_self_of_mem_barA2 (Subgroup.mem_subgroupOf.mp hz)))
    card_barA2' barA2'_inf_barC2' card_barC2' M22Witt.card_m22PtHexStab closure_c2' a2'_mul
    b2'_pow ab2'_pow b2'_fpf
  refine ⟨ψ, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · obtain ⟨x, hx⟩ := h2 (ψ g) (Subgroup.mem_subgroupOf.mpr hg)
    rw [← ψ.injective hx]
    exact ⟨x, rfl⟩
  · obtain ⟨x, hx⟩ := hg
    have e : g = crd' x := Subtype.ext hx.symm
    rw [e]
    exact Subgroup.mem_subgroupOf.mp (h1 x)

theorem exists_mulEquiv_P1_iff
    {X : Type*} [Group X] [Finite X]
    {E C : Subgroup X} [E.Normal]
    (hE2 : ∀ x ∈ E, x * x = 1) (hEc : Nat.card E = 16)
    (hCE : E ⊓ C = ⊥) (hCc : Nat.card C = 60) (hX : Nat.card X = 960)
    {a b : X} (hC : Subgroup.closure {a, b} = C)
    (ha : a * a = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1)
    (hfpf : ∀ e ∈ E, b * e = e * b → e = 1) :
    ∃ ψ : ↥m22TwoStab ≃* X, ∀ g : ↥m22TwoStab, ψ g ∈ E ↔ (g : M22) ∈ barA1 := by
  obtain ⟨ψ, h1, h2, -, -⟩ := exists_mulEquiv_P1 (fun x hx y hy => mul_comm_of_mul_self
    (hE2 x hx) (hE2 y hy) (hE2 _ (E.mul_mem hx hy))) hE2 hEc hCE hCc hX hC ha hb hab hfpf
  refine ⟨ψ, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · obtain ⟨x, hx⟩ := h2 (ψ g) hg
    rw [← ψ.injective hx]
    exact ⟨x, rfl⟩
  · obtain ⟨x, hx⟩ := hg
    have e : g = crd' x := Subtype.ext hx.symm
    rw [e]
    exact h1 x

theorem exists_mulEquiv_P2_iff
    {X : Type*} [Group X] [Finite X] {E C : Subgroup X} [E.Normal]
    (hE2 : ∀ x ∈ E, x * x = 1) (hEc : Nat.card E = 16)
    (hCE : E ⊓ C = ⊥) (hCc : Nat.card C = 60) (hX : Nat.card X = 960)
    {a b : X} (hC : Subgroup.closure {a, b} = C)
    (ha : a * a = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1)
    (hfpf : ∀ e ∈ E, b * e = e * b → e = 1) :
    ∃ ψ : ↥m22PtHexStab ≃* X, ∀ g : ↥m22PtHexStab, ψ g ∈ E ↔ (g : M22) ∈ barA2 := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_P1_iff hE2 hEc hCE hCc hX hC ha hb hab hfpf
  obtain ⟨χ, hχ⟩ := exists_mulEquiv_P1_P2
  refine ⟨χ.symm.trans ψ, fun g => ?_⟩
  rw [MulEquiv.trans_apply, hψ, ← hχ, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.L34Amalgam
