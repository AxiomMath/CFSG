module

public import CFSG.Sporadic.Co2Smith.GlDataC0Card
public import CFSG.Sporadic.Co2Smith.GlC0FixInputs

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Sift


theorem co2PermHom_inv_mul_apply {a g : K} {b : Fin 2300}
    (h : co2PermHom a b = co2PermHom g b) : co2PermHom (a⁻¹ * g) b = b := by
  rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← h]
  simp

theorem co2PermHom_inv_mul_fix {a g : K} {b : Fin 2300} (ha : co2PermHom a b = b)
    (hg : co2PermHom g b = b) : co2PermHom (a⁻¹ * g) b = b :=
  co2PermHom_inv_mul_apply (ha.trans hg.symm)

theorem exists_sift3 {A : Subgroup K} (S : ℕ → Set K)
    (hS : ∀ s < 3, ∀ a ∈ S s, a ∈ A ∧ ∀ j < s, co2PermHom a (glBasePt j) = glBasePt j)
    (horb : ∀ s < 3, ∀ g ∈ A, (∀ j < s, co2PermHom g (glBasePt j) = glBasePt j) →
      ∃ a ∈ S s, co2PermHom a (glBasePt s) = co2PermHom g (glBasePt s))
    (hbot : ∀ g ∈ A, (∀ j < 3, co2PermHom g (glBasePt j) = glBasePt j) → g = 1) :
    ∀ g ∈ A, ∃ a₀ ∈ S 0, ∃ a₁ ∈ S 1, ∃ a₂ ∈ S 2, g = a₀ * a₁ * a₂ := by
  intro g hg
  obtain ⟨a₀, ha₀, e₀⟩ := horb 0 (by norm_num) g hg fun j hj => absurd hj (by omega)
  obtain ⟨hA₀, -⟩ := hS 0 (by norm_num) a₀ ha₀
  set g₁ := a₀⁻¹ * g with hg₁
  have hg₁A : g₁ ∈ A := A.mul_mem (A.inv_mem hA₀) hg
  have hf₁ : ∀ j < 1, co2PermHom g₁ (glBasePt j) = glBasePt j := by
    intro j hj
    rw [show j = 0 by omega]
    exact co2PermHom_inv_mul_apply e₀
  obtain ⟨a₁, ha₁, e₁⟩ := horb 1 (by norm_num) g₁ hg₁A hf₁
  obtain ⟨hA₁, hfa₁⟩ := hS 1 (by norm_num) a₁ ha₁
  set g₂ := a₁⁻¹ * g₁ with hg₂
  have hg₂A : g₂ ∈ A := A.mul_mem (A.inv_mem hA₁) hg₁A
  have hf₂ : ∀ j < 2, co2PermHom g₂ (glBasePt j) = glBasePt j := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact co2PermHom_inv_mul_fix (hfa₁ 0 (by norm_num)) (hf₁ 0 (by norm_num))
    · exact co2PermHom_inv_mul_apply e₁
  obtain ⟨a₂, ha₂, e₂⟩ := horb 2 (by norm_num) g₂ hg₂A hf₂
  obtain ⟨hA₂, hfa₂⟩ := hS 2 (by norm_num) a₂ ha₂
  have hf₃ : ∀ j < 3, co2PermHom (a₂⁻¹ * g₂) (glBasePt j) = glBasePt j := by
    intro j hj
    rcases (show j < 2 ∨ j = 2 by omega) with hj | rfl
    · exact co2PermHom_inv_mul_fix (hfa₂ j hj) (hf₂ j hj)
    · exact co2PermHom_inv_mul_apply e₂
  have h1 := hbot _ (A.mul_mem (A.inv_mem hA₂) hg₂A) hf₃
  refine ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, ?_⟩
  have h2 : g₂ = a₂ := by
    calc g₂ = a₂ * (a₂⁻¹ * g₂) := by group
      _ = a₂ := by rw [h1, mul_one]
  calc g = a₀ * (a₁ * g₂) := by rw [hg₂, hg₁]; group
    _ = a₀ * a₁ * a₂ := by rw [h2, mul_assoc]

theorem exists_of_orbit {A : Subgroup K} {s : ℕ} {pts : List ℕ}
    (horb : orbit (stabChain (G := A.map co2PermHom) glBasePt s) (glBasePt s) =
      {y : Fin 2300 | (y : ℕ) ∈ pts})
    {g : K} (hg : g ∈ A) (hfix : ∀ j < s, co2PermHom g (glBasePt j) = glBasePt j) :
    ((co2PermHom g (glBasePt s) : Fin 2300) : ℕ) ∈ pts := by
  have hσ : (⟨co2PermHom g, g, hg, rfl⟩ : A.map co2PermHom) ∈
      stabChain (G := A.map co2PermHom) glBasePt s := mem_stabChain.2 fun j hj => hfix j hj
  have hmem : (⟨⟨co2PermHom g, g, hg, rfl⟩, hσ⟩ :
      stabChain (G := A.map co2PermHom) glBasePt s) • glBasePt s ∈
        orbit (stabChain (G := A.map co2PermHom) glBasePt s) (glBasePt s) :=
    mem_orbit _ _
  rw [horb] at hmem
  exact hmem

theorem eq_one_of_stabChain {A : Subgroup K}
    (hbot : stabChain (G := A.map co2PermHom) glBasePt 3 = ⊥) {g : K} (hg : g ∈ A)
    (hfix : ∀ j < 3, co2PermHom g (glBasePt j) = glBasePt j) : g = 1 := by
  have hσ : (⟨co2PermHom g, g, hg, rfl⟩ : A.map co2PermHom) ∈
      stabChain (G := A.map co2PermHom) glBasePt 3 := mem_stabChain.2 fun j hj => hfix j hj
  rw [hbot, Subgroup.mem_bot] at hσ
  apply co2PermHom_injective
  rw [map_one]
  exact congrArg Subtype.val hσ

end Sift

theorem glC0Let_lt' {w : List ℕ} (hw : ∀ k ∈ w, k ∈ Native.glC0Let) : ∀ k ∈ w, k < 22 :=
  fun k hk => glC0Let_lt k (hw k hk)

section C0


theorem exists_wit_C0c {g : K} (hg : g ∈ C0c) :
    ∃ e₀ ∈ Native.glWit0, ∃ e₁ ∈ Native.glWit1, ∃ e₂ ∈ Native.glWit2,
      g = glE e₀.2.2 * glFormK e₀.2.1 * glE e₁.2 * glE e₂.2 := by
  let S : ℕ → Set K := fun s =>
    if s = 0 then {a | ∃ e ∈ Native.glWit0, a = glE e.2.2 * glFormK e.2.1}
    else if s = 1 then {a | ∃ e ∈ Native.glWit1, a = glE e.2}
    else {a | ∃ e ∈ Native.glWit2, a = glE e.2}
  have hS : ∀ s < 3, ∀ a ∈ S s, a ∈ C0c ∧
      ∀ j < s, co2PermHom a (glBasePt j) = glBasePt j := by
    intro s hs a ha
    interval_cases s
    · obtain ⟨e, he, rfl⟩ := ha
      obtain ⟨-, hC0, -, -, -⟩ := glWit0_spec he
      exact ⟨C0c.mul_mem hC0 (glFormK_mem_C0c _), fun j hj => absurd hj (by omega)⟩
    · obtain ⟨e, he, rfl⟩ := ha
      obtain ⟨-, hw, -, hfix, -⟩ :=
        glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.1 e he)
      exact ⟨glE_mem_C0c hw, hfix⟩
    · obtain ⟨e, he, rfl⟩ := ha
      obtain ⟨-, hw, -, hfix, -⟩ :=
        glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.2 e he)
      exact ⟨glE_mem_C0c hw, hfix⟩
  have horb : ∀ s < 3, ∀ g ∈ C0c, (∀ j < s, co2PermHom g (glBasePt j) = glBasePt j) →
      ∃ a ∈ S s, co2PermHom a (glBasePt s) = co2PermHom g (glBasePt s) := by
    intro s hs g hg hfix
    interval_cases s
    · obtain ⟨e, he, hex⟩ := List.mem_map.1 (exists_of_orbit orbit_C0P_zero hg hfix)
      obtain ⟨hx, -, -, -, hmap⟩ := glWit0_spec he
      refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
      rw [← glBasePt_zero] at hmap
      rw [hmap]
      exact Fin.ext hex
    · obtain ⟨e, he, hex⟩ := List.mem_map.1 (exists_of_orbit orbit_C0P_one hg hfix)
      obtain ⟨hx, -, -, -, hmap⟩ :=
        glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.1 e he)
      rw [glFormK_zero, mul_one] at hmap
      exact ⟨_, ⟨e, he, rfl⟩, by rw [hmap]; exact Fin.ext hex⟩
    · obtain ⟨e, he, hex⟩ := List.mem_map.1 (exists_of_orbit orbit_C0P_two hg hfix)
      obtain ⟨hx, -, -, -, hmap⟩ :=
        glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.2 e he)
      rw [glFormK_zero, mul_one] at hmap
      exact ⟨_, ⟨e, he, rfl⟩, by rw [hmap]; exact Fin.ext hex⟩
  obtain ⟨a₀, ⟨e₀, he₀, rfl⟩, a₁, ⟨e₁, he₁, rfl⟩, a₂, ⟨e₂, he₂, rfl⟩, h⟩ :=
    exists_sift3 S hS horb (fun g hg hfix => eq_one_of_stabChain stabChain_C0P_three hg hfix)
      g hg
  exact ⟨e₀, he₀, e₁, he₁, e₂, he₂, h⟩

theorem glWit_lt_C0 {e : ℕ × List ℕ} {s : ℕ} (hs : s = 1 ∨ s = 2)
    (he : e ∈ (if s = 1 then Native.glWit1 else Native.glWit2)) : ∀ k ∈ e.2, k < 22 := by
  rcases hs with rfl | rfl
  · obtain ⟨-, hw, -⟩ := glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.1 e he)
    exact glC0Let_lt' hw
  · obtain ⟨-, hw, -⟩ := glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.2 e he)
    exact glC0Let_lt' hw

theorem exists_rows_C0c {g : K} (hg : g ∈ C0c) :
    ∃ R ∈ Native.glMkC0Rows, g.val.val = rowsMatrix 22 R := by
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, rfl⟩ := exists_wit_C0c hg
  obtain ⟨-, hw₀, -⟩ := glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.1 e₀ he₀).1
  have h1 := glWit_lt_C0 (s := 1) (Or.inl rfl) (by simpa using he₁)
  have h2 := glWit_lt_C0 (s := 2) (Or.inr rfl) (by simpa using he₂)
  refine ⟨_, List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨e₀, he₀, rfl⟩,
    List.mem_flatMap.2 ⟨e₁, he₁, List.mem_map.2 ⟨e₂, he₂, rfl⟩⟩⟩, ?_⟩
  rw [val_mul3 (by rw [val_val_mul, glE_val (glC0Let_lt' hw₀), glFormK_val, rowsMatrix_mulRows])
    (glE_val h1) (glE_val h2)]

end C0

section D


abbrev glWitZ (s : ℕ) : List (ℕ × List ℕ) :=
  [Native.glWitZ0, Native.glWitZ1, Native.glWitZ2][s]!

theorem orbit_C0zP {s : ℕ} (hs : s < 3) :
    orbit (stabChain (G := C0zP) glBasePt s) (glBasePt s) =
      {y : Fin 2300 | (y : ℕ) ∈ (glWitZ s).map (·.1)} := by
  have hpts : [Native.glWitZ0.map (·.1), Native.glWitZ1.map (·.1), Native.glWitZ2.map (·.1)][s]! =
      (glWitZ s).map (·.1) := by
    interval_cases s <;> rfl
  exact glGroup_C0zP.orbit_eq_facts glRefineCz_check hs hpts fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact glWitZ_entry hs he

theorem glWitZ_spec {s : ℕ} (hs : s < 3) {e : ℕ × List ℕ} (he : e ∈ glWitZ s) :
    (∀ k ∈ e.2, k < 22) ∧ glE e.2 ∈ C0c ⊓ Cz ∧
      (∀ j < s, co2PermHom (glE e.2) (glBasePt j) = glBasePt j) ∧
      ∃ hx : e.1 < 2300, co2PermHom (glE e.2) (glBasePt s) = ⟨e.1, hx⟩ := by
  have hent : Native.glWitEntryOK Native.glC0Let true Native.glBase s e.1 0 e.2 = true := by
    interval_cases s
    · exact glWitCz_spec.1 e he
    · exact glWitCz_spec.2.1 e he
    · exact glWitCz_spec.2.2 e he
  obtain ⟨hx, hw, hz, hfix, hmap⟩ := glWitEntry_spec glC0Let_lt hs hent
  rw [glFormK_zero, mul_one] at hmap
  exact ⟨glC0Let_lt' hw, ⟨glE_mem_C0c hw, mem_Cz_of_comm (hz rfl)⟩, hfix, hx, hmap⟩

theorem exists_wit_D {g : K} (hg : g ∈ C0c ⊓ Cz) :
    ∃ e₀ ∈ Native.glWitZ0, ∃ e₁ ∈ Native.glWitZ1, ∃ e₂ ∈ Native.glWitZ2,
      g = glE e₀.2 * glE e₁.2 * glE e₂.2 := by
  let S : ℕ → Set K := fun s => {a | ∃ e ∈ glWitZ s, a = glE e.2}
  have hS : ∀ s < 3, ∀ a ∈ S s, a ∈ C0c ⊓ Cz ∧
      ∀ j < s, co2PermHom a (glBasePt j) = glBasePt j := by
    rintro s hs a ⟨e, he, rfl⟩
    obtain ⟨-, hmem, hfix, -⟩ := glWitZ_spec hs he
    exact ⟨hmem, hfix⟩
  have horb : ∀ s < 3, ∀ g ∈ C0c ⊓ Cz, (∀ j < s, co2PermHom g (glBasePt j) = glBasePt j) →
      ∃ a ∈ S s, co2PermHom a (glBasePt s) = co2PermHom g (glBasePt s) := by
    intro s hs g hg hfix
    obtain ⟨e, he, hex⟩ := List.mem_map.1 (exists_of_orbit (orbit_C0zP hs) hg hfix)
    obtain ⟨-, -, -, hx, hmap⟩ := glWitZ_spec hs he
    exact ⟨_, ⟨e, he, rfl⟩, by rw [hmap]; exact Fin.ext hex⟩
  have hbot : stabChain (G := C0zP) glBasePt 3 = ⊥ :=
    glGroup_C0zP.stabChain_three_facts glRefineCz_check
  obtain ⟨a₀, ⟨e₀, he₀, rfl⟩, a₁, ⟨e₁, he₁, rfl⟩, a₂, ⟨e₂, he₂, rfl⟩, h⟩ :=
    exists_sift3 S hS horb (fun g hg hfix => eq_one_of_stabChain hbot hg hfix) g hg
  exact ⟨e₀, he₀, e₁, he₁, e₂, he₂, h⟩

theorem exists_rows_D {g : K} (hg : g ∈ C0c ⊓ Cz) :
    ∃ R ∈ Native.glMkDcRows, g.val.val = rowsMatrix 22 R := by
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, rfl⟩ := exists_wit_D hg
  have h0 := (glWitZ_spec (s := 0) (by norm_num) he₀).1
  have h1 := (glWitZ_spec (s := 1) (by norm_num) he₁).1
  have h2 := (glWitZ_spec (s := 2) (by norm_num) he₂).1
  refine ⟨_, List.mem_flatMap.2 ⟨e₀, he₀, List.mem_flatMap.2 ⟨e₁, he₁,
    List.mem_map.2 ⟨e₂, he₂, rfl⟩⟩⟩, ?_⟩
  rw [val_mul3 (glE_val h0) (glE_val h1) (glE_val h2)]

end D

end CFSG.Sporadic.Co2Smith
