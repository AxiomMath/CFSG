module

public import CFSG.Sporadic.Co2Smith.GlDataC0
public import CFSG.Sporadic.Co2Rank3.Orbital

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glWit0_lt :
    ∀ x ∈ Native.glWit0.map (·.1), x < 2300 := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  exact (glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.1 e he).1).1

theorem glWit1_lt :
    ∀ x ∈ Native.glWit1.map (·.1), x < 2300 := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  exact (glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.1 e he)).1

theorem glWit2_lt :
    ∀ x ∈ Native.glWit2.map (·.1), x < 2300 := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  exact (glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.2 e he)).1

theorem glWit0_spec
    {e : ℕ × ℕ × List ℕ}
    (he : e ∈ Native.glWit0) :
    ∃ hx : e.1 < 2300, glE e.2.2 ∈ C0c ∧ co2PermHom (glE e.2.2) glP0 = glP0 ∧ e.2.1 < 3 ∧
      co2PermHom (glE e.2.2 * glFormK e.2.1) glP0 = ⟨e.1, hx⟩ := by
  obtain ⟨hent, hfix, ht⟩ := glWitC0_spec.1 e he
  obtain ⟨hx, hw, -, -, hmap⟩ := glWitEntry_spec glC0Let_lt (by norm_num) hent
  have hval := glE_val fun k hk => glC0Let_lt k (hw k hk)
  exact ⟨hx, glE_mem_C0c hw, co2PermHom_apply_of_maps hval (by norm_num) (by norm_num) hfix,
    ht, hmap⟩

theorem orbit_C0P_zero :
    orbit (stabChain (G := C0P) glBasePt 0) (glBasePt 0) =
      {y : Fin 2300 | (y : ℕ) ∈ Native.glWit0.map (·.1)} := by
  refine glGroup_C0P.orbit_eq_facts glRefineC0_check (by norm_num) rfl ?_
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hx', hC0, -, -, hmap⟩ := glWit0_spec he
  exact ⟨hx', _, ⟨_, C0c.mul_mem hC0 (glFormK_mem_C0c _), rfl⟩, fun j hj => absurd hj (by omega),
    hmap⟩

theorem orbit_C0P_one :
    orbit (stabChain (G := C0P) glBasePt 1) (glBasePt 1) =
      {y : Fin 2300 | (y : ℕ) ∈ Native.glWit1.map (·.1)} := by
  refine glGroup_C0P.orbit_eq_facts glRefineC0_check (by norm_num) rfl ?_
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hx', hw, -, hfix, hmap⟩ :=
    glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.1 e he)
  rw [glFormK_zero, mul_one] at hmap
  exact ⟨hx', _, ⟨_, glE_mem_C0c hw, rfl⟩, hfix, hmap⟩

theorem orbit_C0P_two :
    orbit (stabChain (G := C0P) glBasePt 2) (glBasePt 2) =
      {y : Fin 2300 | (y : ℕ) ∈ Native.glWit2.map (·.1)} := by
  refine glGroup_C0P.orbit_eq_facts glRefineC0_check (by norm_num) rfl ?_
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hx', hw, -, hfix, hmap⟩ :=
    glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.2 e he)
  rw [glFormK_zero, mul_one] at hmap
  exact ⟨hx', _, ⟨_, glE_mem_C0c hw, rfl⟩, hfix, hmap⟩

theorem stabChain_C0P_three :
    stabChain (G := C0P) glBasePt 3 = ⊥ :=
  glGroup_C0P.stabChain_three_facts glRefineC0_check

theorem ncard_orbit_C0P_zero :
    (orbit (stabChain (G := C0P) glBasePt 0) (glBasePt 0)).ncard = 40 := by
  rw [orbit_C0P_zero, ncard_setOf_mem glWitPts_spec.1 glWit0_lt, List.length_map,
    glWitPts_spec.2.2.2.2.2.2.1]

theorem ncard_orbit_C0P_one :
    (orbit (stabChain (G := C0P) glBasePt 1) (glBasePt 1)).ncard = 108 := by
  rw [orbit_C0P_one, ncard_setOf_mem glWitPts_spec.2.1 glWit1_lt, List.length_map,
    glWitPts_spec.2.2.2.2.2.2.2.1]

theorem ncard_orbit_C0P_two :
    (orbit (stabChain (G := C0P) glBasePt 2) (glBasePt 2)).ncard = 12 := by
  rw [orbit_C0P_two, ncard_setOf_mem glWitPts_spec.2.2.1 glWit2_lt, List.length_map,
    glWitPts_spec.2.2.2.2.2.2.2.2.1]

theorem card_C0c :
    Nat.card C0c = 51840 := by
  rw [← card_map_co2PermHom]
  exact card_eq_of_stabChain (G := C0P) ncard_orbit_C0P_zero ncard_orbit_C0P_one
    ncard_orbit_C0P_two stabChain_C0P_three

theorem glBasePt_zero : glBasePt 0 = glP0 := Fin.ext (glBasePt_val (by norm_num))

theorem stabChain_one_eq {H : Subgroup (Equiv.Perm (Fin 2300))} :
    stabChain (G := H) glBasePt 1 = stabilizer H glP0 := by
  rw [show stabChain (G := H) glBasePt 1 = ⊤ ⊓ stabilizer H (glBasePt 0) from rfl, top_inf_eq,
    glBasePt_zero]

theorem map_C1c :
    C1c.map co2PermHom = C0P ⊓ stabilizer (Equiv.Perm (Fin 2300)) glP0 := by
  ext σ
  constructor
  · rintro ⟨g, ⟨hg0, hg1⟩, rfl⟩
    exact ⟨⟨g, hg0, rfl⟩, hg1⟩
  · rintro ⟨⟨g, hg0, rfl⟩, hσ⟩
    exact ⟨g, ⟨hg0, hσ⟩, rfl⟩

theorem card_C1c :
    Nat.card C1c = 1296 := by
  rw [← card_map_co2PermHom, map_C1c, ← card_inf_stabilizer_eq, ← stabChain_one_eq]
  have e1 := card_stabChain_succ (G := C0P) glBasePt 1
  have e2 := card_stabChain_succ (G := C0P) glBasePt 2
  rw [stabChain_C0P_three, Subgroup.card_bot] at e2
  rw [e1, e2, ncard_orbit_C0P_one, ncard_orbit_C0P_two]

theorem orbit_C0P_eq :
    orbit C0P glP0 = orbit (stabChain (G := C0P) glBasePt 0) (glBasePt 0) := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, mem_stabChain.2 fun j hj => absurd hj (Nat.not_lt_zero _)⟩, rfl⟩
  · rintro ⟨⟨g, -⟩, rfl⟩
    exact ⟨g, rfl⟩

theorem glWitZ_entry
    {s : ℕ} (hs : s < 3) {e : ℕ × List ℕ}
    (he : e ∈ [Native.glWitZ0, Native.glWitZ1, Native.glWitZ2][s]!) :
    ∃ hx : e.1 < 2300, ∃ σ ∈ C0zP, (∀ j < s, σ (glBasePt j) = glBasePt j) ∧
      σ (glBasePt s) = ⟨e.1, hx⟩ := by
  have hent : Native.glWitEntryOK Native.glC0Let true Native.glBase s e.1 0 e.2 = true := by
    interval_cases s
    · exact glWitCz_spec.1 e he
    · exact glWitCz_spec.2.1 e he
    · exact glWitCz_spec.2.2 e he
  obtain ⟨hx, hw, hz, hfix, hmap⟩ := glWitEntry_spec glC0Let_lt hs hent
  rw [glFormK_zero, mul_one] at hmap
  exact ⟨hx, _, ⟨_, ⟨glE_mem_C0c hw, mem_Cz_of_comm (hz rfl)⟩, rfl⟩, hfix, hmap⟩

end CFSG.Sporadic.Co2Smith
