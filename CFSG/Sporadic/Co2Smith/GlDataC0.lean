module

public import CFSG.Sporadic.Co2Smith.GlDataElts
public import CFSG.Sporadic.Co2Smith.GlDataStab

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem card_map_co2PermHom
    (A : Subgroup K) : Nat.card (A.map co2PermHom) = Nat.card A :=
  Subgroup.card_map_of_injective co2PermHom_injective

theorem map_co2PermHom_le_co2P
    (A : Subgroup K) : A.map co2PermHom ≤ co2P := by
  rintro _ ⟨g, -, rfl⟩
  rw [← co2PermHom_range]
  exact ⟨g, rfl⟩

@[expose] noncomputable def C0P :
    Subgroup (Equiv.Perm (Fin 2300)) :=
  C0c.map co2PermHom

@[expose] noncomputable def C0zP :
    Subgroup (Equiv.Perm (Fin 2300)) :=
  (C0c ⊓ Cz).map co2PermHom

theorem glArc_spec :
    ((Native.glPermArr Native.glAl).size = 2300 ∧
      Rep 2300 (Native.glPermArr Native.glAl) (co2PermHom α3K)) ∧
    ((Native.glPermArr Native.glGa).size = 2300 ∧
      Rep 2300 (Native.glPermArr Native.glGa) (co2PermHom γ3K)) ∧
    ((Native.glPermArr Native.glZ).size = 2300 ∧
      Rep 2300 (Native.glPermArr Native.glZ) (co2PermHom z0)) := by
  have h := glElem_parts.2.2.2.2.1
  simp only [Native.glArcOK, Bool.and_eq_true] at h
  exact ⟨rep_co2PermHom_of_permOK α3K_val h.1.1, rep_co2PermHom_of_permOK γ3K_val h.1.2,
    rep_co2PermHom_of_permOK z0_val' h.2⟩

theorem arcComm_of_comm
    {g h : K} {p : Array ℕ} (hp : p.size = 2300 ∧ Rep 2300 p (co2PermHom h))
    (hc : h * g = g * h) : ArcComm (co2PermHom g) p :=
  ⟨hp.1, co2PermHom h, hp.2, by rw [← map_mul, ← map_mul, hc]⟩

theorem glGroup_C0P :
    GlGroup C0P [Native.glPermArr Native.glAl, Native.glPermArr Native.glGa] := by
  refine ⟨map_co2PermHom_le_co2P C0c, ?_⟩
  rintro _ ⟨g, hg, rfl⟩ p hp
  obtain ⟨ha, hc⟩ := mem_C0c.1 hg
  obtain hp | hp := List.mem_cons.1 hp
  · rw [hp]
    exact arcComm_of_comm glArc_spec.1 ha
  · rw [List.mem_singleton.1 hp]
    exact arcComm_of_comm glArc_spec.2.1 hc

theorem glGroup_C0zP :
    GlGroup C0zP [Native.glPermArr Native.glAl, Native.glPermArr Native.glGa,
      Native.glPermArr Native.glZ] := by
  refine ⟨map_co2PermHom_le_co2P _, ?_⟩
  rintro _ ⟨g, ⟨hg, hgz⟩, rfl⟩ p hp
  obtain ⟨ha, hc⟩ := mem_C0c.1 hg
  obtain hp | hp := List.mem_cons.1 hp
  · rw [hp]
    exact arcComm_of_comm glArc_spec.1 ha
  obtain hp | hp := List.mem_cons.1 hp
  · rw [hp]
    exact arcComm_of_comm glArc_spec.2.1 hc
  · rw [List.mem_singleton.1 hp]
    exact arcComm_of_comm glArc_spec.2.2 (comm_of_mem_Cz hgz).symm

theorem glWit_parts :
    Native.glWitC0OK = true ∧ Native.glWitCzOK = true ∧ Native.glWitPtsOK = true := by
  have h := glWit_check
  simp only [Native.glWitOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem glWitPts_spec :
    (Native.glWit0.map (·.1)).Nodup ∧ (Native.glWit1.map (·.1)).Nodup ∧
    (Native.glWit2.map (·.1)).Nodup ∧ (Native.glWitZ0.map (·.1)).Nodup ∧
    (Native.glWitZ1.map (·.1)).Nodup ∧ (Native.glWitZ2.map (·.1)).Nodup ∧
    Native.glWit0.length = 40 ∧ Native.glWit1.length = 108 ∧ Native.glWit2.length = 12 ∧
    Native.glWitZ0.length = 10 ∧ Native.glWitZ1.length = 36 ∧ Native.glWitZ2.length = 4 ∧
    (Native.glWit0Pts 1).length = 27 ∧ (Native.glWit0Pts 2).length = 12 := by
  have h := glWit_parts.2.2
  simp only [Native.glWitPtsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem glBasePt_eq {j : ℕ} (hj : j < 3) :
    glBasePt j = ⟨Native.glBase[j]!, by interval_cases j <;> decide⟩ :=
  Fin.ext (glBasePt_val hj)

theorem glFormK_zero : glFormK 0 = 1 := by
  simp [glFormK]

theorem glWitEntry_spec
    {L : List ℕ} {cz : Bool} {s x t : ℕ} {w : List ℕ} (hL : ∀ k ∈ L, k < 22) (hs : s < 3)
    (h : Native.glWitEntryOK L cz Native.glBase s x t w = true) :
    ∃ hx : x < 2300, (∀ k ∈ w, k ∈ L) ∧ (cz = true → glE w * z0 = z0 * glE w) ∧
      (∀ j < s, co2PermHom (glE w) (glBasePt j) = glBasePt j) ∧
      co2PermHom (glE w * glFormK t) (glBasePt s) = ⟨x, hx⟩ := by
  simp only [Native.glWitEntryOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hx, hw⟩, hz⟩, hfix⟩, hmap⟩ := h
  have hval := glE_val fun k hk => hL k (hw k hk)
  refine ⟨hx, hw, fun hcz => ?_, fun j hj => ?_, ?_⟩
  · rcases hz with hz | hz
    · rw [hcz] at hz
      exact absurd hz (by decide)
    · exact comm_of_commRows hval z0_val' hz
  · have hj3 : j < 3 := by omega
    rw [glBasePt_eq hj3]
    exact co2PermHom_apply_of_maps hval _ _ (hfix j (List.mem_range.2 hj))
  · rw [glBasePt_eq hs]
    have hv : (glE w * glFormK t).val.val =
        rowsMatrix 22 (mulRows 22 (Native.glR w) (Native.glForm t)) := by
      rw [val_val_mul, hval, glFormK_val, rowsMatrix_mulRows]
    exact co2PermHom_apply_of_maps hv _ hx hmap

theorem glC0Let_lt : ∀ k ∈ Native.glC0Let, k < 22 := by decide

theorem glWitC0_spec :
    (∀ e ∈ Native.glWit0, Native.glWitEntryOK Native.glC0Let false Native.glBase 0 e.1 e.2.1
      e.2.2 = true ∧ Native.glMaps (Native.glR e.2.2) 80 80 = true ∧ e.2.1 < 3) ∧
    (∀ e ∈ Native.glWit1,
      Native.glWitEntryOK Native.glC0Let false Native.glBase 1 e.1 0 e.2 = true) ∧
    (∀ e ∈ Native.glWit2,
      Native.glWitEntryOK Native.glC0Let false Native.glBase 2 e.1 0 e.2 = true) := by
  have h := glWit_parts.1
  simp only [Native.glWitC0OK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨fun e he => ⟨(h.1.1 e he).1.1, (h.1.1 e he).1.2, (h.1.1 e he).2⟩, h.1.2, h.2⟩

theorem glWitCz_spec :
    (∀ e ∈ Native.glWitZ0,
      Native.glWitEntryOK Native.glC0Let true Native.glBase 0 e.1 0 e.2 = true) ∧
    (∀ e ∈ Native.glWitZ1,
      Native.glWitEntryOK Native.glC0Let true Native.glBase 1 e.1 0 e.2 = true) ∧
    (∀ e ∈ Native.glWitZ2,
      Native.glWitEntryOK Native.glC0Let true Native.glBase 2 e.1 0 e.2 = true) := by
  have h := glWit_parts.2.1
  simp only [Native.glWitCzOK, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end CFSG.Sporadic.Co2Smith
