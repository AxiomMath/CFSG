module

public import CFSG.Quasithin.H13.GoldschmidtI51T16
public import CFSG.Quasithin.H13.GoldschmidtI51Nbd

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

omit [Finite G] in
theorem ncard_orbit_coset (H K : Subgroup G) (g : G) :
    (MulAction.orbit ↥H (g : G ⧸ K)).ncard = (H ⊓ cj g K).relIndex H := by
  rw [← MulAction.index_stabilizer]
  have : MulAction.stabilizer ↥H (g : G ⧸ K) = (cj g K).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_cj, Subgroup.smul_def,
      MulAction.Quotient.smul_mk, QuotientGroup.eq]
    have key : ((h : G) * g)⁻¹ * g = (g⁻¹ * (h : G) * g)⁻¹ := by group
    rw [smul_eq_mul, key, K.inv_mem_iff]
  rw [this, Subgroup.inf_relIndex_left]; rfl

@[expose] def Col (Gs : Fin 3 → Subgroup G) (p q : G ⧸ Gs 0) : Prop :=
  ∃ a b : G, (a : G ⧸ Gs 0) = p ∧ (b : G ⧸ Gs 0) = q ∧ a⁻¹ * b ∈ Nbd Gs

omit [Finite G] in
theorem col_mk {a b : G} : Col Gs (a : G ⧸ Gs 0) (b : G ⧸ Gs 0) ↔ a⁻¹ * b ∈ Nbd Gs := by
  constructor
  · rintro ⟨a', b', ha, hb, h⟩
    rw [QuotientGroup.eq] at ha hb
    have e : a⁻¹ * b = (a'⁻¹ * a)⁻¹ * (a'⁻¹ * b') * (b'⁻¹ * b) := by group
    rw [e]
    exact Nbd_mul_G0 hb (G0_mul_Nbd ((Gs 0).inv_mem ha) h)
  · intro h; exact ⟨a, b, rfl, rfl, h⟩

omit [Finite G] in
theorem col_smul_mk (g a b : G) :
    Col Gs ((g • (a : G ⧸ Gs 0)) : G ⧸ Gs 0) (g • (b : G ⧸ Gs 0)) ↔ Col Gs (a : G ⧸ Gs 0) b := by
  have h1 : g • (a : G ⧸ Gs 0) = ((g * a : G) : G ⧸ Gs 0) := rfl
  have h2 : g • (b : G ⧸ Gs 0) = ((g * b : G) : G ⧸ Gs 0) := rfl
  have : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
  rw [h1, h2, col_mk, col_mk, this]

omit [Finite G] in
theorem col_smul (g : G) (p q : G ⧸ Gs 0) :
    Col Gs (g • p) (g • q) ↔ Col Gs p q := by
  induction p using QuotientGroup.induction_on with | _ a => ?_
  induction q using QuotientGroup.induction_on with | _ b => ?_
  exact col_smul_mk g a b

omit [Finite G] in
theorem col_refl (p : G ⧸ Gs 0) : Col Gs p p := by
  induction p using QuotientGroup.induction_on with | _ a => ?_
  rw [col_mk, inv_mul_cancel]; exact G0_sub_Nbd (Gs 0).one_mem

omit [Finite G] in
theorem col_symm {p q : G ⧸ Gs 0} (h : Col Gs p q) : Col Gs q p := by
  induction p using QuotientGroup.induction_on with | _ a => ?_
  induction q using QuotientGroup.induction_on with | _ b => ?_
  rw [col_mk] at h ⊢
  simpa using Nbd_inv h

@[expose] def oPt (Gs : Fin 3 → Subgroup G) : G ⧸ Gs 0 := ((1 : G) : G ⧸ Gs 0)

omit [Finite G] in
theorem col_oPt {n : G} : Col Gs (oPt Gs) (n : G ⧸ Gs 0) ↔ n ∈ Nbd Gs := by
  rw [oPt, col_mk, inv_one, one_mul]

@[expose] def Dlt (Gs : Fin 3 → Subgroup G) : Set (G ⧸ Gs 0) :=
  {p | p ≠ oPt Gs ∧ Col Gs (oPt Gs) p}

theorem exists_s0 (hD : IsDSystem D Gs) : ∃ s ∈ Gs 1, s ∉ Gs 0 := by
  by_contra h
  push Not at h
  have h1 : (Gs 0 ⊓ Gs 1).relIndex (Gs 1) = 1 :=
    Subgroup.relIndex_eq_one.2 (fun s hs => ⟨h s hs, hs⟩)
  have := loc1_index_10 hD
  omega

theorem exists_q0 (hD : IsDSystem D Gs) : ∃ q ∈ QQ Gs 0, q ∉ QQ Gs 1 := by
  by_contra h
  push Not at h
  exact not_Q0_le_Q1 hD h

theorem stab_le_P (hD : IsDSystem D Gs) {s0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0) :
    Gs 0 ⊓ cj s0 (Gs 0) ≤ Gs 0 ⊓ Gs 1 := fun _ hg =>
  ⟨hg.1, uniq_line hD hs0 hs00 hs0 hg.1 (mem_cj.1 hg.2)⟩

theorem Dlt_eq_orbit (hD : IsDSystem D Gs) {s0 q0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hq0 : q0 ∈ QQ Gs 0) (hq01 : q0 ∉ QQ Gs 1) :
    Dlt Gs = MulAction.orbit ↥(Gs 0) ((s0 : G) : G ⧸ Gs 0) := by
  have hsm : ∀ (x : ↥(Gs 0)) (y : G),
      x • ((y : G) : G ⧸ Gs 0) = (((x : G) * y : G) : G ⧸ Gs 0) := fun x y => rfl
  ext p
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨hp1, hp2⟩
    induction p using QuotientGroup.induction_on with | _ a => ?_
    rw [col_oPt] at hp2
    obtain ⟨x, hx, s, hs, c, hc, rfl⟩ := hp2
    have hpe : ((x * s * c : G) : G ⧸ Gs 0) = ((x * s : G) : G ⧸ Gs 0) := by
      rw [QuotientGroup.eq]
      have : (x * s * c)⁻¹ * (x * s) = c⁻¹ := by group
      rw [this]; exact (Gs 0).inv_mem hc
    have hs0' : s ∉ Gs 0 := fun h => hp1 (by
      rw [hpe, oPt, QuotientGroup.eq, mul_one]
      exact (Gs 0).inv_mem ((Gs 0).mul_mem hx h))
    rcases line_pts hD hs0 hs00 hq0 hq01 hs with h | h | h
    · exact absurd h hs0'
    · refine ⟨⟨x, hx⟩, ?_⟩
      rw [hsm, hpe, QuotientGroup.eq]
      have : (x * s0)⁻¹ * (x * s) = s0⁻¹ * s := by group
      rw [this]; exact h
    · refine ⟨⟨x * q0, (Gs 0).mul_mem hx (TT_le 0 (QQ_le_TT hD 0 hq0))⟩, ?_⟩
      rw [hsm, hpe, QuotientGroup.eq]
      have : (x * q0 * s0)⁻¹ * (x * s) = (q0 * s0)⁻¹ * s := by group
      rw [this]; exact h
  · rintro ⟨h, rfl⟩
    rw [hsm]
    refine ⟨?_, ?_⟩
    · intro he
      rw [oPt, QuotientGroup.eq, mul_one] at he
      have h1 : ((h : G) * s0) ∈ Gs 0 := by simpa using (Gs 0).inv_mem he
      exact hs00 (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem h.2) h1)
    · rw [col_oPt]
      exact ⟨h, h.2, s0, hs0, 1, (Gs 0).one_mem, by group⟩

theorem orbit_P_s0 (hD : IsDSystem D Gs) {s0 q0 : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hq0 : q0 ∈ QQ Gs 0) (hq01 : q0 ∉ QQ Gs 1) :
    MulAction.orbit ↥(Gs 0 ⊓ Gs 1) ((s0 : G) : G ⧸ Gs 0) =
      {((s0 : G) : G ⧸ Gs 0), ((q0 * s0 : G) : G ⧸ Gs 0)} := by
  have hsm : ∀ (x : ↥(Gs 0 ⊓ Gs 1)) (y : G),
      x • ((y : G) : G ⧸ Gs 0) = (((x : G) * y : G) : G ⧸ Gs 0) := fun x y => rfl
  ext p
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨x, rfl⟩
    rw [hsm]
    rcases line_pts hD hs0 hs00 hq0 hq01 ((Gs 1).mul_mem x.2.2 hs0) with h | h | h
    · exact absurd (by simpa using (Gs 0).mul_mem ((Gs 0).inv_mem x.2.1) h) hs00
    · left
      rw [QuotientGroup.eq]
      have := (Gs 0).inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
    · right
      rw [Set.mem_singleton_iff, QuotientGroup.eq]
      have := (Gs 0).inv_mem h
      rwa [mul_inv_rev, inv_inv] at this
  · rintro (rfl | rfl)
    · exact ⟨1, by rw [hsm]; simp⟩
    · exact ⟨⟨q0, Q0_le_P01 hD hq0⟩, hsm _ _⟩

theorem ncard_Dlt_of (hD : IsDSystem D Gs) {n : ℕ} (hn : (Gs 0 ⊓ Gs 1).relIndex (Gs 0) = n) :
    (Dlt Gs).ncard = 2 * n := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  obtain ⟨q0, hq0, hq01⟩ := exists_q0 hD
  rw [Dlt_eq_orbit hD hs0 hs00 hq0 hq01, ncard_orbit_coset]
  have hS : Gs 0 ⊓ cj s0 (Gs 0) ≤ Gs 0 ⊓ Gs 1 := stab_le_P hD hs0 hs00
  have h1 := Subgroup.relIndex_mul_relIndex (Gs 0 ⊓ cj s0 (Gs 0)) (Gs 0 ⊓ Gs 1) (Gs 0) hS
    inf_le_left
  have hne : (((s0 : G) : G ⧸ Gs 0)) ≠ ((q0 * s0 : G) : G ⧸ Gs 0) := by
    intro he
    rw [QuotientGroup.eq] at he
    have h' : s0⁻¹ * q0 * s0 ∈ Gs 0 := by simpa [mul_assoc] using he
    exact hq01 ((fix_iff hD hs0 hs00 hq0).1 h')
  have h2 : (Gs 0 ⊓ cj s0 (Gs 0)).relIndex (Gs 0 ⊓ Gs 1) = 2 := by
    have := ncard_orbit_coset (Gs 0 ⊓ Gs 1) (Gs 0) s0
    rw [orbit_P_s0 hD hs0 hs00 hq0 hq01, Set.ncard_pair hne] at this
    have e : (Gs 0 ⊓ Gs 1) ⊓ cj s0 (Gs 0) = Gs 0 ⊓ cj s0 (Gs 0) :=
      le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hS inf_le_right)
    rw [e] at this
    exact this.symm
  rw [← h1, h2, hn]

theorem ncard_Dlt (hD : IsDSystem .C3 Gs) : (Dlt Gs).ncard = 30 := by
  have := ncard_Dlt_of hD (gqLoc hD).idx01
  omega

end CFSG.Quasithin.H13.I51
