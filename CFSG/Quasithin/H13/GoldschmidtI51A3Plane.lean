module

public import CFSG.Quasithin.H13.GoldschmidtI51A3Line

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

@[expose] def Pl (Gs : Fin 3 → Subgroup G) : Set (G ⧸ Gs 0) :=
  {p | ∃ c ∈ Gs 2, p = ((c : G) : G ⧸ Gs 0)}

omit [Finite G] in
theorem Pl_eq_orbit : Pl Gs = MulAction.orbit ↥(Gs 2) ((1 : G) : G ⧸ Gs 0) := by
  ext p
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, by
      show (((c : G) * 1 : G) : G ⧸ Gs 0) = ((c : G) : G ⧸ Gs 0)
      rw [mul_one]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, by
      show (((c : G) * 1 : G) : G ⧸ Gs 0) = ((c : G) : G ⧸ Gs 0)
      rw [mul_one]⟩

theorem ncard_Pl (hD : IsDSystem D Gs) : (Pl Gs).ncard = 7 := by
  rw [Pl_eq_orbit, ncard_orbit_coset, cj_one, inf_comm]
  exact loc2_index_20 hD

theorem Line_sub_Pl (hD : IsDSystem D Gs) {a : G} (ha : a ∈ Gs 2) : Line Gs a ⊆ Pl Gs := by
  rintro p ⟨s, hs, rfl⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := loc1_prod2' hD s hs
  refine ⟨a * b, (Gs 2).mul_mem ha hb.2, ?_⟩
  rw [← mul_assoc]
  exact mk_mul_G0 hc.1

theorem Pl_closed (hD : IsDSystem D Gs) {x y z : G ⧸ Gs 0} (hl : Ln Gs x y z) (hx : x ∈ Pl Gs)
    (hy : y ∈ Pl Gs) : z ∈ Pl Gs := by
  obtain ⟨hxy, hxz, hyz, g, hxg, hyg, hzg⟩ := hl
  obtain ⟨c1, hc1, rfl⟩ := hx
  obtain ⟨c2, hc2, rfl⟩ := hy
  obtain ⟨a, ha, b, hb, c0, hc0, hdec⟩ :=
    loc2_fano hD (c1⁻¹ * c2) ((Gs 2).mul_mem ((Gs 2).inv_mem hc1) hc2)
  have hc2e : c2 = c1 * a * b * c0 := by
    have := congrArg (fun w => c1 * w) hdec
    simpa [mul_assoc] using this
  have h1 : ((c1 : G) : G ⧸ Gs 0) ∈ Line Gs (c1 * a) :=
    ⟨1, (Gs 1).one_mem, by rw [mul_one, mk_mul_G0 ha.1]⟩
  have h2 : ((c2 : G) : G ⧸ Gs 0) ∈ Line Gs (c1 * a) :=
    ⟨b, hb.1, by rw [hc2e, mk_mul_G0 hc0.1]⟩
  have hL := Line_eq_of_two hD hxy hxg hyg h1 h2
  rw [hL] at hzg
  exact Line_sub_Pl hD ((Gs 2).mul_mem hc1 ha.2) hzg

theorem Pl_meet (hD : IsDSystem .A3 Gs) {x y z : G ⧸ Gs 0} (hl : Ln Gs x y z) :
    x ∈ Pl Gs ∨ y ∈ Pl Gs ∨ z ∈ Pl Gs := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx, hy, hz⟩ := hcon
  have hex : ∀ p : ↥(Pl Gs), ∃ w, Ln Gs x (p : G ⧸ Gs 0) w := fun p =>
    Ln_exists hD (fun h => hx (by rw [h]; exact p.2))
  choose τ hτ using hex
  let T : Set (G ⧸ Gs 0) := {w | w ∉ Pl Gs ∧ w ≠ x}
  have hτT : ∀ p : ↥(Pl Gs), τ p ∈ T := fun p => by
    refine ⟨fun h => hx ?_, (hτ p).2.1.symm⟩
    exact Pl_closed hD (Ln_swap23 (Ln_swap12 (hτ p))) p.2 h
  have hinj : Function.Injective (fun p : ↥(Pl Gs) => (⟨τ p, hτT p⟩ : ↥T)) := by
    intro p p' h
    have h' : τ p = τ p' := congrArg Subtype.val h
    apply Subtype.ext
    exact Ln_uniq hD (Ln_swap23 (hτ p)) (h' ▸ Ln_swap23 (hτ p'))
  have hTcard : Nat.card ↥T ≤ Nat.card ↥(Pl Gs) := by
    have h1 : (insert x (Pl Gs)).ncard = 8 := by
      rw [Set.ncard_insert_of_notMem hx (Set.toFinite _), ncard_Pl hD]
    have h2 := Set.ncard_add_ncard_compl (insert x (Pl Gs))
    have hTe : T = (insert x (Pl Gs))ᶜ := by
      ext w
      simp only [T, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
      exact and_comm
    rw [h1, card_Omega_A3 hD, ← hTe] at h2
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ncard_Pl hD]
    omega
  obtain ⟨⟨p, hp⟩, hpy⟩ := (hinj.bijective_of_nat_card_le hTcard).2
    (⟨y, hy, hl.1.symm⟩ : ↥T)
  have hτy : τ ⟨p, hp⟩ = y := congrArg Subtype.val hpy
  have h3 : Ln Gs x y p := Ln_swap23 (hτy ▸ hτ ⟨p, hp⟩)
  exact hz (Ln_uniq hD hl h3 ▸ hp)

theorem exists_not_mem_Pl (hD : IsDSystem .A3 Gs) : ∃ a : G ⧸ Gs 0, a ∉ Pl Gs := by
  by_contra h
  push Not at h
  have : Pl Gs = Set.univ := Set.eq_univ_of_forall h
  have h7 := ncard_Pl hD
  rw [this, Set.ncard_univ, card_Omega_A3 hD] at h7
  omega

end CFSG.Quasithin.H13.I51
