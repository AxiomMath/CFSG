module

public import CFSG.Quasithin.MS93.MSPOpp
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.Quasithin.MS93.MSP Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem two_le_card_field : 2 ≤ Nat.card F := by
  have : Nontrivial F := inferInstance
  have := Finite.one_lt_card (α := F)
  omega

theorem eq_qLine_of_count {E : Subgroup (Sp4 F)} (hE : IsPGroup 2 E)
    (hcount : Nat.card F * Nat.card (V4 F) ≤ Nat.card E * Nat.card (fixSp E))
    (hE3 : Nat.card E ≤ Nat.card F ^ 3) :
    ∃ l : Submodule F (V4 F), IsLine l ∧ fixSp E = l ∧ E = qLine l := by
  set q := Nat.card F with hq
  have hq2 : 2 ≤ q := two_le_card_field
  set d := Module.finrank F (fixSp E) with hd
  have hfix : Nat.card (fixSp E) = q ^ d := card_fixSp E
  rw [card_V4, hfix] at hcount
  have hd2 : 2 ≤ d := by
    by_contra hlt
    have h1 : q * q ^ 4 ≤ q ^ 3 * q ^ d :=
      hcount.trans (Nat.mul_le_mul_right _ hE3)
    rw [← pow_succ', ← pow_add] at h1
    have := (Nat.pow_le_pow_iff_right hq2).1 h1
    omega
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot, one_mul] at hcount
    have h4 : d ≤ 4 := by
      have := Submodule.finrank_le (fixSp (⊥ : Subgroup (Sp4 F)))
      simpa using this
    have h1 : q ^ 5 ≤ q ^ 4 := by
      rw [pow_succ']
      exact hcount.trans (Nat.pow_le_pow_right (by omega) h4)
    have := (Nat.pow_le_pow_iff_right hq2).1 h1
    omega
  have hd3 : d ≠ 4 := fun h4 => by
    refine hE1 (fixSp_eq_top_iff.1 (Submodule.eq_top_of_finrank_eq ?_))
    rw [← hd, h4]
    simp
  have hd4 : d ≤ 4 := by
    have := Submodule.finrank_le (fixSp E)
    simpa using this
  rcases (show d = 2 ∨ d = 3 by omega) with h2 | h3
  · obtain ⟨hl, hEl⟩ := isLine_fixSp_of_finrank_two hE h2
    refine ⟨fixSp E, hl, rfl, Subgroup.eq_of_le_of_card_ge hEl ?_⟩
    rw [card_qLine hl]
    rw [h2] at hcount
    have h1 : q * q ^ 4 = q ^ 3 * q ^ 2 := by ring
    rw [h1] at hcount
    exact Nat.le_of_mul_le_mul_right hcount (by positivity)
  · obtain ⟨p, hp, -, hEp⟩ := exists_point_of_finrank_fixSp_three h3
    have hEq : Nat.card E ≤ q := by
      rw [hq, ← card_xPoint hp]
      exact Subgroup.card_le_of_le hEp
    rw [h3] at hcount
    have h1 : q * q ^ 4 ≤ q * q ^ 3 := hcount.trans (Nat.mul_le_mul_right _ hEq)
    have h2 := Nat.le_of_mul_le_mul_left h1 (by omega)
    have := (Nat.pow_le_pow_iff_right hq2).1 h2
    omega

omit [Finite F] [CharP F 2] in
theorem exists_mulVec_eq_add {l : Submodule F (V4 F)} (hl : IsLine l) :
    ∃ c : V4 F, c ≠ 0 ∧ ∀ v : V4 F, form F c v ≠ 0 → ∃ g ∈ qLine l, mat g *ᵥ v = v + c := by
  have hl0 : l ≠ ⊥ := by
    rintro rfl
    have := hl.1
    rw [finrank_bot] at this
    omega
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hl0
  refine ⟨c, hc0, fun v hv => ⟨transv c (form F c v)⁻¹, transv_mem_qLine hl hc _, ?_⟩⟩
  rw [transv_mulVec, inv_mul_cancel₀ hv, one_smul]

section Coord

variable {S : Type} [CommGroup S] {X' : Subgroup (MulAut S)}

theorem offender_coord (φ : ↥X' →* Sp4 F) (θ : S ≃* Multiplicative (V4 F))
    (hθ : ∀ (x : ↥X') (s : S), Multiplicative.toAdd (θ ((x : MulAut S) s)) =
      mat (φ x) *ᵥ Multiplicative.toAdd (θ s))
    {E : Subgroup (MulAut S)} (hEX : E ≤ X') (hE : IsPGroup 2 E)
    (hcount : Nat.card F * Nat.card S ≤ Nat.card E * Nat.card (fixV E))
    (hE3 : Nat.card E ≤ Nat.card F ^ 3) :
    Nat.card S = Nat.card F ^ 2 * Nat.card (fixV E) ∧ Nat.card E = Nat.card F ^ 3 ∧
      ∃ c : S, c ≠ 1 ∧ ∃ H : Subgroup S, H ≠ ⊤ ∧ ∀ s ∉ H, ∃ e ∈ E, e s = s * c := by
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine MulEquiv.ext fun s => θ.injective (Multiplicative.toAdd.injective ?_)
    rw [hθ, hx, mat_one, Matrix.one_mulVec]
    rfl
  set Eh : Subgroup (Sp4 F) := (E.subgroupOf X').map φ with hEh
  have hcardE : Nat.card Eh = Nat.card E := by
    rw [hEh, Subgroup.card_map_of_injective hφi]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hfixiff : ∀ s : S, s ∈ fixV E ↔ Multiplicative.toAdd (θ s) ∈ fixSp Eh := by
    intro s
    rw [mem_fixV, mem_fixSp]
    constructor
    · rintro hs _ ⟨x, hx, rfl⟩
      rw [← hθ, hs _ (Subgroup.mem_subgroupOf.1 hx)]
    · intro hs e he
      have h1 := hs (φ ⟨e, hEX he⟩) ⟨⟨e, hEX he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      rw [← hθ] at h1
      exact θ.injective (Multiplicative.toAdd.injective h1)
  have hcardfix : Nat.card (fixV E) = Nat.card (fixSp Eh) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨Multiplicative.toAdd (θ s), (hfixiff s).1 s.2⟩
        invFun := fun v => ⟨θ.symm (Multiplicative.ofAdd v), (hfixiff _).2 (by simp)⟩
        left_inv := fun s => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  have hcardS : Nat.card S = Nat.card (V4 F) :=
    Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)
  have hEhp : IsPGroup 2 Eh := (hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEX).symm).map φ
  rw [hcardS, ← hcardE, hcardfix] at hcount
  rw [← hcardE] at hE3
  obtain ⟨l, hl, hfl, hEl⟩ := eq_qLine_of_count hEhp hcount hE3
  have hfixcard : Nat.card (fixSp Eh) = Nat.card F ^ 2 := by
    rw [card_fixSp, hfl, hl.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcardS, card_V4, hcardfix, hfixcard]
    ring
  · rw [← hcardE, hEl, card_qLine hl]
  · obtain ⟨c, hc0, hc⟩ := exists_mulVec_eq_add hl
    refine ⟨θ.symm (Multiplicative.ofAdd c), fun h1 => hc0 ?_, ?_⟩
    · have := congrArg (fun s => Multiplicative.toAdd (θ s)) h1
      simpa using this
    let H : Subgroup S :=
      { carrier := {s | form F c (Multiplicative.toAdd (θ s)) = 0}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          have ha' : form F c (Multiplicative.toAdd (θ a)) = 0 := ha
          have hb' : form F c (Multiplicative.toAdd (θ b)) = 0 := hb
          show form F c (Multiplicative.toAdd (θ (a * b))) = 0
          rw [map_mul, toAdd_mul, map_add, ha', hb', add_zero]
        inv_mem' := fun {a} ha => by
          have ha' : form F c (Multiplicative.toAdd (θ a)) = 0 := ha
          show form F c (Multiplicative.toAdd (θ a⁻¹)) = 0
          rw [map_inv, toAdd_inv, map_neg, ha', neg_zero] }
    refine ⟨H, fun hH => ?_, fun s hs => ?_⟩
    · obtain ⟨y, hy⟩ := exists_form_eq_one hc0
      have hmem : θ.symm (Multiplicative.ofAdd y) ∈ H := hH ▸ Subgroup.mem_top _
      have : form F c y = 0 := by simpa [H] using hmem
      rw [hy] at this
      exact one_ne_zero this
    · have hv : form F c (Multiplicative.toAdd (θ s)) ≠ 0 := hs
      obtain ⟨g, hg, hgv⟩ := hc _ hv
      rw [← hEl] at hg
      obtain ⟨x, hx, rfl⟩ := hg
      refine ⟨x, Subgroup.mem_subgroupOf.1 hx, θ.injective (Multiplicative.toAdd.injective ?_)⟩
      rw [hθ, hgv, map_mul, toAdd_mul, MulEquiv.apply_symm_apply, toAdd_ofAdd]

end Coord

end CFSG.Quasithin.MS93.S36E
