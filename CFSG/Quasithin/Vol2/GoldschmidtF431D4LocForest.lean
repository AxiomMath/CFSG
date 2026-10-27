module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocT
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsLie

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native


@[expose] def InvReach (x : D) : Prop :=
  Relation.ReflTransGen (InvStep d4U d4H d4N) d4z x ∨
    Relation.ReflTransGen (InvStep d4U d4H d4N) d4t x

theorem forest_sound : ∀ (F : List (ℕ × ℕ × ℕ)) (seen : List ℕ),
    (∀ r ∈ seen, ∃ x ∈ d4U, RepE d4E locET.El[r]! x ∧ InvReach x) →
    locForestGo locET seen F = true →
    ∀ r ∈ F.map (·.1), ∃ x ∈ d4U, RepE d4E locET.El[r]! x ∧ InvReach x
  | [], _, _, _ => by simp
  | (j, p, s) :: rest, seen, hseen, h => by
    simp only [locForestGo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hp, hs⟩, hj⟩, hconj⟩, hrest⟩ := h
    obtain ⟨xp, hxpT, hxp, hreach⟩ := hseen p (by simpa using hp)
    obtain ⟨g, hg1, hg2, hgHN⟩ := step_spec hs loc_parts.2.1
    have hrepj : RepE d4E locET.El[j]! (g * xp * g⁻¹) := hconj ▸ repE_conjI hg1 hg2 hxp
    obtain ⟨a, haT, harep⟩ := exists_of_T hj
    have hxjT : g * xp * g⁻¹ ∈ d4U := by
      rw [← eq_of_repE d4E_injective harep hrepj]
      exact haT
    have hstep : InvStep d4U d4H d4N xp (g * xp * g⁻¹) := ⟨hxpT, hxjT, g, hgHN, rfl⟩
    have hnew : ∃ x ∈ d4U, RepE d4E locET.El[j]! x ∧ InvReach x :=
      ⟨_, hxjT, hrepj, hreach.imp (fun h => h.tail hstep) (fun h => h.tail hstep)⟩
    have ih := forest_sound rest (j :: seen) (by
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact hnew
      · exact hseen r hr) hrest
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hnew
    · exact ih r hr

theorem inv_chain_spec : ∀ i ∈ d4U, orderOf i = 2 →
    Relation.ReflTransGen (InvStep d4U d4H d4N) d4z i ∨
      Relation.ReflTransGen (InvStep d4U d4H d4N) d4t i := by
  intro i hi hio
  have h := locT_parts.2.2.2.2.2
  simp only [locInvChain, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hrz, hEz⟩, hrt⟩, hEt⟩, hGo, hcover⟩ := h
  have hroots : ∀ r ∈ [locET.idx z0R, locET.idx t0R],
      ∃ x ∈ d4U, RepE d4E locET.El[r]! x ∧ InvReach x := by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨d4z, d4z_mem_d4U, by rw [hEz]; exact repE_z0R, Or.inl Relation.ReflTransGen.refl⟩
    · have : r = locET.idx t0R := by simpa using hr
      subst this
      exact ⟨d4t, d4t_mem_d4U, by rw [hEt]; exact repE_t0R, Or.inr Relation.ReflTransGen.refl⟩
  have hall := forest_sound _ _ hroots hGo
  obtain ⟨j, hj, hrep⟩ := exists_mem_T hi
  have hinv : locIsInv locET.El[j]! = true := by
    refine (locIsInv_iff (validR_T hj) hrep).2 ⟨?_, ?_⟩
    · have h2 := pow_orderOf_eq_one i
      rw [hio, pow_two] at h2
      exact h2
    · rintro rfl
      rw [orderOf_one] at hio
      omega
  have hc := allLt_spec hcover hj
  simp only [hinv, Bool.not_true, Bool.false_or] at hc
  have hmem : j ∈ [locET.idx z0R, locET.idx t0R] ++ (locForest locET [locET.idx z0R,
      locET.idx t0R]).map (·.1) := by simpa using hc
  have hgood : ∃ x ∈ d4U, RepE d4E locET.El[j]! x ∧ InvReach x := by
    rcases List.mem_append.1 hmem with h1 | h1
    · exact hroots j h1
    · exact hall j h1
  obtain ⟨x, -, hxrep, hxreach⟩ := hgood
  rw [eq_of_repE d4E_injective hxrep hrep] at hxreach
  exact hxreach

end CFSG.Quasithin.D4Hex
