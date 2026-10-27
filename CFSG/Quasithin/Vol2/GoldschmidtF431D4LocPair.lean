module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocQ
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Gen

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native


@[expose] def PairRep (p : ℕ × ℕ) (x y : D) : Prop :=
  x ∈ d4U ∧ y ∈ d4U ∧ RepE d4E locET.El[p.1]! x ∧ RepE d4E locET.El[p.2]! y ∧
    Relation.ReflTransGen (PairLink d4U d4H d4N) (d4Word locU0Word, d4t) (x, y)

theorem pair_sound : ∀ (F : List ((ℕ × ℕ) × (ℕ × ℕ) × ℕ)) (seen : List (ℕ × ℕ)),
    (∀ r ∈ seen, ∃ x y, PairRep r x y) → locPairGo locET seen F = true →
    ∀ r ∈ F.map (·.1), ∃ x y, PairRep r x y
  | [], _, _, _ => by simp
  | (j, p, s) :: rest, seen, hseen, h => by
    simp only [locPairGo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hp, hs⟩, hj1⟩, hj2⟩, hconj1⟩, hconj2⟩, hrest⟩ := h
    obtain ⟨xp, yp, hxpT, hypT, hxp, hyp, hreach⟩ := hseen p (by simpa using hp)
    obtain ⟨g, hg1, hg2, hgHN⟩ := step_spec hs loc_parts.2.1
    have hrep1 : RepE d4E locET.El[j.1]! (g * xp * g⁻¹) := hconj1 ▸ repE_conjI hg1 hg2 hxp
    have hrep2 : RepE d4E locET.El[j.2]! (g * yp * g⁻¹) := hconj2 ▸ repE_conjI hg1 hg2 hyp
    obtain ⟨a, haT, harep⟩ := exists_of_T hj1
    obtain ⟨b, hbT, hbrep⟩ := exists_of_T hj2
    have hxjT : g * xp * g⁻¹ ∈ d4U := by
      rw [← eq_of_repE d4E_injective harep hrep1]
      exact haT
    have hyjT : g * yp * g⁻¹ ∈ d4U := by
      rw [← eq_of_repE d4E_injective hbrep hrep2]
      exact hbT
    have hstep : PairLink d4U d4H d4N (xp, yp) (g * xp * g⁻¹, g * yp * g⁻¹) :=
      ⟨hxpT, hypT, hxjT, hyjT, g, hgHN, rfl, rfl⟩
    have hnew : ∃ x y, PairRep j x y :=
      ⟨_, _, hxjT, hyjT, hrep1, hrep2, hreach.tail hstep⟩
    have ih := pair_sound rest (j :: seen) (by
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · exact hnew
      · exact hseen r hr) hrest
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hnew
    · exact ih r hr

theorem u0_mem_d4U : d4Word locU0Word ∈ d4U := d4Word_mem_U locU0Word (by decide)

theorem repE_u0 : RepE d4E (wordR d4Gens locU0Word) (d4Word locU0Word) :=
  repE_d4Word (by decide)

theorem pair_chain_spec : ∃ b' ∈ d4U, b' ∉ d4Q ∧
    Relation.ReflTransGen (PairLink d4U d4H d4N) (d4Word locU0Word, d4t) (d4z, b') := by
  have h := locF_parts.2.2.2.2
  simp only [locPairChain, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.any_eq_true] at h
  obtain ⟨⟨⟨⟨hia, hEa⟩, hib⟩, hEb⟩, hGo, p, hp, ⟨⟨hp1, hp2⟩, hEz⟩, hnq⟩ := h
  have hroot : ∃ x y, PairRep (locET.idx (wordR d4Gens locU0Word), locET.idx t0R) x y :=
    ⟨d4Word locU0Word, d4t, u0_mem_d4U, d4t_mem_d4U, by rw [hEa]; exact repE_u0,
      by rw [hEb]; exact repE_t0R, Relation.ReflTransGen.refl⟩
  have hall := pair_sound _ _ (by
    intro r hr
    rw [List.mem_singleton.1 hr]
    exact hroot) hGo
  have hp' : ∃ x y, PairRep p x y := by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hroot
    · exact hall p hp
  obtain ⟨x, y, hxT, hyT, hxrep, hyrep, hreach⟩ := hp'
  have hx : x = d4z := eq_of_repE d4E_injective hxrep (by rw [hEz]; exact repE_z0R)
  subst hx
  refine ⟨y, hyT, fun hyQ => ?_, hreach⟩
  have := memR_of_mem_Q (validR_T hp2) hyrep hyQ
  rw [this] at hnq
  exact absurd hnq (by simp)

end CFSG.Quasithin.D4Hex
