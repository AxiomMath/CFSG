module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocClass
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocPair
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocV
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442XGen

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

section Model


section Cert


theorem d4_fusion : ∀ u ∈ Subgroup.centralizer ({d4t} : Set D), IsConj d4z u → u ∈ d4V ∨
    ∃ n ∈ d4N, ∃ a ∈ d4U, ∃ b ∈ d4U, u = n * a * n⁻¹ ∧ d4t = n * b * n⁻¹ ∧
      ∃ b' ∈ d4U, Relation.ReflTransGen (PairLink d4U d4H d4N) (a, b) (d4z, b') ∧
        ∀ h ∈ d4H, h * d4t * h⁻¹ ≠ b' := by
  intro u hu hconj
  obtain ⟨i, rfl⟩ := exists_zElt_of_isConj hconj
  have hcov := locF_parts.2.2.1 i.1 (by have := i.2; omega)
  rw [locCz_eq] at hcov
  rcases hcov with h | h | h | h | h
  · exfalso
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hu
    have := (locComm_iff (validR_cz i.2) validR_t0R (repE_zElt i) repE_t0R).2 hc
    rw [this] at h
    exact absurd h (by simp)
  · have hi : i = pt0 := Fin.ext h
    subst hi
    rw [zElt_zero]
    exact Or.inl (mem_d4V_iff.2 (Or.inr (Or.inl rfl)))
  · have hi : i = pt1 := Fin.ext h
    subst hi
    exact Or.inl (mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl))))
  · have hi : i = pt5 := Fin.ext h
    subst hi
    exact Or.inl (mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl))))
  · right
    obtain ⟨hlt, heq⟩ := memR_spec h
    obtain ⟨c, hc, hrep⟩ := exists_conj_mem_of_classTreeOK cGens_hyp' repE_u0 locF_parts.2.1 _ hlt
    rw [heq] at hrep
    have hu' : zElt i = c * d4Word locU0Word * c⁻¹ :=
      eq_of_repE d4E_injective (repE_zElt i) hrep
    have hct : c * d4t = d4t * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (d4Ct_le_centralizer hc)
    obtain ⟨b', hb'U, hb'Q, hchain⟩ := pair_chain_spec
    refine ⟨c, d4Ct_le_d4N hc, d4Word locU0Word, u0_mem_d4U, d4t, d4t_mem_d4U, hu',
      by rw [hct]; group, b', hb'U, hchain, fun h hh heq => hb'Q ?_⟩
    rw [← heq]
    exact d4H_norm_Q h hh d4t d4t_mem_d4Q

theorem d4_Ct_cop : Nat.Coprime (Nat.card (Subgroup.centralizer ({d4t} : Set D))) 65 := by
  rw [centralizer_d4t_eq, card_d4Ct]
  norm_num

theorem d4_Loc442DatumX : ∃ q, CFSG.Quasithin.Loc442DatumX d4H d4N d4U d4z d4t d4V q := by
  obtain ⟨q, hqC, hqA, hqB, hqC', hsq⟩ := exists_q
  have hq : q * q ∈ d4V := by
    rcases hsq with h | h | h <;> rw [h]
    · exact mem_d4V_iff.2 (Or.inr (Or.inl rfl))
    · exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
    · exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨q, ?_⟩
  exact
  { lie := d4_F431LieI
    V_le := d4V_le_centralizer
    V_card := card_d4V
    V_comm := d4V_comm
    V_sq := d4V_sq
    V_norm := fun x hx v hv => d4Ct_norm_V x (centralizer_d4t_eq ▸ hx) v hv
    V_conj := fun v hv hv1 => by
      obtain ⟨x, hx, e⟩ := d4V_conj v hv hv1
      exact ⟨x, centralizer_d4t_eq ▸ hx, e⟩
    q_mem := centralizer_d4t_eq ▸ hqC
    q_comm := fun v hv => by
      rcases mem_d4V_iff.1 hv with rfl | rfl | rfl | rfl
      · simp
      · exact hqA
      · exact hqB
      · exact hqC'
    q_sq := by rw [pow_two]; exact hq
    q_sq_ne := by
      rw [pow_two]
      intro h1
      rcases hsq with h | h | h <;> rw [h] at h1
      · exact d4z_sq.2 h1
      · exact vB_sq.2 h1
      · exact vC_sq.2 h1
    Ct_cop := d4_Ct_cop
    fusion := d4_fusion }

end Cert

end Model

end CFSG.Quasithin.D4Hex
