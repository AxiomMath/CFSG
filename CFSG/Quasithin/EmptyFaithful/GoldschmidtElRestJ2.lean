module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestJ2Out
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2

public section

namespace CFSG.Quasithin.ModH

open CFSG.Blueprint CFSG.Open CFSG.QuasithinUnique CFSG.ComponentClassification
  CFSG.ComponentClassification.J2Cover CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Sporadic.J2 CFSG.Sporadic.Th.Native

theorem j2_center_data :
    ∃ (Q : Subgroup J) (zJ : J), IsSylowTwoOf Q ⊤ ∧
      ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = zJ := by
  have h := center_closure_of_baseCertS (n := 315) (List.range 315)
    (fun b hb => List.mem_range.mp hb) base_of_faithful (a : J) (b : J) j2Prog j2_valid j2Qp
    143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 4725
    (by rw [card_J]; norm_num) (by decide) (by rw [j2_tab_a, j2_tab_b]; exact j2_cert)
  exact ⟨_, _, h.1, h.2⟩

theorem pointwise_j2_P
    (hCS : ∀ T : Subgroup ↥J2Cover.P, IsSylowTwoOf T ⊤ → ∀ x y : ↥J2Cover.P, x ∈ T → y ∈ T →
      (∀ t ∈ T, x * t = t * x) → (∀ t ∈ T, y * t = t * y) → x = 1 ∨ y = 1 ∨ x = y) :
    ∀ T : Subgroup ↥J2Cover.P, IsSylowTwoOf T ⊤ → ∀ α : MulAut ↥J2Cover.P, (∀ t ∈ T, α t = t) →
      ∃ z ∈ T, (∀ t ∈ T, z * t = t * z) ∧ ∀ g, α g = z * g * z⁻¹ := by
  intro T hT α hα
  have hTc : Nat.card T = 128 := by
    have := card_eq_pow_of_isSylowTwoOf_top hT (a := 7) (m := 4725) (by rw [card_P]; norm_num)
      (by norm_num)
    simpa using this
  obtain ⟨r, hr⟩ := rConj_bijective.2 α
  have hTmc : Nat.card (T.map J2Cover.P.subtype) = 128 := by
    rw [Subgroup.card_map_of_injective J2Cover.P.subtype_injective, hTc]
  have hTmP : T.map J2Cover.P.subtype ≤ J2Cover.P := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hrcomm : ∀ x ∈ T.map J2Cover.P.subtype, (r : Equiv.Perm (Fin 315)) * x = x * r := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := congrArg (fun a : MulAut ↥J2Cover.P => ((a t : ↥J2Cover.P) :
      Equiv.Perm (Fin 315))) hr
    simp only [rConj_apply] at h1
    rw [hα t ht] at h1
    calc (r : Equiv.Perm (Fin 315)) * t = (r * t * (r : Equiv.Perm (Fin 315))⁻¹) * r := by group
      _ = t * r := by rw [h1]
  by_cases hrP : (r : Equiv.Perm (Fin 315)) ∈ J2Cover.P
  · have hmem := j2_comm_sylow_mem hTmP hTmc hrP hrcomm
    obtain ⟨y, hy, hyr⟩ := hmem
    have hyz : y = ⟨r, hrP⟩ := Subtype.ext hyr
    subst hyz
    refine ⟨⟨r, hrP⟩, hy, fun t ht => Subtype.ext (hrcomm t ⟨t, ht, rfl⟩), fun g => ?_⟩
    have hrr : rConj ⟨(r : Equiv.Perm (Fin 315)), P_le_R hrP⟩ = α := hr
    rw [rConj_of_mem_P hrP] at hrr
    rw [← hrr, MulAut.conj_apply]
  · exfalso
    refine j2_no_outer_comm_sylow hTmP hTmc ?_ r.2 hrP hrcomm
    rintro _ _ ⟨x', hx', rfl⟩ ⟨y', hy', rfl⟩ hxc hyc
    have hx'c : ∀ t ∈ T, x' * t = t * x' := fun t ht =>
      Subtype.ext (hxc t ⟨t, ht, rfl⟩)
    have hy'c : ∀ t ∈ T, y' * t = t * y' := fun t ht =>
      Subtype.ext (hyc t ⟨t, ht, rfl⟩)
    rcases hCS T hT x' y' hx' hy' hx'c hy'c with h | h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl (by simp [h]))
    · exact Or.inr (Or.inr (by simp [h]))

theorem pointwise_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ → ∀ α : MulAut Y, (∀ t ∈ T, α t = t) →
      ∃ z ∈ T, (∀ t ∈ T, z * t = t * z) ∧ ∀ g, α g = z * g * z⁻¹) :
    ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → ∀ α : MulAut X, (∀ t ∈ T, α t = t) →
      ∃ z ∈ T, (∀ t ∈ T, z * t = t * z) ∧ ∀ g, α g = z * g * z⁻¹ := by
  intro T hT α hα
  obtain ⟨z', ⟨t₀, ht₀, rfl⟩, hz'c, hz'⟩ := hY (T.map e.toMonoidHom) (isSylowTwoOf_map_equiv e hT)
    (MulAut.congr e α) (by
      rintro _ ⟨t, ht, rfl⟩
      simp [MulAut.congr_apply, hα t ht])
  refine ⟨t₀, ht₀, fun t ht => e.injective ?_, fun g => ?_⟩
  · simpa using hz'c (e t) ⟨t, ht, rfl⟩
  · apply e.injective
    have h := hz' (e g)
    simpa [MulAut.congr_apply] using h

end CFSG.Quasithin.ModH
