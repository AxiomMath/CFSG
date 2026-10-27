module

public import CFSG.Quasithin.EmptyFaithful.S1421Q9A
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA12

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem isSylowTwoOf_M (st : Setting1427 T M H K1) : IsSylowTwoOf T M :=
  isSylowTwoOf_of_isSylowTwo st.hyp.sylow st.hyp.m_max.1.2

theorem pCoreOf_M_le_T (st : Setting1427 T M H K1) : pCoreOf 2 M ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_M st)

theorem T_le_normalizer_K (st : Setting1427 T M H K1) :
    T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  st.hStar.1.1.trans (le_normalizer_oTwoUpper H)

theorem T_le_normalizer_inf (st : Setting1427 T M H K1) :
    T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, T_le_normalizer_K st ht⟩

theorem exists_mem_pCore_not_mem_normalizer (st : Setting1427 T M H K1)
    (hO : ¬ pCoreOf 2 M ≤ S1421.sOf T K1) :
    ∃ t : G, t ∈ pCoreOf 2 M ∧ t ∈ T ∧ t ∉ Subgroup.normalizer (K1 : Set G) := by
  by_contra! h
  apply hO
  intro t ht
  exact Subgroup.mem_inf.mpr ⟨pCoreOf_M_le_T st ht, h t ht (pCoreOf_M_le_T st ht)⟩

theorem commutator_mem_inf (st : Setting1427 T M H K1) {t x : G} (ht : t ∈ pCoreOf 2 M)
    (hx : x ∈ M ⊓ oTwoUpper H) : t * x * t⁻¹ * x⁻¹ ∈ T ⊓ oTwoUpper H := by
  have htT : t ∈ T := pCoreOf_M_le_T st ht
  have h1 : x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 M := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M hx.1) t⁻¹).mp
      ((pCoreOf 2 M).inv_mem ht)
    simpa [mul_assoc] using this
  have h2 : t * x * t⁻¹ ∈ oTwoUpper H :=
    (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_K st htT) x).mp hx.2
  have hc : t * x * t⁻¹ * x⁻¹ ∈ oTwoUpper H :=
    (oTwoUpper H).mul_mem h2 ((oTwoUpper H).inv_mem hx.2)
  have hc2 : t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 M := by
    have : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
    rw [this]
    exact (pCoreOf 2 M).mul_mem ht h1
  exact ⟨pCoreOf_M_le_T st hc2, hc⟩

theorem inf_normalizer_le_M (st : Setting1427 T M H K1) (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H)) :
    oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≤ M := by
  obtain ⟨P, P', -, hP, -, hBor, -, -⟩ := hs3.parabolic
  have hTH : T ≤ H := st.hStar.1.1
  set Y : Subgroup G := H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) with hY
  have hTY : T ≤ Y := le_inf hTH (T_le_normalizer_inf st)
  have hYH : Y ≤ H := inf_le_left
  have hYM : Y ≤ M := by
    by_contra hYM
    have hKN : oTwoUpper H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
      obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo st.hyp.sylow
      have hInH : InH (S : Subgroup G) Y := inH_of_le S hTY hYH st.hStar.1
      have hYeq : Y = H := st.hStar.2.2 Y hInH hYH hYM
      intro x hx
      have : x ∈ Y := hYeq ▸ oTwoUpper_le H hx
      exact this.2
    have hKP : oTwoUpper H ≤ P := fun x hx => (hBor ⟨hx, hKN hx⟩).1
    exact hP.2.1 (le_antisymm hP.1.1 hKP)
  exact fun x hx => hYM ⟨oTwoUpper_le H hx.1, hx.2⟩

theorem inf_eq_inf_normalizer (st : Setting1427 T M H K1) (hs3 : ShapeL3Sp4 T K1 (oTwoUpper H)) :
    M ⊓ oTwoUpper H =
      oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  refine le_antisymm (le_inf inf_le_right st.notation_.borel_inf) ?_
  exact fun x hx => ⟨inf_normalizer_le_M st hs3 hx, hx.1⟩

theorem map_conj_swap (st : Setting1427 T M H K1) {P P' : Subgroup G} (hne : P ≠ P')
    (hP : IsMaxParabolic2 (oTwoUpper H) P) (hP' : IsMaxParabolic2 (oTwoUpper H) P')
    (hBor : oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) ≤ P ⊓ P')
    (hK1 : K1 = perfectCore P)
    (hcov : ∀ A : Subgroup G, T ⊓ oTwoUpper H ≤ A → A ≤ oTwoUpper H →
      (A ⋖ oTwoUpper H ↔ A = P ∨ A = P'))
    {t : G} (htT : t ∈ T) (ht : t ∉ Subgroup.normalizer (K1 : Set G)) :
    P.map (MulAut.conj t).toMonoidHom = P' ∧ P'.map (MulAut.conj t).toMonoidHom = P := by
  have hUP : T ⊓ oTwoUpper H ≤ P := fun x hx => (hBor ⟨hx.2, Subgroup.le_normalizer hx⟩).1
  have hUP' : T ⊓ oTwoUpper H ≤ P' := fun x hx => (hBor ⟨hx.2, Subgroup.le_normalizer hx⟩).2
  have hxK := T_le_normalizer_K st htT
  have hxU := T_le_normalizer_inf st htT
  have hcov' : ∀ A : Subgroup G, T ⊓ oTwoUpper H ≤ A → A ≤ oTwoUpper H →
      (A ⋖ oTwoUpper H ↔ A = P' ∨ A = P) := fun A h1 h2 => by
    rw [hcov A h1 h2, or_comm]
  have h1 : P.map (MulAut.conj t).toMonoidHom = P' := by
    rcases Q9.conj_eq_or_eq_of_covBy hcov hUP hP.1.1 hxK hxU with h | h
    · exfalso
      apply ht
      rw [hK1]
      exact normalizer_le_normalizer_perfectCore P (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    · exact h
  refine ⟨h1, ?_⟩
  rcases Q9.conj_eq_or_eq_of_covBy hcov' hUP' hP'.1.1 hxK hxU with h | h
  · exfalso
    apply hne
    have h2 : P'.map (MulAut.conj t).toMonoidHom = P.map (MulAut.conj t).toMonoidHom := by
      rw [h, h1]
    exact (Subgroup.map_injective (MulAut.conj t).injective h2).symm
  · exact h

end QA12

end CFSG.Quasithin
