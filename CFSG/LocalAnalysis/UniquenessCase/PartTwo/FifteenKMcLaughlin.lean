module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLRep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLSym
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLaughlin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module Submodule CFSG.LocalAnalysis.ComponentInitial CFSG.Fischer.Classification.Symplectic
  CFSG.ComponentClassification.OutcomeLocal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem s15k_mclaughlin_main [FiniteDimensional (ZMod 2) V]
    (hn : 1 ≤ finrank (ZMod 2) V) (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hgen : ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (∀ t ∈ S, IsF2Transvection t) ∧ G = Subgroup.closure S)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ G, ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    G = ⊤ ∨
      (Even (finrank (ZMod 2) V) ∧ ∃ f : LinearMap.BilinForm (ZMod 2) V,
        f.Nondegenerate ∧ f.IsAlt ∧ G = bilinIsometryGroup f) ∨
      (Even (finrank (ZMod 2) V) ∧ 4 ≤ finrank (ZMod 2) V ∧ ∃ Q : QuadraticForm (ZMod 2) V,
        (QuadraticMap.polarBilin Q).Nondegenerate ∧
          G = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
            (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom ∧
          (6 ≤ finrank (ZMod 2) V ∨
            ¬ ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)) ∨
      (Even (finrank (ZMod 2) V) ∧
        ((∃ β : V ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) V + 1),
            G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (sumZeroRep (finrank (ZMod 2) V + 1)).range) ∨
          ∃ β : V ≃ₗ[ZMod 2] sumZero (finrank (ZMod 2) V + 2) ⧸ onesLine (finrank (ZMod 2) V + 2),
            G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (heartRep (finrank (ZMod 2) V + 2)).range)) := by
  by_cases h1 : finrank (ZMod 2) V = 1
  · left
    refine eq_top_iff.mpr fun g _ => ?_
    rw [eq_one_of_finrank_eq_one h1 g]
    exact G.one_mem
  by_cases hdih : ∃ (φ ψ : Dual (ZMod 2) V) (a b : V), a ≠ 0 ∧ ψ ≠ 0 ∧ InG G φ a ∧
      InG G ψ b ∧ φ b = 1 ∧ ψ a = 0
  · left
    obtain ⟨φ, ψ, a, b, ha, hψ, hφa, hψb, hφb, hψa⟩ := hdih
    exact eq_top_of_dihedral hgen hirr ha hψ hφa hψb hφb hψa
  have hno : NoDihedralPair G := fun φ ψ a b ha hψ hφa hψb hφb hψa =>
    hdih ⟨φ, ψ, a, b, ha, hψ, hφa, hψb, hφb, hψa⟩
  have hne := centres_nonempty hgen hirr (by omega)
  obtain ⟨P, hPD, hF4, hF5⟩ := exists_preConfig hgen hirr hno hne
  have hBnd : P.b.Nondegenerate :=
    ⟨fun u hu => P.nondeg u hu, fun u hu => P.nondeg u fun v => by rw [P.comm]; exact hu v⟩
  have heven : Even (finrank (ZMod 2) V) :=
    CFSG.PreuniquenessRankFour.Helpers.alternating_nondegenerate_form_finrank_even P.b
      P.self_eq_zero hBnd
  rcases P.toSympConfig.trichotomy with ⟨hall, -⟩ | ⟨⟨Q, hpol, hQ⟩, x, hx, y, hy, hxy, hbxy⟩ | hTN
  ·
    right; left
    have hall' : ∀ v, v ∈ P.D ↔ v ≠ 0 := hall
    refine ⟨heven, P.b, hBnd, P.self_eq_zero, ?_⟩
    exact eq_bilinIsometryGroup_of_forall hgen P.self_eq_zero P.comm P.nondeg hF4 hF5
      fun v hv => hPD ▸ (hall' v).mpr hv
  ·
    right; right; left
    have hpol' : ∀ u v, QuadraticMap.polar Q u v = P.b u v := hpol
    have hQ' : ∀ v, v ∈ P.D ↔ Q v = 1 := hQ
    have hQc : ∀ v, v ∈ centres G ↔ Q v = 1 := fun v => hPD ▸ hQ' v
    have hx' : x ∈ P.D := hx
    have hy' : y ∈ P.D := hy
    have hbxy' : P.b x y = 0 := hbxy
    have h3 : 3 ≤ finrank (ZMod 2) V := by
      have hx0 : x ≠ 0 := P.ne_zero_of_mem hx'
      obtain ⟨z, -, hzx⟩ := P.exists_mem_b_eq_one hx0
      have hyx : y ∉ span (ZMod 2) {x} := by
        intro hmem
        obtain ⟨c, rfl⟩ := mem_span_singleton.mp hmem
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · exact P.ne_zero_of_mem hy' (zero_smul _ _)
        · exact hxy (one_smul _ _).symm
      have hz : z ∉ span (ZMod 2) {x} ⊔ span (ZMod 2) {y} := by
        intro hmem
        obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup.mp hmem
        obtain ⟨c, rfl⟩ := mem_span_singleton.mp hu
        obtain ⟨c', rfl⟩ := mem_span_singleton.mp hw
        rw [P.b_add_left, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
          P.self_eq_zero, P.comm y x, hbxy', smul_zero, smul_zero, add_zero] at hzx
        exact zero_ne_one hzx
      have h2 := finrank_sup_span_of_notMem hyx
      have h3' := finrank_sup_span_of_notMem hz
      rw [finrank_span_singleton hx0] at h2
      have := Submodule.finrank_le (span (ZMod 2) {x} ⊔ span (ZMod 2) {y} ⊔ span (ZMod 2) {z})
      omega
    have hE : 5 ≤ finrank (ZMod 2) V ∨
        ¬ ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
      by_cases h5 : 5 ≤ finrank (ZMod 2) V
      · exact Or.inl h5
      · right
        have h4 : finrank (ZMod 2) V = 4 := by
          obtain ⟨k, hk⟩ := heven
          omega
        exact P.toSympConfig.not_exists_totallySingular h4 hpol hQ
    have hpb : QuadraticMap.polarBilin Q = P.b := LinearMap.ext₂ fun u v => hpol' u v
    refine ⟨heven, by obtain ⟨k, hk⟩ := heven; omega, Q, ?_,
      eq_comap_orthogonalGroup hgen P.self_eq_zero P.comm P.nondeg hF4 hF5
        hpol' hQc h3 hE, ?_⟩
    · rw [hpb]
      exact hBnd
    · rcases hE with h5 | hE'
      · left
        obtain ⟨k, hk⟩ := heven
        omega
      · exact Or.inr hE'
  ·
    right; right; right
    exact ⟨heven, exists_heart_conj hgen P hPD hF4 hF5 hTN hn⟩

theorem rMcLaughlin_holds : RMcLaughlin := by
  intro W _ _ hW J R hJ hirr hfaith hgen
  obtain ⟨D⟩ := s15k_mcl_nonempty hW hirr.2.1 hfaith
  haveI : FiniteDimensional (ZMod 2) D.V := Module.Finite.of_finite
  have hn : 1 ≤ Module.finrank (ZMod 2) D.V := by
    obtain ⟨r, hr, hr1⟩ := SetLike.exists_of_lt hirr.1
    have hne : D.e ⟨r, hr⟩ ≠ 1 := by
      intro h
      apply hr1
      have h1 : (⟨r, hr⟩ : ↥R) = 1 := D.e.injective (h.trans (map_one D.e).symm)
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h1
    haveI : Nontrivial D.V :=
      ⟨⟨Multiplicative.toAdd (D.e ⟨r, hr⟩), 0, fun h => hne (Multiplicative.toAdd.injective h)⟩⟩
    exact Module.finrank_pos
  have h2 : 2 ≤ Module.finrank (ZMod 2) D.V := by
    by_contra hlt
    have h1 : Module.finrank (ZMod 2) D.V = 1 := by omega
    obtain ⟨j, hj1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJ
    refine hj1 (D.inj ?_)
    rw [map_one]
    exact eq_one_of_finrank_eq_one h1 _
  obtain ⟨S, hS, hSeq⟩ := s15k_mcl_gen D hgen
  have hirr' := s15k_mcl_irr D hirr
  unfold s15JNat
  rcases s15k_mclaughlin_main hn D.ρ.range ⟨S, hS, hSeq⟩ hirr' with
    htop | ⟨hev, f, hnd, halt, hf⟩ | ⟨hev, h4, Q, hnd, hQ, hE⟩ | ⟨hev, hsym⟩
  · exact Or.inl (s15k_mcl_top D h2 htop)
  · rcases s15k_mcl_sp D hev h2 f hnd halt hf with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases s15k_mcl_orth D hev h4 Q hnd hQ hE with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases hsym with ⟨β, hβ⟩ | ⟨β, hβ⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (s15k_mcl_sym_odd D hev h2 β hβ))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (s15k_mcl_sym_even D hev h2 β hβ))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
