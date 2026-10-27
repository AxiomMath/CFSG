module

public import CFSG.Quasithin.Background.SmithC27RDefs

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem sylow_two_isSylowTwoOf_top (P : Sylow 2 X) : IsSylowTwoOf (P : Subgroup X) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [show ((P : Subgroup X).subgroupOf ⊤).index = (P : Subgroup X).index from
    Subgroup.relIndex_top_right _]
  exact P.not_dvd_index

omit [Finite X] in
theorem exists_sylow_two_coe_eq {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
  exact ⟨hS.2.1.toSylow hodd, IsPGroup.toSylow_coe hS.2.1 hodd⟩

theorem exists_map_conj_eq_of_sylow {S T : Subgroup X} (hS : IsSylowTwoOf S ⊤)
    (hT : IsSylowTwoOf T ⊤) : ∃ g : X, S.map (MulAut.conj g).toMonoidHom = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := exists_sylow_two_coe_eq hS
  obtain ⟨Q, rfl⟩ := exists_sylow_two_coe_eq hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  rfl

theorem exists_isCoatom_ge {M : Subgroup X} (hM : M ≠ ⊤) : ∃ C : Subgroup X, IsCoatom C ∧ M ≤ C :=
  (IsCoatomic.eq_top_or_exists_le_coatom M).resolve_left hM

end Sylow

theorem eq_of_inf_normalizer_le_of_isPGroup {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Q U : Subgroup G} [Finite Q] (hQ : IsPGroup p Q) (hUQ : U ≤ Q)
    (h : Q ⊓ Subgroup.normalizer (U : Set G) ≤ U) : U = Q := by
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  by_contra hne
  have hlt : U.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hUQ ?_)
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ U.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨x, hxN, hxU⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (G := ↥Q) (U.subgroupOf Q) hlt)
  refine hxU (h ⟨x.2, ?_⟩)
  rw [← Subgroup.subgroupOf_normalizer_eq hUQ] at hxN
  exact hxN

theorem isRadicalParabolic_top_of_holds {X : Type} [Group X] [Finite X]
    (h : CFSG.LieType.BorelTits.Holds X 2) : IsRadicalParabolic (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro U _ hU1 hU2 hUO
  rw [top_inf_eq] at hUO ⊢
  obtain ⟨S, P, -, hNP, -, hUP, hSP⟩ := h U hU1 hU2
  have hQ2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hPQ : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hcore : pCoreOf 2 P ⊓ Subgroup.normalizer (U : Set X) ≤ U := by
    refine le_trans ?_ hUO.le
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun g hg => ?_)
      (hQ2.to_le inf_le_left)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.mp (hPQ (hNP hg)) x)
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer (H := Subgroup.normalizer (U : Set X)) hg) x)
    simp only [Subgroup.mem_inf]
    exact and_congr h1 h2
  have hUeq : U = pCoreOf 2 P := eq_of_inf_normalizer_le_of_isPGroup hQ2 hUP hcore
  refine ⟨le_top, S, sylow_two_isSylowTwoOf_top S, ?_⟩
  rw [top_inf_eq]
  refine hSP.trans fun g hg => ?_
  rw [hUeq]
  exact hPQ hg

section Maximal

variable {X : Type} [Group X]

theorem maxParabolicMaximal_of_isCoatom
    (h : ∀ P : Subgroup X, IsParabolic2 ⊤ P → ¬ IsBorelIn ⊤ P → P ≠ ⊤ → IsCoatom P) :
    MaxParabolicMaximal (⊤ : Subgroup X) := by
  intro P hP hPB hPt
  have hc := h P hP hPB hPt
  have hY : ∀ Y : Subgroup X, P ≤ Y → Y ≠ ⊤ → Y = P := fun Y hPY hYt =>
    ((hc.le_iff.mp hPY).resolve_left hYt)
  exact ⟨⟨hP, hPt, fun Q _ hQt hPQ => hY Q hPQ hQt⟩, fun Y hPY hYt _ => hY Y hPY hYt⟩

theorem maxParabolicMaximal_top_of_forall_sylow
    (h : ∀ U : Subgroup X, IsSylowTwoOf U ⊤ → ∀ M : Subgroup X,
      Subgroup.normalizer (U : Set X) ≤ M → M ≠ ⊤ →
        M = Subgroup.normalizer (U : Set X) ∨ IsCoatom M) :
    MaxParabolicMaximal (⊤ : Subgroup X) := by
  refine maxParabolicMaximal_of_isCoatom fun P hP hPB hPt => ?_
  obtain ⟨-, S, hS, hSP⟩ := hP
  rw [top_inf_eq] at hSP
  refine (h S hS P hSP hPt).resolve_left fun hPeq => hPB ⟨S, hS, ?_⟩
  rw [top_inf_eq]
  exact hPeq

theorem maxParabolicMaximal_top_of_sylow [Finite X] {U₀ : Subgroup X} (hU₀ : IsSylowTwoOf U₀ ⊤)
    (h : ∀ M : Subgroup X, Subgroup.normalizer (U₀ : Set X) ≤ M → M ≠ ⊤ →
        M = Subgroup.normalizer (U₀ : Set X) ∨ IsCoatom M) :
    MaxParabolicMaximal (⊤ : Subgroup X) := by
  refine maxParabolicMaximal_top_of_forall_sylow fun U hU M hNM hMt => ?_
  obtain ⟨g, rfl⟩ := exists_map_conj_eq_of_sylow hU₀ hU
  set e : X ≃* X := MulAut.conj g
  have hN : Subgroup.normalizer ((U₀.map e.toMonoidHom : Subgroup X) : Set X) =
      (Subgroup.normalizer (U₀ : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq U₀ e).symm
  have hback : (M.map e.symm.toMonoidHom).map e.toMonoidHom = M := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id M
    ext x
    simp
  have hNM' : Subgroup.normalizer (U₀ : Set X) ≤ M.map e.symm.toMonoidHom := by
    rw [← (MulEquiv.mapSubgroup e).le_iff_le]
    change (Subgroup.normalizer (U₀ : Set X)).map e.toMonoidHom ≤
      (M.map e.symm.toMonoidHom).map e.toMonoidHom
    rw [hback, ← hN]
    exact hNM
  have hMt' : M.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hMt
    rw [← hback, htop]
    exact Subgroup.map_top_of_surjective _ e.surjective
  rcases h _ hNM' hMt' with h1 | h1
  · left
    rw [← hback, h1, hN]
  · right
    rw [← hback]
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) _).mpr h1

end Maximal

@[expose] def ParabolicIsBorel {Γ : Type} [Group Γ] (L : Subgroup Γ) : Prop :=
  ∀ P : Subgroup Γ, IsParabolic2 L P → P ≠ L → IsBorelIn L P

section Transport

variable {A B : Type} [Group A] [Group B]

theorem parabolicIsBorel_map_iff (ι : A →* B) (hι : Function.Injective ι) (L : Subgroup A) :
    ParabolicIsBorel (L.map ι) ↔ ParabolicIsBorel L := by
  have hinj := Subgroup.map_injective hι
  constructor
  · intro h P hP hPL
    exact (isBorelIn_map_iff ι hι _ _).1 (h (P.map ι) ((SBd3T.isParabolic2_map_iff ι hι _ _).2 hP)
      (hinj.ne_iff.2 hPL))
  · intro h P' hP' hP'L
    obtain ⟨P, hPL, rfl⟩ := exists_eq_map_of_le_map hι hP'.1
    exact (isBorelIn_map_iff ι hι _ _).2 (h P ((SBd3T.isParabolic2_map_iff ι hι _ _).1 hP')
      (hinj.ne_iff.1 hP'L))

theorem parabolicIsBorel_iff_top (L : Subgroup A) :
    ParabolicIsBorel L ↔ ParabolicIsBorel (⊤ : Subgroup ↥L) := by
  rw [← parabolicIsBorel_map_iff L.subtype L.subtype_injective ⊤, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem parabolicIsBorel_congr {L : Subgroup A} {L' : Subgroup B} (e : ↥L ≃* ↥L') :
    ParabolicIsBorel L ↔ ParabolicIsBorel L' := by
  rw [parabolicIsBorel_iff_top L, parabolicIsBorel_iff_top L',
    ← parabolicIsBorel_map_iff e.toMonoidHom e.injective ⊤, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.surjective]

end Transport

theorem parabolicIsBorel_top_of_sylow {X : Type} [Group X] [Finite X] {U₀ : Subgroup X}
    (hU₀ : IsSylowTwoOf U₀ ⊤)
    (h : ∀ M : Subgroup X, U₀ ≤ M → M ≠ ⊤ → M ≤ Subgroup.normalizer (U₀ : Set X)) :
    ParabolicIsBorel (⊤ : Subgroup X) := by
  intro P hP hPt
  obtain ⟨-, S, hS, hSP⟩ := hP
  rw [top_inf_eq] at hSP
  obtain ⟨g, rfl⟩ := exists_map_conj_eq_of_sylow hU₀ hS
  set e : X ≃* X := MulAut.conj g
  have hN : Subgroup.normalizer ((U₀.map e.toMonoidHom : Subgroup X) : Set X) =
      (Subgroup.normalizer (U₀ : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq U₀ e).symm
  have hback : (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id P
    ext x
    simp
  have hUP : U₀ ≤ P.map e.symm.toMonoidHom := by
    rw [← (MulEquiv.mapSubgroup e).le_iff_le]
    change U₀.map e.toMonoidHom ≤ (P.map e.symm.toMonoidHom).map e.toMonoidHom
    rw [hback]
    exact Subgroup.le_normalizer.trans hSP
  have hPt' : P.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hPt
    rw [← hback, htop]
    exact Subgroup.map_top_of_surjective _ e.surjective
  have hle : P ≤ Subgroup.normalizer ((U₀.map e.toMonoidHom : Subgroup X) : Set X) := by
    rw [hN, ← hback]
    exact Subgroup.map_mono (h _ hUP hPt')
  refine ⟨U₀.map e.toMonoidHom, hS, ?_⟩
  rw [top_inf_eq]
  exact le_antisymm hle hSP

end CFSG.Quasithin.SmithC27
