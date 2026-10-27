module

public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.Quasithin.QP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section SL

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_conj_normalizer_of_isSylowTwoOf (hn : 1 ≤ n)
    {S : Subgroup (SpecialLinearGroup (Fin n) F)} (hS : IsSylowTwoOf S ⊤) :
    ∃ g : SpecialLinearGroup (Fin n) F,
      Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin n) F)) =
        (upperTriangular n F).map
          (MulAut.conj g : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := n) hn
  obtain ⟨-, hSp, hSi⟩ := hS
  have hSi' : ¬ 2 ∣ S.index := by
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hSi
  let T : Sylow 2 (SpecialLinearGroup (Fin n) F) := hSp.toSylow hSi'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) F) U₀ T
  refine ⟨g, ?_⟩
  have h1 : (T : Subgroup (SpecialLinearGroup (Fin n) F)) = S := rfl
  have h2 : S = (unitriangular n F).map
      (MulAut.conj g : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) := by
    rw [← h1, ← hg, ← hU₀]
    exact Sylow.coe_subgroup_smul
  have hbij : Function.Bijective
      (MulAut.conj g : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) :=
    (MulAut.conj g).bijective
  rw [h2, ← Subgroup.map_normalizer_eq_of_bijective _ hbij, normalizer_unitriangular]

theorem exists_conj_stabilizer_of_isMaxParabolic2 (hn : 1 ≤ n)
    {P : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hP : IsMaxParabolic2 (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) P) :
    ∃ (g : SpecialLinearGroup (Fin n) F) (d : ℕ), 1 ≤ d ∧ d < n ∧
      P = (stabilizer (flagSpace n F d)).map
        (MulAut.conj g : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) := by
  classical
  obtain ⟨hpar, hne, hmax⟩ := hP
  obtain ⟨-, S, hS, hNS⟩ := hpar
  obtain ⟨g, hg⟩ := exists_conj_normalizer_of_isSylowTwoOf hn hS
  set c : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F :=
    (MulAut.conj g : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) with hc
  set c' : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F :=
    (MulAut.conj g⁻¹ : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) with hc'
  have hcc' : ∀ x, c (c' x) = x := fun x => by simp [hc, hc', MulAut.conj_apply]; group
  have hc'c : ∀ x, c' (c x) = x := fun x => by simp [hc, hc', MulAut.conj_apply]; group
  set P' : Subgroup (SpecialLinearGroup (Fin n) F) := P.map c' with hP'
  have hPP' : P = P'.map c := by
    rw [hP', Subgroup.map_map]
    have : c.comp c' = MonoidHom.id _ := MonoidHom.ext hcc'
    rw [this, Subgroup.map_id]
  have hBP' : upperTriangular n F ≤ P' := by
    intro b hb
    have hbN : c b ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin n) F)) := by
      rw [hg]
      exact ⟨b, hb, rfl⟩
    exact ⟨c b, hNS ⟨Subgroup.mem_top _, hbN⟩, hc'c b⟩
  obtain ⟨hI, -⟩ := borel_overgroups P' hBP'
  set I := borelOvergroupCuts P' with hIdef
  have hP'top : P' ≠ ⊤ := by
    intro h
    apply hne
    rw [hPP', h, Subgroup.map_top_of_surjective c (MulAut.conj g).surjective]
  obtain ⟨d, hdI⟩ : I.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hP'top
    rw [hI, h, flagStabilizer_empty]
  obtain ⟨hd, hdn, -⟩ := id hdI
  have hP'le : P' ≤ stabilizer (flagSpace n F d) := by
    rw [← flagStabilizer_singleton, hI]
    exact fun x hx => mem_flagStabilizer.mpr fun i hi =>
      mem_flagStabilizer.mp hx i ((Set.mem_singleton_iff.mp hi) ▸ hdI)
  refine ⟨g, d, hd, hdn, ?_⟩
  set Q : Subgroup (SpecialLinearGroup (Fin n) F) := (stabilizer (flagSpace n F d)).map c with hQ
  have hBQ' : upperTriangular n F ≤ stabilizer (flagSpace n F d) :=
    upperTriangular_le_stabilizer_flagSpace d
  have hQpar : IsParabolic2 (⊤ : Subgroup (SpecialLinearGroup (Fin n) F)) Q := by
    refine ⟨le_top, S, hS, fun x hx => ?_⟩
    have hx' : x ∈ Subgroup.map c (upperTriangular n F) := by rw [← hg]; exact hx.2
    exact Subgroup.map_mono hBQ' hx'
  have hQne : Q ≠ ⊤ := by
    intro h
    apply stabilizer_flagSpace_ne_top (K := F) (n := n) hd hdn
    have := congrArg (Subgroup.map c') h
    rwa [hQ, Subgroup.map_map, show c'.comp c = MonoidHom.id _ from MonoidHom.ext hc'c,
      Subgroup.map_id, Subgroup.map_top_of_surjective c' (MulAut.conj g⁻¹).surjective] at this
  have hPQ : P ≤ Q := by
    rw [hPP']
    exact Subgroup.map_mono hP'le
  exact (hmax Q hQpar hQne hPQ).symm

end SL

section Transport

variable {G H : Type} [Group G] [Group H]

theorem isMaxParabolic2_top_of_subgroupOf {L P : Subgroup G} (h : IsMaxParabolic2 L P) :
    IsMaxParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
  obtain ⟨hpar, hne, hmax⟩ := h
  have hPL : P ≤ L := hpar.1
  refine ⟨?_, ?_, ?_⟩
  · rw [A312.isParabolic2_top_iff, Subgroup.map_subgroupOf_eq_of_le hPL]
    exact hpar
  · intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rwa [Subgroup.map_subgroupOf_eq_of_le hPL, Subgroup.map_top, Subgroup.range_subtype] at this
  · intro Q' hQ' hQ'top hPQ'
    have hQ : IsParabolic2 L (Q'.map L.subtype) := (A312.isParabolic2_top_iff L Q').mp hQ'
    have hQL : Q'.map L.subtype ≠ L := by
      intro h
      apply hQ'top
      have := congrArg (fun K : Subgroup G => K.subgroupOf L) h
      simpa [A4.subgroupOf_map_subtype', Subgroup.subgroupOf_self] using this
    have hPQ : P ≤ Q'.map L.subtype := by
      have := Subgroup.map_mono (f := L.subtype) hPQ'
      rwa [Subgroup.map_subgroupOf_eq_of_le hPL] at this
    have h1 := hmax _ hQ hQL hPQ
    calc Q' = (Q'.map L.subtype).subgroupOf L := (A4.subgroupOf_map_subtype' L Q').symm
      _ = P.subgroupOf L := by rw [h1]

theorem isMaxParabolic2_top_of_mulEquiv {L P : Subgroup G} (h : IsMaxParabolic2 L P) (e : ↥L ≃* H) :
    IsMaxParabolic2 (⊤ : Subgroup H) ((P.subgroupOf L).map e.toMonoidHom) := by
  have h1 := isMaxParabolic2_top_of_subgroupOf h
  have h2 := (SBd3T.isMaxParabolic2_map_iff e.toMonoidHom e.injective ⊤ (P.subgroupOf L)).2 h1
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at h2

end Transport

section Combined

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {G : Type} [Group G]

theorem exists_conj_stabilizer_of_mulEquiv (hn : 1 ≤ n) {L P : Subgroup G} (h : IsMaxParabolic2 L P)
    (e : ↥L ≃* SpecialLinearGroup (Fin n) F) :
    ∃ (g : SpecialLinearGroup (Fin n) F) (d : ℕ), 1 ≤ d ∧ d < n ∧
      (P.subgroupOf L).map e.toMonoidHom = (stabilizer (flagSpace n F d)).map
        (MulAut.conj g : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) :=
  exists_conj_stabilizer_of_isMaxParabolic2 hn (isMaxParabolic2_top_of_mulEquiv h e)

end Combined

end CFSG.Quasithin.QP
