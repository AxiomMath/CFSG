module

public import CFSG.Quasithin.EmptyFaithful.S151S9UDef
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem ActionDataG.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ActionDataG X) : ActionDataG Y := by
  obtain ⟨N, m, φ, hN, ⟨k, hk⟩, hm, hker, hrange⟩ := h
  let ε : ↥N ≃* ↥(N.map e.toMonoidHom) := N.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨N.map e.toMonoidHom, m, φ.comp ε.symm.toMonoidHom, Subgroup.Normal.map hN _ e.surjective,
    ⟨k, ?_⟩, hm, ?_, ?_⟩
  · rw [Subgroup.index_map_of_bijective e.bijective, hk]
  · have hkerEq : (φ.comp ε.symm.toMonoidHom).ker = φ.ker.map ε.toMonoidHom := by
      ext y
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map]
      constructor
      · intro hy
        exact ⟨ε.symm y, hy, ε.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        show φ (ε.symm (ε x)) = 1
        rw [ε.symm_apply_apply]
        exact hx
    rw [hkerEq]
    exact hker.map ε.toMonoidHom
  · have : (φ.comp ε.symm.toMonoidHom).range = φ.range := by
      ext x
      simp only [MonoidHom.mem_range, MonoidHom.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨y, rfl⟩
        refine ⟨ε y, ?_⟩
        show φ (ε.symm (ε y)) = φ y
        rw [ε.symm_apply_apply]
    rw [this]
    exact hrange

theorem ActionData.map {Q Γ : Type} [Group Q] [Group Γ] (e : Q ≃* Γ) {Y : Subgroup Q}
    (h : ActionData Y) : ActionData (Y.map e.toMonoidHom) :=
  ActionDataG.of_mulEquiv (Y.equivMapOfInjective e.toMonoidHom e.injective) h

@[expose] def MLDAtSylow {Γ : Type} [Group Γ] (S : Subgroup Γ) : Prop :=
  Nat.card ↥(centerOf S) = 2 ∧
    ∀ W : Subgroup Γ, W ≤ centerOf S → W ≠ ⊥ → ∀ Y : Subgroup Γ, S ≤ Y → Y ≠ ⊤ →
      Subgroup.centralizer (W : Set Γ) < Y → ActionData Y

theorem exists_equiv_map_eq_sylow {Γ Q : Type} [Group Γ] [Finite Γ] [Group Q] [Finite Q]
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (e : Q ≃* Γ) {T : Subgroup Q}
    (hT : IsSylowTwoOf T ⊤) : ∃ ψ : Q ≃* Γ, T.map ψ.toMonoidHom = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [hST, Subgroup.map_map]
  rfl

theorem map_centralizer_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (s : Set X) :
    (Subgroup.centralizer s).map e.toMonoidHom = Subgroup.centralizer (e.toMonoidHom '' s) := by
  apply le_antisymm (Subgroup.map_centralizer_le_centralizer_image s e.toMonoidHom)
  intro y hy
  refine ⟨e.symm y, ?_, by simp⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro g hg
  have h := Subgroup.mem_centralizer_iff.mp hy (e g) ⟨g, hg, rfl⟩
  apply e.injective
  simpa using h

theorem centerOf_map_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (P : Subgroup X) :
    centerOf (P.map e.toMonoidHom) = (centerOf P).map e.toMonoidHom := by
  unfold centerOf
  rw [Subgroup.map_inf_eq P (Subgroup.centralizer (P : Set X)) e.toMonoidHom e.injective,
    map_centralizer_equiv, Subgroup.coe_map]

theorem mldOver_of_sylow {Γ Q : Type} [Group Γ] [Finite Γ] [Group Q] [Finite Q] (e : Q ≃* Γ)
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (h : MLDAtSylow S) : MLDOver Q := by
  intro P hP
  obtain ⟨ψ, hψ⟩ := exists_equiv_map_eq_sylow hS e hP
  have hcen : centerOf S = (centerOf P).map ψ.toMonoidHom := by
    rw [← hψ]
    exact centerOf_map_equiv ψ P
  obtain ⟨hcard, hW⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hcen, Subgroup.card_map_of_injective ψ.injective] at hcard
    exact hcard
  · intro W hWP hW0 Y hPY hY hlt
    have hW' : W.map ψ.toMonoidHom ≤ centerOf S := by
      rw [hcen]
      exact Subgroup.map_mono hWP
    have hW0' : W.map ψ.toMonoidHom ≠ ⊥ := fun h0 =>
      hW0 (Subgroup.map_injective ψ.injective (h0.trans (Subgroup.map_bot _).symm))
    have hSY : S ≤ Y.map ψ.toMonoidHom := by
      rw [← hψ]
      exact Subgroup.map_mono hPY
    have hY' : Y.map ψ.toMonoidHom ≠ ⊤ := fun h0 => hY (by
      have := congrArg (Subgroup.map ψ.symm.toMonoidHom) h0
      rw [Subgroup.map_map] at this
      have hid : ψ.symm.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id Q := by
        ext x
        simp
      rw [hid, Subgroup.map_id, Subgroup.map_top_of_surjective _ ψ.symm.surjective] at this
      exact this)
    have hlt' : Subgroup.centralizer ((W.map ψ.toMonoidHom : Subgroup Γ) : Set Γ) <
        Y.map ψ.toMonoidHom := by
      rw [Subgroup.coe_map, ← map_centralizer_equiv]
      exact (Subgroup.map_lt_map_iff_of_injective ψ.injective).mpr hlt
    have h1 := ActionData.map ψ.symm (hW _ hW' hW0' _ hSY hY' hlt')
    have hYY : (Y.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = Y := by
      rw [Subgroup.map_map]
      ext x
      simp
    rwa [hYY] at h1

end CFSG.Quasithin.S151S9U
