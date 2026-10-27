module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Quasithin.EmptyFaithful.R3c11L3b

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

structure Config2 (Q : Type) [Group Q] (A : Set (MulAut Q)) (Sb Yb : Subgroup Q) : Prop where
  nonsolvable : ¬ Group.IsSolvable Q
  sylow : IsSylowTwoOf Sb ⊤
  normalizes : Sb ≤ Subgroup.normalizer (Yb : Set Q)
  solvable : Group.IsSolvable ↥Yb
  nine : 9 ∣ Nat.card ↥Yb
  inv_S : ∀ α ∈ A, Sb.map α.toMonoidHom = Sb
  inv_Y : ∀ α ∈ A, Yb.map α.toMonoidHom = Yb
  maximal : ∀ N : Subgroup Q, IsPGroup 2 ↥N → N ≠ ⊥ → Yb ⊔ Sb ≤ Subgroup.normalizer (N : Set Q) →
    (∀ α ∈ A, N.map α.toMonoidHom = N) → Subgroup.normalizer (N : Set Q) ≠ ⊤ →
      Subgroup.normalizer (N : Set Q) ≤ Subgroup.normalizer (Yb : Set Q)
  third : ∃ g : Subgroup Q, Sb ≤ g ∧ g ≤ Yb ⊔ Sb ∧ g ≠ Yb ⊔ Sb ∧ 3 ∣ Nat.card ↥g ∧
    ∀ α ∈ A, g.map α.toMonoidHom = g

@[expose] def autImage {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (A : Set (MulAut Q)) :
    Set (MulAut Q') := (MulAut.congr e) '' A

theorem map_map_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (α : MulAut Q)
    (X : Subgroup Q) :
    (X.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom =
      (X.map α.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

theorem Config2.of_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') {A : Set (MulAut Q)}
    {Sb Yb : Subgroup Q} (h : Config2 Q A Sb Yb) :
    Config2 Q' (autImage e A) (Sb.map e.toMonoidHom) (Yb.map e.toMonoidHom) := by
  obtain ⟨hns, hS, hN, hsol, h9, hiS, hiY, hmax, g, hSg, hgZ, hgne, hg3, hig⟩ := h
  have hmapsup : (Yb ⊔ Sb).map e.toMonoidHom = Yb.map e.toMonoidHom ⊔ Sb.map e.toMonoidHom :=
    Subgroup.map_sup _ _ _
  have hinj : ∀ (X Y : Subgroup Q), X.map e.toMonoidHom = Y.map e.toMonoidHom → X = Y :=
    fun X Y hXY => Subgroup.map_injective e.injective hXY
  refine ⟨fun hsolv' => hns ?_, CFSG.QuasithinUnique.Ch1.SporLat.isSylowTwoOf_map e hS, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff e Yb t₀).mpr (hN ht₀)
  · exact Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap Yb)
      (e.toMonoidHom.subgroupMap_surjective Yb)
  · rw [Nat.card_congr (Yb.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm]
    exact h9
  · rintro _ ⟨α, hα, rfl⟩
    rw [map_map_congr, hiS α hα]
  · rintro _ ⟨α, hα, rfl⟩
    rw [map_map_congr, hiY α hα]
  · intro N' hNp hN1 hZN hinv hNtop
    set N : Subgroup Q := N'.map e.symm.toMonoidHom with hNdef
    have hNN : N.map e.toMonoidHom = N' := by
      ext x
      simp only [hNdef, Subgroup.mem_map]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
    have hNp' : IsPGroup 2 ↥N :=
      hNp.of_equiv (Subgroup.equivMapOfInjective N' e.symm.toMonoidHom e.symm.injective)
    have hN1' : N ≠ ⊥ := by
      intro hb
      apply hN1
      rw [← hNN, hb, Subgroup.map_bot]
    have hZN' : Yb ⊔ Sb ≤ Subgroup.normalizer (N : Set Q) := by
      intro g' hg'
      have h1 : e g' ∈ Subgroup.normalizer ((N.map e.toMonoidHom : Subgroup Q') : Set Q') := by
        rw [hNN]
        apply hZN
        rw [← hmapsup]
        exact ⟨g', hg', rfl⟩
      exact (R3c11.mem_normalizer_map_equiv_iff e N g').1 h1
    have hinv' : ∀ α ∈ A, N.map α.toMonoidHom = N := by
      intro α hα
      have h1 := hinv _ ⟨α, hα, rfl⟩
      rw [← hNN, map_map_congr] at h1
      exact hinj _ _ h1
    have hNtop' : Subgroup.normalizer (N : Set Q) ≠ ⊤ := by
      intro ht
      apply hNtop
      rw [eq_top_iff]
      intro x _
      have h1 : e (e.symm x) ∈ Subgroup.normalizer ((N.map e.toMonoidHom : Subgroup Q') : Set Q') :=
        (R3c11.mem_normalizer_map_equiv_iff e N (e.symm x)).2 (by rw [ht]; exact Subgroup.mem_top _)
      rw [hNN] at h1
      simpa using h1
    intro x hx
    have h1 : e (e.symm x) ∈ Subgroup.normalizer ((N.map e.toMonoidHom : Subgroup Q') : Set Q') := by
      rw [hNN]
      simpa using hx
    have h2 := hmax N hNp' hN1' hZN' hinv' hNtop'
      ((R3c11.mem_normalizer_map_equiv_iff e N (e.symm x)).1 h1)
    have h3 := (R3c11.mem_normalizer_map_equiv_iff e Yb (e.symm x)).2 h2
    simpa using h3
  · refine ⟨g.map e.toMonoidHom, Subgroup.map_mono hSg, ?_, ?_, ?_, ?_⟩
    · rw [← hmapsup]
      exact Subgroup.map_mono hgZ
    · intro heq
      rw [← hmapsup] at heq
      exact hgne (hinj _ _ heq)
    · rw [Nat.card_congr (g.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm]
      exact hg3
    · rintro _ ⟨α, hα, rfl⟩
      rw [map_map_congr, hig α hα]

end CFSG.Quasithin.ModH
