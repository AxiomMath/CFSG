module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type*} [CommGroup T]

structure S16fPair (M A : Subgroup (MulAut T)) (g : MulAut T) : Prop where
  le : A ≤ M
  mem : g ∈ M
  ne : A.map (MulAut.conj g).toMonoidHom ≠ A
  conj : ∀ φ ∈ M, A.map (MulAut.conj φ).toMonoidHom = A ∨
    A.map (MulAut.conj φ).toMonoidHom = A.map (MulAut.conj g).toMonoidHom
  sup : commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom = ⊤

private theorem s16f_normalizes_of_odd {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16fPair M A g) {e : MulAut T} (he : e ∈ M) {n : ℕ} (hn : Odd n) (hen : e ^ n = 1) :
    A.map (MulAut.conj e).toMonoidHom = A := by
  by_contra hne
  obtain ⟨m, hm⟩ := hn
  have hAe : A.map (MulAut.conj e).toMonoidHom = A.map (MulAut.conj g).toMonoidHom :=
    (h.conj e he).resolve_left hne
  have hone : A.map (MulAut.conj (e ^ n)).toMonoidHom = A := by
    rw [hen]
    exact s16n9b_map_conj_one A
  have hBe : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj e).toMonoidHom =
      A.map (MulAut.conj (e * g)).toMonoidHom := s16n9b_map_conj_map_conj A g e
  rcases h.conj (e * g) (M.mul_mem he h.mem) with h1 | h1
  ·
    have h2 : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (e ^ 2)).toMonoidHom =
        A.map (MulAut.conj g).toMonoidHom := by
      rw [sq, ← s16n9b_map_conj_map_conj _ e e, hBe, h1, hAe]
    have h3 := s16n9b_map_conj_pow_fixed _ h2 m
    apply h.ne
    calc A.map (MulAut.conj g).toMonoidHom
        = (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj ((e ^ 2) ^ m)).toMonoidHom :=
          h3.symm
      _ = (A.map (MulAut.conj e).toMonoidHom).map (MulAut.conj ((e ^ 2) ^ m)).toMonoidHom := by
          rw [hAe]
      _ = A.map (MulAut.conj ((e ^ 2) ^ m * e)).toMonoidHom := s16n9b_map_conj_map_conj A e _
      _ = A.map (MulAut.conj (e ^ n)).toMonoidHom := by rw [hm, pow_succ e (2 * m), pow_mul]
      _ = A := hone
  ·
    have key : ∀ k : ℕ, A.map (MulAut.conj (e ^ (k + 1))).toMonoidHom =
        A.map (MulAut.conj g).toMonoidHom := by
      intro k
      induction k with
      | zero => rw [zero_add, pow_one]; exact hAe
      | succ k ih =>
        rw [pow_succ', ← s16n9b_map_conj_map_conj A (e ^ (k + 1)) e, ih, hBe]
        exact h1
    have h2 := key (2 * m)
    rw [← hm, hone] at h2
    exact h.ne h2.symm

private theorem s16f_normalizes_conj {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16fPair M A g) {φ : MulAut T} (hφM : φ ∈ M)
    (hA : A.map (MulAut.conj φ).toMonoidHom = A) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom := by
  rw [s16n9b_map_conj_map_conj]
  rcases h.conj (φ * g) (M.mul_mem hφM h.mem) with h1 | h1
  · exfalso
    apply h.ne
    have h2 : A.map (MulAut.conj φ⁻¹).toMonoidHom = A := by
      have := congrArg (fun X : Subgroup (MulAut T) => X.map (MulAut.conj φ⁻¹).toMonoidHom) hA
      simp only [s16n9b_map_conj_map_conj, inv_mul_cancel, s16n9b_map_conj_one] at this
      exact this.symm
    calc A.map (MulAut.conj g).toMonoidHom
        = (A.map (MulAut.conj (φ * g)).toMonoidHom).map (MulAut.conj φ⁻¹).toMonoidHom := by
          rw [s16n9b_map_conj_map_conj, inv_mul_cancel_left]
      _ = A.map (MulAut.conj φ⁻¹).toMonoidHom := by rw [h1]
      _ = A := h2
  · exact h1

theorem S16fPair.stab_of_odd {M A : Subgroup (MulAut T)} {g : MulAut T} (h : S16fPair M A g)
    {e : MulAut T} (he : e ∈ M) {n : ℕ} (hn : Odd n) (hen : e ^ n = 1) :
    e ∈ stabSub (commSub ⊤ A) ∧ e ∈ stabSub ((commSub ⊤ A).map g.toMonoidHom) := by
  have hA : A.map (MulAut.conj e).toMonoidHom = A := s16f_normalizes_of_odd h he hn hen
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ A).map g.toMonoidHom :=
    s15_Infra_commSub_top_map_conj A g
  constructor
  · apply s16n9b_mem_stabSub_of_map_eq
    rw [← s15_Infra_commSub_top_map_conj A e, hA]
  · apply s16n9b_mem_stabSub_of_map_eq
    rw [← hgB, ← s15_Infra_commSub_top_map_conj _ e, s16f_normalizes_conj h he hA]

end Generic

section Construction

variable {G : Type} [Group G] [Finite G]

theorem s16f_pair_of_two (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 2) :
    ∃ g : MulAut (Vtil V₀ V hV), S16fPair (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g := by
  have h : Hyp151 D V₀ V L := hset.hyp151
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  show ∃ g : MulAut (Vtil V₀ V hV), S16fPair (Mbar D.M V₀ V hV) (barSub V₀ V hV L) g
  have hS : {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}.ncard = 2 :=
    hs
  obtain ⟨x, y, hxy, hSxy⟩ := Set.ncard_eq_two.1 hS
  have hAS : barSub V₀ V hV L ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨1, (Mbar D.M V₀ V hV).one_mem, (s16n9b_map_conj_one _).symm⟩
  rw [hSxy] at hAS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hAS
  obtain ⟨B, hBA, hSAB⟩ : ∃ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≠ barSub V₀ V hV L ∧
      {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
        X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = {barSub V₀ V hV L, B} := by
    rcases hAS with h1 | h1
    · exact ⟨y, fun hy => hxy (h1.symm.trans hy.symm), by rw [hSxy, h1]⟩
    · exact ⟨x, fun hx => hxy (hx.trans h1), by rw [hSxy, h1, Set.pair_comm]⟩
  have hBS : B ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := by
    rw [hSAB]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨φ₀, hφ₀M, hBφ₀⟩ := hBS
  have hAB : (barSub V₀ V hV L).map (MulAut.conj φ₀).toMonoidHom = B := hBφ₀.symm
  have hWB : (commSub ⊤ (barSub V₀ V hV L)).map φ₀.toMonoidHom = commSub ⊤ B := by
    rw [← hAB, s15_Infra_commSub_top_map_conj]
  have hKcases : ∀ m : G, m ∈ D.M → barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L ∨
      barSub V₀ V hV (conjSubgroup L m) = B := by
    intro m hm
    have hmem : barSub V₀ V hV (conjSubgroup L m) ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨(actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹,
        Subgroup.inv_mem _ (actTil_mem_barSub V₀ V hV hm (hMs hm)),
        s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L⟩
    rw [hSAB] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  refine ⟨φ₀, ?_⟩
  refine ⟨barSub_mono V₀ V hV h.le, hφ₀M, ?_, ?_, ?_⟩
  ·
    rw [hAB]
    exact hBA
  ·
    intro φ hφ
    have hmem : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∈
        {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
          X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := ⟨φ, hφ, rfl⟩
    rw [hSAB] at hmem
    rcases hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ((Set.mem_singleton_iff.1 h1).trans hAB.symm)
  ·
    rw [hWB]
    have htop := s15_Two_iSup_commSub_eq_top D h1217 h hL
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup (Vtil V₀ V hV))
        = ⨆ m : D.M, commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m : G))) := htop.symm
      _ ≤ commSub ⊤ (barSub V₀ V hV L) ⊔ commSub ⊤ B := by
        refine iSup_le fun m => ?_
        rcases hKcases m m.2 with h1 | h1
        · exact (congrArg (commSub ⊤) h1).le.trans le_sup_left
        · exact (congrArg (commSub ⊤) h1).le.trans le_sup_right

end Construction

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
