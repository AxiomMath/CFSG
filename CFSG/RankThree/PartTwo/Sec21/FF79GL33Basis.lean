module

public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Phi
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Unit

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

section Transport

variable (P : GL (Fin 3) (ZMod 3))

@[expose] def psi (u : Vec) : Vec := Matrix.vecMul u (P : Mat)

@[expose] def cj (g : GL (Fin 3) (ZMod 3)) : GL (Fin 3) (ZMod 3) := P * g * P⁻¹

theorem psi_inv_left (u : Vec) :
    Matrix.vecMul (psi P u) ((P⁻¹ : GL (Fin 3) (ZMod 3)) : Mat) = u := by
  unfold psi
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem psi_inv_right (u : Vec) :
    psi P (Matrix.vecMul u ((P⁻¹ : GL (Fin 3) (ZMod 3)) : Mat)) = u := by
  unfold psi
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]

theorem psi_inj : Function.Injective (psi P) := by
  intro u u' h
  have := congrArg (fun x => Matrix.vecMul x ((P⁻¹ : GL (Fin 3) (ZMod 3)) : Mat)) h
  rwa [psi_inv_left, psi_inv_left] at this

theorem psi_add (u u' : Vec) : psi P (u + u') = psi P u + psi P u' := by
  unfold psi; rw [Matrix.add_vecMul]

theorem psi_smul (a : ZMod 3) (u : Vec) : psi P (a • u) = a • psi P u := by
  unfold psi; rw [Matrix.smul_vecMul]

theorem psi_neg (u : Vec) : psi P (-u) = -psi P u := Matrix.neg_vecMul u (P : Mat)

theorem psi_cj (g : GL (Fin 3) (ZMod 3)) (u : Vec) :
    act33 g (psi P u) = psi P (act33 (cj P g) u) := by
  unfold psi cj act33
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
  congr 1
  rw [← Units.val_mul (P * g * P⁻¹) P, mul_assoc (P * g) P⁻¹ P, inv_mul_cancel, mul_one,
    Units.val_mul]

theorem psi_mem_span {a b u : Vec} :
    psi P u ∈ Submodule.span (ZMod 3) {psi P a, psi P b} ↔
      u ∈ Submodule.span (ZMod 3) {a, b} := by
  rw [Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, psi_inj P ?_⟩
    rw [psi_add, psi_smul, psi_smul]
    exact h
  · rintro ⟨x, y, h⟩
    refine ⟨x, y, ?_⟩
    rw [← psi_smul, ← psi_smul, ← psi_add, h]

theorem exists_psi (u : Vec) : ∃ u' : Vec, psi P u' = u :=
  ⟨Matrix.vecMul u ((P⁻¹ : GL (Fin 3) (ZMod 3)) : Mat), psi_inv_right P u⟩

theorem act_cj_iff (g : GL (Fin 3) (ZMod 3)) (u u' : Vec) :
    act33 (cj P g) u = u' ↔ act33 g (psi P u) = psi P u' := by
  rw [psi_cj]
  exact ⟨fun h => by rw [h], fun h => psi_inj P h⟩

theorem cj_mul (g h : GL (Fin 3) (ZMod 3)) : cj P (g * h) = cj P g * cj P h := by
  unfold cj; group

theorem cj_inj : Function.Injective (cj P) := by
  intro g h hgh
  unfold cj at hgh
  simpa using hgh

@[expose] def conjSub (X : Subgroup (GL (Fin 3) (ZMod 3))) : Subgroup (GL (Fin 3) (ZMod 3)) :=
  X.map (MulAut.conj P).toMonoidHom

theorem mem_conjSub {X : Subgroup (GL (Fin 3) (ZMod 3))} {g' : GL (Fin 3) (ZMod 3)} :
    g' ∈ conjSub P X ↔ ∃ g ∈ X, cj P g = g' := by
  unfold conjSub
  rw [Subgroup.mem_map]
  rfl

theorem cj_mem {X : Subgroup (GL (Fin 3) (ZMod 3))} {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ X) :
    cj P g ∈ conjSub P X := (mem_conjSub P).mpr ⟨g, hg, rfl⟩

theorem mem_of_cj {X : Subgroup (GL (Fin 3) (ZMod 3))} {g : GL (Fin 3) (ZMod 3)}
    (hg : cj P g ∈ conjSub P X) : g ∈ X := by
  obtain ⟨h, hh, hhg⟩ := (mem_conjSub P).mp hg
  rw [← cj_inj P hhg]; exact hh

theorem psi_mem_set6 (a b c y : Vec) (hy : y ∈ ({a, -a, b, -b, c, -c} : Set Vec)) :
    psi P y ∈ ({psi P a, -psi P a, psi P b, -psi P b, psi P c, -psi P c} : Set Vec) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (psi_neg P a))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (psi_neg P b))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (psi_neg P c)))))

theorem exists_set6 (a b c x : Vec)
    (hx : x ∈ ({psi P a, -psi P a, psi P b, -psi P b, psi P c, -psi P c} : Set Vec)) :
    ∃ y ∈ ({a, -a, b, -b, c, -c} : Set Vec), x = psi P y := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨a, Or.inl rfl, rfl⟩
  · exact ⟨-a, Or.inr (Or.inl rfl), (psi_neg P a).symm⟩
  · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨-b, Or.inr (Or.inr (Or.inr (Or.inl rfl))), (psi_neg P b).symm⟩
  · exact ⟨c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
  · exact ⟨-c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), (psi_neg P c).symm⟩

theorem GL33At_transport (X : Subgroup (GL (Fin 3) (ZMod 3)))
    (h : GL33At (conjSub P X) e0 e1 e2) : GL33At X (psi P e0) (psi P e1) (psi P e2) := by
  intro hτ hcard hnon hD hE
  have hN : ∀ g, act33 g (psi P e0) = psi P e0 ↔ act33 (cj P g) e0 = e0 := fun g =>
    (act_cj_iff P g e0 e0).symm
  have hspan : ∀ u, psi P u ∈ Submodule.span (ZMod 3) {psi P e1, psi P e2} ↔
      u ∈ Submodule.span (ZMod 3) {e1, e2} := fun u => psi_mem_span P
  have hconcl := h ?_ ?_ ?_ ?_ ?_
  · rcases hconcl with ⟨hst, hall⟩ | ⟨u₁, hu₁, u₂, hu₂, hli, hcl, h1, h2, h3⟩
    · left
      refine ⟨?_, ?_⟩
      · intro g hg w hw
        obtain ⟨w', rfl⟩ := exists_psi P w
        rw [psi_cj]
        exact (hspan _).mpr (hst _ (cj_mem P hg) w' ((hspan w').mp hw))
      · intro u hu
        obtain ⟨u', rfl⟩ := exists_psi P u
        obtain ⟨g', hg', hg'u⟩ := hall u' (fun hh => hu ((hspan u').mpr hh))
        obtain ⟨g, hg, rfl⟩ := (mem_conjSub P).mp hg'
        refine ⟨g, hg, ?_⟩
        rw [psi_cj]
        rcases hg'u with hh | hh
        · left; rw [hh]
        · right; rw [hh, psi_neg]
    · right
      refine ⟨psi P u₁, (hspan _).mpr hu₁, psi P u₂, (hspan _).mpr hu₂, ?_, ?_, ?_, ?_, ?_⟩
      · exact li_vecMul _ _ _ P hli
      · intro g hg x hx
        obtain ⟨y, hy, rfl⟩ := exists_set6 P e0 u₁ u₂ x hx
        rw [psi_cj]
        exact psi_mem_set6 P e0 u₁ u₂ _ (hcl _ (cj_mem P hg) y hy)
      · obtain ⟨g', hg', k0, k1, k2⟩ := h1
        obtain ⟨g, hg, rfl⟩ := (mem_conjSub P).mp hg'
        refine ⟨g, hg, ?_, ?_, ?_⟩
        · have := (act_cj_iff P g e0 (-e0)).mp k0
          rwa [psi_neg] at this
        · exact (act_cj_iff P g u₁ u₁).mp k1
        · exact (act_cj_iff P g u₂ u₂).mp k2
      · obtain ⟨g', hg', k0, k1, k2⟩ := h2
        obtain ⟨g, hg, rfl⟩ := (mem_conjSub P).mp hg'
        exact ⟨g, hg, (act_cj_iff P g e0 u₁).mp k0, (act_cj_iff P g u₁ e0).mp k1,
          (act_cj_iff P g u₂ u₂).mp k2⟩
      · obtain ⟨g', hg', k0, k1, k2⟩ := h3
        obtain ⟨g, hg, rfl⟩ := (mem_conjSub P).mp hg'
        exact ⟨g, hg, (act_cj_iff P g e0 u₁).mp k0, (act_cj_iff P g u₁ u₂).mp k1,
          (act_cj_iff P g u₂ e0).mp k2⟩
  · obtain ⟨τ, hτX, h0, h1, h2⟩ := hτ
    refine ⟨cj P τ, cj_mem P hτX, (hN τ).mp h0, ?_, ?_⟩
    · apply (act_cj_iff P τ e1 (-e1)).mpr
      rw [psi_neg]; exact h1
    · apply (act_cj_iff P τ e2 (-e2)).mpr
      rw [psi_neg]; exact h2
  · let eqv : {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g (psi P e0) = psi P e0} ≃
        {g' : GL (Fin 3) (ZMod 3) // g' ∈ conjSub P X ∧ act33 g' e0 = e0} :=
      Equiv.subtypeEquiv (MulAut.conj P).toEquiv (fun g =>
        ⟨fun ⟨a, b⟩ => ⟨cj_mem P a, (hN g).mp b⟩, fun ⟨a, b⟩ => ⟨mem_of_cj P a, (hN g).mpr b⟩⟩)
    rw [← Nat.card_congr eqv]
    exact hcard
  · obtain ⟨g, hg, k, hk, hg0, hk0, hgk⟩ := hnon
    refine ⟨cj P g, cj_mem P hg, cj P k, cj_mem P hk, (hN g).mp hg0, (hN k).mp hk0, ?_⟩
    intro heq
    apply hgk
    apply cj_inj P
    rw [cj_mul, cj_mul]
    exact heq
  · intro g' hg' hcase
    obtain ⟨g, hg, rfl⟩ := (mem_conjSub P).mp hg'
    have hcase' : act33 g (psi P e0) = psi P e0 ∨ act33 g (psi P e0) = -psi P e0 := by
      rcases hcase with hc | hc
      · exact Or.inl ((hN g).mpr hc)
      · right
        have := (act_cj_iff P g e0 (-e0)).mp hc
        rwa [psi_neg] at this
    obtain ⟨hW, d, hd, hd0, hrows⟩ := hD g hg hcase'
    refine ⟨?_, cj P d, cj_mem P hd, (hN d).mp hd0, ?_⟩
    · intro w hw
      have := hW (psi P w) ((hspan w).mpr hw)
      rw [psi_cj] at this
      exact (hspan _).mp this
    · rcases hrows with hr | hr
      · left
        intro w hw
        have := hr (psi P w) ((hspan w).mpr hw)
        rw [psi_cj, psi_cj] at this
        exact psi_inj P this
      · right
        intro w hw
        have := hr (psi P w) ((hspan w).mpr hw)
        rw [psi_cj, psi_cj, ← psi_neg] at this
        exact psi_inj P this
  · obtain ⟨g, hg, h1, h2⟩ := hE
    refine ⟨cj P g, cj_mem P hg, fun hh => h1 ((hN g).mpr hh), fun hh => h2 ?_⟩
    have := (act_cj_iff P g e0 (-e0)).mp hh
    rwa [psi_neg] at this

end Transport

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end
