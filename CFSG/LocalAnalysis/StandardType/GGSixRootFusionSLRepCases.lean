module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRep

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane

namespace SLRep

variable {G : Type} [Group G] {n : ℕ} {F : Type} [Field F]

@[expose] def ggFrame (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (A₀ : Matrix.SpecialLinearGroup (Fin n) F) : Matrix.SpecialLinearGroup (Fin n) F →* G :=
  ψ.comp (MulAut.conj A₀).toMonoidHom

theorem ggFrame_apply (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (A₀ s : Matrix.SpecialLinearGroup (Fin n) F) : ggFrame ψ A₀ s = ψ (A₀ * s * A₀⁻¹) :=
  rfl

theorem range_ggFrame (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (A₀ : Matrix.SpecialLinearGroup (Fin n) F) : (ggFrame ψ A₀).range = ψ.range := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨A₀⁻¹ * s * A₀, by rw [ggFrame_apply]; congr 1; group⟩

theorem ker_ggFrame_le {ψ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (A₀ : Matrix.SpecialLinearGroup (Fin n) F) :
    (ggFrame ψ A₀).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) := by
  intro s hs
  have hc : A₀ * s * A₀⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) := hker hs
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro g
  have h := hc (A₀ * g * A₀⁻¹)
  have h2 : A₀ * (g * s) * A₀⁻¹ = A₀ * (s * g) * A₀⁻¹ := by
    calc A₀ * (g * s) * A₀⁻¹ = A₀ * g * A₀⁻¹ * (A₀ * s * A₀⁻¹) := by group
      _ = A₀ * s * A₀⁻¹ * (A₀ * g * A₀⁻¹) := h
      _ = A₀ * (s * g) * A₀⁻¹ := by group
  simpa using h2

theorem transvection_mem_coordBlockSL {S : Finset (Fin n)} {i j : Fin n} (hi : i ∈ S)
    (hj : j ∈ S) (hij : i ≠ j) (c : F) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ coordBlockSL F S := by
  rw [mem_coordBlockSL_iff]
  intro a b hab
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply]
  have hne : ¬ (i = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    rcases hab with h | h
    · exact h hi
    · exact h hj
  rw [ite_eq_right hne, add_zero]

theorem eq_of_mem_centralizer_coordBlockSL {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) {S : Finset (Fin n)}
    {b : G} (hbL : b ∈ Subgroup.centralizer (((coordBlockSL F S).map φ : Subgroup G) : Set G))
    {D : GL (Fin n) F} {t : Fin n → F} (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) {i₀ : Fin n} (hi₀ : i₀ ∈ S) :
    ∀ i ∈ S, t i = t i₀ := by
  intro i hi
  by_cases hii : i = i₀
  · rw [hii]
  have hmem : φ (Matrix.SpecialLinearGroup.transvection hii 1) ∈
      ((coordBlockSL F S).map φ : Subgroup G) :=
    ⟨_, transvection_mem_coordBlockSL hi hi₀ hii 1, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp hbL _ hmem
  have h1 : b * φ (Matrix.SpecialLinearGroup.transvection hii 1) * b⁻¹ =
      φ (Matrix.SpecialLinearGroup.transvection hii 1) := by
    rw [← hc]
    group
  rw [hb, slConj_transvection hD hii] at h1
  have h2 := eq_of_map_transvection_eq hker hii h1
  have h0 := ne_zero_of_diagonal hD i₀
  rw [mul_one] at h2
  field_simp at h2
  exact h2

theorem slConj_eq_self_of_const {D : GL (Fin n) F} {t : Fin n → F}
    (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t) (hc : ∀ i j, t i = t j)
    (s : Matrix.SpecialLinearGroup (Fin n) F) : slConj n F D s = s :=
  mem_ggFix.mp ((TypeA.mem_ggFix_slConjugation_iff hD).mpr fun i j hij => absurd (hc i j) hij)

theorem ne_one_of_frame {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) {b : G}
    {D : GL (Fin n) F} {t : Fin n → F} (hD : (D : Matrix (Fin n) (Fin n) F) = diagonal t)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s)) {i j : Fin n} (hij : t i ≠ t j) : b ≠ 1 := by
  rintro rfl
  have hne : i ≠ j := by
    rintro rfl
    exact hij rfl
  have h := hb (Matrix.SpecialLinearGroup.transvection hne 1)
  rw [one_mul, inv_one, mul_one, slConj_transvection hD hne] at h
  have h1 := eq_of_map_transvection_eq hker hne h
  have h0 := ne_zero_of_diagonal hD j
  rw [mul_one] at h1
  field_simp at h1
  exact hij h1.symm

theorem slConj_toGL (d s : Matrix.SpecialLinearGroup (Fin n) F) :
    slConj n F (Matrix.SpecialLinearGroup.toGL d) s = d * s * d⁻¹ := by
  apply Subtype.ext
  rw [ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, ← map_inv]
  rfl

theorem act_map (φ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (d s : Matrix.SpecialLinearGroup (Fin n) F) :
    φ d * φ s * (φ d)⁻¹ = φ (slConj n F (Matrix.SpecialLinearGroup.toGL d) s) := by
  rw [slConj_toGL, map_mul, map_mul, map_inv]

theorem mul_act {φ : Matrix.SpecialLinearGroup (Fin n) F →* G} {b c : G} {D D' : GL (Fin n) F}
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F D s))
    (hc : ∀ s, c * φ s * c⁻¹ = φ (slConj n F D' s)) (s : Matrix.SpecialLinearGroup (Fin n) F) :
    (b * c) * φ s * (b * c)⁻¹ = φ (slConj n F (D * D') s) := by
  have hm : slConj n F (D * D') = slConj n F D * slConj n F D' := map_mul _ _ _
  rw [hm, MulAut.mul_apply, ← hb, ← hc]
  group

theorem ggRootFusionWitnessAlt_of_conj_comm (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    {p : ℕ} {Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r : G}
    {u w : Matrix.SpecialLinearGroup (Fin n) F} {b : G}
    (hcomm : b * ψ (w * u * w⁻¹) = ψ (w * u * w⁻¹) * b) (hwM : ψ w ∈ M)
    (hW : GGSixFusionWitness p Bs D E G₀ t f b) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ u) := by
  refine Or.inr (Or.inl ⟨(ψ w)⁻¹ * b * ψ w, ?_, ψ w, hwM, ?_⟩)
  · have h : b * (ψ w * ψ u * (ψ w)⁻¹) = (ψ w * ψ u * (ψ w)⁻¹) * b := by
      simpa only [map_mul, map_inv] using hcomm
    calc (ψ w)⁻¹ * b * ψ w * ψ u = (ψ w)⁻¹ * (b * (ψ w * ψ u * (ψ w)⁻¹)) * ψ w := by group
      _ = (ψ w)⁻¹ * ((ψ w * ψ u * (ψ w)⁻¹) * b) * ψ w := by rw [h]
      _ = ψ u * ((ψ w)⁻¹ * b * ψ w) := by group
  · have he : ψ w * ((ψ w)⁻¹ * b * ψ w) * (ψ w)⁻¹ = b := by group
    rw [he]
    exact hW

theorem ggSixFusionWitness_of_frame [Finite F] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1)
    (h4 : 4 ≤ Nat.card F) {B Bs D E G₀ : Subgroup G} {t : StatedLieTag} {f : ℕ}
    (hBs : GGBstar p B Bs) {φ : Matrix.SpecialLinearGroup (Fin n) F →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    (hrange : φ.range = G₀) (hcent : Subgroup.centralizer (G₀ : Set G) = ⊥)
    (hframe : ∀ b ∈ Bs, GGFrameDiag φ b) {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1)
    {Dm : GL (Fin n) F} {τ : Fin n → F} (hDm : (Dm : Matrix (Fin n) (Fin n) F) = diagonal τ)
    (hb : ∀ s, b * φ s * b⁻¹ = φ (slConj n F Dm s)) {S : Finset (Fin n)} {μ : F}
    (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ) (hcard : Sᶜ.card < S.card)
    (hS2 : 2 ≤ S.card) (hSc2 : Sᶜ.card ≤ 2) {i₁ : Fin n} (hi₁ : i₁ ∉ S) :
    GGSixFusionWitness p Bs D E G₀ t f b := by
  have hcent' : Subgroup.centralizer (φ.range : Set G) = ⊥ := by rw [hrange]; exact hcent
  obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨hb1, Or.inr (Or.inr ⟨hbBs, (coordBlockSL F S).map φ, ?_, Or.inl ?_⟩)⟩
  · have := isComponentOf_map_coordBlockSL h4 hker hDm hb hS hSc hcard hS2 hi₁
    rwa [hrange] at this
  · refine (card_le_of_frame hp hpF hker hcent' (X := Bs ⊓ Subgroup.centralizer
      (((coordBlockSL F S).map φ : Subgroup G) : Set G)) (fun c hc => hBs.2.1.2 c hc.1)
      (fun c hc => hframe c hc.1) (S := S) (i₀ := i₀) ?_).trans
      (Nat.pow_le_pow_right hp.pos hSc2)
    intro c hc D' t' hD' hc' i hi
    exact eq_of_mem_centralizer_coordBlockSL hker hc.2 hD' hc' hi₀ i hi

structure FrameCtx (p : ℕ) (B Bs G₀ : Subgroup G) (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (A₀ : Matrix.SpecialLinearGroup (Fin n) F) : Prop where
  bstar : GGBstar p B Bs
  ker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)
  range : ψ.range = G₀
  cent : Subgroup.centralizer (G₀ : Set G) = ⊥
  frame : ∀ b ∈ Bs, GGFrameDiag (ggFrame ψ A₀) b
  prime : p.Prime
  odd : p ≠ 2
  dvd : p ∣ Nat.card F - 1
  four : 4 ≤ Nat.card F

theorem ggRootFusionWitnessAlt_of_frame [Finite F] [CharP F 2] {p : ℕ}
    {B Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r : G}
    {ψ : Matrix.SpecialLinearGroup (Fin n) F →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) F}
    (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M) {b : G} (hbBs : b ∈ Bs) (hb1 : b ≠ 1)
    {Dm : GL (Fin n) F} {τ : Fin n → F} (hDm : (Dm : Matrix (Fin n) (Fin n) F) = diagonal τ)
    (hb : ∀ s, b * ggFrame ψ A₀ s * b⁻¹ = ggFrame ψ A₀ (slConj n F Dm s))
    {S : Finset (Fin n)} {μ : F} (hS : ∀ i ∈ S, τ i = μ) (hSc : ∀ i ∉ S, τ i ≠ μ)
    (hcard : Sᶜ.card < S.card) (hS2 : 2 ≤ S.card) (hSc2 : Sᶜ.card ≤ 2) {i₁ : Fin n}
    (hi₁ : i₁ ∉ S) {l : ℕ} (σ : Equiv.Perm (Fin n))
    (hpair : ∀ a c : Fin n, (σ c : ℕ) < l → (σ a : ℕ) = σ c + (n - l) → τ a = τ c) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  have hrangeφ : (ggFrame ψ A₀).range = G₀ := (range_ggFrame ψ A₀).trans hc.range
  have hW := ggSixFusionWitness_of_frame (D := D) (E := E) (t := t) (f := f) hc.prime hc.dvd
    hc.four hc.bstar (ker_ggFrame_le hc.ker A₀) hrangeφ hc.cent hc.frame hbBs hb1 hDm hb hS hSc
    hcard hS2 hSc2 hi₁
  set P : Matrix.SpecialLinearGroup (Fin n) F := ggPermSL σ with hP
  set u := ggInvSL n l F with hu
  have hfix : P * u * P⁻¹ ∈ ggFix (slConj n F Dm) := by
    rw [TypeA.mem_ggFix_slConjugation_iff hDm]
    intro a c hac
    rw [hP, coe_ggPermSL_conj, Matrix.submatrix_apply, hu, coe_ggInvSL, ggInvMatrix,
      Matrix.add_apply, ggInvNil_apply]
    have hac' : a ≠ c := by
      rintro rfl
      exact hac rfl
    rw [Matrix.one_apply_ne (fun h => hac' (σ.injective h)), zero_add]
    split_ifs with h
    · exact absurd (hpair a c h.1 h.2.1) hac
    · rfl
  have hwG : ψ (A₀ * P) ∈ G₀ := hc.range ▸ (⟨A₀ * P, rfl⟩ : ψ (A₀ * P) ∈ ψ.range)
  refine ggRootFusionWitnessAlt_of_conj_comm ψ (w := A₀ * P) ?_ (hle hwG) hW
  have he : A₀ * P * u * (A₀ * P)⁻¹ = A₀ * (P * u * P⁻¹) * A₀⁻¹ := by group
  have h1 : b * ggFrame ψ A₀ (P * u * P⁻¹) * b⁻¹ = ggFrame ψ A₀ (P * u * P⁻¹) := by
    rw [hb, mem_ggFix.mp hfix]
  rw [he, ← ggFrame_apply]
  calc b * ggFrame ψ A₀ (P * u * P⁻¹) = b * ggFrame ψ A₀ (P * u * P⁻¹) * b⁻¹ * b := by group
    _ = ggFrame ψ A₀ (P * u * P⁻¹) * b := by rw [h1]

theorem prod_update_const {M₀ : Type} [CommMonoid M₀] (a : Fin n) (x y : M₀) :
    ∏ i, Function.update (fun _ => x) a y i = y * x ^ (n - 1) := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ a), Finset.prod_const,
    Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin]

theorem prod_update_update_const {M₀ : Type} [CommMonoid M₀] {a c : Fin n} (hac : a ≠ c)
    (x y z : M₀) :
    ∏ i, Function.update (Function.update (fun _ => x) a y) c z i = z * (y * x ^ (n - 2)) := by
  have hcard : ((Finset.univ \ {c}) \ {a} : Finset (Fin n)).card = n - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem (by simpa using hac), Finset.card_erase_of_mem (Finset.mem_univ c),
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [Finset.prod_update_of_mem (Finset.mem_univ c), Finset.prod_update_of_mem
    (by simpa using hac : a ∈ Finset.univ \ {c}), Finset.prod_const, hcard]

theorem ggDiagSL_pow_eq_one [CharP F 2] {p : ℕ} {δ : Fin n → F} (hδ : ∏ i, δ i = 1)
    (hδp : ∀ i, δ i ^ p = 1) : ggDiagSL δ hδ ^ p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (diagonal δ) ^ p = 1
  rw [diagonal_pow, ← diagonal_one]
  congr 1
  funext i
  exact hδp i

theorem ggRootFusionWitnessAlt_of_inner [Finite F] [CharP F 2] {p : ℕ}
    {B Bs D E G₀ M : Subgroup G} {t : StatedLieTag} {f : ℕ} {r : G}
    {ψ : Matrix.SpecialLinearGroup (Fin n) F →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) F}
    (hc : FrameCtx p B Bs G₀ ψ A₀) (hle : G₀ ≤ M) {δ : Fin n → F} (hδ : ∏ i, δ i = 1)
    (hδp : ∀ i, δ i ^ p = 1) {S : Finset (Fin n)} {μ : F} (hS : ∀ i ∈ S, δ i = μ)
    (hSc : ∀ i ∉ S, δ i ≠ μ) (hcard : Sᶜ.card < S.card) (hS2 : 2 ≤ S.card)
    (hSc2 : Sᶜ.card ≤ 2) {i₁ : Fin n} (hi₁ : i₁ ∉ S) {l : ℕ} (σ : Equiv.Perm (Fin n))
    (hpair : ∀ a c : Fin n, (σ c : ℕ) < l → (σ a : ℕ) = σ c + (n - l) → δ a = δ c) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ (ggInvSL n l F)) := by
  set d := ggDiagSL δ hδ with hd
  have hdδ : (d : Matrix (Fin n) (Fin n) F) = diagonal δ := rfl
  obtain ⟨i₀, hi₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hb := act_map (ggFrame ψ A₀) d
  have hbBs := mem_of_frame_diagonal_inner hc.bstar hc.frame hdδ (ggDiagSL_pow_eq_one hδ hδp)
  have hne : δ i₁ ≠ δ i₀ := by rw [hS i₀ hi₀]; exact hSc i₁ hi₁
  have hb1 := ne_one_of_frame (ker_ggFrame_le hc.ker A₀) hdδ hb hne
  exact ggRootFusionWitnessAlt_of_frame hc hle hbBs hb1 hdδ hb hS hSc hcard hS2 hSc2 hi₁ σ hpair

end SLRep

end CFSG.StandardType
