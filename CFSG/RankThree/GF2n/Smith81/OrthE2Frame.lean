module

public import CFSG.RankThree.GF2n.Smith81.OrthRootFwd
public import CFSG.RankThree.GF2n.Smith81.OrthNoA2
public import CFSG.RankThree.GF2n.Smith81.Orth52
public import CFSG.RankThree.GF2n.Smith81.OrthFactors

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80


theorem exists_mem_M_eq_conj_of_tacit {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (h34 : Stroth34Statement) (hc : SmithOrthCfg M Q Z B)
    (hT : ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') ∧ GenByB M Q B')
    {C : Subgroup G} (hC : Ctx M Q Z C) : ∃ m ∈ M, C = conjSubgroup m B := by
  obtain ⟨n, hw, -, h4⟩ := hc.orth.exists_width
  have h15c : ∀ B' : Subgroup G, Ctx M Q Z B' →
      CQt Q Z (LB M Q B') = ((B' ⊔ Z : Subgroup G) : Set G) := fun B' hB' =>
    (stroth_3_5 h34 hB' hw (by omega) (hT B' hB').1 (hT B' hB').2).2.1
  have h25 := smith25_of_117 smith117Statement_holds hc.ctx hw (by omega)
    (fun B' hB' => (hT B' hB').1) h15c
  have hmem : C ⊔ Z ∈ {V : Subgroup G | ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ∧ A ≠ Z ∧
      V = A ⊔ Z} := ⟨C, hC.conj, hC.le, hC.ne, rfl⟩
  rw [h25] at hmem
  obtain ⟨m, hm, hCm⟩ := hmem
  have hcm : Ctx M Q Z (conjSubgroup m B) := hc.ctx.conj_of_mem hm
  have hle : conjSubgroup m B ≤ Z ⊔ C := by
    rw [sup_comm, hCm]
    exact le_sup_left
  obtain ⟨p, hpQ, hp⟩ := hC.exists_conj_of_le_ZB hcm hle
  have hpM : p ∈ M := hc.ctx.hyp.Q_normal.1 hpQ
  refine ⟨p⁻¹ * m, M.mul_mem (M.inv_mem hpM) hm, ?_⟩
  rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem orthSLPartStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → ∀ (t : G) (m : ℕ),
      3 ≤ m → (CaseE2Plus M Q Z B t m ∨ CaseE2Minus M Q Z B t m) →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
        (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) →
        ∀ s ∈ Lgen M (LB M Q B), ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 →
          ActsAsTensor Q Z M₀ φ s g id → ∀ x ∈ M, ∃ g' : Matrix (Fin 2) (Fin 2) K, g'.det = 1 ∧
            ActsAsTensor Q Z M₀ φ (x * s * x⁻¹) g' id :=
  fun _ _ _ _ _ _ _ hcB _ _ hm hE _ _ _ _ _ _ hD _ _ _ _ _ hAct => slPart_normal hcB hm hE hD hAct

theorem smith24ActE2_of (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hG : StrothGenByBStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (m : ℕ),
      SmithOrthCfg M Q Z B → CtxD4 M Q Z B t → 3 ≤ m →
      (CaseE2Plus M Q Z B t m ∨ CaseE2Minus M Q Z B t m) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
        ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
          (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
          OrthFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) := by
  intro G _ _ M Q Z B t m hc ht hm hE
  have hT := orthTacit_of_caseE2 hc.toCfg ((caseE2_iff M Q Z B t m).mpr hE) hG
  obtain ⟨hno, hgen⟩ := hT B hc.ctx
  have hw : Width Q Z (2 * m) := by
    unfold Width
    rcases hE with hE | hE
    · rw [hE.2.1]; congr 1; ring
    · rw [hE.2.1]; congr 1; ring
  have hs : Sec5Hyp hc.ctx (2 * m) t := ⟨hw, by omega, hno, hgen, ht.2.1, ht.2.2.1⟩
  have hmodel : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
        (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) ∧
          OrthBLine M₀ qU φ B := by
    rcases hE with hE | hE
    · exact smith24E2Plus_tensorB h34 hc ht hm hE hno hgen
        (orth_e2Natural_plus h34 h310 hc.ctx hs hm hE)
    · exact smith24E2Minus_tensorB h34 hc ht hm hE hno hgen
        (orth_e2Natural_minus h34 h310 hc.ctx hs hm hE)
  obtain ⟨K, _, _, _, γ, M₀, hD, ι, _, _, qU, φ, hF, hAct, c, u, hc0, hu0, hBimg, -⟩ := hmodel
  refine ⟨K, inferInstance, inferInstance, inferInstance, γ, M₀, hD, ι, inferInstance,
    inferInstance, qU, φ, ?_, hAct⟩
  have hn : 4 ≤ Fintype.card ι := by
    obtain ⟨n, hw', -, h4⟩ := hc.orth.exists_width
    have hZ : 2 ≤ Nat.card Z := by have := hc.ctx.hyp.q4; omega
    rw [width_eq_of_width hZ (width_of_tensor hD φ) hw']
    exact h4
  exact orthFrame_of_tensor hc.ctx (fun C hC => exists_mem_M_eq_conj_of_tacit h34 hc hT hC)
    (fun C hC => (hT C hC).1) hD hF hAct
    (orthSLPartStatement_holds G M Q Z B hc.ctx t m hm hE K γ M₀ hD ι qU φ hAct) hn hc0 hu0 hBimg

@[expose] def Smith24ActFourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    (∃ t : G, CtxD4 M Q Z B t ∧ (CaseE1 M Q Z B t ∨ CaseE2 M Q Z B t 2)) →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ),
      GlobalModelData M Q Z γ M₀ ∧ ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))

theorem smith24Act_of_four (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hG : StrothGenByBStatement) (hFour : Smith24ActFourStatement) : Smith24ActStatement := by
  intro G _ _ M Q Z B hc
  obtain ⟨t, ht, h1 | ⟨m, hm⟩⟩ := hc.orth
  · exact hFour G M Q Z B hc ⟨t, ht, Or.inl h1⟩
  · rcases Nat.lt_or_ge m 3 with h | h
    · have h2 : m = 2 := by have := hm.1; omega
      subst h2
      exact hFour G M Q Z B hc ⟨t, ht, Or.inr hm⟩
    · exact smith24ActE2_of h34 h310 hG G M Q Z B t m hc ht h
        ((caseE2_iff M Q Z B t m).mp hm)

end CFSG.RankThree.GF2n.Smith81
