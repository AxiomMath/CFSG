module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5n

public section

namespace CFSG.Quasithin.H13.S127.L5.Sp4

open CFSG.Open Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace StdSplit

variable {K U Z V : Subgroup G} {α : ↥K →* ↥(StatedSp 2 F)}
  {β : ↥U →* Multiplicative (Fin 2 ⊕ Fin 2 → F)} (s : StdSplit K U Z V α β)
include s

omit [Finite G] [Fintype F] in
theorem diag_conj {l : F} (hl0 : l ≠ 0) {δ : ↥K} (hδ : α δ = ⟨diagGL hl0, diagGL_mem hl0⟩)
    {v : G} (hv : v ∈ V) :
    ∃ h : (δ : G) * v * (δ : G)⁻¹ ∈ U, (δ : G) * v * (δ : G)⁻¹ ∈ V ∧
      Multiplicative.toAdd (β ⟨_, h⟩) = l • Multiplicative.toAdd (β ⟨v, s.VU hv⟩) := by
  have hU := s.conj_mem δ.2 (s.VU hv)
  refine ⟨hU, ?_⟩
  have hmem := (s.memV ⟨v, s.VU hv⟩).mp hv
  set x : Fin 2 → F := fun i => Multiplicative.toAdd (β ⟨v, s.VU hv⟩) (Sum.inl i) with hx
  have hβv : Multiplicative.toAdd (β ⟨v, s.VU hv⟩) = Sum.elim x 0 := by
    funext i
    rcases i with i | i
    · rfl
    · exact mem_ell0.mp hmem i
  have hβ : Multiplicative.toAdd (β ⟨_, hU⟩) = l • Multiplicative.toAdd (β ⟨v, s.VU hv⟩) := by
    rw [s.equiv δ ⟨v, s.VU hv⟩ ⟨_, hU⟩ rfl, hδ, hβv]
    exact diagMat_mulVec_elim l x
  refine ⟨(s.memV ⟨_, hU⟩).mpr ?_, hβ⟩
  rw [hβ]
  exact ell0.smul_mem l hmem

theorem exists_complement (hF : Fintype.card F = 4) :
    ∃ W : Subgroup G, W ≤ V ∧
      K ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (W : Set G) ∧
      W ⊓ Z = ⊥ ∧ W ⊔ Z = V := by
  classical
  have : CharP F 2 :=
    FFC.charP_two_of_card_pow (n := 2) (by rw [Nat.card_eq_fintype_card, hF]; norm_num)
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hno x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hF] at this
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  have hl3 : l ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one l hl0
    rwa [hF] at this
  have hlq : 1 + l + l ^ 2 = 0 := by
    have h : (l - 1) * (1 + l + l ^ 2) = 0 := by linear_combination hl3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hl1
    · exact h
  obtain ⟨δ, hδ⟩ := s.surjα ⟨diagGL hl0, diagGL_mem hl0⟩
  set c : G → G := fun v => (δ : G) * v * (δ : G)⁻¹ with hc
  have hcV : ∀ v ∈ V, c v ∈ V := fun v hv => (s.diag_conj hl0 hδ hv).2.1
  have hcβ : ∀ v (hv : v ∈ V), Multiplicative.toAdd (β ⟨c v, s.VU (hcV v hv)⟩) =
      l • Multiplicative.toAdd (β ⟨v, s.VU hv⟩) := fun v hv => (s.diag_conj hl0 hδ hv).2.2
  have hcmul : ∀ a b : G, c (a * b) = c a * c b := fun a b => by simp only [hc]; group
  set N : G → G := fun v => v * c v * c (c v) with hN
  have hNU : ∀ v ∈ V, N v ∈ V := fun v hv =>
    V.mul_mem (V.mul_mem hv (hcV v hv)) (hcV _ (hcV v hv))
  have hcZ : ∀ z ∈ Z, c z = z := fun z hz => by
    simp only [hc]
    rw [s.Zc z hz δ δ.2, mul_inv_cancel_right]
  have hNmul : ∀ a ∈ V, ∀ b ∈ V, N (a * b) = N a * N b := by
    intro a ha b hb
    have hU : ∀ x ∈ V, x ∈ U := fun x hx => s.VU hx
    have e1 : b * c a = c a * b := s.comm _ (hU _ hb) _ (hU _ (hcV a ha))
    have e2 : b * c b * c (c a) = c (c a) * (b * c b) :=
      s.comm _ (U.mul_mem (hU _ hb) (hU _ (hcV b hb))) _ (hU _ (hcV _ (hcV a ha)))
    simp only [hN, hcmul]
    calc a * b * (c a * c b) * (c (c a) * c (c b))
        = a * (b * c a) * c b * (c (c a) * c (c b)) := by group
      _ = a * (c a * b) * c b * (c (c a) * c (c b)) := by rw [e1]
      _ = a * c a * (b * c b * c (c a)) * c (c b) := by group
      _ = a * c a * (c (c a) * (b * c b)) * c (c b) := by rw [e2]
      _ = a * c a * c (c a) * (b * c b * c (c b)) := by group
  have hNZ : ∀ v (hv : v ∈ V), N v ∈ Z := by
    intro v hv
    have hβN : Multiplicative.toAdd (β ⟨N v, s.VU (hNU v hv)⟩) = 0 := by
      have hm : (⟨N v, s.VU (hNU v hv)⟩ : ↥U) = ⟨v, s.VU hv⟩ * ⟨c v, s.VU (hcV v hv)⟩ *
          ⟨c (c v), s.VU (hcV _ (hcV v hv))⟩ := rfl
      rw [hm, map_mul β, map_mul β, toAdd_mul, toAdd_mul, hcβ (c v) (hcV v hv), hcβ v hv,
        smul_smul, ← pow_two]
      calc Multiplicative.toAdd (β ⟨v, s.VU hv⟩) + l • Multiplicative.toAdd (β ⟨v, s.VU hv⟩) +
            l ^ 2 • Multiplicative.toAdd (β ⟨v, s.VU hv⟩)
          = (1 + l + l ^ 2) • Multiplicative.toAdd (β ⟨v, s.VU hv⟩) := by
            rw [add_smul, add_smul, one_smul]
        _ = 0 := by rw [hlq, zero_smul]
    exact s.mem_Z hβN
  have hsqZ : ∀ z ∈ Z, z * z = 1 := fun z hz => by
    have := s.sq z (s.ZU hz)
    rwa [pow_two] at this
  have hNz : ∀ z ∈ Z, N z = z := fun z hz => by
    simp only [hN]
    rw [hcZ z hz, hcZ z hz, hsqZ z hz, one_mul]
  let W : Subgroup G :=
    { carrier := {v | v ∈ V ∧ N v = 1}
      mul_mem' := fun {a b} ha hb => ⟨V.mul_mem ha.1 hb.1, by rw [hNmul a ha.1 b hb.1, ha.2, hb.2,
        one_mul]⟩
      one_mem' := ⟨V.one_mem, by simp [hN, hc]⟩
      inv_mem' := fun {a} ha => by
        have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by
          have := s.sq a (s.VU ha.1)
          rwa [pow_two] at this)
        rw [h1]
        exact ha }
  have hWV : W ≤ V := fun w hw => hw.1
  refine ⟨W, hWV, ?_, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨hgK, hgN⟩ := hg
    set g' : ↥K := ⟨g, hgK⟩ with hg'
    set h : ↥K := g'⁻¹ * δ * g' * δ⁻¹ with hh
    have hfix : ∀ x : Fin 2 → F, mat (α h) *ᵥ Sum.elim x 0 = Sum.elim x 0 := by
      intro x
      have hw := s.mulVec_mem_ell0 (g := g') hgN (elim_mem_ell0 (l⁻¹ • x))
      set x₁ : Fin 2 → F := fun i => (mat (α g') *ᵥ Sum.elim (l⁻¹ • x) 0) (Sum.inl i)
      have hx₁ : mat (α g') *ᵥ Sum.elim (l⁻¹ • x) 0 = Sum.elim x₁ 0 := by
        funext i
        rcases i with i | i
        · rfl
        · exact mem_ell0.mp hw i
      have hmat : mat (α h) = mat (α g')⁻¹ * diagMat l * mat (α g') * diagMat l⁻¹ := by
        rw [hh, map_mul, map_mul, map_mul, map_inv, map_inv, hδ]
        rfl
      have hsm : Sum.elim (l⁻¹ • x) (0 : Fin 2 → F) = l⁻¹ • Sum.elim x 0 := by
        funext i
        rcases i with i | i <;> simp
      rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        diagMat_mulVec_elim, ← hsm, hx₁, diagMat_mulVec_elim, ← hx₁, Matrix.mulVec_smul,
        mat_inv_mulVec, hsm, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    have hcen := fun v (hv : v ∈ V) => s.centralize_of_fix hF hfix hv
    have hkey : ∀ v ∈ V, c (g * v * g⁻¹) = g * c v * g⁻¹ := by
      intro v hv
      have h1 := hcen (c v) (hcV v hv)
      have h2 : ((h : ↥K) : G) = g⁻¹ * δ * g * (δ : G)⁻¹ := by
        rw [hh]
        simp [hg']
      rw [h2] at h1
      simp only [hc] at h1 ⊢
      calc (δ : G) * (g * v * g⁻¹) * (δ : G)⁻¹
          = g * ((g⁻¹ * δ * g * (δ : G)⁻¹) * (δ * v * (δ : G)⁻¹)) *
              (g⁻¹ * δ * g * (δ : G)⁻¹)⁻¹ * g⁻¹ := by group
        _ = g * ((δ * v * (δ : G)⁻¹) * (g⁻¹ * δ * g * (δ : G)⁻¹)) *
              (g⁻¹ * δ * g * (δ : G)⁻¹)⁻¹ * g⁻¹ := by rw [h1]
        _ = g * (δ * v * (δ : G)⁻¹) * g⁻¹ := by group
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    have hgw : g * w * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgN w).mp hw.1
    refine ⟨hgw, ?_⟩
    simp only [hN]
    rw [hkey w hw.1, hkey (c w) (hcV w hw.1)]
    calc g * w * g⁻¹ * (g * c w * g⁻¹) * (g * c (c w) * g⁻¹) = g * N w * g⁻¹ := by
          simp only [hN]; group
      _ = 1 := by rw [hw.2]; group
  ·
    refine eq_bot_iff.mpr fun z hz => ?_
    obtain ⟨⟨-, hNz1⟩, hzZ⟩ := hz
    rw [Subgroup.mem_bot, ← hNz z hzZ]
    exact hNz1
  ·
    refine le_antisymm (sup_le hWV s.Z_le_V) fun v hv => ?_
    have hNv := hNZ v hv
    have hvN : v * N v ∈ W := by
      refine ⟨V.mul_mem hv (s.Z_le_V hNv), ?_⟩
      rw [hNmul v hv (N v) (s.Z_le_V hNv), hNz (N v) hNv, hsqZ (N v) hNv]
    have : v = (v * N v) * (N v)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hvN)
      (Subgroup.mem_sup_right (Z.inv_mem hNv))

end StdSplit

end CFSG.Quasithin.H13.S127.L5.Sp4
