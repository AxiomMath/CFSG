module

public import CFSG.Milestones.ASVolI.F429.aC2cU4Mat
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F429.aC5corrU4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {E : Type} [Group E]

theorem burnsideF429a_coe_conj {Gp : Subgroup E} {C : Type} [Group C] (Ψ : C ≃* ↥Gp) (u v : C) :
    ((Ψ u : ↥Gp) : E) * ((Ψ v : ↥Gp) : E) * ((Ψ u : ↥Gp) : E)⁻¹ = ((Ψ (u * v * u⁻¹) : ↥Gp) : E) := by
  simp [map_mul, map_inv]

theorem burnsideF429a_eq_one_of_act {Gp : Subgroup E} (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {e : E}
    (he : ∀ y : C, e * ((Ψ y : ↥Gp) : E) * e⁻¹ = ((Ψ y : ↥Gp) : E)) : e = 1 := by
  have hmem : e ∈ Subgroup.centralizer (Gp : Set E) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨y, rfl⟩ : ∃ y, ((Ψ y : ↥Gp) : E) = g := ⟨Ψ.symm ⟨g, hg⟩, by simp⟩
    calc ((Ψ y : ↥Gp) : E) * e = (e * ((Ψ y : ↥Gp) : E) * e⁻¹) * e := by rw [he]
      _ = e * ((Ψ y : ↥Gp) : E) := by group
  rw [hc] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem burnsideF429a_eq_of_act {Gp : Subgroup E} (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {e₁ e₂ : E}
    (he : ∀ y : C, e₁ * ((Ψ y : ↥Gp) : E) * e₁⁻¹ = e₂ * ((Ψ y : ↥Gp) : E) * e₂⁻¹) : e₁ = e₂ := by
  have h1 : e₂⁻¹ * e₁ = 1 := burnsideF429a_eq_one_of_act hc Ψ fun y => by
    calc e₂⁻¹ * e₁ * ((Ψ y : ↥Gp) : E) * (e₂⁻¹ * e₁)⁻¹ =
        e₂⁻¹ * (e₁ * ((Ψ y : ↥Gp) : E) * e₁⁻¹) * e₂ := by group
      _ = ((Ψ y : ↥Gp) : E) := by rw [he]; group
  calc e₁ = e₂ * (e₂⁻¹ * e₁) := by group
    _ = e₂ := by rw [h1, mul_one]

theorem burnsideF429a_eq_one_of_central {Gp : Subgroup E}
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {u : C}
    (hu : ∀ y : C, u * y * u⁻¹ = y) : u = 1 := by
  have h1 : ((Ψ u : ↥Gp) : E) = 1 := burnsideF429a_eq_one_of_act hc Ψ fun y => by
    rw [burnsideF429a_coe_conj, hu]
  have h2 : Ψ u = 1 := Subtype.ext h1
  exact Ψ.injective (by rw [h2, map_one])

end Generic

section Rank

theorem burnsideF429a_rank_conj_rect {m n F : Type} [Fintype m] [Fintype n] [DecidableEq n]
    [Field F] {R : Matrix m n F} {Ri : Matrix n m F} (hRR : Ri * R = 1) (X : Matrix n n F) :
    (R * X * Ri).rank = X.rank := by
  refine le_antisymm ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)) ?_
  have e : X = Ri * (R * X * Ri) * R := by
    calc X = (Ri * R) * X * (Ri * R) := by rw [hRR, Matrix.one_mul, Matrix.mul_one]
      _ = Ri * (R * X * Ri) * R := by simp only [Matrix.mul_assoc]
  calc X.rank = (Ri * (R * X * Ri) * R).rank := by rw [← e]
    _ ≤ (R * X * Ri).rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Rank

section U4Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429a_U4_frobElt_mul (u v : hypSU h 2 0) :
    frobElt h (u * v) = frobElt h u * frobElt h v := by
  rw [← frob_apply, ← frob_apply, ← frob_apply, map_mul]

theorem burnsideF429a_U4_frobElt_inv (u : hypSU h 2 0) : frobElt h u⁻¹ = (frobElt h u)⁻¹ := by
  rw [← frob_apply, ← frob_apply, map_inv]

theorem burnsideF429a_U4_fieldAut_z0 (τ : K ≃+* K) :
    fieldAut h τ (burnsideF429a_U4_z0 h) = burnsideF429a_U4_z0 h := by
  apply hypSU_ext h
  rw [fieldAut_apply, mat_fieldHom, burnsideF429a_U4_coe_z0,
    Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.map_single,
    map_one]

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429a_U4_inv_classify [Finite E] [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom)
    {t : E} (htM : t ∈ M₁ ⊓ M₂) (htG : t ∉ Gp) (ht2 : t * t = 1) :
    ∃ a : hypSU h 2 0,
      (∀ x, ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) = t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) ∨
      (∀ x, ((Φ (a * burnsideF429a_U4_z0 h * frobElt h x * (a * burnsideF429a_U4_z0 h)⁻¹) :
        ↥Gp) : E) = t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) := by
  have := h.finite
  obtain ⟨g, -, τ, hgτ⟩ := burnsideF429a_U4_nf h Φ hP₁ hP₂ htM
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply htG
    have e1 : ∀ x, ((Φ (g * x * g⁻¹) : ↥Gp) : E) = t * ((Φ x : ↥Gp) : E) * t⁻¹ := by
      intro x
      have := hgτ x
      rwa [fieldAut_apply, fieldHom_one] at this
    rw [burnsideF429a_eq_of_conj hc Φ e1]
    exact (Φ g).2
  have hτ2 : τ * τ = 1 := by
    apply burnsideF429a_U4_fieldAut_eq_one_of_inner h
    refine ⟨(g * fieldAut h τ g)⁻¹, MulEquiv.ext fun x => ?_⟩
    have e1 : ((Φ (g * fieldAut h τ (g * fieldAut h τ x * g⁻¹) * g⁻¹) : ↥Gp) : E) =
        ((Φ x : ↥Gp) : E) := by
      rw [hgτ, hgτ]
      calc t * (t * ((Φ x : ↥Gp) : E) * t⁻¹) * t⁻¹ =
          (t * t) * ((Φ x : ↥Gp) : E) * (t * t)⁻¹ := by group
        _ = ((Φ x : ↥Gp) : E) := by rw [ht2]; group
    have e2 := Φ.injective (Subtype.ext e1)
    rw [map_mul, map_mul, map_inv] at e2
    have e3 : fieldAut h (τ * τ) x = fieldAut h τ (fieldAut h τ x) := fieldHom_mul h τ τ x
    show (g * fieldAut h τ g)⁻¹ * x * ((g * fieldAut h τ g)⁻¹)⁻¹ = fieldAut h (τ * τ) x
    rw [e3]
    calc (g * fieldAut h τ g)⁻¹ * x * ((g * fieldAut h τ g)⁻¹)⁻¹ =
        (g * fieldAut h τ g)⁻¹ * (g * (fieldAut h τ g * fieldAut h τ (fieldAut h τ x) *
          (fieldAut h τ g)⁻¹) * g⁻¹) * (g * fieldAut h τ g) := by rw [e2]; group
      _ = fieldAut h τ (fieldAut h τ x) := by group
  have hτb : ∀ c, τ c = h.bar c := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar h hτ2 with h1 | h1
    · exact absurd h1 hτ1
    · exact h1
  have hgγ : ∀ x, ((Φ (g * frobElt h x * g⁻¹) : ↥Gp) : E) = t * ((Φ x : ↥Gp) : E) * t⁻¹ := by
    intro x
    rw [← burnsideF429a_U4_fieldAut_eq_frob h hτb]
    exact hgτ x
  have hgg : g * frobElt h g = 1 := by
    apply burnsideF429a_eq_one_of_central hc Φ
    intro y
    have e1 : ((Φ (g * frobElt h (g * frobElt h y * g⁻¹) * g⁻¹) : ↥Gp) : E) =
        ((Φ y : ↥Gp) : E) := by
      rw [hgγ, hgγ]
      calc t * (t * ((Φ y : ↥Gp) : E) * t⁻¹) * t⁻¹ =
          (t * t) * ((Φ y : ↥Gp) : E) * (t * t)⁻¹ := by group
        _ = ((Φ y : ↥Gp) : E) := by rw [ht2]; group
    have e2 := Φ.injective (Subtype.ext e1)
    rw [burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_inv,
      frobElt_frobElt] at e2
    calc g * frobElt h g * y * (g * frobElt h g)⁻¹ =
        g * (frobElt h g * y * (frobElt h g)⁻¹) * g⁻¹ := by group
      _ = y := e2
  obtain ⟨a, ha | ha⟩ := burnsideF429a_U4_cocycle h hgg
  · refine ⟨a, Or.inl fun x => ?_⟩
    have e : a * frobElt h x * a⁻¹ =
        g * (frobElt h a * frobElt h x * (frobElt h a)⁻¹) * g⁻¹ := by
      calc a * frobElt h x * a⁻¹ = (g * frobElt h a) * frobElt h x * (g * frobElt h a)⁻¹ := by
            rw [ha]
        _ = _ := by group
    rw [← hgγ, burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul,
      burnsideF429a_U4_frobElt_inv, ← e]
  · refine ⟨a, Or.inr fun x => ?_⟩
    have e : a * burnsideF429a_U4_z0 h * frobElt h x * (a * burnsideF429a_U4_z0 h)⁻¹ =
        g * (frobElt h a * frobElt h x * (frobElt h a)⁻¹) * g⁻¹ := by
      calc a * burnsideF429a_U4_z0 h * frobElt h x * (a * burnsideF429a_U4_z0 h)⁻¹ =
          (g * frobElt h a) * frobElt h x * (g * frobElt h a)⁻¹ := by rw [ha]
        _ = _ := by group
    rw [← hgγ, burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul,
      burnsideF429a_U4_frobElt_inv, ← e]

theorem burnsideF429a_U4_graph_inv (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (Φ : hypSU h 2 0 ≃* ↥Gp) {s : E} (a : hypSU h 2 0)
    (hs : ∀ x, ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) = s * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * s⁻¹) :
    s ∉ Gp ∧ s * s = 1 := by
  constructor
  · intro hsG
    obtain ⟨w, hw⟩ : ∃ w, ((Φ w : ↥Gp) : E) = s := ⟨Φ.symm ⟨s, hsG⟩, by simp⟩
    have hinner : fieldAut h (barEquiv h) ∈
        (MulAut.conj : hypSU h 2 0 →* MulAut (hypSU h 2 0)).range := by
      refine ⟨a⁻¹ * w * a, MulEquiv.ext fun x => ?_⟩
      have e1 := hs x
      rw [← hw, burnsideF429a_coe_conj] at e1
      have e2 := Φ.injective (Subtype.ext e1)
      rw [MulAut.conj_apply, burnsideF429a_U4_fieldAut_eq_frob h (fun c => barEquiv_apply h c)]
      calc a⁻¹ * w * a * x * (a⁻¹ * w * a)⁻¹ = a⁻¹ * (w * (a * x * a⁻¹) * w⁻¹) * a := by group
        _ = a⁻¹ * (a * frobElt h x * a⁻¹) * a := by rw [← e2]
        _ = frobElt h x := by group
    have h1 := burnsideF429a_U4_fieldAut_eq_one_of_inner h hinner
    have h2 := burnsideF429a_U4_orderOf_barEquiv h
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · apply burnsideF429a_eq_one_of_act hc Φ
    intro y
    obtain ⟨x, rfl⟩ : ∃ x, a * x * a⁻¹ = y := ⟨a⁻¹ * y * a, by group⟩
    calc s * s * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * (s * s)⁻¹ =
        s * (s * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * s⁻¹) * s⁻¹ := by group
      _ = s * ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) * s⁻¹ := by rw [← hs x]
      _ = ((Φ (a * frobElt h (frobElt h x) * a⁻¹) : ↥Gp) : E) := by rw [← hs (frobElt h x)]
      _ = ((Φ (a * x * a⁻¹) : ↥Gp) : E) := by rw [frobElt_frobElt]

theorem burnsideF429a_U4_typeIII_split (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (Φ : hypSU h 2 0 ≃* ↥Gp) {t : E} (a : hypSU h 2 0)
    (ht : ∀ x, ((Φ (a * burnsideF429a_U4_z0 h * frobElt h x * (a * burnsideF429a_U4_z0 h)⁻¹) :
      ↥Gp) : E) = t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹)
    {z s : E} (hz : z = ((Φ (a * burnsideF429a_U4_z0 h * a⁻¹) : ↥Gp) : E)) (hs : s = t * z⁻¹) :
    (∀ x, ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) = s * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * s⁻¹) ∧
      s * z = z * s := by
  set z₀ := burnsideF429a_U4_z0 h with hz₀
  have hz2 : z₀ * z₀ = 1 := burnsideF429a_U4_z0_mul_self h
  have hzi : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz2
  have hγz : frobElt h z₀ = z₀ := burnsideF429a_U4_frobElt_z0 h
  have hsact : ∀ x, ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) =
      s * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * s⁻¹ := by
    intro x
    have e1 : z⁻¹ * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * z =
        ((Φ (a * (z₀ * x * z₀) * a⁻¹) : ↥Gp) : E) := by
      rw [hz]
      have e := burnsideF429a_coe_conj Φ (a * z₀ * a⁻¹)⁻¹ (a * x * a⁻¹)
      rw [inv_inv, map_inv, Subgroup.coe_inv, inv_inv] at e
      rw [e]
      congr 2
      calc (a * z₀ * a⁻¹)⁻¹ * (a * x * a⁻¹) * (a * z₀ * a⁻¹) = a * (z₀⁻¹ * x * z₀) * a⁻¹ := by
            group
        _ = a * (z₀ * x * z₀) * a⁻¹ := by rw [hzi]
    have e2 := ht (z₀ * x * z₀)
    have e3 : a * z₀ * frobElt h (z₀ * x * z₀) * (a * z₀)⁻¹ = a * frobElt h x * a⁻¹ := by
      rw [burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul, hγz]
      calc a * z₀ * (z₀ * frobElt h x * z₀) * (a * z₀)⁻¹ =
          a * (z₀ * z₀) * frobElt h x * (z₀ * z₀⁻¹) * a⁻¹ := by group
        _ = a * frobElt h x * a⁻¹ := by rw [hz2, mul_inv_cancel]; group
    rw [e3] at e2
    rw [e2, hs, ← e1]
    group
  refine ⟨hsact, burnsideF429a_eq_of_act hc Φ fun y => ?_⟩
  obtain ⟨x, rfl⟩ : ∃ x, a * x * a⁻¹ = y := ⟨a⁻¹ * y * a, by group⟩
  have hzc : ∀ w : hypSU h 2 0, z * ((Φ w : ↥Gp) : E) * z⁻¹ =
      ((Φ (a * z₀ * a⁻¹ * w * (a * z₀ * a⁻¹)⁻¹) : ↥Gp) : E) := fun w => by
    rw [hz, burnsideF429a_coe_conj]
  calc s * z * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * (s * z)⁻¹ =
      s * (z * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * z⁻¹) * s⁻¹ := by group
    _ = s * ((Φ (a * (z₀ * x * z₀⁻¹) * a⁻¹) : ↥Gp) : E) * s⁻¹ := by
        rw [hzc]
        congr 4
        group
    _ = ((Φ (a * frobElt h (z₀ * x * z₀⁻¹) * a⁻¹) : ↥Gp) : E) := by rw [← hsact]
    _ = ((Φ (a * z₀ * a⁻¹ * (a * frobElt h x * a⁻¹) * (a * z₀ * a⁻¹)⁻¹) : ↥Gp) : E) := by
        rw [burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul,
          burnsideF429a_U4_frobElt_inv, hγz]
        congr 2
        group
    _ = z * (s * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * s⁻¹) * z⁻¹ := by rw [← hzc, ← hsact]
    _ = z * s * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * (z * s)⁻¹ := by group

theorem burnsideF429a_U4_comm_of_comm [Finite E] [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ x ∈ M₁ ⊓ M₂, e = n * x) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom)
    {t : E} (a : hypSU h 2 0)
    (ht : ∀ x, ((Φ (a * burnsideF429a_U4_z0 h * frobElt h x * (a * burnsideF429a_U4_z0 h)⁻¹) :
      ↥Gp) : E) = t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹)
    {e : E} (he : e * t = t * e) :
    e * ((Φ (a * burnsideF429a_U4_z0 h * a⁻¹) : ↥Gp) : E) =
      ((Φ (a * burnsideF429a_U4_z0 h * a⁻¹) : ↥Gp) : E) * e := by
  set z₀ := burnsideF429a_U4_z0 h with hz₀
  have hγz : frobElt h z₀ = z₀ := burnsideF429a_U4_frobElt_z0 h
  obtain ⟨n, hn, y, hy, rfl⟩ := hsplit e
  obtain ⟨g₀, -, τ, hgτ⟩ := burnsideF429a_U4_nf h Φ hP₁ hP₂ hy
  obtain ⟨n', rfl⟩ : ∃ n', ((Φ n' : ↥Gp) : E) = n := ⟨Φ.symm ⟨n, hn⟩, by simp⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = n' * g₀ := ⟨_, rfl⟩
  have hact : ∀ w, ((Φ (g₁ * fieldAut h τ w * g₁⁻¹) : ↥Gp) : E) =
      ((Φ n' : ↥Gp) : E) * y * ((Φ w : ↥Gp) : E) * (((Φ n' : ↥Gp) : E) * y)⁻¹ := by
    intro w
    have e1 : g₁ * fieldAut h τ w * g₁⁻¹ = n' * (g₀ * fieldAut h τ w * g₀⁻¹) * n'⁻¹ := by
      rw [hg₁]; group
    rw [e1, ← burnsideF429a_coe_conj, hgτ]
    group
  obtain ⟨gt, hgt⟩ : ∃ gt, gt = a * z₀ * (frobElt h a)⁻¹ := ⟨_, rfl⟩
  have hact_t : ∀ w, ((Φ (gt * frobElt h w * gt⁻¹) : ↥Gp) : E) =
      t * ((Φ w : ↥Gp) : E) * t⁻¹ := by
    intro w
    have e1 := ht (a⁻¹ * w * a)
    have e2 : a * z₀ * frobElt h (a⁻¹ * w * a) * (a * z₀)⁻¹ = gt * frobElt h w * gt⁻¹ := by
      rw [burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul,
        burnsideF429a_U4_frobElt_inv, hgt]
      group
    have e3 : a * (a⁻¹ * w * a) * a⁻¹ = w := by group
    rw [e2, e3] at e1
    exact e1
  have hkey : g₁ * fieldAut h τ gt = gt * frobElt h g₁ := by
    have hu := burnsideF429a_eq_one_of_central hc Φ
      (u := (gt * frobElt h g₁)⁻¹ * (g₁ * fieldAut h τ gt)) (fun v => by
        obtain ⟨w, rfl⟩ : ∃ w, fieldAut h τ (frobElt h w) = v :=
          ⟨frobElt h ((fieldAut h τ).symm v), by rw [frobElt_frobElt, MulEquiv.apply_symm_apply]⟩
        have e1 : ((Φ (g₁ * fieldAut h τ (gt * frobElt h w * gt⁻¹) * g₁⁻¹) : ↥Gp) : E) =
            ((Φ (gt * frobElt h (g₁ * fieldAut h τ w * g₁⁻¹) * gt⁻¹) : ↥Gp) : E) := by
          rw [hact, hact_t, hact_t, hact]
          calc ((Φ n' : ↥Gp) : E) * y * (t * ((Φ w : ↥Gp) : E) * t⁻¹) *
                (((Φ n' : ↥Gp) : E) * y)⁻¹ =
              (((Φ n' : ↥Gp) : E) * y * t) * ((Φ w : ↥Gp) : E) *
                (((Φ n' : ↥Gp) : E) * y * t)⁻¹ := by group
            _ = (t * (((Φ n' : ↥Gp) : E) * y)) * ((Φ w : ↥Gp) : E) *
                (t * (((Φ n' : ↥Gp) : E) * y))⁻¹ := by rw [he]
            _ = t * (((Φ n' : ↥Gp) : E) * y * ((Φ w : ↥Gp) : E) *
                (((Φ n' : ↥Gp) : E) * y)⁻¹) * t⁻¹ := by group
        have e2 := Φ.injective (Subtype.ext e1)
        rw [map_mul, map_mul, map_inv, burnsideF429a_U4_fieldAut_frobElt,
          burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul,
          burnsideF429a_U4_frobElt_inv, ← burnsideF429a_U4_fieldAut_frobElt] at e2
        calc (gt * frobElt h g₁)⁻¹ * (g₁ * fieldAut h τ gt) * fieldAut h τ (frobElt h w) *
              ((gt * frobElt h g₁)⁻¹ * (g₁ * fieldAut h τ gt))⁻¹ =
            (gt * frobElt h g₁)⁻¹ * (g₁ * (fieldAut h τ gt * fieldAut h τ (frobElt h w) *
              (fieldAut h τ gt)⁻¹) * g₁⁻¹) * (gt * frobElt h g₁) := by group
          _ = (gt * frobElt h g₁)⁻¹ * (gt * (frobElt h g₁ * fieldAut h τ (frobElt h w) *
              (frobElt h g₁)⁻¹) * gt⁻¹) * (gt * frobElt h g₁) := by rw [e2]
          _ = fieldAut h τ (frobElt h w) := by group)
    calc g₁ * fieldAut h τ gt = (gt * frobElt h g₁) *
        ((gt * frobElt h g₁)⁻¹ * (g₁ * fieldAut h τ gt)) := by group
      _ = gt * frobElt h g₁ := by rw [hu, mul_one]
  obtain ⟨k, hk⟩ : ∃ k, k = a⁻¹ * g₁ * fieldAut h τ a := ⟨_, rfl⟩
  have hkz : k * z₀ = z₀ * frobElt h k := by
    have e1 : fieldAut h τ gt = fieldAut h τ a * z₀ * (frobElt h (fieldAut h τ a))⁻¹ := by
      rw [hgt, map_mul, map_mul, map_inv, burnsideF429a_U4_fieldAut_z0,
        burnsideF429a_U4_fieldAut_frobElt]
    have e2 : frobElt h k = (frobElt h a)⁻¹ * frobElt h g₁ * frobElt h (fieldAut h τ a) := by
      rw [hk, burnsideF429a_U4_frobElt_mul, burnsideF429a_U4_frobElt_mul,
        burnsideF429a_U4_frobElt_inv]
    rw [e2]
    calc k * z₀ = a⁻¹ * (g₁ * (fieldAut h τ a * z₀ * (frobElt h (fieldAut h τ a))⁻¹)) *
        frobElt h (fieldAut h τ a) := by rw [hk]; group
      _ = a⁻¹ * (g₁ * fieldAut h τ gt) * frobElt h (fieldAut h τ a) := by rw [e1]
      _ = a⁻¹ * (gt * frobElt h g₁) * frobElt h (fieldAut h τ a) := by rw [hkey]
      _ = z₀ * ((frobElt h a)⁻¹ * frobElt h g₁ * frobElt h (fieldAut h τ a)) := by
          rw [hgt]; group
  have hcomm := burnsideF429a_U4_comm_z0 h hkz
  have hez : ((Φ n' : ↥Gp) : E) * y * ((Φ (a * z₀ * a⁻¹) : ↥Gp) : E) *
      (((Φ n' : ↥Gp) : E) * y)⁻¹ = ((Φ (a * z₀ * a⁻¹) : ↥Gp) : E) := by
    rw [← hact]
    have hg₁a : g₁ * fieldAut h τ a = a * k := by rw [hk]; group
    have e1 : g₁ * fieldAut h τ (a * z₀ * a⁻¹) * g₁⁻¹ = a * z₀ * a⁻¹ := by
      rw [map_mul, map_mul, map_inv, burnsideF429a_U4_fieldAut_z0]
      calc g₁ * (fieldAut h τ a * z₀ * (fieldAut h τ a)⁻¹) * g₁⁻¹ =
          (g₁ * fieldAut h τ a) * z₀ * (g₁ * fieldAut h τ a)⁻¹ := by group
        _ = (a * k) * z₀ * (a * k)⁻¹ := by rw [hg₁a]
        _ = a * (k * z₀) * k⁻¹ * a⁻¹ := by group
        _ = a * (z₀ * k) * k⁻¹ * a⁻¹ := by rw [hcomm]
        _ = a * z₀ * a⁻¹ := by group
    rw [e1]
  calc ((Φ n' : ↥Gp) : E) * y * ((Φ (a * z₀ * a⁻¹) : ↥Gp) : E) =
      (((Φ n' : ↥Gp) : E) * y * ((Φ (a * z₀ * a⁻¹) : ↥Gp) : E) *
        (((Φ n' : ↥Gp) : E) * y)⁻¹) * (((Φ n' : ↥Gp) : E) * y) := by group
    _ = ((Φ (a * z₀ * a⁻¹) : ↥Gp) : E) * (((Φ n' : ↥Gp) : E) * y) := by rw [hez]

theorem burnsideF429a_U4_centralizer_typeIII [Finite E] [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ x ∈ M₁ ⊓ M₂, e = n * x) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom)
    {t : E} (a : hypSU h 2 0)
    (ht : ∀ x, ((Φ (a * burnsideF429a_U4_z0 h * frobElt h x * (a * burnsideF429a_U4_z0 h)⁻¹) :
      ↥Gp) : E) = t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹)
    {z s : E} (hz : z = ((Φ (a * burnsideF429a_U4_z0 h * a⁻¹) : ↥Gp) : E)) (hts : t = s * z) :
    Subgroup.centralizer ({t} : Set E) =
      Subgroup.centralizer ({s} : Set E) ⊓ Subgroup.centralizer ({z} : Set E) := by
  ext e
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro he
    have hze : e * z = z * e := by
      rw [hz]
      exact burnsideF429a_U4_comm_of_comm h hc hsplit Φ hP₁ hP₂ a ht he
    refine ⟨?_, hze⟩
    have hs : s = t * z⁻¹ := by rw [hts]; group
    have hzi : e * z⁻¹ = z⁻¹ * e := by
      calc e * z⁻¹ = z⁻¹ * (z * e) * z⁻¹ := by group
        _ = z⁻¹ * (e * z) * z⁻¹ := by rw [hze]
        _ = z⁻¹ * e := by group
    rw [hs]
    calc e * (t * z⁻¹) = (e * t) * z⁻¹ := by group
      _ = (t * e) * z⁻¹ := by rw [he]
      _ = t * (e * z⁻¹) := by group
      _ = t * (z⁻¹ * e) := by rw [hzi]
      _ = t * z⁻¹ * e := by group
  · rintro ⟨hse, hze⟩
    rw [hts]
    calc e * (s * z) = (e * s) * z := by group
      _ = (s * e) * z := by rw [hse]
      _ = s * (e * z) := by group
      _ = s * (z * e) := by rw [hze]
      _ = s * z * e := by group

theorem burnsideF429a_U4_conj_z0 (a : hypSU h 2 0) :
    a * burnsideF429a_U4_z0 h * a⁻¹ ≠ 1 ∧
      a * burnsideF429a_U4_z0 h * a⁻¹ * (a * burnsideF429a_U4_z0 h * a⁻¹) = 1 ∧
      Matrix.rank ((((a * burnsideF429a_U4_z0 h * a⁻¹ : hypSU h 2 0) : GL Ix K) :
        Matrix Ix Ix K) - 1) = 1 := by
  refine ⟨fun h1 => burnsideF429a_U4_z0_ne_one h ?_, ?_, ?_⟩
  · calc burnsideF429a_U4_z0 h = a⁻¹ * (a * burnsideF429a_U4_z0 h * a⁻¹) * a := by group
      _ = 1 := by rw [h1]; group
  · calc a * burnsideF429a_U4_z0 h * a⁻¹ * (a * burnsideF429a_U4_z0 h * a⁻¹) =
        a * (burnsideF429a_U4_z0 h * burnsideF429a_U4_z0 h) * a⁻¹ := by group
      _ = 1 := by rw [burnsideF429a_U4_z0_mul_self]; group
  · have hA : ((a : GL Ix K) : Matrix Ix Ix K) *
        (((a⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = 1 := by
      rw [← coe_mul_hypSU, mul_inv_cancel]
      rfl
    have hA' : (((a⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) *
        ((a : GL Ix K) : Matrix Ix Ix K) = 1 := by
      rw [← coe_mul_hypSU, inv_mul_cancel]
      rfl
    have e : (((a * burnsideF429a_U4_z0 h * a⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1 =
        ((a : GL Ix K) : Matrix Ix Ix K) *
          ((((burnsideF429a_U4_z0 h : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) - 1) *
          (((a⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hA, coe_mul_hypSU, coe_mul_hypSU]
    rw [e, burnsideF429a_rank_conj_rect hA', burnsideF429a_U4_rank_z0]

end U4Model

section Chart

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF429a_U4_rankInv_iff {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U4 2 f Gp M₁ M₂) {mk : Marking .U4 2 f ↥Gp}
    (hcp : hyp.chart.coordinatePayload = NativeCoordinates.classical .U4 rfl mk)
    (w : hypSU (burnsideF4gU4_fieldData mk) 2 0) :
    hyp.chart.coordinatePayload.RankInvolution 1 ((burnsideF4gU4_Phi mk w : ↥Gp) : E) ↔
      w ≠ 1 ∧ w * w = 1 ∧
        Matrix.rank (((w : GL (HypIndex 2 0) mk.field) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field) - 1) = 1 := by
  have hPhi : ∀ g, burnsideF4gU4_Phi mk g = mk.transport (burnsideF4gU4_T mk g) := fun g =>
    congrArg (fun φ : hypSU (burnsideF4gU4_fieldData mk) 2 0 →* ↥Gp => φ g)
      (burnsideF4gU4_Phi_toMonoidHom mk)
  have hrank : ∀ g : hypSU (burnsideF4gU4_fieldData mk) 2 0,
      Matrix.rank ((((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ f) mk.field) :
        GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) - 1) =
      Matrix.rank (((g : GL (HypIndex 2 0) mk.field) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field) - 1) := by
    intro g
    have hR := burnsideF4gU4_marking_isHypTransport mk
    have h1 := transportInv_mul hR
    have h2 := mul_transportInv hR
    rw [burnsideF4gU4_coe_T]
    have e : burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
        ((g : GL (HypIndex 2 0) mk.field) : Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field) *
        transportInv (burnsideF4gU4_fieldData mk)
          (burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)) - 1 =
        burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
        (((g : GL (HypIndex 2 0) mk.field) : Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field) - 1) *
        transportInv (burnsideF4gU4_fieldData mk)
          (burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2]
    rw [e]
    exact burnsideF429a_rank_conj_rect h1 _
  constructor
  · intro hri
    rw [hcp] at hri
    obtain ⟨-, hne, -, rep, hrep, hrep2, hrk⟩ := hri
    obtain ⟨w', rfl⟩ := (burnsideF4gU4_T mk).surjective rep
    have hw' : w' = w := by
      apply (burnsideF4gU4_Phi mk).injective
      apply Subtype.ext
      rw [hPhi w']
      exact hrep
    subst hw'
    refine ⟨fun h1 => hne (by rw [h1, map_one]; rfl), ?_, ?_⟩
    · apply (burnsideF4gU4_T mk).injective
      rw [map_mul, hrep2, map_one]
    · rw [← hrank]
      exact hrk
  · rintro ⟨hne, hsq, hrk⟩
    rw [hcp]
    refine ⟨(burnsideF4gU4_Phi mk w).2, ?_, ?_, burnsideF4gU4_T mk w, ?_, ?_, ?_⟩
    · intro h1
      apply hne
      apply (burnsideF4gU4_Phi mk).injective
      rw [map_one]
      exact Subtype.ext h1
    · rw [← Subgroup.coe_mul, ← map_mul, hsq, map_one]
      rfl
    · rw [← hPhi]
    · rw [← map_mul, hsq, map_one]
    · rw [hrank]
      exact hrk

theorem burnsideF429a_U4_rankInv_z0 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U4 2 f Gp M₁ M₂) {mk : Marking .U4 2 f ↥Gp}
    (hcp : hyp.chart.coordinatePayload = NativeCoordinates.classical .U4 rfl mk)
    (a : hypSU (burnsideF4gU4_fieldData mk) 2 0) :
    hyp.chart.coordinatePayload.RankInvolution 1
      ((burnsideF4gU4_Phi mk (a * burnsideF429a_U4_z0 (burnsideF4gU4_fieldData mk) * a⁻¹) :
        ↥Gp) : E) := by
  rw [burnsideF429a_U4_rankInv_iff hyp hcp]
  exact burnsideF429a_U4_conj_z0 (burnsideF4gU4_fieldData mk) a

end Chart

end CFSG.ASVolI
