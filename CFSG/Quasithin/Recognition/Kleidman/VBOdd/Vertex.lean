module

public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Ctx
public import CFSG.Quasithin.Recognition.SzVBOddL24Loc

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

namespace Ctx

variable (C : Ctx G₀ G₁ G₂ T V z)

include C

omit [Finite G] in
theorem data_smul_γ₁ (g : ↥G₀) :
    stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂ ∧
      pCoreOf 2 (stab (g • γ₁ G₀ G₁ G₂)) = conjSub (g : G) (pCoreOf 2 G₂) ∧
      Vv V (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) (conjClosure V G₂) := by
  have hst : stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂ := by
    rw [stab_smul, stab_γ₁ C.hyp.le₂]
  refine ⟨hst, by rw [hst, pCoreOf_conjSub], ?_⟩
  rw [Vv_smul C.hyp.normalizes, Vv_γ₁ C.hyp.le₂ C.hyp.normalizes]

omit [Finite G] in
theorem comm_big_at {u : CosetGeom G₀ G₁ G₂} (hu : vtype u = true) {w : G}
    (hw : w ∈ stab u) (hw2 : w * w = 1) (hwQ : w ∉ pCoreOf 2 (stab u)) (c : G) :
    ∃ a ∈ Vv V u, w * a * w⁻¹ * a⁻¹ ≠ 1 ∧ w * a * w⁻¹ * a⁻¹ ≠ c := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hu
  obtain ⟨hst, hQ, hW⟩ := C.data_smul_γ₁ g
  rw [hst, mem_conjSub] at hw
  rw [hQ, mem_conjSub] at hwQ
  rw [hW]
  have hw2' : (g : G)⁻¹ * w * g * ((g : G)⁻¹ * w * g) = 1 := by
    calc (g : G)⁻¹ * w * g * ((g : G)⁻¹ * w * g) = (g : G)⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hw2]; group
  obtain ⟨a, ha, h1, h2⟩ := C.comm_big _ hw hw2' hwQ ((g : G)⁻¹ * c * g)
  refine ⟨(g : G) * a * (g : G)⁻¹, mul_mem_conjSub ha, ?_, ?_⟩
  · intro h
    apply h1
    calc (g : G)⁻¹ * w * g * a * ((g : G)⁻¹ * w * g)⁻¹ * a⁻¹
        = (g : G)⁻¹ * (w * ((g : G) * a * (g : G)⁻¹) * w⁻¹ * ((g : G) * a * (g : G)⁻¹)⁻¹) *
          g := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply h2
    calc (g : G)⁻¹ * w * g * a * ((g : G)⁻¹ * w * g)⁻¹ * a⁻¹
        = (g : G)⁻¹ * (w * ((g : G) * a * (g : G)⁻¹) * w⁻¹ * ((g : G) * a * (g : G)⁻¹)⁻¹) *
          g := by group
      _ = (g : G)⁻¹ * c * g := by rw [h]

omit [Finite G] in
theorem quad_pair_at {u : CosetGeom G₀ G₁ G₂} (hu : vtype u = true) {e e' : G}
    (he : e ∈ stab u) (he' : e' ∈ stab u) (he2 : e * e = 1) (he'2 : e' * e' = 1)
    (hc : e * e' = e' * e)
    (hq : ∀ a ∈ Vv V u, e' * (e * a * e⁻¹ * a⁻¹) * e'⁻¹ = e * a * e⁻¹ * a⁻¹) :
    e ∈ pCoreOf 2 (stab u) ∨ e' ∈ pCoreOf 2 (stab u) ∨ e * e' ∈ pCoreOf 2 (stab u) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hu
  obtain ⟨hst, hQ, hW⟩ := C.data_smul_γ₁ g
  rw [hst, mem_conjSub] at he he'
  rw [hW] at hq
  rw [hQ, mem_conjSub, mem_conjSub, mem_conjSub]
  set g' : G := (g : G)
  have key : ∀ x y : G, x * y = 1 → g'⁻¹ * x * g' * (g'⁻¹ * y * g') = 1 := fun x y h => by
    calc g'⁻¹ * x * g' * (g'⁻¹ * y * g') = g'⁻¹ * (x * y) * g' := by group
      _ = 1 := by rw [h]; group
  have hc' : g'⁻¹ * e * g' * (g'⁻¹ * e' * g') = g'⁻¹ * e' * g' * (g'⁻¹ * e * g') := by
    calc g'⁻¹ * e * g' * (g'⁻¹ * e' * g') = g'⁻¹ * (e * e') * g' := by group
      _ = g'⁻¹ * (e' * e) * g' := by rw [hc]
      _ = g'⁻¹ * e' * g' * (g'⁻¹ * e * g') := by group
  have hq' : ∀ a ∈ conjClosure V G₂, g'⁻¹ * e' * g' * (g'⁻¹ * e * g' * a * (g'⁻¹ * e * g')⁻¹ *
      a⁻¹) * (g'⁻¹ * e' * g')⁻¹ = g'⁻¹ * e * g' * a * (g'⁻¹ * e * g')⁻¹ * a⁻¹ := by
    intro a ha
    have h := hq (g' * a * g'⁻¹) (mul_mem_conjSub ha)
    calc g'⁻¹ * e' * g' * (g'⁻¹ * e * g' * a * (g'⁻¹ * e * g')⁻¹ * a⁻¹) * (g'⁻¹ * e' * g')⁻¹
        = g'⁻¹ * (e' * (e * (g' * a * g'⁻¹) * e⁻¹ * (g' * a * g'⁻¹)⁻¹) * e'⁻¹) * g' := by
          group
      _ = g'⁻¹ * (e * (g' * a * g'⁻¹) * e⁻¹ * (g' * a * g'⁻¹)⁻¹) * g' := by rw [h]
      _ = g'⁻¹ * e * g' * a * (g'⁻¹ * e * g')⁻¹ * a⁻¹ := by group
  rcases C.quad_pair _ he _ he' (key e e he2) (key e' e' he'2) hc' hq' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ?_)
    have e1 : g'⁻¹ * (e * e') * g' = g'⁻¹ * e * g' * (g'⁻¹ * e' * g') := by group
    rw [e1]
    exact h

omit [Finite G] in
theorem exists_nbr_smul_γ₁ (g : ↥G₀) {x : CosetGeom G₀ G₁ G₂}
    (hx : x ∈ nbrs (g • γ₁ G₀ G₁ G₂)) :
    ∃ k : ↥G₀, (k : G) ∈ G₂ ∧ x = (g * k) • γ₀ G₀ G₁ G₂ := by
  have h1 : g⁻¹ • x ∈ nbrs (γ₁ G₀ G₁ G₂) := by
    have := (smul_adj (G₁ := G₁) (G₂ := G₂) g⁻¹ (u := g • γ₁ G₀ G₁ G₂) (v := x)).mpr hx
    rwa [inv_smul_smul] at this
  have h0 : γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := (adj_γ₀_γ₁ (G₀ := G₀)).symm
  obtain ⟨k, hk, hkx⟩ := stab_transitive_on_nbrs h0 h1
  refine ⟨k, ?_, ?_⟩
  · rw [← stab_γ₁ C.hyp.le₂ (G₁ := G₁)]
    exact hk
  · rw [mul_smul, hkx, smul_inv_smul]

omit [Finite G] in
theorem exists_nbr_smul_γ₀ (g : ↥G₀) {y : CosetGeom G₀ G₁ G₂}
    (hy : y ∈ nbrs (g • γ₀ G₀ G₁ G₂)) :
    ∃ l : ↥G₀, (l : G) ∈ G₁ ∧ y = (g * l) • γ₁ G₀ G₁ G₂ := by
  have h1 : g⁻¹ • y ∈ nbrs (γ₀ G₀ G₁ G₂) := by
    have := (smul_adj (G₁ := G₁) (G₂ := G₂) g⁻¹ (u := g • γ₀ G₀ G₁ G₂) (v := y)).mpr hy
    rwa [inv_smul_smul] at this
  have h0 : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁ (G₀ := G₀)
  obtain ⟨l, hl, hly⟩ := stab_transitive_on_nbrs h0 h1
  refine ⟨l, ?_, ?_⟩
  · rw [← stab_γ₀ C.hyp.le₁ (G₂ := G₂)]
    exact hl
  · rw [mul_smul, hly, smul_inv_smul]

omit [Finite G] in
theorem two_fixed_at {u x x' : CosetGeom G₀ G₁ G₂} (hu : vtype u = true) (hx : x ∈ nbrs u)
    (hx' : x' ∈ nbrs u) (hne : Vv V x ≠ Vv V x') {e : G} (he : e ∈ stab u) (he2 : e * e = 1)
    (hex : e ∈ Subgroup.normalizer (Vv V x : Set G))
    (hex' : e ∈ Subgroup.normalizer (Vv V x' : Set G)) : e ∈ pCoreOf 2 (stab u) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hu
  obtain ⟨hst, hQ, -⟩ := C.data_smul_γ₁ g
  obtain ⟨k, hk, rfl⟩ := C.exists_nbr_smul_γ₁ g hx
  obtain ⟨k', hk', rfl⟩ := C.exists_nbr_smul_γ₁ g hx'
  have hVx : Vv V ((g * k) • γ₀ G₀ G₁ G₂) = conjSub ((g : G) * k) V := by
    rw [Vv_smul_γ₀ C.hyp.normalizes]; rfl
  have hVx' : Vv V ((g * k') • γ₀ G₀ G₁ G₂) = conjSub ((g : G) * k') V := by
    rw [Vv_smul_γ₀ C.hyp.normalizes]; rfl
  rw [hVx, hVx'] at hne
  rw [hVx] at hex
  rw [hVx'] at hex'
  rw [hst, mem_conjSub] at he
  rw [hQ, mem_conjSub]
  set g' : G := (g : G)
  set k₁ : G := (k : G)
  set k₂ : G := (k' : G)
  rw [conjSub_normalizer, mem_conjSub] at hex hex'
  have he₀ : k₁⁻¹ * (g'⁻¹ * e * g') * k₁ ∈ G₂ :=
    G₂.mul_mem (G₂.mul_mem (G₂.inv_mem hk) he) hk
  have he₀2 : k₁⁻¹ * (g'⁻¹ * e * g') * k₁ * (k₁⁻¹ * (g'⁻¹ * e * g') * k₁) = 1 := by
    calc k₁⁻¹ * (g'⁻¹ * e * g') * k₁ * (k₁⁻¹ * (g'⁻¹ * e * g') * k₁)
        = (g' * k₁)⁻¹ * (e * e) * (g' * k₁) := by group
      _ = 1 := by rw [he2]; group
  have he₀V : k₁⁻¹ * (g'⁻¹ * e * g') * k₁ ∈ Subgroup.normalizer (V : Set G) := by
    have e1 : k₁⁻¹ * (g'⁻¹ * e * g') * k₁ = (g' * k₁)⁻¹ * e * (g' * k₁) := by group
    rw [e1]
    exact hex
  have hk₀ : k₁⁻¹ * k₂ ∈ G₂ := G₂.mul_mem (G₂.inv_mem hk) hk'
  have hne₀ : conjSub (k₁⁻¹ * k₂) V ≠ V := by
    intro h
    apply hne
    rw [show g' * k₂ = g' * k₁ * (k₁⁻¹ * k₂) by group, conjSub_mul (g' * k₁), h]
  have he₀V' : k₁⁻¹ * (g'⁻¹ * e * g') * k₁ ∈
      Subgroup.normalizer (conjSub (k₁⁻¹ * k₂) V : Set G) := by
    rw [conjSub_normalizer, mem_conjSub]
    have e1 : (k₁⁻¹ * k₂)⁻¹ * (k₁⁻¹ * (g'⁻¹ * e * g') * k₁) * (k₁⁻¹ * k₂) =
        (g' * k₂)⁻¹ * e * (g' * k₂) := by group
    rw [e1]
    exact hex'
  have hQ₀ := C.two_fixed _ he₀ he₀2 he₀V _ hk₀ hne₀ he₀V'
  have hkN : k₁ ∈ Subgroup.normalizer (pCoreOf 2 G₂ : Set G) := le_normalizer_pCoreOf 2 G₂ hk
  have := (Subgroup.mem_normalizer_iff''.mp hkN (g'⁻¹ * e * g')).mpr hQ₀
  exact this

omit [Finite G] in
theorem twin_at {u x x' : CosetGeom G₀ G₁ G₂} (hu : vtype u = true) (hx : x ∈ nbrs u)
    (hx' : x' ∈ nbrs u) (heq : Vv V x = Vv V x') {y : CosetGeom G₀ G₁ G₂} (hy : y ∈ nbrs x') :
    y ∈ nbrs x := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hu
  obtain ⟨k, hk, rfl⟩ := C.exists_nbr_smul_γ₁ g hx
  obtain ⟨k', hk', rfl⟩ := C.exists_nbr_smul_γ₁ g hx'
  obtain ⟨l, hl, rfl⟩ := C.exists_nbr_smul_γ₀ (g * k') hy
  have hVx : Vv V ((g * k) • γ₀ G₀ G₁ G₂) = conjSub ((g : G) * k) V := by
    rw [Vv_smul_γ₀ C.hyp.normalizes]; rfl
  have hVx' : Vv V ((g * k') • γ₀ G₀ G₁ G₂) = conjSub ((g : G) * k') V := by
    rw [Vv_smul_γ₀ C.hyp.normalizes]; rfl
  rw [hVx, hVx'] at heq
  have ht : (k : G)⁻¹ * k' ∈ G₂ := G₂.mul_mem (G₂.inv_mem hk) hk'
  have htV : (k : G)⁻¹ * k' ∈ Subgroup.normalizer (V : Set G) := by
    apply mem_normalizer_of_conjSub_eq
    have h1 := congrArg (conjSub ((g : G) * k)⁻¹) heq
    rw [conjSub_conjSub_inv, ← conjSub_mul] at h1
    rw [show (k : G)⁻¹ * k' = ((g : G) * k)⁻¹ * ((g : G) * k') by group]
    exact h1.symm
  obtain ⟨l', hl', hll'⟩ := C.twin _ ht htV _ hl
  have hl'0 : l' ∈ G₀ := C.hyp.le₁ hl'
  set L' : ↥G₀ := ⟨l', hl'0⟩
  have hfix : (L'⁻¹ * (k⁻¹ * k' * l)) • γ₁ G₀ G₁ G₂ = γ₁ G₀ G₁ G₂ := by
    apply smul_eq_of_mem_stab
    rw [stab_γ₁ C.hyp.le₂]
    simpa [L', mul_assoc] using hll'
  have hy' : (g * k' * l) • γ₁ G₀ G₁ G₂ = (g * k * L') • γ₁ G₀ G₁ G₂ := by
    have e1 : g * k' * l = g * k * L' * (L'⁻¹ * (k⁻¹ * k' * l)) := by group
    rw [e1, mul_smul, hfix]
  rw [hy']
  have hL' : L' • γ₀ G₀ G₁ G₂ = γ₀ G₀ G₁ G₂ := by
    apply smul_eq_of_mem_stab
    rw [stab_γ₀ C.hyp.le₁]
    exact hl'
  show (graph G₀ G₁ G₂).Adj ((g * k) • γ₀ G₀ G₁ G₂) ((g * k * L') • γ₁ G₀ G₁ G₂)
  rw [mul_smul (g * k) L', smul_adj]
  have := (smul_adj (G₁ := G₁) (G₂ := G₂) L' (u := γ₀ G₀ G₁ G₂) (v := γ₁ G₀ G₁ G₂)).mpr
    (adj_γ₀_γ₁ (G₀ := G₀))
  rwa [hL'] at this

theorem inf_centralizer_le_at {x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false) :
    stab x ⊓ Subgroup.centralizer (Vv V x : Set G) ≤ pCoreOf 2 (stab x) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  rw [Vv_smul_γ₀ C.hyp.normalizes, stab_smul, stab_γ₀ C.hyp.le₁, pCoreOf_conjSub,
    conjSub_centralizer, ← conjSub_inf]
  apply conjSub_mono
  rw [pCoreOf_eq_inf_centralizer C.hyp]
  exact le_inf (SzVB.inf_centralizer_le_T C.hyp C.natS3 C.index3) inf_le_right

end Ctx

end CFSG.Quasithin.Kleidman.VBOdd
