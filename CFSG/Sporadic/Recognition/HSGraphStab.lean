module

public import CFSG.Sporadic.Recognition.HSGraphDefs
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneAxioms
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open CFSG.ComponentClassification.WittDesign MulAction

universe u

variable {Ω : Type u} {𝓑 : Finset (Finset Ω)}

theorem vPt_injective : Function.Injective (vPt : Ω → Vert 𝓑) := fun _ _ h =>
  Sum.inl.inj (Option.some.inj h)

theorem vBlk_injective : Function.Injective (vBlk : {B // B ∈ 𝓑} → Vert 𝓑) := fun _ _ h =>
  Sum.inr.inj (Option.some.inj h)

theorem exists_vPt {σ : Equiv.Perm (Vert 𝓑)} (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf) (a : Ω) :
    ∃ b, σ (vPt a) = vPt b := by
  have h1 := (hσ vInf (vPt a)).2 (adj_vInf_vPt a)
  rw [h] at h1
  rcases hx : σ (vPt a) with _ | b | B
  · rw [hx] at h1
    exact absurd h1 not_adj_vInf_vInf
  · exact ⟨b, rfl⟩
  · rw [hx] at h1
    exact absurd h1 (not_adj_vInf_vBlk B)

theorem exists_vBlk {σ : Equiv.Perm (Vert 𝓑)} (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf)
    (B : {B // B ∈ 𝓑}) : ∃ C : {B // B ∈ 𝓑}, σ (vBlk B) = vBlk C := by
  rcases hx : σ (vBlk B) with _ | b | C
  · exact absurd (σ.injective (hx.trans h.symm)) (by simp)
  · have h1 := (hσ vInf (vBlk B)).1 (by rw [h, hx]; exact adj_vInf_vPt b)
    exact absurd h1 (not_adj_vInf_vBlk B)
  · exact ⟨C, rfl⟩

@[expose] def resFun (σ : Equiv.Perm (Vert 𝓑)) (a : Ω) : Ω :=
  match σ (vPt a) with
  | some (Sum.inl b) => b
  | _ => a

theorem apply_vPt {σ : Equiv.Perm (Vert 𝓑)} (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf) (a : Ω) :
    σ (vPt a) = vPt (resFun σ a) := by
  obtain ⟨b, hb⟩ := exists_vPt hσ h a
  simp only [resFun, hb]

theorem inv_apply_vInf {σ : Equiv.Perm (Vert 𝓑)} (h : σ vInf = vInf) : σ⁻¹ vInf = vInf := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, h]

@[expose] def resPerm (σ : Equiv.Perm (Vert 𝓑)) (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf) :
    Equiv.Perm Ω where
  toFun := resFun σ
  invFun := resFun σ⁻¹
  left_inv a := by
    have e2 := apply_vPt (inv_mem hσ) (inv_apply_vInf h) (resFun σ a)
    rw [← apply_vPt hσ h a] at e2
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at e2
    exact (vPt_injective e2).symm
  right_inv a := by
    have e2 := apply_vPt hσ h (resFun σ⁻¹ a)
    rw [← apply_vPt (inv_mem hσ) (inv_apply_vInf h) a] at e2
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at e2
    exact (vPt_injective e2).symm

theorem resPerm_apply {σ : Equiv.Perm (Vert 𝓑)} (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf)
    (a : Ω) : resPerm σ hσ h a = resFun σ a := rfl

theorem apply_vPt' {σ : Equiv.Perm (Vert 𝓑)} (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf) (a : Ω) :
    σ (vPt a) = vPt (resPerm σ hσ h a) :=
  apply_vPt hσ h a

theorem apply_vBlk {σ : Equiv.Perm (Vert 𝓑)} (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf)
    (B : {B // B ∈ 𝓑}) : ∃ C : {B // B ∈ 𝓑}, σ (vBlk B) = vBlk C ∧
      C.1 = B.1.map (resPerm σ hσ h).toEmbedding := by
  obtain ⟨C, hC⟩ := exists_vBlk hσ h B
  refine ⟨C, hC, ?_⟩
  ext x
  rw [Finset.mem_map_equiv]
  have h1 := hσ (vPt ((resPerm σ hσ h).symm x)) (vBlk B)
  rw [apply_vPt' hσ h, hC, Equiv.apply_symm_apply] at h1
  simpa using h1

theorem resPerm_eq {σ : Equiv.Perm (Vert 𝓑)} (hσ : σ ∈ autGroup 𝓑) (h : σ vInf = vInf) {a b : Ω}
    (hab : σ (vPt a) = vPt b) : resPerm σ hσ h a = b :=
  vPt_injective ((apply_vPt' hσ h a).symm.trans hab)

variable (𝓑)

@[expose] def restrictΩ : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑) →* Equiv.Perm Ω where
  toFun g := resPerm g.1.1 g.1.2 g.2
  map_one' := Equiv.ext fun a => resPerm_eq _ _ rfl
  map_mul' g h := Equiv.ext fun a => resPerm_eq _ _ (by
    change g.1.1 (h.1.1 (vPt a)) = _
    rw [apply_vPt' h.1.2 h.2, apply_vPt' g.1.2 g.2]
    rfl)

variable {𝓑}

theorem restrictΩ_smul (g : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)) (a : Ω) :
    g • (vPt a : Vert 𝓑) = vPt (restrictΩ 𝓑 g a) :=
  apply_vPt' g.1.2 g.2 a

theorem restrictΩ_injective : Function.Injective (restrictΩ 𝓑) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Subtype.ext (Equiv.ext fun u => ?_))
  show g.1.1 u = u
  rcases u with _ | a | B
  · exact g.2
  · have := restrictΩ_smul g a
    rw [hg] at this
    exact this
  · obtain ⟨C, hC, hCB⟩ := apply_vBlk g.1.2 g.2 B
    have h1 : resPerm g.1.1 g.1.2 g.2 = 1 := hg
    rw [h1, show (1 : Equiv.Perm Ω).toEmbedding = Function.Embedding.refl Ω from rfl,
      Finset.map_refl] at hCB
    rw [hC, Subtype.ext hCB]

theorem map_map_inv (τ : Equiv.Perm Ω) (C : Finset Ω) :
    (C.map τ.toEmbedding).map τ⁻¹.toEmbedding = C := by
  rw [← map_perm_mul', inv_mul_cancel,
    show (1 : Equiv.Perm Ω).toEmbedding = Function.Embedding.refl Ω from rfl, Finset.map_refl]

theorem restrictΩ_mem_blockAut (g : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)) :
    restrictΩ 𝓑 g ∈ blockAut 𝓑 := by
  have key : ∀ g : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑), ∀ C ∈ 𝓑,
      C.map (restrictΩ 𝓑 g).toEmbedding ∈ 𝓑 := by
    intro g C hC
    obtain ⟨D, -, hD⟩ := apply_vBlk g.1.2 g.2 ⟨C, hC⟩
    have : D.1 ∈ 𝓑 := D.2
    rw [hD] at this
    exact this
  rw [mem_blockAut]
  intro C
  refine ⟨fun hC => ?_, key g C⟩
  have h1 := key g⁻¹ _ hC
  rwa [map_inv, map_map_inv] at h1

@[expose] def extFun (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) : Vert 𝓑 → Vert 𝓑
  | vInf => vInf
  | vPt a => vPt (τ a)
  | vBlk B => vBlk ⟨B.1.map τ.toEmbedding, (mem_blockAut.1 hτ B.1).2 B.2⟩

@[expose] def extPerm (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) : Equiv.Perm (Vert 𝓑) where
  toFun := extFun τ hτ
  invFun := extFun τ⁻¹ (inv_mem hτ)
  left_inv u := by
    rcases u with _ | a | B
    · rfl
    · simp [extFun]
    · simp only [extFun, map_map_inv]
  right_inv u := by
    rcases u with _ | a | B
    · rfl
    · simp [extFun]
    · simp only [extFun]
      have := map_map_inv τ⁻¹ B.1
      rw [inv_inv] at this
      simp only [this]

theorem extPerm_vInf (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) : extPerm τ hτ vInf = vInf := rfl

theorem extPerm_vPt (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) (a : Ω) :
    extPerm τ hτ (vPt a) = vPt (τ a) := rfl

theorem extPerm_vBlk (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) (B : {B // B ∈ 𝓑}) :
    extPerm τ hτ (vBlk B) = vBlk ⟨B.1.map τ.toEmbedding, (mem_blockAut.1 hτ B.1).2 B.2⟩ := rfl

theorem extPerm_mem (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) : extPerm τ hτ ∈ autGroup 𝓑 := by
  intro u v
  rcases u with _ | a | B <;> rcases v with _ | b | C <;>
    simp only [extPerm_vInf, extPerm_vPt, extPerm_vBlk, adj_vInf_vPt, adj_vPt_vInf,
      adj_vPt_vBlk, adj_vBlk_vPt, adj_vBlk_vBlk, not_adj_vInf_vInf, not_adj_vInf_vBlk,
      not_adj_vBlk_vInf, not_adj_vPt_vPt, Finset.mem_map_equiv, Equiv.symm_apply_apply, Ne,
      Subtype.ext_iff, Finset.map_inj, Finset.disjoint_map]

@[expose] def extElem (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) :
    stabilizer (autGroup 𝓑) (vInf : Vert 𝓑) :=
  ⟨⟨extPerm τ hτ, extPerm_mem τ hτ⟩, extPerm_vInf τ hτ⟩

theorem extElem_smul_vPt (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) (a : Ω) :
    extElem τ hτ • (vPt a : Vert 𝓑) = vPt (τ a) := rfl

theorem extElem_smul_vBlk (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) (B : {B // B ∈ 𝓑}) :
    extElem τ hτ • (vBlk B : Vert 𝓑) =
      vBlk ⟨B.1.map τ.toEmbedding, (mem_blockAut.1 hτ B.1).2 B.2⟩ := rfl

theorem restrictΩ_extElem (τ : Equiv.Perm Ω) (hτ : τ ∈ blockAut 𝓑) :
    restrictΩ 𝓑 (extElem τ hτ) = τ :=
  Equiv.ext fun a => resPerm_eq (extElem τ hτ).1.2 (extElem τ hτ).2 (extPerm_vPt τ hτ a)

theorem range_restrictΩ : (restrictΩ 𝓑).range = blockAut 𝓑 := by
  ext τ
  constructor
  · rintro ⟨g, rfl⟩
    exact restrictΩ_mem_blockAut g
  · intro hτ
    exact ⟨extElem τ hτ, restrictΩ_extElem τ hτ⟩

@[expose] noncomputable def stabEquiv : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑) ≃* blockAut 𝓑 :=
  (MonoidHom.ofInjective (restrictΩ_injective (𝓑 := 𝓑))).trans
    (MulEquiv.subgroupCongr range_restrictΩ)

@[simp] theorem coe_stabEquiv (g : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)) :
    ((stabEquiv g : blockAut 𝓑) : Equiv.Perm Ω) = restrictΩ 𝓑 g := rfl

theorem card_stabilizer_vInf :
    Nat.card (stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)) = Nat.card (blockAut 𝓑) :=
  Nat.card_congr stabEquiv.toEquiv

section Orbits

variable (G : Type*) [Group G] [MulAction G (Vert 𝓑)]

theorem orbit_vInf_eq (h1 : ∀ g : G, g • (vInf : Vert 𝓑) = vInf) :
    MulAction.orbit G (vInf : Vert 𝓑) = {vInf} := by
  ext v
  simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact h1 g
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem orbit_vPt_eq (h1 : ∀ g : G, g • (vInf : Vert 𝓑) = vInf)
    (h2 : ∀ (g : G) (u v : Vert 𝓑), (hsGraph 𝓑).Adj (g • u) (g • v) ↔ (hsGraph 𝓑).Adj u v)
    (h3 : ∀ a b : Ω, ∃ g : G, g • (vPt a : Vert 𝓑) = vPt b) (a : Ω) :
    MulAction.orbit G (vPt a : Vert 𝓑) = Set.range vPt := by
  have hmem : ∀ g : G, MulAction.toPermHom G (Vert 𝓑) g ∈ autGroup 𝓑 := fun g u v => h2 g u v
  ext v
  simp only [MulAction.mem_orbit_iff, Set.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨b, hb⟩ := exists_vPt (hmem g) (h1 g) a
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, rfl⟩
    exact h3 a b

theorem orbit_vBlk_eq (h1 : ∀ g : G, g • (vInf : Vert 𝓑) = vInf)
    (h2 : ∀ (g : G) (u v : Vert 𝓑), (hsGraph 𝓑).Adj (g • u) (g • v) ↔ (hsGraph 𝓑).Adj u v)
    (h4 : ∀ B C : {B // B ∈ 𝓑}, ∃ g : G, g • (vBlk B : Vert 𝓑) = vBlk C)
    (B : {B // B ∈ 𝓑}) : MulAction.orbit G (vBlk B : Vert 𝓑) = Set.range vBlk := by
  have hmem : ∀ g : G, MulAction.toPermHom G (Vert 𝓑) g ∈ autGroup 𝓑 := fun g u v => h2 g u v
  ext v
  simp only [MulAction.mem_orbit_iff, Set.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨C, hC⟩ := exists_vBlk (hmem g) (h1 g) B
    exact ⟨C, hC.symm⟩
  · rintro ⟨C, rfl⟩
    exact h4 B C

theorem range_orbit_eq [Nonempty Ω] (hne : 𝓑.Nonempty) (h1 : ∀ g : G, g • (vInf : Vert 𝓑) = vInf)
    (h2 : ∀ (g : G) (u v : Vert 𝓑), (hsGraph 𝓑).Adj (g • u) (g • v) ↔ (hsGraph 𝓑).Adj u v)
    (h3 : ∀ a b : Ω, ∃ g : G, g • (vPt a : Vert 𝓑) = vPt b)
    (h4 : ∀ B C : {B // B ∈ 𝓑}, ∃ g : G, g • (vBlk B : Vert 𝓑) = vBlk C) :
    Set.range (MulAction.orbit G : Vert 𝓑 → Set (Vert 𝓑)) =
      {{vInf}, Set.range vPt, Set.range vBlk} := by
  have o1 := orbit_vInf_eq G h1
  have o2 := orbit_vPt_eq G h1 h2 h3
  have o3 := orbit_vBlk_eq G h1 h2 h4
  ext S
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    rcases u with _ | a | B
    · exact Or.inl o1
    · exact Or.inr (Or.inl (o2 a))
    · exact Or.inr (Or.inr (o3 B))
  · rintro (rfl | rfl | rfl)
    · exact ⟨vInf, o1⟩
    · obtain ⟨a⟩ := ‹Nonempty Ω›
      exact ⟨vPt a, o2 a⟩
    · obtain ⟨B, hB⟩ := hne
      exact ⟨vBlk ⟨B, hB⟩, o3 ⟨B, hB⟩⟩

end Orbits

end CFSG.Sporadic.Recognition.HSGraph
