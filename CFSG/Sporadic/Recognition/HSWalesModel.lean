module

public import CFSG.Sporadic.Recognition.HSWalesRank3
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Actions

public section

namespace CFSG.Sporadic.Recognition.HSWales

open MulAction CFSG.ComponentClassification.WittDesign
open scoped Pointwise

universe u v

theorem m22_facts :
    (∀ a x y : Fin 22, x ≠ a → y ≠ a → ∃ g ∈ stabilizer M22 a, g • x = y) ∧
    ((∀ B ∈ hexads, ∀ B' ∈ hexads, B ≠ B' → (B ∩ B').card = 0 ∨ (B ∩ B').card = 2) ∧
      ∀ B ∈ hexads, (hexads.filter fun B' => Disjoint B B').card = 16 ∧
        (hexads.filter fun B' => (B ∩ B').card = 2).card = 60) ∧
    (∀ B ∈ hexads, ∀ C ∈ hexads, ∀ C' ∈ hexads,
      (∃ g : stabilizer M22 B, g.1 • C = C') ↔ (B ∩ C).card = (B ∩ C').card) ∧
    (∀ a : Fin 22, (hexads.filter (a ∈ ·)).card = 21 ∧ (hexads.filter (a ∉ ·)).card = 56 ∧
      ∀ C ∈ hexads, ∀ C' ∈ hexads,
        (∃ g : stabilizer M22 a, g.1 • C = C') ↔ (a ∈ C ↔ a ∈ C')) ∧
    ((∀ H : Subgroup M22, H.index = 22 → ∃ a : Fin 22, H = stabilizer M22 a) ∧
      ∀ H : Subgroup M22, H.index = 77 → ∃ B ∈ hexads, H = stabilizer M22 B) := by
  obtain ⟨⟨-, -, -, h1⟩, ⟨-, -, -, -, h2a, h2b⟩, h3, h4, ⟨-, -, h5a, h5b, -⟩, -⟩ :=
    m22_point_hexad_actions
  exact ⟨fun a => (h1 a).2.2, ⟨h2a, h2b⟩,
    fun B hB => (h3 B hB).2.2.2.2.2.2.2.2, h4, ⟨h5a, h5b⟩⟩

theorem exists_equivariant_equiv {H M X Y : Type*} [Group H] [Group M] [MulAction H X]
    [MulAction M Y] [IsPretransitive H X] [IsPretransitive M Y] (φ : H ≃* M) (x₀ : X) (y₀ : Y)
    (h : ∀ s : H, s • x₀ = x₀ ↔ φ s • y₀ = y₀) :
    ∃ ψ : X ≃ Y, ∀ (s : H) (x : X), ψ (s • x) = φ s • ψ x := by
  classical
  have key : ∀ s t : H, s • x₀ = t • x₀ ↔ φ s • y₀ = φ t • y₀ := by
    intro s t
    have h1 : s • x₀ = t • x₀ ↔ (s⁻¹ * t) • x₀ = x₀ := by
      rw [mul_smul, inv_smul_eq_iff, eq_comm]
    have h2 : φ s • y₀ = φ t • y₀ ↔ φ (s⁻¹ * t) • y₀ = y₀ := by
      rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]
    rw [h1, h2, h]
  let g : X → H := fun x => Classical.choose (exists_smul_eq H x₀ x)
  have hg : ∀ x, g x • x₀ = x := fun x => Classical.choose_spec (exists_smul_eq H x₀ x)
  let f : X → Y := fun x => φ (g x) • y₀
  have hf : ∀ (s : H) (x : X), s • x₀ = x → f x = φ s • y₀ := fun s x hs =>
    (key (g x) s).1 ((hg x).trans hs.symm)
  have hsmul : ∀ (s : H) (x : X), f (s • x) = φ s • f x := by
    intro s x
    have : (s * g x) • x₀ = s • x := by rw [mul_smul, hg]
    rw [hf (s * g x) (s • x) this, map_mul, mul_smul]
  have hinj : Function.Injective f := by
    intro x x' hxx'
    have := (key (g x) (g x')).2 hxx'
    rw [hg, hg] at this
    exact this
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨m, hm⟩ := exists_smul_eq M y₀ y
    refine ⟨φ.symm m • x₀, ?_⟩
    rw [hf (φ.symm m) _ rfl, MulEquiv.apply_symm_apply, hm]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hsmul⟩

instance instMulActionHexads :
    MulAction M22 {B // B ∈ hexads} where
  smul g B := ⟨g • B.1, smul_mem_hexads g B.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

theorem coe_smul_hexads (g : M22) (B : {B // B ∈ hexads}) :
    ((g • B : {B // B ∈ hexads}) : Finset (Fin 22)) = g • B.1 := rfl

instance instIsPretransitiveHexads :
    IsPretransitive M22 {B // B ∈ hexads} where
  exists_smul_eq B C := by
    obtain ⟨g₁, h₁⟩ := mem_hexads_iff.1 B.2
    obtain ⟨g₂, h₂⟩ := mem_hexads_iff.1 C.2
    refine ⟨g₂ * g₁⁻¹, Subtype.ext ?_⟩
    rw [coe_smul_hexads, ← h₁, ← h₂, smul_smul, mul_assoc, inv_mul_cancel, mul_one]

structure Model (G : Type u) {Ω : Type v} [Group G] [MulAction G Ω] (a b c : Ω)
    (φ : stabilizer G a ≃* M22) where
  ψ : orbit (stabilizer G a) b ≃ Fin 22
  θ : orbit (stabilizer G a) c ≃ {B // B ∈ hexads}
  ψ_smul : ∀ (s : stabilizer G a) (x : orbit (stabilizer G a) b), ψ (s • x) = φ s • ψ x
  θ_smul : ∀ (s : stabilizer G a) (y : orbit (stabilizer G a) c), θ (s • y) = φ s • θ y

namespace Rank3

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] {a b c : Ω}

theorem nonempty_model
    (D : Rank3 G a b c) (φ : stabilizer G a ≃* M22) :
    Nonempty (Model G a b c φ) := by
  have hstab : ∀ {x : Ω} (s : stabilizer G a),
      s • (⟨x, mem_orbit_self x⟩ : orbit (stabilizer G a) x) = ⟨x, mem_orbit_self x⟩ ↔
        s ∈ stabilizer (stabilizer G a) x := by
    intro x s
    rw [mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  obtain ⟨y₀, hy₀⟩ := m22_facts.2.2.2.2.1
    ((stabilizer (stabilizer G a) b).map φ.toMonoidHom) (by
      rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective, index_stabilizer,
        D.ncard_Δ])
  obtain ⟨ψ, hψ⟩ := exists_equivariant_equiv φ
    (⟨b, mem_orbit_self b⟩ : orbit (stabilizer G a) b) y₀ (fun s => by
      rw [hstab, ← mem_stabilizer_iff, ← hy₀, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply])
  obtain ⟨B₀, hB₀, hB⟩ := m22_facts.2.2.2.2.2
    ((stabilizer (stabilizer G a) c).map φ.toMonoidHom) (by
      rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective, index_stabilizer,
        D.ncard_Γ])
  have hy : ∀ g : M22, g • (⟨B₀, hB₀⟩ : {B // B ∈ hexads}) = ⟨B₀, hB₀⟩ ↔
      g ∈ stabilizer M22 B₀ := fun g => by
    rw [mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  obtain ⟨θ, hθ⟩ := exists_equivariant_equiv φ
    (⟨c, mem_orbit_self c⟩ : orbit (stabilizer G a) c) (⟨B₀, hB₀⟩ : {B // B ∈ hexads}) (fun s => by
      rw [hstab, hy, ← hB, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply])
  exact ⟨⟨ψ, θ, hψ, hθ⟩⟩

end Rank3

theorem ncard_subtype_val {Ω : Type v} {A : Set Ω} (P : Ω → Prop) :
    {x : A | P x}.ncard = ({w | P w} ∩ A).ncard := by
  rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := (· ∈ A)))]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x.2⟩
  · rintro ⟨hw, hwA⟩
    exact ⟨⟨w, hwA⟩, hw, rfl⟩

namespace Model

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] {a b c : Ω}

@[simp] theorem coe_smul_orbit {H : Subgroup G} {a' : Ω} (s : H) (x : orbit H a') :
    ((s • x : orbit H a') : Ω) = (s : G) • (x : Ω) := rfl

variable {φ : stabilizer G a ≃* M22} (𝓜 : Model G a b c φ)

theorem smul_eq_self_iff_ψ (s : stabilizer G a) (x : orbit (stabilizer G a) b) :
    s • x = x ↔ φ s • 𝓜.ψ x = 𝓜.ψ x := by
  rw [← 𝓜.ψ_smul, 𝓜.ψ.apply_eq_iff_eq]

theorem smul_eq_self_iff_θ (s : stabilizer G a) (y : orbit (stabilizer G a) c) :
    s • y = y ↔ φ s • 𝓜.θ y = 𝓜.θ y := by
  rw [← 𝓜.θ_smul, 𝓜.θ.apply_eq_iff_eq]

include 𝓜 in
theorem exists_smul_Δ
    (x y z : orbit (stabilizer G a) b) (hy : y ≠ x) (hz : z ≠ x) :
    ∃ t : stabilizer G a, t • x = x ∧ t • y = z := by
  obtain ⟨m, hm, hmy⟩ := m22_facts.1 (𝓜.ψ x) (𝓜.ψ y) (𝓜.ψ z)
    (fun h => hy (𝓜.ψ.injective h)) (fun h => hz (𝓜.ψ.injective h))
  have hm' : m • 𝓜.ψ x = 𝓜.ψ x := mem_stabilizer_iff.1 hm
  refine ⟨φ.symm m, ?_, ?_⟩
  · rw [𝓜.smul_eq_self_iff_ψ, MulEquiv.apply_symm_apply]
    exact hm'
  · apply 𝓜.ψ.injective
    rw [𝓜.ψ_smul, MulEquiv.apply_symm_apply, hmy]

@[expose] def hexNbrs (v : Ω) : Set (Finset (Fin 22)) :=
  {B | ∃ y' : orbit (stabilizer G a) c, (rGraph G a b).Adj v y' ∧ (𝓜.θ y').1 = B}

theorem mem_hexNbrs_iff {v : Ω} {y : orbit (stabilizer G a) c} :
    (𝓜.θ y).1 ∈ 𝓜.hexNbrs v ↔ (rGraph G a b).Adj v y := by
  constructor
  · rintro ⟨y', hy', h⟩
    have : y' = y := 𝓜.θ.injective (Subtype.ext h)
    rwa [this] at hy'
  · exact fun h => ⟨y, h, rfl⟩

theorem hexNbrs_subset (v : Ω) : 𝓜.hexNbrs v ⊆ ↑hexads := by
  rintro _ ⟨y', -, rfl⟩
  exact (𝓜.θ y').2

theorem finite_hexNbrs (v : Ω) : (𝓜.hexNbrs v).Finite :=
  (Finset.finite_toSet hexads).subset (𝓜.hexNbrs_subset v)

theorem ncard_hexNbrs (v : Ω) :
    (𝓜.hexNbrs v).ncard = ({w | (rGraph G a b).Adj v w} ∩ orbit (stabilizer G a) c).ncard := by
  have hinj : Function.Injective fun y' : orbit (stabilizer G a) c => (𝓜.θ y').1 :=
    fun y₁ y₂ h => 𝓜.θ.injective (Subtype.ext h)
  have h : 𝓜.hexNbrs v = (fun y' : orbit (stabilizer G a) c => (𝓜.θ y').1) ''
      {y' | (rGraph G a b).Adj v y'} := by
    ext B
    simp only [hexNbrs, Set.mem_ofPred_eq, Set.mem_image]
  rw [h, Set.ncard_image_of_injective _ hinj, ncard_subtype_val]

theorem exists_stab_ψ (x : orbit (stabilizer G a) b) (g : stabilizer M22 (𝓜.ψ x)) :
    ∃ s : stabilizer G a, φ s = g.1 ∧ (s : G) • (x : Ω) = x := by
  refine ⟨φ.symm g.1, φ.apply_symm_apply _, congrArg Subtype.val
    ((𝓜.smul_eq_self_iff_ψ _ x).2 ?_)⟩
  rw [φ.apply_symm_apply]
  exact mem_stabilizer_iff.1 g.2

theorem exists_stab_θ (y : orbit (stabilizer G a) c) (g : stabilizer M22 (𝓜.θ y).1) :
    ∃ s : stabilizer G a, φ s = g.1 ∧ (s : G) • (y : Ω) = y := by
  refine ⟨φ.symm g.1, φ.apply_symm_apply _, congrArg Subtype.val
    ((𝓜.smul_eq_self_iff_θ _ y).2 ?_)⟩
  rw [φ.apply_symm_apply]
  exact Subtype.ext (mem_stabilizer_iff.1 g.2)

variable [Finite Ω] [IsPretransitive G Ω] (D : Rank3 G a b c)

include 𝓜 D

theorem not_adj_Δ
    (x y : orbit (stabilizer G a) b) : ¬ (rGraph G a b).Adj x y := by
  intro hxy
  refine D.not_forall_adj fun x' hx' y' hy' hne => ?_
  obtain ⟨s, hs⟩ := exists_smul_eq (stabilizer G a) x (⟨x', hx'⟩ : orbit (stabilizer G a) b)
  have hadj : (rGraph G a b).Adj ((s • x : orbit (stabilizer G a) b) : Ω)
      ((s • y : orbit (stabilizer G a) b) : Ω) := (D.adj_smul (s : G)).2 hxy
  obtain ⟨t, ht1, ht2⟩ := 𝓜.exists_smul_Δ (s • x) (s • y) ⟨y', hy'⟩
    (fun h => hxy.ne (congrArg Subtype.val (MulAction.injective s h)).symm)
    (fun h => hne (by rw [hs] at h; exact (congrArg Subtype.val h).symm))
  have h3 := (D.adj_smul (t : G)).2 hadj
  rw [← coe_smul_orbit, ← coe_smul_orbit, ht1, ht2, hs] at h3
  exact h3

theorem hexNbrs_stable {v : Ω} {s : stabilizer G a} (hv : (s : G) • v = v) {B : Finset (Fin 22)}
    (hB : B ∈ 𝓜.hexNbrs v) : φ s • B ∈ 𝓜.hexNbrs v := by
  obtain ⟨y', hy', rfl⟩ := hB
  refine ⟨s • y', ?_, ?_⟩
  · have := (D.adj_smul (s : G)).2 hy'
    rwa [hv] at this
  · rw [𝓜.θ_smul, coe_smul_hexads]

theorem adj_Δ_Γ
    (x : orbit (stabilizer G a) b) (y : orbit (stabilizer G a) c) :
    (rGraph G a b).Adj x y ↔ 𝓜.ψ x ∈ (𝓜.θ y).1 := by
  classical
  have hcard : (𝓜.hexNbrs x).ncard = 21 := by
    rw [𝓜.ncard_hexNbrs]
    have hN := D.ncard_neighbors (x : Ω)
    have heq : {w | (rGraph G a b).Adj x w} =
        insert a ({w | (rGraph G a b).Adj x w} ∩ orbit (stabilizer G a) c) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_inter_iff]
      constructor
      · intro hw
        rcases D.cover w with hwa | hwΔ | hwΓ
        · exact Or.inl hwa
        · exact absurd hw (𝓜.not_adj_Δ D x ⟨w, hwΔ⟩)
        · exact Or.inr ⟨hw, hwΓ⟩
      · rintro (hwa | ⟨hw, -⟩)
        · rw [hwa]
          exact ((D.adj_a).2 x.2).symm
        · exact hw
    rw [heq, Set.ncard_insert_of_notMem (fun h => D.a_notMem_Γ h.2) (Set.toFinite _)] at hN
    omega
  obtain ⟨h21, h56, hiff⟩ := m22_facts.2.2.2.1 (𝓜.ψ x)
  have hsubZ : 𝓜.hexNbrs x ⊆ ↑(hexads.filter fun B => 𝓜.ψ x ∈ B) := by
    intro B hB
    have hBh := 𝓜.hexNbrs_subset x hB
    by_contra hnot
    have hxB : 𝓜.ψ x ∉ B := fun h => hnot (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hBh, h⟩))
    have hall : ↑(hexads.filter fun B => 𝓜.ψ x ∉ B) ⊆ 𝓜.hexNbrs x := by
      intro C hC
      have hC' := Finset.mem_filter.1 (Finset.mem_coe.1 hC)
      obtain ⟨g, hg⟩ := (hiff B (Finset.mem_coe.1 hBh) C hC'.1).2 (iff_of_false hxB hC'.2)
      obtain ⟨s, hs1, hs2⟩ := 𝓜.exists_stab_ψ x g
      rw [← hg, ← hs1]
      exact 𝓜.hexNbrs_stable D hs2 hB
    have := Set.ncard_le_ncard hall (𝓜.finite_hexNbrs x)
    rw [Set.ncard_coe_finset, h56, hcard] at this
    omega
  have hTZ : 𝓜.hexNbrs x = ↑(hexads.filter fun B => 𝓜.ψ x ∈ B) :=
    Set.eq_of_subset_of_ncard_le hsubZ (by rw [Set.ncard_coe_finset, h21, hcard])
      (Finset.finite_toSet _)
  constructor
  · intro h
    have : (𝓜.θ y).1 ∈ 𝓜.hexNbrs x := (𝓜.mem_hexNbrs_iff).2 h
    rw [hTZ] at this
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 this)).2
  · intro h
    refine (𝓜.mem_hexNbrs_iff).1 ?_
    rw [hTZ]
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(𝓜.θ y).2, h⟩)

theorem adj_Γ_Γ
    (y y' : orbit (stabilizer G a) c) :
    (rGraph G a b).Adj y y' ↔ 𝓜.θ y ≠ 𝓜.θ y' ∧ Disjoint (𝓜.θ y).1 (𝓜.θ y').1 := by
  classical
  have hcard : (𝓜.hexNbrs y).ncard = 16 := by
    rw [𝓜.ncard_hexNbrs]
    have hN := D.ncard_neighbors (y : Ω)
    have heq : {w | (rGraph G a b).Adj y w} =
        ({w | (rGraph G a b).Adj y w} ∩ orbit (stabilizer G a) b) ∪
          ({w | (rGraph G a b).Adj y w} ∩ orbit (stabilizer G a) c) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
      constructor
      · intro hw
        rcases D.cover w with hwa | hwΔ | hwΓ
        · exfalso
          rw [hwa] at hw
          exact D.notMem_Γ_of_mem_Δ ((D.adj_a).1 hw.symm) y.2
        · exact Or.inl ⟨hw, hwΔ⟩
        · exact Or.inr ⟨hw, hwΓ⟩
      · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
    have hdisj : Disjoint ({w | (rGraph G a b).Adj y w} ∩ orbit (stabilizer G a) b)
        ({w | (rGraph G a b).Adj y w} ∩ orbit (stabilizer G a) c) := by
      rw [Set.disjoint_left]
      rintro w ⟨-, hwΔ⟩ ⟨-, hwΓ⟩
      exact D.notMem_Γ_of_mem_Δ hwΔ hwΓ
    rw [heq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at hN
    have h6 : ({w | (rGraph G a b).Adj y w} ∩ orbit (stabilizer G a) b).ncard = 6 := by
      rw [← ncard_subtype_val (A := orbit (stabilizer G a) b) fun w => (rGraph G a b).Adj y w]
      have : {x : orbit (stabilizer G a) b | (rGraph G a b).Adj y x} =
          𝓜.ψ ⁻¹' ↑(𝓜.θ y).1 := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe]
        rw [← 𝓜.adj_Δ_Γ D x y]
        exact SimpleGraph.adj_comm _ _ _
      rw [this, Set.ncard_preimage_of_injective_subset_range 𝓜.ψ.injective (by
        rw [Equiv.range_eq_univ]; exact Set.subset_univ _), Set.ncard_coe_finset,
        card_of_mem_hexads (𝓜.θ y).2]
    omega
  have hB₁h : (𝓜.θ y).1 ∈ hexads := (𝓜.θ y).2
  have hnot : (𝓜.θ y).1 ∉ 𝓜.hexNbrs y := fun h =>
    (rGraph G a b).irrefl ((𝓜.mem_hexNbrs_iff).1 h)
  have h3 := m22_facts.2.2.1 (𝓜.θ y).1 hB₁h
  have hsubZ : 𝓜.hexNbrs y ⊆ ↑(hexads.filter fun C => Disjoint (𝓜.θ y).1 C) := by
    intro C hC
    have hCh := 𝓜.hexNbrs_subset y hC
    have hCne : C ≠ (𝓜.θ y).1 := fun h => hnot (h ▸ hC)
    rcases m22_facts.2.1.1 (𝓜.θ y).1 hB₁h C (Finset.mem_coe.1 hCh) (Ne.symm hCne) with h0 | h2
    · refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_coe.1 hCh, ?_⟩)
      rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
      exact h0
    · exfalso
      have hall : ↑(hexads.filter fun C' => ((𝓜.θ y).1 ∩ C').card = 2) ⊆ 𝓜.hexNbrs y := by
        intro C' hC'
        have hC'' := Finset.mem_filter.1 (Finset.mem_coe.1 hC')
        obtain ⟨g, hg⟩ := (h3 C (Finset.mem_coe.1 hCh) C' hC''.1).2 (by rw [h2, hC''.2])
        obtain ⟨s, hs1, hs2⟩ := 𝓜.exists_stab_θ y g
        rw [← hg, ← hs1]
        exact 𝓜.hexNbrs_stable D hs2 hC
      have := Set.ncard_le_ncard hall (𝓜.finite_hexNbrs y)
      rw [Set.ncard_coe_finset, (m22_facts.2.1.2 (𝓜.θ y).1 hB₁h).2, hcard] at this
      omega
  have hTZ : 𝓜.hexNbrs y = ↑(hexads.filter fun C => Disjoint (𝓜.θ y).1 C) :=
    Set.eq_of_subset_of_ncard_le hsubZ
      (by rw [Set.ncard_coe_finset, (m22_facts.2.1.2 (𝓜.θ y).1 hB₁h).1, hcard])
      (Finset.finite_toSet _)
  constructor
  · intro h
    have hmem : (𝓜.θ y').1 ∈ 𝓜.hexNbrs y := (𝓜.mem_hexNbrs_iff).2 h
    rw [hTZ] at hmem
    exact ⟨fun e => h.ne (congrArg Subtype.val (𝓜.θ.injective e)),
      (Finset.mem_filter.1 (Finset.mem_coe.1 hmem)).2⟩
  · rintro ⟨-, hd⟩
    refine (𝓜.mem_hexNbrs_iff).1 ?_
    rw [hTZ]
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(𝓜.θ y').2, hd⟩)

end Model

end CFSG.Sporadic.Recognition.HSWales
