module

public import CFSG.Quasithin.EmptyFaithful.S152He9C
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin

namespace W5

theorem mem_normalizer_iff_map_eq {X : Type*} [Group X] {A : Subgroup X} {g : X} :
    g ∈ Subgroup.normalizer (A : Set X) ↔ A.map (MulAut.conj g).toMonoidHom = A := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hg _).2 (by simpa [mul_assoc] using hx), ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · intro h x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        simpa using h1
      rwa [← this]

theorem conj_A1_of_mem_base {w : W5} (hw : w ∈ base) :
    A1.map (MulAut.conj w).toMonoidHom = A1 := by
  rw [← mem_normalizer_iff_map_eq, normalizer_A1]
  exact hw

theorem conj_A2_of_mem_base {w : W5} (hw : w ∈ base) :
    A2.map (MulAut.conj w).toMonoidHom = A2 := by
  rw [← mem_normalizer_iff_map_eq, normalizer_A2]
  exact hw

theorem conj_A1_of_not_base {w : W5} (hw : w.right = g2) :
    A1.map (MulAut.conj w).toMonoidHom = A2 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := hy
    show w * incl1 σ * w⁻¹ ∈ A2
    rw [conj_incl1_of_not_base hw]
    exact incl2_mem_A2 (Subgroup.Normal.conj_mem inferInstance σ hσ _)
  · intro hx
    refine ⟨w⁻¹ * x * w, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    obtain ⟨σ, hσ, rfl⟩ := hx
    have hw' : (w⁻¹).right = g2 := by simp [inv_r, hw, Q2_inv]
    have := conj_incl2_of_not_base hw' σ
    rw [inv_inv] at this
    rw [this]
    exact incl1_mem_A1 (Subgroup.Normal.conj_mem inferInstance σ hσ _)

theorem conj_A2_of_not_base {w : W5} (hw : w.right = g2) :
    A2.map (MulAut.conj w).toMonoidHom = A1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := hy
    show w * incl2 σ * w⁻¹ ∈ A1
    rw [conj_incl2_of_not_base hw]
    exact incl1_mem_A1 (Subgroup.Normal.conj_mem inferInstance σ hσ _)
  · intro hx
    refine ⟨w⁻¹ * x * w, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    obtain ⟨σ, hσ, rfl⟩ := hx
    have hw' : (w⁻¹).right = g2 := by simp [inv_r, hw, Q2_inv]
    have := conj_incl1_of_not_base hw' σ
    rw [inv_inv] at this
    rw [this]
    exact incl2_mem_A2 (Subgroup.Normal.conj_mem inferInstance σ hσ _)

theorem right_eq_g2_of_not_mem_base {w : W5} (hw : w ∉ base) : w.right = g2 := by
  rcases Q2_cases w.right with h | h
  · exact absurd (mem_base.2 h) hw
  · exact h

end W5

section Lift

variable {Γ : Type*} [Group Γ] [Finite Γ]

structure WrData (π : Γ →* W5) : Prop where
  surj : Function.Surjective π
  ker2 : IsPGroup 2 π.ker

theorem WrData.solvable {π : Γ →* W5} (h : WrData π) : Group.IsSolvable π.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.ker2.isNilpotent
  infer_instance

theorem exists_components {π : Γ →* W5} (h : WrData π) :
    ∃ K₁ K₂ : Subgroup Γ, K₁ ∈ cComp (⊤ : Subgroup Γ) ∧ K₂ ∈ cComp (⊤ : Subgroup Γ) ∧
      K₁.map π = W5.A1 ∧ K₂.map π = W5.A2 := by
  have hs := h.solvable
  obtain ⟨K₁, hK₁, h1⟩ := map_surjOn_cComp_top π h.surj hs W5.A1_mem_cComp
  obtain ⟨K₂, hK₂, h2⟩ := map_surjOn_cComp_top π h.surj hs W5.A2_mem_cComp
  exact ⟨K₁, K₂, hK₁, hK₂, h1, h2⟩

theorem conj_mem_cComp_top {K : Subgroup Γ} (hK : K ∈ cComp (⊤ : Subgroup Γ)) (g : Γ) :
    K.map (MulAut.conj g).toMonoidHom ∈ cComp (⊤ : Subgroup Γ) := by
  have h1 := cComp_map_mulEquiv (MulAut.conj g) hK
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1

theorem map_conj_map (π : Γ →* W5) (K : Subgroup Γ) (g : Γ) :
    (K.map (MulAut.conj g).toMonoidHom).map π = (K.map π).map (MulAut.conj (π g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun x => by simp [MulAut.conj_apply]

theorem mem_normalizer_iff_K1 {π : Γ →* W5} (hπ : WrData π) {K₁ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (m₁ : K₁.map π = W5.A1)
    (g : Γ) : g ∈ Subgroup.normalizer (K₁ : Set Γ) ↔ π g ∈ W5.base := by
  constructor
  · intro hg
    rw [W5.mem_normalizer_iff_map_eq] at hg
    have := congrArg (Subgroup.map π) hg
    rw [map_conj_map, m₁] at this
    rw [← W5.normalizer_A1, W5.mem_normalizer_iff_map_eq]
    exact this
  · intro hg
    rw [W5.mem_normalizer_iff_map_eq]
    apply map_injOn_cComp_top π hπ.solvable (conj_mem_cComp_top hK₁ g) hK₁
    rw [map_conj_map, m₁, W5.conj_A1_of_mem_base hg]

theorem mem_normalizer_iff_K2 {π : Γ →* W5} (hπ : WrData π) {K₂ : Subgroup Γ}
    (hK₂ : K₂ ∈ cComp (⊤ : Subgroup Γ)) (m₂ : K₂.map π = W5.A2)
    (g : Γ) : g ∈ Subgroup.normalizer (K₂ : Set Γ) ↔ π g ∈ W5.base := by
  constructor
  · intro hg
    rw [W5.mem_normalizer_iff_map_eq] at hg
    have := congrArg (Subgroup.map π) hg
    rw [map_conj_map, m₂] at this
    rw [← W5.normalizer_A2, W5.mem_normalizer_iff_map_eq]
    exact this
  · intro hg
    rw [W5.mem_normalizer_iff_map_eq]
    apply map_injOn_cComp_top π hπ.solvable (conj_mem_cComp_top hK₂ g) hK₂
    rw [map_conj_map, m₂, W5.conj_A2_of_mem_base hg]

theorem conj_eq_of_not_mem_base {π : Γ →* W5} (hπ : WrData π) {K₁ K₂ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (hK₂ : K₂ ∈ cComp (⊤ : Subgroup Γ))
    (m₁ : K₁.map π = W5.A1) (m₂ : K₂.map π = W5.A2) {g : Γ} (hg : π g ∉ W5.base) :
    K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  apply map_injOn_cComp_top π hπ.solvable (conj_mem_cComp_top hK₁ g) hK₂
  rw [map_conj_map, m₁, m₂, W5.conj_A1_of_not_base (W5.right_eq_g2_of_not_mem_base hg)]

theorem conj_eq_of_not_mem_base' {π : Γ →* W5} (hπ : WrData π) {K₁ K₂ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (hK₂ : K₂ ∈ cComp (⊤ : Subgroup Γ))
    (m₁ : K₁.map π = W5.A1) (m₂ : K₂.map π = W5.A2) {g : Γ} (hg : π g ∉ W5.base) :
    K₂.map (MulAut.conj g).toMonoidHom = K₁ := by
  apply map_injOn_cComp_top π hπ.solvable (conj_mem_cComp_top hK₂ g) hK₁
  rw [map_conj_map, m₁, m₂, W5.conj_A2_of_not_base (W5.right_eq_g2_of_not_mem_base hg)]

theorem ker_le_of_sylow {π : Γ →* W5} (hπ : WrData π) {T : Subgroup Γ} (hT2 : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) : π.ker ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : π.ker.Normal := π.normal_ker
  have h := hπ.ker2.le_sylow_of_normal (hT2.toSylow hTi)
  simpa using h

theorem map_sylow_odd {π : Γ →* W5} (hπ : WrData π) {T : Subgroup Γ} (hTi : ¬ 2 ∣ T.index) :
    ¬ 2 ∣ (T.map π).index := fun h =>
  hTi (h.trans (Subgroup.index_map_dvd T hπ.surj))

theorem sup_eq_top {π : Γ →* W5} (hπ : WrData π) {K₁ K₂ : Subgroup Γ}
    (m₁ : K₁.map π = W5.A1) (m₂ : K₂.map π = W5.A2) {T : Subgroup Γ}
    (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) : K₁ ⊔ K₂ ⊔ T = ⊤ := by
  have hmap : (K₁ ⊔ K₂ ⊔ T).map π = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, m₁, m₂, eq_top_iff]
    rw [← W5.S0_sup_eq_top (map_sylow_odd hπ hTi)]
    exact sup_le_sup_right (fun w hw => by
      obtain ⟨a, ha, b, hb, rfl⟩ := W5.S0_eq_mul hw
      exact (W5.A1 ⊔ W5.A2).mul_mem ((le_sup_left : W5.A1 ≤ W5.A1 ⊔ W5.A2) ha)
        ((le_sup_right : W5.A2 ≤ W5.A1 ⊔ W5.A2) hb)) _
  have hle : π.ker ≤ K₁ ⊔ K₂ ⊔ T := (ker_le_of_sylow hπ hT2 hTi).trans le_sup_right
  have h1 := Subgroup.comap_map_eq π (K₁ ⊔ K₂ ⊔ T)
  rw [hmap, Subgroup.comap_top, sup_eq_left.2 hle] at h1
  exact h1.symm

@[expose] def chi (π : Γ →* W5) : Γ →* Q2 := (RegularWreathProduct.rightHom : W5 →* Q2).comp π

theorem mem_ker_chi {π : Γ →* W5} {g : Γ} : g ∈ (chi π).ker ↔ π g ∈ W5.base := Iff.rfl

theorem normalizer_eq_ker_chi {π : Γ →* W5} (hπ : WrData π) {K₁ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (m₁ : K₁.map π = W5.A1) :
    Subgroup.normalizer (K₁ : Set Γ) = (chi π).ker := by
  ext g
  rw [mem_normalizer_iff_K1 hπ hK₁ m₁, mem_ker_chi]

theorem chi_range {π : Γ →* W5} (hπ : WrData π) : (chi π).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro q
  obtain ⟨g, hg⟩ := hπ.surj (RegularWreathProduct.inl q)
  exact ⟨g, by simp [chi, hg]⟩

theorem index_normalizer {π : Γ →* W5} (hπ : WrData π) {K₁ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (m₁ : K₁.map π = W5.A1) :
    (Subgroup.normalizer (K₁ : Set Γ)).index = 2 := by
  rw [normalizer_eq_ker_chi hπ hK₁ m₁, Subgroup.index_ker, chi_range hπ, Subgroup.card_top,
    W5.card_Q2]

theorem ker_le_inf_normalizer {π : Γ →* W5} (hπ : WrData π) {K₁ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (m₁ : K₁.map π = W5.A1) {T : Subgroup Γ}
    (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    π.ker ≤ T ⊓ Subgroup.normalizer (K₁ : Set Γ) := by
  refine le_inf (ker_le_of_sylow hπ hT2 hTi) fun g hg => ?_
  rw [mem_normalizer_iff_K1 hπ hK₁ m₁]
  have : π g = 1 := hg
  rw [this]
  exact one_mem _

theorem exists_not_mem_base {π : Γ →* W5} (hπ : WrData π) {T : Subgroup Γ} (hT2 : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) : ∃ t ∈ T, π t ∉ W5.base := by
  by_contra h
  push Not at h
  apply W5.not_le_base_of_sylow (hT2.map π) (map_sylow_odd hπ hTi)
  rintro _ ⟨t, ht, rfl⟩
  exact h t ht

theorem relIndex_inf_normalizer {π : Γ →* W5} (hπ : WrData π) {K₁ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (m₁ : K₁.map π = W5.A1) {T : Subgroup Γ}
    (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    (T ⊓ Subgroup.normalizer (K₁ : Set Γ)).relIndex T = 2 := by
  have h1 : (T ⊓ Subgroup.normalizer (K₁ : Set Γ)).subgroupOf T = ((chi π).comp T.subtype).ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf,
      normalizer_eq_ker_chi hπ hK₁ m₁]
    simp [MonoidHom.mem_ker]
  have hr : ((chi π).comp T.subtype).range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro q
    obtain ⟨t, ht, htb⟩ := exists_not_mem_base hπ hT2 hTi
    rcases Q2_cases q with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨⟨t, ht⟩, W5.right_eq_g2_of_not_mem_base htb⟩
  unfold Subgroup.relIndex
  rw [h1, Subgroup.index_ker, hr, Subgroup.card_top, W5.card_Q2]

theorem relIndex_inf_normalizer_odd {π : Γ →* W5} (hπ : WrData π) {K₁ : Subgroup Γ}
    (hK₁ : K₁ ∈ cComp (⊤ : Subgroup Γ)) (m₁ : K₁.map π = W5.A1) {T : Subgroup Γ}
    (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    ¬ 2 ∣ (T ⊓ Subgroup.normalizer (K₁ : Set Γ)).relIndex (Subgroup.normalizer (K₁ : Set Γ)) := by
  have hST : T ⊓ Subgroup.normalizer (K₁ : Set Γ) ≤ T := inf_le_left
  have hSN : T ⊓ Subgroup.normalizer (K₁ : Set Γ) ≤ Subgroup.normalizer (K₁ : Set Γ) := inf_le_right
  have h1 := Subgroup.relIndex_mul_index hST
  have h2 := Subgroup.relIndex_mul_index hSN
  rw [relIndex_inf_normalizer hπ hK₁ m₁ hT2 hTi] at h1
  rw [index_normalizer hπ hK₁ m₁] at h2
  have : (T ⊓ Subgroup.normalizer (K₁ : Set Γ)).relIndex (Subgroup.normalizer (K₁ : Set Γ)) =
      T.index := by omega
  rw [this]
  exact hTi

end Lift

end CFSG.Quasithin.He9
