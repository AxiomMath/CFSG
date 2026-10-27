module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bCF

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13bCF

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L13b

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {ω : Fin 3 → G}

theorem exists_sylow_nor (hB3 : IsPGroup 3 B) :
    ∃ P : Subgroup G, IsSylowOf 3 P (Nor B) ∧ B ≤ P := by
  obtain ⟨P, hP⟩ := exists_sylowOf (G := G) (Nor B)
  obtain ⟨k, hk, hkB⟩ := exists_conj_le_sylowOf hP Subgroup.le_normalizer hB3
  refine ⟨P, hP, fun x hx => ?_⟩
  have hk' : k⁻¹ ∈ Nor B := inv_mem hk
  have := hkB _ (conj_mem' hk' hx)
  simpa [mul_assoc] using this

theorem conjBy_eq_of_le (M : Mono B ω) {b : G} (hb : b ∈ B) (hB : IsSylowOf 3 B (Cen b))
    {P : Subgroup G} (hPN : P ≤ Nor B) (hP3 : IsPGroup 3 P) {g : G}
    (hg : ∀ z ∈ B, g * z * g⁻¹ ∈ P) : conjBy g B = B := by
  have hle : conjBy g B ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hg z hz
  refine cfAbelian_eq M hb hB (hle.trans hPN) (hP3.to_le hle) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := M.comm x hx y hy
    show g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [this]
      _ = _ := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, M.card]

theorem sylow_top (M : Mono B ω) {b : G} (hb : b ∈ B) (hB : IsSylowOf 3 B (Cen b))
    {P : Subgroup G} (hP : IsSylowOf 3 P (Nor B)) (hBP : B ≤ P) : IsSylowOf 3 P ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := hP.2.1.exists_le_sylow
  have hPS : P = (S : Subgroup G) := by
    by_contra hne
    have hlt : P < (S : Subgroup G) := lt_of_le_of_ne hS hne
    haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥(S : Subgroup G))
    have hlt' : P.subgroupOf (S : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      exact not_le_of_gt hlt
    obtain ⟨s, hs, hsn⟩ := SetLike.exists_of_lt (hnc _ hlt')
    have hg : ∀ z ∈ B, (s : G) * z * (s : G)⁻¹ ∈ P := by
      intro z hz
      have hz' : (⟨z, hS (hBP hz)⟩ : ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) :=
        hBP hz
      have := (Subgroup.mem_normalizer_iff.mp hs _).mp hz'
      exact this
    have hconj := conjBy_eq_of_le M hb hB (hP.1) hP.2.1 hg
    have hsN : (s : G) ∈ Nor B := by
      refine mem_nor_of_forall fun y hy => ?_
      have : (s : G) * y * (s : G)⁻¹ ∈ conjBy (s : G) B := ⟨y, hy, rfl⟩
      rwa [hconj] at this
    have hP2le : P ⊔ Subgroup.zpowers (s : G) ≤ Nor B :=
      sup_le hP.1 (Subgroup.zpowers_le.mpr hsN)
    have hP2S : P ⊔ Subgroup.zpowers (s : G) ≤ (S : Subgroup G) :=
      sup_le hS (Subgroup.zpowers_le.mpr s.2)
    have hP2p : IsPGroup 3 (P ⊔ Subgroup.zpowers (s : G) : Subgroup G) :=
      S.isPGroup'.to_le hP2S
    have heq := eq_of_sylowOf hP le_sup_left hP2le hP2p
    have : (s : G) ∈ P := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact hsn this
  refine ⟨le_top, hP.2.1, ?_⟩
  rw [hPS, Subgroup.relIndex_top_right]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr S.not_dvd_index

theorem weak_closure (M : Mono B ω) {b : G} (hb : b ∈ B) (hB : IsSylowOf 3 B (Cen b))
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) {k h : G} (hk : ∀ z ∈ B, k * z * k⁻¹ ∈ Q)
    (hkh : ∀ z ∈ B, (k * h) * z * (k * h)⁻¹ ∈ Q) : ∀ z ∈ B, h * z * h⁻¹ ∈ B := by
  obtain ⟨P, hP, hBP⟩ := exists_sylow_nor hB.2.1
  have hPT := sylow_top M hb hB hP hBP
  obtain ⟨m, -, hm⟩ := exists_conj_le_sylowOf hPT le_top hQ
  have h1 := conjBy_eq_of_le M hb hB hP.1 hP.2.1 (g := m * k) fun z hz => by
    have := hm _ (hk z hz)
    simpa [mul_assoc] using this
  have h2 := conjBy_eq_of_le M hb hB hP.1 hP.2.1 (g := m * (k * h)) fun z hz => by
    have := hm _ (hkh z hz)
    simpa [mul_assoc] using this
  intro z hz
  have hw : m * (k * h) * z * (m * (k * h))⁻¹ ∈ conjBy (m * k) B := by
    rw [h1, ← h2]
    exact ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hyw⟩ := hw
  have hyw' : (m * k) * y * (m * k)⁻¹ = m * (k * h) * z * (m * (k * h))⁻¹ := hyw
  have e : m * (k * h) * z * (m * (k * h))⁻¹ = (m * k) * (h * z * h⁻¹) * (m * k)⁻¹ := by group
  have hyeq : y = h * z * h⁻¹ := mul_left_cancel (mul_right_cancel (hyw'.trans e))
  rw [← hyeq]
  exact hy


theorem nonempty_mono {b b₁ b₂ : G} (hB : IsElemAb 3 3 B)
    (hcl : B = Subgroup.closure {b, b₁, b₂})
    (hmono : ∀ n ∈ Nor B, ∀ x ∈ ({b, b₁, b₂} : Set G),
      n * x * n⁻¹ ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) :
    ∃ (ω : Fin 3 → G) (_ : Mono B ω), ω 0 = b ∧ ω 1 = b₁ ∧ ω 2 = b₂ := by
  let ω : Fin 3 → G := ![b, b₁, b₂]
  have hrange : Set.range ω = {b, b₁, b₂} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [ω]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hcl' : B = Subgroup.closure (Set.range ω) := by rw [hrange]; exact hcl
  have hmem : ∀ i, ω i ∈ B := fun i => by
    rw [hcl']
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨crd⟩ := exists_crd hB hmem hcl'
  refine ⟨ω, ⟨crd, hmem, hcl', fun n hn i => ?_, by rw [hB.2]; norm_num, ?_⟩, rfl, rfl, rfl⟩
  · have h := hmono n hn (ω i) (by rw [← hrange]; exact ⟨i, rfl⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h | h
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
    · exact ⟨1, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩
    · exact ⟨2, Or.inl h⟩
    · exact ⟨2, Or.inr h⟩
  · intro x hx y hy
    haveI := hB.1
    letI : CommGroup ↥B := IsMulCommutative.instCommGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥B) ⟨y, hy⟩)

end CFSG.RankThree.PartTwo.Sec21.FF79.L13bCF

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.PartTwo.Sec21.FF79.L13b CFSG.RankThree.PartTwo.Sec21.FF79.L13bCF

theorem controlsFusionIn_of_monomial {G : Type} [Group G] [Finite G] {b b₁ b₂ : G}
    {B : Subgroup G} (hB : IsSylowOf 3 B (Cen b)) (hM : IsFullMonomial B b b₁ b₂) :
    ControlsFusionIn B := by
  obtain ⟨ω, M, h0, -, -⟩ := nonempty_mono hM.1 hM.2.1 hM.2.2.1
  have hb : b ∈ B := h0 ▸ M.mem 0
  intro x hx y hy g hg
  have hcen : ∀ c ∈ Cen y, c * y * c⁻¹ = y := fun c hc => by
    have := (Subgroup.mem_centralizer_iff.mp hc) y (Set.mem_singleton y)
    rw [← this, mul_inv_cancel_right]
  have hBy : B ≤ Cen y := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact M.comm h hy z hz
  have hBg : conjBy g B ≤ Cen y := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← hg]
    show g * x * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * x * g⁻¹)
    have := M.comm x hx z hz
    calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [this]
      _ = _ := by group
  obtain ⟨Q0, hQ0⟩ := exists_sylowOf (G := G) (Cen y)
  obtain ⟨k₁, hk₁, hk₁Q⟩ := exists_conj_le_sylowOf hQ0 hBy hB.2.1
  obtain ⟨k₂, hk₂, hk₂Q⟩ := exists_conj_le_sylowOf hQ0 hBg
    (hB.2.1.map (MulAut.conj g).toMonoidHom)
  have hh := weak_closure M hb hB hQ0.2.1 (k := k₁) (h := k₁⁻¹ * k₂ * g) hk₁Q (fun z hz => by
    have h1 := hk₂Q (g * z * g⁻¹) ⟨z, hz, rfl⟩
    have e : k₁ * (k₁⁻¹ * k₂ * g) * z * (k₁ * (k₁⁻¹ * k₂ * g))⁻¹ =
        k₂ * (g * z * g⁻¹) * k₂⁻¹ := by group
    rw [e]
    exact h1)
  refine ⟨k₁⁻¹ * k₂ * g, mem_nor_of_forall hh, ?_⟩
  have e : k₁⁻¹ * k₂ * g * x * (k₁⁻¹ * k₂ * g)⁻¹ =
      k₁⁻¹ * (k₂ * (g * x * g⁻¹) * k₂⁻¹) * k₁ := by group
  rw [e, hg, hcen k₂ hk₂]
  have := hcen k₁⁻¹ (inv_mem hk₁)
  simpa using this

end CFSG.RankThree.PartTwo.Sec21.FF79
