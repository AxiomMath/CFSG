module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLABender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {L P : Subgroup G} {Λ : Type} [Group Λ]

omit [Finite G] in
theorem map_normalizer_eq_normalizer_map1521 (hP : IsSylowTwoOf P L) {π : ↥L →* Λ}
    (hπ : Function.Surjective π) (hker : π.ker = CFSG.pCore 2 ↥L) :
    ((L ⊓ Subgroup.normalizer (P : Set G)).subgroupOf L).map π =
      Subgroup.normalizer (((P.subgroupOf L).map π : Subgroup Λ) : Set Λ) := by
  have hN : (L ⊓ Subgroup.normalizer (P : Set G)).subgroupOf L =
      Subgroup.normalizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hP.1]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hN]
  have hkerP : ∀ x : ↥L, π x = 1 → x ∈ P.subgroupOf L := fun x hx =>
    GoldMLA.pCore_le_subgroupOf hP x (hker ▸ (MonoidHom.mem_ker.mpr hx))
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    have hb' := Subgroup.mem_normalizer_iff.mp hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨b * x * b⁻¹, (hb' x).mp hx, by simp⟩
    · rintro ⟨x', hx', hxy⟩
      refine ⟨b⁻¹ * x' * b, (hb' _).mpr (by simpa [mul_assoc] using hx'), ?_⟩
      have : π x' = π b * y * (π b)⁻¹ := hxy
      simp [map_mul, map_inv, this, mul_assoc]
  · intro y hy
    obtain ⟨b, rfl⟩ := hπ y
    refine ⟨b, ?_, rfl⟩
    have key : ∀ c : ↥L, π c ∈ Subgroup.normalizer (((P.subgroupOf L).map π : Subgroup Λ) :
        Set Λ) → ∀ x ∈ P.subgroupOf L, c * x * c⁻¹ ∈ P.subgroupOf L := by
      intro c hc x hx
      have h1 : π c * π x * (π c)⁻¹ ∈ (P.subgroupOf L).map π :=
        (Subgroup.mem_normalizer_iff.mp hc _).mp ⟨x, hx, rfl⟩
      obtain ⟨x', hx', hxx'⟩ := h1
      have h2 : x'⁻¹ * (c * x * c⁻¹) ∈ P.subgroupOf L := by
        apply hkerP
        simp only [map_mul, map_inv, hxx']
        group
      have := (P.subgroupOf L).mul_mem hx' h2
      simpa using this
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key b hy x, fun hx => ?_⟩
    have hy' : π b⁻¹ ∈ Subgroup.normalizer (((P.subgroupOf L).map π : Subgroup Λ) : Set Λ) := by
      rw [map_inv]; exact Subgroup.inv_mem _ hy
    have := key b⁻¹ hy' _ hx
    simpa [mul_assoc] using this

theorem exists_lift_oTwoUpper1521 (hP : IsSylowTwoOf P L) {π : ↥L →* Λ}
    (hπ : Function.Surjective π) (hker : π.ker = CFSG.pCore 2 ↥L) {M : Λ}
    (hM : M ∈ oTwoUpper (Subgroup.normalizer (((P.subgroupOf L).map π : Subgroup Λ) : Set Λ))) :
    ∃ b : ↥L, (b : G) ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)) ∧ π b = M := by
  rw [← map_normalizer_eq_normalizer_map1521 hP hπ hker, oTwoUpper_map] at hM
  obtain ⟨b, hb, rfl⟩ := hM
  refine ⟨b, ?_, rfl⟩
  have h := oTwoUpper_map L.subtype ((L ⊓ Subgroup.normalizer (P : Set G)).subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h
  rw [h]
  exact ⟨b, hb, rfl⟩

theorem exists_odd_index_oTwoUpper1521 (hP : IsSylowTwoOf P L) {π : ↥L →* Λ}
    (hπ : Function.Surjective π) (hker : π.ker = CFSG.pCore 2 ↥L)
    (hidx : ¬ 2 ∣ (oTwoUpper (Subgroup.normalizer
      (((P.subgroupOf L).map π : Subgroup Λ) : Set Λ))).index) :
    ∃ H : Subgroup G, H ≤ L ∧ ¬ 2 ∣ (H.subgroupOf L).index ∧
      ∀ h ∈ H, ∃ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), ∃ q ∈ pCoreOf 2 L,
        h = b * q := by
  set H₀ : Subgroup ↥L := (oTwoUpper (Subgroup.normalizer
      (((P.subgroupOf L).map π : Subgroup Λ) : Set Λ))).comap π with hH₀
  refine ⟨H₀.map L.subtype, Subgroup.map_subtype_le H₀, ?_, ?_⟩
  · have h1 : (H₀.map L.subtype).subgroupOf L = H₀ :=
      Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _
    rw [h1, hH₀, Subgroup.index_comap_of_surjective _ hπ]
    exact hidx
  · rintro _ ⟨h', hh', rfl⟩
    obtain ⟨b, hb, hbπ⟩ := exists_lift_oTwoUpper1521 hP hπ hker (M := π h') hh'
    refine ⟨(b : G), hb, ((b⁻¹ * h' : ↥L) : G), ?_, by simp⟩
    have hq : b⁻¹ * h' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbπ]; simp
    rw [hker] at hq
    exact ⟨b⁻¹ * h', hq, rfl⟩

theorem commutator_mem_pCoreOf_of_centralizes1521 (hP : IsSylowTwoOf P L) {π : ↥L →* Λ}
    (hπ : Function.Surjective π) (hker : π.ker = CFSG.pCore 2 ↥L)
    (hrig : ∀ β : MulAut Λ, (∀ z ∈ Subgroup.normalizer (((P.subgroupOf L).map π : Subgroup Λ) :
      Set Λ), Odd (orderOf z) → β z = z) → β = 1)
    {v : G} (hv : v ∈ Subgroup.normalizer (L : Set G))
    (hc : ∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), v * b = b * v) :
    ∀ l ∈ L, ⁅l, v⁆ ∈ pCoreOf 2 L := by
  classical
  set σ : MulAut ↥L := conjAct L ⟨v, hv⟩ with hσdef
  have hσ : ∀ x : ↥L, ((σ x : ↥L) : G) = v * x * v⁻¹ := fun x => rfl
  have hker' : π.ker.map σ.toMonoidHom = π.ker := by
    rw [hker]
    exact Subgroup.characteristic_iff_map_eq.mp (CFSG.pCore_characteristic (G := ↥L) (p := 2)) σ
  let e : (↥L ⧸ π.ker) ≃* Λ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let σ' : (↥L ⧸ π.ker) ≃* (↥L ⧸ π.ker) := QuotientGroup.congr π.ker π.ker σ hker'
  let β : MulAut Λ := e.symm.trans (σ'.trans e)
  have hβ : ∀ x : ↥L, β (π x) = π (σ x) := by
    intro x
    have h1 : e (QuotientGroup.mk x) = π x := rfl
    have h2 : e.symm (π x) = QuotientGroup.mk x := by rw [← h1]; exact e.symm_apply_apply _
    show e (σ' (e.symm (π x))) = π (σ x)
    rw [h2]
    rfl
  have hβ1 : β = 1 := by
    apply hrig
    intro z hz hzo
    have hzM : z ∈ oTwoUpper (Subgroup.normalizer (((P.subgroupOf L).map π : Subgroup Λ) :
        Set Λ)) := mem_oTwoUpper_of_odd hz hzo
    obtain ⟨b, hb, rfl⟩ := exists_lift_oTwoUpper1521 hP hπ hker hzM
    rw [hβ]
    congr 1
    apply Subtype.ext
    rw [hσ]
    have := hc _ hb
    have e : v * (b : G) * v⁻¹ = (b : G) := by rw [this]; group
    exact e
  intro l hl
  have hall : ∀ x : ↥L, π (σ x) = π x := by
    intro x
    have := congrArg (fun γ : MulAut Λ => γ (π x)) hβ1
    simp only [MulAut.one_apply] at this
    rw [← hβ]; exact this
  have hl' : (⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hall]; simp
  have hq : (⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := hker ▸ hl'
  have hmem : (⟨l, hl⟩ : ↥L) * ((⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩)⁻¹ * (⟨l, hl⟩ : ↥L)⁻¹ ∈
      CFSG.pCore 2 ↥L :=
    Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ hq) _
  have heq : ⁅l, v⁆ = (((⟨l, hl⟩ : ↥L) * ((⟨l, hl⟩ : ↥L)⁻¹ * σ ⟨l, hl⟩)⁻¹ *
      (⟨l, hl⟩ : ↥L)⁻¹ : ↥L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ, commutatorElement_def]
    group
  rw [heq]
  exact ⟨_, hmem, rfl⟩

end Lift

end CFSG.Quasithin
