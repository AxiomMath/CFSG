module

public import CFSG.RankThree.CentralLiftU.UnitaryThreeLift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.RankThree.CentralLift.LinearTwoLifting
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.RankThree.CentralLiftU

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedSU)
open scoped Matrix

universe u v

section Package

variable {H : Type u} [Group H] {E : Type v} {G : Type*} [Group E] [Group G]

theorem lifting_package_of_unique (π : E →* G)
    (hex : ∀ β : H →* G, ∃ βh : H →* E, π.comp βh = β)
    (huniq : ∀ β₁ β₂ : H →* E, π.comp β₁ = π.comp β₂ → β₁ = β₂) (α : H →* G) :
    (∃! αh : H →* E, π.comp αh = α) ∧
    ∀ αh : H →* E, π.comp αh = α →
      (Function.Injective α → Function.Injective αh) ∧
      (∀ (e : E) (β : H →* E),
        π.comp β = (MulAut.conj (π e)).toMonoidHom.comp α ↔
          β = (MulAut.conj e).toMonoidHom.comp αh) ∧
      ∀ g : G, (∀ x, g * α x = α x * g) → ∀ e : E, π e = g → ∀ x, e * αh x = αh x * e := by
  obtain ⟨αh, hαh⟩ := hex α
  refine ⟨⟨αh, hαh, fun β hβ => huniq β αh (hβ.trans hαh.symm)⟩, fun αh' hαh' => ?_⟩
  have hconj : ∀ e : E, π.comp ((MulAut.conj e).toMonoidHom.comp αh') =
      (MulAut.conj (π e)).toMonoidHom.comp α := by
    intro e
    ext x
    change π (e * αh' x * e⁻¹) = π e * α x * (π e)⁻¹
    rw [map_mul, map_mul, map_inv, ← DFunLike.congr_fun hαh' x]
    rfl
  refine ⟨fun hα x y hxy => hα ?_, fun e β => ⟨fun hβ => ?_, fun hβ => ?_⟩,
    fun g hg e he x => ?_⟩
  · rw [← DFunLike.congr_fun hαh' x, ← DFunLike.congr_fun hαh' y]
    exact congrArg π hxy
  · exact huniq _ _ (hβ.trans (hconj e).symm)
  · rw [hβ]
    exact hconj e
  · have hα : (MulAut.conj (π e)).toMonoidHom.comp α = α := by
      ext y
      change π e * α y * (π e)⁻¹ = α y
      rw [he, hg y, mul_inv_cancel_right]
    have h := huniq _ αh' (((hconj e).trans hα).trans hαh'.symm)
    have hx := DFunLike.congr_fun h x
    change e * αh' x * e⁻¹ = αh' x at hx
    calc e * αh' x = e * αh' x * e⁻¹ * e := by group
      _ = αh' x * e := by rw [hx]

theorem lift_unique_of_coprime [Finite H] {p : ℕ} [Fact p.Prime] {π : E →* G}
    (hcen : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker)
    (hcop : Nat.Coprime p (Nat.card H)) {β₁ β₂ : H →* E} (h : π.comp β₁ = π.comp β₂) :
    β₁ = β₂ := by
  have hmem : ∀ x, (β₁ x)⁻¹ * β₂ x ∈ π.ker := fun x => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
      h, inv_mul_cancel]
  let δ : H →* E :=
    { toFun := fun x => (β₁ x)⁻¹ * β₂ x
      map_one' := by rw [map_one, map_one, inv_one, one_mul]
      map_mul' := fun x y => by
        have hc := Subgroup.mem_center_iff.1 (hcen (hmem x)) (β₁ y)⁻¹
        change (β₁ (x * y))⁻¹ * β₂ (x * y) = (β₁ x)⁻¹ * β₂ x * ((β₁ y)⁻¹ * β₂ y)
        calc (β₁ (x * y))⁻¹ * β₂ (x * y) = (β₁ y)⁻¹ * ((β₁ x)⁻¹ * β₂ x) * β₂ y := by
              rw [map_mul, map_mul]
              group
          _ = (β₁ x)⁻¹ * β₂ x * (β₁ y)⁻¹ * β₂ y := by rw [hc]
          _ = (β₁ x)⁻¹ * β₂ x * ((β₁ y)⁻¹ * β₂ y) := by group }
  have h1 := CFSG.RankThree.CentralLift.eq_one_of_coprime hp hcop δ hmem
  ext x
  have hx := DFunLike.congr_fun h1 x
  exact inv_mul_eq_one.1 hx

theorem forall_section_of_coprime [Finite H] {p : ℕ} (hp : p.Prime)
    (hcop : ¬p ∣ Nat.card H) (R : Type*) [Group R] [Finite R] (ρ : R →* H)
    (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ Subgroup.center R) (hpk : IsPGroup p ρ.ker) :
    ∃ s : H →* R, ∀ x, ρ (s x) = x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hpk.exists_card_eq
  have hcop' : Nat.Coprime (Nat.card ρ.ker) (Nat.card H) := by
    rw [hn]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hcop).pow_left n
  obtain ⟨σ, hσ⟩ := CFSG.RankThree.CentralLift.exists_section_of_coprime ρ hρ hcen hcop'
  exact ⟨σ, fun x => DFunLike.congr_fun hσ x⟩

end Package

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem nonempty_gramSU_mulEquiv_statedSU {G₀ : Matrix (Fin 3) (Fin 3) K}
    (hG : (G₀.map h.bar)ᵀ = G₀) (hdet : G₀.det ≠ 0) :
    Nonempty (gramSU h G₀ ≃* StatedSU 3 (2 ^ f) K) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨h.prime⟩
  have := h.charP
  have hK := card_eq_sq_of_unitaryFieldData h
  obtain ⟨e₁⟩ := nonempty_gramSU_mulEquiv_SU h hG hdet
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  exact ⟨(e₁.trans (conjEquiv P hP)).trans
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3))⟩

theorem nonempty_sesqSU_mulEquiv_statedSU {V : Type*} [AddCommGroup V] [Module K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 3) :
    Nonempty (sesqSpecialUnitaryGroup B ≃* StatedSU 3 (2 ^ f) K) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨h.prime⟩
  have := h.charP
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  have hK := card_eq_sq_of_unitaryFieldData h
  obtain ⟨b', hb'⟩ : ∃ b' : Module.Basis (Fin 3) K V,
      ∀ i j, B (b' i) (b' j) = if i = j then 1 else 0 := by
    obtain ⟨c, hc⟩ := h.exists_orthonormal_basis hB hBl
    exact ⟨c.reindex (finCongr hV), fun i j => by
      rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hc]
      simp⟩
  obtain ⟨e₁⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid h b' hb'
  have hS : SUid h.barEquiv 3 = SUid (unitaryInvolution K 2 f) 3 := by
    rw [barEquiv_eq_unitaryInvolution h]
  exact ⟨(e₁.trans (MulEquiv.subgroupCongr hS)).trans
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3))⟩

include h in
theorem card_statedSU_three_two (hf : f = 1) : Nat.card (StatedSU 3 (2 ^ f) K) = 216 := by
  have := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  obtain ⟨e⟩ := nonempty_sesqSU_mulEquiv_statedSU h hsymm hsep (Module.finrank_fin_fun K)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  subst hf
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 27 := by decide
  rw [hprod] at hSU
  norm_num at hSU
  rw [← Nat.card_congr e.toEquiv]
  exact_mod_cast hSU

include h in
theorem statedSU_three_even_lift_facts {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    (∀ (R : Type*) [Group R] [Finite R] (ρ : R →* StatedSU 3 (2 ^ f) K),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center R → IsPGroup p ρ.ker →
        ∃ s : StatedSU 3 (2 ^ f) K →* R, ∀ x, ρ (s x) = x) ∧
    ∀ {E G : Type*} [Group E] [Group G] (π : E →* G), π.ker ≤ Subgroup.center E →
      IsPGroup p π.ker → ∀ β₁ β₂ : StatedSU 3 (2 ^ f) K →* E, π.comp β₁ = π.comp β₂ →
        β₁ = β₂ := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨h.prime⟩
  have := h.charP
  have : Fact p.Prime := ⟨hp⟩
  have hK := card_eq_sq_of_unitaryFieldData h
  have : Finite (StatedSU 3 (2 ^ f) K) := inferInstance
  rcases Nat.lt_or_ge f 2 with hf | hf
  ·
    have hf1 : f = 1 := by have := h.one_le; omega
    have hcard := card_statedSU_three_two h hf1
    have hndvd : ¬p ∣ Nat.card (StatedSU 3 (2 ^ f) K) := by
      rw [hcard]
      intro hd
      have h216 : (216 : ℕ) = 2 ^ 3 * 3 ^ 3 := by norm_num
      rw [h216] at hd
      rcases (Nat.Prime.dvd_mul hp).1 hd with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    refine ⟨fun R _ _ ρ hρ hcen hpk => forall_section_of_coprime hp hndvd R ρ hρ hcen hpk,
      fun π hcen hpk β₁ β₂ hβ => lift_unique_of_coprime hcen hpk
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd) hβ⟩
  ·
    have hnq : (3, 2 ^ f) ≠ (3, 2) := fun e => by
      have : 2 ^ f = 2 ^ 1 := by simpa using congrArg Prod.snd e
      have := Nat.pow_right_injective le_rfl this
      omega
    have hperf : Group.IsPerfect (StatedSU 3 (2 ^ f) K) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK le_rfl hnq
    refine ⟨fun R _ _ ρ hρ hcen hpk => ?_,
      fun π hcen _ β₁ β₂ hβ => eq_of_comp_eq_of_isPerfect hcen hβ⟩
    have hodd : Odd (Nat.card ρ.ker) := by
      obtain ⟨n, hn⟩ := hpk.exists_card_eq
      rw [hn]
      exact (hp.odd_of_ne_two (by omega)).pow
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting hK hf hρ hcen
        hodd
    exact ⟨σ, hσ⟩

theorem even_unitary_three_central_large_prime_homomorphism_lifting
    {G₀ : Matrix (Fin 3) (Fin 3) K} (hG : (G₀.map h.bar)ᵀ = G₀) (hdet : G₀.det ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {E G : Type*} [Group E] [Group G] [Finite E] [Finite G]
    (π : E →* G) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) (α : gramSU h G₀ →* G) :
    (∃! αh : gramSU h G₀ →* E, π.comp αh = α) ∧
    ∀ αh : gramSU h G₀ →* E, π.comp αh = α →
      (Function.Injective α → Function.Injective αh) ∧
      (∀ (e : E) (β : gramSU h G₀ →* E),
        π.comp β = (MulAut.conj (π e)).toMonoidHom.comp α ↔
          β = (MulAut.conj e).toMonoidHom.comp αh) ∧
      ∀ g : G, (∀ x, g * α x = α x * g) → ∀ e : E, π e = g → ∀ x, e * αh x = αh x * e := by
  obtain ⟨e⟩ := nonempty_gramSU_mulEquiv_statedSU h hG hdet
  have := h.finite
  have : Finite (gramSU h G₀) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨hsplit, huniq⟩ := statedSU_three_even_lift_facts h hp hp3
  refine lifting_package_of_unique π (fun β => ?_) (fun β₁ β₂ hβ => ?_) α
  · exact exists_lift_of_forall_section_prime (fun R _ _ ρ hρ hcen hpk =>
      forall_section_of_mulEquiv e (fun ρ' hρ' hcen' hp' => hsplit R ρ' hρ' hcen' hp')
        ρ hρ hcen hpk) hπ hC hCp β
  · have h1 := huniq π hC hCp (β₁.comp e.symm.toMonoidHom) (β₂.comp e.symm.toMonoidHom)
      (by rw [← MonoidHom.comp_assoc, hβ, MonoidHom.comp_assoc])
    ext x
    have := DFunLike.congr_fun h1 (e x)
    simpa using this

theorem even_unitary_three_central_large_prime_homomorphism_lifting'
    {V : Type*} [AddCommGroup V] [Module K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hV : Module.finrank K V = 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {E G : Type*} [Group E] [Group G] [Finite E] [Finite G] (π : E →* G)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker)
    (α : sesqSpecialUnitaryGroup B →* G) :
    (∃! αh : sesqSpecialUnitaryGroup B →* E, π.comp αh = α) ∧
    ∀ αh : sesqSpecialUnitaryGroup B →* E, π.comp αh = α →
      (Function.Injective α → Function.Injective αh) ∧
      (∀ (e : E) (β : sesqSpecialUnitaryGroup B →* E),
        π.comp β = (MulAut.conj (π e)).toMonoidHom.comp α ↔
          β = (MulAut.conj e).toMonoidHom.comp αh) ∧
      ∀ g : G, (∀ x, g * α x = α x * g) → ∀ e : E, π e = g → ∀ x, e * αh x = αh x * e := by
  obtain ⟨e⟩ := nonempty_sesqSU_mulEquiv_statedSU h hB hBl hV
  have := h.finite
  have : Finite (sesqSpecialUnitaryGroup B) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨hsplit, huniq⟩ := statedSU_three_even_lift_facts h hp hp3
  refine lifting_package_of_unique π (fun β => ?_) (fun β₁ β₂ hβ => ?_) α
  · exact exists_lift_of_forall_section_prime (fun R _ _ ρ hρ hcen hpk =>
      forall_section_of_mulEquiv e (fun ρ' hρ' hcen' hp' => hsplit R ρ' hρ' hcen' hp')
        ρ hρ hcen hpk) hπ hC hCp β
  · have h1 := huniq π hC hCp (β₁.comp e.symm.toMonoidHom) (β₂.comp e.symm.toMonoidHom)
      (by rw [← MonoidHom.comp_assoc, hβ, MonoidHom.comp_assoc])
    ext x
    have := DFunLike.congr_fun h1 (e x)
    simpa using this

end Even

end CFSG.RankThree.CentralLiftU
