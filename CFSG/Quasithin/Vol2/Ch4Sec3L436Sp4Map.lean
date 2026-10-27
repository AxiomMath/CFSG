module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Defs
public import CFSG.Quasithin.Vol2.Lie2ParabolicRadicalSp4
public import CFSG.Quasithin.H13.NQCatL2LieParabolic

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace L436

variable {G : Type} [Group G]

@[expose] def Sp4Coord (n : ℕ) (P S V : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ (α : ↥(perfectCore P) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))
      (β : ↥V →* Multiplicative (Fin 2 → F)),
      Function.Surjective α ∧ (∀ ℓ, α ℓ = 1 ↔ (ℓ : G) ∈ V) ∧ Function.Surjective β ∧
      (∀ v, β v = 1 ↔ (v : G) ∈ sp4C P V) ∧
      (∀ (a : ↥(perfectCore P)) (u v : ↥V), (v : G) = a * u * a⁻¹ →
        Multiplicative.toAdd (β v) =
          ((α a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) ∧
      (∀ ℓ : ↥(perfectCore P), (ℓ : G) ∈ S ↔ ∃ t : F, α ℓ = L436.uT F t) ∧
      (∀ v : ↥V, (v : G) ∈ sp4C P V ⊔ sp4Z P S V ↔ Multiplicative.toAdd (β v) 1 = 0)

variable {G' : Type} [Group G'] (φ : G →* G') (hφ : Function.Injective φ)
include hφ

theorem map_inf_centralizer (A B : Subgroup G) :
    (A ⊓ Subgroup.centralizer (B : Set G)).map φ =
      A.map φ ⊓ Subgroup.centralizer (B.map φ : Set G') := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyC⟩, rfl⟩
    refine ⟨⟨y, hyA, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hyC b hb]
  · rintro ⟨⟨y, hyA, rfl⟩, hC⟩
    refine ⟨y, ⟨hyA, Subgroup.mem_centralizer_iff.mpr fun b hb => hφ ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hC (φ b) ⟨b, hb, rfl⟩

theorem map_inf_normalizer (A B : Subgroup G) :
    (A ⊓ Subgroup.normalizer (B : Set G)).map φ =
      A.map φ ⊓ Subgroup.normalizer (B.map φ : Set G') := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyN⟩, rfl⟩
    refine ⟨⟨y, hyA, rfl⟩, Subgroup.mem_normalizer_iff.mpr fun z => ?_⟩
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨y * b * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN b).mp hb, by simp⟩
    · rintro ⟨c, hc, hce⟩
      refine ⟨y⁻¹ * c * y, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.mp hyN _).mpr ?_
        simpa [mul_assoc] using hc
      · have : z = φ y⁻¹ * φ c * φ y := by
          rw [hce, map_inv]
          group
        rw [this, map_mul, map_mul]
  · rintro ⟨⟨y, hyA, rfl⟩, hN⟩
    refine ⟨y, ⟨hyA, Subgroup.mem_normalizer_iff.mpr fun b => ?_⟩, rfl⟩
    have h := Subgroup.mem_normalizer_iff.mp hN (φ b)
    constructor
    · intro hb
      obtain ⟨c, hc, hce⟩ := h.mp ⟨b, hb, rfl⟩
      have : c = y * b * y⁻¹ := hφ (by rw [hce, map_mul, map_mul, map_inv])
      rw [← this]
      exact hc
    · intro hb
      obtain ⟨c, hc, hce⟩ := h.mpr ⟨_, hb, by simp⟩
      have : c = b := hφ (by rw [hce])
      rw [← this]
      exact hc

omit hφ in
theorem map_conjClosure (Z H : Subgroup G) :
    (conjClosure Z H).map φ = conjClosure (Z.map φ) (H.map φ) := by
  rw [conjClosure, conjClosure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨h, hh, z, hz, rfl⟩, rfl⟩
    exact ⟨φ h, ⟨h, hh, rfl⟩, φ z, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨h * z * h⁻¹, ⟨h, hh, z, hz, rfl⟩, by simp⟩

theorem isSylowTwoOf_map {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.map φ) (H.map φ) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map φ, ?_⟩
  change ¬ 2 ∣ (S.map φ).relIndex (H.map φ)
  rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
  exact h.2.2

variable [Finite G] [Finite G']

theorem map_sp4C (P V : Subgroup G) : (sp4C P V).map φ = sp4C (P.map φ) (V.map φ) := by
  rw [sp4C, sp4C, map_inf_centralizer φ hφ, map_perfectCore]

theorem map_sp4Z (P S V : Subgroup G) :
    (sp4Z P S V).map φ = sp4Z (P.map φ) (S.map φ) (V.map φ) := by
  rw [sp4Z, sp4Z, Subgroup.map_commutator, map_inf_centralizer φ hφ, map_inf_normalizer φ hφ,
    map_perfectCore]

theorem map_sp4K₂ (K P S V : Subgroup G) :
    (sp4K₂ K P S V).map φ = sp4K₂ (K.map φ) (P.map φ) (S.map φ) (V.map φ) := by
  rw [sp4K₂, sp4K₂, map_perfectCore, map_inf_normalizer φ hφ, map_sp4Z φ hφ]

theorem map_sp4Q₁ (K P S V : Subgroup G) :
    (sp4Q₁ K P S V).map φ = sp4Q₁ (K.map φ) (P.map φ) (S.map φ) (V.map φ) := by
  rw [sp4Q₁, sp4Q₁, ← Lie2Parabolic.pCoreOf_map_of_injective φ hφ, map_sp4K₂ φ hφ]

@[expose] noncomputable def equivOfMapEq {X : Subgroup G} {X' : Subgroup G'} (h : X.map φ = X') :
    ↥X ≃* ↥X' :=
  (X.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr h)

omit [Finite G] [Finite G'] in
theorem coe_equivOfMapEq_symm {X : Subgroup G} {X' : Subgroup G'} (h : X.map φ = X')
    (x : ↥X') : φ ((equivOfMapEq φ hφ h).symm x : G) = x := by
  conv_rhs => rw [← (equivOfMapEq φ hφ h).apply_symm_apply x]
  rfl

omit [Finite G] [Finite G'] in
theorem mem_map_iff {X : Subgroup G} {x : G} : φ x ∈ X.map φ ↔ x ∈ X :=
  Subgroup.mem_map_iff_mem hφ

theorem Sp4Coord.map {n : ℕ} {P S V : Subgroup G} (h : Sp4Coord n P S V) :
    Sp4Coord n (P.map φ) (S.map φ) (V.map φ) := by
  obtain ⟨F, _, _, hF, α, β, hαs, hαk, hβs, hβk, heq, hS, hCZ⟩ := h
  let eL := equivOfMapEq φ hφ (map_perfectCore φ P)
  let eV := equivOfMapEq φ hφ (rfl : V.map φ = V.map φ)
  have hL : ∀ ℓ : ↥(perfectCore (P.map φ)), φ (eL.symm ℓ : G) = ℓ :=
    coe_equivOfMapEq_symm φ hφ _
  have hV : ∀ v : ↥(V.map φ), φ (eV.symm v : G) = v := coe_equivOfMapEq_symm φ hφ _
  refine ⟨F, inferInstance, inferInstance, hF, α.comp eL.symm.toMonoidHom,
    β.comp eV.symm.toMonoidHom, hαs.comp eL.symm.surjective, fun ℓ => ?_,
    hβs.comp eV.symm.surjective, fun v => ?_, fun a u v hv => ?_, fun ℓ => ?_, fun v => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hαk, ← mem_map_iff φ hφ, hL]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβk, ← mem_map_iff φ hφ, hV,
      map_sp4C φ hφ]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    refine heq _ _ _ (hφ ?_)
    rw [map_mul, map_mul, Subgroup.coe_inv, map_inv, hL, hV, hV, hv, Subgroup.coe_inv]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hS, ← mem_map_iff φ hφ, hL]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hCZ, ← mem_map_iff φ hφ, hV,
      Subgroup.map_sup, map_sp4C φ hφ, map_sp4Z φ hφ]

omit [Finite G] [Finite G'] in
theorem IsNaturalSection.map' {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (GL ι F)}
    (h : IsNaturalSection A V Z (CFSG.pCore 2 ↥A) Γ) :
    IsNaturalSection (A.map φ) (V.map φ) (Z.map φ) (CFSG.pCore 2 ↥(A.map φ)) Γ := by
  obtain ⟨hN, α, hαs, hαk, β, hβs, hβk, heq⟩ := h
  let eA := A.equivMapOfInjective φ hφ
  let eV := V.equivMapOfInjective φ hφ
  have hA : ∀ a : ↥(A.map φ), φ (eA.symm a : G) = a := fun a => by
    conv_rhs => rw [← eA.apply_symm_apply a]
    rfl
  have hV : ∀ v : ↥(V.map φ), φ (eV.symm v : G) = v := fun v => by
    conv_rhs => rw [← eV.apply_symm_apply v]
    rfl
  refine ⟨?_, α.comp eA.symm.toMonoidHom, hαs.comp eA.symm.surjective, ?_,
    β.comp eV.symm.toMonoidHom, hβs.comp eV.symm.surjective, ?_, fun a u v hv => ?_⟩
  · have h1 := map_inf_normalizer φ hφ A V
    rw [inf_eq_left.mpr hN] at h1
    rw [h1]
    exact inf_le_right
  · rw [← MonoidHom.comap_ker, hαk, Subgroup.comap_equiv_eq_map_symm', MulEquiv.symm_symm]
    exact CFSG.pCore_map_iso 2 eA
  · rw [← MonoidHom.comap_ker, hβk, Subgroup.comap_equiv_eq_map_symm', MulEquiv.symm_symm]
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, Subgroup.mem_subgroupOf.mp hv, rfl⟩
    · intro hx
      refine ⟨eV.symm x, Subgroup.mem_subgroupOf.mpr ?_, eV.apply_symm_apply x⟩
      rw [← mem_map_iff φ hφ, hV]
      exact hx
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    refine heq _ _ _ (hφ ?_)
    rw [map_mul, map_mul, Subgroup.coe_inv, map_inv, hA, hV, hV, hv, Subgroup.coe_inv]

omit [Finite G] [Finite G'] in
theorem isCyclic_map {Y : Subgroup G} (h : IsCyclic ↥Y) : IsCyclic ↥(Y.map φ) :=
  isCyclic_of_surjective (Y.equivMapOfInjective φ hφ).toMonoidHom
    (Y.equivMapOfInjective φ hφ).surjective

omit [Finite G] [Finite G'] in
theorem map_le_normalizer {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A.map φ ≤ Subgroup.normalizer (B.map φ : Set G') := by
  have h1 := map_inf_normalizer φ hφ A B
  rw [inf_eq_left.mpr h] at h1
  rw [h1]
  exact inf_le_right

omit [Finite G] [Finite G'] in
theorem map_le_centralizer {A B : Subgroup G} (h : A ≤ Subgroup.centralizer (B : Set G)) :
    A.map φ ≤ Subgroup.centralizer (B.map φ : Set G') := by
  have h1 := map_inf_centralizer φ hφ A B
  rw [inf_eq_left.mpr h] at h1
  rw [h1]
  exact inf_le_right

omit [Finite G] [Finite G'] in
theorem Sp4Torus.map {n : ℕ} {K P C Z K₂ Q₁ : Subgroup G} (h : Sp4Torus n K P C Z K₂ Q₁) :
    Sp4Torus n (K.map φ) (P.map φ) (C.map φ) (Z.map φ) (K₂.map φ) (Q₁.map φ) := by
  obtain ⟨Y₁, Y₂, hY₁N, hY₁P, hY₁c, hY₁card, hreg, hcomm, heq, hY₂, hY₂c, hY₂card, hY₁₂, hNC,
    htr⟩ := h
  refine ⟨Y₁.map φ, Y₂.map φ, ?_, Subgroup.map_mono hY₁P, isCyclic_map φ hφ hY₁c, ?_, ?_, ?_, ?_,
    Subgroup.map_mono hY₂, isCyclic_map φ hφ hY₂c, ?_, ?_, ?_, ?_⟩
  · rw [← map_inf_normalizer φ hφ]
    exact Subgroup.map_mono hY₁N
  · rw [Subgroup.card_map_of_injective hφ]
    exact hY₁card
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
    rcases hreg y hy z hz (hφ (by rw [map_mul, map_mul, map_inv]; exact hyz)) with h1 | h1
    · left
      rw [h1, map_one]
    · right
      rw [h1, map_one]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨k, hk, rfl⟩
    exact ⟨_, hcomm y hy k hk, by simp⟩
  · rw [← map_inf_normalizer φ hφ, heq, Subgroup.map_sup]
  · rw [Subgroup.card_map_of_injective hφ]
    exact hY₂card
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hY₁₂ a ha b hb]
  · rw [← Subgroup.map_sup]
    exact map_le_normalizer φ hφ hNC
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hc1 hc'1
    obtain ⟨y, hy, hyc⟩ := htr c hc c' hc' (fun h => hc1 (by rw [h, map_one]))
      (fun h => hc'1 (by rw [h, map_one]))
    refine ⟨φ y, ?_, by rw [← map_inv, ← map_mul, ← map_mul, hyc]⟩
    rw [← Subgroup.map_sup]
    exact ⟨y, hy, rfl⟩

end L436

open L436

variable {G : Type} [Group G]

variable {G' : Type} [Group G'] (φ : G →* G') (hφ : Function.Injective φ) [Finite G] [Finite G']
include hφ

theorem Sp4ParConcl.map {n : ℕ} {K P S V : Subgroup G} (h : Sp4ParConcl n K P S V) :
    Sp4ParConcl n (K.map φ) (P.map φ) (S.map φ) (V.map φ) where
  V_eq := by
    rw [← map_perfectCore φ P, Lie2Parabolic.pCoreOf_map_of_injective φ hφ, ← h.V_eq]
  V_sq := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, h.V_sq v hv, map_one]
  card_V := by
    rw [Subgroup.card_map_of_injective hφ]
    exact h.card_V
  comm_V := by rw [← map_perfectCore, ← Subgroup.map_commutator, h.comm_V]
  card_C := by
    rw [← L436.map_sp4C φ hφ, Subgroup.card_map_of_injective hφ]
    exact h.card_C
  S_le := by
    rw [← map_perfectCore]
    exact Subgroup.map_mono h.S_le
  S_syl := L436.isSylowTwoOf_map φ hφ h.S_syl
  card_Z := by
    rw [← L436.map_sp4Z φ hφ, Subgroup.card_map_of_injective hφ]
    exact h.card_Z
  C_inf_Z := by
    rw [← L436.map_sp4C φ hφ, ← L436.map_sp4Z φ hφ, ← Subgroup.map_inf_eq _ _ φ hφ, h.C_inf_Z,
      Subgroup.map_bot]
  cent_S := by
    rw [← L436.map_inf_centralizer φ hφ, h.cent_S, Subgroup.map_sup, L436.map_sp4C φ hφ,
      L436.map_sp4Z φ hφ]
  K₂_le := by
    rw [← L436.map_sp4K₂ φ hφ, ← L436.map_sp4Z φ hφ]
    exact L436.map_le_centralizer φ hφ h.K₂_le
  sup_eq := by rw [← map_perfectCore, ← L436.map_sp4K₂ φ hφ, ← Subgroup.map_sup, h.sup_eq]
  V_le_K₂ := by
    rw [← L436.map_sp4K₂ φ hφ]
    exact Subgroup.map_mono h.V_le_K₂
  K₂_closure := by rw [← L436.map_sp4K₂ φ hφ, ← L436.map_conjClosure, h.K₂_closure]
  psl := by
    rw [← L436.map_sp4K₂ φ hφ]
    exact IsPSL.of_mulEquiv (NQCat.modO2Congr ((sp4K₂ K P S V).equivMapOfInjective φ hφ)) h.psl
  natural := by
    obtain ⟨F, _, _, hF, hnat⟩ := h.natural
    refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
    rw [← L436.map_sp4K₂ φ hφ, ← L436.map_sp4Q₁ φ hφ, ← L436.map_sp4Z φ hφ]
    exact L436.IsNaturalSection.map' φ hφ hnat
  Q₁_closure := by
    rw [← L436.map_sp4C φ hφ, ← L436.map_sp4K₂ φ hφ, ← L436.map_sp4Q₁ φ hφ,
      ← L436.map_conjClosure, h.Q₁_closure]
  card_Q₁ := by
    rw [← L436.map_sp4Q₁ φ hφ, Subgroup.card_map_of_injective hφ]
    exact h.card_Q₁
  Q₁_cent := by
    rw [← L436.map_sp4Q₁ φ hφ, ← L436.map_sp4K₂ φ hφ, ← L436.map_inf_centralizer φ hφ, h.Q₁_cent,
      L436.map_sp4Z φ hφ]
  S_eq := by rw [← L436.map_sp4Q₁ φ hφ, ← Subgroup.map_sup, ← h.S_eq]
  V_inf_Q₁ := by
    rw [← L436.map_sp4Q₁ φ hφ, ← Subgroup.map_inf_eq _ _ φ hφ, h.V_inf_Q₁, Subgroup.map_sup,
      L436.map_sp4C φ hφ, L436.map_sp4Z φ hφ]
  V_cent_Q₁ := by
    rw [← L436.map_sp4Q₁ φ hφ, ← L436.map_inf_centralizer φ hφ, h.V_cent_Q₁,
      Subgroup.map_inf_eq _ _ φ hφ]
  Q₁_cent_V := by
    rw [← L436.map_sp4Q₁ φ hφ, ← L436.map_inf_centralizer φ hφ, h.Q₁_cent_V,
      Subgroup.map_inf_eq _ _ φ hφ]
  index_V := by
    rw [← L436.map_sp4Q₁ φ hφ, ← Subgroup.map_inf_eq _ _ φ hφ,
      Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact h.index_V
  index_Q₁ := by
    rw [← L436.map_sp4Q₁ φ hφ, ← Subgroup.map_inf_eq _ _ φ hφ,
      Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact h.index_Q₁
  torus := by
    rw [← L436.map_sp4C φ hφ, ← L436.map_sp4Z φ hφ, ← L436.map_sp4K₂ φ hφ, ← L436.map_sp4Q₁ φ hφ]
    exact L436.Sp4Torus.map φ hφ h.torus
  coord := L436.Sp4Coord.map φ hφ h.coord

end CFSG.Quasithin.H13.Ch4
