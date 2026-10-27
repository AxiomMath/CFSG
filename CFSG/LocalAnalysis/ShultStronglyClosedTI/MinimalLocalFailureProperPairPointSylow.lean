module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryEmbedding

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

theorem card_sylow_eq_of_mulEquiv {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A']
    {p : ℕ} [Fact p.Prime] (e : A ≃* A') (S : Sylow p A) (S' : Sylow p A') :
    Nat.card S = Nat.card S' := by
  rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]

variable {G : Type} [Group G] [Finite G]

theorem aligned_point_sylow (H K B : Subgroup G) {P Ω : Type*} [Group P] [Finite P]
    [MulAction P Ω] (ψ : K ≃* P) {a₀ : Ω} {U T₀ : Subgroup P}
    (hsup : U ⊔ T₀ = MulAction.stabilizer P a₀)
    (hnormU : MulAction.stabilizer P a₀ ≤ Subgroup.normalizer (U : Set P))
    (hinf : U ⊓ T₀ = ⊥) (hsyl : ∃ S : Sylow 2 P, (S : Subgroup P) = U)
    (hψ₀ : (H.subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₀)
    (hψB : (B.subgroupOf K).map ψ.toMonoidHom = T₀) :
    let T := (U.comap ψ.toMonoidHom).map K.subtype
    T ≤ H ⊓ K ∧ Nat.card T = Nat.card U ∧ IsPGroup 2 T ∧
      H ⊓ K = T ⊔ (B ⊓ K) ∧ T ⊓ (B ⊓ K) = ⊥ ∧ (T.subgroupOf (H ⊓ K)).Normal ∧
      ∀ S : Sylow 2 ↥(H ⊓ K), (S : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype = T := by
  intro T
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' := U.comap ψ.toMonoidHom with hT'
  have hmapT' : T'.map ψ.toMonoidHom = U :=
    Subgroup.map_comap_eq_self_of_surjective ψ.surjective U
  have hUstab : U ≤ MulAction.stabilizer P a₀ := hsup ▸ le_sup_left
  have hcardT : Nat.card T = Nat.card U := by
    have hc : Nat.card (T'.map ψ.toMonoidHom) = Nat.card T' :=
      Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective
    rw [hmapT'] at hc
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hc.symm
  obtain ⟨S₀, hS₀⟩ := hsyl
  have hUp : IsPGroup 2 U := hS₀ ▸ S₀.isPGroup'
  have hTp : IsPGroup 2 T := by
    obtain ⟨n, hn⟩ := hUp.exists_card_eq
    exact IsPGroup.of_card (hcardT.trans hn)
  have hHK : H.subgroupOf K = T' ⊔ B.subgroupOf K := by
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [Subgroup.map_sup, hmapT', hψB, hψ₀, hsup]
  have hinf' : T' ⊓ B.subgroupOf K = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ (f := ψ.toMonoidHom) ψ.injective).mp
    rw [Subgroup.map_inf _ _ _ ψ.injective, hmapT', hψB, hinf]
  have hBK : (B.subgroupOf K).map K.subtype = B ⊓ K := Subgroup.subgroupOf_map_subtype B K
  have hsupG : H ⊓ K = T ⊔ (B ⊓ K) := by
    rw [← Subgroup.subgroupOf_map_subtype H K, hHK, Subgroup.map_sup, hBK]
  have hinfG : T ⊓ (B ⊓ K) = ⊥ := by
    rw [← hBK, ← Subgroup.map_inf _ _ _ K.subtype_injective, hinf', Subgroup.map_bot]
  have hTM : T ≤ H ⊓ K := hsupG ▸ le_sup_left
  have hnormal : (T.subgroupOf (H ⊓ K)).Normal := by
    constructor
    intro n hn g
    obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
    have hgK : (g : G) ∈ K := g.2.2
    let g' : K := ⟨g, hgK⟩
    have hg'H : g' ∈ H.subgroupOf K := g.2.1
    have hψg : ψ g' ∈ MulAction.stabilizer P a₀ := by
      rw [← hψ₀]
      exact Subgroup.mem_map_of_mem _ hg'H
    have hconj : ψ (g' * y * g'⁻¹) ∈ U := by
      rw [map_mul, map_mul, map_inv]
      exact ((Subgroup.mem_normalizer_iff.mp (hnormU hψg)) (ψ y)).mp hy
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.mpr ⟨g' * y * g'⁻¹, hconj, ?_⟩
    simp only [g', Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hyn]
    rfl
  refine ⟨hTM, hcardT, hTp, hsupG, hinfG, hnormal, fun S => ?_⟩
  have hTp' : IsPGroup 2 (T.subgroupOf (H ⊓ K)) :=
    hTp.comap_of_injective _ (H ⊓ K).subtype_injective
  have hTS : T.subgroupOf (H ⊓ K) ≤ S := hTp'.le_sylow_of_normal S
  have hTle : T ≤ (S : Subgroup ↥(H ⊓ K)).map (H ⊓ K).subtype := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTM hx⟩, hTS hx, rfl⟩
  let ι := Subgroup.inclusion (inf_le_right : H ⊓ K ≤ K)
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective _
  obtain ⟨R, hR⟩ := (S.isPGroup'.map ι).exists_le_sylow
  have hSR : Nat.card S ≤ Nat.card R := by
    rw [← Subgroup.card_map_of_injective hιinj]
    exact Subgroup.card_le_of_le hR
  have hRU : Nat.card R = Nat.card U := by
    rw [card_sylow_eq_of_mulEquiv ψ R S₀, hS₀]
  symm
  apply Subgroup.eq_of_le_of_card_ge hTle
  rw [Subgroup.card_map_of_injective (H ⊓ K).subtype_injective, hcardT, ← hRU]
  exact hSR

omit [Finite G] in
theorem aligned_point_regular (H K : Subgroup G) {P Ω : Type*} [Group P] [MulAction P Ω]
    (ψ : K ≃* P) {a₀ : Ω} {U : Subgroup P}
    (hreg : ∀ x y : Ω, x ≠ a₀ → y ≠ a₀ → ∃! g : U, (g : P) • x = y)
    (f : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} ≃ Ω)
    (hfeq : ∀ (x : K) (ω ω' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}),
      (ω' : rightCosetSpace H) = rightCosetTranslate H ω x → f ω' = (ψ x)⁻¹ • f ω)
    (hfα : ∀ ω : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
      (ω : rightCosetSpace H) = rightCosetMk H 1 → f ω = a₀) :
    ∀ ω ∈ {ω : rightCosetSpace H | ∃ x ∈ K, rightCosetMk H x = ω},
    ∀ ω' ∈ {ω : rightCosetSpace H | ∃ x ∈ K, rightCosetMk H x = ω},
      ω ≠ rightCosetMk H 1 → ω' ≠ rightCosetMk H 1 →
        ∃! s : (U.comap ψ.toMonoidHom).map K.subtype, rightCosetTranslate H ω (s : G) = ω' := by
  intro ω hω ω' hω' hωα hω'α
  let o : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} := ⟨ω, hω⟩
  let o' : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} := ⟨ω', hω'⟩
  let o₀ : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} :=
    ⟨rightCosetMk H 1, 1, K.one_mem, rfl⟩
  have hf₀ : f o₀ = a₀ := hfα o₀ rfl
  have hne : ∀ o₁ : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω},
      (o₁ : rightCosetSpace H) ≠ rightCosetMk H 1 → f o₁ ≠ a₀ := fun o₁ h₁ heq =>
    h₁ (congrArg Subtype.val (f.injective (heq.trans hf₀.symm)))
  obtain ⟨g, hg, hguniq⟩ := hreg (f o) (f o') (hne o hωα) (hne o' hω'α)
  obtain ⟨x₁, hx₁K, hx₁⟩ := hω
  let s₀ : K := ψ.symm (g : P)⁻¹
  have hs₀ : s₀ ∈ U.comap ψ.toMonoidHom := by
    change ψ (ψ.symm (g : P)⁻¹) ∈ U
    rw [MulEquiv.apply_symm_apply]
    exact inv_mem g.2
  have hmove : ∀ y : K, y ∈ U.comap ψ.toMonoidHom →
      (rightCosetTranslate H ω (y : G) = ω' ↔ y = s₀) := by
    intro y hy
    have hmemo : ∃ x ∈ K, rightCosetMk H x = rightCosetTranslate H ω (y : G) :=
      ⟨x₁ * y, K.mul_mem hx₁K y.2, by rw [← hx₁, rightCosetTranslate_mk]⟩
    let oy : {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω} := ⟨_, hmemo⟩
    have hfy : f oy = (ψ y)⁻¹ • f o := hfeq y o oy rfl
    have hyU : (ψ y)⁻¹ ∈ U := inv_mem hy
    constructor
    · intro hyω
      have hoy : oy = o' := Subtype.ext hyω
      have h1 := hguniq ⟨(ψ y)⁻¹, hyU⟩ (by
        change (ψ y)⁻¹ • f o = f o'
        rw [← hfy, hoy])
      have h2 : (ψ y)⁻¹ = (g : P) := congrArg Subtype.val h1
      apply ψ.injective
      rw [MulEquiv.apply_symm_apply, ← h2, inv_inv]
    · intro hys
      have h2 : (ψ y)⁻¹ = (g : P) := by rw [hys, MulEquiv.apply_symm_apply, inv_inv]
      have : f oy = f o' := by rw [hfy, h2, hg]
      exact congrArg Subtype.val (f.injective this)
  refine ⟨⟨(s₀ : G), Subgroup.mem_map_of_mem _ hs₀⟩, (hmove s₀ hs₀).mpr rfl, ?_⟩
  rintro ⟨s, hs⟩ hsω
  obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp hs
  have hsy : s = (y : G) := hys.symm
  subst hsy
  have := (hmove y hy).mp hsω
  apply Subtype.ext
  change (y : G) = (s₀ : G)
  rw [this]

end CFSG.ShultStronglyClosedTI.ProperPairModel
