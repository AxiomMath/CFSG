module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocal

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

private lemma card_eq_of_regular {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    {ω : Ω} {R : Subgroup X} (hR : R ≤ MulAction.stabilizer X ω)
    (hreg : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β)
    (hω : ∃ ω' : Ω, ω' ≠ ω) : Nat.card Ω = Nat.card R + 1 := by
  classical
  obtain ⟨ω', hω'⟩ := hω
  have hne : ∀ r : R, (r : X) • ω' ≠ ω := by
    intro r hr
    have hrω : (r : X) • ω = ω := hR r.2
    have h1 : ω' = ω := by
      calc ω' = (r : X)⁻¹ • ((r : X) • ω') := (inv_smul_smul (r : X) ω').symm
        _ = (r : X)⁻¹ • ω := by rw [hr]
        _ = ω := by
          conv_lhs => rw [← hrω]
          exact inv_smul_smul (r : X) ω
    exact hω' h1
  have hbij : Function.Bijective
      (fun r : R => (⟨(r : X) • ω', hne r⟩ : {α : Ω // α ≠ ω})) := by
    constructor
    · intro r s hrs
      have h1 : (r : X) • ω' = (s : X) • ω' := congrArg Subtype.val hrs
      have hfix : (((r⁻¹ * s : R) : X)) • ω' = ω' := by
        change ((r : X)⁻¹ * (s : X)) • ω' = ω'
        rw [mul_smul, ← h1, inv_smul_smul]
      have hone : (r⁻¹ * s : R) = 1 :=
        (hreg ω' ω' hω' hω').unique hfix (by simp)
      have h2 : s = r := by
        calc s = r * (r⁻¹ * s) := by group
          _ = r := by rw [hone, mul_one]
      exact h2.symm
    · intro b
      obtain ⟨r, hr, -⟩ := hreg ω' b.1 hω' b.2
      exact ⟨r, Subtype.ext hr⟩
  let e : R ≃ {α : Ω // α ≠ ω} := Equiv.ofBijective _ hbij
  have hcardR : Nat.card R = Nat.card {α : Ω // α ≠ ω} := Nat.card_congr e
  haveI : Finite {α : Ω // α ≠ ω} := Finite.of_injective e.symm e.symm.injective
  have hcardΩ : Nat.card Ω = Nat.card {α : Ω // α ≠ ω} + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe ω)]
    exact Finite.card_option
  omega

structure RankOneRoot (X Ω : Type*) [Group X] [MulAction X Ω] (N : Subgroup X) : Prop where
  le_root : ∀ ω ω' : Ω, ω ≠ ω' → ∀ Q R : Subgroup X, Q ≤ MulAction.stabilizer X ω →
    R ≤ MulAction.stabilizer X ω → (R.subgroupOf (MulAction.stabilizer X ω)).Normal →
    IsPGroup 2 Q → IsPGroup 2 R → (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
    (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', ∀ q ∈ Q,
      t * q * t⁻¹ ∈ Q) → Q ≤ R

structure RankOneCenter (X Ω : Type*) [Group X] [MulAction X Ω] (N : Subgroup X) (e : ℕ) :
    Prop where
  centralizer_le : ∀ (ω : Ω) (R : Subgroup X), R ≤ MulAction.stabilizer X ω →
    (R.subgroupOf (MulAction.stabilizer X ω)).Normal → IsPGroup 2 R →
    (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
    ∀ g ∈ MulAction.stabilizer X ω, (∀ r ∈ R, g * r = r * g) → g ∈ R
  center_le : ∀ (ω ω' : Ω), ω ≠ ω' → ∀ R Z : Subgroup X, R ≤ MulAction.stabilizer X ω →
    (R.subgroupOf (MulAction.stabilizer X ω)).Normal → IsPGroup 2 R →
    (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
    Z ≤ R → (∀ r ∈ R, ∀ y ∈ Z, r * y = y * r) →
    (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', ∀ y ∈ Z,
      t * y * t⁻¹ ∈ Z) → Z ≠ ⊥ →
    ∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ Z
  centralizer_center : ∀ (ω ω' : Ω), ω ≠ ω' → ∀ R : Subgroup X,
    R ≤ MulAction.stabilizer X ω → (R.subgroupOf (MulAction.stabilizer X ω)).Normal →
    IsPGroup 2 R → (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
    ∀ g ∈ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', Odd (orderOf g) →
      (∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → g * y = y * g) → g ^ e = 1

structure RankOneUnitary (X Ω : Type*) [Group X] [MulAction X Ω] (N : Subgroup X) (q : ℕ) :
    Prop where
  fix_two : ∀ ω ω' : Ω, ω ≠ ω' →
    ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', t ^ (q + 1) ≠ 1 →
      ∀ ω'', t • ω'' = ω'' → ω'' = ω ∨ ω'' = ω'
  pow_card : ∀ ω ω' : Ω, ω ≠ ω' →
    ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', t ^ (q ^ 2 - 1) = 1
  exists_pow : ∀ ω ω' : Ω, ω ≠ ω' →
    ∃ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', (t ^ (q + 1)) ^ (q + 1) ≠ 1

structure RankOneTransitive (X Ω : Type*) [Group X] [MulAction X Ω] (N : Subgroup X) : Prop where
  transitive : ∀ ω ω' : Ω, ω ≠ ω' → ∀ P : Subgroup X, P ≤ MulAction.stabilizer X ω →
    IsPGroup 2 P → P ≠ ⊥ →
    (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', ∀ x ∈ P,
      t * x * t⁻¹ ∈ P) →
    ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃ r ∈ P, r • α = β

structure RankOneNonabelian (X Ω : Type*) [Group X] [MulAction X Ω] : Prop where
  not_comm : ∀ (ω : Ω) (R : Subgroup X), R ≤ MulAction.stabilizer X ω →
    (R.subgroupOf (MulAction.stabilizer X ω)).Normal → IsPGroup 2 R →
    (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
    ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a

theorem RankOneRoot.centralizer_le {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω]
    [FaithfulSMul X Ω] {N : Subgroup X} (hA7 : RankOneRoot X Ω N) (ω : Ω) (R : Subgroup X)
    (hR : R ≤ MulAction.stabilizer X ω)
    (hRn : (R.subgroupOf (MulAction.stabilizer X ω)).Normal) (hR2 : IsPGroup 2 R)
    (hreg : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) :
    ∀ g ∈ MulAction.stabilizer X ω, (∀ r ∈ R, g * r = r * g) → g ∈ R := by
  classical
  intro g hg hgcomm
  by_cases hω : ∃ ω' : Ω, ω' ≠ ω
  · obtain ⟨ω', hω'⟩ := hω
    let Gω : Subgroup X := MulAction.stabilizer X ω
    let C : Subgroup X := Subgroup.centralizer (R : Set X) ⊓ Gω
    have hC_le : C ≤ Gω := inf_le_right
    have hCnorm : (C.subgroupOf Gω).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hC_le]
      intro c k hc hk
      refine ⟨?_, ?_⟩
      · change k * c * k⁻¹ ∈ Subgroup.centralizer (R : Set X)
        have hccent : c ∈ Subgroup.centralizer (R : Set X) := hc.1
        rw [Subgroup.mem_centralizer_iff] at hccent ⊢
        intro r hr
        have hkr : k⁻¹ * r * k ∈ R := by
          simpa using
            (Subgroup.normal_subgroupOf_iff hR).mp hRn r k⁻¹ hr (Gω.inv_mem hk)
        have hck := hccent (k⁻¹ * r * k) hkr
        calc r * (k * c * k⁻¹) = k * ((k⁻¹ * r * k) * c) * k⁻¹ := by group
          _ = k * (c * (k⁻¹ * r * k)) * k⁻¹ := by rw [hck]
          _ = (k * c * k⁻¹) * r := by group
      · exact Gω.mul_mem (Gω.mul_mem hk hc.2) (Gω.inv_mem hk)
    have hsem : ∀ c ∈ C, ∀ α : Ω, α ≠ ω → c • α = α → c = 1 := by
      intro c hc α hα hfix
      apply FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
      intro β
      by_cases hβ : β = ω
      · rw [hβ]
        simpa using MulAction.mem_stabilizer_iff.mp hc.2
      · obtain ⟨r, hr, -⟩ := hreg α β hα hβ
        have hmem : c ∈ Subgroup.centralizer (R : Set X) := hc.1
        rw [Subgroup.mem_centralizer_iff] at hmem
        have hcomm : c * (r : X) = (r : X) * c := (hmem (r : X) r.2).symm
        calc c • β = c • ((r : X) • α) := by rw [← hr]
          _ = (c * (r : X)) • α := (mul_smul c (r : X) α).symm
          _ = ((r : X) * c) • α := by rw [hcomm]
          _ = (r : X) • (c • α) := mul_smul (r : X) c α
          _ = (r : X) • α := by rw [hfix]
          _ = β := hr
          _ = (1 : X) • β := by rw [one_smul]
    have hC2 : IsPGroup 2 C := by
      have hne : ∀ c : C, (c : X) • ω' ≠ ω := by
        intro c h
        have hcGω : (c : X) ∈ Gω := hC_le c.2
        have h1 : ω' = ω := by
          calc ω' = (c : X)⁻¹ • ((c : X) • ω') := (inv_smul_smul (c : X) ω').symm
            _ = (c : X)⁻¹ • ω := by rw [h]
            _ = ω := by
              conv_lhs => rw [← hcGω]
              exact inv_smul_smul (c : X) ω
        exact hω' h1
      have hsmul_eq : ∀ (r s : R), (r : X) • ω' = (s : X) • ω' → r = s := by
        intro r s h
        have hfix : (((r⁻¹ * s : R) : X)) • ω' = ω' := by
          change ((r : X)⁻¹ * (s : X)) • ω' = ω'
          rw [mul_smul, ← h, inv_smul_smul]
        have hone : (r⁻¹ * s : R) = 1 :=
          (hreg ω' ω' hω' hω').unique hfix (by simp)
        have h2 : s = r := by
          calc s = r * (r⁻¹ * s) := by group
            _ = r := by rw [hone, mul_one]
        exact h2.symm
      let φ : C → R := fun c => (hreg ω' ((c : X) • ω') hω' (hne c)).choose
      have φ_spec : ∀ c : C, ((φ c : R) : X) • ω' = (c : X) • ω' := fun c =>
        (hreg ω' ((c : X) • ω') hω' (hne c)).choose_spec.1
      have hφmul : ∀ c₁ c₂ : C, φ (c₁ * c₂) = φ c₂ * φ c₁ := by
        intro c₁ c₂
        apply hsmul_eq
        have hcomm : (φ c₂ : X) * (c₁ : X) = (c₁ : X) * (φ c₂ : X) := by
          have hc₁ : (c₁ : X) ∈ Subgroup.centralizer (R : Set X) := c₁.2.1
          rw [Subgroup.mem_centralizer_iff] at hc₁
          exact hc₁ (φ c₂ : X) (φ c₂).2
        calc (((φ (c₁ * c₂) : R) : X)) • ω'
            = ((c₁ : X) * (c₂ : X)) • ω' := by
              simpa [Subgroup.coe_mul] using φ_spec (c₁ * c₂)
          _ = (c₁ : X) • ((c₂ : X) • ω') := mul_smul (c₁ : X) (c₂ : X) ω'
          _ = (c₁ : X) • ((φ c₂ : X) • ω') := by rw [← φ_spec c₂]
          _ = ((c₁ : X) * (φ c₂ : X)) • ω' := (mul_smul (c₁ : X) (φ c₂ : X) ω').symm
          _ = ((φ c₂ : X) * (c₁ : X)) • ω' := by rw [← hcomm]
          _ = (φ c₂ : X) • ((c₁ : X) • ω') := mul_smul (φ c₂ : X) (c₁ : X) ω'
          _ = (φ c₂ : X) • ((φ c₁ : X) • ω') := by rw [← φ_spec c₁]
          _ = ((φ c₂ * φ c₁ : R) : X) • ω' := (mul_smul (φ c₂ : X) (φ c₁ : X) ω').symm
      let ψ : C →* R :=
        { toFun := fun c => (φ c)⁻¹
          map_one' := by
            have h1 : φ 1 = 1 := hsmul_eq (φ 1) 1 (by simpa using φ_spec 1)
            rw [h1, inv_one]
          map_mul' := by
            intro c₁ c₂
            change (φ (c₁ * c₂))⁻¹ = (φ c₁)⁻¹ * (φ c₂)⁻¹
            rw [hφmul c₁ c₂, mul_inv_rev] }
      have hψinj : Function.Injective ψ := by
        intro c₁ c₂ h
        have hφ : φ c₁ = φ c₂ := by
          have h' := congrArg (fun r : R => r⁻¹) h
          simpa [ψ] using h'
        have hsm : (c₁ : X) • ω' = (c₂ : X) • ω' := by
          rw [← φ_spec c₁, ← φ_spec c₂, hφ]
        have hfix : (((c₁⁻¹ * c₂ : C) : X)) • ω' = ω' := by
          change ((c₁ : X)⁻¹ * (c₂ : X)) • ω' = ω'
          rw [mul_smul, ← hsm, inv_smul_smul]
        have hone : (c₁⁻¹ * c₂ : C) = 1 := by
          apply Subtype.ext
          exact hsem ((c₁⁻¹ * c₂ : C) : X) (c₁⁻¹ * c₂).2 ω' hω' hfix
        have h2 : c₂ = c₁ := by
          calc c₂ = c₁ * (c₁⁻¹ * c₂) := by group
            _ = c₁ := by rw [hone, mul_one]
        exact h2.symm
      exact hR2.of_injective ψ hψinj
    have hCn : ∀ t ∈ N ⊓ Gω ⊓ MulAction.stabilizer X ω', ∀ q ∈ C,
        t * q * t⁻¹ ∈ C := by
      intro t ht q hq
      refine ⟨?_, ?_⟩
      · change t * q * t⁻¹ ∈ Subgroup.centralizer (R : Set X)
        have hqcent : q ∈ Subgroup.centralizer (R : Set X) := hq.1
        rw [Subgroup.mem_centralizer_iff] at hqcent ⊢
        intro r hr
        have htr : t⁻¹ * r * t ∈ R := by
          simpa using
            (Subgroup.normal_subgroupOf_iff hR).mp hRn r t⁻¹ hr (Gω.inv_mem ht.1.2)
        have hcomm := hqcent (t⁻¹ * r * t) htr
        calc r * (t * q * t⁻¹) = t * ((t⁻¹ * r * t) * q) * t⁻¹ := by group
          _ = t * (q * (t⁻¹ * r * t)) * t⁻¹ := by rw [hcomm]
          _ = (t * q * t⁻¹) * r := by group
      · exact Gω.mul_mem (Gω.mul_mem ht.1.2 hq.2) (Gω.inv_mem ht.1.2)
    have hC_le_R : C ≤ R := hA7.le_root ω ω' hω'.symm C R hC_le hR hRn hC2 hR2 hreg hCn
    exact hC_le_R ⟨Subgroup.mem_centralizer_iff.mpr (fun r hr => (hgcomm r hr).symm), hg⟩
  · have hsub : Subsingleton Ω := ⟨fun a b => by
      by_cases ha : a = ω
      · by_cases hb : b = ω
        · rw [ha, hb]
        · exact absurd ⟨b, hb⟩ hω
      · exact absurd ⟨a, ha⟩ hω⟩
    have hX : Subsingleton X := ⟨fun a b =>
      FaithfulSMul.eq_of_smul_eq_smul (M := X) (α := Ω)
        (fun x => Subsingleton.elim (a • x) (b • x))⟩
    have hg1 : g = 1 := Subsingleton.elim g 1
    rw [hg1]
    exact R.one_mem

namespace RankOneLocal

theorem rankOneRoot_of_centralizer {X Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω] {N : Subgroup X} (h : RankOneLocal X Ω N)
    (hC : ∀ ω ω' : Ω, ω ≠ ω' → ∀ g ∈ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
      (∃ k : ℕ, g ^ 2 ^ k = 1) →
      (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', g * t = t * g) →
        g = 1) :
    RankOneRoot X Ω N := by
  classical
  have hNnormal : N.Normal := by
    rw [← h.perfectResidual_eq]
    infer_instance
  refine ⟨?le_root⟩
  intro ω ω' hne Q R hQ hR hRn hQ2 hR2 hreg hQn
  let Gω : Subgroup X := MulAction.stabilizer X ω
  let Gω' : Subgroup X := MulAction.stabilizer X ω'
  let T : Subgroup X := N ⊓ Gω ⊓ Gω'
  have hQR2 : IsPGroup 2 ↥(Q ⊔ R : Subgroup X) := by
    refine hQ2.to_sup_of_normal_right' hR2 ?_
    rw [Subgroup.le_normalizer_iff]
    intro q hq r hr
    exact (Subgroup.normal_subgroupOf_iff hR).mp hRn r q hr (hQ hq)
  let Q₁ : Subgroup X := (Q ⊔ R) ⊓ Gω'
  have hQ₁_le : Q₁ ≤ Gω' := inf_le_right
  have hQ₁_le_sup : Q₁ ≤ Q ⊔ R := inf_le_left
  have hQ₁2 : IsPGroup 2 Q₁ := hQR2.to_le hQ₁_le_sup
  have hQ₁_le_Gω : Q₁ ≤ Gω := le_trans hQ₁_le_sup (sup_le hQ hR)
  have hTnormQ : T ≤ Subgroup.normalizer Q := Subgroup.le_normalizer_iff.mpr hQn
  have hTnormR : T ≤ Subgroup.normalizer R := by
    rw [Subgroup.le_normalizer_iff]
    intro t ht r hr
    exact (Subgroup.normal_subgroupOf_iff hR).mp hRn r t hr ht.1.2
  have hTnormal : ∀ t ∈ T, ∀ g ∈ Gω ⊓ Gω', g * t * g⁻¹ ∈ T := by
    intro t ht g hg
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hNnormal.conj_mem t ht.1.1 g
    · exact Gω.mul_mem (Gω.mul_mem hg.1 ht.1.2) (Gω.inv_mem hg.1)
    · exact Gω'.mul_mem (Gω'.mul_mem hg.2 ht.2) (Gω'.inv_mem hg.2)
  have hQ₁n : ∀ t ∈ T, ∀ q ∈ Q₁, t * q * t⁻¹ ∈ Q₁ := by
    intro t ht q hq
    have hTnormSup : T ≤ Subgroup.normalizer ((Q ⊔ R : Subgroup X) : Set X) :=
      le_trans (le_inf hTnormQ hTnormR)
        (Subgroup.inf_normalizer_le_normalizer_sup Q R)
    refine ⟨(Subgroup.le_normalizer_iff.mp hTnormSup) t ht q hq.1, ?_⟩
    exact Gω'.mul_mem (Gω'.mul_mem ht.2 hq.2) (Gω'.inv_mem ht.2)
  have hcop : Nat.Coprime (Nat.card Q₁) (Nat.card T) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hQ₁2.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_left.mpr
      (by simpa [T, Gω, Gω'] using h.torus_odd ω ω' hne)).pow_left k
  have hdisj : Disjoint T Q₁ := Subgroup.disjoint_of_coprime_natCard hcop.symm
  have hcomm : ∀ t ∈ T, ∀ q ∈ Q₁, q * t = t * q := by
    intro t ht q hq
    have htGω : t ∈ Gω := ht.1.2
    have htGω' : t ∈ Gω' := ht.2
    have hqGω : q ∈ Gω := hQ₁_le_Gω hq
    have hqGω' : q ∈ Gω' := hq.2
    have hcommT : t * q * t⁻¹ * q⁻¹ ∈ T := by
      have hconj : q * t⁻¹ * q⁻¹ ∈ T :=
        hTnormal t⁻¹ (T.inv_mem ht) q ⟨hqGω, hqGω'⟩
      have h1 : t * q * t⁻¹ * q⁻¹ = t * (q * t⁻¹ * q⁻¹) := by group
      rw [h1]
      exact T.mul_mem ht hconj
    have hcommQ₁ : t * q * t⁻¹ * q⁻¹ ∈ Q₁ :=
      Q₁.mul_mem (hQ₁n t ht q hq) (Q₁.inv_mem hq)
    have hbot : t * q * t⁻¹ * q⁻¹ ∈ (⊥ : Subgroup X) := by
      rw [← disjoint_iff.mp hdisj]
      exact ⟨hcommT, hcommQ₁⟩
    rw [Subgroup.mem_bot] at hbot
    have hconj : t * q * t⁻¹ = q := by
      calc t * q * t⁻¹ = (t * q * t⁻¹ * q⁻¹) * q := by group
        _ = 1 * q := by rw [hbot]
        _ = q := one_mul q
    have h1 : t * q = q * t := by
      calc t * q = (t * q * t⁻¹) * t := by group
        _ = q * t := by rw [hconj]
    exact h1.symm
  have hQ₁bot : Q₁ = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_bot]
    have hq2 : ∃ k : ℕ, q ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hQ₁2 ⟨q, hq⟩
      exact ⟨k, by simpa using congrArg (fun x : ↥Q₁ => (x : X)) hk⟩
    exact hC ω ω' hne q ⟨hQ₁_le_Gω hq, hq.2⟩ hq2
      (fun t ht => hcomm t ht q hq)
  intro q hq
  have hqω' : q • ω' ≠ ω := by
    intro hqω
    have hqGω : q ∈ Gω := hQ hq
    have h1 : ω' = ω := by
      calc ω' = q⁻¹ • (q • ω') := (inv_smul_smul q ω').symm
        _ = q⁻¹ • ω := by rw [hqω]
        _ = ω := by
          conv_lhs => rw [← hqGω]
          exact inv_smul_smul q ω
    exact hne h1.symm
  obtain ⟨r, hr, -⟩ := hreg ω' (q • ω') hne.symm hqω'
  have hmemQ₁ : (r : X)⁻¹ * q ∈ Q₁ := by
    refine ⟨?_, ?_⟩
    · exact (Q ⊔ R).mul_mem (Subgroup.mem_sup_right (R.inv_mem r.2))
        (Subgroup.mem_sup_left hq)
    · change ((r : X)⁻¹ * q) • ω' = ω'
      rw [mul_smul, ← hr, inv_smul_smul]
  have hone : (r : X)⁻¹ * q = 1 := by
    have h1 : ((r : X)⁻¹ * q) ∈ (⊥ : Subgroup X) := hQ₁bot ▸ hmemQ₁
    rwa [Subgroup.mem_bot] at h1
  have hqeq : q = (r : X) := by
    calc q = (r : X) * ((r : X)⁻¹ * q) := by group
      _ = (r : X) * 1 := by rw [hone]
      _ = (r : X) := mul_one _
  rw [hqeq]
  exact r.2

theorem rankOneRoot_of_zassenhaus {X Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω] {N : Subgroup X} (h : RankOneLocal X Ω N) (hZ : RankOneZassenhaus X Ω N) :
    RankOneRoot X Ω N := by
  classical
  refine h.rankOneRoot_of_centralizer ?_
  intro ω ω' hne g hg hg2 hgt
  have hgN : g ∈ N := hZ.centralizer_le ω ω' hne g hg hgt
  have hgT : g ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω' :=
    ⟨⟨hgN, hg.1⟩, hg.2⟩
  have hodd : Odd (orderOf g) :=
    (h.torus_odd ω ω' hne).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hgT)
  obtain ⟨k, hk⟩ := hg2
  have hdvd : orderOf g ∣ 2 ^ k := (orderOf_dvd_iff_pow_eq_one).mpr hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓
      MulAction.stabilizer X ω')) :=
    (Nat.coprime_two_left.mpr (h.torus_odd ω ω' hne)).pow_left k
  have hone : orderOf g = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd (Subgroup.orderOf_dvd_natCard _ hgT)
  exact orderOf_eq_one_iff.mp hone

theorem rankOneTransitive_of_zassenhaus {X Ω : Type*} [Group X] [Finite X]
    [MulAction X Ω] [FaithfulSMul X Ω] {N : Subgroup X}
    (h : RankOneLocal X Ω N) (hZ : RankOneZassenhaus X Ω N)
    (hcard : ∀ ω ω' : Ω, ω ≠ ω' →
      Nat.card Ω = Nat.card ↥(N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω') + 2) :
    RankOneTransitive X Ω N := by
  classical
  refine ⟨?transitive⟩
  intro ω ω' hne P hP hP2 hPne hPn α β hα hβ
  obtain ⟨R, hR, hRn, hR2, hreg⟩ := h.root ω
  have hA7 : RankOneRoot X Ω N := h.rankOneRoot_of_zassenhaus hZ
  have hPleR : P ≤ R := hA7.le_root ω ω' hne P R hP hR hRn hP2 hR2 hreg hPn
  let T : Subgroup X := N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
  have hcardΩ : Nat.card Ω = Nat.card R + 1 :=
    card_eq_of_regular hR hreg ⟨ω', hne.symm⟩
  have hcardR : Nat.card R = Nat.card T + 1 := by
    have hT := hcard ω ω' hne
    have hT' : Nat.card Ω = Nat.card T + 2 := by simpa [T] using hT
    omega
  obtain ⟨p₀, hp₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hp₀P : (p₀ : X) ∈ P := p₀.2
  have hp₀R : (p₀ : X) ∈ R := hPleR hp₀P
  have hp₀neX : (p₀ : X) ≠ 1 := fun h1 => hp₀ne (Subtype.ext h1)
  have hconj_mem : ∀ t : T, (t : X) * (p₀ : X) * (t : X)⁻¹ ∈ R := by
    intro t
    exact (Subgroup.normal_subgroupOf_iff hR).mp hRn (p₀ : X) (t : X) hp₀R t.2.1.2
  have hconj_ne : ∀ t : T, (t : X) * (p₀ : X) * (t : X)⁻¹ ≠ 1 := by
    intro t h1
    apply hp₀neX
    calc (p₀ : X) = (t : X)⁻¹ * ((t : X) * (p₀ : X) * (t : X)⁻¹) * (t : X) := by group
      _ = 1 := by rw [h1]; group
  let F : T → {r : R // r ≠ 1} := fun t =>
    ⟨⟨(t : X) * (p₀ : X) * (t : X)⁻¹, hconj_mem t⟩, by
      intro h1
      exact hconj_ne t (congrArg Subtype.val h1)⟩
  have hSubCard : Nat.card {r : R // r ≠ 1} = Nat.card T := by
    haveI : Fintype R := Fintype.ofFinite R
    have h1 : Nat.card {r : R // r ≠ 1} = Nat.card R - 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl (fun r : R => r = 1)]
      simp
    omega
  have hFinj : Function.Injective F := by
    intro t₁ t₂ h
    have hconj : (t₁ : X) * (p₀ : X) * (t₁ : X)⁻¹ =
        (t₂ : X) * (p₀ : X) * (t₂ : X)⁻¹ :=
      congrArg (fun r : {r : R // r ≠ 1} => ((r : R) : X)) h
    by_contra hneq
    have hu_ne : (t₂⁻¹ * t₁ : T) ≠ 1 := by
      intro hu
      apply hneq
      calc t₁ = t₂ * (t₂⁻¹ * t₁) := by group
        _ = t₂ * 1 := by rw [hu]
        _ = t₂ := mul_one t₂
    have hu_neX : ((t₂⁻¹ * t₁ : T) : X) ≠ 1 := fun h1 => hu_ne (Subtype.ext h1)
    have hcommX : (t₂ : X)⁻¹ * (t₁ : X) * (p₀ : X) =
        (p₀ : X) * ((t₂ : X)⁻¹ * (t₁ : X)) := by
      have h1 : (t₂ : X)⁻¹ * (t₁ : X) * (p₀ : X) *
          ((t₂ : X)⁻¹ * (t₁ : X))⁻¹ = (p₀ : X) := by
        calc (t₂ : X)⁻¹ * (t₁ : X) * (p₀ : X) * ((t₂ : X)⁻¹ * (t₁ : X))⁻¹
            = (t₂ : X)⁻¹ * ((t₁ : X) * (p₀ : X) * (t₁ : X)⁻¹) * (t₂ : X) := by group
          _ = (t₂ : X)⁻¹ * ((t₂ : X) * (p₀ : X) * (t₂ : X)⁻¹) * (t₂ : X) := by rw [hconj]
          _ = (p₀ : X) := by group
      calc (t₂ : X)⁻¹ * (t₁ : X) * (p₀ : X)
          = ((t₂ : X)⁻¹ * (t₁ : X) * (p₀ : X) * ((t₂ : X)⁻¹ * (t₁ : X))⁻¹) *
              ((t₂ : X)⁻¹ * (t₁ : X)) := by group
        _ = (p₀ : X) * ((t₂ : X)⁻¹ * (t₁ : X)) := by rw [h1]
    have hcomm : ((t₂⁻¹ * t₁ : T) : X) * (p₀ : X) =
        (p₀ : X) * ((t₂⁻¹ * t₁ : T) : X) := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hcommX
    have hp₀ω'_ne_ω : (p₀ : X) • ω' ≠ ω := by
      intro h1
      have hp₀ω : (p₀ : X) • ω = ω := hR hp₀R
      have h2 : ω' = ω := by
        calc ω' = (p₀ : X)⁻¹ • ((p₀ : X) • ω') := (inv_smul_smul (p₀ : X) ω').symm
          _ = (p₀ : X)⁻¹ • ω := by rw [h1]
          _ = ω := by
            conv_lhs => rw [← hp₀ω]
            exact inv_smul_smul (p₀ : X) ω
      exact hne h2.symm
    have hp₀ω'_ne_ω' : (p₀ : X) • ω' ≠ ω' := by
      intro h1
      have h2 : (⟨(p₀ : X), hp₀R⟩ : R) = 1 := by
        apply (hreg ω' ω' hne.symm hne.symm).unique
        · show ((⟨(p₀ : X), hp₀R⟩ : R) : X) • ω' = ω'
          simpa using h1
        · simp
      have h3 : (p₀ : X) = 1 := congrArg Subtype.val h2
      exact hp₀neX h3
    have hfix : ((t₂⁻¹ * t₁ : T) : X) • ((p₀ : X) • ω') = (p₀ : X) • ω' := by
      rw [← mul_smul, hcomm, mul_smul]
      congr 1
      exact MulAction.mem_stabilizer_iff.mp (t₂⁻¹ * t₁ : T).2.2
    rcases hZ.fix_two ω ω' hne ((t₂⁻¹ * t₁ : T) : X) (t₂⁻¹ * t₁ : T).2 hu_neX
      ((p₀ : X) • ω') hfix with h2 | h2
    · exact hp₀ω'_ne_ω h2
    · exact hp₀ω'_ne_ω' h2
  have hFsurj : Function.Surjective F := by
    have hbij : Function.Bijective F :=
      (Nat.bijective_iff_injective_and_card F).mpr ⟨hFinj, hSubCard.symm⟩
    exact hbij.2
  obtain ⟨r₀, hr₀, -⟩ := hreg α β hα hβ
  have hr₀P : (r₀ : X) ∈ P := by
    by_cases hr₀1 : r₀ = 1
    · rw [hr₀1]
      exact P.one_mem
    · obtain ⟨t, ht⟩ := hFsurj ⟨r₀, hr₀1⟩
      have hconj : (t : X) * (p₀ : X) * (t : X)⁻¹ = (r₀ : X) := by
        simpa [F] using congrArg (fun r : {r : R // r ≠ 1} => ((r : R) : X)) ht
      rw [← hconj]
      exact hPn t t.2 (p₀ : X) hp₀P
  exact ⟨(r₀ : X), hr₀P, hr₀⟩

end RankOneLocal

end CFSG.Quasithin.Stroth.WeissDelta
