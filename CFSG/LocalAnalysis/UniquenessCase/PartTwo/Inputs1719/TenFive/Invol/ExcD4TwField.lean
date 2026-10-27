module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeis
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

private def d4i2 : Fin TwistTag.D4.tag.rank := ⟨2, by decide⟩

private def d4E2 : Fin TwistTag.D4.tag.rank → ℤ := Pi.single d4i2 1

private def d4Beta : Fin TwistTag.D4.tag.rank → ℤ := fun _ => 1

private def d4Gamma : Fin TwistTag.D4.tag.rank → ℤ := d4E2 + d4Beta

private lemma isRoot_d4E2 : IsRoot TwistTag.D4.tag d4E2 := by
  rw [isRoot_iff_mem_artifactRoots]
  decide

private lemma isRoot_d4Beta : IsRoot TwistTag.D4.tag d4Beta := by
  rw [isRoot_iff_mem_artifactRoots]
  decide

private lemma isRoot_d4Gamma : IsRoot TwistTag.D4.tag d4Gamma := by
  rw [isRoot_iff_mem_artifactRoots]
  decide

private lemma not_isRoot_d4Gamma_add_e2 :
    ¬ IsRoot TwistTag.D4.tag (d4Gamma + d4E2) := by
  rw [isRoot_iff_mem_artifactRoots]
  decide

private lemma not_isRoot_d4Gamma_add_beta :
    ¬ IsRoot TwistTag.D4.tag (d4Gamma + d4Beta) := by
  rw [isRoot_iff_mem_artifactRoots]
  decide

private lemma permLattice_d4E2 : permLattice TwistTag.D4.perm d4E2 = d4E2 := by
  ext i
  fin_cases i <;> rfl

private lemma permLattice_d4Beta : permLattice TwistTag.D4.perm d4Beta = d4Beta := by
  ext i
  fin_cases i <;> rfl

private lemma permLattice_d4Gamma : permLattice TwistTag.D4.perm d4Gamma = d4Gamma := by
  ext i
  fin_cases i <;> rfl

private lemma d4E2_ne_d4Beta : d4E2 ≠ d4Beta := by decide

private lemma d4E2_ne_neg_d4Beta : d4E2 ≠ -d4Beta := by decide

private lemma d4Gamma_ne_d4E2 : d4Gamma ≠ d4E2 := by decide

private lemma d4Gamma_ne_neg_d4E2 : d4Gamma ≠ -d4E2 := by decide

private lemma d4Gamma_ne_d4Beta : d4Gamma ≠ d4Beta := by decide

private lemma d4Gamma_ne_neg_d4Beta : d4Gamma ≠ -d4Beta := by decide

private lemma exists_pow_div_two_ne_self {F : Type*} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (hf : 1 ≤ f) (hfe : Even f) :
    ∃ c : F, c ^ (p ^ (f / 2)) ≠ c := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨k, hk⟩ := hfe
  have hf2eq : f / 2 = k := by omega
  have hkpos : 0 < k := by omega
  set r := p ^ (f / 2) with hr
  have hr2 : 2 ≤ r := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle := le_self_pow (by omega : 1 ≤ p) (by omega : f / 2 ≠ 0)
    omega
  have hrlt : r < p ^ f := by
    rw [hr]
    exact pow_lt_pow_right₀ hp.one_lt (by omega)
  have hdeg : (Polynomial.X ^ r - Polynomial.X : Polynomial F).natDegree = r := by
    have := FiniteField.X_pow_card_pow_sub_X_natDegree_eq F (by omega : f / 2 ≠ 0) hp.one_lt
    simpa [hr] using this
  have hne : (Polynomial.X ^ r - Polynomial.X : Polynomial F) ≠ 0 := by
    have := FiniteField.X_pow_card_pow_sub_X_ne_zero F (by omega : f / 2 ≠ 0) hp.one_lt
    simpa [hr] using this
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ r - Polynomial.X : Polynomial F).roots := by
    intro x _
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [h x, sub_self]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at hcard
  have huniv : (Finset.univ : Finset F).card = p ^ f := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
  rw [huniv] at hcard
  omega

private lemma d4_field_charP {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) : CharP K p := by
  have hq3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (by omega) hq3

private lemma d4_field_sigma_cube {p f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ∀ c, σ (σ (σ c)) = c := by
  have : Fintype K := Fintype.ofFinite K
  intro c
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
  have hexp : p ^ f * (p ^ f * p ^ f) = Nat.card K := by rw [hK]; ring
  rw [hexp]
  simp [Nat.card_eq_fintype_card]

private lemma d4_field_delta_square {p f : ℕ} (hfe : Even f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3)
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ (3 * f / 2))) :
    ∀ c, δ (δ c) = c := by
  have : Fintype K := Fintype.ofFinite K
  intro c
  rw [hδ, hδ, ← pow_mul, ← pow_add]
  have h3f2 : 3 * f / 2 + 3 * f / 2 = 3 * f := by
    obtain ⟨k, rfl⟩ := hfe
    omega
  have hq3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  rw [h3f2, ← hq3]
  simp [Nat.card_eq_fintype_card]

private lemma d4_field_sigma_delta {p f : ℕ}
    {K : Type} [Field K] (σ δ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hδ : ∀ c, δ c = c ^ (p ^ (3 * f / 2))) :
    ∀ c, σ (δ c) = δ (σ c) := by
  intro c
  rw [hσ, hδ, hδ, hσ, ← pow_mul, ← pow_mul, mul_comm]

private lemma d4_field_embedding {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) [Fact p.Prime]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    ∃ ι₀ : GaloisField p f →+* K, Function.Injective ι₀ ∧ ∀ a, σ (ι₀ a) = ι₀ a := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := d4_field_charP hp hf hK
  have hq3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  let K₀ := GaloisField p f
  let : Algebra (ZMod p) K₀ := instAlgebraZModGaloisField p f
  have : Fintype K₀ := Fintype.ofFinite K₀
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have hK₀card : Nat.card K₀ = p ^ f := GaloisField.card p f (by omega)
  have hfinK : Module.finrank (ZMod p) K = 3 * f := by
    have hpow : p ^ Module.finrank (ZMod p) K = p ^ (3 * f) := by
      rw [FiniteField.pow_finrank_eq_natCard p K, hq3]
    exact Nat.pow_right_injective hp.two_le hpow
  have hfinK₀ : Module.finrank (ZMod p) K₀ = f := by
    have hpow : p ^ Module.finrank (ZMod p) K₀ = p ^ f := by
      rw [FiniteField.pow_finrank_eq_natCard p K₀, hK₀card]
    exact Nat.pow_right_injective hp.two_le hpow
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := K₀) (L := K)
    (by rw [hfinK₀, hfinK]; exact dvd_mul_left f 3)
  let ι₀ : K₀ →+* K := φ.toRingHom
  have hι₀inj : Function.Injective ι₀ := fun a b h => φ.injective h
  refine ⟨ι₀, hι₀inj, ?_⟩
  intro a
  rw [hσ, ← map_pow]
  have ha : a ^ (p ^ f) = a := by
    rw [← GaloisField.card p f (by omega)]
    simp [Nat.card_eq_fintype_card]
  rw [ha]

private lemma d4_field_exists_lambda {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hfe : Even f) [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ (3 * f / 2))) :
    ∃ lam : K, σ lam = lam ∧ lam ≠ 0 ∧ δ lam = -lam := by
  classical
  have : CharP K p := d4_field_charP hp hf hK
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  obtain ⟨ι₀, hι₀inj, hι₀fix⟩ := d4_field_embedding hp hf hK σ hσ
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨c₀, hc₀⟩ := exists_pow_div_two_ne_self hp hp2 hF hf hfe
  let lam : K := ι₀ c₀ - δ (ι₀ c₀)
  have hδι : ∀ a : GaloisField p f, δ (ι₀ a) = ι₀ (a ^ (p ^ (f / 2))) := by
    intro a
    rw [hδ, ← map_pow]
    congr 1
    have ha : a ^ (p ^ f) = a := by
      rw [← GaloisField.card p f (by omega)]
      simp [Nat.card_eq_fintype_card]
    have hexp : 3 * f / 2 = f + f / 2 := by
      obtain ⟨k, rfl⟩ := hfe
      omega
    calc a ^ (p ^ (3 * f / 2)) = a ^ (p ^ (f + f / 2)) := by rw [hexp]
      _ = a ^ (p ^ f * p ^ (f / 2)) := by rw [pow_add]
      _ = (a ^ (p ^ f)) ^ (p ^ (f / 2)) := by rw [pow_mul]
      _ = a ^ (p ^ (f / 2)) := by rw [ha]
  have hσδ := d4_field_sigma_delta σ δ hσ hδ
  have hσlam : σ lam = lam := by
    change σ (ι₀ c₀ - δ (ι₀ c₀)) = ι₀ c₀ - δ (ι₀ c₀)
    rw [map_sub, hι₀fix, hσδ, hι₀fix]
  have hlam_ne : lam ≠ 0 := by
    intro h
    have hι : ι₀ c₀ = δ (ι₀ c₀) := sub_eq_zero.mp h
    rw [hδι c₀] at hι
    exact hc₀ (hι₀inj hι).symm
  have hδlam : δ lam = -lam := by
    have hδ2 := d4_field_delta_square hfe hK δ hδ
    change δ (ι₀ c₀ - δ (ι₀ c₀)) = -(ι₀ c₀ - δ (ι₀ c₀))
    rw [map_sub, hδ2]
    ring
  exact ⟨lam, hσlam, hlam_ne, hδlam⟩


private lemma diagramMap_conj_pinnedX_fixed {K : Type} [Field K]
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α)
    (hρα : permLattice TwistTag.D4.perm α = α) (c : K) :
    diagramMap TwistTag.D4 K * pinnedX TwistTag.D4.tag K α c *
      (diagramMap TwistTag.D4 K)⁻¹ = pinnedX TwistTag.D4.tag K α c := by
  obtain ⟨ε, hε2, hεc⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hα
  have hfx : ∀ c, diagramMap TwistTag.D4 K * pinnedX TwistTag.D4.tag K α c *
      (diagramMap TwistTag.D4 K)⁻¹ = pinnedX TwistTag.D4.tag K α (ε * c) := by
    intro c
    rw [hεc c, hρα]
  have hP3 : diagramMap TwistTag.D4 K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hXeq : pinnedX TwistTag.D4.tag K α 1 = pinnedX TwistTag.D4.tag K α (ε ^ 3) := by
    calc pinnedX TwistTag.D4.tag K α 1
        = diagramMap TwistTag.D4 K ^ 3 * pinnedX TwistTag.D4.tag K α 1 *
            (diagramMap TwistTag.D4 K ^ 3)⁻¹ := by rw [hP3, inv_one, one_mul, mul_one]
      _ = diagramMap TwistTag.D4 K * (diagramMap TwistTag.D4 K *
            (diagramMap TwistTag.D4 K * pinnedX TwistTag.D4.tag K α 1 *
              (diagramMap TwistTag.D4 K)⁻¹) * (diagramMap TwistTag.D4 K)⁻¹) *
            (diagramMap TwistTag.D4 K)⁻¹ := by
                rw [pow_succ, pow_succ, pow_one]
                group
      _ = diagramMap TwistTag.D4 K * (diagramMap TwistTag.D4 K *
            pinnedX TwistTag.D4.tag K α (ε * 1) * (diagramMap TwistTag.D4 K)⁻¹) *
            (diagramMap TwistTag.D4 K)⁻¹ := by rw [hfx 1]
      _ = diagramMap TwistTag.D4 K * pinnedX TwistTag.D4.tag K α (ε * (ε * 1)) *
            (diagramMap TwistTag.D4 K)⁻¹ := by rw [hfx (ε * 1)]
      _ = pinnedX TwistTag.D4.tag K α (ε * (ε * (ε * 1))) := hfx (ε * (ε * 1))
      _ = pinnedX TwistTag.D4.tag K α (ε ^ 3) := by congr 1; ring
  have hε3 : ε ^ 3 = 1 := (pinnedX_injective TwistTag.D4.tag K α hXeq).symm
  have hε1 : ε = 1 := by
    have hcube : ε ^ 3 = ε := by
      calc ε ^ 3 = ε ^ 2 * ε := by ring
        _ = ε := by rw [pow_two, hε2, one_mul]
    rw [← hcube, hε3]
  rw [hfx c, hε1, one_mul]

private lemma pinnedX_commute {K : Type} [Field K] {γ δ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (hδ : IsRoot TwistTag.D4.tag δ)
    (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h : ¬ IsRoot TwistTag.D4.tag (γ + δ)) (c d : K) :
    Commute (pinnedX TwistTag.D4.tag K γ c) (pinnedX TwistTag.D4.tag K δ d) :=
  (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) hγ hδ hne hne').2 h K
    (pinnedX TwistTag.D4.tag K γ c) (Subgroup.subset_closure ⟨c, rfl⟩)
    (pinnedX TwistTag.D4.tag K δ d) (Subgroup.subset_closure ⟨d, rfl⟩)

private lemma mem_graphFixedRootGroup_pinnedX {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c)
    (hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σ c = c ^ n)
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α)
    (hρα : permLattice TwistTag.D4.perm α = α) {c : K} (hc : σ c = c) :
    pinnedX TwistTag.D4.tag K α c ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hfixeq := twistedFixedGroup_eq_graphFixedRootGroup_triality σ hσ3 hpar
  rw [← hfixeq, mem_twistedFixedGroup_iff_twistHom]
  refine ⟨pinnedX_mem_adjointGroup α c, ?_⟩
  apply Units.ext
  rw [coe_twistHom, entrywise_pinnedX, show σ.toRingHom c = c from hc]
  exact congrArg Units.val (diagramMap_conj_pinnedX_fixed hα hρα c)

theorem exists_inv_good_D4tw_field {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (h3 : 3 < p ^ f) (hfe : Even f) (δ : K ≃+* K)
    (hδ : ∀ c, δ c = c ^ (p ^ (3 * f / 2))) :
    ∃ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, orderOf x = p ∧
      fieldActor σ δ x = x⁻¹ ∧ IsSpecialGood p x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := d4_field_charP hp hf hK
  have hσ3 := d4_field_sigma_cube hK σ hσ
  have hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σ c = c ^ n :=
    Or.inr ⟨p ^ f, (hp.odd_of_ne_two hp2).pow, hσ⟩
  obtain ⟨ι₀, hι₀inj, hι₀fix⟩ := d4_field_embedding hp hf hK σ hσ
  obtain ⟨lam, hσlam, hlam0, hδlam⟩ := d4_field_exists_lambda hp hp2 hf hfe hK σ hσ δ hδ
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hcf := (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) isRoot_d4E2
    isRoot_d4Beta d4E2_ne_d4Beta d4E2_ne_neg_d4Beta).1 isRoot_d4Gamma
  have hn0 : (commConst TwistTag.D4.tag d4E2 d4Beta (1, 1) : K) ≠ 0 := by
    rcases hcf.1 with h | h <;> simp [h]
  let xa : GaloisField p f → graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun s =>
    ⟨pinnedX TwistTag.D4.tag K d4E2 (ι₀ s),
      mem_graphFixedRootGroup_pinnedX σ hσ3 hpar isRoot_d4E2 permLattice_d4E2 (hι₀fix s)⟩
  let xb : GaloisField p f → graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun s =>
    ⟨pinnedX TwistTag.D4.tag K d4Beta (lam * ι₀ s),
      mem_graphFixedRootGroup_pinnedX σ hσ3 hpar isRoot_d4Beta permLattice_d4Beta
        (by rw [map_mul, hσlam, hι₀fix])⟩
  let z : GaloisField p f → graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun s =>
    ⟨pinnedX TwistTag.D4.tag K d4Gamma
        ((commConst TwistTag.D4.tag d4E2 d4Beta (1, 1) : K) * (lam * ι₀ s)),
      mem_graphFixedRootGroup_pinnedX σ hσ3 hpar isRoot_d4Gamma permLattice_d4Gamma
        (by rw [map_mul, map_mul, map_intCast, hσlam, hι₀fix])⟩
  have hxa : ∀ s t, xa (s + t) = xa s * xa t := fun s t => Subtype.ext <| by
    show pinnedX TwistTag.D4.tag K d4E2 (ι₀ (s + t)) =
      pinnedX TwistTag.D4.tag K d4E2 (ι₀ s) * pinnedX TwistTag.D4.tag K d4E2 (ι₀ t)
    rw [map_add, pinnedX_add]
  have hxb : ∀ s t, xb (s + t) = xb s * xb t := fun s t => Subtype.ext <| by
    show pinnedX TwistTag.D4.tag K d4Beta (lam * ι₀ (s + t)) =
      pinnedX TwistTag.D4.tag K d4Beta (lam * ι₀ s) *
        pinnedX TwistTag.D4.tag K d4Beta (lam * ι₀ t)
    rw [map_add, mul_add, pinnedX_add]
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => Subtype.ext <| by
    show pinnedX TwistTag.D4.tag K d4Gamma
        ((commConst TwistTag.D4.tag d4E2 d4Beta (1, 1) : K) * (lam * ι₀ (s + t))) =
      pinnedX TwistTag.D4.tag K d4Gamma
          ((commConst TwistTag.D4.tag d4E2 d4Beta (1, 1) : K) * (lam * ι₀ s)) *
        pinnedX TwistTag.D4.tag K d4Gamma
          ((commConst TwistTag.D4.tag d4E2 d4Beta (1, 1) : K) * (lam * ι₀ t))
    rw [map_add, mul_add, mul_add, pinnedX_add]
  have hzi : Function.Injective z := by
    intro s t h
    have h' := pinnedX_injective TwistTag.D4.tag K d4Gamma (congrArg Subtype.val h)
    exact hι₀inj (mul_left_cancel₀ hlam0 (mul_left_cancel₀ hn0 h'))
  have hab : ∀ s t, ⁅xa s, xb t⁆ = z (s * t) := fun s t => Subtype.ext <| by
    show ⁅pinnedX TwistTag.D4.tag K d4E2 (ι₀ s), pinnedX TwistTag.D4.tag K d4Beta (lam * ι₀ t)⁆ =
      pinnedX TwistTag.D4.tag K d4Gamma
        ((commConst TwistTag.D4.tag d4E2 d4Beta (1, 1) : K) * (lam * ι₀ (s * t)))
    rw [hcf.2 K (ι₀ s) (lam * ι₀ t), map_mul]
    congr 1
    ring
  have hza : ∀ s t, Commute (z s) (xa t) := fun s t => Subtype.ext
    (pinnedX_commute isRoot_d4Gamma isRoot_d4E2 d4Gamma_ne_d4E2 d4Gamma_ne_neg_d4E2
      not_isRoot_d4Gamma_add_e2 _ _).eq
  have hzb : ∀ s t, Commute (z s) (xb t) := fun s t => Subtype.ext
    (pinnedX_commute isRoot_d4Gamma isRoot_d4Beta d4Gamma_ne_d4Beta d4Gamma_ne_neg_d4Beta
      not_isRoot_d4Gamma_add_beta _ _).eq
  have hspec := isSpecialGood_of_comm (K := GaloisField p f) hp hp2 hF h3 hxa hxb hz hzi hab
    hza hzb 1
  have hx1 : ((xb 1 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K d4Beta lam := by
    show pinnedX TwistTag.D4.tag K d4Beta (lam * ι₀ 1) = _
    rw [map_one, mul_one]
  have hxb0 : xb 0 = 1 := Subtype.ext <| by
    show pinnedX TwistTag.D4.tag K d4Beta (lam * ι₀ 0) = 1
    rw [map_zero, mul_zero, pinnedX_zero]
  have hpow : ∀ m : ℕ, xb (m : GaloisField p f) = xb 1 ^ m := by
    intro m
    induction m with
    | zero => rw [Nat.cast_zero, hxb0]; exact (pow_zero _).symm
    | succ m ih => rw [Nat.cast_succ, hxb, ih, pow_succ]
  have hup : xb 1 ^ p = 1 := by
    rw [← hpow p, show (p : GaloisField p f) = 0 from CharP.cast_eq_zero _ p, hxb0]
  have hne : xb 1 ≠ 1 := by
    intro h
    have h' : pinnedX TwistTag.D4.tag K d4Beta lam = pinnedX TwistTag.D4.tag K d4Beta 0 := by
      rw [← hx1, h, pinnedX_zero]
      rfl
    exact hlam0 (pinnedX_injective TwistTag.D4.tag K d4Beta h')
  have hact : fieldActor σ δ (xb 1) = (xb 1)⁻¹ := by
    apply Subtype.ext
    rw [coe_fieldActor, Subgroup.coe_inv, hx1, pinnedX_neg]
    apply Units.ext
    rw [Units.coe_map]
    change entrywise δ.toRingHom
      (pinnedX TwistTag.D4.tag K d4Beta lam : Module.End K (RootModule TwistTag.D4.tag K)) = _
    rw [entrywise_pinnedX, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hδlam]
  exact ⟨xb 1, orderOf_eq_prime hup hne, hact, hspec.2.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
