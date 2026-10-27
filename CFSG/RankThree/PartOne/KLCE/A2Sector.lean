module

public import CFSG.RankThree.PartOne.KLCE.Engine
public import CFSG.RankThree.PartOne.KLCE.FrameConj
public import CFSG.RankThree.PartOne.KLCE.TypeSL
public import CFSG.RankThree.PartOne.KLCE.A2Model
public import CFSG.RankThree.PartOne.KLCE.A2Family
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalDescent

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedSU)

open scoped MatrixGroups

section Claims

@[expose] def A2LayerClaims (p : ℕ) {G : Type} [Group G] (α : MulAut G) (Q : Subgroup G) : Prop :=
  (∀ g ∈ Q, α g ∈ Q) ∧ (∃ g ∈ Q, α g ≠ g) ∧ (∀ z ∈ Subgroup.center ↥Q, z ^ 3 = 1) ∧
    (∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
      LieModel (↥Q ⧸ Subgroup.center ↥Q) t' n' 2 (p * f'')) ∧
    ∃ t₁ ∈ Q, α t₁ = t₁ ∧ ∃ t₂ ∈ Q, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

end Claims

section Bridge

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)} {L : Type} [Field L]

theorem a2_bridge (E : A2Embedding τ S) {n₀ : ModGL τ L} {Φ₀ Fr : L →+* L} {p : ℕ}
    (hn₀fix : Units.map (entrywiseHom Φ₀) n₀ = n₀)
    (hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u)
    (Θ₀ : SL(3, L) ≃* SL(3, L))
    (hΘ₀ : ∀ X, n₀ * Units.map (entrywiseHom Φ₀) (E.ρ L X) * n₀⁻¹ = E.ρ L (Θ₀ X))
    {D : Type} [Group D] (ψ : D →* SL(3, L)) (τ' : D →* D) (hψinj : Function.Injective ψ)
    (hcompat : ∀ d, Θ₀ (ψ d) = ψ (τ' d))
    (hfix : ∀ X, (⇑Θ₀)^[p] X = X ↔ X ∈ ψ.range) :
    Function.Injective ((E.ρ L).comp ψ) ∧
      ((E.ρ L).comp ψ).range = (E.ρ L).range ⊓
        twistedFixedPoints (n₀ ^ p) (Units.map (entrywiseHom Fr)) ∧
      ∀ d, n₀ * Units.map (entrywiseHom Φ₀) (((E.ρ L).comp ψ) d) * n₀⁻¹ =
        ((E.ρ L).comp ψ) (τ' d) := by
  have hρiter : ∀ (k : ℕ) (X : SL(3, L)), E.ρ L ((⇑Θ₀)^[k] X) =
      (fun v => n₀ * Units.map (entrywiseHom Φ₀) v * n₀⁻¹)^[k] (E.ρ L X) := by
    intro k
    induction k with
    | zero => intro X; rfl
    | succ k ih =>
      intro X
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hΘ₀]
  have hρp : ∀ X : SL(3, L), E.ρ L ((⇑Θ₀)^[p] X) =
      n₀ ^ p * Units.map (entrywiseHom Fr) (E.ρ L X) * (n₀ ^ p)⁻¹ := by
    intro X
    rw [hρiter, iterate_F0 (Units.map (entrywiseHom Φ₀)) hn₀fix p, ← hΦK]
  refine ⟨(E.inj L).comp hψinj, ?_, fun d => ?_⟩
  · refine Subgroup.ext fun u => ?_
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨⟨ψ d, rfl⟩, ?_⟩
      rw [mem_twistedFixedPoints]
      show n₀ ^ p * Units.map (entrywiseHom Fr) (E.ρ L (ψ d)) * (n₀ ^ p)⁻¹ = E.ρ L (ψ d)
      rw [← hρp, (hfix _).2 ⟨d, rfl⟩]
    · rintro ⟨⟨X, rfl⟩, hX⟩
      rw [mem_twistedFixedPoints, ← hρp] at hX
      have h1 : (⇑Θ₀)^[p] X = X := (E.inj L) hX
      obtain ⟨d, hd⟩ := (hfix X).1 h1
      exact ⟨d, by simp [hd]⟩
  · change n₀ * Units.map (entrywiseHom Φ₀) (E.ρ L (ψ d)) * n₀⁻¹ = E.ρ L (ψ (τ' d))
    rw [hΘ₀, hcompat]

end Bridge


section Model

variable {τ : Tag} {S : Set (Fin τ.rank → ℤ)}

theorem a2_model (E : A2Embedding τ S) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {K₀ K L : Type}
    [Field K₀] [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K₀ L] [IsAlgClosure K₀ L]
    [Algebra K L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ (p * f₀)) (σ : K ≃+* K)
    (hσord : orderOf σ = p)
    (hσ : ∀ c : K, iterateFrobenius L 2 f₀ (algebraMap K L c) = algebraMap K L (σ c))
    (n₀ : ModGL τ L) (hn₀fix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀)
    (hn₀m : n₀ ∈ monomialSubgroup τ L)
    (hW : ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = δ • E.r i j) :
    ∃ (D : Type) (_ : Group D) (ρ' : D →* ModGL τ L) (τ' : D →* D), Function.Injective ρ' ∧
      ρ'.range = (E.ρ L).range ⊓ twistedFixedPoints (n₀ ^ p)
        (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) ∧
      (∀ d, n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (ρ' d) * n₀⁻¹ = ρ' (τ' d)) ∧
      ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
        (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → A2LayerClaims p α Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have hp0 := hp.pos
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσord
    exact hp.one_lt.ne hσord
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀c : ∀ c, Φ₀ c = c ^ 2 ^ f₀ := fun c => iterateFrobenius_def 2 f₀ c
  have hΦ₀bij : Function.Bijective Φ₀ := ⟨Φ₀.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 ^ f₀ by positivity)
    exact ⟨x, by rw [hΦ₀c, hx]⟩⟩
  have hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u := units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) => E.gen L i j hij
  rcases hδ with rfl | rfl
  ·
    have hconj := E.conj_split hn₀m (fun i j hij => by rw [hW i j hij, one_smul])
    obtain ⟨Θ₀, hΘ₀, b, hshape⟩ := exists_aut_of_rootData (E.ρ L) (E.inj L) E.r ε hε Φ₀ hΦ₀bij
      n₀ (fun i j => (i, j)) (fun i j hij => hij) (fun i j hij => ⟨i, j, hij, rfl⟩) hconj
    obtain ⟨ψ, hψinj, hψcompat, hψfix⟩ := a2_split_model hf₀ hK₀ hp.one_le hK σ hσ Θ₀ b hshape
    obtain ⟨hinj, hrange, hcompat⟩ := a2_bridge E hn₀fix hΦK Θ₀ hΘ₀ ψ
      (Matrix.SpecialLinearGroup.map σ.toRingHom) hψinj hψcompat hψfix
    refine ⟨SL(3, K), inferInstance, (E.ρ L).comp ψ, Matrix.SpecialLinearGroup.map σ.toRingHom, hinj,
      hrange, hcompat, ?_⟩
    intro G _ α φ hφ hαφ Q hQ
    exact sl_type_claims (m := 1) hp5 hf₀ hK hσ1 α φ hφ hαφ Q hQ
  ·
    have hconj := E.conj_unitary hn₀m (fun i j hij => by rw [hW i j hij, neg_one_smul])
    obtain ⟨Θ₀, hΘ₀, b, hshape⟩ := exists_aut_of_rootData (E.ρ L) (E.inj L) E.r ε hε Φ₀ hΦ₀bij
      n₀ (fun i j => (j, i)) (fun i j hij => hij.symm) (fun i j hij => ⟨j, i, hij.symm, rfl⟩)
      hconj
    obtain ⟨K'', _, _, _, σ'', ψ, τ', hK'', hσ''ord, hτ', hψinj, hψcompat, hψfix⟩ :=
      a2_unitary_model hf₀ hK₀ hp (hp.odd_of_ne_two (by omega)) Θ₀ b hshape
    obtain ⟨hinj, hrange, hcompat⟩ := a2_bridge E hn₀fix hΦK Θ₀ hΘ₀ ψ τ' hψinj hψcompat hψfix
    refine ⟨↥(StatedSU 3 (2 ^ (p * f₀)) K''), inferInstance, (E.ρ L).comp ψ, τ', hinj, hrange,
      hcompat, ?_⟩
    intro G _ α φ hφ hαφ Q hQ
    exact su3_type_claims hp hp5 hf₀ hK'' hσ''ord α φ hφ τ' hτ' hαφ Q hQ

end Model


section Weyl

theorem weyl_pow_smul {τ : Tag} (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1) (hw : w • γ = δ • γ) {p : ℕ} (hp : Odd p) :
    (w ^ p) • γ = δ • γ := by
  rcases hδ with rfl | rfl
  · rw [one_smul] at hw ⊢
    clear hp
    induction p with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_smul, ih, hw]
  · rw [neg_one_smul] at hw ⊢
    obtain ⟨m, rfl⟩ := hp
    have h2 : (w ^ 2) • γ = γ := by
      rw [pow_two, mul_smul, hw, smul_neg, hw, neg_neg]
    have hm : ∀ k : ℕ, ((w ^ 2) ^ k) • γ = γ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', mul_smul, ih, h2]
    rw [pow_succ, pow_mul, mul_smul, hw, smul_neg, hm]

end Weyl


section Sector


theorem frobSector_of_a2Frame {τ : Tag} {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {e p₀ : ℕ}
    {S : Set (Fin τ.rank → ℤ)} (E : A2Embedding τ S) (δ : ℤ)
    (hδ : δ = 1 ∨ δ = -1)
    (hlow : ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
      Nat.card K = 2 ^ (p * f₀) → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      CFSG.pRank p (adjointGroup τ K) = 1 → p₀ < p)
    (hframe : ∀ (K₀ L : Type) [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
      [IsAlgClosure K₀ L] [CharP L 2] (f₀ p : ℕ), 1 ≤ f₀ → Nat.card K₀ = 2 ^ f₀ → p.Prime →
      p₀ < p → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) →
      ¬ p ∣ Nat.card (WeylGroup τ) ∧
      ∃ n₀ : ModGL τ L, ∃ hn₀m : n₀ ∈ monomialSubgroup τ L,
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        (∀ i j, i ≠ j → weylQuotientHom τ L ⟨n₀, hn₀m⟩ • E.r i j = δ • E.r i j) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) S) =
            N₀ ∧
          p ^ (Nat.card (adjointGroup τ K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin τ.rank → Lˣ,
            rootDiagUnit τ a ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) S →
            orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ S)) :
    FrobSector τ e := by
  intro K _ _ p f₀ hp hp5 hf₀ hK σ hσord hσ hΦ hpr x hxp hx1 hxσ
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : p₀ < p := hlow K p f₀ hp hp5 hf₀ hK hΦ hpr
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf hK
  obtain ⟨K₀, _, _, _, hK₀⟩ := exists_subfield_of_frobenius hp hf₀ hK hσord
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨_, hst, hac⟩ := exists_tower_algebra (K₀ := K₀) (K := K) (L := L)
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀K : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c) := fun c => by
    rw [hΦ₀def, iterateFrobenius_def, ← map_pow, hσ]
  have hFrc : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u := units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  have hcard : (Nat.card K : ℤ) = (Nat.card K₀ : ℤ) ^ p := by
    rw [hK, hK₀]
    push_cast
    rw [← pow_mul, mul_comm]
  have hpf₀ : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) :=
    dvd_eval_of_dvd_eval_pow hp (exhaustionPhi e) (by rwa [hcard] at hΦ)
  obtain ⟨hordW, n₀, hn₀m, hn₀fix, hW, N₀, hN₀, hZcard, hord, hkerZ₀⟩ :=
    hframe K₀ L f₀ p hf₀ hK₀ hp hp0 hpf₀
  have hn₀C : n₀ ∈ adjointGroup τ L := monomialSubgroup_le_adjointGroup' hn₀m
  obtain ⟨g₀, hg₀C, hg₀, hconj⟩ := frame_conj (K₀ := K₀) (K := K) (L := L) hτ
    hf₀ hK₀ hp (by omega) n₀ hn₀C
    (subtorusSigma n₀ (Units.map (entrywiseHom Φ₀)) S) (subtorusSigma_le_twistedTorusOf _ _ _)
    hN₀ hZcard hord
  have hxfix : Units.map (entrywiseHom Φ₀) (adjEmb τ K L x) = adjEmb τ K L x := by
    rw [entrywise_adjEmb hΦ₀K x, hxσ]
  obtain ⟨c, hcfix, hcx⟩ := hconj x hxord hxfix
  have hcσ : entrywiseAdjointAut τ σ c = c := by
    apply adjEmb_injective (τ := τ) (K := K) (L := L)
    rw [← entrywise_adjEmb hΦ₀K c]
    exact hcfix
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hn₀pm : n₀ ^ p ∈ monomialSubgroup τ L := pow_mem hn₀m p
  have hpowW : weylQuotientHom τ L ⟨n₀ ^ p, hn₀pm⟩ = (weylQuotientHom τ L ⟨n₀, hn₀m⟩) ^ p := by
    rw [← map_pow]
    rfl
  have hWp : ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n₀ ^ p, hn₀pm⟩ • E.r i j = δ • E.r i j :=
    fun i j hij => by
      rw [hpowW]
      exact weyl_pow_smul _ _ δ hδ (hW i j hij) hpodd
  have hFr' : ∀ c, Fr c = c ^ 2 ^ (f₀ * p) := fun c => iterateFrobenius_def 2 (f₀ * p) c
  have hKf : Nat.card K = 2 ^ (f₀ * p) := by rw [hK, mul_comm]
  have hq2 : 2 < 2 ^ (f₀ * p) := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f₀ * p) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  obtain ⟨P, hfam, hP'⟩ := a2_family_join E Nat.prime_two (f := f₀ * p) (by nlinarith) (k := K)
    hKf hq2 Fr hFr' (n₀ ^ p) hn₀pm δ hδ hWp
  have hg₀N : Units.map (entrywiseHom Fr) g₀ = g₀ * n₀ ^ p := by
    rw [hΦK, iterate_lang (Units.map (entrywiseHom Φ₀)) hn₀fix hg₀ p]
  have hperf : ∀ Y : Subgroup (ModGL τ L), Finite Y → Y ≤ adjointGroup τ L →
      (∀ y ∈ Y, Units.map (entrywiseHom Fr) y = y) → ⁅Y, Y⁆ = Y → Y ≤ (adjEmb τ K L).range :=
    fun Y hY hYC hYF hYp => by
      rw [adjEmb_range]
      exact (finite_fixed_subgroup_rational_perfect (K := K) d hτ Fr hFrc Y hYC
        hYF).2.2 Y le_rfl hYp
  have hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf (n₀ ^ p) (Units.map (entrywiseHom Fr)) →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)) :=
    fun a hap ha1 _ => rootCharStabilizer_subset_closure hp hordW hap ha1
  have hjoin : rootSpan τ L S ⊓ twistedFixedPoints (n₀ ^ p) (Units.map (entrywiseHom Fr)) ≤
      ⨆ i : Unit, P i := by
    rw [iSup_unique]
    change _ ≤ P ()
    rw [hP', E.range L]
  have hZle : subtorusSigma n₀ (Units.map (entrywiseHom Φ₀)) S ≤
      subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) S :=
    fun z hz => ⟨twistedTorusOf_le_pow hn₀fix p hΦK hz.1, hz.2⟩
  have hzmem : g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ ∈
      subtorusSigma n₀ (Units.map (entrywiseHom Φ₀)) S :=
    (mem_subtorusImage_iff _ _ _ _).1 hcx
  have hc : c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀
      (subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) S) :=
    (mem_subtorusImage_iff _ _ _ _).2 (hZle hzmem)
  have hker : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a = g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ → rootCharKernel a ⊆ S := by
    intro a ha
    have hord' : orderOf (rootDiagUnit τ a) = p := by
      rw [ha, ← psiTilde_apply, orderOf_injective (psiTilde τ K L g₀ c)
        (psiTilde_injective g₀ c) x, hxord]
    exact hkerZ₀ a (ha ▸ hzmem) hord'
  obtain ⟨hPrange, hcomp, hsolv, hnormal, hodd⟩ := layerData_structure hp Fr hFrc (n₀ ^ p) g₀
    hg₀C hg₀N hperf hstab E.isRoot_of_mem E.neg_mem P hfam hjoin
    (fun i j hij => absurd (Subsingleton.elim i j) hij) hxord c hc hker
  obtain ⟨D, _, ρ', τ', hρ'inj, hρ'range, hρ'compat, hclaims⟩ :=
    a2_model E δ hδ hf₀ hK₀ hp hp5 hK σ hσord hΦ₀K n₀ hn₀fix hn₀m hW
  refine ⟨Unit, fun i => layerComp g₀ c P i, ⟨()⟩, hcomp, hsolv, hnormal, hodd, fun i hstabQ => ?_⟩
  have hPrange' : ρ'.range ≤ (psiTilde τ K L g₀ c).range := by
    rw [hρ'range, ← hP']
    exact hPrange ()
  obtain ⟨φ, hφinj, hψφ, hφrange⟩ := exists_hom_of_push (psiTilde τ K L g₀ c)
    (psiTilde_injective g₀ c) ρ' hρ'inj hPrange'
  have hQ : φ.range = layerComp g₀ c P () := by
    rw [hφrange, hρ'range, ← hP']
    rfl
  have hασ : ∀ d', entrywiseAdjointAut τ σ (φ d') = φ (τ' d') := fun d' => by
    apply psiTilde_injective g₀ c
    rw [← psiTilde_entrywise hΦ₀K hg₀ hcσ, hψφ, hρ'compat, ← hψφ]
  have hαp : entrywiseAdjointAut τ σ ^ p = 1 := by
    have h1 : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
    have := map_pow (entrywiseAdjointAutHom (τ := τ) (K := K)) σ p
    rw [h1, map_one] at this
    exact this.symm
  obtain ⟨-, hmove, hZ, hmodel, hfix⟩ := hclaims (entrywiseAdjointAut τ σ) φ hφinj hασ _ hQ
  refine ⟨?_, hmodel, hfix⟩
  have hQX := (hcomp ()).1
  exact component_outer hp hpr hxord hαp
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hQX hy)) hstabQ (n := 3)
    (by norm_num) (by omega) hZ hmove

end Sector


section Rational

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem canonicalRep_frobenius_fixed (f₀ : ℕ) (w : WeylGroup τ) :
    Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (canonicalRep (coxeterSystem τ) L w) =
      canonicalRep (coxeterSystem τ) L w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.LieType.Chevalley.entrywise_canonicalRep (iterateFrobeniusEquiv L 2 f₀) w
  rw [CFSG.LieType.AlgebraicGroups.iterateFrobeniusEquiv_toRingHom] at this
  exact this

end Rational

end CFSG.RankThree.PartOne.KLCE
