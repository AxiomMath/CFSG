module

public import CFSG.RankThree.PartOne.KLCE.Engine
public import CFSG.RankThree.PartOne.KLCE.Frob
public import CFSG.RankThree.PartOne.KLCE.FrameConj
public import CFSG.RankThree.PartOne.KLCE.TypeSL
public import CFSG.RankThree.PartOne.KLCE.A1TypeII

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped MatrixGroups

section Sector


theorem frobSector_of_a1FrameU {τ : Tag} {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {e p₀ : ℕ}
    (hp₀ : 5 ≤ p₀) {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hlow : ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
      Nat.card K = 2 ^ (p * f₀) → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      CFSG.pRank p (adjointGroup τ K) = 1 → p₀ < p)
    (hframe : ∀ (K₀ L : Type) [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
      [IsAlgClosure K₀ L] [CharP L 2] (f₀ p : ℕ), 1 ≤ f₀ → Nat.card K₀ = 2 ^ f₀ → p.Prime →
      p₀ < p → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) →
      ¬ p ∣ Nat.card (WeylGroup τ) ∧
      ∃ n₀ : ModGL τ L, n₀ ∈ adjointGroup τ L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        (∃ J₀ : SL(2, L),
          (∀ B : SL(2, L), n₀ * rootSL2 τ L θ B * n₀⁻¹ = rootSL2 τ L θ (J₀ * B * J₀⁻¹)) ∧
          Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f₀) J₀ = J₀ ∧ J₀ * J₀ = 1 ∧
          ∃ P₀ : GL (Fin 2) L, P₀ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 f₀) P₀⁻¹ =
            Matrix.SpecialLinearGroup.toGL J₀) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) θ) = N₀ ∧
          p ^ (Nat.card (adjointGroup τ K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin τ.rank → Lˣ,
            rootDiagUnit τ a ∈ subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
              θ → orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ {θ, -θ})) :
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
  obtain ⟨hordW, n₀, hn₀C, hn₀fix, ⟨J₀, hn₀J, hJ₀fix, hJ₀sq, P₀, hP₀⟩, N₀, hN₀, hZcard, hord,
    hkerZ₀⟩ := hframe K₀ L f₀ p hf₀ hK₀ hp hp0 hpf₀
  obtain ⟨g₀, hg₀C, hg₀, hconj⟩ := frame_conj (K₀ := K₀) (K := K) (L := L) hτ
    hf₀ hK₀ hp (by omega) n₀ hn₀C
    (subtorusA1 n₀ (Units.map (entrywiseHom Φ₀)) θ) (subtorusA1_le_twistedTorusOf _ _ _)
    hN₀ hZcard hord
  have hxfix : Units.map (entrywiseHom Φ₀) (adjEmb τ K L x) = adjEmb τ K L x := by
    rw [entrywise_adjEmb hΦ₀K x, hxσ]
  obtain ⟨c, hcfix, hcx⟩ := hconj x hxord hxfix
  have hcσ : entrywiseAdjointAut τ σ c = c := by
    apply adjEmb_injective (τ := τ) (K := K) (L := L)
    rw [← entrywise_adjEmb hΦ₀K c]
    exact hcfix
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hJpow : ∀ J : SL(2, L), J * J = 1 → J ^ p = J := fun J hJ => by
    obtain ⟨m, hm⟩ := hpodd
    rw [hm, pow_succ, pow_mul, pow_two, hJ, one_pow, one_mul]
  have hNJ : ∀ B : SL(2, L), n₀ ^ p * rootSL2 τ L θ B * (n₀ ^ p)⁻¹ =
      rootSL2 τ L θ (J₀ * B * J₀⁻¹) := fun B => by
    rw [pow_conj_rootSL2 hn₀J p B, hJpow J₀ hJ₀sq]
  have hP : P₀ * Matrix.GeneralLinearGroup.map Fr P₀⁻¹ = Matrix.SpecialLinearGroup.toGL J₀ := by
    have hJGL : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL J₀) =
        Matrix.SpecialLinearGroup.toGL J₀ := by
      have h2 : Matrix.GeneralLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.toGL J₀) =
          Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Φ₀ J₀) := by
        ext i j
        rfl
      rw [h2, hJ₀fix]
    have h1 := P_frobenius_pow hJGL hP₀ p
    rw [h1]
    have hsq : Matrix.SpecialLinearGroup.toGL J₀ * Matrix.SpecialLinearGroup.toGL J₀ = 1 := by
      rw [← map_mul, hJ₀sq, map_one]
    obtain ⟨m, hm⟩ := hpodd
    rw [hm, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hX := a1_hX_of_J hNJ Fr hP
  obtain ⟨P, hfam, hP'⟩ := a1_sigma_family_of_action hK4 hθ Fr hFrc P₀ hX
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
  have hS : ∀ α ∈ ({θ, -θ} : Set (Fin τ.rank → ℤ)), IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hθ, IsRoot.neg hθ]
  have hSn : ∀ α ∈ ({θ, -θ} : Set (Fin τ.rank → ℤ)), -α ∈ ({θ, -θ} : Set (Fin τ.rank → ℤ)) := by
    intro α hα
    rcases hα with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  have hjoin : (⨆ i : Unit, P i) = rootSpan τ L {θ, -θ} ⊓
      twistedFixedPoints (n₀ ^ p) (Units.map (entrywiseHom Fr)) := by
    rw [iSup_unique]
    change P () = _
    rw [hP', a1_fixed_range_of_action hθ Fr hFrc P₀ hX]
  have hZle : subtorusA1 n₀ (Units.map (entrywiseHom Φ₀)) θ ≤
      subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) {θ, -θ} := by
    intro z hz
    refine ⟨twistedTorusOf_le_pow hn₀fix p hΦK hz.1, ?_⟩
    rw [rootSpan_pm_eq_range hθ]
    exact hz.2
  have hzmem : g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ ∈
      subtorusA1 n₀ (Units.map (entrywiseHom Φ₀)) θ :=
    (mem_subtorusImage_iff _ _ _ _).1 hcx
  have hc : c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀
      (subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) {θ, -θ}) :=
    (mem_subtorusImage_iff _ _ _ _).2 (hZle hzmem)
  have hker : ∀ a : Fin τ.rank → Lˣ,
      rootDiagUnit τ a = g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ {θ, -θ} := by
    intro a ha
    have hord' : orderOf (rootDiagUnit τ a) = p := by
      rw [ha, ← psiTilde_apply, orderOf_injective (psiTilde τ K L g₀ c)
        (psiTilde_injective g₀ c) x, hxord]
    exact hkerZ₀ a (ha ▸ hzmem) hord'
  obtain ⟨hPrange, hcomp, hsolv, hnormal, hodd⟩ := layerData_structure hp Fr hFrc (n₀ ^ p) g₀ hg₀C
    hg₀N hperf hstab hS hSn P hfam hjoin.ge (fun i j hij => absurd (Subsingleton.elim i j) hij) hxord
    c hc hker
  refine ⟨Unit, fun i => layerComp g₀ c P i, ⟨()⟩, hcomp, hsolv, hnormal, hodd, fun i hstabQ => ?_⟩
  have hPrange' : (a1HomConj τ K L θ P₀).range ≤ (psiTilde τ K L g₀ c).range := by
    rw [← hP']
    exact hPrange ()
  obtain ⟨φ, hφinj, hψφ, hφrange⟩ := exists_hom_of_push (psiTilde τ K L g₀ c)
    (psiTilde_injective g₀ c) (a1HomConj τ K L θ P₀) (a1HomConj_injective _ _) hPrange'
  have hQ : φ.range = layerComp g₀ c P () := by
    rw [hφrange, ← hP']
    rfl
  have hασ : ∀ B : SL(2, K), entrywiseAdjointAut τ σ (φ B) =
      φ (Matrix.SpecialLinearGroup.map σ.toRingHom B) := fun B => by
    apply psiTilde_injective g₀ c
    rw [← psiTilde_entrywise hΦ₀K hg₀ hcσ, hψφ, a1_F0_compat_II hn₀J hΦ₀K hP₀, ← hψφ]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσord
    exact hp.one_lt.ne hσord
  have hαp : entrywiseAdjointAut τ σ ^ p = 1 := by
    have h1 : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
    have := map_pow (entrywiseAdjointAutHom (τ := τ) (K := K)) σ p
    rw [h1, map_one] at this
    exact this.symm
  obtain ⟨-, hmove, hZ, hmodel, hfix⟩ := sl_type_claims (m := 0) hp5 hf₀ hK hσ1
    (entrywiseAdjointAut τ σ) φ hφinj hασ _ hQ
  refine ⟨?_, hmodel, hfix⟩
  have hQX := (hcomp ()).1
  exact component_outer hp hpr hxord hαp
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hQX hy)) hstabQ (n := 2)
    (by norm_num) (by omega) hZ hmove

theorem frobSector_of_a1Frame {τ : Tag} {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {e p₀ : ℕ}
    (hp₀ : 5 ≤ p₀) {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hlow : ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → 5 ≤ p → 1 ≤ f₀ →
      Nat.card K = 2 ^ (p * f₀) → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      CFSG.pRank p (adjointGroup τ K) = 1 → p₀ < p)
    (hframe : ∀ (K₀ L : Type) [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
      [IsAlgClosure K₀ L] [CharP L 2] (f₀ p : ℕ), 1 ≤ f₀ → Nat.card K₀ = 2 ^ f₀ → p.Prime →
      p₀ < p → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) →
      ¬ p ∣ Nat.card (WeylGroup τ) ∧
      ∃ n₀ : ModGL τ L, n₀ ∈ adjointGroup τ L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        n₀ ∈ Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L)) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) θ) = N₀ ∧
          p ^ (Nat.card (adjointGroup τ K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin τ.rank → Lˣ,
            rootDiagUnit τ a ∈ subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
              θ → orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ {θ, -θ})) :
    FrobSector τ e := by
  refine frobSector_of_a1FrameU hτ hp₀ hθ hlow ?_
  intro K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp0 hpf
  obtain ⟨hordW, n₀, hn₀C, hn₀fix, hn₀cent, N₀, hN₀, hZcard, hord, hker⟩ :=
    hframe K₀ L f₀ p hf₀ hK₀ hp hp0 hpf
  refine ⟨hordW, n₀, hn₀C, hn₀fix, ⟨1, fun B => ?_, map_one _, mul_one _, 1, ?_⟩, N₀, hN₀,
    hZcard, hord, hker⟩
  · have h := Subgroup.mem_centralizer_iff.1 hn₀cent (rootSL2 τ L θ B) ⟨_, rfl⟩
    rw [one_mul, inv_one, mul_one, ← h, mul_inv_cancel_right]
  · rw [inv_one, map_one, mul_one, map_one]

end Sector

end CFSG.RankThree.PartOne.KLCE
