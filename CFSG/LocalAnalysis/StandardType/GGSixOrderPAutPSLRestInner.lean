module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace OrdPRest

section Split

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem exists_conj_mem_centralizer_of_root
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (h24 : GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G))) (hpF : p ∣ Nat.card F - 1)
    {y : G} (hyp : y ^ p = 1) {A : GL (Fin (m + 1)) F}
    (hA : ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagA.conjSL A u))
    (hroot : ∀ c : Fˣ, A ^ p = GeneralLinearGroup.scalar (Fin (m + 1)) c → ∃ μ : Fˣ, μ ^ p = c) :
    ∃ s : SpecialLinearGroup (Fin (m + 1)) F,
      (ψ s)⁻¹ * y * ψ s ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  obtain ⟨A', hA'p, hA'⟩ := exists_pow_eq_one hker hA hyp hroot
  obtain ⟨ζ, hζ⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd hS.prime hpF
  have : NeZero p := ⟨hS.prime.ne_zero⟩
  obtain ⟨Q, hQ⟩ := TypeA.PGLTor.exists_conj_diagonal hζ ({A'} : Set (GL (Fin (m + 1)) F))
    (fun x hx z hz => by
      rw [Set.mem_singleton_iff] at hx hz
      rw [hx, hz])
    (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx, hA'p])
  refine exists_conj_mem_centralizer hCψ (bstar_toral hS h24 hpF)
    (fun b hb => RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hS.innerDiag b hb)) hA' (Q := Q) ?_
  intro i j hij
  rw [Units.val_mul, Units.val_mul]
  exact hQ A' (Set.mem_singleton A') i j hij

end Split

end OrdPRest

section Family

theorem ggOrdPInnerConj_PSL_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSL n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSL n f).D .PSL n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ GGOutdiagPrimeConfig p .PSL n f →
    p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiInnerDiag (ggU .PSL n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS h24 hncfg hpq y _ hyo hy
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hm : 2 ≤ m := hrank
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hpn : ¬ p ∣ Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    exact fun h => hncfg (Or.inl ⟨rfl, h, hpq⟩)
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag (F := GaloisField 2 f) hm hker hy
  obtain ⟨s, hs⟩ := OrdPRest.exists_conj_mem_centralizer_of_root (F := GaloisField 2 f) hS h24
    hpF hyp hA fun c hc => by
      refine TypeA.PGLTor.exists_pow_eq_of_pow_eq_scalar hS.prime
        (M := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) ?_ hpn
      have h := congrArg (fun X : GL (Fin (m + 1)) (GaloisField 2 f) =>
        (X : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) hc
      simpa only [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] using h
  exact ⟨ψ s, Subgroup.le_normalizer (hrange ▸ ⟨s, rfl⟩), hs⟩

@[expose] def GGOrdPInnerConjPSLNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .PSL n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSL n f).D .PSL n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiInnerDiag (ggU .PSL n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPInnerConjAt_PSL_of_nonsplit (h : GGOrdPInnerConjPSLNonsplit) :
    GGOrdPInnerConjAt .PSL := by
  intro G _ _ p Bs G₀ n f ψ hS h24 hncfg y hyM hyo hy
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact ggOrdPInnerConj_PSL_split G p Bs G₀ n f ψ hS h24 hncfg hpq y hyM hyo hy
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hy

end Family

end CFSG.StandardType
