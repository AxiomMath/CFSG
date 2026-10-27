module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKOmega
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKGlue1
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKGlue2
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCount
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKU5
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKS4

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {n : ℕ}

theorem exists_coreHyp (s : Setting28 T M L Mm I H K n)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h48 : ASC48Statement G) (h425 : Thm4_2_5)
    (hline : ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (V₁ : Subgroup G), 1 < m ∧
      Fintype.card F = 2 ^ m ∧ IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁)
    {F₃ : Type} [Field F₃] [Fintype F₃] {V₁ V₂ : Subgroup G} (hF₃ : Fintype.card F₃ = 2 ^ n)
    (hV : ⁅reducedAggregate (L ⊔ T), L⁆ = V₁ ⊔ V₂) (hdisj : V₁ ⊓ V₂ = ⊥)
    (h₁ : IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₁
      (V₁ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F₃))
    (h₂ : IsNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) V₂
      (V₂ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G))
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL 2 F₃)) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥K →* ↥(StatedSL 3 F))
      (β : ↥(c134Q (K ⊔ pCoreOf 2 I) K) →* Multiplicative (Fin 2 → Fin 3 → F)),
      CoreHyp (pCoreOf 2 I) (pCoreOf 2 (L ⊔ T)) H K (c134Q (K ⊔ pCoreOf 2 I) K)
        (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ F α β := by
  obtain ⟨⟨_, F, hFi, hFf, α, -, hαm, hN⟩, -⟩ := (s.h2 : IsC134Case2 _ _ _)
  obtain ⟨β, hco⟩ := CoordData.of_isSumOfNaturalModulesVia hN
  have hFn : Fintype.card F = 2 ^ n := card_field_eq s hαm
  have hn2 : 2 ≤ n := by have := s.hn1; omega
  have hF₂ : ∃ m : ℕ, 2 ≤ m ∧ Fintype.card F = 2 ^ m := ⟨n, hn2, hFn⟩
  have hMS : IsMSPair (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) := by
    obtain ⟨-, hC3⟩ := s.c.c41Case3_of_isC134Case2 s.h2
    obtain ⟨_, _, _, _, _, _, _, hMS, _⟩ := hC3
    exact hMS
  have hpCore : pCoreOf 2 H ≠ ⊥ := s.c.inH.2
  have hG : ∃ g ∈ pCoreOf 2 (perfectCore (L ⊓ H)), g ∉ pCoreOf 2 K := by
    obtain ⟨m, F', hFi', hFf', V₁', hm, hF', hstab⟩ := hline
    exact exists_pCoreOf_LH_not_le s.c ⟨m, by omega, hF'⟩ hstab
  obtain ⟨g, hgLH, hgK⟩ := hG
  have hgR : g ∈ pCoreOf 2 I := pCoreOf_LH_le_R s.c hgLH
  have hgKs : g ∈ K := s.c.LH_le (pCoreOf_le 2 (perfectCore (L ⊓ H)) hgLH)
  have hg₀α : α ⟨g, hgKs⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨g, hgKs⟩ : ↥K) ∈ α.ker := MonoidHom.mem_ker.mpr h1
    rw [hαm.2] at h2
    exact hgK ((mem_pCoreOf_iff' ⟨g, hgKs⟩).mpr h2)
  have hVQ : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ c134Q (K ⊔ pCoreOf 2 I) K :=
    V_le_Q s.c s.hy h37 h38 h39 s.hKH hMS
  have hVΩ : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ omegaOneCenterOf (pCoreOf 2 I) :=
    V_le_omega s.c s.hy h37 h38 h39
  have hVcardF : Nat.card ↥⁅reducedAggregate (L ⊔ T), L⁆ = Fintype.card F ^ 4 := by
    rw [s.hVcard, hFn]
    ring
  have hΩQ := omega_inf_eq_of_card hco hgKs hg₀α hgR hVQ hVΩ hVcardF
  have LHRp : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    ((perfectCore_le (L ⊓ H)).trans inf_le_left).trans
      ((le_sup_left : L ≤ L ⊔ T).trans (le_normalizer_pCoreOf 2 (L ⊔ T)))
  have RLH : pCoreOf 2 I ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
    (le_inf ((pCoreOf_le 2 I).trans s.c.inH.1) ((pCoreOf_le 2 I).trans s.c.I_le)).trans
      s.c.LH_normal
  have LH_C := omega_inf_centralizer_le s.c h37 s.hKH s.h2 hline
  have CV := cv_of_sum s.c hF₃ hV hdisj h₁ h₂ s.hVL
  have hZ0 := omegaOneCenter_Rp_inf_centralizer_eq_bot s.c s.hy h37 h38 h39 LH_C
  have h27 : ∀ Y : Subgroup G, Y ≤ H → ⁅Y, Y⁆ = Y →
      (∃ ρ : ↥Y →* ↥(StatedSL 2 F), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker) → Y ≤ K := by
    rintro Y hYH hYp ⟨ρ, hρ, hρ2⟩
    exact lemma27 s.hy.qtke s.hy.simple s.hy.nonabelian h37 h39 hpCore s.c.K_mem s.hKH hn2 hFn
      hαm.1 hαm.2 hYH hYp ρ hρ hρ2
  refine ⟨F, hFi, hFf, α, β, ?_⟩
  exact ⟨pCoreOf_isPGroup 2 (L ⊔ T), s.c.R_le, s.c.inf_le_pCoreOf_I s.hy h37 h38 h39,
    V_le_omega s.c s.hy h37 h38 h39, Rp_le_centralizer_V s.c, hΩQ.1,
    commutator_omega_le_Q s.c h37 s.hKH hMS, s.c.LH_le, perfectCore_perfect (L ⊓ H),
    s.c.perfectCore_le_normalizer_pCoreOf_I, LHRp, RLH, s.c.LH_le_normalizer_V, LH_C, CV,
    normalizer_Q_le_H s h36 h37 h38 h39 h48 h425,
    fun hZ => normalizer_ZC_le_H s h36 h37 h38 h39 h48 h425 hZ,
    fun hR => omega_inf_centralizer_eq_bot_of_eq s.c hZ0 hR, h27, hco, hαm.1, hαm.2, hF₂,
    ⟨hVQ, ⟨g, hgKs, hg₀α, hΩQ.2⟩, hVcardF⟩⟩

end CFSG.Quasithin.H13.Ch4.CentK
