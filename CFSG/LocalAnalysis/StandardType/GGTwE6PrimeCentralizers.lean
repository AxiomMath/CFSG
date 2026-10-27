module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inputs
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidAssembly

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.SeitzReduction.TwistedE6Pilot

@[expose] def TwE6OddSpectrum :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (Fr : L →+* L)
    (S : LangSetup TwistTag.E6.tag L p₀), S.IsAlgebraic → S.D.q = 2 → (∀ c, Fr c = c ^ 2) →
      S.D.Φ = twistHom TwistTag.E6 L Fr → ∀ x : S.Γ, Odd (orderOf x) →
        (13 ∣ orderOf x → orderOf x = 13) ∧ (19 ∣ orderOf x → orderOf x = 19)

theorem twE6q2_not_dvd_centralizer_of_no_order_mul {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (hb : b.Prime) (hab : Nat.Coprime a b) (hno : ∀ x : G, orderOf x ≠ a * b) {g : G}
    (hg : orderOf g = a) : ¬ b ∣ Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  intro hbdvd
  haveI : Fact b.Prime := ⟨hb⟩
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({g} : Set G))) b hbdvd
  have hmem : (y : G) ∈ Subgroup.centralizer ({g} : Set G) := y.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  have hcomm : Commute g (y : G) := hmem.symm
  have hyorder : orderOf (y : G) = b := by rw [Subgroup.orderOf_coe, hy]
  have hcop : Nat.Coprime (orderOf g) (orderOf (y : G)) := by rw [hg, hyorder]; exact hab
  exact hno (g * (y : G)) (by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hg, hyorder])

theorem exists_langSetup_of_lieModel_twistedE6
    {G : Type} [Group G] (h : LieModel G .twistedE6 0 2 1) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2) (Fr : L →+* L)
      (S : LangSetup TwistTag.E6.tag L 5), S.IsAlgebraic ∧ S.D.q = 2 ∧ (∀ c, Fr c = c ^ 2) ∧
        S.D.Φ = twistHom TwistTag.E6 L Fr ∧ Nonempty (G ≃* S.Γ) := by
  obtain ⟨hf, K, hKf, hKfin, σ0, hK, hσ0, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_lieModel h
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hbij : Function.Bijective σ0 :=
    ⟨σ0.injective, Finite.injective_iff_surjective.1 σ0.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ0 hbij
  have hσ : ∀ c, σ c = c ^ (2 ^ 1) := hσ0
  have hσσ : σ.toRingHom = σ0 := RingHom.ext fun _ => rfl
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hK']; norm_num)
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI hL : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨Fr, hFr, D, hΦ, hDq, -⟩ :=
    exists_langDatum_twistedE6 Nat.prime_two hf K hK' (1 : WeylGroup TwistTag.E6.tag)
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.E6.tag L D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    refine ⟨hDq ▸ (Nat.prime_two.isPrimePow.pow (by norm_num)), ?_⟩
    rw [hDq, pow_one]
    exact CharP.cast_eq_zero L 2
  have hpq : ¬ 5 ∣ D.q := by rw [hDq]; norm_num
  have hfin := finite_model_twistedE6 Nat.prime_two hf hK' hσ hFr D hΦ
  have hFr2 : ∀ c, Fr c = c ^ 2 := fun c => by simpa using hFr c
  have hDq2 : D.q = 2 := by simpa using hDq
  let S := D.toSetup 5 ρ hρ (by norm_num) (Or.inl le_rfl) hqpow hpq hfin
  have hSq : S.D.q = 2 := hDq2
  refine ⟨L, inferInstance, hL, inferInstance, Fr, S,
    LangSetup.isAlgebraic_of_isAlgClosure S K 2 (by rw [hK', hSq]; norm_num), hDq2, hFr2, hΦ,
    ⟨?_⟩⟩
  have e' : G ≃* twistedE6RootGroup K σ := by rw [twistedE6RootGroup, hσσ]; exact e
  exact e'.trans (twistedE6EquivΓ Nat.prime_two hf hK' hσ hFr D hΦ)

theorem twE6q2OrderThreeCentralizers_of_oddSpectrum
    (h3 : TwE6OddSpectrum) : TwE6q2OrderThreeCentralizers := by
  intro G _ _ n hG g hg
  have hn : n = 0 := ((LieModel.chevalleyExceptional_iff (by decide)).1 hG).1
  subst hn
  obtain ⟨L, _, _, _, Fr, S, hal, hq, hFr, hΦ, ⟨e⟩⟩ := exists_langSetup_of_lieModel_twistedE6 hG
  have hodd := h3 L 5 Fr S hal hq hFr hΦ
  have hspec : ∀ x : G, Odd (orderOf x) →
      (13 ∣ orderOf x → orderOf x = 13) ∧ (19 ∣ orderOf x → orderOf x = 19) := by
    intro x hx
    have := hodd (e x) (by rwa [MulEquiv.orderOf_eq e])
    rwa [MulEquiv.orderOf_eq e] at this
  refine ⟨twE6q2_not_dvd_centralizer_of_no_order_mul (a := 3) (b := 13) (by norm_num)
    (by norm_num) ?_ hg, twE6q2_not_dvd_centralizer_of_no_order_mul (a := 3) (b := 19)
    (by norm_num) (by norm_num) ?_ hg⟩
  · intro x hx
    have := (hspec x (by rw [hx]; exact ⟨19, by norm_num⟩)).1 (by rw [hx]; norm_num)
    omega
  · intro x hx
    have := (hspec x (by rw [hx]; exact ⟨28, by norm_num⟩)).2 (by rw [hx]; norm_num)
    omega

end CFSG.StandardType.TableCRes

end
