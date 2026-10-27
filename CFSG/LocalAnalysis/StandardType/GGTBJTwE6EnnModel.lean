module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Row
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelE6Cover
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt

theorem ggTwE6_ker_center_recipe {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : ¬ 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* TwE6Delta.RecipeR K n) (hψ0 : Function.Surjective ψ₀)
    (hker0 : ψ₀.ker ≤ Subgroup.center L') (hperf0 : commutator L' = ⊤) :
    ψ₀.ker = ⊥ ∧ Subgroup.center L' = ⊥ := by
  classical
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  have hcen : Subgroup.center (twistedE6Group 2 n) = ⊥ := by
    have hcard : Nat.card (Subgroup.center (twistedE6Group 2 n)) = Nat.gcd 3 (2 ^ n + 1) :=
      (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n)
        (q := 2 ^ n) (CFSG.LieType.Universal.card_galoisField_two_mul 2 n (by omega))
        (fun c => by rw [frobQ_apply])).1
    have h1 : Nat.gcd 3 (2 ^ n + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    exact Subgroup.eq_bot_of_card_eq _ (hcard.trans h1)
  obtain ⟨π, φ, hπs, hπk, hφs, hψφ, -, -⟩ :=
    exists_cover_phi_recipe_twE6 hn hK L' ψ₀ hψ0 hker0 hperf0
  have hπinj : Function.Injective π :=
    (MonoidHom.ker_eq_bot_iff π).1 (eq_bot_iff.2 (hπk.trans hcen.le))
  have hker1 : ψ₀.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hφs x
    have h1 : π y = 1 := by rw [← hψφ]; exact hx
    have h2 : y = 1 := hπinj (by rw [h1, map_one])
    rw [h2, map_one]
    exact Subgroup.one_mem _
  refine ⟨hker1, ?_⟩
  have hψ₀inj : Function.Injective ψ₀ := (MonoidHom.ker_eq_bot_iff ψ₀).1 hker1
  rw [eq_bot_iff]
  intro x hx
  have hxz : ψ₀ x ∈ Subgroup.center (TwE6Delta.RecipeR K n) := by
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨l, rfl⟩ := hψ0 r
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx l]
  rw [TwE6Delta.center_recipeR_eq_bot (by omega) hK, Subgroup.mem_bot] at hxz
  have : x = 1 := hψ₀inj (by rw [hxz, map_one])
  rw [this]
  exact Subgroup.one_mem _

theorem ggTwE6_center_eq_bot {G : Type} [Group G] [Finite G] {X : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (h3 : ¬ 3 ∣ 2 ^ n + 1) {P : LargeEvenMarkProp ↥X}
    (hP : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* R), P lab R I F θ → lab = ⟨.twE6, 0, n⟩)
    (hmark : LargeEvenMarking ↥X P) : Subgroup.center ↥X = ⊥ := by
  have hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab = ⟨.twE6, 0, n⟩ →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ₀ : L' →* R), Function.Surjective ψ₀ →
          ψ₀.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Subgroup.center L' = ⊥) := by
    intro lab _ hlabeq
    subst hlabeq
    refine nbrC_labelAll_guard ?_
    exact TwE6Delta.labelAll (Q := fun R _ _ => ∀ (L' : Type) [Group L'] [Finite L']
        (ψ₀ : L' →* R), Function.Surjective ψ₀ → ψ₀.ker ≤ Subgroup.center L' →
          commutator L' = ⊤ → Subgroup.center L' = ⊥) rfl
      fun K _ _ hK L' _ _ ψ₀ hψ0 hker0 hperf0 =>
        (ggTwE6_ker_center_recipe hn hK h3 ψ₀ hψ0 hker0 hperf0).2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => lab = (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (P' := fun R _ I _ => ∀ (L' : Type) [Group L'] [Finite L'] (ψ₀ : L' →* R),
      Function.Surjective ψ₀ → ψ₀.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Subgroup.center L' = ⊥) hall hP hmark
  obtain ⟨R, _, I, F, -, -, θ, -, hCen⟩ := largeEvenRawDatum_exists hraw
  exact hCen ↥X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hXc

@[expose] def GGTwE6ModelAt (p n : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ₀ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p 5 R I L' ψ₀ A →
      ∃ (Kf : Type) (_ : Field Kf) (_ : Finite Kf) (σ : Kf ≃+* Kf), Nat.card Kf = (2 ^ n) ^ 2 ∧
        (∀ c, σ c = c ^ (2 ^ n)) ∧
        ∃ (e : L' ≃* ↥(twistedE6RootGroup Kf σ)) (E : Subgroup ↥(twistedE6RootGroup Kf σ)),
          IsElemAbelian p E ∧ p ^ 5 ≤ Nat.card E ∧
          (∀ g : ↥(twistedE6RootGroup Kf σ), (∀ b ∈ E, g * b = b * g) → g ^ p = 1 → g ∈ E) ∧
          A.map (MulAut.congr e).toMonoidHom =
            E.map (MulAut.conj : ↥(twistedE6RootGroup Kf σ) →* MulAut ↥(twistedE6RootGroup Kf σ)) ∧
          Subgroup.center L' = ⊥

theorem ggTwE6ModelAt_recipe {K : Type} [Field K] [Finite K] {n p : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    GGTwE6ModelAt p n (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  intro L' _ _ ψ₀ A hA
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hψ0, hker0, hperf0, hAe, hAI, hr, -, hsc⟩ := hA
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  have hψ₀inj : Function.Injective ψ₀ := by
    obtain ⟨hker1, -⟩ := ggTwE6_ker_center_recipe hn hK h3 ψ₀ hψ0 hker0 hperf0
    exact (MonoidHom.ker_eq_bot_iff ψ₀).1 hker1
  have hZL : Subgroup.center L' = ⊥ :=
    (ggTwE6_ker_center_recipe hn hK h3 ψ₀ hψ0 hker0 hperf0).2
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hE₀ab, hcardE₀, hE₀A, hscE₀⟩ :=
    exists_innerModel_recipe_twE6 (p := p) (n := n) (K := K) hp (by omega) hK
      (TwE6Delta.ggOutdiagPrime_twE6 (by omega) hK hp hp3)
      (TwE6Delta.ggCenterPrime_twE6 (by omega) hK hp hp2 hp3) ψ₀ hψ0 hker0 hperf0 hAe hAI hsc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ (2 ^ n) := fun c => iterateFrobeniusEquiv_def K 2 n c
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (by omega) hK σ.toRingHom hσ
  set E₀ : Subgroup (TwE6Delta.RecipeR K n) := A.comap Λ with hE₀
  let E : Subgroup ↥(twistedE6RootGroup K σ) := E₀.map e.toMonoidHom
  have hEab : IsElemAbelian p E := hE₀ab.map e.toMonoidHom
  have hcardE : Nat.card E = Nat.card A := by
    rw [Subgroup.card_map_of_injective e.injective, hcardE₀]
  have hscE : ∀ g : ↥(twistedE6RootGroup K σ), (∀ b ∈ E, g * b = b * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨g₀, rfl⟩ : ∃ g₀, e g₀ = g := ⟨e.symm g, e.apply_symm_apply g⟩
    refine Subgroup.mem_map_of_mem e.toMonoidHom (hscE₀ g₀ (fun b hb => ?_) ?_)
    · have h1 := hg (e b) (Subgroup.mem_map_of_mem e.toMonoidHom hb)
      exact e.injective (by rw [map_mul, map_mul]; exact h1)
    · exact e.injective (by rw [map_pow, hgp, map_one])
  let ψ : L' →* ↥(twistedE6RootGroup K σ) := e.toMonoidHom.comp ψ₀
  have hψbij : Function.Bijective ψ := e.bijective.comp ⟨hψ₀inj, hψ0⟩
  let eL : L' ≃* ↥(twistedE6RootGroup K σ) := MulEquiv.ofBijective ψ hψbij
  have heL : ∀ x, eL x = e (ψ₀ x) := fun x => rfl
  have hcomp : (MulAut.congr eL).toMonoidHom.comp Λ =
      (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).comp
        e.toMonoidHom := by
    refine MonoidHom.ext fun r => MulEquiv.ext fun l' => ?_
    obtain ⟨l, rfl⟩ := eL.surjective l'
    change eL (Λ r (eL.symm (eL l))) = e r * eL l * (e r)⁻¹
    rw [MulEquiv.symm_apply_apply]
    simp only [heL, hΛmap, map_mul, map_inv]
  have hAE : A.map (MulAut.congr eL).toMonoidHom =
      E.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)) := by
    calc A.map (MulAut.congr eL).toMonoidHom
        = ((A.comap Λ).map Λ).map (MulAut.congr eL).toMonoidHom := by rw [hE₀A]
      _ = (A.comap Λ).map ((MulAut.congr eL).toMonoidHom.comp Λ) := Subgroup.map_map _ _ _
      _ = (A.comap Λ).map ((MulAut.conj : ↥(twistedE6RootGroup K σ) →*
            MulAut ↥(twistedE6RootGroup K σ)).comp e.toMonoidHom) := by rw [hcomp]
      _ = E.map (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
            MulAut ↥(twistedE6RootGroup K σ)) := (Subgroup.map_map _ _ _).symm
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, eL, E, hEab, by rw [hcardE]; exact hr, hscE,
    hAE, hZL⟩

theorem ggTwE6_model_of_innerDiag (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hI : GGInnerDiagOn Bs X) (hp5 : 5 ≤ p) {n : ℕ} (hpq : p ∣ 2 ^ n + 1)
    (h3 : ¬ 3 ∣ 2 ^ n + 1) (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hcard : commutator ↥X = ⊤ → ∀ {R : Type} [Group R]
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      GGTorusLift p 5 R →
        p ^ 5 ≤ Nat.card ↥(ggGamma X hN).range ∧ p ^ 3 ≤ Nat.card ↥(ggGamma X hN).range)
    {r : ℕ} (hr6 : r ≤ 6) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F ≃+* F) (_ : Nat.card F = (2 ^ n) ^ 2) (_ : ∀ c, σ c = c ^ 2 ^ n)
      (e : ↥X ≃* ↥(twistedE6RootGroup F σ)) (E : Subgroup ↥(twistedE6RootGroup F σ)),
      Subgroup.center ↥X = ⊥ ∧ IsElemAbelian p E ∧ p ^ r ≤ Nat.card E ∧
      (∀ g : ↥(twistedE6RootGroup F σ), (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : ↥(twistedE6RootGroup F σ) →* MulAut ↥(twistedE6RootGroup F σ)) := by
  classical
  have hp : p.Prime := Fact.out
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ n := hΛ.1
    by_contra hn
    have : n = 1 := by omega
    subst this
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  have hmark := ggInnerDiagOn_relabel hRig hI hΛ hX
  have hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab = ⟨.twE6, 0, n⟩ →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard
        fun R _ I _ => GGTorusLift p 5 R ∧ GGTwE6ModelAt p n R I) := by
    intro lab hlab hlabeq
    subst hlabeq
    refine nbrC_labelAll_guard ?_
    have h1 := largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨rfl, hpq⟩
    have h2 : LargeEvenLabelAll (⟨.twE6, 0, n⟩ : LargeEvenLabel)
        fun R _ I _ => GGTwE6ModelAt p n R I :=
      TwE6Delta.labelAll rfl fun K _ _ hK => ggTwE6ModelAt_recipe hn hK hp5 hpq h3
    refine (largeEvenLabelAll_and h1 h2).mono fun _ _ _ _ ⟨hl, hw⟩ => ⟨?_, hw⟩
    rwa [TwE6Delta.liftRank_of_ne (by omega)] at hl
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => lab = (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (P' := fun R _ I _ => GGTorusLift p 5 R ∧ GGTwE6ModelAt p n R I) hall
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, Fm, -, -, θ, ⟨-, hBsN, h3I⟩, hlift, hModel⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  obtain ⟨hr, h3'⟩ := hcard hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3'
  obtain ⟨Kf, _, _, σ, hK, hσ, e, E, hEab, h5E, hsc, hAE, hZ⟩ := hModel X (ggQuotHom θ) _ hTB
  have hcardE : Nat.card E = p ^ 6 := by
    obtain ⟨Lf, _, ζ, hζ, ι₀, nk, m, wt, -, hinj, hrange, -⟩ :=
      ggTwE6_leviFrame hn hK hp5 hpq hσ E hEab h5E hsc
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  exact ⟨hBsN, Kf, inferInstance, inferInstance, σ, hK, hσ, e, E, hZ, hEab,
    (Nat.pow_le_pow_right hp.pos hr6).trans hcardE.ge, hsc, hAE⟩

theorem ggTwE6Enn_model_L (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F ≃+* F) (_ : Nat.card F = (2 ^ n) ^ 2) (_ : ∀ c, σ c = c ^ 2 ^ n)
      (e : ↥L ≃* ↥(twistedE6RootGroup F σ)) (E : Subgroup ↥(twistedE6RootGroup F σ)),
      Subgroup.center ↥L = ⊥ ∧ IsElemAbelian p E ∧ p ^ 5 ≤ Nat.card E ∧
      (∀ g : ↥(twistedE6RootGroup F σ), (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma L hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : ↥(twistedE6RootGroup F σ) →* MulAut ↥(twistedE6RootGroup F σ)) := by
  obtain ⟨-, hBs, -, -, -⟩ := hH.1.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  exact ggTwE6_model_of_innerDiag hRig hBs hSC hH.2.2.1.1 hp5 hpn h3 hΛ hL
    (fun hXc {R} [Group R] θ hN hlift => card_range_ggGamma_bstar_ge hH.1 hXc θ hN hlift)
    (by norm_num)

theorem ggTwE6Enn_model_K (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F ≃+* F) (_ : Nat.card F = (2 ^ n) ^ 2) (_ : ∀ c, σ c = c ^ 2 ^ n)
      (e : ↥K ≃* ↥(twistedE6RootGroup F σ)) (E : Subgroup ↥(twistedE6RootGroup F σ)),
      Subgroup.center ↥K = ⊥ ∧ IsElemAbelian p E ∧ p ^ 5 ≤ Nat.card E ∧
      (∀ g : ↥(twistedE6RootGroup F σ), (∀ c ∈ E, g * c = c * g) → g ^ p = 1 → g ∈ E) ∧
      (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : ↥(twistedE6RootGroup F σ) →* MulAut ↥(twistedE6RootGroup F σ)) := by
  obtain ⟨-, hBs, -, -, -⟩ := hH.1.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  exact ggTwE6_model_of_innerDiag hRig hBs hSC (hH.2.2.1.2 y K hH.2.2.2.2.1) hp5 hpn h3 hΛ hK
    (fun hXc {R} [Group R] θ hN hlift =>
      ⟨pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hH.2.2.2.2.1 hXc θ hN hlift,
        pow_three_le_card_range_ggGamma_bstar hH.1 hH.2.2.2.2.1 hN⟩)
    (by norm_num)

end CFSG.StandardType

end
