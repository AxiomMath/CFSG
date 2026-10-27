module

public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviClass
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Lang
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Sylow
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LieType.SeitzGeneration.ExcTorusCount

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem ggTBJ_twE6_stdModel
    {K : Type} [Field K] [Finite K] {n p : ℕ} [Fact p.Prime]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* TwE6Delta.RecipeR K n)
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ₀ A) :
    ∃ (σ : K ≃+* K) (_ : ∀ c, σ c = c ^ (2 ^ n)) (E : Subgroup (twistedE6RootGroup K σ))
      (F : TwE6Frame K σ n p E) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ)
      (ψ : L' →* twistedE6RootGroup K σ)
      (σ' : Multiplicative (Fin Tag.E6.rank → ZMod p) →* L')
      (Θ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* ↥A),
      orderOf ζ = p ∧ ExcIsLongest TwistTag.E6.tag F.v ∧ Function.Injective T ∧
      (∀ t : Fin Tag.E6.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t)) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center L' ∧
      (∀ f, ψ (σ' f) = T f) ∧ ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ' f) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hψ0, hker0, hperf0, hAe, hAI, hr, h3, hsc⟩ := hA
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  have hZ : Subgroup.center (TwE6Delta.RecipeR K n) = ⊥ := TwE6Delta.center_recipeR_eq_bot hn hK
  have hIp := TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3
  have hcpL := TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3 L' ψ₀ hψ0 hker0 hperf0
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : TwE6Delta.RecipeR K n →* MulAut L',
      (∀ {e : TwE6Delta.RecipeR K n} {x : L'}, ψ₀ x = e → Λ e = MulAut.conj x) ∧
      Function.Injective Λ ∧ (∀ e l, ψ₀ (Λ e l) = e * ψ₀ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ₀ hψ0 hker0, fun hx => ReflInner.liftConj_eq hψ0 hker0 hx,
      ReflInner.liftConj_injective hψ0 hker0 hZ, ReflInner.map_liftConj_apply hψ0 hker0⟩
  have hΛn : ∀ x : L', Λ (ψ₀ x) = MulAut.conj x := fun x => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ₀ l) = ψ₀ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨l, rfl⟩ := hψ0 x
      rw [hk, hAe.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ₀ hker0 hperf0 fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E₀ : Subgroup (TwE6Delta.RecipeR K n) := A.comap Λ with hE₀
  have hΦbij : Function.Bijective (fun e : E₀ => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE₀ : Nat.card E₀ = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hE₀ab : IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe.2 _ he
  have hscE₀ : ∀ g : TwE6Delta.RecipeR K n, (∀ e ∈ E₀, g * e = e * g) → g ^ p = 1 → g ∈ E₀ := by
    intro g hg hgp
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ0 hker0 hcpL hgp
    have hfix : ∀ a ∈ A, a x = x := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E₀ := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker0 hcpL ?_ ?_ hxp
      · rw [hΛmap, hx, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hxp, map_one]
    have h1 := hsc x hfix hxp
    rw [← hΛn, hx] at h1
    exact h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ (2 ^ n) := fun c => iterateFrobeniusEquiv_def K 2 n c
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK σ.toRingHom hσ
  let E : Subgroup (twistedE6RootGroup K σ) := E₀.map e.toMonoidHom
  have hEab : IsElemAbelian p E := hE₀ab.map e.toMonoidHom
  have hcardE : Nat.card E = Nat.card A := by
    rw [Subgroup.card_map_of_injective e.injective, hcardE₀]
  have hscE : ∀ g : twistedE6RootGroup K σ, (∀ b ∈ E, g * b = b * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨g₀, rfl⟩ : ∃ g₀, e g₀ = g := ⟨e.symm g, e.apply_symm_apply g⟩
    refine Subgroup.mem_map_of_mem e.toMonoidHom (hscE₀ g₀ (fun b hb => ?_) ?_)
    · have h1 := hg (e b) (Subgroup.mem_map_of_mem e.toMonoidHom hb)
      exact e.injective (by rw [map_mul, map_mul]; exact h1)
    · exact e.injective (by rw [map_pow, hgp, map_one])
  have h3E : p ^ 3 ≤ Nat.card E := hcardE ▸ h3
  have h5E : p ^ 5 ≤ Nat.card E := hcardE ▸ hr
  obtain ⟨F, -, hv⟩ := ExcTwE6Nons.twE6SCTorusInput_nonsplit σ hp hp5 hK hσ hpq E hEab h3E h5E hscE
  have hv' : ExcIsLongest TwistTag.E6.tag F.v := hv hpq
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two hp hp2
  have hζ : ζ ^ p = 1 := hζp.pow_eq_one
  obtain ⟨T, hTinj, hTE, hT⟩ :=
    TwE6PlusRootGen.exists_twE6PlusTorus hK hσ hp5 hpq F hv' hζp.eq_orderOf.symm hζ
  let ψ : L' →* twistedE6RootGroup K σ := e.toMonoidHom.comp ψ₀
  have hψ : Function.Surjective ψ := e.surjective.comp hψ0
  have hker : ψ.ker ≤ Subgroup.center L' := by
    intro l hl
    apply hker0
    rw [MonoidHom.mem_ker] at hl ⊢
    exact e.map_eq_one_iff.mp hl
  have hV : ∀ v : Multiplicative (Fin Tag.E6.rank → ZMod p), v ^ p = 1 := by
    intro v
    apply Multiplicative.toAdd.injective
    funext j
    simp
  obtain ⟨σ', hσ', -⟩ := exists_section_of_centerPrime hp hψ hker hcpL hV T
  have hTE₀ : ∀ f, e.symm (T f) ∈ E₀ := by
    intro f
    have hf : T f ∈ E := hTE ▸ ⟨f, rfl⟩
    obtain ⟨b, hb, hbe⟩ := hf
    rw [← hbe]
    change e.symm (e b) ∈ E₀
    rw [MulEquiv.symm_apply_apply]
    exact hb
  have hψ₀σ' : ∀ f, ψ₀ (σ' f) = e.symm (T f) := by
    intro f
    rw [← hσ' f]
    exact (e.symm_apply_apply (ψ₀ (σ' f))).symm
  let θ : Multiplicative (Fin Tag.E6.rank → ZMod p) →* A :=
    { toFun := fun f => ⟨MulAut.conj (σ' f), by rw [← hΛn, hψ₀σ']; exact hTE₀ f⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun f g => Subtype.ext (by simp) }
  have hθbij : Function.Bijective θ := by
    refine ⟨fun f g hfg => ?_, fun a => ?_⟩
    · have h1 : MulAut.conj (σ' f) = MulAut.conj (σ' g) := congrArg Subtype.val hfg
      rw [← hΛn, ← hΛn, hψ₀σ', hψ₀σ'] at h1
      exact hTinj (e.symm.injective (hΛinj h1))
    · obtain ⟨b, hb⟩ := hAΛ a a.2
      have hbE : e b ∈ E := Subgroup.mem_map_of_mem e.toMonoidHom
        (show Λ b ∈ A from hb ▸ a.2)
      rw [← hTE] at hbE
      obtain ⟨f, hf⟩ := hbE
      refine ⟨f, Subtype.ext ?_⟩
      change MulAut.conj (σ' f) = (a : MulAut L')
      rw [← hΛn, hψ₀σ', hf, MulEquiv.symm_apply_apply, hb]
  let Θ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* A := MulEquiv.ofBijective θ hθbij
  exact ⟨σ, hσ, E, F, ζ, hζ, T, ψ, σ', Θ, hζp.eq_orderOf.symm, hv', hTinj, hT, hψ,
    hker, hσ', fun f => rfl⟩

theorem ggTBJ_twE6_bsModel
    {K : Type} [Field K] [Finite K] {n p : ℕ} [Fact p.Prime]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (ψ₀ : X →* TwE6Delta.RecipeR K n)
    (hA : GGTorusTBGroup p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      X ψ₀ (ggGamma X hN).range) :
    ∃ (σ : K ≃+* K) (_ : ∀ c, σ c = c ^ (2 ^ n))
      (E : Subgroup (twistedE6RootGroup K σ)) (F : TwE6Frame K σ n p E)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ)
      (ψ : X →* twistedE6RootGroup K σ)
      (s : Multiplicative (Fin Tag.E6.rank → ZMod p) →* X)
      (Θ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* (ggGamma X hN).range)
      (e : (Fin Tag.E6.rank → Multiplicative (ZMod p)) ≃*
        Multiplicative (Fin Tag.E6.rank → ZMod p))
      (ΘB : ((Fin Tag.E6.rank → Multiplicative (ZMod p)) ×
        ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* Bs),
      orderOf ζ = p ∧ ExcIsLongest TwistTag.E6.tag F.v ∧ Function.Injective T ∧
      (∀ t : Fin Tag.E6.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t)) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center X ∧
      (∀ f, ψ (s f) = T f) ∧
      (∀ f, ((Θ f : (ggGamma X hN).range) : MulAut X) = MulAut.conj (s f)) ∧
      (∀ f, e f = Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j))) ∧
      (∀ f c, ((ΘB (f, c) : Bs) : G) = ((s (e f) : X) : G) * c) ∧
      ∀ H : Subgroup G, H ≤ X →
        ggAutomizer H Bs =
          (FrameBs.sectionFrameAut (X.subtype.comp (s.comp e.toMonoidHom)) H).map
            (TypeBDatum.liftBs ΘB) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨σ, hσ, E, F, ζ, hζ, T, ψ, s, Θ, hζo, hv, hTinj, hT, hψ, hker, hs, hΘ⟩ :=
    ggTBJ_twE6_stdModel hn hK (by omega) hpq ψ₀ _ hA
  let e : (Fin Tag.E6.rank → Multiplicative (ZMod p)) ≃*
      Multiplicative (Fin Tag.E6.rank → ZMod p) :=
    (MulEquiv.piMultiplicative (fun _ : Fin Tag.E6.rank => ZMod p)).symm
  let s' : (Fin Tag.E6.rank → Multiplicative (ZMod p)) →* X := s.comp e.toMonoidHom
  let ΘA : (Fin Tag.E6.rank → Multiplicative (ZMod p)) ≃* (ggGamma X hN).range := e.trans Θ
  have hΘA : ∀ f, ((ΘA f : (ggGamma X hN).range) : MulAut X) = MulAut.conj (s' f) :=
    fun f => hΘ (e f)
  have hcp : ¬ p ∣ Nat.card (Subgroup.center X) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3 X ψ₀ hA.1 hA.2.1 hA.2.2.1
  have hZker : Subgroup.center X ≤ ψ₀.ker := MonoidHom.center_le_ker ψ₀ hA.1
    (TwE6Delta.center_recipeR_eq_bot hn hK)
  have hZ : ∀ z ∈ Subgroup.center X, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    exact eq_of_lift_pow_eq_one hp hA.2.1 hcp
      ((MonoidHom.mem_ker.mp (hZker hz)).trans (map_one ψ₀).symm) hzp (one_pow p)
  obtain ⟨ΘB, hΘB, hAut⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hN hZ s' ΘA hΘA
  exact ⟨σ, hσ, E, F, ζ, hζ, T, ψ, s, Θ, e, ΘB, hζo, hv, hTinj, hT, hψ, hker, hs,
    hΘ, fun _ => rfl, hΘB, hAut⟩

open CFSG.LieType.AlgebraicGroups in
theorem ggTBJ_twE6_bs_levi_model
    {K : Type} [Field K] [Finite K] {n p : ℕ} [Fact p.Prime]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hp5 : 5 < p) (hpq : p ∣ 2 ^ n + 1)
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (ψ₀ : X →* TwE6Delta.RecipeR K n)
    (hA : GGTorusTBGroup p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      X ψ₀ (ggGamma X hN).range)
    (y : MulAut X) (hy : y ∈ (ggGamma X hN).range) (hy1 : y ≠ 1) {J : Subgroup X}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y)) :
    ∃ (σ : K ≃+* K) (_ : ∀ c, σ c = c ^ (2 ^ n))
      (E : Subgroup (twistedE6RootGroup K σ)) (F : TwE6Frame K σ n p E)
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ)
      (ψ : X →* twistedE6RootGroup K σ)
      (s : Multiplicative (Fin Tag.E6.rank → ZMod p) →* X)
      (Θ : Multiplicative (Fin Tag.E6.rank → ZMod p) ≃* (ggGamma X hN).range)
      (e : (Fin Tag.E6.rank → Multiplicative (ZMod p)) ≃*
        Multiplicative (Fin Tag.E6.rank → ZMod p))
      (ΘB : ((Fin Tag.E6.rank → Multiplicative (ZMod p)) ×
        ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* Bs)
      (t₀ : Fin Tag.E6.rank → ZMod p)
      (i : KernelComponent (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)))
      (v : WeylGroup Tag.E6) (S : Set (Fin Tag.E6.rank)),
      orderOf ζ = p ∧ ExcIsLongest TwistTag.E6.tag F.v ∧ Function.Injective T ∧
      (∀ t : Fin Tag.E6.rank → ZMod p, ggKGTwY F (T (Multiplicative.ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t)) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center X ∧
      (∀ f, ψ (s f) = T f) ∧
      (∀ f, ((Θ f : (ggGamma X hN).range) : MulAut X) = MulAut.conj (s f)) ∧
      (∀ f, e f = Multiplicative.ofAdd (fun j => Multiplicative.toAdd (f j))) ∧
      (∀ f c, ((ΘB (f, c) : Bs) : G) = ((s (e f) : X) : G) * c) ∧
      (∀ H : Subgroup G, H ≤ X →
        ggAutomizer H Bs =
          (FrameBs.sectionFrameAut (X.subtype.comp (s.comp e.toMonoidHom)) H).map
            (TypeBDatum.liftBs ΘB)) ∧
      t₀ ≠ 0 ∧ y = MulAut.conj (s (Multiplicative.ofAdd t₀)) ∧ S ≠ Set.univ ∧
      componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i =
        (v • ·) '' parabolicRoots Tag.E6 S ∧
      (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
        ∀ r ∈ ggKGTwJ F γ, ∃ m ∈ J, ψ m = r) ∧
      ∀ t : Fin Tag.E6.rank → ZMod p,
        (∀ γ ∈ componentRoots (rootCharHom (TableBExc.E6Three.zetaVec ζ hζ t₀)) i,
          ∑ j, (γ j : ZMod p) * t j = 0) →
        ∀ x ∈ J, s (Multiplicative.ofAdd t) * x = x * s (Multiplicative.ofAdd t) := by
  classical
  have hp : p.Prime := Fact.out
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    rw [hn1, pow_one] at hpq
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpq
    omega
  obtain ⟨σ, hσ, E, F, ζ, hζ, T, ψ, s, Θ, e, ΘB, hζo, hv, hTinj, hT, hψ, hker, hs,
      hΘ, he, hΘB, hAut⟩ := ggTBJ_twE6_bsModel hn hK (by omega) hpq hBs hSC hN ψ₀ hA
  let f₀ : Multiplicative (Fin Tag.E6.rank → ZMod p) := Θ.symm ⟨y, hy⟩
  let t₀ : Fin Tag.E6.rank → ZMod p := Multiplicative.toAdd f₀
  have hft : Multiplicative.ofAdd t₀ = f₀ := rfl
  have hyf : y = MulAut.conj (s f₀) := by
    rw [← hΘ f₀, show Θ f₀ = ⟨y, hy⟩ from Θ.apply_symm_apply _]
  have ht₀ : t₀ ≠ 0 := by
    intro h
    have hf : f₀ = 1 := Multiplicative.toAdd.injective h
    apply hy1
    rw [hyf, hf, map_one, map_one]
  have hd1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t₀) ≠ 1 := by
    intro h
    have hTf : T f₀ = 1 := by
      apply ggKGTl_conj_injective F
      change ggKGTwY F (T f₀) = ggKGTwY F 1
      rw [← hft, hT, h, map_one]
    have hf : f₀ = 1 := hTinj (hTf.trans (map_one T).symm)
    exact ht₀ (congrArg Multiplicative.toAdd hf)
  have hcp : ¬p ∣ Nat.card (Subgroup.center X) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp (by omega) (by omega) X ψ₀
      hA.1 hA.2.1 hA.2.2.1
  have hkerp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    exact eq_of_lift_pow_eq_one hp hker hcp
      ((MonoidHom.mem_ker.mp hz).trans (map_one ψ).symm) hzp (one_pow p)
  have hJc : CFSG.Open.IsComponentOf J (Subgroup.centralizer {s f₀}) := by
    simpa only [hyf, ggTBJ_fixSubgroup_conj] using hJ
  have hfp : f₀ ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    funext j
    simp
  obtain ⟨i, hlower, hfix⟩ :=
    ggTBJ_twE6_class_of_central_cover hn2 hK hσ hpq F hv hζ ψ hψ hker hkerp t₀ hd1
      (a := s f₀) (by rw [← map_pow, hfp, map_one]) (by rw [hs, ← hft, hT]) hJc
  obtain ⟨v, S, hΨ, hproper⟩ :=
    exists_componentRoots_eq_smul_parabolicRoots_e6 hp5 hζo hζ t₀ i
  have hS : S ≠ Set.univ := hproper ht₀
  refine ⟨σ, hσ, E, F, ζ, hζ, T, ψ, s, Θ, e, ΘB, t₀, i, v, S, hζo, hv, hTinj, hT,
    hψ, hker, hs, hΘ, he, hΘB, hAut, ht₀, ?_, hS, hΨ, hlower, ?_⟩
  · rw [hft]
    exact hyf
  · intro t ht x hx
    exact hfix (s (Multiplicative.ofAdd t)) t (by rw [hs, hT]) ht x hx

end CFSG.StandardType

end
