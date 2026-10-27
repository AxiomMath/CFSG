module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Struct
import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorData
import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.TensorAssemble
import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.AutRankL2
import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.L2Dim
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Restrict

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris CFSG.Assembly.LowTwoRank
open scoped MatrixGroups TensorProduct
open Matrix
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

section Section

variable {G : Type} [Group G]

theorem forall_eq_one_of_comm {H : Type*} [Group H] (hG : Group.IsPerfect G) (ρ : G →* H)
    (hc : ∀ a b, ρ a * ρ b = ρ b * ρ a) : ∀ g, ρ g = 1 := by
  have hker : commutator G ≤ ρ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc a b
  intro g
  refine MonoidHom.mem_ker.1 (hker ?_)
  rw [hG.commutator_eq_top]
  trivial

theorem exists_irr_section (hG : Group.IsPerfect G) :
    ∀ (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : G →* GLV M), Module.finrank (ZMod 2) M = N → (∃ g, ρ g ≠ 1) →
      ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module (ZMod 2) Y) (_ : Finite Y)
        (σ : G →* GLV Y), Module.finrank (ZMod 2) Y ≤ N ∧ (∃ g, σ g ≠ 1) ∧
          IsIrr σ.range ⊤ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro M _ _ _ ρ hN hρ
    by_cases hirr : IsIrr ρ.range ⊤
    · exact ⟨M, inferInstance, inferInstance, inferInstance, ρ, hN.le, hρ, hirr⟩
    · have hMnt : Nontrivial M := by
        obtain ⟨g, hg⟩ := hρ
        by_contra hM
        rw [not_nontrivial_iff_subsingleton] at hM
        exact hg (LinearEquiv.ext fun x => Subsingleton.elim _ _)
      have hbt : (⊥ : Submodule (ZMod 2) M) < ⊤ := by
        have := (Submodule.nontrivial_iff (ZMod 2)).2 hMnt
        exact bot_lt_top
      have hinvtop : Invariant ρ.range (⊤ : Submodule (ZMod 2) M) :=
        fun _ _ _ _ => Submodule.mem_top
      obtain ⟨J, hJinv, hJ⟩ : ∃ J : Submodule (ZMod 2) M, Invariant ρ.range J ∧ J ≠ ⊥ ∧ J ≠ ⊤ := by
        by_contra hcon
        push Not at hcon
        refine hirr ⟨hinvtop, hbt, fun J hJ _ _ => ?_⟩
        by_cases hJb : J = ⊥
        · exact Or.inl hJb
        · exact Or.inr (hcon J hJ hJb)
      have hJle : Module.finrank (ZMod 2) J < N := by
        rw [← hN]; exact Submodule.finrank_lt hJ.2
      have hsum := Submodule.finrank_quotient_add_finrank J
      have : Finite (M ⧸ J) := Quotient.finite _
      have hJpos : 0 < Module.finrank (ZMod 2) J := by
        have : Module.Finite (ZMod 2) J := Module.Finite.of_finite
        have : Nontrivial J := Submodule.nontrivial_iff_ne_bot.2 hJ.1
        exact Module.finrank_pos
      have hQlt : Module.finrank (ZMod 2) (M ⧸ J) < N := by omega
      let σ₁ : G →* GLV J :=
        (IrreducibleModulesAndBounds.restrictHom ρ.range J hJinv).comp ρ.rangeRestrict
      let σ₂ : G →* GLV (M ⧸ J) :=
        (IrreducibleModulesAndBounds.quotientHom ρ.range J hJinv).comp ρ.rangeRestrict
      have hσ₁ : ∀ g (j : J), ((σ₁ g j : J) : M) = ρ g j := fun g j => by
        simp [σ₁, IrreducibleModulesAndBounds.restrictHom_apply]
      have hσ₂ : ∀ g (x : M), σ₂ g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
        fun g x => by simp [σ₂, IrreducibleModulesAndBounds.quotientHom_apply]
      by_cases h1 : ∃ g, σ₁ g ≠ 1
      · obtain ⟨Y, i1, i2, i3, σ, h1', h2', h3'⟩ := ih _ hJle J σ₁ rfl h1
        exact ⟨Y, i1, i2, i3, σ, h1'.trans hJle.le, h2', h3'⟩
      by_cases h2 : ∃ g, σ₂ g ≠ 1
      · obtain ⟨Y, i1, i2, i3, σ, h1', h2', h3'⟩ := ih _ hQlt (M ⧸ J) σ₂ rfl h2
        exact ⟨Y, i1, i2, i3, σ, h1'.trans hQlt.le, h2', h3'⟩
      exfalso
      push Not at h1 h2
      have hfix : ∀ g, ∀ j ∈ J, ρ g j = j := fun g j hj => by
        have := congrArg (fun f : GLV J => ((f ⟨j, hj⟩ : J) : M)) (h1 g)
        simpa [hσ₁] using this
      have hdiff : ∀ g x, ρ g x - x ∈ J := fun g x => by
        have := congrArg (fun f : GLV (M ⧸ J) => f (Submodule.Quotient.mk x)) (h2 g)
        simp only [hσ₂, LinearEquiv.coe_one, id_eq] at this
        exact (Submodule.Quotient.eq J).1 this
      have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := fun a b => by
        ext x
        simp only [LinearEquiv.mul_apply]
        obtain ⟨u, hu, huJ⟩ : ∃ u, ρ b x = x + u ∧ u ∈ J := ⟨ρ b x - x, by abel, hdiff b x⟩
        obtain ⟨v, hv, hvJ⟩ : ∃ v, ρ a x = x + v ∧ v ∈ J := ⟨ρ a x - x, by abel, hdiff a x⟩
        rw [hu, hv, map_add, map_add, hfix a u huJ, hfix b v hvJ, hu, hv]
        abel
      obtain ⟨g, hg⟩ := hρ
      exact hg (forall_eq_one_of_comm hG ρ hcomm g)

theorem two_mul_le_finrank_of_ne_one {n : ℕ} (hn : 2 ≤ n) [IsSimpleGroup G]
    (hG : Group.IsPerfect G) (eG : G ≃* SL(2, GaloisField 2 n)) {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] (ρ : G →* GLV M) (hρ : ∃ g, ρ g ≠ 1) :
    2 * n ≤ Module.finrank (ZMod 2) M := by
  obtain ⟨Y, _, _, _, σ, hle, hσ, hirr⟩ := exists_irr_section hG _ M ρ rfl hρ
  have hker : σ.ker = ⊥ := by
    have := σ.normal_ker
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := hσ
      exact hg (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))
  have hinj : Function.Injective σ := (MonoidHom.ker_eq_bot_iff _).1 hker
  have := two_mul_le_finrank_of_irr hn σ.range ((MonoidHom.ofInjective hinj).symm.trans eG) hirr
  omega

@[expose] def zmodEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ZMod 2) M]
    [Module (ZMod 2) N] (e : M ≃+ N) : M ≃ₗ[ZMod 2] N :=
  { toLinearMap := e.toAddMonoidHom.toZModLinearMap 2, invFun := e.symm, left_inv := e.left_inv,
    right_inv := e.right_inv }

theorem zmodEquiv_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ZMod 2) M]
    [Module (ZMod 2) N] (e : M ≃+ N) (x : M) : zmodEquiv e x = e x := rfl

theorem two_pow_le_natCard_of_ne_one {n : ℕ} (hn : 2 ≤ n) [IsSimpleGroup G]
    (hG : Group.IsPerfect G) (eG : G ≃* SL(2, GaloisField 2 n)) {F : Type} [Field F]
    [Algebra (ZMod 2) F] {W : Type} [AddCommGroup W] [Module F W] [Finite W]
    (ρ : G →* (W ≃ₗ[F] W)) (hρ : ∃ g, ρ g ≠ 1) : 2 ^ (2 * n) ≤ Nat.card W := by
  have hchar : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have h2 : ∀ x : W, (2 : ℕ) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  let _ : Module (ZMod 2) W := AddCommGroup.zmodModule h2
  let ρ' : G →* GLV W :=
    { toFun := fun g => zmodEquiv (ρ g).toAddEquiv
      map_one' := by ext x; simp [zmodEquiv_apply]
      map_mul' := fun a b => by ext x; simp [zmodEquiv_apply] }
  have hρ' : ∃ g, ρ' g ≠ 1 := by
    obtain ⟨g, hg⟩ := hρ
    refine ⟨g, fun h => hg ?_⟩
    ext x
    exact congrArg (fun f : GLV W => f x) h
  have := two_mul_le_finrank_of_ne_one hn hG eG ρ' hρ'
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  rw [Nat.card_zmod] at hcard
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) this

theorem forall_eq_one_of_finrank_eq_one (hG : Group.IsPerfect G) {F : Type} [Field F]
    {W : Type} [AddCommGroup W] [Module F W] (ρ : G →* (W ≃ₗ[F] W))
    (h1 : Module.finrank F W = 1) : ∀ g, ρ g = 1 := by
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.1 h1
  refine forall_eq_one_of_comm hG ρ fun a b => ?_
  ext w
  obtain ⟨c, rfl⟩ := hv w
  obtain ⟨α, hα⟩ := hv (ρ a v)
  obtain ⟨β, hβ⟩ := hv (ρ b v)
  simp only [LinearEquiv.mul_apply, map_smul, ← hα, ← hβ]
  rw [smul_comm β α v]

theorem tensor_numerics {n : ℕ} (hn : 2 ≤ n) {G₀ G₁ : Type} [Group G₀] [Group G₁]
    [IsSimpleGroup G₀] [IsSimpleGroup G₁] (hG₀ : Group.IsPerfect G₀) (hG₁ : Group.IsPerfect G₁)
    (e₀ : G₀ ≃* SL(2, GaloisField 2 n)) (e₁ : G₁ ≃* SL(2, GaloisField 2 n))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {V₀ V₁ : Type} [AddCommGroup V₀] [AddCommGroup V₁] [Module F V₀] [Module F V₁]
    [Module.Finite F V₀] [Module.Finite F V₁] [Nontrivial V₀] [Nontrivial V₁]
    (ρ₀ : G₀ →* (V₀ ≃ₗ[F] V₀)) (ρ₁ : G₁ →* (V₁ ≃ₗ[F] V₁))
    (hρ₀ : ∃ g, ρ₀ g ≠ 1) (hρ₁ : ∃ g, ρ₁ g ≠ 1) (e : V ≃+ V₀ ⊗[F] V₁) {m : ℕ} (hm : m ≤ 2 * n)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1)) :
    Module.finrank F V₀ = 2 ∧ Module.finrank F V₁ = 2 ∧ Nat.card F = 2 ^ n ∧
      Module.finrank (ZMod 2) V = 4 * n := by
  have : Finite V₀ := Module.finite_of_finite F
  have : Finite V₁ := Module.finite_of_finite F
  have hF2 : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rwa [Nat.card_zmod] at this
  set ε := Module.finrank (ZMod 2) F with hε
  set k := Module.finrank F V₀ with hk
  set t := Module.finrank F V₁ with ht
  set d := Module.finrank (ZMod 2) V with hdd
  have hV : Nat.card V = 2 ^ d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at this
  have hV0 : Nat.card V₀ = 2 ^ (ε * k) := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := V₀), hF2, ← pow_mul]
  have hV1 : Nat.card V₁ = 2 ^ (ε * t) := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := V₁), hF2, ← pow_mul]
  have hVT : Nat.card (V₀ ⊗[F] V₁) = 2 ^ (ε * (k * t)) := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := V₀ ⊗[F] V₁), hF2, ← pow_mul,
      Module.finrank_tensorProduct]
  have hdim : d = ε * (k * t) := by
    have h1 : Nat.card V = Nat.card (V₀ ⊗[F] V₁) := Nat.card_congr e.toEquiv
    rw [hV, hVT] at h1
    exact Nat.pow_right_injective le_rfl h1
  have hk1 : 1 ≤ k := Module.finrank_pos
  have ht1 : 1 ≤ t := Module.finrank_pos
  have hk0 : k ≠ 1 := fun h1 => by
    obtain ⟨g, hg⟩ := hρ₀
    exact hg (forall_eq_one_of_finrank_eq_one hG₀ ρ₀ h1 g)
  have ht0 : t ≠ 1 := fun h1 => by
    obtain ⟨g, hg⟩ := hρ₁
    exact hg (forall_eq_one_of_finrank_eq_one hG₁ ρ₁ h1 g)
  have hek : 2 * n ≤ ε * k := by
    have := two_pow_le_natCard_of_ne_one hn hG₀ e₀ ρ₀ hρ₀
    rw [hV0] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have het : 2 * n ≤ ε * t := by
    have := two_pow_le_natCard_of_ne_one hn hG₁ e₁ ρ₁ hρ₁
    rw [hV1] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hdle : d ≤ 4 * n + 2 := by omega
  have hd1 : 2 * n * t ≤ d := by
    rw [hdim]
    calc 2 * n * t ≤ (ε * k) * t := Nat.mul_le_mul_right _ hek
      _ = ε * (k * t) := by ring
  have hd2 : 2 * n * k ≤ d := by
    rw [hdim]
    calc 2 * n * k ≤ (ε * t) * k := Nat.mul_le_mul_right _ het
      _ = ε * (k * t) := by ring
  have ht2 : t ≤ 2 := by
    by_contra hcon
    have : 2 * n * 3 ≤ 2 * n * t := Nat.mul_le_mul_left _ (by omega)
    omega
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have : 2 * n * 3 ≤ 2 * n * k := Nat.mul_le_mul_left _ (by omega)
    omega
  have hk' : k = 2 := by omega
  have ht' : t = 2 := by omega
  rw [hk'] at hdim hek
  rw [ht'] at hdim het
  refine ⟨hk', ht', ?_, ?_⟩
  · have : ε = n := by omega
    rw [hF2, this]
  · omega
end Section

@[expose] noncomputable def slRingEquiv {d : ℕ} {K K' : Type} [Field K] [Field K'] (σ : K ≃+* K') :
    SL(d, K) ≃* SL(d, K') :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (σ : K →+* K'))
    (Matrix.SpecialLinearGroup.map (σ.symm : K' →+* K))
    (by ext A i j; exact σ.symm_apply_apply _) (by ext A i j; exact σ.apply_symm_apply _)

@[expose] noncomputable def statedSLEquiv {d : ℕ} {K K' : Type} [Field K] [Field K']
    (σ : K ≃+* K') :
    StatedSL d K ≃* StatedSL d K' :=
  (specialLinearGroupEquivStatedSL d K).symm.trans
    ((slRingEquiv σ).trans (specialLinearGroupEquivStatedSL d K'))

theorem statedSLEquiv_coe {d : ℕ} {K K' : Type} [Field K] [Field K'] (σ : K ≃+* K')
    (x : StatedSL d K) (i j : Fin d) :
    (((statedSLEquiv σ x : StatedSL d K') : GL (Fin d) K') : Matrix (Fin d) (Fin d) K') i j =
      σ (((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j) := by
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL d K).surjective x
  simp only [statedSLEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    specialLinearGroupEquivStatedSL_coe]
  rfl

theorem IsTensorModel.of_ringEquiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {d : ℕ}
    {K K' : Type} [Field K] [Field K']
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) K'] (σ : K ≃+* K') {H : Subgroup (GLV V)}
    (h : IsTensorModel d K H) : IsTensorModel d K' H := by
  obtain ⟨φ, ψ, hψ⟩ := h
  refine ⟨φ.trans (MulEquiv.prodCongr (statedSLEquiv σ) (statedSLEquiv σ)),
    ψ.trans (zmodEquiv (RingEquiv.mapMatrix (m := Fin d) σ).toAddEquiv), fun γ v => ?_⟩
  have hmap : ∀ x : StatedSL d K, (((statedSLEquiv σ x : StatedSL d K') : GL (Fin d) K') :
      Matrix (Fin d) (Fin d) K') = (((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).map σ :=
    fun x => by ext i j; exact statedSLEquiv_coe σ x i j
  have hp1 : ∀ y : ↥(StatedSL d K) × ↥(StatedSL d K),
      ((MulEquiv.prodCongr (statedSLEquiv σ) (statedSLEquiv σ)) y).1 = statedSLEquiv σ y.1 :=
    fun _ => rfl
  have hp2 : ∀ y : ↥(StatedSL d K) × ↥(StatedSL d K),
      ((MulEquiv.prodCongr (statedSLEquiv σ) (statedSLEquiv σ)) y).2 = statedSLEquiv σ y.2 :=
    fun _ => rfl
  simp only [LinearEquiv.trans_apply, zmodEquiv_apply, MulEquiv.trans_apply, hp1, hp2, hmap, hψ]
  simp [Matrix.transpose_map]

theorem statedScalars_sl2_eq_bot {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf
      (StatedSL 2 K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

theorem psl2_facts
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) {n : ℕ}
    (hS : IsPSL 2 2 n (X ⧸ Subgroup.center X)) :
    Subgroup.center X = ⊥ ∧ Nonempty (X ≃* SL(2, GaloisField 2 n)) ∧ IsSimpleGroup X := by
  have hZ : Subgroup.center X = ⊥ := by
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := n)
      (by rw [← Nat.card_eq_fintype_card, hK])
    have : Group.IsPerfect X := ⟨hq.1⟩
    obtain ⟨φ, -, -, hD⟩ := CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map
      (K := K) (n := 2) le_rfl hodd e
    rw [← hD, statedScalars_sl2_eq_bot, Subgroup.map_bot]
  obtain ⟨e⟩ := L2.nonempty_mulEquiv_sl2 hS
  let q : X ≃* (X ⧸ Subgroup.center X) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact ⟨hZ, ⟨q.trans e⟩, by have := hq.2; exact q.isSimpleGroup⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Γ A L L₂ : Subgroup (GLV V)} {m : ℕ}

theorem Setting.tensor15
    (h : Setting Γ A L L₂ m) {n : ℕ} (hn : 2 ≤ n)
    (hS : IsPSL 2 2 n (↥L ⧸ Subgroup.center ↥L)) :
    Module.finrank (ZMod 2) V = 4 * n ∧ 2 * n ≤ m + 1 ∧ m ≤ 2 * n ∧
      IsTensorModel 2 (GaloisField 2 n) (L ⊔ L₂) := by
  have hq : CFSG.Open.IsQuasisimple ↥L := h.hyp.L_comp.2.2
  have hq₂ : CFSG.Open.IsQuasisimple ↥L₂ := h.comp₂.2.2
  have hfin : Finite (GLV V) :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.finite_GLV_of_finite (V := V)
  obtain ⟨hZ, ⟨eL⟩, hsimp⟩ := psl2_facts hq h.centerL_odd hS
  obtain ⟨φ, -⟩ := h.qe
  have hsimp₂ : IsSimpleGroup ↥L₂ := φ.symm.isSimpleGroup
  let eL₂ : ↥L₂ ≃* SL(2, GaloisField 2 n) := φ.symm.trans eL
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hperf₂ : Group.IsPerfect ↥L₂ := ⟨hq₂.1⟩
  have hm : m ≤ 2 * n :=
    h.m_le_two_mul eL (r := n) (by omega) (card_elemAbelian_mulAut_sl2 hn (MulEquiv.refl _))
  have := h.nontrivial_V
  obtain ⟨F, _, _, _, V₀, V₁, _, _, _, _, _, _, ρ₀, ρ₁, e, _, _, he₀, he₁, -, -⟩ :=
    exists_tensorData h.comm h.hyp.H_irr
  have hρ₀ : ∃ g, ρ₀ g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥L)
    refine hg (Subtype.ext (LinearEquiv.ext fun v => e.injective ?_))
    have h1 : ((1 : V₀ ≃ₗ[F] V₀) : V₀ →ₗ[F] V₀) = LinearMap.id := rfl
    rw [he₀, hcon g, h1, TensorProduct.map_id]
    rfl
  have hρ₁ : ∃ g, ρ₁ g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥L₂)
    refine hg (Subtype.ext (LinearEquiv.ext fun v => e.injective ?_))
    have h1 : ((1 : V₁ ≃ₗ[F] V₁) : V₁ →ₗ[F] V₁) = LinearMap.id := rfl
    rw [he₁, hcon g, h1, TensorProduct.map_id]
    rfl
  obtain ⟨hk, ht, hcardF, hdim⟩ := tensor_numerics hn hperf hperf₂ eL eL₂ ρ₀ ρ₁ hρ₀ hρ₁ e hm
    h.hyp.bound
  have hinj₀ : Function.Injective ρ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ₀.ker with h0 | h0
    · exact h0
    · obtain ⟨g, hg⟩ := hρ₀
      exact absurd (MonoidHom.mem_ker.1 (h0 ▸ Subgroup.mem_top g)) hg
  have hinj₁ : Function.Injective ρ₁ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ₁.ker with h0 | h0
    · exact h0
    · obtain ⟨g, hg⟩ := hρ₁
      exact absurd (MonoidHom.mem_ker.1 (h0 ▸ Subgroup.mem_top g)) hg
  have hinf : L ⊓ L₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxL₂⟩
    have hc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (h.comm g g.2 x hxL₂)
    rw [hZ, Subgroup.mem_bot] at hc
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hc)
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hFcard : Fintype.card F = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF,
      GaloisField.card 2 n (by omega)]
  let σ : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq hFcard
  let θ : StatedSL 2 (GaloisField 2 n) ≃* StatedSL 2 F := statedSLEquiv σ.symm
  have hcL : Nat.card ↥L = Nat.card ↥(StatedSL 2 F) :=
    Nat.card_congr (eL.trans ((specialLinearGroupEquivStatedSL 2 _).trans θ)).toEquiv
  have hcL₂ : Nat.card ↥L₂ = Nat.card ↥(StatedSL 2 F) :=
    Nat.card_congr (eL₂.trans ((specialLinearGroupEquivStatedSL 2 _).trans θ)).toEquiv
  refine ⟨hdim, by have := h.hyp.bound; omega, hm, ?_⟩
  exact IsTensorModel.of_ringEquiv σ (isTensorModel_of_tensorData h.comm hinf ρ₀ ρ₁ e he₀ he₁
    hk ht hperf hperf₂ hcL hcL₂ hinj₀ hinj₁)

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
