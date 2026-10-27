module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise MatrixGroups

noncomputable section

theorem burnsideA315y_pglAction_bijective (p : ℕ) [Fact p.Prime] :
    Function.Bijective (pglAction (ZMod p)) := by
  refine ⟨CFSG.RankThree.PartTwo.KFacts.pglAction_injective (K := ZMod p),
    fun α => ?_⟩
  have hcard : Nat.card (RingAut (ZMod p)) = 1 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (Fact.out : p.Prime) (ZMod p)
      (by rw [Nat.card_zmod, pow_one])).1
  haveI : Subsingleton (RingAut (ZMod p)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one
    (K := ZMod p) (α := α) (Subsingleton.elim _ _)
  exact ⟨g, hg⟩

@[expose] def burnsideA315y_pglEquiv (p : ℕ) [Fact p.Prime] :
    PGL2 (ZMod p) ≃* MulAut (PSL2 (ZMod p)) :=
  MulEquiv.ofBijective (pglAction (ZMod p)) (burnsideA315y_pglAction_bijective p)

@[expose] def burnsideA315y_autQuotCenter (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ Subgroup.center G) where
  toFun α := QuotientGroup.congr (Subgroup.center G) (Subgroup.center G) α
    ((Subgroup.characteristic_iff_map_eq.mp inferInstance) α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem burnsideA315y_autQuotCenter_mk {G : Type*} [Group G] (α : MulAut G) (x : G) :
    burnsideA315y_autQuotCenter G α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  rfl

theorem burnsideA315y_sl2_center_sq {R : Type*} [CommRing R] {z : SL(2, R)}
    (hz : z ∈ Subgroup.center (SL(2, R))) : z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem burnsideA315y_sl2Upper_pow {K : Type*} [Field K] (c : K) (n : ℕ) :
    (sl2Upper K c) ^ n = sl2Upper K (n * c) := by
  induction n with
  | zero => simp [sl2Upper_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← sl2Upper_add]
    congr 1
    push_cast
    ring

theorem burnsideA315y_sl2Lower_pow {K : Type*} [Field K] (c : K) (n : ℕ) :
    (sl2Lower K c) ^ n = sl2Lower K (n * c) := by
  induction n with
  | zero => simp [sl2Lower_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← sl2Lower_add]
    congr 1
    push_cast
    ring

theorem burnsideA315y_sl2_aut_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (α : MulAut (SL(2, ZMod p)))
    (h : ∀ x, (QuotientGroup.mk (α x) : PSL2 (ZMod p)) = QuotientGroup.mk x) : α = 1 := by
  have hcop : Nat.Coprime p 2 :=
    Nat.coprime_two_right.2 ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have key : ∀ x : SL(2, ZMod p), x ^ p = 1 → α x = x := by
    intro x hx
    have hz : (α x)⁻¹ * x ∈ Subgroup.center (SL(2, ZMod p)) := QuotientGroup.eq.mp (h x)
    set z := (α x)⁻¹ * x with hzdef
    have hαx : x = α x * z := by rw [hzdef, mul_inv_cancel_left]
    have hcomm : Commute (α x) z := Subgroup.mem_center_iff.mp hz (α x)
    have hz2 : z ^ 2 = 1 := burnsideA315y_sl2_center_sq hz
    have hzp : z ^ p = 1 := by
      have h1 : x ^ p = (α x * z) ^ p := by rw [← hαx]
      rw [hcomm.mul_pow, ← map_pow, hx, map_one, one_mul] at h1
      exact h1.symm
    have hz1 : z = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzp)
        (orderOf_dvd_of_pow_eq_one hz2))
    rw [hz1, mul_one] at hαx
    exact hαx.symm
  have hU : ∀ c : ZMod p, (sl2Upper (ZMod p) c) ^ p = 1 := fun c => by
    rw [burnsideA315y_sl2Upper_pow, ZMod.natCast_self, zero_mul, sl2Upper_zero]
  have hL : ∀ c : ZMod p, (sl2Lower (ZMod p) c) ^ p = 1 := fun c => by
    rw [burnsideA315y_sl2Lower_pow, ZMod.natCast_self, zero_mul, sl2Lower_zero]
  have hle : Subgroup.closure (Set.range (sl2Upper (ZMod p)) ∪ Set.range (sl2Lower (ZMod p))) ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact key _ (hU c)
    · exact key _ (hL c)
  rw [sl2_closure_upper_lower] at hle
  exact MulEquiv.ext fun x => hle (Subgroup.mem_top x)

variable {X : Type} [Group X] {p : ℕ} [Fact p.Prime] {K M : Subgroup X}

@[expose] def burnsideA315y_conjSL (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M)
    (hMN : M ≤ Subgroup.normalizer (K : Set X)) : ↥M →* MulAut (SL(2, ZMod p)) :=
  haveI : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMN
  (MulAut.congr ((Subgroup.subgroupOfEquivOfLe hKM).trans e)).toMonoidHom.comp MulAut.conjNormal

theorem burnsideA315y_conjSL_apply (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M)
    (hMN : M ≤ Subgroup.normalizer (K : Set X)) (m : ↥M) (x : SL(2, ZMod p)) :
    ((e.symm (burnsideA315y_conjSL e hKM hMN m x) : ↥K) : X) =
      (m : X) * (e.symm x : X) * (m : X)⁻¹ := by
  simp [burnsideA315y_conjSL, MulAut.congr_apply, MulAut.conjNormal_apply,
    Subgroup.subgroupOfEquivOfLe]

@[expose] def burnsideA315y_theta (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M)
    (hMN : M ≤ Subgroup.normalizer (K : Set X)) : ↥M →* PGL2 (ZMod p) :=
  (burnsideA315y_pglEquiv p).symm.toMonoidHom.comp
    ((burnsideA315y_autQuotCenter (SL(2, ZMod p))).comp (burnsideA315y_conjSL e hKM hMN))

theorem burnsideA315y_theta_of_mem (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M)
    (hMN : M ≤ Subgroup.normalizer (K : Set X)) (k : X) (hk : k ∈ K) :
    burnsideA315y_theta e hKM hMN ⟨k, hKM hk⟩ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (e ⟨k, hk⟩)) := by
  apply (burnsideA315y_pglEquiv p).injective
  have h1 : burnsideA315y_pglEquiv p (burnsideA315y_theta e hKM hMN ⟨k, hKM hk⟩) =
      burnsideA315y_autQuotCenter (SL(2, ZMod p))
        (burnsideA315y_conjSL e hKM hMN ⟨k, hKM hk⟩) := by
    simp [burnsideA315y_theta]
  rw [h1]
  change _ = pglAction (ZMod p) _
  rw [pglAction_toPGL]
  ext y
  induction y using QuotientGroup.induction_on with
  | H x =>
  rw [burnsideA315y_autQuotCenter_mk, MulAut.conj_apply]
  have hx : burnsideA315y_conjSL e hKM hMN ⟨k, hKM hk⟩ x = e ⟨k, hk⟩ * x * (e ⟨k, hk⟩)⁻¹ := by
    apply e.symm.injective
    apply Subtype.ext
    rw [burnsideA315y_conjSL_apply]
    simp
  rw [hx]
  rfl

theorem burnsideA315y_theta_eq_one_iff (hp2 : p ≠ 2) (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M)
    (hMN : M ≤ Subgroup.normalizer (K : Set X)) (m : ↥M) :
    burnsideA315y_theta e hKM hMN m = 1 ↔ (m : X) ∈ Subgroup.centralizer (K : Set X) := by
  have h0 : burnsideA315y_theta e hKM hMN m = 1 ↔
      burnsideA315y_autQuotCenter (SL(2, ZMod p)) (burnsideA315y_conjSL e hKM hMN m) = 1 := by
    simp [burnsideA315y_theta]
  rw [h0, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have hα : burnsideA315y_conjSL e hKM hMN m = 1 := by
      apply burnsideA315y_sl2_aut_eq_one hp2
      intro x
      have := congrArg (fun β : MulAut (PSL2 (ZMod p)) => β (QuotientGroup.mk x)) h
      simpa [burnsideA315y_autQuotCenter_mk] using this
    have h1 := burnsideA315y_conjSL_apply e hKM hMN m (e ⟨k, hk⟩)
    rw [hα] at h1
    simp only [MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    have h2 : k * (m : X) = (m : X) * k := by
      calc k * (m : X) = (m : X) * k * (m : X)⁻¹ * (m : X) := by rw [← h1]
        _ = (m : X) * k := by group
    exact h2
  · intro hm
    have hα : burnsideA315y_conjSL e hKM hMN m = 1 := by
      refine MulEquiv.ext fun x => ?_
      apply e.symm.injective
      apply Subtype.ext
      rw [burnsideA315y_conjSL_apply, MulAut.one_apply]
      have := hm (e.symm x : X) (e.symm x).2
      calc (m : X) * (e.symm x : X) * (m : X)⁻¹ = (e.symm x : X) * (m : X) * (m : X)⁻¹ := by
            rw [this]
        _ = (e.symm x : X) := by group
    rw [hα, map_one]

theorem burnsideA315y_exists_theta (hp2 : p ≠ 2) (e : ↥K ≃* SL(2, ZMod p)) (hKM : K ≤ M)
    (hMN : M ≤ Subgroup.normalizer (K : Set X)) :
    ∃ θ : ↥M →* PGL2 (ZMod p),
      (∀ (k : X) (hk : k ∈ K), θ ⟨k, hKM hk⟩ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (e ⟨k, hk⟩))) ∧
      (∀ m : ↥M, θ m = 1 ↔ (m : X) ∈ Subgroup.centralizer (K : Set X)) :=
  ⟨burnsideA315y_theta e hKM hMN, burnsideA315y_theta_of_mem e hKM hMN,
    burnsideA315y_theta_eq_one_iff hp2 e hKM hMN⟩

end

end CFSG.ASVolI
