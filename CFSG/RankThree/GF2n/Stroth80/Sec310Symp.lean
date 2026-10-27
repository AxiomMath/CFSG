module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Form
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import CFSG.RankThree.GF2n.Stroth80.Sec310MatRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem toGL_mulVec_equivFun {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W) (f : W ≃ₗ[K] W) (w : W) :
    (b.toGL f : Matrix ι ι K) *ᵥ b.equivFun w = b.equivFun (f w) := by
  have h1 : (Matrix.GeneralLinearGroup.toLin' b (b.toGL f)).toLinearEquiv w = f w := by
    rw [Module.Basis.toLin'_toGL]
    rfl
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at h1
  apply b.equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply, ← h1,
    Fintype.linearCombination_apply]
  rfl

theorem exists_matrixRep_of_basis {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W) {R : Type} [Group R]
    (ρ : R →* (W ≃ₗ[K] W)) :
    ∃ φ : R →* GL ι K, (∀ (r : R) (w : W),
        b.equivFun (ρ r w) = (φ r : Matrix ι ι K) *ᵥ b.equivFun w) ∧ φ.ker = ρ.ker := by
  refine ⟨(b.toGL).toMonoidHom.comp ρ, fun r w => (toGL_mulVec_equivFun b (ρ r) w).symm,
    ?_⟩
  ext r
  simp [MonoidHom.mem_ker]

theorem J_eq_spJ_of_charTwo {m : ℕ} {K : Type} [Field K] [CharP K 2] :
    Matrix.J (Fin m) K = spJ m K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.J, spJ, Matrix.one_apply, CharTwo.neg_eq]

theorem exists_sympRep_of_form {R V N : Subgroup G} (H : StrothHyp M Q Z) (hVQ : V ≤ Q)
    (hRH : R ≤ H0 M Z) (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hN : ∀ r, r ∈ N ↔ r ∈ R ∧ ∀ v ∈ V, ⁅r, v⁆ ∈ Z) {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V) {m : ℕ}
    (b : Module.Basis (Fin m ⊕ Fin m) K ↥(imgSub M₀ V hS))
    (F : LinearMap.BilinForm K ↥(imgSub M₀ V hS))
    (hG : ∀ u w, F u w = spForm m K (b.equivFun u) (b.equivFun w))
    (hinv : ∀ (r : ↥R) (S : M₀.E ≃ₗ[K] M₀.E),
      (∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = S (M₀.π x)) →
      ∀ (w w' : ↥(imgSub M₀ V hS)) (hw : S (w : M₀.E) ∈ imgSub M₀ V hS)
        (hw' : S (w' : M₀.E) ∈ imgSub M₀ V hS), F ⟨S w, hw⟩ ⟨S w', hw'⟩ = F w w') :
    ∃ φ : ↥R →* GL (Fin m ⊕ Fin m) K, φ.range ≤ StatedSp m K ∧ φ.ker = N.subgroupOf R ∧
      SectionAct K R V Z φ (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) := by
  classical
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 H h
  let W : Submodule K M₀.E := imgSub M₀ V hS
  have hWmem : ∀ e, e ∈ W ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hπW : ∀ v : ↥V, M₀.π (v : G) ∈ W := fun v =>
    (hWmem _).mpr (M₀.pi_mem_img v.2 (hVQ v.2))
  let φR : ↥R →* (M₀.E ≃ₗ[K] M₀.E) := φ₀.comp (Subgroup.inclusion hRH)
  have hφRπ : ∀ (r : ↥R) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) = φR r (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hRH r) x hx
  have hinvW : ∀ (r : ↥R) (w : M₀.E), w ∈ W → φR r w ∈ W := by
    intro r w hw
    obtain ⟨u, huV, huQ, rfl⟩ := (hWmem w).mp hw
    have hru : (r : G) * u * (r : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hRV r.2) u).mp huV
    rw [← hφRπ r u huQ]
    exact (hWmem _).mpr (M₀.pi_mem_img hru (hVQ hru))
  let ρ : ↥R →* (W ≃ₗ[K] W) := actionOnSubspace φR W hinvW
  have hρ : ∀ (r : ↥R) (w : W), ((ρ r w : W) : M₀.E) = φR r (w : M₀.E) := fun r w =>
    actionOnSubspace_apply φR W hinvW r w
  obtain ⟨φ, hc, hker⟩ := exists_matrixRep_of_basis b ρ
  have hkerρ : ρ.ker = N.subgroupOf R := by
    ext r
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hN]
    constructor
    · intro h1
      refine ⟨r.2, fun v hv => ?_⟩
      have hvQ : v ∈ Q := hVQ hv
      have hrvQ : (r : G) * v * (r : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (hRH r.2).1) v).mp hvQ
      refine (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hvQ hrvQ).mpr ?_
      have h2 := congrArg (fun f : W ≃ₗ[K] W => ((f ⟨M₀.π v, hπW ⟨v, hv⟩⟩ : W) : M₀.E)) h1
      simp only [hρ] at h2
      rw [hφRπ r v hvQ]
      exact h2
    · rintro ⟨-, h1⟩
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [hρ]
      obtain ⟨u, huV, huQ, hu⟩ := (hWmem _).mp w.2
      have hruQ : (r : G) * u * (r : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (hRH r.2).1) u).mp (hVQ huV)
      have := (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) huQ hruQ).mp (h1 u huV)
      change φR r (w : M₀.E) = (w : M₀.E)
      rw [← hu, ← hφRπ r u huQ, this]
  let πV : ↥V →* Multiplicative W :=
    { toFun := fun v => Multiplicative.ofAdd (⟨M₀.π (v : G), hπW v⟩ : W)
      map_one' := by
        have h0 : M₀.π (1 : G) = 0 := (M₀.π_ker 1 (Q.one_mem)).mpr Z.one_mem
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact h0
      map_mul' := by
        intro v w
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact M₀.π_mul _ (hVQ v.2) _ (hVQ w.2) }
  have hker' : πV.ker = Z.subgroupOf V := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 := congrArg (fun a : Multiplicative W => ((Multiplicative.toAdd a : W) : M₀.E)) h1
      exact (M₀.π_ker _ (hVQ v.2)).mp h2
    · intro h1
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact (M₀.π_ker _ (hVQ v.2)).mpr h1
  have hsurj : Function.Surjective πV := by
    intro w
    obtain ⟨u, huV, huQ, hu⟩ := (hWmem _).mp (Multiplicative.toAdd w).2
    refine ⟨⟨u, huV⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hu
  have hn : (Z.subgroupOf V).Normal := hker' ▸ πV.normal_ker
  haveI := hn
  let e1 : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative W :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective πV hsurj)
  let ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin m ⊕ Fin m → K) :=
    e1.trans b.equivFun.toAddEquiv.toMultiplicative
  have hψ : ∀ v : ↥V, Multiplicative.toAdd (ψ (QuotientGroup.mk v)) =
      b.equivFun ⟨M₀.π (v : G), hπW v⟩ := fun v => rfl
  have hcompat : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
    intro s v w hw
    rw [hψ, hψ]
    have hρv : (⟨M₀.π (w : G), hπW w⟩ : W) = ρ s ⟨M₀.π (v : G), hπW v⟩ := by
      apply Subtype.ext
      rw [hρ]
      show M₀.π (w : G) = φR s (M₀.π (v : G))
      rw [hw]
      exact hφRπ s v (hVQ v.2)
    rw [hρv]
    exact hc s _
  have hkey : ∀ (r : ↥R) (w w' : W), F (ρ r w) (ρ r w') = F w w' := by
    intro r w w'
    have e1' : ρ r w = ⟨φR r (w : M₀.E), hinvW r _ w.2⟩ := Subtype.ext (hρ r w)
    have e2' : ρ r w' = ⟨φR r (w' : M₀.E), hinvW r _ w'.2⟩ := Subtype.ext (hρ r w')
    rw [e1', e2']
    exact hinv r (φR r) (hφRπ r) w w' (hinvW r _ w.2) (hinvW r _ w'.2)
  have hrange : φ.range ≤ StatedSp m K := by
    intro A hA
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hA
    refine (mem_statedSp_iff_forall (φ r)).mpr fun x y => ?_
    obtain ⟨w, rfl⟩ := b.equivFun.surjective x
    obtain ⟨w', rfl⟩ := b.equivFun.surjective y
    rw [← hc r w, ← hc r w', ← hG, ← hG]
    exact hkey r w w'
  have hsec : SectionAct K R V Z φ (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) :=
    ⟨hRV, hn, ψ, hcompat⟩
  exact ⟨φ, hrange, hker.trans hkerρ, hsec⟩

theorem stroth310SympForm_of_34 (h34 : Stroth34Statement) : Stroth310SympFormStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs _hR hnot
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c _ he => hc.smul_mem_img_Vt h t c he
  obtain ⟨F, hnd, halt, hinv⟩ := hc.exists_comm_form h35 hs.mem hs.notQ hnot h hS
  obtain ⟨m, b, hb⟩ := halt.exists_basis_toMatrix_eq_J hnd
  have hG : ∀ u w, F u w = spForm m (GaloisField 2 n') (b.equivFun u) (b.equivFun w) := by
    intro u w
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b F u w, hb,
      J_eq_spJ_of_charTwo, spForm_apply]
    rfl
  have hm : m ≠ 0 := by
    intro hm0
    apply hnot
    subst hm0
    have hfin : Module.finrank (GaloisField 2 n')
        ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) = 0 := by
      rw [Module.finrank_eq_card_basis b]
      simp
    have hsub : Subsingleton ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Module.finrank_zero_iff.mp hfin
    intro v hv
    have hvQ : v ∈ Q := hc.Vt_le_Q t hv
    have hπ0 : M₀.π v = 0 := by
      have := Subsingleton.elim
        (⟨M₀.π v, mem_imgSub.mpr (M₀.pi_mem_img hv hvQ)⟩ :
          ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS)) 0
      exact congrArg Subtype.val this
    exact hc.Z_le_QB.1 ((M₀.π_ker v hvQ).mp hπ0)
  obtain ⟨φ, h1, h2, h3⟩ := exists_sympRep_of_form (R := Rt M (LB M Q B) t)
    (N := hc.CN t) (V := Vt M (LB M Q B) B Z t) hc.hyp (hc.Vt_le_Q t) (hc.Rt_le_H0 t)
    (hc.Rt_normalizes_Vt hs.mem) (fun _ => Ctx.mem_CN (hc := hc)) h hS b F hG hinv
  exact ⟨GaloisField 2 n', inferInstance, inferInstance, h.card, m,
    Nat.one_le_iff_ne_zero.mpr hm, φ, h1, h2, h3⟩

end CFSG.RankThree.GF2n.Stroth80
