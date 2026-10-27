module

public import CFSG.RankThree.GF2n.Smith81.Lin31TwoModel

import CFSG.RankThree.GF2n.Smith81.TiD2Module

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem tensorModel_of_left {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    {φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    (Θ : M₀.E ≃ₗ[K] Mat2 K) (hΘ : ∀ e, (Θ e).det = M₀.Qf e)
    (p : ↥(Lgen M (LB M Q B)) →* SL(2, K))
    (hp : ∀ m e, Θ (φS m e) = (p m : Mat2 K) * Θ e)
    (hps : Function.Surjective p)
    (hpk : ∀ m, p m = 1 ↔ (m : G) ∈ Q) : Nonempty (TensorModel M Q Z B) := by
  let φ : ↥(Lgen M (LB M Q B)) →* GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL.comp p
  have hφrange : φ.range = StatedSL 2 K := by
    show (Matrix.SpecialLinearGroup.toGL.comp p).range = StatedSL 2 K
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hps, Subgroup.map_top,
      ← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
  have hφker : φ.ker = Q.subgroupOf (Lgen M (LB M Q B)) := by
    have hpk' : p.ker = Q.subgroupOf (Lgen M (LB M Q B)) := by
      ext m
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hpk m
    show (Matrix.SpecialLinearGroup.toGL.comp p).ker = Q.subgroupOf (Lgen M (LB M Q B))
    rw [MonoidHom.ker_comp_of_injective p Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective, hpk']
  exact ⟨{
    K := K
    γ := γ
    M₀ := M₀
    gm := hD
    F := K
    card_F := hD.card
    ε := RingEquiv.refl K
    Φ := Θ.toAddEquiv
    φ := φ
    φ_range := hφrange
    φ_ker := hφker
    smul := fun c e => by
      show Θ (c • e) = c • Θ e
      exact map_smul Θ c e
    qf := fun e => (hΘ e).symm
    act := fun s x hx => by
      show Θ (M₀.π ((s : G) * x * (s : G)⁻¹)) = (p s : Mat2 K) * Θ (M₀.π x)
      rw [hφπ s x hx, hp s] }⟩

private theorem surjective_of_ker_eq {K : Type} [Field K] [Finite K] {S : Type} [Group S]
    [Finite S] {ψ p : S →* SL(2, K)} (hψs : Function.Surjective ψ) (hk : ψ.ker = p.ker) :
    Function.Surjective p := by
  haveI : Finite SL(2, K) :=
    Finite.of_injective (fun g : SL(2, K) => (g : Mat2 K)) Subtype.val_injective
  have htop : p.range = ⊤ := by
    have h1 := Subgroup.card_ker_mul_card_range p
    have h2 := Subgroup.card_ker_mul_card_range ψ
    rw [← hk] at h1
    have hpos : 0 < Nat.card ↥ψ.ker := by
      haveI : Nonempty ↥ψ.ker := ⟨1⟩
      exact Nat.card_pos
    have hc := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [MonoidHom.range_eq_top.mpr hψs, Subgroup.card_top] at hc
    exact Subgroup.eq_top_of_card_eq (H := p.range) hc
  exact MonoidHom.range_eq_top.mp htop

private theorem exists_line_of_isA2 (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀)
    {φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    (hφker : ∀ m : ↥(Lgen M (LB M Q B)), φS m = 1 ↔ (m : G) ∈ Q)
    (D : D2Data Q Z M₀ φS) {a : G} (haL : a ∈ LB M Q B) (hA2 : IsA2 Q Z a) :
    ∃ v₀ : M₀.E, v₀ ≠ 0 ∧
      M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z) ≤
        (Submodule.span K {v₀}).toAddSubgroup := by
  obtain ⟨haN, haQ, ha2, -, hel⟩ := hA2
  have haS : a ∈ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B) haL
  let t : ↥(Lgen M (LB M Q B)) := ⟨a, haS⟩
  have hQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hSQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr haN)
  have ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp haN x).mp hx
  have ha' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q := by
    intro x hx
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) x).mp hx
    rwa [inv_inv] at h
  obtain ⟨c, hc0, hcline⟩ := D.lemmaS (t := t) haQ ha2
  let v₀ : M₀.E := D.Θ.symm (D2.tw D.σ c)
  have hv₀ : v₀ ≠ 0 := by
    intro h
    apply D2.tw_ne_zero D.σ hc0
    have h' : D.Θ (D.Θ.symm (D2.tw D.σ c)) = D.Θ 0 := congrArg D.Θ h
    rw [LinearEquiv.apply_symm_apply, map_zero] at h'
    exact h'
  have hT2 : φS t * φS t = 1 := by
    have hm : ((t * t : ↥(Lgen M (LB M Q B))) : G) ∈ Q := by
      show a * a ∈ Q
      rw [← sq]
      exact ha2
    have h := (hφker (t * t)).mpr hm
    rwa [map_mul] at h
  have hneg : ∀ v : M₀.E, -v = v := by
    intro v
    rw [neg_eq_iff_add_eq_zero]
    have h2 : (2 : K) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    exact (two_smul K v).symm.trans h2
  have hfix : ∀ v ∈ LinearMap.range ((φS t : M₀.E →ₗ[K] M₀.E) - 1), φS t v = v := by
    intro v hv
    obtain ⟨e, rfl⟩ := hv
    have hTe : φS t (φS t e) = e := by
      have h := congrArg (fun (S : M₀.E ≃ₗ[K] M₀.E) => S e) hT2
      simpa using h
    show φS t (φS t e - e) = φS t e - e
    rw [map_sub, hTe, sub_eq_add_neg, sub_eq_add_neg, hneg, hneg, add_comm]
  refine ⟨v₀, hv₀, ?_⟩
  have hlift : ⁅Q, Subgroup.zpowers a⁆ ⊔ Z ≤ M₀.lift (M₀.img ⁅Q, Subgroup.zpowers a⁆) := by
    refine sup_le (fun y hy => ⟨hSQ hy, M₀.pi_mem_img hy (hSQ hy)⟩) (fun z hz => ?_)
    refine ⟨hQ hz, ?_⟩
    rw [(M₀.π_ker z (hQ hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  intro v hv
  obtain ⟨x, hx, -, rfl⟩ := hv
  have hv' : M₀.π x ∈ M₀.img ⁅Q, Subgroup.zpowers a⁆ := (hlift hx).2
  have hTπ : ∀ y ∈ Q, M₀.π (a * y * a⁻¹) = φS t (M₀.π y) := fun y hy => hφπ t y hy
  have hrv : M₀.π x ∈ LinearMap.range ((φS t : M₀.E →ₗ[K] M₀.E) - 1) :=
    (Tim79.QuadModel.mem_img_commutator_zpowers (M₀ := M₀) (φS t) ha ha' hTπ).mp hv'
  have hsing : M₀.Qf (M₀.π x) = 0 :=
    (M₀.isElemAbelian_iff hD.reg hSQ).mp hel (M₀.π x) hv'
  obtain ⟨μ, hμ⟩ := hcline (M₀.π x) (hfix _ hrv) hsing
  rw [hμ]
  exact Submodule.smul_mem _ μ (Submodule.mem_span_singleton_self v₀)

private theorem false_of_both_faithful (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀)
    {φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    (hφker : ∀ m : ↥(Lgen M (LB M Q B)), φS m = 1 ↔ (m : G) ∈ Q)
    (D : D2Data Q Z M₀ φS) (hno : ¬ NoA2 Q Z (LB M Q B)) : False := by
  haveI : Finite M₀.E := Module.finite_of_finite K
  obtain ⟨a, haL, hA2⟩ : ∃ a ∈ LB M Q B, IsA2 Q Z a := by
    by_contra h
    exact hno fun a ha ha2 => h ⟨a, ha, ha2⟩
  obtain ⟨v₀, hv₀, hline⟩ := exists_line_of_isA2 hc hD hφπ hφker D haL hA2
  obtain ⟨haN, -, -, hcardA2, -⟩ := hA2
  have hQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hSQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr haN)
  have hcard_img : Nat.card ↥(M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z)) ≤ Nat.card K := by
    have hspan : Nat.card ↥((Submodule.span K {v₀}).toAddSubgroup) = Nat.card K := by
      have h : Nat.card (Submodule.span K {v₀}) = Nat.card K := by
        rw [Module.natCard_eq_pow_finrank (K := K), finrank_span_singleton (K := K) hv₀,
          pow_one]
      exact h
    rw [← hspan]
    refine Nat.card_le_card_of_injective
      (fun x : ↥(M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z)) =>
        (⟨(x : M₀.E), hline x.2⟩ : ↥((Submodule.span K {v₀}).toAddSubgroup))) ?_
    intro x y h
    exact Subtype.ext (congrArg (fun z : ↥((Submodule.span K {v₀}).toAddSubgroup) =>
      (z : M₀.E)) h)
  have hcard_eq : Nat.card ↥(M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z)) = Nat.card Z ^ 2 := by
    have h1 := M₀.card_eq (S := ⁅Q, Subgroup.zpowers a⁆ ⊔ Z) (sup_le hSQ hQ) le_sup_right
    rw [hcardA2] at h1
    have hpos : 0 < Nat.card Z := by
      have := hc.hyp.q4
      omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← h1]
    ring
  have hq : Nat.card Z ^ 2 ≤ Nat.card Z := by
    calc Nat.card Z ^ 2 = Nat.card ↥(M₀.img (⁅Q, Subgroup.zpowers a⁆ ⊔ Z)) := hcard_eq.symm
      _ ≤ Nat.card K := hcard_img
      _ = Nat.card Z := hD.card
  have h4 : 4 ≤ Nat.card Z := hc.hyp.q4
  nlinarith

private theorem tensorModel_of_pair (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K]
    [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀)
    {φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x))
    (hφker : ∀ m : ↥(Lgen M (LB M Q B)), φS m = 1 ↔ (m : G) ∈ Q)
    (Θ₀ : M₀.E ≃ₗ[K] Mat2 K) (hΘ₀ : ∀ e, (Θ₀ e).det = M₀.Qf e) (h4 : 4 ≤ Nat.card K)
    (ψ : ↥(Lgen M (LB M Q B)) →* SL(2, K)) (hψs : Function.Surjective ψ)
    (hψk : ∀ m : ↥(Lgen M (LB M Q B)), ψ m = 1 ↔ (m : G) ∈ Q)
    (p₁ p₂ : ↥(Lgen M (LB M Q B)) →* SL(2, K))
    (hp : ∀ m e, Θ₀ (φS m e) = (p₁ m : Mat2 K) * Θ₀ e * (p₂ m : Mat2 K)ᵀ)
    (hQ1 : ∀ m : ↥(Lgen M (LB M Q B)), (m : G) ∈ Q → p₁ m = 1 ∧ p₂ m = 1)
    (hno : ¬ NoA2 Q Z (LB M Q B)) : Nonempty (TensorModel M Q Z B) := by
  have hker₁ : ∀ m, ψ m = 1 → p₁ m = 1 := fun m hm => (hQ1 m ((hψk m).mp hm)).1
  have hker₂ : ∀ m, ψ m = 1 → p₂ m = 1 := fun m hm => (hQ1 m ((hψk m).mp hm)).2
  rcases kernel_dichotomy h4 ψ hψs p₁ hker₁ with h1 | h1 <;>
    rcases kernel_dichotomy h4 ψ hψs p₂ hker₂ with h2 | h2
  ·
    exfalso
    have hall : ∀ m : ↥(Lgen M (LB M Q B)), ψ m = 1 := by
      intro m
      rw [hψk m, ← hφker m]
      refine LinearEquiv.ext fun e => ?_
      apply Θ₀.injective
      rw [hp m e, h1 m, h2 m]
      simp
    obtain ⟨m, hm⟩ := hψs (D2.uSL 1)
    have := hall m
    rw [hm] at this
    have h3 := congrArg (fun A : SL(2, K) => (A : Mat2 K) 0 1) this
    simp at h3
  ·
    have hk₂ : ψ.ker = p₂.ker := by
      ext m
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨hker₂ m, h2 m⟩
    let τ : Mat2 K ≃ₗ[K] Mat2 K := Matrix.transposeLinearEquiv (Fin 2) (Fin 2) K K
    let Θ' : M₀.E ≃ₗ[K] Mat2 K := Θ₀.trans τ
    have hΘ' : ∀ e, (Θ' e).det = M₀.Qf e := fun e => by
      show ((Θ₀ e)ᵀ).det = M₀.Qf e
      rw [Matrix.det_transpose, hΘ₀]
    have hp' : ∀ m e, Θ' (φS m e) = (p₂ m : Mat2 K) * Θ' e := fun m e => by
      show (Θ₀ (φS m e))ᵀ = (p₂ m : Mat2 K) * (Θ₀ e)ᵀ
      rw [hp m e, h1 m]
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one,
        Matrix.transpose_mul, Matrix.transpose_one, Matrix.transpose_transpose]
    refine tensorModel_of_left hD hφπ Θ' hΘ' p₂ hp'
      (surjective_of_ker_eq hψs hk₂) (fun m => ?_)
    exact ⟨fun hm => (hψk m).mp (h2 m hm), fun hm => (hQ1 m hm).2⟩
  ·
    have hk₁ : ψ.ker = p₁.ker := by
      ext m
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨hker₁ m, h1 m⟩
    refine tensorModel_of_left hD hφπ Θ₀ hΘ₀ p₁ ?_
      (surjective_of_ker_eq hψs hk₁) (fun m => ?_)
    · intro m e
      rw [hp m e, h2 m]
      simp
    · exact ⟨fun hm => (hψk m).mp (h1 m hm), fun hm => (hQ1 m hm).1⟩
  ·
    exfalso
    obtain ⟨Θ', σ, p, hdet, hps, hpk, hact⟩ := twist_of_pair h4 Θ₀ φS ψ hψs p₁ p₂ hp
      (fun m => ⟨hker₁ m, h1 m⟩) (fun m => ⟨hker₂ m, h2 m⟩)
    let D : D2Data Q Z M₀ φS :=
      { Θ := Θ'
        σ := σ
        p := p
        det_eq := fun e => by rw [hdet, hΘ₀]
        surj := hps
        ker_iff := fun m => (hpk m).trans (hψk m)
        act := hact }
    exact false_of_both_faithful hc hD hφπ hφker D hno

theorem exists_tensorModel_of_not_noA2 (hc : Ctx M Q Z B) (hD2 : CaseD2 M Q Z B)
    (hno : ¬ NoA2 Q Z (LB M Q B)) : Nonempty (TensorModel M Q Z B) := by
  have hw : Width Q Z 2 := by
    have := hD2.1
    unfold Width
    simpa using this
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  have hK : 1 < Nat.card K := by
    have := hc.hyp.q4
    rw [hD.card]
    omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hD.card]
    exact hc.hyp.q4
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  let φS : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E) :=
    φ.comp (Subgroup.inclusion hc.Lgen_le_H0)
  have hφSπ : ∀ (m : ↥(Lgen M (LB M Q B))) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φS m (M₀.π x) :=
    fun m x hx => hφπ ⟨m, hc.Lgen_le_H0 m.2⟩ x hx
  have hφSker : ∀ m : ↥(Lgen M (LB M Q B)), φS m = 1 ↔ (m : G) ∈ Q :=
    fun m => hφker ⟨m, hc.Lgen_le_H0 m.2⟩
  have hφSQ : ∀ (m : ↥(Lgen M (LB M Q B))) e, M₀.Qf (φS m e) = M₀.Qf e :=
    fun m e => hφQ ⟨m, hc.Lgen_le_H0 m.2⟩ e
  obtain ⟨Θ₀, hΘ₀⟩ := exists_det_equiv (CharTwo.two_eq_zero) M₀.B M₀.Qf M₀.alt M₀.nondeg
    M₀.Qf_add hD.hyperbolic (by rw [hD.finrank_E hw hK])
  obtain ⟨ψ, hψs, hψk⟩ := exists_psi hD2.2 hD.card
  obtain ⟨δ, hδ⟩ := D2.exists_dicksonHom K
  have hiso : ∀ m e, (Θ₀ (φS m e)).det = (Θ₀ e).det := fun m e => by
    rw [hΘ₀, hΘ₀, hφSQ m e]
  obtain ⟨p₁, p₂, hp⟩ := exists_pair_homs h4 δ hδ Θ₀ φS hiso ψ hψs
    (fun m hm => (hφSker m).mpr ((hψk m).mp hm))
  have hQ1 : ∀ m : ↥(Lgen M (LB M Q B)), (m : G) ∈ Q → p₁ m = 1 ∧ p₂ m = 1 := by
    intro m hm
    have h1 : φS m = 1 := (hφSker m).mpr hm
    apply D2.pair_unique (g := p₁ m) (g' := 1) (h := p₂ m) (h' := 1)
    intro X
    obtain ⟨e, rfl⟩ := Θ₀.surjective X
    rw [← hp m e, h1]
    simp
  exact tensorModel_of_pair hc hD hφSπ hφSker Θ₀ hΘ₀ h4 ψ hψs hψk p₁ p₂ hp hQ1 hno

end CFSG.RankThree.GF2n.Smith81
