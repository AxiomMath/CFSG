module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module
open scoped commutatorElement Matrix

section Semilinear

variable {K E ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [AddCommGroup E] [Module K E]

theorem exists_basis_of_semilinear (V : Submodule K E) (W : Submodule K ↥V) (σ : K ≃+* K)
    (F : (ι → K) →+ ↥V) (hFσ : ∀ (c : K) x, F (c • x) = σ c • F x) (hinj : Function.Injective F)
    (hW : ∀ x, F x ∈ W) (hsurj : ∀ w ∈ W, ∃ x, F x = w) :
    ∃ b : Module.Basis ι K ↥(W.map V.subtype),
      (∀ i, ((b i : ↥(W.map V.subtype)) : E) = ((F (Pi.single i 1) : ↥V) : E)) ∧
      ∀ x : ι → K, ∑ i, σ (x i) • ((b i : ↥(W.map V.subtype)) : E) = ((F x : ↥V) : E) := by
  obtain ⟨f, hf⟩ : ∃ f : (ι → K) →ₗ[K] E,
      ∀ x, f x = ((F (fun i => σ.symm (x i)) : ↥V) : E) :=
    ⟨{ toFun := fun x => ((F (fun i => σ.symm (x i)) : ↥V) : E)
       map_add' := fun x y => by
         have h : (fun i => σ.symm ((x + y) i)) =
             (fun i => σ.symm (x i)) + (fun i => σ.symm (y i)) := by
           funext i
           simp [map_add]
         rw [h, map_add, Submodule.coe_add]
       map_smul' := fun c x => by
         have h : (fun i => σ.symm ((c • x) i)) = σ.symm c • (fun i => σ.symm (x i)) := by
           funext i
           simp [map_mul]
         rw [h, hFσ]
         simp only [RingEquiv.apply_symm_apply, RingHom.id_apply, Submodule.coe_smul] },
      fun x => rfl⟩
  have hmem : ∀ x, f x ∈ W.map V.subtype := fun x =>
    Submodule.mem_map.mpr ⟨F (fun i => σ.symm (x i)), hW _, (hf x).symm⟩
  have hinjW : Function.Injective (f.codRestrict (W.map V.subtype) hmem) := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    simp only [LinearMap.codRestrict_apply, hf] at h1
    have h2 : F (fun i => σ.symm (x i)) = F (fun i => σ.symm (y i)) := Subtype.ext h1
    funext i
    exact σ.symm.injective (congrFun (hinj h2) i)
  have hsurjW : Function.Surjective (f.codRestrict (W.map V.subtype) hmem) := by
    rintro ⟨w, hw⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨x0, hx0⟩ := hsurj v hv
    refine ⟨fun i => σ (x0 i), Subtype.ext ?_⟩
    simp only [LinearMap.codRestrict_apply, hf]
    simp [hx0]
  obtain ⟨e, he⟩ : ∃ e : (ι → K) ≃ₗ[K] ↥(W.map V.subtype),
      ∀ x : ι → K, ((e x : ↥(W.map V.subtype)) : E) = ((F (fun i => σ.symm (x i)) : ↥V) : E) :=
    ⟨LinearEquiv.ofBijective (f.codRestrict (W.map V.subtype) hmem) ⟨hinjW, hsurjW⟩,
      fun x => (hf x).symm ▸ rfl⟩
  have hfirst : ∀ i, ((((Pi.basisFun K ι).map e) i : ↥(W.map V.subtype)) : E) =
      ((F (Pi.single i 1) : ↥V) : E) := by
    intro i
    have h1 : (fun j => σ.symm ((Pi.single i (1 : K) : ι → K) j)) = Pi.single i 1 := by
      funext j
      by_cases h : j = i <;> simp [h]
    rw [Module.Basis.map_apply, Pi.basisFun_apply, he, h1]
  refine ⟨(Pi.basisFun K ι).map e, hfirst, fun x => ?_⟩
  have hx : x = ∑ i, x i • (Pi.single i 1 : ι → K) := pi_eq_sum_univ' x
  have hFx : F x = ∑ i, σ (x i) • F (Pi.single i 1) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hFσ (x i) (Pi.single i 1)
  rw [hFx, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, hfirst]

end Semilinear

private theorem two_mul_finrank_le_of_totallySingular {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) (W : Submodule K V)
    (hW : ∀ w ∈ W, Qf w = 0) : 2 * finrank K W ≤ finrank K V := by
  have hB : (polarBilin Qf).Nondegenerate :=
    ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => by rw [polar_comm]; exact hy x⟩
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) W := fun x hx => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    show polarBilin Qf n x = 0
    rw [QuadraticMap.polarBilin_apply_apply]
    simp only [polar, hW _ (add_mem hn hx), hW n hn, hW x hx, sub_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at h1
  have h2 := Submodule.finrank_le W
  omega

variable {G : Type} [Group G]


theorem Ctx.rt1_of_global [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal]
    (hRT1 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
        (N : Type) [AddCommGroup N] [Module K N] [FiniteDimensional K N]
        (BN : LinearMap.BilinForm K N)
        (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
        4 ≤ Nat.card K → ∀ (hBN : BN.IsAlt), BN.Nondegenerate → 4 ≤ finrank K N →
        ∀ (Qf : QuadraticForm K V), (∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) →
        ∀ (ρ : Gsp BN →* (V ≃ₗ[K] V)), (∀ g v, Qf (ρ g v) = Qf v) →
        (∃ v₀ : N, v₀ ≠ 0 ∧ ∃ c₀ : K, c₀ ≠ 0 ∧
          finrank K (movedSpace (ρ (Tsp hBN v₀ c₀))) = 2 ∧
          ∀ w ∈ movedSpace (ρ (Tsp hBN v₀ c₀)), Qf w = 0) →
        (∀ v : V, (∀ g, ρ g v = v) → v = 0) →
        commutatorSpace ρ.range = ⊤ →
        ∃ W₁ W₂ : Submodule K V, IsCompl W₁ W₂ ∧
          (∀ w ∈ W₁, Qf w = 0) ∧ (∀ w ∈ W₂, Qf w = 0) ∧
          (∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
          ∃ (σ : K ≃+* K) (F : N →+ V), (∀ (c : K) x, F (c • x) = σ c • F x) ∧
            Function.Injective F ∧ (∀ x, F x ∈ W₁) ∧ (∀ w ∈ W₁, ∃ x, F x = w) ∧
            ∀ g x, F (g.app x) = ρ g (F x))
    (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)} (hT : CMSpTransvAt M Q Z B m x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (hK : Nat.card K = 2 ^ x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q → M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) :
    Module.finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 4 * m ∧
      ∃ W₁ W₂ : Submodule K M₀.E,
        W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ ∧
        (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁) ∧
        (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂) ∧
        (∀ w ∈ W₁, M₀.Qf w = 0) ∧ (∀ w ∈ W₂, M₀.Qf w = 0) ∧
        ∃ (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁)
          (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K),
          ρ.range = StatedSp m K ∧
          (∀ s : ↥(XbarH M Q Z B), ρ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
          ∀ (s : ↥(XbarH M Q Z B)) (i : Fin m ⊕ Fin m),
            φ s ((b i : ↥W₁) : M₀.E) =
              ∑ j, (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i •
                ((b j : ↥W₁) : M₀.E) := by
  classical
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hq4 : 4 ≤ Nat.card K := hKZ ▸ hc.hyp.q4
  have hm2 : 2 ≤ m := (hLm.admissible).2.2.1
  obtain ⟨Θ, hΘsurj, hΘker, s₀, hs₀a, hs₀rk⟩ := hc.exists_hom_statedSp_of_transvAt hLm hT hK
  have hφB : ∀ (g : ↥(H0 M Z)) e f, M₀.B (φ g e) (φ g f) = M₀.B e f := by
    intro g e f
    have h1 := M₀.Qf_add (φ g e) (φ g f)
    have h2 := M₀.Qf_add e f
    rw [← map_add, hφQ g, hφQ g e, hφQ g f] at h1
    linear_combination h2 - h1
  obtain ⟨ρV, hρV⟩ := hc.exists_rho_factor φ Θ hΘsurj
    (fun s hs => (hφk (s : ↥(H0 M Z))).mpr ((hΘker s).mp hs))
  have hspΘ : ∀ g : Gsp (spForm m K), ∃ s : ↥(XbarH M Q Z B), spEquiv (Θ s) = g := fun g => by
    obtain ⟨t, ht⟩ := hΘsurj ((spEquiv (m := m) (K := K)).symm g)
    exact ⟨t, by rw [ht]; exact MulEquiv.apply_symm_apply _ _⟩
  have hnd := hc.cmCommQf_nondegenerate hD φ hφπ
  have hρQ : ∀ (g : Gsp (spForm m K)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      cmCommQf B φ (ρV g v) = cmCommQf B φ v := by
    intro g v
    obtain ⟨s, rfl⟩ := hspΘ g
    rw [hρV s]
    exact cmCommQf_cmCommAct hc φ hφQ s v
  have hS₀ : ∃ v₀ : Fin m ⊕ Fin m → K, v₀ ≠ 0 ∧ ∃ c₀ : K, c₀ ≠ 0 ∧
      finrank K (movedSpace (ρV (Tsp (spForm_isAlt (m := m) (K := K)) v₀ c₀))) = 2 ∧
      ∀ w ∈ movedSpace (ρV (Tsp (spForm_isAlt (m := m) (K := K)) v₀ c₀)),
        cmCommQf B φ w = 0 := by
    obtain ⟨u, c, hu, hc0, hTsp⟩ := exists_spEquiv_eq_Tsp_of_rank_eq_one (Θ s₀) hs₀rk
    refine ⟨u, hu, c, hc0, ?_⟩
    rw [← hTsp, hρV s₀]
    exact hc.cmCommAct_moved hD hKZ φ hφπ ha2 (by rw [hs₀a]; exact h.1)
      (by rw [hs₀a]; exact h.2)
  have hC : ∀ v : ↥(cmComm M Q Z B K γ M₀ φ), (∀ g, ρV g v = v) → v = 0 := by
    intro v hv
    refine Subtype.ext (hc.eq_zero_of_fixed_of_mem_cmComm hD φ hφπ hφB v.2 fun s => ?_)
    have h1 := hv (spEquiv (Θ s))
    rw [hρV s] at h1
    exact congrArg Subtype.val h1
  have hrange : ρV.range = (cmCommAct hc φ).range := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨s, rfl⟩ := hspΘ g
      exact ⟨s, (hρV s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨spEquiv (Θ s), hρV s⟩
  have hVtop : commutatorSpace ρV.range = ⊤ := by
    rw [hrange]
    exact hc.commutatorSpace_cmCommAct_eq_top hD φ hφπ hφB
  obtain ⟨W₁, W₂, hcompl, hs₁, hs₂, hi₁, hi₂, σ, F, hFσ, hFinj, hFW, hFsurj, hFeq⟩ :=
    hRT1 K (Fin m ⊕ Fin m → K) (spForm m K) (cmComm M Q Z B K γ M₀ φ) hq4 spForm_isAlt
      spForm_nondegenerate (by rw [finrank_spSpace]; omega) (cmCommQf B φ) hnd ρV hρQ hS₀ hC hVtop
  have hfr₁ := two_mul_finrank_le_of_totallySingular (cmCommQf B φ) hnd W₁ hs₁
  have hfr₂ := two_mul_finrank_le_of_totallySingular (cmCommQf B φ) hnd W₂ hs₂
  have hfrsum := Submodule.finrank_add_eq_of_isCompl hcompl
  obtain ⟨b, hb1, hb2⟩ := exists_basis_of_semilinear (cmComm M Q Z B K γ M₀ φ) W₁ σ F hFσ hFinj
    hFW hFsurj
  have hfrW₁ : finrank K ↥W₁ = 2 * m := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Submodule.finrank_map_subtype_eq, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  have hdim : finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 4 * m := by omega
  have hinf : W₁.map (cmComm M Q Z B K γ M₀ φ).subtype ⊓ W₂.map (cmComm M Q Z B K γ M₀ φ).subtype
      = ⊥ := by
    rw [← Submodule.map_inf _ (Submodule.injective_subtype _), hcompl.inf_eq_bot,
      Submodule.map_bot]
  have hsup : W₁.map (cmComm M Q Z B K γ M₀ φ).subtype ⊔ W₂.map (cmComm M Q Z B K γ M₀ φ).subtype
      = cmComm M Q Z B K γ M₀ φ := by
    rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_subtype_top]
  have hinv : ∀ W : Submodule K ↥(cmComm M Q Z B K γ M₀ φ), (∀ g, ∀ w ∈ W, ρV g w ∈ W) →
      ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W.map (cmComm M Q Z B K γ M₀ φ).subtype,
        φ (s : ↥(H0 M Z)) w ∈ W.map (cmComm M Q Z B K γ M₀ φ).subtype := by
    intro W hW s w hw
    obtain ⟨w', hw', rfl⟩ := hw
    refine ⟨cmCommAct hc φ s w', ?_, rfl⟩
    rw [← hρV s]
    exact hW _ _ hw'
  let ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K :=
    ((Matrix.GeneralLinearGroup.map (σ : K →+* K)).comp (StatedSp m K).subtype).comp Θ
  have hρrange : ρ.range = StatedSp m K := by
    ext A
    constructor
    · rintro ⟨s, rfl⟩
      exact CFSG.Open.StatedAPI.map_mem_statedSp (σ : K →+* K) (Θ s).2
    · intro hA
      obtain ⟨s, hs⟩ := hΘsurj ⟨Matrix.GeneralLinearGroup.map (σ.symm : K →+* K) A,
        CFSG.Open.StatedAPI.map_mem_statedSp _ hA⟩
      refine ⟨s, ?_⟩
      show Matrix.GeneralLinearGroup.map (σ : K →+* K) ((Θ s : StatedSp m K) : GL _ K) = A
      rw [hs]
      refine Units.ext (Matrix.ext fun i j => ?_)
      simp
  have hρker : ∀ s : ↥(XbarH M Q Z B), ρ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q := by
    intro s
    rw [← hΘker s]
    have hρs : ρ s = Matrix.GeneralLinearGroup.map (σ : K →+* K)
        ((Θ s : StatedSp m K) : GL (Fin m ⊕ Fin m) K) := rfl
    have hback : Matrix.GeneralLinearGroup.map (σ.symm : K →+* K) (ρ s) =
        ((Θ s : StatedSp m K) : GL (Fin m ⊕ Fin m) K) := by
      rw [hρs]
      exact Units.ext (Matrix.ext fun i j => by simp)
    constructor
    · intro h1
      rw [h1, map_one] at hback
      exact Subtype.ext hback.symm
    · intro h1
      rw [h1] at hρs
      rw [hρs]
      exact map_one _
  have hcol : ∀ (s : ↥(XbarH M Q Z B)) (i : Fin m ⊕ Fin m),
      φ (s : ↥(H0 M Z)) ((b i : ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) : M₀.E) =
        ∑ j, ((ρ s : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i •
          ((b j : ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) : M₀.E) := by
    intro s i
    rw [hb1 i]
    have h1 : φ (s : ↥(H0 M Z)) ((F (Pi.single i 1) : ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E) =
        ((F (((Θ s : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Pi.single i 1) : ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E) := by
      have h2 := hFeq (spEquiv (Θ s)) (Pi.single i 1)
      rw [spEquiv_app] at h2
      rw [h2, hρV s]
      rfl
    rw [h1]
    have h3 : ((Θ s : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        Pi.single i 1 = fun j => ((Θ s : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i := by
      ext j
      simp
    rw [h3, ← hb2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb1 j]
    rfl
  refine ⟨hdim, W₁.map (cmComm M Q Z B K γ M₀ φ).subtype,
    W₂.map (cmComm M Q Z B K γ M₀ φ).subtype, hinf, hsup, hinv W₁ hi₁, hinv W₂ hi₂, ?_, ?_, b, ρ,
    hρrange, hρker, hcol⟩
  · rintro w ⟨w', hw', rfl⟩
    exact hs₁ w' hw'
  · rintro w ⟨w', hw', rfl⟩
    exact hs₂ w' hw'

theorem cmSpTransv_of_rt1 [Finite G]
    (hRT1 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
      (N : Type) [AddCommGroup N] [Module K N] [FiniteDimensional K N]
      (BN : LinearMap.BilinForm K N)
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      4 ≤ Nat.card K → ∀ (hBN : BN.IsAlt), BN.Nondegenerate → 4 ≤ finrank K N →
      ∀ (Qf : QuadraticForm K V), (∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) →
      ∀ (ρ : Gsp BN →* (V ≃ₗ[K] V)), (∀ g v, Qf (ρ g v) = Qf v) →
      (∃ v₀ : N, v₀ ≠ 0 ∧ ∃ c₀ : K, c₀ ≠ 0 ∧
        finrank K (movedSpace (ρ (Tsp hBN v₀ c₀))) = 2 ∧
        ∀ w ∈ movedSpace (ρ (Tsp hBN v₀ c₀)), Qf w = 0) →
      (∀ v : V, (∀ g, ρ g v = v) → v = 0) →
      commutatorSpace ρ.range = ⊤ →
      ∃ W₁ W₂ : Submodule K V, IsCompl W₁ W₂ ∧
        (∀ w ∈ W₁, Qf w = 0) ∧ (∀ w ∈ W₂, Qf w = 0) ∧
        (∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
        ∃ (σ : K ≃+* K) (F : N →+ V), (∀ (c : K) x, F (c • x) = σ c • F x) ∧
          Function.Injective F ∧ (∀ x, F x ∈ W₁) ∧ (∀ w ∈ W₁, ∃ x, F x = w) ∧
          ∀ g x, F (g.app x) = ρ g (F x))
    (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n m x : ℕ) (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (hx : 2 ^ x = Nat.card Z)
    (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G))
    (hT : CMSpTransvAt M Q Z B m x a h) :
    Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ (4 * m + 1) ∧
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E),
        (∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
          M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y)) ∧
        ∃ W₁ W₂ : Submodule K M₀.E,
          W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ ∧
          (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁) ∧
          (∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂) ∧
          (∀ w ∈ W₁, M₀.Qf w = 0) ∧ (∀ w ∈ W₂, M₀.Qf w = 0) ∧
          ∃ (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁)
            (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K),
            ρ.range = StatedSp m K ∧
            (∀ s : ↥(XbarH M Q Z B), ρ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
            ∀ (s : ↥(XbarH M Q Z B)) (i : Fin m ⊕ Fin m),
              φ s ((b i : ↥W₁) : M₀.E) =
                ∑ j, (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i •
                  ((b j : ↥W₁) : M₀.E) := by
  have _ := hw
  have _ := hn
  refine ⟨?_, ?_⟩
  · obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
    obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
    have hK : Nat.card K = 2 ^ x := hD.card.trans hx.symm
    obtain ⟨hdim, -⟩ := hc.rt1_of_global hRT1 hLm ha2 hT hD hK φ hφπ hφk hφQ
    rw [hc.card_sup_commXbarPre_eq hD φ hφπ,
      Module.natCard_eq_pow_finrank (K := K) (V := ↥(cmComm M Q Z B K γ M₀ φ)), hdim, hD.card,
      pow_succ']
  · intro K _ _ _ γ M₀ hD
    obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
    have hK : Nat.card K = 2 ^ x := hD.card.trans hx.symm
    obtain ⟨-, W₁, W₂, hW⟩ := hc.rt1_of_global hRT1 hLm ha2 hT hD hK φ hφπ hφk hφQ
    exact ⟨φ, hφπ, W₁, W₂, hW⟩

end CFSG.RankThree.GF2n.Stroth80
