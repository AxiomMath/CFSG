module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportHom
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportInv
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportLin
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotT

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module
open scoped commutatorElement Matrix

variable {G : Type} [Group G]


section Input

variable {M Q Z B : Subgroup G}

theorem Ctx.exists_form_ne_zero_of_not_cmSpTransvAt [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ x)
    (ψ : ↥(Xbar M Q Z B) ≃* StatedSp m K) :
    Module.finrank K (Fin m ⊕ Fin m → K) = 4 → ∃ v : Fin m ⊕ Fin m → K,
      spForm m K v ((((spEquiv (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩) :
        LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
        (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) - 1) v) ≠ 0 := by
  intro h4
  have hm : m = 2 := by
    rw [finrank_spSpace] at h4
    omega
  subst hm
  obtain ⟨-, v, hv⟩ := hc.type_c2_of_not_cmSpTransvAt hLm hnT hK ψ
  exact ⟨v, by rw [spForm_spEquiv_sub_one_apply]; exact hv⟩

theorem Ctx.exists_negT_input [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) (hK : Nat.card K = 2 ^ x)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) :
    ∃ (ψ : ↥(Xbar M Q Z B) ≃* StatedSp m K) (Θ : ↥(XbarH M Q Z B) →* StatedSp m K)
      (ρV : Gsp (spForm m K) →*
        (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))),
      (∀ s, Θ s = ψ (xbarHToXbar M Q Z B s)) ∧ Function.Surjective Θ ∧
      (∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q) ∧
      (∀ s, ρV (spEquiv (Θ s)) = cmCommAct hc φ s) ∧
      (∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v) ∧
      (∀ v : ↥(cmComm M Q Z B K γ M₀ φ), (∀ g, ρV g v = v) → v = 0) ∧
      commutatorSpace ρV.range = ⊤ ∧
      ∃ t₀ : Gsp (spForm m K),
        t₀ = spEquiv (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩) ∧
        t₀ * t₀ = 1 ∧ t₀ ≠ 1 ∧
        (Module.finrank K (movedSpace (ρV t₀)) = 2 ∧
          ∀ w ∈ movedSpace (ρV t₀), cmCommQf B φ w = 0) ∧
        Module.finrank K (LinearMap.range
          (((t₀ : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
            (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) - 1)) ≠ 1 ∧
        (Module.finrank K (Fin m ⊕ Fin m → K) = 4 → ∃ v : Fin m ⊕ Fin m → K,
          spForm m K v ((((t₀ : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
            (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) - 1) v) ≠ 0) := by
  classical
  obtain ⟨ψ, Θ, hΘψ, hΘsurj, hΘker⟩ := hc.exists_hom_statedSp_of_lieModel hLm hK
  obtain ⟨s₀, hs₀a, hs₀ψ⟩ := hc.exists_lift_a2 (h := h)
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hΘs₀ : Θ s₀ = ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ := by
    rw [hΘψ, hs₀ψ]
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
  obtain ⟨hg2, hg1⟩ := image_mul_self_eq_one_and_ne_one (h := h) ψ
  refine ⟨ψ, Θ, ρV, hΘψ, hΘsurj, hΘker, hρV, ?_, ?_, ?_,
    spEquiv (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩), rfl, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro g v
    obtain ⟨s, rfl⟩ := hspΘ g
    rw [hρV s]
    exact cmCommQf_cmCommAct hc φ hφQ s v
  · intro v hv
    refine Subtype.ext (hc.eq_zero_of_fixed_of_mem_cmComm hD φ hφπ hφB v.2 fun s => ?_)
    have h1 := hv (spEquiv (Θ s))
    rw [hρV s] at h1
    exact congrArg Subtype.val h1
  · have hrange : ρV.range = (cmCommAct hc φ).range := by
      ext f
      constructor
      · rintro ⟨g, rfl⟩
        obtain ⟨s, rfl⟩ := hspΘ g
        exact ⟨s, (hρV s).symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨spEquiv (Θ s), hρV s⟩
    rw [hrange]
    exact hc.commutatorSpace_cmCommAct_eq_top hD φ hφπ hφB
  · rw [← map_mul, hg2, map_one]
  · intro h1
    exact hg1 ((spEquiv (m := m) (K := K)).injective (h1.trans (map_one _).symm))
  · rw [← hΘs₀, hρV s₀]
    exact hc.cmCommAct_moved hD hKZ φ hφπ ha2 (by rw [hs₀a]; exact h.1)
      (by rw [hs₀a]; exact h.2)
  · rw [finrank_range_spEquiv_sub_one]
    exact hc.rank_ne_one_of_not_cmSpTransvAt hLm hnT hK ψ
  · exact hc.exists_form_ne_zero_of_not_cmSpTransvAt hLm hnT hK ψ

end Input

variable [Finite G]

theorem cmSpNotTransv_of_negT
    (hNegT : ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
      (N : Type) [AddCommGroup N] [Module K N] [FiniteDimensional K N]
      (BN : LinearMap.BilinForm K N)
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      4 ≤ Nat.card K → BN.IsAlt → BN.Nondegenerate → 4 ≤ finrank K N →
      ∀ (Qf : QuadraticForm K V), (∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) →
      ∀ (ρ : Gsp BN →* (V ≃ₗ[K] V)), (∀ g v, Qf (ρ g v) = Qf v) →
      ∀ (t₀ : Gsp BN), t₀ * t₀ = 1 → t₀ ≠ 1 →
      (finrank K (movedSpace (ρ t₀)) = 2 ∧ ∀ w ∈ movedSpace (ρ t₀), Qf w = 0) →
      finrank K (LinearMap.range
        (((t₀ : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1)) ≠ 1 →
      (finrank K N = 4 → ∃ v : N,
        BN v ((((t₀ : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1) v) ≠ 0) →
      (∀ v : V, (∀ g, ρ g v = v) → v = 0) →
      commutatorSpace ρ.range = ⊤ →
      finrank K N = 6 ∧ finrank K V = 8 ∧
        ∀ U : AddSubgroup V, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n m x : ℕ) (_hw : Width Q Z n) (_hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (hx : 2 ^ x = Nat.card Z)
    (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G))
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h) :
    m = 3 ∧ Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ 9 ∧
      (∀ W : Subgroup G, Z ≤ W → W ≤ Z ⊔ ⁅Q, XbarPre M Q Z B⁆ →
        (∀ g ∈ XbarPre M Q Z B, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
        W = Z ∨ W = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hK : Nat.card K = 2 ^ x := hKZ.trans hx.symm
  have hq4 : 4 ≤ Nat.card K := hKZ ▸ hc.hyp.q4
  have hm2 : 2 ≤ m := (hLm.admissible).2.2.1
  obtain ⟨-, Θ, ρV, -, hΘ, -, hρV, hρQ, hC, hV, t₀, -, ht₀sq, ht₀1, hsieg, hT, hA2⟩ :=
    hc.exists_negT_input hLm ha2 hnT hD hK φ hφπ hφk hφQ
  obtain ⟨h6, h8, hirr⟩ := hNegT K (Fin m ⊕ Fin m → K) (spForm m K)
    (cmComm M Q Z B K γ M₀ φ) hq4 spForm_isAlt spForm_nondegenerate
    (by rw [finrank_spSpace]; omega) (cmCommQf B φ) (hc.cmCommQf_nondegenerate hD φ hφπ) ρV hρQ
    t₀ ht₀sq ht₀1 hsieg hT hA2 hC hV
  rw [finrank_spSpace] at h6
  refine ⟨by omega, hc.card_sup_commXbarPre_eq_pow_nine hD φ hφπ h8, ?_⟩
  intro W hZW hWY hinv
  exact hc.eq_or_eq_of_invariant hD φ hφπ ((spEquiv (m := m) (K := K)).toMonoidHom.comp Θ)
    ((spEquiv (m := m) (K := K)).surjective.comp hΘ) ρV hρV hirr W hZW hWY hinv

end CFSG.RankThree.GF2n.Stroth80
