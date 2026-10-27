module

public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishCoord
public import CFSG.RankThree.GF2n.Stroth80.Sec710Family
public import CFSG.RankThree.GF2n.Stroth80.Sec7NormalizerOmega
public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishCount

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def OmegaMinusFourSingularTransStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ x y : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, x ≠ 0 → y ≠ 0 →
      CFSG.LieType.Universal.Spin.quadMinus 2 K b c x = 0 →
      CFSG.LieType.Universal.Spin.quadMinus 2 K b c y = 0 →
      ∃ A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c),
        ((A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x = y

@[expose] def Step71VanishGeomStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → (∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z) →
      ∃ v ∈ Vt M (LB M Q B) B Z t, ∀ r ∈ Rt M (LB M Q B) t, ⁅x, v⁆ ∉ conjSubgroup r B ⊔ Z

theorem conjMod_facts
    (hc : Ctx M Q Z B) {t x : G} (ht : t ∈ LB M Q B) (hx : ConjMod M Q t x) :
    x ∈ H0 M Z ∧ x ^ 2 ∈ Q := by
  obtain ⟨-, g, hg, hq⟩ := hx
  have htH : t ∈ H0 M Z := hc.LB_le_H0' ht
  have hx₀H : g * t * g⁻¹ ∈ H0 M Z := hc.conj_mem_H0 hg htH
  have hx₀M : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg (hc.LB_le_M ht)) (M.inv_mem hg)
  have hxe : x * (g * t * g⁻¹)⁻¹ * (g * t * g⁻¹) = x := by group
  constructor
  · have := (H0 M Z).mul_mem (hc.Q_le_H0 hq) hx₀H
    rwa [hxe] at this
  · have hx₀2 : (g * t * g⁻¹) ^ 2 ∈ Q := by
      have e : (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ := by
        simp only [pow_two]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) (t ^ 2)).mp
        (hc.sq_mem_Q_of_mem_LB ht)
    have hconj : (g * t * g⁻¹) * (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hx₀M) _).mp hq
    have e2 : x ^ 2 = (x * (g * t * g⁻¹)⁻¹) *
        ((g * t * g⁻¹) * (x * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) ^ 2 := by
      simp only [pow_two]
      group
    rw [e2]
    exact Q.mul_mem (Q.mul_mem hq hconj) hx₀2

theorem exists_fx_of_natural
    (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {X : Subgroup (GL ι K)}
    (hX : AddCommutantScalar X) (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q) (hxH : x ∈ H0 M Z) :
    ∃ Fx : (ι → K) →ₗ[K] (ι → K), ∀ k k' : ↥(Vt M (LB M Q B) B Z t),
      (k' : G) = x * k * x⁻¹ → Fx (secVec ψ k) = secVec ψ k' := by
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)) v).mp hv
  obtain ⟨Kg, fKg, finKg, γ, M₀, ρ, b, hS, ψA, hψA, -, -, -, -, hA0b⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  have hcard : Nat.card Kg = Nat.card K := by rw [hS.card, hK]
  have hSmul : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun c e he =>
    hc.smul_mem_img_Vt hS.model t c he
  have hlin : ∀ r ∈ Rt M (LB M Q B) t, ∃ T : M₀.E →ₗ[Kg] M₀.E,
      ∀ q ∈ Q, M₀.π (r * q * r⁻¹) = T (M₀.π q) := by
    intro r hr
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have hrbar : (QuotientGroup.mk (⟨r, hrM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
      Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr (hc.Rt_le_H0 t hr), rfl⟩
    refine ⟨(AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨r, hrM⟩ : ↥M))).toAdd
      (hS.lin _ hrbar)).toLinearMap, fun q hq => ?_⟩
    exact hS.conj ⟨r, hrM⟩ q hq
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcard M₀ hVQ hX hSmul hlin φ hφ
    (hc.Rt_normalizes_Vt ht) ψ hψ
  exact exists_natLinear_conj hc hS ψ θ hθ hSmul hxM hxH hxV

theorem step71VanishPair_of_geom
    (hGeom : Step71VanishGeomStatement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement)
    (hWm4 : OmegaMinusFourSingularTransStatement) : Step71VanishPairStatement := by
  unfold Step71VanishPairStatement
  intro G _ _ M Q Z B hc n t hs hno x hx hxt hmov
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hxH, hx2⟩ := conjMod_facts hc ht hx
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hxM : x ∈ M := hx.1
  have hG : ∃ k : G, k ∈ Vt M (LB M Q B) B Z t ∧
      ∀ r ∈ Rt M (LB M Q B) t, ⁅x, k⁆ ∉ conjSubgroup r B ⊔ Z := by
    obtain ⟨v, hv, hvn⟩ := hGeom G M Q Z B hc n t hs hno x hx hxt hmov
    exact ⟨v, hv, hvn⟩
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨m, hm2, hm⟩ := hs.orth
  rcases hm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  ·
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have h2 : m = 2 := by omega
      subst h2
      exact hs.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact hq4
    have hnat' := hnat
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have h4 : 4 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    obtain ⟨Fx, hFx⟩ := exists_fx_of_natural h34 h310chi hZc hZV hZcard hc hs hZ0 hK
      (addCommutantScalar_statedOmegaPlus hm3) φ hφ ψ hψ hxM hxt hxH
    have hW : ∀ x y : (Fin m ⊕ Fin m) → K, x ≠ 0 → y ≠ 0 →
        quadPlus m K x = 0 → quadPlus m K y = 0 →
        ∃ A ∈ StatedOmega (StatedQuadPlus m K),
          ((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = y :=
      fun a d ha hd ha0 hd0 => statedOmegaPlus_exists_mulVec_eq hm3 ha hd (by rw [ha0, hd0])
    have hN : ∀ A : GL (Fin m ⊕ Fin m) K,
        (∀ g ∈ StatedOmega (StatedQuadPlus m K),
          A * g * A⁻¹ ∈ StatedOmega (StatedQuadPlus m K)) →
        ∃ c : K, c ≠ 0 ∧ ∀ v,
          quadPlus m K (c • ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v)) =
            quadPlus m K v := by
      intro A hA
      obtain ⟨c, hc0, hcv⟩ := normalizerOmegaFor_plus K hK4 hm2 A hA
      exact ⟨c, hc0, fun v => by rw [coe_quadPlus]; exact hcv v⟩
    obtain ⟨h, hh, r, hr, hp, he⟩ := vanishPair_coord h34 hRoot hc hs.toSec5
      (Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hnat'⟩⟩) hK (ElemMatrixIso.plus hm3)
      (nondegenerate_polarBilin_quadPlus m K) h4 (addCommutantScalar_statedOmegaPlus hm3) φ hφ
      hker ψ hψ hW hN hxM hxt hx2 Fx hFx hG
    exact ⟨h, hh, r, hr, hp, he⟩
  ·
    have hK' : Nat.card K = Nat.card Z := hK
    haveI : CharP K 2 := sec7ctr_charP hc hK
    have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact hq4
    have hnat' := hnat
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨-, hn, ψ, hψ⟩ := hact
    haveI := hn
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have h4 : 4 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega
    obtain ⟨Fx, hFx⟩ := exists_fx_of_natural h34 h310chi hZc hZV hZcard hc hs hZ0 hK'
      (addCommutantScalar_statedOmegaMinus hm2 hirr) φ hφ ψ hψ hxM hxt hxH
    have hW : ∀ x y : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) → K, x ≠ 0 → y ≠ 0 →
        quadMinus m K b c x = 0 → quadMinus m K b c y = 0 →
        ∃ A ∈ StatedOmega (StatedQuadMinus m K b c),
          ((A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
            Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
              (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ x = y := by
      intro a d ha hd ha0 hd0
      by_cases h2 : m = 2
      · subst h2
        exact hWm4 K b c hirr a d ha hd ha0 hd0
      · exact statedOmegaMinus_exists_mulVec_eq (by omega) hirr ha hd (by rw [ha0, hd0])
    have hN : ∀ A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K,
        (∀ g ∈ StatedOmega (StatedQuadMinus m K b c),
          A * g * A⁻¹ ∈ StatedOmega (StatedQuadMinus m K b c)) →
        ∃ c' : K, c' ≠ 0 ∧ ∀ v, quadMinus m K b c
          (c' • ((A : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ v)) = quadMinus m K b c v := by
      intro A hA
      obtain ⟨c', hc0, hcv⟩ := normalizerOmegaFor_minus K hm2 hirr A hA
      exact ⟨c', hc0, fun v => by rw [coe_quadMinus]; exact hcv v⟩
    obtain ⟨h, hh, r, hr, hp, he⟩ := vanishPair_coord h34 hRoot hc hs.toSec5
      (Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm2, hirr, hnat'⟩⟩) hK'
      (ElemMatrixIso.minus hm2 hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h4
      (addCommutantScalar_statedOmegaMinus hm2 hirr) φ hφ hker ψ hψ hW hN hxM hxt hx2 Fx hFx hG
    exact ⟨h, hh, r, hr, hp, he⟩

end CFSG.RankThree.GF2n.Stroth80
