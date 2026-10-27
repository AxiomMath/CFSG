module

public import CFSG.RankThree.GF2n.Stroth80.Sec7ActOp
public import CFSG.RankThree.GF2n.Stroth80.Sec7SiegelGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_point_data (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (h4 : OmegaPlusNat hc t 4) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2), Nat.card K' = Nat.card Z ∧
      ∃ (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 4 ⊕ Fin 4) K') (u : Fin 4 ⊕ Fin 4 → K'),
        φ.range = StatedOmega (StatedQuadPlus 4 K') ∧
        φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
        StatedQuadPlus 4 K' u = 0 ∧ u ≠ 0 ∧
        ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = rootGroupGL (quadPlus 4 K') u ∧
        ∀ r : ↥(Rt M (LB M Q B) t),
          (∃ c : K', ((φ r : GL (Fin 4 ⊕ Fin 4) K') : Matrix _ _ K').mulVec u = c • u) →
          conjSubgroup (r : G) (LB M Q B) = LB M Q B := by
  classical
  obtain ⟨K, fK, finK, hK, hnat⟩ := h4
  letI := fK
  letI := finK
  have hm : 3 ≤ 4 := by norm_num
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inl ⟨4, hm, hnat⟩⟩
  haveI hchar : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  haveI : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin 4 ⊕ Fin 4 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    norm_num
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  have hX := addCommutantScalar_statedOmegaPlus (K := K) (m := 4) hm
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hsing := hc.omega_singular h34 hRoot hs hnatSO hK (ElemMatrixIso.plus hm) hQ h3
    hX φ hφ ψ hψ
  obtain ⟨u, hQu, hu0, hBiff, -, hL, -⟩ := hc.omega_points_core h34 hRoot hs hnatSO hK
    (ElemMatrixIso.plus hm) hQ h3 hX φ hφ hker ψ hψ hsing
  have ht : t ∈ LB M Q B := hs.mem
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  refine ⟨K, fK, finK, hchar, hK, φ, u, hφ, hker,
    (congrFun (coe_quadPlus 4 K) u).symm.trans hQu, hu0, ?_, ?_⟩
  · rw [hL, ElemMatrixIso.LomGL_plus hm, sec7_rootGroupGL_eq_LomGLPlus hm]
  · rintro r ⟨c, hcr⟩
    refine hc.conj_LB_eq_of_le_sup_Z (hc.Rt_le_M t r.2) ?_
    intro x hx
    have hxB : (r : G)⁻¹ * x * r ∈ B := mem_conjSubgroup.mp hx
    have hb₁V : (r : G)⁻¹ * x * r ∈ Vt M (LB M Q B) B Z t := hBV hxB
    have hxeq : x = (r : G) * ((r : G)⁻¹ * x * r) * (r : G)⁻¹ := by group
    have hxV : x ∈ Vt M (LB M Q B) B Z t := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht r.2) _).mp hb₁V
      rwa [← hxeq] at h1
    have hsv := hψ r ⟨_, hb₁V⟩ ⟨x, hxV⟩ hxeq
    change secVec ψ ⟨x, hxV⟩ = (φ r : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
      secVec ψ ⟨_, hb₁V⟩ at hsv
    obtain ⟨c₁, hc₁⟩ := (hBiff (secVec ψ ⟨_, hb₁V⟩)).mp ⟨⟨_, hb₁V⟩, hxB, rfl⟩
    obtain ⟨b', hb'B, hb'⟩ := (hBiff (secVec ψ ⟨x, hxV⟩)).mpr ⟨c₁ * c, by
      rw [hsv, hc₁, Matrix.mulVec_smul, hcr, smul_smul]⟩
    have hz : (x : G) * (b' : G)⁻¹ ∈ Z := (secVec_eq_iff ψ ⟨x, hxV⟩ b').mp hb'.symm
    have e : x = (x * (b' : G)⁻¹) * (b' : G) := by group
    rw [e]
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hb'B)

end

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}
  (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}

include hc hS

theorem sec7_irred_E (hSec : Sec7WVSecCardStatement) {n' : ℕ} (hs : Sec7Hyp hc n' t)
    (h4 : OmegaPlusNat hc t 4) (ψ : M₀.E →ₗ[K] M₀.E)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0)
    (P : Submodule K M₀.E) (hPW : P ≤ M₀.B.orthogonal (hc.VtSub hS.model t))
    (hcardU : Nat.card (hc.VtSub hS.model t) = Nat.card K ^ 8)
    (hcardP : Nat.card P = Nat.card K ^ 16)
    (A : AddSubgroup M₀.E) (hUA : (hc.VtSub hS.model t).toAddSubgroup ≤ A)
    (hAP : A ≤ P.toAddSubgroup)
    (hAinv : ∀ (r : G) (hr : r ∈ Rt M (LB M Q B) t), ∀ a ∈ A,
      sec7Op hc hS (hc.Rt_le_H0 t hr) a ∈ A) :
    A = (hc.VtSub hS.model t).toAddSubgroup ∨ A = P.toAddSubgroup := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  set Pg : Subgroup G := sec7Pre M₀ A with hPg
  have hVP : Vt M (LB M Q B) B Z t ≤ Pg := fun x hx =>
    ⟨hVQ hx, hUA ((hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hx (hVQ hx)))⟩
  have hPgW : Pg ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx =>
    (sec7_mem_Wt_iff_perp hc hS ψ hW hx.1).mpr (hPW (hAP hx.2))
  have hPR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r Pg = Pg := by
    intro r hr
    apply conjSubgroup_eq_self_iff.mpr
    refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
    · exact (hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t hr)).1 x hx.1
    · show M₀.π (r * x * r⁻¹) ∈ A
      rw [sec7Op_pi hc hS (hc.Rt_le_H0 t hr) hx.1]
      exact hAinv r hr _ hx.2
  obtain ⟨k, hk⟩ := (hSec G M Q Z B hc n' t hs Pg hVP hPgW hPR 4 (by norm_num)).2 h4
    (by norm_num)
  have hZPg : Z ≤ Pg := fun z hz => ⟨hc.Z_le_Q hz, by
    rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]
    exact A.zero_mem⟩
  have hcP := Tim79.QuadModel.card_eq M₀ (fun x hx => hx.1 : Pg ≤ Q) hZPg
  have hcimgP : Nat.card (M₀.img Pg) = Nat.card A :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun e => sec7_img_pre M₀ A e))
  have hcV := Tim79.QuadModel.card_eq M₀ hVQ hZV
  have hcimgV : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card (hc.VtSub hS.model t) :=
    rfl
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hAcard : Nat.card A = Nat.card K ^ (8 + 8 * k) := by
    rw [hcP, hcimgP, hcV, hcimgV, hcardU] at hk
    have h2 : Nat.card Z * Nat.card A =
        Nat.card Z * (Nat.card K ^ 8 * Nat.card K ^ (8 * k)) := by
      rw [hk, mul_assoc, hZK]
      norm_num
    rw [Nat.eq_of_mul_eq_mul_left hZpos h2, ← pow_add]
  have hle : Nat.card A ≤ Nat.card P := by
    have := AddSubgroup.card_le_of_le hAP
    exact this
  rw [hAcard, hcardP] at hle
  have hk1 : 8 + 8 * k ≤ 16 := (Nat.pow_le_pow_iff_right (by omega)).mp hle
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl
  · left
    refine (AddSubgroup.eq_of_le_of_card_ge hUA ?_).symm
    show Nat.card A ≤ Nat.card (hc.VtSub hS.model t)
    rw [hAcard, hcardU]
  · right
    refine AddSubgroup.eq_of_le_of_card_ge hAP ?_
    show Nat.card P ≤ Nat.card A
    rw [hAcard, hcardP]

end

end CFSG.RankThree.GF2n.Stroth80
