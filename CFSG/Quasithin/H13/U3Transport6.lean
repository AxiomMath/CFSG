module

public import CFSG.Quasithin.H13.U3SixAction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB Matrix
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem u3_six_module_transport
    (h1332 : Stmt13_3_2) [Finite G] {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z) :
    ∃ Φ : Additive V ≃ₗ[ZMod 2] W6,
      (∀ (l : G) (hl : l ∈ L), ∃ j ∈ J6, linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j) ∧
      (∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
        (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j) ∧
      ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
        linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hVT, -, hV64, -, -, hLV, hTV, hirr, hnt, hTC, -, -⟩ := id hF
  obtain ⟨-, hVM, -, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* U33G := e1.trans e2.symm
  let φ := SteinbergBS.normalizerConjOn V L hLV
  have hOL : pCoreOf 2 L ≤ centralizer (V : Set G) := by
    refine (pCoreOf_le_pCoreOf_sup hTL).trans ?_
    rw [← hTC]
    exact inf_le_right
  have hO : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [ker_normalizerConjOn hLV, mem_subgroupOf]
    refine ⟨x.2, hOL ?_⟩
    rw [← inSubgroup_pCore_eq_pCoreOf]
    exact ⟨x, hx, rfl⟩
  let ψ : U33G →* MulAut V :=
    (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO).comp e.symm.toMonoidHom
  let f : ↥L →* U33G := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψf : ∀ l : ↥L, ψ (f l) = φ l := fun l => by
    change QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO (e.symm (e (l : ↥L ⧸ CFSG.pCore 2 ↥L))) =
      φ l
    rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]
  have hCL : V ⊓ centralizer (L : Set G) = ⊥ := by
    rcases hirr (V ⊓ centralizer (L : Set G)) inf_le_left
        (fun l hl w hw => by
          rw [show l * w * l⁻¹ = w by
            rw [(mem_centralizer_iff.1 hw.2) l hl, mul_inv_cancel_right]]
          exact hw) with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, v, hv, hlv⟩ := hnt
      have hvC : v ∈ centralizer (L : Set G) := (h.symm ▸ hv : v ∈ V ⊓ _).2
      exact hlv (by rw [(mem_centralizer_iff.1 hvC) l hl, mul_inv_cancel_right])
  have hψfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1 := by
    intro v hv
    have hvC : (v : G) ∈ V ⊓ centralizer (L : Set G) := by
      refine ⟨v.2, mem_centralizer_iff.2 fun l hl => ?_⟩
      have h1 := congrArg Subtype.val (hv (f ⟨l, hl⟩))
      rw [hψf] at h1
      change l * v * l⁻¹ = v at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    rw [hCL] at hvC
    exact Subtype.ext ((mem_bot).1 hvC)
  have hV2 : ∀ v : V, v * v = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian _ v.2)
  obtain ⟨F, hFeq⟩ := exists_equiv_u33_module hV2 hV64 ψ hψfix
  set Φ := linOfMulEquiv F with hΦ
  have hΦψ : ∀ (k : U33G) (x : Additive V),
      Φ (mulAutToLin V (ψ k) x) = glLin (rho6 k) (Φ x) := by
    intro k x
    rw [hΦ, linOfMulEquiv_apply, linOfMulEquiv_apply, mulAutToLin_apply, toMul_ofMul,
      glLin_apply]
    set w := F.symm (Additive.toMul x) with hw
    have h1 : F.symm (ψ k (Additive.toMul x)) = psiW k w := by
      rw [MulEquiv.symm_apply_eq, hFeq, hw, MulEquiv.apply_symm_apply]
    rw [h1]
    show Multiplicative.toAdd (psiW k (Multiplicative.ofAdd (Multiplicative.toAdd w))) = _
    rw [psiW_apply]
    rfl
  have hlinψ : ∀ k : U33G, linConj Φ (mulAutToLin V (ψ k)) = glLin (rho6 k) := by
    intro k
    ext w
    rw [linConj_apply, hΦψ, LinearEquiv.apply_symm_apply]
  have hψu : ∀ l : L, mulAutToLin V (ψ (f l)) =
      u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hLV l.2⟩ := fun l => by
    rw [hψf]
    rfl
  have hnl : ∀ (n : normalizer (V : Set G)) (l : L), (n : G) * l * (n : G)⁻¹ ∈ L :=
    fun n l => (mem_normalizer_iff.1 (hVM n.2) l).1 l.2
  have hcomm : ∀ (n : normalizer (V : Set G)) (l : L),
      u3ConjLin V _ le_rfl n * u3ConjLin V _ le_rfl ⟨l, hLV l.2⟩ * (u3ConjLin V _ le_rfl n)⁻¹ =
        u3ConjLin V _ le_rfl ⟨n * l * n⁻¹, hLV (hnl n l)⟩ := by
    intro n l
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  let gN : normalizer (V : Set G) → GL (Fin 6) (ZMod 2) := fun n =>
    glLin.symm (linConj Φ (u3ConjLin V _ le_rfl n))
  have hgN_inv : ∀ n, gN n⁻¹ = (gN n)⁻¹ := fun n => by
    simp only [gN, map_inv]
  have hgN_conj : ∀ (n : normalizer (V : Set G)) (l : L),
      gN n * rho6 (f l) * (gN n)⁻¹ = rho6 (f ⟨n * l * n⁻¹, hnl n l⟩) := by
    intro n l
    apply glLin.injective
    simp only [gN, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← hlinψ, ← hlinψ, hψu, hψu, ← map_inv (linConj Φ), ← map_mul, ← map_mul, hcomm]
  have hgN_mem : ∀ n, gN n ∈ N6 := by
    intro n
    rw [← normalizer_J6_eq, mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨l, rfl⟩ := hf k
      exact ⟨_, (hgN_conj n l).symm⟩
    · rintro ⟨k, hk⟩
      obtain ⟨l, rfl⟩ := hf k
      obtain ⟨k', hk'⟩ : ∃ k', gN n⁻¹ * rho6 (f l) * (gN n⁻¹)⁻¹ = rho6 k' :=
        ⟨_, hgN_conj n⁻¹ l⟩
      refine ⟨k', ?_⟩
      rw [← hk', hgN_inv, inv_inv, hk]
      group
  refine ⟨Φ, fun l hl => ⟨rho6 (f ⟨l, hl⟩), ⟨_, rfl⟩, ?_⟩, fun j hj => ?_, fun n =>
    ⟨gN n, hgN_mem n, by simp only [gN, MulEquiv.apply_symm_apply]⟩⟩
  · rw [← hlinψ, hψu]
  · obtain ⟨k, rfl⟩ := hj
    obtain ⟨l, rfl⟩ := hf k
    exact ⟨l, l.2, by rw [← hlinψ, hψu]⟩

end CFSG.Quasithin.H13.U3
